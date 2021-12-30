//! A lock-free concurrent hash table which uses leapfrog probing.
//!
//! All map operations can be used fuilly concurrently, and is both efficient
//! and scalable up to many threads. If the value type for the map supports atomic
//! operations then this map will not lock, while if the value type does not support atomic
//! operations then accessing the value uses an efficient spinlock implementation.
//! The interface for the map has been kept as close as possible to
//! `std::collections::HashMap`, however, there are some differences to ensure
//! that concurrent operations are always correct and efficient.
//!
//! The biggest differences between the interface of this map and the
//! `std::collections::HashMap`, is the types returned by (LeapMap::get) and
//! [LeapMap::get_mut]. These methods return [Ref] and [RefMut] types,
//! respectively, which have interfaces to allow for accessing the cells returned
//! by the get calls, concurrently and correctly. As a result, it is not possible
//! to get a reference to the cell's value, since the cell value type is atomic.
//! The value can be accessed with `value()` for [Ref] and [RefMut] types, or
//! can be set with `set_value()`, or updated with `update`, for [RefMut] types.
//! These interfaces ensure that the most up to date value is loaded/stored/updated,
//! and that if the referenced cell is invalidated or erased by other threads,
//! the reference [Ref]/[RefMut] type is updated appropriately. These interfaces
//! are designed to ensure that using the map does not require thinking about
//! concurrency.
//!
//! The map uses [leapfrog probing](https://preshing.com/20160314/leapfrog-probing/)
//! which is similar to [hopscotch hashing](https://en.wikipedia.org/wiki/Hopscotch_hashing)
//! since it is based off of it. Leapfrog probing stores two offset per
//! cell which are used to efficiently traverse a local neighbourhood of values
//! around the cell to which a key hashes. This makes the map operations are cache
//! friendly and scalable, even under heavy contention.
//!
//! # Performance
//!
//! This map has been benchmarked against other hash maps across multiple threads
//! and multiple workloads. The benchmarks can be found [here](https://github.com/robclu/conc-map-bench).
//! A snapshot of the results for a read heavy workload are the following (with
//! throughput in Mops/second, cores in brackets, and performance realtive to
//! `std::collections::HashMap` with RwLock):
//!
//! | Map              | Throughput (1) | Relative (1) | Throughput (16) | Relative (16) |
//! |------------------|----------------|--------------|-----------------|---------------|
//! | RwLock + HashMap | 17.6           | 1.0          | 12.3            | 0.69          |
//! | Flurry           | 10.2           | 0.58         | 76.3            | 4.34          |
//! | DashMap          | 14.1           | 0.80         | 84.5            | 4.8           |
//! | LeapMap          | 16.8           | 0.95         | 167.8           | 9.53          |
//!
//! # Consistency
//!
//! All operations on the map are non-blocking, and accessing/updating a value
//! in the map will not lock if the value type has built-in atomic support. All
//! operations can therefore be overlapped from any number of threads.
//!
//! # Limitations
//!
//! Every design has tradeoffs, and there are some limitations for this map as
//! well.
//!
//! The primary limitation of the map is that it does not store keys, but rather
//! hashes of the keys. Thus far this has not been a limitation, however, it would
//! be possible to add key support, if neccessary.
//!
//! You should use a hasher which produces unique hashes for each key. As only
//! hashes are stored, if two keys hash to the same hash then the value for the
//! keys which hash to the same value my be overwritten by each other if they
//! are inserted concurrently. The [MurmurHasher] is the default hasher, and has
//! been found to be efficient and passed all stress tests. The built in hasher
//! and [fxhash](https://docs.rs/fxhash/latest/fxhash/) have also passed all
//! stress tests.
//!
//! See the first section for limitations relating to the types returned by
//! [LeapMap::get] and [LeapMap::get_mut].
//!
//! Getting the length of the map does not return the length of the map, but rather an
//! estimate of the length, unless the calling thread is the only thread operating
//! on the map, and therefore that there are no other readers or writers. Additionally,
//! the length is expensive to compute since it is not tracked as insertions and
//! removals are performed. The overhead of doing so when under contention
//! was found to be significant during benchmarking, and given that it's only an
//! estimate, it's not worth the cost.
//!
//! The size of the map must always be a power of two.
//!
//! The value type for the map needs to implement the [Value] trait, which is
//! simple enough to implement, however, two values need to be chosen, one as a
//! null value and another as a redirect value. For integer types, MAX and MAX-1
//! are used respectively. A good choice should be values which are efficient for
//! comparison, so for strings, a single character which not be used as the first
//! character for any valid string would be a good choice.
//!
//! # Resizing
//!
//! The buckets for the map are expanded when an insertion would result in a
//! offset which would overflow the maximum probe offset (i.e, when it's not
//! possible to find an empty cell within the probe neighbourhood), or shrunk
//! when probes are too far apart. The resizing and subsequent removal of buckets
//! from the old table to the new table will happen concurrently when multiple
//! threads are attempting to modify the map concurrently, which makes the reszing
//! efficient. Despite this, it is best to choose a larger size where possible,
//! since it will ensure more stable performance of inserts and gets.

#![feature(allocator_api)]
#![feature(const_fn_trait_bound)]

pub mod hashmap;
pub mod leapmap;
mod leapref;
mod util;

use crate::util::load_u64_le;
use std::borrow::Borrow;
use std::{
    default::Default,
    fmt::Debug,
    hash::{BuildHasher, Hash, Hasher},
};

pub use hashmap::HashMap;
pub use leapmap::LeapMap;
pub use leapref::Ref;
pub use leapref::RefMut;

/// Trait which represents a value which can be stored in a map.
pub trait Value: Default + Debug + Sized + PartialEq + Clone + Copy {
    /// Returns the value used for redirection.
    fn redirect() -> Self;
    fn null() -> Self;
}

macro_rules! value_impl {
    ($type:ty, $redirect_expr:expr, $null_expr:expr) => {
        impl Value for $type {
            fn redirect() -> $type {
                $redirect_expr
            }
            fn null() -> $type {
                $null_expr
            }
        }
    };
}

value_impl!(u8, u8::MAX, u8::MAX - 1);
value_impl!(u16, u16::MAX, u16::MAX - 1);
value_impl!(u32, u32::MAX, u32::MAX - 1);
value_impl!(u64, u64::MAX, u64::MAX - 1);
value_impl!(i8, i8::MAX, i8::MAX - 1);
value_impl!(i16, i16::MAX, i16::MAX - 1);
value_impl!(i32, i32::MAX, i32::MAX - 1);
value_impl!(i64, i64::MAX, i64::MAX - 1);
value_impl!(usize, usize::MAX, usize::MAX - 1);

/// Creates a hash value from the `hash_builder` and `value`.
///
/// # Arguments
///
/// * `hash_builder` - The builder to builde the hasher with.
/// * `value`        - The value to hash.
pub(crate) fn make_hash<K, Q, S>(hash_builder: &S, value: &Q) -> u64
where
    K: Borrow<Q>,
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    let mut hasher = hash_builder.build_hasher();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Implementation of a hasher which hashes using murmur.
pub struct MurmurHasher(u64);

impl Default for MurmurHasher {
    #[inline]
    fn default() -> MurmurHasher {
        MurmurHasher(0)
    }
}

impl Hasher for MurmurHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut v = load_u64_le(bytes, bytes.len());
        v ^= v >> 33;
        v = v.wrapping_mul(0xff51afd7ed558ccd);
        v ^= v >> 33;
        v = v.wrapping_mul(0xc4ceb9fe1a85ec53);
        v ^= v >> 33;
        *self = MurmurHasher(v);
    }
}

/// Implementaion of hasher which hashes using FNV (Fowler-Noll-Vo).
pub struct FnvHasher(u64);

impl Default for FnvHasher {
    #[inline]
    fn default() -> FnvHasher {
        FnvHasher(0xcbf29ce484222325)
    }
}

impl Hasher for FnvHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let FnvHasher(mut hash) = *self;

        for byte in bytes.iter() {
            hash = hash ^ (*byte as u64);
            hash = hash.wrapping_mul(0x100000001b3);
        }

        *self = FnvHasher(hash);
    }
}

// This is not really a hasher, it just returns the value to be hashed, however,
// if it's known that the key is unique, it might be useful in such a scenario.
pub struct SimpleHasher(u64);

impl Default for SimpleHasher {
    #[inline]
    fn default() -> SimpleHasher {
        SimpleHasher(0)
    }
}

impl Hasher for SimpleHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        *self = SimpleHasher(load_u64_le(bytes, bytes.len()));
    }
}
