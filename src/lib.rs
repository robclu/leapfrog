//! A concurrent hash table which uses leapfrog probing. This map is also lock-free
//! **if** the key and value support atomic operations. If not, an efficient spin-lock
//! is used instead.
//!
//! All operations on a [`LeapMap`] can be used concurrently with each other, and
//! the map is both fast and scalable up to many threads. The interface for the map
//! has been kept as close as possible to `std::collections::HashMap`, however,
//! there are some differences to ensure that concurrent operations are always correct
//! without decreasing performance.
//!
//! The biggest differences between the interface of the [`LeapMap`] and the
//! `std::collections::HashMap` are the types returned by `get` and `get_mut`.
//! For the [`LeapMap`], these methods return [`Ref`] and [`RefMut`] types,
//! respectively, whose interfaces are designed to allow for accessing the cells
//! returned by the those methods concurrently and correctly. As a result, it is
//! not possible to get a reference to a cell's value, since the cell value type
//! is atomic. The cell's key, value, and key-value pairs can be accessed with
//! `key`, `value`, and `key_value` methods, respectively for [`Ref`] and
//! [`RefMut`] types. For the [`RefMut`] type, the value can additionally be
//! modified with `set_value` or `update`. These interfaces ensure that the most
//! up to date value is loaded/stored/updated, and that if the referenced cell is
//! invalidated/updated/erased by other threads, the [`Ref`]/[`RefMut`] type is
//! updated appropriately. This makes working concurrently with the map simple,
//! without sacrificing performance.
//!
//! The map uses [leapfrog probing](https://preshing.com/20160314/leapfrog-probing/)
//! which is similar to [hopscotch hashing](https://en.wikipedia.org/wiki/Hopscotch_hashing)
//! since it is based off of it. Leapfrog probing stores two offset per
//! cell which are used to traverse a local neighbourhood of values
//! around the cell to which a key hashes. This makes the map operations cache
//! friendly and scalable, even under heavy contention. Keys are also stored,
//! and to allow the [`LeapMap`] to still be efficient the hash of a key is also
//! stored, which adds 8 bytes of overhead per key-value pair. This can very likely
//! be improved, but this map is still in its early stages. The [`LeapMap`] is
//! designed for performance so if memory efficiency is more important, a different
//! map is likely a better choice.
//!
//! # HashMap
//!
//! This crate also provides [`HashMap`], which is an fast single-threaded
//! version of the concurrent lock-free hash map, whose performance is roughly
//! 1.2-1.5x the hash map implementation in the standard library, when using the
//! same hash function. The tradeoff that is currently made to enable this performance
//! is increased memory use, since the map stores the offsets (8 bytes) and the
//! hashed value for a key (8 bytes). This may make the map unsuitable for some
//! use cases.
//!
//! # Hash Functions
//!
//! By default, the default hash function from the standard library is used for
//! both the [`HashMap`] and the [`LeapMap`], since it is DOS resistant. It is,
//! however, more expensive to evaluate. The [`MurmurHasher`] can be used instead,
//! which is quite a bit faster but which is **not** DOS resistant. Additionally, the
//! default initialization of the [`HashMap`] and [`LeapMap`] data requires that
//! 0 not be used as a key for the map *if the [`MurmurHasher`] is used*. With the
//! default hasher this limitation does not apply. Any other hash functions can
//! be used by creating the maps with `with_hasher` or `with_capacity_and_hasher`.
//!
//! # Performance
//!
//! This map has been benchmarked against other hash maps across multiple threads
//! and multiple workloads. The benchmarks can be found [here](https://github.com/robclu/conc-map-bench).
//! A snapshot of the results for a read heavy workload are the following (with
//! throughput in Mops/second, cores in brackets, and performance realtive to
//! `std::collections::HashMap` with RwLock). While these benchmarks show good
//! performance, **please take note of the limitations described above**, and
//! benchmark for your use case. Please also create an issue if there are either
//! correctness or performance problems for a specific use case. For a read heavy
//! workload on 16 cores the following was benchmarked:
//!
//! | Map              | Throughput (1) | Relative (1) | Throughput (16) | Relative (16) |
//! |------------------|----------------|--------------|-----------------|---------------|
//! | RwLock + HashMap | 19.4           | 1.0          | 11.7            | 0.60          |
//! | Flurry           | 11.2           | 0.58         | 80.8            | 4.16          |
//! | DashMap          | 14.1           | 0.72         | 87.5            | 4.51          |
//! | LeapMap          | 17.8           | 0.92         | 148.0           | 7.62          |
//!
//! On an exchange heavy benchmark, the leapmap was even faster.
//! The performance of the [`LeapMap`] is limited is when rapidly growing the map, since
//! the bottleneck then becomes the resizing (allocation) and migration operations.
//! The map **is not** designed to be resized often (resizing infrequently has very
//! little impact on performance, however), so it's best to use an initial capacity
//! which is close to the expected maximum number of elements for the map. The growing
//! performace is slightly worse than DashMap's growing performance (see the
//! benchmarks). If resizing is frequent, this map is currently not the best choice,
//! however, this can be improved by using a more efficient allocator.
//!
//! # Consistency
//!
//! All operations on a [`LeapMap`] map are non-blocking, and accessing/updating
//! a value in the map will not lock **if the value type has built-in atomic support**.
//! The map can be iterated (mutable or immutably) from multiple threads while
//! concurrently calling the operations directly on the map from other threads.
//!
//! # Limitations
//!
//! Getting the length of the map does not return the length of the map, but rather an
//! estimate of the length, unless the calling thread is the only thread operating
//! on the map, and therefore there are no other readers or writers. Additionally,
//! the length is expensive to compute since it is not tracked as insertions and
//! removals are performed. The overhead of doing so when under contention
//! was found to be significant during benchmarking, and given that it's only an
//! estimate, it's not worth the cost.
//!
//! The same applies for `is_empty`.
//!
//! The size of the map must always be a power of two. This is handled internally
//! and may change in the future to improve memory efficiency.
//!
//! The value type for the map needs to implement the [`Value`] trait, which is
//! simple enough to implement, however, two values need to be chosen: one as a
//! null value and another as a redirect value. For integer types MAX and MAX-1
//! are used respectively. A good choice is values which are efficient for
//! comparison.
//!
//! # Resizing
//!
//! The buckets for the map are expanded when an insertion would result in a
//! offset which would overflow the maximum probe offset (i.e when it's not
//! possible to find an empty cell within the probe neighbourhood), or shrunk
//! when probes are too far apart. The resizing and subsequent removal of buckets
//! from the old table to the new table will happen concurrently when multiple
//! threads are attempting to modify the map, which makes the reszing
//! efficient. Despite this, it is best to choose a larger size where possible,
//! since it will ensure more stable performance of map operations. When the table
//! is resized, the old memory is cleanup up using what is essentially a quescient
//! based reclaimation strategy.
//!
//! # Features
//!
//! There is optional support for serde, via the "serde" feature.

#![feature(allocator_api)]
#![feature(const_fn_trait_bound)]

mod hashentry;
mod hashiter;
pub mod hashmap;
mod leapiter;
pub mod leapmap;
pub mod leapref;
pub mod util;

#[cfg(feature = "serde")]
mod hashmap_serde;

#[cfg(feature = "serde")]
mod leapmap_serde;

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
pub trait Value: Sized + Debug + Clone + Copy {
    /// Must return true if the value is the redirect value.
    fn is_redirect(&self) -> bool;

    /// Returns true if the value is a null value.
    fn is_null(&self) -> bool;

    /// Returns the redirect value.
    fn redirect() -> Self;

    /// Returns the null value.
    fn null() -> Self;
}

macro_rules! value_impl {
    ($type:ty, $redirect_expr:expr, $null_expr:expr) => {
        impl Value for $type {
            #[inline]
            fn is_redirect(&self) -> bool {
                *self == $redirect_expr
            }
            #[inline]
            fn is_null(&self) -> bool {
                *self == $null_expr
            }
            #[inline]
            fn redirect() -> Self {
                $redirect_expr
            }
            #[inline]
            fn null() -> Self {
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
#[derive(Default)]
pub struct MurmurHasher(u64);

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
#[derive(Default)]
pub struct SimpleHasher(u64);

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
