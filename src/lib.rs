//==----------------------------------------------------------- ------------==//
//                                  Flame
//                      Copyright (c) 2021 Rob Clucas
//      This file is distributed under the APACHE License, Version 2.0.
//                         See LICENSE for details.
//==------------------------------------------------------------------------==//

//! Module for hash related functionality, such as efficient hash functions,
//! and single-threaded and concurrent hash maps.

#![feature(allocator_api)]
#![feature(const_fn_trait_bound)]

pub mod hashmap;
pub mod leapfrogmap;
mod util;

use crate::util::load_u64_le;
use std::borrow::Borrow;
use std::{
    default::Default,
    fmt::Debug,
    hash::{BuildHasher, Hash, Hasher},
};

pub use hashmap::HashMap;

/// Trait which represents a value which can be stored in a map.
pub trait Value: Default + Debug + Sized + PartialEq + Clone + Copy {
    /// Returns the null value for the value.
    fn null() -> Self;

    /// Returns the value used for redirection.
    fn redirect() -> Self;
}

impl Value for u32 {
    fn null() -> u32 {
        u32::default()
    }

    fn redirect() -> u32 {
        u32::MAX
    }
}

impl Value for u64 {
    fn null() -> u64 {
        u64::default()
    }

    fn redirect() -> u64 {
        u64::MAX
    }
}

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
