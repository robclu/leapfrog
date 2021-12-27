//==----------------------------------------------------------- ------------==//
//                                  Flame
//                      Copyright (c) 2021 Rob Clucas
//      This file is distributed under the APACHE License, Version 2.0.
//                         See LICENSE for details.
//==------------------------------------------------------------------------==//

//! Module for a single threaded hash map which uses a leapfrog probing strategy.

use crate::util::round_to_pow2;
use crate::{make_hash, MurmurHasher, Value};
use std::{
    borrow::Borrow,
    default::Default,
    hash::{BuildHasher, BuildHasherDefault, Hash, Hasher},
};

/// The type used for hashed keys.
pub(crate) type HashedKey = u64;

/// Struct which stores a cell in a hash map. A cell is simply a hash (rather
/// than the key iteself) and the value associated with the key for which the
/// hash is associated.
#[derive(Clone, Copy)]
struct Cell<V: Value> {
    /// The hashed value of the cell.
    hash: HashedKey,
    /// The value assosciated with the hash.
    value: V,
}

impl<V: Value> Default for Cell<V> {
    fn default() -> Cell<V> {
        Cell {
            hash: HashedKey::default(),
            value: V::default(),
        }
    }
}

/// Struct which stores buckets of cells. Each bucket stores four cells
/// and two delta values per cell. The first delta value for a cell provides
/// the offset to the cell which is the start of the probe chain for the cell.
/// The second delta value provides the offset to the next link in the probe
/// chain once a search along the probe chain has started.
#[derive(Clone)]
struct Bucket<K, V: Value> {
    /// Delta values for the cells. The first 4 values are the delta values to
    /// the start of the probe chain, and the second 4 values are the delta
    /// values to the next probe in the chain, for each cell, respectively.
    deltas: [u8; 8],
    /// Cells for the bucket.
    cells: [Cell<V>; 4],
    /// Placeholder for the key
    _key: std::marker::PhantomData<K>,
}

impl<K, V: Value> Default for Bucket<K, V> {
    fn default() -> Bucket<K, V> {
        Bucket {
            deltas: [0u8; 8],
            cells: [Cell::<V>::default(); 4],
            _key: std::marker::PhantomData::default(),
        }
    }
}

/// Defines the result of an insert into the [HashMap].
enum InsertResult<V> {
    /// The insertion found a cell for the key, replaced the old value with
    /// a new one, and returned the old value.
    Found(V),
    /// The insertion was performed with a new key, so a new cell was filled.
    NewInsert,
    /// No new cell was found for the key withing the linear search range,
    /// so we overflowed the max delta value and need to move the map to
    /// a larger table.
    Overflow(usize),
}

/// A HashMap implementation which uses a modified form of RobinHood/Hopscotch
/// probing. This implementation is efficient, roughly 2x the performance of
/// the default hash map *when using a the same fast hasher*, and a lot more
/// when using the default hasher. It has also been benchmarked to be as fast/
/// faster than other hashmaps which are known to be very efficient. The
/// implementation is also fully safe.
///
/// # Limitations
///
/// This hash map *does not* store keys, so if that is required, then another
/// map would be better. This does, however, save space when the key is large.
///
/// Currently, moving the table *does not* use a custom allocator, which would
/// further improve the implementation.
///
/// The number of elements in the map must be a power of two.
///
/// # Threading
///
/// This version is *not* thread-safe. However, the extension to the thread-safe
/// version is relatively straight forward, see [flame::collections::ConcurrentHashMap].
pub struct HashMap<K, V: Value, H = BuildHasherDefault<MurmurHasher>> {
    /// Groups of cells which store the map data.
    buckets: Vec<Bucket<K, V>>,
    /// The hasher for the map.
    hash_builder: H,
    /// Mask for the size of the table.
    size_mask: usize,
}

impl<K, V, H> HashMap<K, V, H>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + Default,
{
    /// The default initial size of the map.
    const INITIAL_SIZE: usize = 8;

    /// The max number of elements to search through when having to fallback
    /// to using linear search to try to find a cell.
    const LINEAR_SEARCH_LIMIT: usize = 128;

    /// The number of cells to use to estimate if the map is full.
    const CELLS_IN_USE: usize = Self::LINEAR_SEARCH_LIMIT >> 1;

    /// Number of cells per bucked.
    const CELLS_PER_BUCKET: usize = 4;

    /// Creates the hash map with space for the default number of elements.
    pub fn new() -> HashMap<K, V, H> {
        HashMap {
            buckets: Self::create_buckets(Self::INITIAL_SIZE),
            hash_builder: H::default(),
            size_mask: Self::INITIAL_SIZE - 1,
        }
    }

    /// Creates the hash map with space for `size` number of key-value pairs.
    ///
    /// # Assertations
    ///
    /// This will assert if `size` is not a power of two.
    ///
    /// # Arguments
    ///
    /// * `size`         - The initial number of elements for the map.
    pub fn with_capacity(size: usize) -> HashMap<K, V, H> {
        assert!(size % 2 == 0);

        HashMap {
            buckets: Self::create_buckets(size),
            hash_builder: H::default(),
            size_mask: size - 1,
        }
    }

    /// Creates the hash map with space for `size` number of key-value pairs,
    /// and with the `builder` to use to build a hasher.
    ///
    /// # Assertations
    ///
    /// This will assert if `size` is not a power of two.
    ///
    /// # Arguments
    ///
    /// * `size`         - The initial number of elements for the map.
    /// * `hash_builder` - The builder to create a hasher with.
    pub fn with_capacity_and_hasher(size: usize, builder: H) -> HashMap<K, V, H> {
        assert!(size % 2 == 0);

        HashMap {
            buckets: Self::create_buckets(size),
            hash_builder: builder,
            size_mask: size - 1,
        }
    }

    /// Returns the capacity of the map. This is the number of elements that
    /// that map can hold without having to resize/reallocate. It may be able
    /// to hold more, but it can hold *at least* this many.
    pub fn capacity(&self) -> usize {
        self.buckets.capacity() * Self::CELLS_PER_BUCKET
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, None is returned.
    ///
    /// If the map did have this key present, the value is updated and the old
    /// value is returned.
    ///
    /// # Arguments
    ///
    /// * `key`   - The key to use to insert the value into the map.
    /// * `value` - The value to insert into the map for the key.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let mut state = self.hash_builder.build_hasher();
        key.hash(&mut state);
        let hash = state.finish();
        loop {
            match Self::insert_or_find(hash, value, &mut self.buckets, self.size_mask) {
                InsertResult::Overflow(overflow_index) => {
                    // Resize and move into a new map, then try again.
                    // If this happens on the first iteration, then deleted cells
                    // will be removed.
                    // If this happens on the second iteration, this will double
                    // the size of the map.
                    // If this happens on the third iteration, the insert will
                    // succeed.
                    self.move_to_new_buckets(overflow_index);
                }
                InsertResult::Found(old_value) => {
                    return Some(old_value);
                }
                InsertResult::NewInsert => {
                    return None;
                }
            }
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to get the value for.
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.find(make_hash::<K, Q, H>(&self.hash_builder, &key))
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Argumentts
    ///
    /// * `key` - The key for which to get a mutable reference to the value.
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let size_mask = self.size_mask;
        let buckets = &mut self.buckets;
        let hash = make_hash::<K, Q, H>(&self.hash_builder, key);
        Self::find_mut(buckets, hash, size_mask)
    }

    /// Returns true if the map contains the key.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to determine if is in the map.
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get(key).is_some()
    }

    /// Removes the item assosciated with the key.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to remove the value for.
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        // Here, we could shuffle the existing cells so that the gaps left
        // by this cell are filled in. However, we rather just leave them as
        // deleted, and the next time the map is resized they will be removed.
        if let Some(v) = self.get_mut(key) {
            let old_value = *v;
            *v = V::default();
            Some(old_value)
        } else {
            None
        }
    }

    /// Inserts a new cell into the given `buckets`, where the max number of
    /// buckets is `size_mask` + 1.
    ///
    /// # Arguments
    ///
    /// * `hash`      - The hash value to use to find a cell.
    /// * `value`     - The value to insert into the buckets.
    /// * `buckets`   - The buckets to insert the hash into.
    /// * `size_mask` - The size mask for number of elements in the buckets.
    ///
    /// # Returns
    ///
    /// This returns an [InsertResult] which specifies what happened during
    /// the insertion procedure.
    ///
    /// If the hash was found in the map, then  [InsertResult::Found] will be
    /// returned with the value set to the old value for the found cell.
    ///
    /// If the hash was not found, then [InsertResult::NewInsert] will be returned
    /// to specify that the hash was newly inserted.
    ///
    /// If the hash was not found in the map, and it was not possible to insert
    /// the hash into the map, then [InsertResult::Overflow] will be returned
    /// with the index of the overflow.
    fn insert_or_find(
        hash: HashedKey,
        value: V,
        buckets: &mut Vec<Bucket<K, V>>,
        size_mask: usize,
    ) -> InsertResult<V> {
        let mut index = hash as usize;
        {
            let cell = Self::get_cell_mut(buckets, index, size_mask);
            if cell.hash == hash {
                let old_value = cell.value;
                cell.value = value;
                return InsertResult::Found(old_value);
            } else if cell.hash == HashedKey::default() {
                cell.hash = hash;
                cell.value = value;
                return InsertResult::NewInsert;
            }
        }

        // Here, we get the offset delta which will allow us to find the desired
        // bucket. After that, we need to use the second set of delta values to
        // walk along the chain. At each point, we check if the hash is a match;
        // if we find a match, then we have found the cell.
        let mut delta = Self::get_first_delta(buckets, index, size_mask);
        let first_delta = if delta == 0 { true } else { false };
        while delta != 0 {
            index += delta as usize;
            delta = Self::get_second_delta(buckets, index, size_mask);

            let mut cell = Self::get_cell_mut(buckets, index, size_mask);
            if cell.hash == hash {
                let old_value = cell.value;
                cell.value = value;
                return InsertResult::Found(old_value);
            }
        }

        // If we are here, then we have reached the end of the chain for this
        // bucket. The key does not exist, so we switch here to linear probing
        // to find a free cell to insert into.
        let max_index = index + size_mask;
        debug_assert!(max_index as i64 - index as i64 >= 0);

        let prev_link_index = index;
        let mut probes_remaining = Self::LINEAR_SEARCH_LIMIT.min(max_index - index);
        while probes_remaining > 0 {
            index += 1;

            // We found an empty cell, so reserve it and link it
            // to the previous cell in the same bucket.
            let mut cell = Self::get_cell_mut(buckets, index, size_mask);
            if cell.hash == HashedKey::default() {
                cell.hash = hash;
                cell.value = value;

                let offset = (index - prev_link_index) as u8;
                if first_delta {
                    *Self::get_first_delta_mut(buckets, prev_link_index, size_mask) = offset;
                } else {
                    *Self::get_second_delta_mut(buckets, prev_link_index, size_mask) = offset;
                }
                return InsertResult::NewInsert;
            }

            // This is single threaded map, so it's impossible for the hash
            // which is a match to appear outside of the probe chain.
            debug_assert!(cell.hash != hash);
            probes_remaining -= 1;
        }

        // Table is too full, we need to grow it.
        InsertResult::Overflow(index + 1)
    }

    /// Tries to find the value for the `hash`, without inserting into the map.
    /// This will reuturn a Some(&v) if the find succeeded, otherwise this will
    /// return None.
    ///
    /// # Arguments
    ///
    /// * `hash` - The hashed value to find.
    fn find(&self, hash: HashedKey) -> Option<&V> {
        debug_assert!(hash != HashedKey::default());

        let mut index = hash as usize;
        let cell = Self::get_cell(&self.buckets, index, self.size_mask);
        if cell.hash == hash {
            return Some(&cell.value);
        }

        // Now we need to follow the probe chain for the bucket.
        let mut delta = Self::get_first_delta(&self.buckets, index, self.size_mask);
        while delta != 0 {
            index += delta as usize;
            let cell = Self::get_cell(&self.buckets, index, self.size_mask);
            if cell.hash == hash {
                return Some(&cell.value);
            }

            delta = Self::get_second_delta(&self.buckets, index, self.size_mask);
        }

        None
    }

    /// Tries to find the value for the `hash` without inserting into the
    /// `buckets`. This will reuturn a Some(&mut v) if the find succeeded,
    /// otherwise this will return None.
    ///
    /// # Arguments
    ///
    /// * `buckets`   - The buckets in which to look for the hash.
    /// * `hash`      - The hash to look for in the buckets.
    /// * `size_mask` - Mask for the total number of cells in the buckets.
    fn find_mut(
        buckets: &mut Vec<Bucket<K, V>>,
        hash: HashedKey,
        size_mask: usize,
    ) -> Option<&mut V> {
        debug_assert!(hash != HashedKey::default());

        let mut index = hash as usize;
        let mut delta = 0u8;
        let mut found = false;

        if Self::get_cell(buckets, index, size_mask).hash == hash {
            found = true;
        } else {
            delta = Self::get_first_delta(buckets, index, size_mask);
        }

        // If we have found the correct hash, then we will just skip this,
        // otherwise we need to search the probe chain and see if we find
        // something
        while !found && delta != 0 {
            index += delta as usize;
            if Self::get_cell(buckets, index, size_mask).hash == hash {
                found = true;
                break;
            }
            delta = Self::get_second_delta(buckets, index, size_mask);
        }

        if found {
            Some(&mut Self::get_cell_mut(buckets, index, size_mask).value)
        } else {
            None
        }
    }

    /// Moves the current map buckets into a larger container of buckets.
    ///
    /// # Arguments
    ///
    /// * `overflow_index` - The index at which an attempt to insert would have
    ///                      overflowed the delta value.
    fn move_to_new_buckets(&mut self, overflow_index: usize) {
        // Estimate the number of cells
        let mut index = overflow_index - Self::CELLS_IN_USE;
        let mut cells_in_use = 0;

        for _ in 0..Self::CELLS_IN_USE {
            let cell = Self::get_cell(&self.buckets, index, self.size_mask);
            if cell.value != V::default() {
                cells_in_use += 1;
            }
            index += 1;
        }

        // Estimate how much we need to resize by:
        let ratio = cells_in_use as f32 / Self::CELLS_IN_USE as f32;
        let in_use_estimated = (self.size_mask + 1) as f32 * ratio;
        let estimated = round_to_pow2((in_use_estimated * 2.0) as usize);
        let mut new_table_size = estimated.max(Self::INITIAL_SIZE as usize);

        loop {
            if self.try_move_to_new_buckets(new_table_size) {
                return; // Succeeded, we can return
            }

            // Increase the size and try again. It's currently expensive to
            // try to move the buckets to new buckets, however, this very
            // rarely happens.
            new_table_size *= 2;
        }
    }

    /// Tries to move the current map buckets into new buckets to support `size`
    /// number of elements in the map.
    ///
    /// # Limitations
    ///
    /// Currently this doesn't use a custom allocator, which needs to be changed
    /// to improve performance.
    ///
    /// # Argments
    ///
    /// * `size` - The number of elements in the new map.
    fn try_move_to_new_buckets(&mut self, size: usize) -> bool {
        let source_size = self.size_mask + 1;
        let size_mask = size - 1;

        // This is very bad for performance, we need to allocate this from
        // somewhere else ...
        let mut buckets = Self::create_buckets(size);

        for source_index in 0..source_size {
            let cell = Self::get_cell(&self.buckets, source_index, self.size_mask);
            if cell.value != V::default() {
                match Self::insert_or_find(cell.hash, cell.value, &mut buckets, size_mask) {
                    InsertResult::Overflow(_) => {
                        // New bucekts are too small, failed to move.
                        // New buckets will be automatically cleaned up
                        return false;
                    }
                    InsertResult::Found(_) => {
                        // Shouldn't find a value in the new table ...
                        debug_assert!(false);
                    }
                    InsertResult::NewInsert => {
                        // Success, continue ...
                    }
                }
            }
        }

        // Succeeded in moving all buckets, so update the map:
        self.buckets = buckets;
        self.size_mask = size_mask;

        true
    }

    /// Creates buckets with sufficient space for `size` buckets.
    ///
    /// FIXME: This needs to get the data from some other allocator, because
    ///        we can't be allocting all the time.
    fn create_buckets(size: usize) -> Vec<Bucket<K, V>> {
        // Check that the size is a power of two:
        debug_assert!(size >= 4 && (size & (size - 1)) == 0);

        // Each bucket holds 4 cells, hence division by 4.
        vec![Bucket::<K, V>::default(); size >> 2]
    }

    /// Gets a reference to a cell for the `index` from the `buckets`.
    ///
    /// # Arguments
    ///
    /// * `buckets`   - The buckets to find the cell in.
    /// * `index`     - The raw index value to convert to a bucket and cell index.
    /// * `size_mask` - A mask for the number of elements in the buckets.
    #[inline]
    fn get_cell(buckets: &Vec<Bucket<K, V>>, index: usize, size_mask: usize) -> &Cell<V> {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        &buckets[bucket_index].cells[cell_index]
    }

    /// Gets a mutable reference mutable to a cell for the `index` from the
    /// `buckets`.
    ///
    /// * `buckets`   - The buckets to find the cell in.
    /// * `index`     - The raw index value to convert to a bucket and cell index.
    /// * `size_mask` - A mask for the number of elements in the buckets.
    #[inline]
    fn get_cell_mut(
        buckets: &mut Vec<Bucket<K, V>>,
        index: usize,
        size_mask: usize,
    ) -> &mut Cell<V> {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        &mut buckets[bucket_index].cells[cell_index]
    }

    /// Gets the first delta value for a cell with the given `index`. The first
    /// delta value gives the offset to the start of the probe chain for bucket
    /// assosciated with the `index`.
    ///
    /// # Arguments
    ///
    /// * `buckets`   - The buckets to find the cell in.
    /// * `index`     - The raw index value to convert to a bucket and cell index.
    /// * `size_mask` - A mask for the number of elements in the buckets.
    #[inline]
    fn get_first_delta(buckets: &Vec<Bucket<K, V>>, index: usize, size_mask: usize) -> u8 {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        buckets[bucket_index].deltas[cell_index]
    }

    /// Gets a mutable reference to the first delta value for a cell with the
    /// given `index`. The first delta value gives the offset to the start of
    /// the probe chain for bucket assosciated with the `index`.
    ///
    /// * `buckets`   - The buckets to find the cell in.
    /// * `index`     - The raw index value to convert to a bucket and cell index.
    /// * `size_mask` - A mask for the number of elements in the buckets.
    #[inline]
    fn get_first_delta_mut(
        buckets: &mut Vec<Bucket<K, V>>,
        index: usize,
        size_mask: usize,
    ) -> &mut u8 {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        &mut buckets[bucket_index].deltas[cell_index]
    }

    /// Gets the second delta value for a cell with the given `index`. The
    /// second delta value gives the offset to the next probe in a probe chain
    /// for a given cell.
    ///
    /// # Arguments
    ///
    /// * `buckets`   - The buckets to find the cell in.
    /// * `index`     - The raw index value to convert to a bucket and cell index.
    /// * `size_mask` - A mask for the number of elements in the buckets.
    #[inline]
    fn get_second_delta(buckets: &Vec<Bucket<K, V>>, index: usize, size_mask: usize) -> u8 {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        buckets[bucket_index].deltas[cell_index + 4]
    }

    // Gets the second delta value for a cell with the given index.

    /// Gets a mutable reference to the second delta value for a cell with the
    /// given `index`. The second delta value gives the offset to the next probe
    /// in a probe chain for a given cell.
    ///
    /// # Arguments
    ///
    /// * `buckets`   - The buckets to find the cell in.
    /// * `index`     - The raw index value to convert to a bucket and cell index.
    /// * `size_mask` - A mask for the number of elements in the buckets.
    #[inline]
    fn get_second_delta_mut(
        buckets: &mut Vec<Bucket<K, V>>,
        index: usize,
        size_mask: usize,
    ) -> &mut u8 {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        &mut buckets[bucket_index].deltas[cell_index + 4]
    }

    /// Gets the index of the bucket for the `index`.
    ///
    /// # Arguments
    ///
    /// * `index`     - The raw index to get the index of the bucket for.
    /// * `size_mask` - A mask for the total number of cells in the map.
    #[inline]
    const fn get_bucket_index(index: usize, size_mask: usize) -> usize {
        (index & size_mask) >> 2
    }

    /// Gets the index of the cell within a bucket for the `index`.
    ///
    /// # Arguments
    ///
    /// * `index`     - The raw index to get the index of the cell for.
    /// * `size_mask` - A mask for the total number of cells in the map.
    #[inline]
    const fn get_cell_index(index: usize) -> usize {
        index & 3
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{thread_rng, Rng};

    const KEYS_TO_INSERT: usize = 2048;

    #[test]
    fn create_hash_map() {
        const ELEMENTS: usize = 8;
        let map = HashMap::<u32, u32>::with_capacity(ELEMENTS);

        assert!(map.capacity() >= ELEMENTS);
    }

    #[test]
    fn hash_map_key_insert() {
        let mut map = HashMap::<u64, u64>::with_capacity(KEYS_TO_INSERT);

        let mut rng = thread_rng();
        let start_index: u32 = rng.gen();
        let value: u32 = rng.gen();
        let relative_prime: u64 = value as u64 * 2 + 1;

        let mut inserted: usize = 0;
        let mut index = start_index;
        let mut insert_checksum = 0u64;
        while inserted < KEYS_TO_INSERT {
            let mut key: u64 = (index as u64).wrapping_mul(relative_prime);
            key = key ^ (key >> 16);

            // Don't add keys which are 0 or 1
            if key >= 2 {
                // Map is empty, we should only have None here:
                if let Some(_old) = map.insert(key, key) {
                    assert!(false);
                }
                inserted += 1;
                insert_checksum = insert_checksum.wrapping_add(key);
            }
            index += 1;
        }

        let mut removed: usize = 0;
        let mut index = start_index;
        let mut remove_checksum = 0u64;
        while removed < KEYS_TO_INSERT {
            let mut key: u64 = (index as u64).wrapping_mul(relative_prime);
            key = key ^ (key >> 16);

            if key >= 2 {
                if let Some(value) = map.get(&key) {
                    assert!(*value == key);
                    remove_checksum = remove_checksum.wrapping_add(key);
                    removed += 1;
                } else {
                    assert!(false);
                }

                // Check get mut as well
                if let Some(value) = map.get_mut(&key) {
                    assert!(*value == key);
                } else {
                    assert!(false);
                }
            }
            index += 1;
        }

        assert_eq!(insert_checksum, remove_checksum);
        assert_eq!(inserted, removed);

        // TODO: Add check for iterator usage.
    }
}
