use crate::hashiter::{Iter, IterMut, OwnedIter};
use crate::util::{allocate, deallocate, round_to_pow2, AllocationKind};
use crate::{make_hash, Value};
use core::alloc::Allocator;
use core::{
    borrow::Borrow,
    default::Default,
    hash::{BuildHasher, BuildHasherDefault, Hash, Hasher},
};
use std::alloc::Global;

// Re export the entry api.
pub use crate::hashentry::{Entry, OccupiedEntry, VacantEntry};

/// The default hasher for a [`HashMap`].
pub(crate) type DefaultHash = std::collections::hash_map::DefaultHasher;

/// A [`HashMap`] implementation which uses a modified form of RobinHood/Hopscotch
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
/// This version is *not* thread-safe. [`LeapMap`] is a thread-safe version of
/// the map.
pub struct HashMap<K, V, H = BuildHasherDefault<DefaultHash>, A: Allocator = Global> {
    /// Table for the map.
    table: *mut Table<K, V>,
    /// The hasher for the map.
    hash_builder: H,
    /// Allocator for the buckets.
    allocator: A,
    /// The number of elements in the map.
    size: usize,
}

impl<'a, K, V, H, A: Allocator> HashMap<K, V, H, A> {
    /// Gets the capacity of the hash map.
    pub fn capacity(&self) -> usize {
        self.get_table().size()
    }

    /// Gets a reference to the map's table, using the specified `ordering` to
    /// load the table reference.
    fn get_table(&self) -> &'a Table<K, V> {
        unsafe { &*self.table }
    }

    /// Gets a mutable reference to the map's table, using the specified
    /// `ordering` to load the table reference.
    fn get_table_mut(&self) -> &'a mut Table<K, V> {
        unsafe { &mut *self.table }
    }

    /// Returns true if the hash map has been allocated.
    fn is_allocated(&self) -> bool {
        !self.table.is_null()
    }
}

impl<K, V> HashMap<K, V, BuildHasherDefault<DefaultHash>, Global>
where
    K: Eq + Hash + Clone,
    V: Value,
{
    /// Creates the hash map with space for the default number of elements, which
    /// will use the global allocator for allocation of the map data.
    pub fn new() -> HashMap<K, V, BuildHasherDefault<DefaultHash>, Global> {
        Self::new_in(Global)
    }

    /// Creates the hash map with space for `capacity` elements, which will use
    /// the global allocator for allocation of the map data.
    pub fn with_capacity(
        capacity: usize,
    ) -> HashMap<K, V, BuildHasherDefault<DefaultHash>, Global> {
        Self::with_capacity_and_hasher_in(
            capacity,
            BuildHasherDefault::<DefaultHash>::default(),
            Global,
        )
    }
}

impl<K, V, H> HashMap<K, V, H, Global>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + Default,
{
    /// Creates the hash map with space for `capacity` elements, using the
    /// `builder` to create the hasher, which will use the global allocator for
    /// allocation of the map data.
    pub fn with_capacity_and_hasher(capacity: usize, builder: H) -> HashMap<K, V, H, Global> {
        Self::with_capacity_and_hasher_in(capacity, builder, Global)
    }
}

impl<'a, K, V, H, A> HashMap<K, V, H, A>
where
    K: Eq + Hash + Clone + 'a,
    V: Value + 'a,
    H: BuildHasher + Default,
    A: Allocator,
{
    /// The default initial size of the map.
    const INITIAL_SIZE: usize = 8;

    /// The max number of elements to search through when having to fallback
    /// to using linear search to try to find a cell.
    const LINEAR_SEARCH_LIMIT: usize = 128;

    /// The number of cells to use to estimate if the map is full.
    const CELLS_IN_USE: usize = Self::LINEAR_SEARCH_LIMIT >> 1;

    /// Creates the hash map with space for the default number of elements, using
    /// the provided `allocator` to allocate data for the map.
    pub fn new_in(allocator: A) -> HashMap<K, V, H, A> {
        Self::with_capacity_and_hasher_in(Self::INITIAL_SIZE, H::default(), allocator)
    }

    /// Creates the hash map with space for the `capacity` number of elements
    /// using the provided `builder` to build the hasher, and `allocator` for
    /// allocating the map data.
    pub fn with_capacity_and_hasher_in(
        capacity: usize,
        builder: H,
        allocator: A,
    ) -> HashMap<K, V, H, A> {
        let capacity = round_to_pow2(capacity.max(Self::INITIAL_SIZE));
        let table = Self::allocate_and_init_table(&allocator, capacity);
        HashMap {
            table,
            hash_builder: builder,
            allocator,
            size: 0,
        }
    }

    /// Returns the hashed value for the `key` as usize.
    pub fn hash_usize<Q: ?Sized>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        make_hash::<K, Q, H>(&self.hash_builder, key) as usize
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated and the old
    /// value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::new();
    /// assert_eq!(map.insert(37, 12), None);
    /// assert_eq!(map.insert(37, 14), Some(12));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let mut state = self.hash_builder.build_hasher();
        key.hash(&mut state);
        let hash = state.finish();
        debug_assert!(hash != null_hash());
        loop {
            let size_mask = self.get_table().size_mask;
            let buckets = self.get_table_mut().bucket_slice_mut();
            match Self::insert_or_find(hash, &key, value, buckets, size_mask) {
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
                    self.size += 1;
                    return None;
                }
            }
        }
    }

    /// Returns an optional reference type to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::new();
    /// map.insert(0, 12);
    /// if let Some(value) = map.get(&0) {
    ///     assert_eq!(*value, 12);
    /// }
    /// assert!(map.get(&2).is_none());
    ///```
    pub fn get<Q: ?Sized>(&'a self, key: &Q) -> Option<&'a V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.find(make_hash::<K, Q, H>(&self.hash_builder, key), key)
            .and_then(|(_k, v)| if v.is_null() { None } else { Some(v) })
    }

    /// Returns a mutable reference type to the value corresponding to the `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::new();
    /// map.insert(1, 12);
    /// if let Some(value) = map.get_mut(&1) {
    ///     *value = 14;
    /// }
    /// assert_eq!(*map.get(&1).unwrap(), 14);
    /// assert!(map.get(&2).is_none());
    ///```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&'a mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let table = self.get_table_mut();
        let size_mask = table.size_mask;
        let buckets = table.bucket_slice_mut();
        let hash = make_hash::<K, Q, H>(&self.hash_builder, key);
        Self::find_mut(buckets, hash, key, size_mask).and_then(|old| {
            if old.is_null() {
                None
            } else {
                Some(old)
            }
        })
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrower form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for the key
    /// type.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::new();
    /// map.insert(1, 12);
    /// assert_eq!(map.get_key_value(&1), Some((&1, &12)));
    /// assert!(map.get(&2).is_none());
    /// ```
    pub fn get_key_value<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.find(make_hash::<K, Q, H>(&self.hash_builder, key), key)
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::<i32, i32>::new();
    ///
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    ///
    /// for i in 1..5 {
    ///     let value = map.entry(i).or_insert(i * 10);
    ///     *value += 1;
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&11));
    /// assert_eq!(map.get(&2), Some(&21));
    /// assert_eq!(map.get(&3), Some(&31));
    /// assert_eq!(map.get(&4), Some(&41));
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, H, A> {
        if let Some(v_ref) = self.get_mut(&key) {
            Entry::Occupied(OccupiedEntry {
                map: self,
                key,
                value: v_ref,
            })
        } else {
            Entry::Vacant(VacantEntry { map: self, key })
        }
    }

    /// Returns true if the map contains the specified `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::new();
    /// map.insert(1, 47u64);
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get(key).is_some()
    }

    /// Removes the key from the map, returning the value at the key if the key
    /// was present in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::new();
    /// map.insert(2, 17);
    /// assert_eq!(map.remove(&2), Some(17));
    /// assert_eq!(map.remove(&2), None);
    /// ```
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
            if old_value.is_null() {
                return None;
            }
            *v = V::null();
            self.size -= 1;
            Some(old_value)
        } else {
            None
        }
    }

    /// Creates an iterator over a [`HashMap`] which yields immutable key-value
    /// reference pairs.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(12, 27);
    /// assert_eq!(map.iter().count(), 1);
    /// ```
    pub fn iter(&'a self) -> Iter<'a, K, V, H, A> {
        Iter::new(self)
    }

    /// Creates an iterator over a [`HashMap`] which yields mutable key-value
    /// reference pairs.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(12, 27);
    /// map.iter_mut().for_each(|(_k, v)| *v += 1);
    /// assert_eq!(map.get(&12), Some(&28));
    /// assert_eq!(map.iter_mut().count(), 1);
    /// ```
    pub fn iter_mut(&'a mut self) -> IterMut<'a, K, V, H, A> {
        IterMut::new(self)
    }

    /// Returns the length of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::new();
    /// map.insert(2, 17);
    /// assert_eq!(map.len(), 1);
    /// map.insert(4, 17);
    /// assert_eq!(map.len(), 2);
    /// map.remove(&2);
    /// assert_eq!(map.len(), 1);
    /// map.remove(&4);
    /// assert_eq!(map.len(), 0);
    /// map.remove(&4);
    /// assert_eq!(map.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Inserts a new cell into the given `buckets`, where the max number of
    /// buckets is `size_mask` + 1.
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
        key: &K,
        value: V,
        buckets: &mut [Bucket<K, V>],
        size_mask: usize,
    ) -> InsertResult<V> {
        let mut index = hash as usize;
        {
            let cell = Self::get_cell_mut(buckets, index, size_mask);
            if cell.hash == hash && cell.key == *key {
                let old_value = cell.value;
                cell.value = value;
                return InsertResult::Found(old_value);
            } else if cell.hash == null_hash() {
                cell.key = key.clone();
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
        let first_delta = delta == 0;
        while delta != 0 {
            index += delta as usize;
            delta = Self::get_second_delta(buckets, index, size_mask);

            let mut cell = Self::get_cell_mut(buckets, index, size_mask);
            if hash == cell.hash && cell.key == *key {
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
            if cell.hash == null_hash() {
                cell.hash = hash;
                cell.key = key.clone();
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
            debug_assert!(cell.key != *key);
            probes_remaining -= 1;
        }

        // Table is too full, we need to grow it.
        InsertResult::Overflow(index + 1)
    }

    /// Tries to find the value for the `hash`, without inserting into the map.
    /// This will reuturn a Some(&v) if the find succeeded, otherwise this will
    /// return None.
    fn find<Q: ?Sized + Eq>(&self, hash: HashedKey, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
    {
        debug_assert!(hash != null_hash());

        let buckets = self.get_table().bucket_slice();
        let size_mask = self.get_table().size_mask;

        let mut index = hash as usize;
        let cell = Self::get_cell(buckets, index, size_mask);
        if cell.hash == hash && key.eq(cell.key.borrow()) {
            return Some((&cell.key, &cell.value));
        }

        // Now we need to follow the probe chain for the bucket.
        let mut delta = Self::get_first_delta(buckets, index, size_mask);
        while delta != 0 {
            index += delta as usize;
            let cell = Self::get_cell(buckets, index, size_mask);
            if cell.hash == hash && key.eq(cell.key.borrow()) {
                return Some((&cell.key, &cell.value));
            }

            delta = Self::get_second_delta(buckets, index, size_mask);
        }

        None
    }

    /// Tries to find the value for the `hash` without inserting into the
    /// `buckets`. This will reuturn a reference to the old value if the find
    /// was successful.
    fn find_mut<Q: ?Sized + Eq>(
        buckets: &'a mut [Bucket<K, V>],
        hash: HashedKey,
        key: &Q,
        size_mask: usize,
    ) -> Option<&'a mut V>
    where
        K: Borrow<Q>,
    {
        debug_assert!(hash != null_hash());

        let mut index = hash as usize;
        let mut delta = 0u8;
        let mut found = false;

        let cell = Self::get_cell(buckets, index, size_mask);
        if cell.hash == hash && key.eq(cell.key.borrow()) {
            found = true;
        } else {
            delta = Self::get_first_delta(buckets, index, size_mask);
        }

        // If we have found the correct hash, then we will just skip this,
        // otherwise we need to search the probe chain and see if we find
        // something
        while !found && delta != 0 {
            index += delta as usize;
            let cell = Self::get_cell(buckets, index, size_mask);
            if cell.hash == hash && key.eq(cell.key.borrow()) {
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

    /// Moves the current map buckets into a larger container of buckets, where
    /// `overflow_index` is the index at which an overflow of the delta value
    /// would have happened.
    fn move_to_new_buckets(&mut self, overflow_index: usize) {
        // Estimate the number of cells
        let mut index = overflow_index - Self::CELLS_IN_USE;
        let mut cells_in_use = 0;

        let buckets = self.get_table().bucket_slice();
        let size_mask = self.get_table().size_mask;
        for _ in 0..Self::CELLS_IN_USE {
            let cell = Self::get_cell(buckets, index, size_mask);
            if !cell.value.is_null() {
                cells_in_use += 1;
            }
            index += 1;
        }

        // Estimate how much we need to resize by:
        let ratio = cells_in_use as f32 / Self::CELLS_IN_USE as f32;
        let in_use_estimated = (size_mask + 1) as f32 * ratio;
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
    fn try_move_to_new_buckets(&mut self, size: usize) -> bool {
        let source_buckets = self.get_table().bucket_slice();
        let source_size_mask = self.get_table().size_mask;
        let source_size = source_size_mask + 1;

        // This is very bad for performance, we need to allocate this from
        // somewhere else ...
        let dst_table_ptr = Self::allocate_and_init_table(&self.allocator, size);
        let dst_table = unsafe { &mut *dst_table_ptr };
        let dst_size_mask = dst_table.size_mask;
        let dst_buckets = dst_table.bucket_slice_mut();

        for source_index in 0..source_size {
            let cell = Self::get_cell(source_buckets, source_index, source_size_mask);
            if !cell.value.is_null() {
                match Self::insert_or_find(
                    cell.hash,
                    &cell.key,
                    cell.value,
                    dst_buckets,
                    dst_size_mask,
                ) {
                    InsertResult::Overflow(_) => {
                        // New bucekts are too small, failed to move.
                        Self::deallocate_table(&self.allocator, dst_table_ptr);
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

        // Succeeded in moving all buckets, so update the map table:
        Self::deallocate_table(&self.allocator, self.table);
        self.table = dst_table_ptr;

        true
    }

    /// Allocates and initializes buckets which will hold `cells` number of
    /// cells, using the provided `allocator`.
    fn allocate_and_init_table(allocator: &A, cells: usize) -> *mut Table<K, V> {
        assert!(cells >= 4 && (cells % 2 == 0));
        let bucket_count = cells >> 2;
        let bucket_ptr =
            allocate::<Bucket<K, V>, A>(allocator, bucket_count, AllocationKind::Uninitialized);
        let buckets = unsafe { std::slice::from_raw_parts_mut(bucket_ptr, bucket_count) };

        // Since AtomicU8 and AtomicU64 are the same as u8 and u64 in memory,
        // we can write them as zero, rather than calling the atomic versions
        for i in 0..bucket_count {
            unsafe {
                let bucket_deltas = &mut buckets[i].deltas as *mut u8;
                std::ptr::write_bytes(bucket_deltas, 0, 8);
            };

            for cell in 0..4 {
                // FIXME: How to initialize keys?
                unsafe {
                    let cell_hash = &mut buckets[i].cells[cell].hash as *mut HashedKey;
                    std::ptr::write_bytes(cell_hash, 0, 1);
                };

                // FIXME: We should check if the stored type is directly writable ..
                let cell_value = &mut buckets[i].cells[cell].value;
                *cell_value = V::null();
            }
        }

        let table_ptr = allocate::<Table<K, V>, A>(allocator, 1, AllocationKind::Uninitialized);
        let table = unsafe { &mut *table_ptr };

        table.buckets = bucket_ptr;
        table.size_mask = cells - 1;

        table_ptr
    }

    /// Deallocates the table pointed to by `table_ptr` using the `allocator`.
    fn deallocate_table(allocator: &A, table_ptr: *mut Table<K, V>) {
        let table = unsafe { &mut *table_ptr };
        let bucket_ptr = table.buckets;
        let bucket_count = table.size() >> 2;
        deallocate::<Bucket<K, V>, A>(allocator, bucket_ptr, bucket_count);
        deallocate::<Table<K, V>, A>(allocator, table_ptr, 1);
    }

    pub(crate) fn get_cell_at_index(&self, index: usize) -> Option<&Cell<K, V>> {
        let table = self.get_table();
        if index >= table.size() {
            return None;
        }

        let buckets = table.bucket_slice();
        Some(Self::get_cell(buckets, index, table.size_mask))
    }

    pub(crate) fn get_cell_at_index_mut(&self, index: usize) -> Option<&'a mut Cell<K, V>> {
        let table = self.get_table_mut();
        if index >= table.size() {
            return None;
        }

        let size_mask = table.size_mask;
        let buckets = table.bucket_slice_mut();
        Some(Self::get_cell_mut(buckets, index, size_mask))
    }

    /// Gets a reference to a cell for the `index` from the `buckets`.
    #[inline]
    fn get_cell(buckets: &[Bucket<K, V>], index: usize, size_mask: usize) -> &Cell<K, V> {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        &buckets[bucket_index].cells[cell_index]
    }

    /// Gets a mutable reference mutable to a cell for the `index` from the
    /// `buckets`.
    #[inline]
    fn get_cell_mut(
        buckets: &mut [Bucket<K, V>],
        index: usize,
        size_mask: usize,
    ) -> &mut Cell<K, V> {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        &mut buckets[bucket_index].cells[cell_index]
    }

    /// Gets the first delta value for a cell with the given `index`.
    #[inline]
    fn get_first_delta(buckets: &[Bucket<K, V>], index: usize, size_mask: usize) -> u8 {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        buckets[bucket_index].deltas[cell_index]
    }

    /// Gets a mutable reference to the first delta value for a cell with the
    /// given `index`.
    #[inline]
    fn get_first_delta_mut(
        buckets: &mut [Bucket<K, V>],
        index: usize,
        size_mask: usize,
    ) -> &mut u8 {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        &mut buckets[bucket_index].deltas[cell_index]
    }

    /// Gets the second delta value for a cell with the given `index`.
    #[inline]
    fn get_second_delta(buckets: &[Bucket<K, V>], index: usize, size_mask: usize) -> u8 {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        buckets[bucket_index].deltas[cell_index + 4]
    }

    /// Gets a mutable reference to the second delta value for a cell with the
    /// given `index`.
    #[inline]
    fn get_second_delta_mut(
        buckets: &mut [Bucket<K, V>],
        index: usize,
        size_mask: usize,
    ) -> &mut u8 {
        let bucket_index = Self::get_bucket_index(index, size_mask);
        let cell_index = Self::get_cell_index(index);
        &mut buckets[bucket_index].deltas[cell_index + 4]
    }

    /// Gets the index of the bucket for the spcified `index` and `size_mask`.
    #[inline]
    const fn get_bucket_index(index: usize, size_mask: usize) -> usize {
        (index & size_mask) >> 2
    }

    /// Gets the `index` of the cell within a bucket for the `index`.
    #[inline]
    const fn get_cell_index(index: usize) -> usize {
        index & 3
    }
}

// This is safe to be send if the hasher and allocator are send, since the pointer
// to the table is not thread-local and can be sent between threads.
unsafe impl<K, V, H, A> Send for HashMap<K, V, H, A>
where
    H: BuildHasher + Send,
    A: Allocator + Send,
{
}

impl<K, V, H, A: Allocator> Drop for HashMap<K, V, H, A> {
    fn drop(&mut self) {
        if !self.is_allocated() {
            return;
        }

        let table = self.get_table_mut();

        let bucket_ptr = table.buckets;
        let bucket_count = table.size() >> 2;
        deallocate::<Bucket<K, V>, A>(&self.allocator, bucket_ptr, bucket_count);

        let table_ptr = self.table;
        deallocate::<Table<K, V>, A>(&self.allocator, table_ptr, 1);
    }
}

impl<K, V, H, A> IntoIterator for HashMap<K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + Default,
    A: Allocator,
{
    type Item = (K, V);
    type IntoIter = OwnedIter<K, V, H, A>;

    fn into_iter(self) -> Self::IntoIter {
        OwnedIter::new(self)
    }
}

impl<'a, K, V, H, A> IntoIterator for &'a HashMap<K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + Default + 'a,
    A: Allocator + 'a,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, H, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Returns the null hash value.
#[inline]
pub(crate) const fn null_hash() -> HashedKey {
    0_u64
}

/// The type used for hashed keys.
pub(crate) type HashedKey = u64;

/// Struct which stores a cell in a hash map. A cell is simply a hash (rather
/// than the key iteself) and the value associated with the key for which the
/// hash is associated.
pub(crate) struct Cell<K, V> {
    /// The hashed value of the cell. This adds 8 bytes of overhead to per key-value
    /// pair for the cell, which is a lot, but it improves performance, so we
    /// make the tradeoff.
    /// FIXME: Reduce this overhead ...
    hash: HashedKey,
    // The key for the cell.
    pub(crate) key: K,
    /// The value assosciated with the hash.
    pub(crate) value: V,
}

impl<K, V> Cell<K, V> {
    /// Returns true if the cell is empty.
    pub fn is_empty(&self) -> bool {
        self.hash == null_hash()
    }
}

/// Underlying table for a [HashMap]. This stores a pointer to the buckets and
/// the mask for the number of cells which are stored in the table.
struct Table<K, V> {
    /// Pointer to the buckets for the table.
    buckets: *mut Bucket<K, V>,
    /// The mask for indexing into the buckets.
    size_mask: usize,
}

impl<K, V> Table<K, V> {
    /// Gets a mutable slice of the table buckets.
    pub fn bucket_slice_mut(&mut self) -> &mut [Bucket<K, V>] {
        unsafe { std::slice::from_raw_parts_mut(self.buckets, self.size()) }
    }

    /// Gets a slice of the table buckets.
    pub fn bucket_slice(&self) -> &[Bucket<K, V>] {
        unsafe { std::slice::from_raw_parts(self.buckets, self.size()) }
    }

    /// Returns the number of cells in the table.
    pub fn size(&self) -> usize {
        self.size_mask + 1
    }
}

/// Struct which stores buckets of cells. Each bucket stores four cells
/// and two delta values per cell. The first delta value for a cell provides
/// the offset to the cell which is the start of the probe chain for the cell.
/// The second delta value provides the offset to the next link in the probe
/// chain once a search along the probe chain has started.
struct Bucket<K, V> {
    /// Delta values for the cells. The first 4 values are the delta values to
    /// the start of the probe chain, and the second 4 values are the delta
    /// values to the next probe in the chain, for each cell, respectively.
    deltas: [u8; 8],
    /// Cells for the bucket.
    cells: [Cell<K, V>; 4],
    /// Placeholder for the key
    _key: std::marker::PhantomData<K>,
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
