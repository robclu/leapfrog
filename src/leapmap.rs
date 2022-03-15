use crate::leapiter::{Iter, IterMut, OwnedIter};
use crate::leapref::{Ref, RefMut};
use crate::util::{allocate, deallocate, round_to_pow2, AllocationKind};
use crate::{make_hash, Value};
use atomic::Atomic;
use std::alloc::{Allocator, Global};
use std::borrow::Borrow;
use std::hash::{BuildHasher, BuildHasherDefault, Hash};
use std::sync::atomic::{
    AtomicBool, AtomicPtr, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering,
};

/// The default hasher for a [`LeapMap`].
pub(crate) type DefaultHash = std::collections::hash_map::DefaultHasher;

/// A concurrent hash map implementation which uses a modified form of RobinHood/
/// Hopscotch probing. This implementation is lock-free, and therefore it will
/// *not* deadlock when any of the map operations are performed concurrently.
/// The map is lock-free if the key and value types have built-in atomic support,
/// and if not, an efficient spin-lock is used.
///
/// By default, the `LeapMap` map uses the default hasher from the standard
/// library, which is DOS resistent, but is less efficient. Any other hasher
/// can be used instead, likely with improved performance but less security.
/// Using a different hasher is as simple a reating the map using the
/// `with_hasher` or `with_capacity_and_hasher` methods.
///
/// Values stored in the map need to mplement the [`Value`] trait. The trait is
/// simple to implement, requiring that two values be reserved, one for the
/// `null` case, which is used as a placeholder, and one for a `redirect`, which
/// is used to signal that the map is being migrated. This trait is only implemented
/// for numeric types and uses MAX and MAX -1 for the null and redirect values,
/// respectively. For any other type this needs to be implemented.
///
/// This map is very fast for concurrent operations since the locking is either
/// atomic or uses very finer grained locking than other maps.
///
/// # Limitations
///
/// This biggest limitations of this map are that the interface is slightly
/// different than using [`std::sync::RwLock<HashMap>`]. The type returned
/// when calling `get`, `get_mut`, `iter`, etc, are not references, but rather a
/// [`Ref`] or [`RefMut`] type which acts like a reference but still allows concurrent
/// operations on both that reference type and the map. This interface is still
/// being worked out, and might be changed in the future.
///
/// When adding a key-value pair to the map, it's possible that the map is too
/// full and there is no bucket, in which case a larger map needs to be allocated
/// and then filled from the old map. This will happen concurrently. The current
/// implementation *does not* use a custom allocator, but would likely further
/// improve the performance.
///
/// The number of elements in the map must be a power of two. This is handled
/// internally.
///
/// Lastly, this map stores additional data for each key-value pair. There are
/// 8 bytes used to store offsets for the probe search, and 8 bytes for the hashed
/// key. This is quite a lot of overhead, but this map is designed for good performace
/// and scaling. This will be a focus area for improvement in the future, but if
/// memory use is more important that performance, another map will be a better
/// choice.
///
/// # Threading
///
/// The map *is* thread-safe, and items can be added, removed, pdated, and iterated
/// over cuncurrently from any number of threads.
pub struct LeapMap<K, V, H = BuildHasherDefault<DefaultHash>, A: Allocator = Global> {
    /// Pointer to the buckets for the map. This needs to be a pointer to that
    /// we can atomically get the buckets for operations, since when the map
    /// is resized the buckets might change, and we need to ensure that all
    /// operations can identify if they have the correct buckets.
    table: AtomicPtr<Table<K, V>>,
    /// The hasher for the map.
    hash_builder: H,
    /// Alloctor for the buckets.
    allocator: A,
    /// Migrator for moving buckets into larger storage.
    migrator: AtomicPtr<Migrator<K, V>>,
}

impl<'a, K, V, H, A: Allocator> LeapMap<K, V, H, A> {
    /// Gets the capacity of the hash map.
    pub fn capacity(&self) -> usize {
        self.get_table(Ordering::Relaxed).size()
    }

    /// Gets a reference to the map's table, using the specified `ordering` to
    /// load the table reference.
    fn get_table(&self, ordering: Ordering) -> &'a Table<K, V> {
        unsafe { &*self.table.load(ordering) }
    }

    /// Gets a mutable reference to the map's table, using the specified
    /// `ordering` to load the table reference.
    fn get_table_mut(&self, ordering: Ordering) -> &'a mut Table<K, V> {
        unsafe { &mut *self.table.load(ordering) }
    }

    /// Returns true if the table has been allocated.
    fn is_allocated(&self) -> bool {
        !self.table.load(Ordering::Relaxed).is_null()
    }
}

impl<K, V> LeapMap<K, V, BuildHasherDefault<DefaultHash>, Global>
where
    K: Eq + Hash + Copy,
    V: Value,
{
    /// Creates the hash map with space for the default number of elements, which
    /// will use the global allocator for allocation of the map data.
    pub fn new() -> LeapMap<K, V, BuildHasherDefault<DefaultHash>, Global> {
        Self::new_in(Global)
    }

    /// Creates the hash map with space for `capacity` elements, which will use
    /// the global allocator for allocation of the map data.
    pub fn with_capacity(
        capacity: usize,
    ) -> LeapMap<K, V, BuildHasherDefault<DefaultHash>, Global> {
        Self::with_capacity_and_hasher_in(
            capacity,
            BuildHasherDefault::<DefaultHash>::default(),
            Global,
        )
    }
}

impl<K, V, H> LeapMap<K, V, H, Global>
where
    K: Eq + Hash + Copy,
    V: Value,
    H: BuildHasher + Default,
{
    /// Creates the hash map with space for `capacity` elements, using the
    /// `builder` to create the hasher, which will use the global allocator for
    /// allocation of the map data.
    pub fn with_capacity_and_hasher(capacity: usize, builder: H) -> LeapMap<K, V, H, Global> {
        Self::with_capacity_and_hasher_in(capacity, builder, Global)
    }
}

impl<'a, K, V, H, A> LeapMap<K, V, H, A>
where
    K: Eq + Hash + Copy + 'a,
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

    /// The number of muckets to migrate as a unit. Larger sizes tend to perform
    /// better, but this also depends on the map size.
    const MIGRATION_UNIT_SIZE: usize = 128;

    /// Creates the hash map with space for the default number of elements, using
    /// the provided `allocator` to allocate data for the map.
    pub fn new_in(allocator: A) -> LeapMap<K, V, H, A> {
        Self::with_capacity_and_hasher_in(Self::INITIAL_SIZE, H::default(), allocator)
    }

    /// Creates the hash map with space for the `capacity` number of elements
    /// using the provided `builder` to build the hasher, and `allocator` for
    /// allocating the map data.
    pub fn with_capacity_and_hasher_in(
        capacity: usize,
        builder: H,
        allocator: A,
    ) -> LeapMap<K, V, H, A> {
        let migrator_ptr = allocate::<Migrator<K, V>, A>(&allocator, 1, AllocationKind::Zeroed);
        let migrator = unsafe { &mut *migrator_ptr };
        migrator.initialize();

        let capacity = round_to_pow2(capacity.max(Self::INITIAL_SIZE));
        let table_ptr = Self::allocate_and_init_table(&allocator, capacity);
        LeapMap {
            table: AtomicPtr::new(table_ptr),
            hash_builder: builder,
            allocator,
            migrator: AtomicPtr::new(migrator_ptr),
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

    /// Returns an optional reference type to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// let map = leapfrog::LeapMap::new();
    /// map.insert(0, 12);
    /// if let Some(mut r) = map.get(&0) {
    ///     assert_eq!(r.value(), Some(12));
    /// } else {
    ///     // Map is stale
    ///     assert!(false);
    /// }
    /// assert!(map.get(&2).is_none());
    ///```
    pub fn get<Q: ?Sized>(&'a self, key: &Q) -> Option<Ref<'a, K, V, H, A>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let hash = make_hash::<K, Q, H>(&self.hash_builder, key);
        self.find(key, hash).map(|cell| Ref::new(self, cell, hash))
    }

    /// Returns a mutable reference type to the value corresponding to the `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// let map = leapfrog::LeapMap::new();
    /// map.insert(1, 12);
    /// if let Some(mut value_ref) = map.get_mut(&1) {
    ///     if let Some(old) = value_ref.set_value(14) {
    ///         assert_eq!(old, 12);
    ///     } else {
    ///        // Map is being moved, can't update
    ///     }
    /// }
    /// assert_eq!(map.get(&1).unwrap().value(), Some(14));
    /// assert!(map.get(&2).is_none());
    ///```
    pub fn get_mut<Q: ?Sized>(&'a self, key: &Q) -> Option<RefMut<'a, K, V, H, A>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let hash = make_hash::<K, Q, H>(&self.hash_builder, key);
        self.find(key, hash)
            .map(|cell| RefMut::new(self, cell, hash))
    }

    /// Returns true if the map contains the specified `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// let map = leapfrog::LeapMap::new();
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
    /// let map = leapfrog::LeapMap::new();
    /// map.insert(2, 17);
    /// assert_eq!(map.remove(&2), Some(17));
    /// assert_eq!(map.remove(&2), None);
    /// ```
    pub fn remove<Q: ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let hash = make_hash::<K, Q, H>(&self.hash_builder, key);
        self.find(key, hash).and_then(|cell| self.erase_value(cell))
    }

    /// Updates a key-value pair.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated and the old
    /// value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// let map = leapfrog::LeapMap::new();
    /// assert_eq!(map.insert(&37, 12), None);
    /// assert_eq!(map.update(&37, 14), Some(12));
    /// ```
    pub fn update<Q: ?Sized>(&self, key: &Q, value: V) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let hash = make_hash::<K, _, H>(&self.hash_builder, key);
        debug_assert!(!value.is_null());

        loop {
            match self.find(key, hash) {
                Some(cell) => {
                    let old = cell.value.load(Ordering::Relaxed);
                    match Self::exchange_value(cell, value, old) {
                        // A racing thread deleted the cell just before we performed the update
                        ConcurrentInsertResult::NewInsert => {
                            return Some(V::null());
                        }
                        ConcurrentInsertResult::Replaced(old_value) => {
                            return Some(old_value);
                        }
                        ConcurrentInsertResult::Overflow(_) => {
                            // This should never happen, so we panic if it does.
                            panic!("LeapMap update overflowed");
                        }
                        ConcurrentInsertResult::Migration(_) => {
                            // Help with the migration and then try again
                            self.participate_in_migration();
                        }
                    }
                }
                None => {
                    return None;
                }
            }
        }
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
    /// let map = leapfrog::LeapMap::new();
    /// assert_eq!(map.insert(37, 12), None);
    /// assert_eq!(map.insert(37, 14), Some(12));
    /// ```
    pub fn insert(&self, key: K, mut value: V) -> Option<V> {
        let hash = make_hash::<K, _, H>(&self.hash_builder, &key);
        debug_assert!(!value.is_null());

        loop {
            // We need to get the pointer to the buckets which we are going to
            // attempt to insert into. The ideal ordering here would be Consume,
            // but we don't have that, so we use Acquire instead. For most platforms
            // the impact should be negligible, however, that mught not be the case
            // for ARM, so we should check this for those platforms.
            let table = self.get_table_mut(Ordering::Acquire);
            let size_mask = table.size_mask;
            let buckets = table.bucket_slice_mut();

            match Self::insert_or_find(hash, &key, value, buckets, size_mask) {
                ConcurrentInsertResult::Overflow(overflow_index) => {
                    // Try and create the table migration. Only a single thread
                    // should do this. Any threads which don't get the flag should
                    // start cleaning up old tables which have not been deallocated.
                    let migrator = unsafe { &mut *self.migrator.load(Ordering::Relaxed) };
                    if migrator.set_initialization_begin_flag() {
                        Self::initialize_migrator(
                            &self.allocator,
                            migrator,
                            &self.table,
                            overflow_index,
                        );
                        migrator.set_initialization_complete_flag();
                    }

                    // Migration is created, all threads can see that try and migrate.
                    if migrator.initialization_complete() {
                        Self::perform_migration(&self.allocator, migrator, &self.table);
                    }
                }
                ConcurrentInsertResult::Replaced(old_value) => {
                    return Some(old_value);
                }
                ConcurrentInsertResult::NewInsert => {
                    return None;
                }
                ConcurrentInsertResult::Migration(retry_value) => {
                    // Another thread overflowed and started a migration.
                    value = retry_value;
                    //debug_assert!(value == retry_value);
                    self.participate_in_migration();
                }
            }
        }
    }

    /// Creates an iterator over a [`LeapMap`] which yields immutable key-value
    /// pairs.
    ///
    /// # Threading
    ///
    /// This is thread-safe and can be called from any number of threads, and
    /// will *not* deadlock. See the [`Ref`] type for how to access iterated
    /// values.
    //
    /// # Examples
    ///
    /// ```
    /// use leapfrog::LeapMap;
    ///
    /// let map = LeapMap::new();
    /// map.insert(12, 27);
    /// assert_eq!(map.iter().count(), 1);
    ///
    /// for mut item in map.iter() {
    ///     assert_eq!(item.key_value(), Some((12, 27)));
    /// }
    /// ```
    pub fn iter(&'a self) -> Iter<'a, K, V, H, A> {
        Iter::new(self)
    }

    /// Creates an iterator over a [`LeapMap`] which yields mutable key-value
    /// pairs.
    ///
    /// # Threading
    ///
    /// This is thread-safe and can be called from any number of threads, and
    /// will *not* deadlock. See the [`Ref`] type for how to access iterated
    /// values.
    //
    /// # Examples
    ///
    /// ```
    /// use leapfrog::LeapMap;
    ///
    /// let map = LeapMap::new();
    /// map.insert(12u32, 27u32);
    /// map.insert(13u32, 28u32);
    /// assert_eq!(map.iter_mut().count(), 2);
    ///
    /// for mut item in map.iter_mut() {
    ///     let old = item.update(|v| {
    ///         let current = *v;
    ///         *v = current + current;
    ///     });
    ///     assert!(old.is_some());
    /// }
    ///
    /// assert_eq!(map.get(&12).unwrap().value(), Some(54));
    /// assert_eq!(map.get(&13).unwrap().value(), Some(56));
    /// ```
    pub fn iter_mut(&'a self) -> IterMut<'a, K, V, H, A> {
        IterMut::new(self)
    }

    /// Returns the length of the map.
    ///
    /// This computes the length each time, since the alternative--pdating the
    /// length on inserts and removals--hurts performance signitifantly under
    /// contention.
    ///
    /// For almost all use cases, gettting the length will be performed very
    /// infrequently, if at all, so the tradeoff is made here that the more
    /// likely operations are more performant.
    pub fn len(&self) -> usize {
        let table = self.get_table(Ordering::Acquire);
        let buckets = table.bucket_slice();
        let size = table.size();

        let mut index: usize = 0;
        let mut elements: usize = 0;
        for bucket in buckets {
            for cell in &bucket.cells {
                if index >= size {
                    break;
                }

                if !cell.value.load(Ordering::Relaxed).is_null() {
                    elements += 1;
                }

                index += 1;
            }
        }
        elements
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Tries to find the value for the `hash`, without inserting into the map.
    /// This will reuturn a reference to the cell if the find succeeded.
    pub(crate) fn find<Q: ?Sized>(&self, key: &Q, hash: HashedKey) -> Option<&'a AtomicCell<K, V>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        debug_assert!(hash != null_hash());

        loop {
            let table = self.get_table(Ordering::Acquire);
            let size_mask = table.size_mask;
            let buckets = table.bucket_slice();

            if let Some(cell) = self.find_inner(key, hash, buckets, size_mask) {
                let value = cell.value.load(Ordering::Acquire);
                if !value.is_redirect() {
                    if value.is_null() {
                        return None;
                    }
                    return Some(cell);
                }

                // Help finish the migration, and then try again ...
                self.participate_in_migration();
            } else {
                // None was returned, so we didn't find the hash in the map
                return None;
            }
        }
    }

    /// Inner loop for finding a value for the specified `hash` in the specified
    /// `buckets`, which have an assosciated `size_mask` representing the number
    /// of cells in the buckets. This returns a reference to the cell if the
    /// find was successful.
    fn find_inner<Q: ?Sized>(
        &self,
        key: &Q,
        hash: HashedKey,
        buckets: &'a [Bucket<K, V>],
        size_mask: usize,
    ) -> Option<&'a AtomicCell<K, V>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let mut index = hash as usize & size_mask;
        let cell = get_cell(buckets, index, size_mask);
        let probe_hash = cell.hash.load(Ordering::Relaxed);
        let probe_key = cell.key.load(Ordering::Relaxed);
        if hash == probe_hash && key.eq(probe_key.borrow()) {
            return Some(cell);
        } else if probe_hash == null_hash() {
            return None;
        }

        // Otherwise we have to follow the probe chain:
        let mut delta = get_first_delta(buckets, index, size_mask).load(Ordering::Relaxed);
        while delta != 0 {
            index = (index + delta as usize) & size_mask;
            let cell = get_cell(buckets, index, size_mask);
            let probe_hash = cell.hash.load(Ordering::Relaxed);
            let probe_key = cell.key.load(Ordering::Relaxed);

            // NOTE: It's possible that a concurrent insert memory reordering
            //       causes probe_hash to be default, but we don't need to check
            //       for that case, and we can just follow the probe chain.
            if probe_hash == hash && key.eq(probe_key.borrow()) {
                return Some(cell);
            }

            delta = get_second_delta(buckets, index, size_mask).load(Ordering::Relaxed);
        }

        None
    }

    /// Erases the cell from the map, returning the old value if the cell was
    /// in the map and has a valid value. This returns `None` if the cell has
    /// already been erased, or if the map was migrated and this cell was not
    /// migrated and therefore erased.
    ///
    /// This does not actually remove the cell from the map, delete the cell hash
    /// value, or modify any deltas for the probe chain, since that would break
    /// lookups of other cells in the map. This also means that if another cell
    /// is inserted with the same hash then there is a faster path when inserting.
    fn erase_value(&self, mut cell: &'a AtomicCell<K, V>) -> Option<V> {
        loop {
            let value = cell.value.load(Ordering::Relaxed);

            // If the cell was found, but the value is default, then it means
            // that this cell has already been erased, since the value
            // would have been set to default.
            if value.is_null() {
                return None;
            }

            let key = cell.key.load(Ordering::Relaxed);
            match cell.value.compare_exchange(
                value,
                V::null(),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    return Some(value);
                }
                Err(updated) => {
                    // Another thread wrote to the cell before we exchanged, we
                    // can treat this as if we erased the cell and then the new
                    // thread performed the write, which is what happened, we just
                    // didn't finish the erasure.
                    if !updated.is_redirect() {
                        return Some(value);
                    }

                    // There is a migration, so we can't erase. Help finish the
                    // migration:
                    let hash = cell.hash.load(Ordering::Relaxed);
                    loop {
                        self.participate_in_migration();
                        match self.find(&key, hash) {
                            Some(new_cell) => {
                                cell = new_cell;
                                // This should almost always be true, migration is finished.
                                // Break and then search again with the new cell.
                                if !cell.value.load(Ordering::Relaxed).is_redirect() {
                                    break;
                                }
                                // Migration not finished, try again ..
                            }
                            // Not found in new map, so it's effectively erased
                            None => return None,
                        }
                    }
                }
            }
        }
    }

    /// Creates the `migrator`, which is used to migrate from the old `buckets`. Only
    /// a single thread must do this, so `acquire_migration_flag` should be called
    /// prior to calling this, and then this must only be called by the thread which
    /// acquired the migration flag.
    fn initialize_migrator(
        allocator: &A,
        migrator: &mut Migrator<K, V>,
        table: &AtomicPtr<Table<K, V>>,
        overflow_index: usize,
    ) {
        let src_table_ptr = table.load(Ordering::Relaxed);
        let src_table = unsafe { &*src_table_ptr };
        let src_buckets = src_table.bucket_slice();
        let size_mask = src_table.size_mask;

        // As above, only a single thread should do this to avoid contention
        let mut index = overflow_index - Self::CELLS_IN_USE;
        let mut cells_in_use = 0;
        for _ in 0..Self::CELLS_IN_USE {
            let cell = get_cell(src_buckets, index, size_mask);
            if !cell.value.load(Ordering::Relaxed).is_null() {
                cells_in_use += 1;
            }
            index += 1;
        }

        // Estimate how much we need to resize by:
        let ratio = cells_in_use as f32 / Self::CELLS_IN_USE as f32;
        let in_use_estimated = (size_mask + 1) as f32 * ratio;
        let estimated = round_to_pow2((in_use_estimated * 2.0).max(1.0) as usize);

        // FIXME: This doesn't allow the map to shrink
        //let new_table_size = estimated.max((size_mask + 1) as usize);
        let new_table_size = estimated.max(Self::INITIAL_SIZE as usize);

        // Migrator initialization:
        let dst_table_ptr = Self::allocate_and_init_table(allocator, new_table_size);
        let dst_table = unsafe { &*dst_table_ptr };
        debug_assert!(dst_table.size_mask != 0);
        migrator.dst_table.store(dst_table_ptr, Ordering::Relaxed);

        // Zero out the status during migration, but keep the low bits for
        // initialization status:
        migrator
            .status
            .fetch_and(Migrator::<K, V>::STATUS_MASK, Ordering::Relaxed);
        migrator
            .remaining_units
            .store(Self::remaining_units(size_mask), Ordering::Relaxed);
        migrator.overflowed.store(false, Ordering::Relaxed);

        // Check if there are any old source tables, and move them to the cleanup
        // queue:
        let last_source = migrator.last_stale_source.load(Ordering::Relaxed);
        let num_sources = migrator.num_source_tables.load(Ordering::Relaxed);
        migrator.num_source_tables.store(0, Ordering::Relaxed);

        for i in 0..num_sources {
            let source = migrator.sources.pop().unwrap();
            let index = migrator.stale_source_index((last_source + i) as usize);

            // If this is not null, then we have wrapped:
            // FIXME: This occasionally causes a panic in the tests!
            debug_assert!(migrator.stale_sources[index]
                .load(Ordering::Relaxed)
                .is_null());

            migrator.stale_sources[index]
                .store(source.table.load(Ordering::Relaxed), Ordering::Relaxed);
            migrator.last_stale_source.fetch_add(1, Ordering::Relaxed);
        }

        let source = MigrationSource::<K, V> {
            table: AtomicPtr::new(src_table_ptr),
            index: AtomicUsize::new(0),
        };
        if migrator.sources.is_empty() {
            migrator.sources.push(source);
        } else {
            migrator.sources[0] = source;
        }
        migrator.num_source_tables.store(1, Ordering::Relaxed);
    }

    /// Makes the calling thread participate in the migtration.
    pub(crate) fn participate_in_migration(&self) {
        let migrator = unsafe { &mut *self.migrator.load(Ordering::Relaxed) };

        // Nothing to do here ...
        if !migrator.in_process() {
            return;
        }

        // First check if that migration is in the completion stage,
        // in which case we should go and clean up some of the old
        // migration tables.
        if migrator.finishing() {
            while migrator.finishing() {
                // Clean up old tables, then return:
                migrator.cleanup_stale_table(&self.allocator);
            }
            return;
        }

        if migrator.in_process() && !migrator.initialization_complete() {
            while !migrator.initialization_complete() {
                migrator.cleanup_stale_table(&self.allocator);
            }
        }

        // Otherwise we need to join in the migration;
        Self::perform_migration(&self.allocator, migrator, &self.table);
    }

    /// Perfoms migration using the `migrator`. When the migration is successful,
    /// this will then store the migrated buckets into `dst_bucekt_ptr` and set
    /// the `dst_size_mask`.
    fn perform_migration(
        allocator: &A,
        migrator: &mut Migrator<K, V>,
        dst_table: &AtomicPtr<Table<K, V>>,
    ) {
        // Increment the number of workers for the migrator.
        let mut status = migrator.status.load(Ordering::Relaxed);
        loop {
            if status & 1 == 1 {
                // Migration is finished, we can break
                return;
            }
            // Last bit is flag for completion, hence + 8:
            match migrator.status.compare_exchange(
                status,
                status + 8,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(updated) => status = updated,
            }
        }

        // Iterate over all source tables
        let num_sources = migrator.num_source_tables.load(Ordering::Relaxed);
        for i in 0..num_sources {
            let mut finished = false;
            loop {
                if migrator.finishing() {
                    finished = true;
                    break;
                }

                // FIXME: This should not be here
                if i as usize >= migrator.sources.len() {
                    break;
                }

                let source = &migrator.sources[i as usize];
                // Check if this source has finished migration and we can move on:
                let start_index = source
                    .index
                    .fetch_add(Self::MIGRATION_UNIT_SIZE, Ordering::Relaxed);
                if start_index >= source.size() {
                    break;
                }

                // Check if the migration failed due to overflow in the destination
                // table. Since this source caused an overflow, the migration can't
                // complete for any thread because this unit will never complete.
                // Multiple threads may overflow concurrently.
                // We need to notify all threads of the overflow, so that they are
                // flushed an we can safely deal with the overflow.
                let end_index = start_index + Self::MIGRATION_UNIT_SIZE;
                if !migrator.migrate_range::<H, A>(i as usize, start_index, end_index) {
                    migrator.overflowed.store(true, Ordering::Relaxed);
                    migrator.status.fetch_or(1, Ordering::Relaxed);
                    finished = true;
                    break;
                }

                // Successfully migrated some of the units, update status and
                // then either try again or we are done:
                if migrator.remaining_units.fetch_sub(1, Ordering::Relaxed) == 1 {
                    migrator.status.fetch_or(1, Ordering::Relaxed);
                    finished = true;
                    break;
                }
            }

            if finished {
                break;
            }
        }

        // Finish the migration:
        // Decrement the status to indicate that this thread is done. We need
        // acquire release here to make all previous writes visible to the
        // last thread to reach this point, which will actually finish the
        // migration
        let prev_status = migrator.status.fetch_sub(8, Ordering::AcqRel);
        if prev_status >= 16 {
            // Clean up old migrated tables until finished. This also makes the
            // performance of inserts more stable.
            while migrator.status.load(Ordering::Relaxed) >= 1 {
                //migrator.cleanup_stale_table(allocator);
            }

            // We weren't the last thread here, so we can exit.
            return;
        }

        // We are the last thread, complete the migration:
        // The status still indicates that a migration is being performed, so
        // other threads will be able to see that the migration is still in
        // progress but is in the completion stage.
        debug_assert!(prev_status == 15);
        if migrator.overflowed.load(Ordering::Relaxed) {
            // Overflow of destination table, move the destination table to be
            // a source in the migrator, create a new destination table, and
            // then break so that we can try again.
            let table_ptr = migrator.dst_table.load(Ordering::Relaxed);
            let table = unsafe { &*table_ptr };

            let mut remaining_units = Self::remaining_units(table.size_mask);
            for source in &migrator.sources {
                remaining_units += Self::remaining_units(source.size());
                source.index.store(0, Ordering::Relaxed);
            }

            migrator.sources.push(MigrationSource {
                table: AtomicPtr::new(table_ptr),
                index: AtomicUsize::new(0),
            });

            migrator
                .remaining_units
                .store(remaining_units, Ordering::Relaxed);

            // Create the new table for the migrator:
            let new_dst_table_ptr =
                Self::allocate_and_init_table(allocator, (table.size_mask + 1) * 2);
            migrator
                .dst_table
                .store(new_dst_table_ptr, Ordering::Relaxed);

            // Finally we can set that we are done!
            migrator.status.store(0, Ordering::Relaxed);
        } else {
            // Migration was successful, we can update the migrator. Here
            // we only set the variables which we need to:
            let new_table_ptr = migrator.dst_table.load(Ordering::Relaxed);
            dst_table.store(new_table_ptr, Ordering::Release);

            migrator.overflowed.store(false, Ordering::Relaxed);
            //migrator
            //    .dst_table
            //    .store(std::ptr::null_mut(), Ordering::Relaxed);

            // We don't move the source tables here, rather, we wait until the
            // next mogration and add them to the cleanup queue then.

            // Finally we can set that we are done!
            migrator.status.store(0, Ordering::Release);
        }
    }

    /// Inserts a new cell into the given `buckets`, where the max number of
    /// cells is `size_mask` + 1.
    ///
    /// # Returns
    ///
    /// This returns a [ConcurrentInsertResult] which specifies what happened
    /// during the insertion procedure.
    ///
    /// If the hash was found in the map, then  [ConcurrentInsertResult::Replaced]
    /// will be returned with the value set to the old value for the found cell.
    ///
    /// If the hash was not found, then [ConcurrentInsertResult::NewInsert] will be
    /// returned to specify that the hash was newly inserted.
    ///
    /// If the hash was not found in the map, and it was not possible to insert
    /// the hash into the map, then [ConcurrentInsertResult::Overflow] will be
    /// returned with the index of the overflow.
    ///
    /// If the hash was found and it was either not possible to perform an
    /// exchange, or the value at the hashed location was a redirect, then
    /// [ConcurrentInsertResult::Migration] will be returned to indicate that
    /// a migration is in progress.
    pub(super) fn insert_or_find(
        hash: HashedKey,
        key: &K,
        value: V,
        buckets: &[Bucket<K, V>],
        size_mask: usize,
    ) -> ConcurrentInsertResult<V> {
        let mut index = hash as usize;

        // Start by checking the hashed cell. It's quite unlikely that it belongs
        // to the bucket it hashes to, but this is fast if it does.
        let cell = get_cell(buckets, index, size_mask);
        let mut probe_hash = cell.hash.load(Ordering::Relaxed);

        if probe_hash == null_hash() {
            match cell
                .hash
                .compare_exchange(probe_hash, hash, Ordering::Relaxed, Ordering::Relaxed)
            {
                Ok(_) => {
                    // This is an empty cell, and we won the race to claim it.
                    // We can just set the key. The only problem we could have
                    // here is a migration, in which case the value exchange below
                    // will fail.
                    cell.key.store(*key, Ordering::Relaxed);
                    return Self::exchange_value(cell, value, V::null());
                }
                Err(new_hash) => {
                    // Lost the race, so likely go and search through the probe chain.
                    probe_hash = new_hash;
                }
            }
        }

        // Hash already in table, check if the keys match, if they do then we
        // can exchange and return the value.
        let probe_key = cell.key.load(Ordering::Relaxed);
        if probe_hash == hash && probe_key.eq(key.borrow()) {
            let old_value = cell.value.load(Ordering::Acquire);

            // Check if the table is being moved:
            if old_value.is_redirect() {
                return ConcurrentInsertResult::Migration(value);
            }

            // Otherwise try and exchange the old value with the new one.
            return Self::exchange_value(cell, value, old_value);
        }

        // Hard part, need to find a new cell ...
        // Follow the linked probes to find a new cell.
        // Here, we get the offset delta which will allow us to find the desired
        // bucket. After that, we need to use the second set of delta values to
        // walk along the chain. At each point, we check if the hash is a match;
        // if we find a match, then we have found the cell.
        let max_index = index + size_mask;
        debug_assert!(max_index as i64 - index as i64 >= 0);

        let mut first = true;
        loop {
            let mut follow_link = false;
            let prev_link = get_delta(buckets, index, size_mask, first);
            let probe_delta = prev_link.load(Ordering::Relaxed);
            first = false;

            // Search the probe chain for this cell:
            if probe_delta != 0 {
                index += probe_delta as usize;

                let cell = get_cell(buckets, index, size_mask);
                let mut probe_hash = cell.hash.load(Ordering::Relaxed);
                if probe_hash == null_hash() {
                    // The cell has been linked to the probe chain, but the hash
                    // is not yet visible. We chould change this here to use
                    // acquire and release, which would guarantee that the change
                    // is visible, but it's easier to just poll:
                    // FIXME : Cange this to acquire releaase ...
                    loop {
                        probe_hash = cell.hash.load(Ordering::Acquire);
                        if probe_hash != null_hash() {
                            break;
                        }
                    }
                }

                // Only hashes in the same bucket can be linked.
                debug_assert!((probe_hash ^ hash) as usize & size_mask == 0);
                let probe_key = cell.key.load(Ordering::Relaxed);
                if probe_hash == hash && probe_key.eq(key.borrow()) {
                    let old_value = cell.value.load(Ordering::Acquire);

                    // Check if the table is being moved:
                    if old_value.is_redirect() {
                        return ConcurrentInsertResult::Migration(value);
                    }

                    return Self::exchange_value(cell, value, old_value);
                }

                // We updated the index and the delta value, so we will go back
                // to the start of the loop and search the next probe in the chain
            } else {
                // We have reached the end of the probe chain for the current
                // bucket. We now need to move to linear probing until we either
                // find a new cell, or we find a cell in the same bucket whose
                // changes have only just been made visible.
                let prev_link_index = index;
                debug_assert!(max_index as i64 - index as i64 >= 0);

                let mut probes_remaining = Self::LINEAR_SEARCH_LIMIT.min(max_index - index);
                while probes_remaining > 0 {
                    index += 1;

                    // We found an empty cell, so reserve it and link it
                    // to the previous cell in the same bucket.
                    let cell = get_cell(buckets, index, size_mask);
                    let mut probe_hash = cell.hash.load(Ordering::Relaxed);
                    if probe_hash == null_hash() {
                        // Same as above, there is an empty cell, we we want to
                        // try and reserve it. If we lose the race here, then
                        // we just fall through to the next stage ...
                        match cell.hash.compare_exchange(
                            probe_hash,
                            hash,
                            Ordering::Relaxed,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => {
                                // Now link the cell to the previous cell in the same bucket:
                                let offset = (index - prev_link_index) as u8;
                                prev_link.store(offset, Ordering::Relaxed);

                                // CHECK: No race here with another cell
                                cell.key.store(*key, Ordering::Relaxed);

                                return Self::exchange_value(cell, value, V::null());
                            }
                            Err(updated) => probe_hash = updated,
                        }
                    }

                    // Check for the same hash, so we can replace:
                    let x = hash ^ probe_hash;
                    let probe_key = cell.key.load(Ordering::Relaxed);
                    if x == 0 && probe_key == *key {
                        let old_value = cell.value.load(Ordering::Acquire);
                        return Self::exchange_value(cell, value, old_value);
                    }

                    // Check for the same bucket:
                    if x & size_mask as u64 == 0 {
                        // A cell's visibility has just been published, attempt
                        // to set the link for it. This is usually redundant, however,
                        // if we don't attempt to set the link, the is no guarantee that
                        // the link chain is well-formed, and subsequent lookups could
                        // fail.
                        let offset = (index - prev_link_index) as u8;
                        prev_link.store(offset, Ordering::Relaxed);

                        // Now we need to go back to the start of the loop, and follow
                        // the probe chain from this index, now that the previous
                        // link has the delta value set ...
                        follow_link = true;
                        break;
                    }

                    // Continue to next cell for linear search ...
                    probes_remaining -= 1;
                }

                // If we are not supposed to go back to the start, then the table
                // is too full, and we need to increase the number of buckets.
                if !follow_link {
                    return ConcurrentInsertResult::Overflow(index + 1);
                }

                // Otherwise we needed to go back to the start of the loop so that
                // we follow the next link in the chain ...
            }
        }
    }

    /// Attempts to exhange the value of the `cell` with the `desired` value.
    ///
    /// If this succeeds, this will return [ConcurrentInsertResult::Replaced].
    /// The old value stored in the result will be `old_value` if the thread
    /// callling this function successfully exchanged the value. If it did not,
    /// but the value is not a redirect value, then `desired` will be returned
    /// since this is the same case as if this thread first won the race and then
    /// the other thread tried to exchange.
    ///
    /// If the exchange returns a redirect value then this will return a
    /// [ConcurrentInsertResult::Migration] with the `desired` value, which
    /// needs to be inserted into the new table.
    fn exchange_value(
        cell: &AtomicCell<K, V>,
        desired: V,
        old_value: V,
    ) -> ConcurrentInsertResult<V> {
        let exchange_result =
            cell.value
                .compare_exchange(old_value, desired, Ordering::AcqRel, Ordering::Relaxed);

        // Success: just return the old value, as the desired value is now stord.
        if exchange_result.is_ok() {
            if old_value.is_null() {
                return ConcurrentInsertResult::NewInsert;
            } else {
                return ConcurrentInsertResult::Replaced(old_value);
            }
        }

        // If the map is not being migrated, but we lost the race:
        let value = exchange_result.unwrap_err();
        if !value.is_redirect() {
            // There was a racing write or erasure to this cell. We can
            // treat this situation as if we just exchanged the value and
            // then the other thread did so just after, in which case our
            // desired value is the old value.
            return ConcurrentInsertResult::Replaced(desired);
        }

        // The value was updated to a redirect value, which means that
        // another thread tried to perform an insert but the table was too
        // small, so now we need to move all data to the new table and then
        // try to insert the desired value into the new map.
        ConcurrentInsertResult::Migration(desired)
    }

    /// Allocates and initializes buckets which will hold `cells` number of
    /// cells, using the provided `allocator`.
    //fn allocate_and_init_buckets(allocator: &A, cells: usize) -> *mut Bucket<K, V> {
    fn allocate_and_init_table(allocator: &A, cells: usize) -> *mut Table<K, V> {
        assert!(cells >= 4 && (cells % 2 == 0));
        let bucket_count = cells >> 2;
        let bucket_ptr =
            allocate::<Bucket<K, V>, A>(allocator, bucket_count, AllocationKind::Uninitialized);
        let buckets = unsafe { std::slice::from_raw_parts_mut(bucket_ptr, bucket_count) };

        // Since AtomicU8 and AtomicU64 are the same as u8 and u64 in memory,
        // we can write them as zero, rather than calling the atomic versions
        for bucket in buckets.iter_mut().take(bucket_count) {
            unsafe {
                let bucket_deltas = &mut bucket.deltas as *mut AtomicU8;
                std::ptr::write_bytes(bucket_deltas, 0, 8);
            };

            for cell in 0..4 {
                unsafe {
                    // We only need to write the hash as null, an can ignore th key.
                    let cell_hash = &mut bucket.cells[cell].hash as *mut AtomicHashedKey;
                    std::ptr::write_bytes(cell_hash, 0, 1);
                };

                // FIXME: Check if the stored type is directly writable ..
                let cell_value = &mut bucket.cells[cell].value;
                *cell_value = Atomic::new(V::null());
            }
        }

        let table_ptr = allocate::<Table<K, V>, A>(allocator, 1, AllocationKind::Uninitialized);
        let table = unsafe { &mut *table_ptr };

        table.buckets = bucket_ptr;
        table.size_mask = cells - 1;

        table_ptr
    }

    pub(crate) fn get_cell_at_index_mut(&'a self, index: usize) -> Option<RefMut<'a, K, V, H, A>> {
        let table = self.get_table(Ordering::Acquire);
        if index >= table.size() {
            return None;
        }

        let buckets = table.bucket_slice();
        let size_mask = table.size_mask;
        let cell = get_cell(buckets, index, size_mask);
        let cell_hash = cell.hash.load(Ordering::Relaxed);
        Some(RefMut::new(self, cell, cell_hash))
    }

    pub(crate) fn get_cell_at_index(&'a self, index: usize) -> Option<Ref<'a, K, V, H, A>> {
        let table = self.get_table(Ordering::Acquire);
        if index >= table.size() {
            return None;
        }

        let buckets = table.bucket_slice();
        let size_mask = table.size_mask;
        let cell = get_cell(buckets, index, size_mask);
        let cell_hash = cell.hash.load(Ordering::Relaxed);
        Some(Ref::new(self, cell, cell_hash))
    }

    /// Calculates the number of remaining migration units for the `size_mask`.
    #[inline]
    fn remaining_units(size_mask: usize) -> usize {
        size_mask / Self::MIGRATION_UNIT_SIZE + 1
    }
}

impl<K, V, H, A: Allocator> Drop for LeapMap<K, V, H, A> {
    fn drop(&mut self) {
        if self.is_allocated() {
            let table = self.get_table_mut(Ordering::SeqCst);

            let bucket_ptr = table.buckets;
            let bucket_count = table.size() >> 2;
            deallocate::<Bucket<K, V>, A>(&self.allocator, bucket_ptr, bucket_count);

            let table_ptr = self.table.load(Ordering::Relaxed);
            deallocate::<Table<K, V>, A>(&self.allocator, table_ptr, 1);
        }

        let migrator_ptr = self.migrator.load(Ordering::SeqCst);
        if !migrator_ptr.is_null() {
            let migrator = unsafe { &*migrator_ptr };
            while migrator.stale_tables_remaining() > 0 {
                migrator.cleanup_stale_table(&self.allocator);
            }
            deallocate::<Migrator<K, V>, A>(&self.allocator, migrator_ptr, 1);
        }
    }
}

impl<K, V, H, A> IntoIterator for LeapMap<K, V, H, A>
where
    K: Eq + Hash + Copy,
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

/// Returns the null hash value.
#[inline]
pub(crate) const fn null_hash() -> u64 {
    0u64
}

/// Gets a reference to a cell using the `index` to find the cell in the
/// `buckets` slice.
#[inline]
fn get_cell<K, V: Value>(
    buckets: &[Bucket<K, V>],
    index: usize,
    size_mask: usize,
) -> &AtomicCell<K, V> {
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
    &buckets[bucket_index].cells[cell_index]
}

/// Gets a delta value for the cell assosciated with the `index`  in the bucket
/// `slice`. If `first` is true, then this will return the first delta value,
/// while if `first` is false then this will return the second delta value.
#[inline]
fn get_delta<K, V>(
    buckets: &[Bucket<K, V>],
    index: usize,
    size_mask: usize,
    first: bool,
) -> &AtomicU8 {
    let offset = if first { 0 } else { 4 };
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
    &buckets[bucket_index].deltas[cell_index + offset]
}

/// Gets the first delta value for the cell assosciated with the `index` into
/// the bucket slice.
#[inline]
fn get_first_delta<K, V>(buckets: &[Bucket<K, V>], index: usize, size_mask: usize) -> &AtomicU8 {
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
    &buckets[bucket_index].deltas[cell_index]
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
fn get_second_delta<K, V>(buckets: &[Bucket<K, V>], index: usize, size_mask: usize) -> &AtomicU8 {
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
    &buckets[bucket_index].deltas[cell_index + 4]
}

/// Gets the index of the bucket for a raw `index` value, which `size_mask` is
/// a mask for the number of cell which can be stored in the buckets.
#[inline]
const fn get_bucket_index(index: usize, size_mask: usize) -> usize {
    (index & size_mask) >> 2
}

/// Gets the index of the cell within a bucket for the `index` which would be
/// used to get the bucket from a bucket slice.
#[inline]
const fn get_cell_index(index: usize) -> usize {
    index & 3
}

/// The type used for hashed keys.
type HashedKey = u64;

/// The atomic type of the hashed key.
type AtomicHashedKey = AtomicU64;

/// Result types when an insert into a [LeapMap].
pub(super) enum ConcurrentInsertResult<V> {
    /// The insertion found a cell for the key, replaced the old value with
    /// a new one, and returned the old value.
    Replaced(V),
    /// The insertion was performed with a new key, so a new cell was filled.
    NewInsert,
    /// The insertion found a cell whose value was stale, so the map data needs
    /// to be migrated, after which the value should be inserted into the migrated
    /// map.
    Migration(V),
    /// No new cell was found for the key withing the linear search range,
    /// so we overflowed the max delta value and need to move the map to
    /// a larger table.
    Overflow(usize),
}

/// Underlying table for a [LeapMap]. This stores a pointer to the buckets and
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

/// Struct which stores a cell in a concurrent hash map. A cell is simply a
/// hash (rather than the key iteself) and the value associated with the key
/// for which the hash is associated.
///
/// Here we need the value to be atomic. Since V is generic, it's possible that
/// there is no built-in atomic support for it, in which case the `Atomic`
/// type will fall back to using an efficient spinlock implementation.
pub struct AtomicCell<K, V> {
    /// The hashed value of the cell.
    pub(crate) hash: AtomicHashedKey,
    /// The key for the cell.
    pub(crate) key: Atomic<K>,
    /// The value assosciated with the hash.
    pub(crate) value: Atomic<V>,
}

/// Struct which stores buckets of cells. Each bucket stores four cells
/// and two delta values per cell. The first delta value for a cell provides
/// the offset to the cell which is the start of the probe chain for the cell.
/// The second delta value provides the offset to the next link in the probe
/// chain once a search along the probe chain has started (via the first offset
/// value).
pub(super) struct Bucket<K, V> {
    /// Delta values for the cells, see the above documentation for what each
    /// delta value means.
    deltas: [AtomicU8; 8],
    /// Cells for the bucket.
    cells: [AtomicCell<K, V>; 4],
}

/// A struct for a migration source, which stores a pointer to the source buckets
/// to migrate from, and the index in the source table.
struct MigrationSource<K, V> {
    /// A table for which the cells should be migrated from.
    table: AtomicPtr<Table<K, V>>,
    /// The index of the source.
    index: AtomicUsize,
}

impl<K, V> MigrationSource<K, V> {
    /// Returns the number of cells in the table.
    pub fn size(&self) -> usize {
        let table = unsafe { &*self.table.load(Ordering::Relaxed) };
        table.size_mask + 1
    }
}

/// A struct which migrates stale tables for a [LeapMap] into a non-stale
/// destination table.
struct Migrator<K, V> {
    /// Destination table for migrator.
    dst_table: AtomicPtr<Table<K, V>>,
    /// Sources to migrate from.
    sources: Vec<MigrationSource<K, V>>,
    /// Number of worker threads and a flag for migration completion.
    status: AtomicUsize,
    /// Number of units which need to be migrated.
    remaining_units: AtomicUsize,
    /// If the migration resulted in overflow.
    overflowed: AtomicBool,
    /// The number of source tables to migrate:
    num_source_tables: AtomicU32,
    /// Tables which have been migrated from and which need to be dealocated
    stale_sources: Vec<AtomicPtr<Table<K, V>>>,
    /// The index of the last visible stale source table.
    last_stale_source: AtomicU32,
    /// The index of the current stale source table to clean up.
    current_stale_source: AtomicU32,
}

impl<K, V> Migrator<K, V> {
    /// Mask for resetting the status.
    pub(super) const RESET_FLAG: usize = 0x00;
    /// Mask for migration complete flag:
    pub(super) const MIGRATION_COMPLETE_FLAG: usize = 0x01;
    /// Mask for initialization started.
    pub(super) const INITIALIZATION_START_FLAG: usize = 0x02;
    /// Mask for initialization complete.
    pub(super) const INITIALIZATION_END_FLAG: usize = 0x04;
    /// Mask of all initialization flags.
    pub const INITIALIZATION_MASK: usize =
        Self::INITIALIZATION_START_FLAG | Self::INITIALIZATION_END_FLAG;

    /// Mask for status flags.
    /// bit 0 : migration finished,
    /// bit 1 : initialization started.
    /// bit 2 : initialization finished.
    pub(super) const STATUS_MASK: usize = Self::MIGRATION_COMPLETE_FLAG | Self::INITIALIZATION_MASK;

    /// Number of stale source elements
    const STALE_SOURCES: usize = 32;
    /// Mask for stale source index.
    const STALE_CAPACITY_MASK: usize = Self::STALE_SOURCES - 1;

    /// Initializes the migrator.
    pub fn initialize(&mut self) {
        self.stale_sources = Vec::with_capacity(Self::STALE_SOURCES);
        for _ in 0..Self::STALE_SOURCES {
            self.stale_sources
                .push(AtomicPtr::<Table<K, V>>::new(std::ptr::null_mut()));
        }

        self.dst_table
            .store(std::ptr::null_mut(), Ordering::Relaxed);
        self.sources = vec![];
        self.status.store(Self::RESET_FLAG, Ordering::Relaxed);
        self.remaining_units.store(0, Ordering::Relaxed);
        self.overflowed.store(false, Ordering::Relaxed);
        self.num_source_tables.store(0, Ordering::Relaxed);
        self.last_stale_source.store(0, Ordering::Relaxed);
        self.current_stale_source.store(0, Ordering::Relaxed);
    }

    /// Set the flag which indicates that the migrator is being initialized. This
    /// returns true if flag was not set and the calling thread caused it to be
    /// set. It returns false if the flag was already set.
    fn set_initialization_begin_flag(&self) -> bool {
        let old = self
            .status
            .fetch_or(Self::INITIALIZATION_START_FLAG, Ordering::Relaxed);
        old & Self::INITIALIZATION_START_FLAG == 0
    }

    /// Sets the flag which indicates that the initialization process is complete.
    /// This returns true if the calling thread was the one which caused the flag
    /// to be set, otherwise it return false.
    fn set_initialization_complete_flag(&self) -> bool {
        let old = self
            .status
            .fetch_or(Self::INITIALIZATION_END_FLAG, Ordering::Relaxed);
        old & Self::INITIALIZATION_END_FLAG == 0
    }

    /// If the migrator has completed/is completing the migration.
    pub fn finishing(&self) -> bool {
        let status = self.status.load(Ordering::Relaxed);
        status & Self::MIGRATION_COMPLETE_FLAG == Self::MIGRATION_COMPLETE_FLAG || status == 0
    }

    /// If the migrator has completed initialization
    pub fn initialization_complete(&self) -> bool {
        self.status.load(Ordering::Relaxed) & Self::INITIALIZATION_MASK == Self::INITIALIZATION_MASK
    }

    /// This returns true if the migrator is in process, which is the time from
    /// which the initialization flag is set until the time at which the thread
    /// which finishes the migration sets the status to zero.
    pub fn in_process(&self) -> bool {
        self.status.load(Ordering::Relaxed) & Self::INITIALIZATION_START_FLAG
            == Self::INITIALIZATION_START_FLAG
    }

    /// Gets the index into the stale source buffer for the specified `index`.
    pub fn stale_source_index(&self, index: usize) -> usize {
        index & Self::STALE_CAPACITY_MASK
    }

    /// Returns the number of stale source tables to clean up.
    pub fn stale_tables_remaining(&self) -> u32 {
        self.last_stale_source.load(Ordering::Relaxed)
            - self.current_stale_source.load(Ordering::Relaxed)
    }

    /// Tries to clean up (deallocate) any stale source tables.
    pub fn cleanup_stale_table<A: Allocator>(&self, allocator: &A) {
        let current = self.current_stale_source.load(Ordering::Relaxed);
        let last_visible = self.last_stale_source.load(Ordering::Relaxed);

        // Check if there are any old source tables to clean up
        if current >= last_visible {
            return;
        }

        // There are sources to clean up, try and get one:
        if self
            .current_stale_source
            .compare_exchange(current, current + 1, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            // Won the race, we can deallocate the stale source for our index:
            let index = self.stale_source_index(current as usize);
            let table_ptr = self.stale_sources[index].load(Ordering::Relaxed);
            if table_ptr.is_null() {
                return;
            }

            let table = unsafe { &mut *table_ptr };
            let bucket_ptr = table.buckets;
            let bucket_count = table.size() >> 2;
            deallocate::<Bucket<K, V>, A>(allocator, bucket_ptr, bucket_count);
            deallocate::<Table<K, V>, A>(allocator, table_ptr, 1);
            self.stale_sources[index].store(std::ptr::null_mut(), Ordering::Relaxed);
        }

        // Lost the race, just return.
    }

    /// Performs the migration of a range of the buckets between `start_index`
    /// and `end_index` for the source with index `src_index. This returns true
    /// if the migration completed successfully.
    pub fn migrate_range<H, A>(
        &self,
        src_index: usize,
        start_index: usize,
        end_index: usize,
    ) -> bool
    where
        K: Hash + Eq + Copy,
        H: BuildHasher + Default,
        A: Allocator,
        V: Value,
    {
        let source = &self.sources[src_index];
        let src_table = unsafe { &*source.table.load(Ordering::Relaxed) };
        let src_size_mask = src_table.size_mask;
        let src_buckets = src_table.bucket_slice();

        let dst_table = unsafe { &*self.dst_table.load(Ordering::Relaxed) };
        let dst_size_mask = dst_table.size_mask;
        let dst_buckets = dst_table.bucket_slice();

        for index in start_index..end_index {
            let cell = get_cell(src_buckets, index, src_size_mask);

            loop {
                let src_hash = cell.hash.load(Ordering::Relaxed);

                // Check if we have an unused cell, in which case we need to put
                // a redirect marker in its place.
                if src_hash == null_hash() {
                    match cell.value.compare_exchange(
                        V::null(),
                        V::redirect(),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        // We placed the redirect
                        Ok(_) => break,
                        Err(old) => {
                            // Either redirect has already been placed
                            if old.is_redirect() {
                                break;
                            }
                        }
                    }

                    // Somone else just claimed the cell, read the hash again
                } else {
                    // Check for deleted/uninitialized value ...
                    let mut src_value = cell.value.load(Ordering::Relaxed);
                    if src_value.is_null() {
                        // Need to place a redirect as above:
                        match cell.value.compare_exchange(
                            src_value,
                            V::redirect(),
                            Ordering::Relaxed,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => break,
                            Err(old) => {
                                if old.is_redirect() {
                                    // Should never happen, this would be a race to place
                                    // a redirect on the cell, each thread should be
                                    // working on its own migration unit.
                                    break;
                                }
                            }
                        }
                    } else if src_value.is_redirect() {
                        // Already marked redirect from previous migration
                        break;
                    }

                    let src_key = cell.key.load(Ordering::Relaxed);

                    // We need to perform a migration of the cell. This should
                    // change. We actually want to get a reference to the cell
                    // here, and then try to exchange it here, rather than
                    // having insert_or_find perform the insert.
                    loop {
                        match LeapMap::<K, V, H, A>::insert_or_find(
                            src_hash,
                            &src_key,
                            src_value,
                            dst_buckets,
                            dst_size_mask,
                        ) {
                            ConcurrentInsertResult::Overflow(_) => {
                                // Overflow of destination when trying to insert.
                                // This will cause a failed migration and a new one
                                // in a larger table to be performed.
                                return false;
                            }
                            ConcurrentInsertResult::Migration(_) => {
                                // Failed to insert because a migration of the destination
                                // is required, need to resize and try again.
                                return false;
                            }
                            _ => {
                                // Succeeded, we need to update the source value to
                                // contain redirect as the value now exists in the new
                                // table.
                                match cell.value.compare_exchange(
                                    src_value,
                                    V::redirect(),
                                    Ordering::Relaxed,
                                    Ordering::Relaxed,
                                ) {
                                    Ok(_old) => {
                                        //debug_assert!(old == src_value);
                                        break;
                                    }
                                    Err(updated) => {
                                        // Another thread just managed to write or erase
                                        // the cell value, we need to update it and try
                                        // to re-migrate the cell.
                                        src_value = updated;
                                    }
                                }
                            }
                        }
                    }

                    // Migrated the cell, proceed to next cell:
                    break;
                }

                // Migrated the cell, proceed to next cell:
                //break;
            }
        }

        true
    }
}
