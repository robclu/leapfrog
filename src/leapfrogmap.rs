use crate::util::round_to_pow2;
use crate::{make_hash, MurmurHasher, Value};
use atomic::Atomic;
use std::alloc::{Allocator, Global, Layout};
use std::hash::{BuildHasher, BuildHasherDefault, Hash, Hasher};
use std::sync::atomic::{
    AtomicBool, AtomicPtr, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering,
};

/// The type used for hashed keys.
type HashedKey = u64;

/// The atomic type of the hashed key.
type AtomicHashedKey = AtomicU64;

/// Struct which stores a cell in a concurrent hash map. A cell is simply a
/// hash (rather than the key iteself) and the value associated with the key
/// for which the hash is associated.
///
/// Here we need the value to be atomic. Since V is generic, it's possible that
/// there is no built-in atomic support for it, in which case the `Atomic`
/// type will fall back to using an efficient spinlock implementation.
pub(super) struct AtomicCell<V> {
    /// The hashed value of the cell.
    hash: AtomicHashedKey,
    /// The value assosciated with the hash.
    value: Atomic<V>,
}

/// Struct which stores buckets of cells. Each bucket stores four cells
/// and two delta values per cell. The first delta value for a cell provides
/// the offset to the cell which is the start of the probe chain for the cell.
/// The second delta value provides the offset to the next link in the probe
/// chain once a search along the probe chain has started.
pub(super) struct Bucket<K, V> {
    /// Delta values for the cells. The first 4 values are the delta values to
    /// the start of the probe chain, and the second 4 values are the delta
    /// values to the next probe in the chain, for each cell, respectively.
    deltas: [AtomicU8; 8],
    /// Cells for the bucket.
    cells: [AtomicCell<V>; 4],
    /// Placeholder for the key.
    _key: std::marker::PhantomData<K>,
}

/// Allocates `bucket_count` buckets using the given allocator
fn allocate_buckets<K, V, A>(allocator: &A, bucket_count: usize) -> *mut Bucket<K, V>
where
    A: Allocator,
{
    let bucket_size = std::mem::size_of::<Bucket<K, V>>();
    let bucket_align = std::mem::align_of::<Bucket<K, V>>();

    // We unwrap here because we want to panic if we fail to get a valid layout
    let layout = Layout::from_size_align(bucket_size * bucket_count, bucket_align).unwrap();

    // Again, unwrap the allocation result, because we should never fail to
    // allocate.
    let bucket_ptr = allocator.allocate(layout).unwrap().as_ptr() as *mut Bucket<K, V>;
    bucket_ptr
}

/// Deallocates `bucket_count` buckets using the given allocator
fn deallocate_buckets<K, V, A>(allocator: &A, bucket_ptr: *mut Bucket<K, V>, bucket_count: usize)
where
    A: Allocator,
{
    let bucket_size = std::mem::size_of::<Bucket<K, V>>();
    let bucket_align = std::mem::align_of::<Bucket<K, V>>();

    // We unwrap here because we want to panic if we fail to get a valid layout
    let layout = Layout::from_size_align(bucket_size * bucket_count, bucket_align).unwrap();

    // Again, unwrap the non-null so that if we try to deallocate a null ptr
    // then this panics.
    let raw_ptr = bucket_ptr as *mut u8;
    let ptr = std::ptr::NonNull::new(raw_ptr).unwrap();
    unsafe {
        allocator.deallocate(ptr, layout);
    }
}

/// Allocates `bucket_count` buckets using the given allocator
fn allocate_migrator<K, V, A>(allocator: &A) -> *mut Migrator<K, V>
where
    A: Allocator,
{
    let size = std::mem::size_of::<Migrator<K, V>>();
    let align = std::mem::align_of::<Migrator<K, V>>();

    // We unwrap here because we want to panic if we fail to get a valid layout
    let layout = Layout::from_size_align(size, align).unwrap();

    // Again, unwrap the allocation result, because we should never fail to
    // allocate.
    let ptr = allocator.allocate(layout).unwrap().as_ptr() as *mut Migrator<K, V>;
    ptr
}

/// Deallocates `bucket_count` buckets using the given allocator
fn deallocate_migrator<K, V, A>(allocator: &A, migrator_ptr: *mut Migrator<K, V>)
where
    A: Allocator,
{
    let size = std::mem::size_of::<Migrator<K, V>>();
    let align = std::mem::align_of::<Migrator<K, V>>();

    // We unwrap here because we want to panic if we fail to get a valid layout
    let layout = Layout::from_size_align(size, align).unwrap();

    // Again, unwrap the non-null so that if we try to deallocate a null ptr
    // then this panics.
    let raw_ptr = migrator_ptr as *mut u8;
    let ptr = std::ptr::NonNull::new(raw_ptr).unwrap();
    unsafe {
        allocator.deallocate(ptr, layout);
    }
}

/// Defines the result of an insert into a [LeapfrogMap].
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

/// A concurrent HashMap implementation which uses a modified form of RobinHood/
/// Hopscotch probing.
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
/// This version *is* thread-safe, and items cana be added and removed from
/// any number of threads concurrently.
pub struct LeapfrogMap<K, V, H = BuildHasherDefault<MurmurHasher>, A: Allocator = Global> {
    /// Pointer to the buckets for the map. This needs to be a pointer to that
    /// we can atomically get the buckets for operations, since when the map
    /// is resized the buckets might change, and we need to ensure that all
    /// operations can identify if they have the correct buckets.
    buckets: AtomicPtr<Bucket<K, V>>,
    /// Mask for the size of the table.
    size_mask: AtomicUsize,
    /// The hasher for the map.
    hash_builder: H,
    /// Alloctor for the buckets.
    allocator: A,
    /// Map migration flag.
    migration_flag: AtomicBool,
    /// Migrator for moving buckets into larger storage.
    migrator: AtomicPtr<Migrator<K, V>>,
}

impl<K, V, H, A: Allocator> LeapfrogMap<K, V, H, A> {
    /// Gets the capacity of the hash map.
    pub fn capacity(&self) -> usize {
        self.size_mask.load(Ordering::Relaxed) + 1
    }

    /// Gets the number of buckets in the map.
    fn bucket_count(&self) -> usize {
        (self.size_mask.load(Ordering::Relaxed) + 1) >> 2
    }
}

impl<K, V, H> LeapfrogMap<K, V, H, Global>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + Default,
{
    /// Creates the hash map with space for the default number of elements, which
    /// will use the global allocator for allocation of the map data.
    pub fn new() -> LeapfrogMap<K, V, H, Global> {
        Self::new_in(Global)
    }

    /// Creates the hash map with space for `capacity` elements, which will use
    /// the global allocator for allocation of the map data.
    pub fn with_capacity(capacity: usize) -> LeapfrogMap<K, V, H, Global> {
        Self::with_capacity_in(capacity, Global)
    }
}

impl<K, V, H, A> LeapfrogMap<K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
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

    /// Number of cells per bucked.
    const CELLS_PER_BUCKET: usize = 4;

    /// The number of muckets to migrate as a unit.
    const MIGRATION_UNIT_SIZE: usize = 32;

    /// Creates the hash map with space for the default number of elements, using
    /// the provided `allocator` to allocate data for the map.
    pub fn new_in(allocator: A) -> LeapfrogMap<K, V, H, A> {
        Self::with_capacity_in(Self::INITIAL_SIZE, allocator)
    }

    /// Creates the hash map with space for the `capacity` number of elements
    /// using the provided `allocator`.
    ///
    /// # Arguments
    ///
    /// * `capacity`  - The number of elements the map should be created to hold.
    /// * `allocator` - The allocator for the map.
    pub fn with_capacity_in(capacity: usize, allocator: A) -> LeapfrogMap<K, V, H, A> {
        let bucket_ptr = Self::allocate_and_init_buckets(&allocator, capacity);
        let migrator_ptr = allocate_migrator(&allocator);
        LeapfrogMap {
            buckets: AtomicPtr::new(bucket_ptr),
            size_mask: AtomicUsize::new(capacity - 1),
            hash_builder: H::default(),
            allocator,
            migration_flag: AtomicBool::new(false),
            migrator: AtomicPtr::new(migrator_ptr),
        }
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
    pub fn insert(&self, key: K, mut value: V) -> Option<V> {
        let hash = make_hash::<K, _, H>(&self.hash_builder, &key);

        loop {
            // We need to get the pointer to the buckets which we are going to
            // attempt to insert into. The ideal ordering here would be Consume,
            // but we don't have that, so we use Acquire instead. For most platforms
            // the impact should be negligible, however, that mught not be the case
            // for ARM, so we should check this for those platforms.
            let buckets = self.bucket_slice_mut(Ordering::Acquire);
            let size_mask = self.size_mask.load(Ordering::Relaxed);

            //match Self::insert_or_find(hash, value, buckets, size_mask) {
            match Self::insert_or_find(hash, value, buckets, size_mask) {
                ConcurrentInsertResult::Overflow(overflow_index) => {
                    // Need to resize the map:
                    //self.move_to_new_buckets(overflow_index);

                    // Try and create the table migration. Only a single thread
                    // should do this. Any threads which don't get the flag should
                    // start cleaning up old tables which have not been deallocated.
                    let mut migrator = unsafe { &mut *self.migrator.load(Ordering::Relaxed) };
                    if self.acquire_migration_flag() {
                        Self::create_migrator(
                            &self.allocator,
                            &mut migrator,
                            buckets,
                            size_mask,
                            overflow_index,
                        );
                        self.release_migration_flag();
                    } else {
                        // Clean up old migration tables ...

                        // Wait for migrator to be created ...
                        while self.migration_flag.load(Ordering::Relaxed) {
                            std::hint::spin_loop();
                        }
                    }

                    // Migration is created, all threads can see updates, now migrate:
                    Self::perform_migration(
                        &self.allocator,
                        migrator,
                        &self.buckets,
                        &self.size_mask,
                    );

                    // Threads which
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
                    let migrator = unsafe { &mut *self.migrator.load(Ordering::Relaxed) };

                    // First check if that migration is in the completion stage,
                    // in which case we should go and clean up some of the old
                    // migration tables.
                    if migrator.finished() {
                        // Clean up old tables ...
                    }

                    // Otherwise we need to join in the migration;
                    Self::perform_migration(
                        &self.allocator,
                        migrator,
                        &self.buckets,
                        &self.size_mask,
                    );
                }
            }
        }
    }

    fn acquire_migration_flag(&self) -> bool {
        self.migration_flag
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .map_or(false, |_| true)
    }

    fn release_migration_flag(&self) {
        self.migration_flag.store(false, Ordering::Relaxed);
    }

    // Creates the `migrator`, which should migrate from the old `buckets`. Only
    // a single thread must do this, so `acquire_migration_flag` should be called
    // prior to calling this.
    fn create_migrator(
        allocator: &A,
        migrator: &mut Migrator<K, V>,
        buckets: &mut [Bucket<K, V>],
        size_mask: usize,
        overflow_index: usize,
    ) {
        // Estimate the number of cells. We only want a single thread to be
        // doing this, we we attempt to acquire the flag for migration table
        // creation. If we fail to do so, we then try and clean up old tables.

        let mut index = overflow_index - Self::CELLS_IN_USE;
        let mut cells_in_use = 0;

        for _ in 0..Self::CELLS_IN_USE {
            let cell = get_cell(buckets, index, size_mask);
            if cell.value.load(Ordering::Relaxed) != V::default() {
                cells_in_use += 1;
            }
            index += 1;
        }

        // Estimate how much we need to resize by:
        let ratio = cells_in_use as f32 / Self::CELLS_IN_USE as f32;
        let in_use_estimated = (size_mask + 1) as f32 * ratio;
        let estimated = round_to_pow2((in_use_estimated * 2.0) as usize);
        let new_table_size = estimated.max(Self::INITIAL_SIZE as usize);

        // Create the migrator:
        migrator.dst_buckets.store(
            Self::allocate_and_init_buckets(&allocator, new_table_size),
            Ordering::Relaxed,
        );
        migrator.dst_size_mask = new_table_size - 1;
        migrator.status.store(0, Ordering::Relaxed);
        migrator
            .remaining_units
            .store(Self::remaining_units(size_mask), Ordering::Relaxed);
        migrator.overflowed.store(false, Ordering::Relaxed);
        migrator.num_source_tables.store(1, Ordering::Relaxed);

        let source_ptr = &mut buckets[0] as *mut Bucket<K, V>;
        let source = MigrationSource::<K, V> {
            buckets: AtomicPtr::new(source_ptr),
            index: AtomicUsize::new(0),
            size_mask,
        };
        if migrator.sources.len() < 1 {
            migrator.sources.push(source);
        } else {
            migrator.sources[0] = source;
        }
    }

    fn perform_migration(
        allocator: &A,
        migrator: &mut Migrator<K, V>,
        dst_bucket_ptr: &AtomicPtr<Bucket<K, V>>,
        dst_size_mask: &AtomicUsize,
    ) {
        // Increment the number of workers for the migrator.
        let mut status = migrator.status.load(Ordering::Relaxed);
        loop {
            if status & 1 == 1 {
                // Migration is finished, we can break
                return;
            }
            // Last bit is flag for completion, hence + 2:
            match migrator.status.compare_exchange_weak(
                status,
                status + 2,
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
            let source = &migrator.sources[i as usize];
            loop {
                if migrator.finished() {
                    finished = true;
                    break;
                }

                // Check if this source has finished migration. If it is, we need
                // to move on to the next source:
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
        if migrator.status.fetch_sub(2, Ordering::AcqRel) >= 4 {
            // We aren't the last thread here, so we can exit.
            return;
        }

        // We are the last thread, complete the migration:
        // Set the migration acquire flag, just in case ...
        debug_assert!(migrator.status.load(Ordering::Relaxed) == 3);
        if migrator.overflowed.load(Ordering::Relaxed) {
            // Overflow of destination table, move the destination table to be
            // a source in the migrator, create a new destination table, and
            // then break so that we can try again:
            let buckets = migrator.dst_buckets.load(Ordering::Relaxed);
            let size_mask = migrator.dst_size_mask;

            let mut remaining_units = Self::remaining_units(size_mask);
            for source in &migrator.sources {
                remaining_units += Self::remaining_units(source.size_mask);
                source.index.store(0, Ordering::Relaxed);
            }

            migrator.sources.push(MigrationSource {
                buckets: AtomicPtr::new(buckets),
                index: AtomicUsize::new(0),
                size_mask,
            });

            migrator
                .remaining_units
                .store(remaining_units, Ordering::Relaxed);

            // Create the new buckets for the migrator:
            migrator.dst_buckets.store(
                Self::allocate_and_init_buckets(&allocator, (size_mask + 1) * 2),
                Ordering::Relaxed,
            );
            migrator.dst_size_mask = (size_mask + 1) * 2 - 1;
        } else {
            // Migration was successful, we can update the migrator. Here
            // we only set the variables which we need to:
            migrator.overflowed.store(false, Ordering::Relaxed);

            // FIXME: Move the source buckets into the cleanup queue:
            for _ in 0..num_sources {
                // ...
            }

            // Swap the bucket pointer for the new map
            dst_bucket_ptr.store(
                migrator.dst_buckets.load(Ordering::Relaxed),
                Ordering::Relaxed,
            );
            dst_size_mask.store(migrator.dst_size_mask, Ordering::Relaxed);
            migrator
                .dst_buckets
                .store(std::ptr::null_mut(), Ordering::Relaxed);

            // Finally we can set that we are done!
            migrator.status.store(0, Ordering::Relaxed);
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
    pub(super) fn insert_or_find(
        hash: HashedKey,
        value: V,
        buckets: &mut [Bucket<K, V>],
        size_mask: usize,
    ) -> ConcurrentInsertResult<V> {
        let mut index = hash as usize;

        // Start by checking the hashed cell. It's quite unlikely that it belongs
        // to the bucket it hashes to, but this is fast if it does.
        {
            let mut cell = get_cell_mut(buckets, index, size_mask);
            let probe_hash = cell.hash.load(Ordering::Relaxed);

            if probe_hash == HashedKey::null() {
                if cell
                    .hash
                    .compare_exchange(probe_hash, hash, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
                {
                    // Succeeded in setting the hash and claiming the cell, try
                    // and exchange the value:
                    return Self::exchange_value(&mut cell, value, V::null());
                }
            }

            // Hash already in table, exchange and return the value.
            if probe_hash == hash {
                let old_value = cell.value.load(Ordering::Acquire);

                // Check if the table is being moved:
                if old_value == V::redirect() {
                    return ConcurrentInsertResult::Migration(value);
                }

                // Otherwise try and exchange the old value with the new one.
                return Self::exchange_value(cell, value, old_value);
            }
        }

        // Follow the linked probes to find a new cell.
        // Here, we get the offset delta which will allow us to find the desired
        // bucket. After that, we need to use the second set of delta values to
        // walk along the chain. At each point, we check if the hash is a match;
        // if we find a match, then we have found the cell.
        let max_index = index + size_mask;
        debug_assert!(max_index as i64 - index as i64 >= 0);

        let mut probe_delta = get_first_delta(buckets, index, size_mask).load(Ordering::Relaxed);
        let first_delta = if probe_delta == 0 { true } else { false };

        loop {
            let mut follow_link = false;

            // Search the probe chain for this cell:
            if probe_delta != 0 {
                index += probe_delta as usize;

                // Update the delta value for the next iteration:
                probe_delta = get_first_delta(buckets, index, size_mask).load(Ordering::Relaxed);

                let cell = get_cell_mut(buckets, index, size_mask);
                let mut probe_hash = cell.hash.load(Ordering::Relaxed);
                if probe_hash == HashedKey::null() {
                    // The cell has been linked to the probe chain, but the hash
                    // is not yet visible. We chould change this here to use
                    // acquire and release, which would guarantee that the change
                    // is visible, but it's easier to just poll: FIXME
                    loop {
                        probe_hash = cell.hash.load(Ordering::Relaxed);
                        if probe_hash != HashedKey::null() {
                            break;
                        }
                    }

                    // Only hashes in the same bucket can be linked:
                    debug_assert!((probe_hash ^ hash) as usize & size_mask == 0);

                    if probe_hash == hash {
                        let old_value = cell.value.load(Ordering::Acquire);

                        // Check if the table is being moved:
                        if old_value == V::redirect() {
                            return ConcurrentInsertResult::Migration(value);
                        }

                        return Self::exchange_value(cell, value, old_value);
                    }
                }

                // We updated the index and the delta value, so we will go back
                // to the start of the loop and search the next probe in the chain ...
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
                    let cell = get_cell_mut(buckets, index, size_mask);
                    let probe_hash = cell.hash.load(Ordering::Relaxed);
                    if probe_hash == HashedKey::default() {
                        // Same as above, there is an empty cell, we we want to
                        // try and reserve it. If we lose the race here, then
                        // we just fall through to the next stage ...
                        if cell
                            .hash
                            .compare_exchange(
                                probe_hash,
                                hash,
                                Ordering::Relaxed,
                                Ordering::Relaxed,
                            )
                            .is_ok()
                        {
                            // Now link the cell to the previous cell in the same bucket:
                            let offset = (index - prev_link_index) as u8;

                            // In debug, we can perform an exchange here to get the old
                            // value and check that it's correct, but we just store for release.
                            if first_delta {
                                get_first_delta_mut(buckets, prev_link_index, size_mask)
                                    .store(offset, Ordering::Relaxed);
                            } else {
                                get_second_delta_mut(buckets, prev_link_index, size_mask)
                                    .store(offset, Ordering::Relaxed);
                            }

                            return ConcurrentInsertResult::NewInsert;
                        }
                    }

                    // Check for the same hash, so we can replace:
                    let x = hash ^ probe_hash;
                    if x != 0 {
                        let old_value = cell.value.load(Ordering::Relaxed);
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
                        if first_delta {
                            get_first_delta_mut(buckets, prev_link_index, size_mask)
                                .store(offset, Ordering::Relaxed);
                        } else {
                            get_second_delta_mut(buckets, prev_link_index, size_mask)
                                .store(offset, Ordering::Relaxed);
                        }

                        // Now we need to go back to the start of the loop, and follow
                        // the probe chain:
                        follow_link = true;
                        break;
                    }

                    // This is single threaded map, so it's impossible for the hash
                    // which is a match to appear outside of the probe chain.
                    //debug_assert!(cell.hash != hash);
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
        cell: &mut AtomicCell<V>,
        desired: V,
        old_value: V,
    ) -> ConcurrentInsertResult<V> {
        let exchange_result =
            cell.value
                .compare_exchange(old_value, desired, Ordering::Release, Ordering::Relaxed);

        // Success: just return the old value, as the desired value is now stord.
        if exchange_result.is_ok() {
            // Success, we can return the old value
            return ConcurrentInsertResult::Replaced(old_value);
        }

        // If the map is not being migrated, but we lost the race:
        let value = exchange_result.unwrap_err();
        if value != V::redirect() {
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
    fn allocate_and_init_buckets(allocator: &A, cells: usize) -> *mut Bucket<K, V> {
        assert!(cells >= 4 && (cells % 2 == 0));
        let bucket_count = cells >> 2;
        let bucket_ptr = allocate_buckets(&allocator, bucket_count);
        let buckets = unsafe { std::slice::from_raw_parts_mut(bucket_ptr, bucket_count) };

        // Since AtomicU8 and AtomicU64 are the same as u8 and u64 in memory,
        // we can write them as zero, rather than calling the atomic versions
        for i in 0..bucket_count {
            unsafe {
                let bucket_deltas = &mut buckets[i].deltas as *mut AtomicU8;
                std::ptr::write_bytes(bucket_deltas, 0, 8);
            };

            for cell in 0..4 {
                unsafe {
                    let cell_hash = &mut buckets[i].cells[cell].hash as *mut AtomicHashedKey;
                    std::ptr::write_bytes(cell_hash, 0, 1);
                };

                // FIXME: We should check if the stored type is directly writable ..
                let cell_value = &mut buckets[i].cells[cell].value;
                *cell_value = Atomic::new(V::default());
            }
        }

        bucket_ptr
    }

    /// Create a mutable slice of buckets from a pointer to the buckets and the
    /// number of buckets.
    #[inline]
    fn bucket_slice_mut(&self, ordering: Ordering) -> &mut [Bucket<K, V>] {
        let buckets = self.buckets.load(ordering);
        let len = self.bucket_count();
        unsafe { std::slice::from_raw_parts_mut(buckets, len) }
    }

    /// Create a slice of buckets from a pointer to the buckets and the number
    /// of buckets.
    #[inline]
    fn bucket_slice(&self, ordering: Ordering) -> &[Bucket<K, V>] {
        let buckets = self.buckets.load(ordering);
        let len = self.bucket_count();
        unsafe { std::slice::from_raw_parts(buckets, len) }
    }

    #[inline]
    fn remaining_units(size_mask: usize) -> usize {
        size_mask / Self::MIGRATION_UNIT_SIZE + 1
    }
}

/// Gets a  reference mutable to a cell for the `index` from the `buckets`.
///
/// * `buckets`   - The buckets to find the cell in.
/// * `index`     - The raw index value to convert to a bucket and cell index.
/// * `size_mask` - A mask for the number of elements in the buckets.
#[inline]
fn get_cell<K, V: Value>(
    buckets: &[Bucket<K, V>],
    index: usize,
    size_mask: usize,
) -> &AtomicCell<V> {
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
    &buckets[bucket_index].cells[cell_index]
}

/// Gets a mutable reference mutable to a cell for the `index` from the
/// `buckets`.
///
/// * `buckets`   - The buckets to find the cell in.
/// * `index`     - The raw index value to convert to a bucket and cell index.
/// * `size_mask` - A mask for the number of elements in the buckets.
#[inline]
fn get_cell_mut<K, V: Value>(
    buckets: &mut [Bucket<K, V>],
    index: usize,
    size_mask: usize,
) -> &mut AtomicCell<V> {
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
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
fn get_first_delta<K, V>(buckets: &[Bucket<K, V>], index: usize, size_mask: usize) -> &AtomicU8 {
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
    &buckets[bucket_index].deltas[cell_index]
}

/// Gets a mutable reference to the first delta value for a cell with the
/// given `index`. The first delta value gives the offset to the start of
/// the probe chain for bucket assosciated with the `index`.
///
/// * `buckets`   - The buckets to find the cell in.
/// * `index`     - The raw index value to convert to a bucket and cell index.
/// * `size_mask` - A mask for the number of elements in the buckets.
#[inline]
fn get_first_delta_mut<K, V>(
    buckets: &mut [Bucket<K, V>],
    index: usize,
    size_mask: usize,
) -> &mut AtomicU8 {
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
    &mut buckets[bucket_index].deltas[cell_index]
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

/// Gets a mutable reference to the first delta value for a cell with the
/// given `index`. The first delta value gives the offset to the start of
/// the probe chain for bucket assosciated with the `index`.
///
/// * `buckets`   - The buckets to find the cell in.
/// * `index`     - The raw index value to convert to a bucket and cell index.
/// * `size_mask` - A mask for the number of elements in the buckets.
#[inline]
fn get_second_delta_mut<K, V>(
    buckets: &mut [Bucket<K, V>],
    index: usize,
    size_mask: usize,
) -> &mut AtomicU8 {
    let bucket_index = get_bucket_index(index, size_mask);
    let cell_index = get_cell_index(index);
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

impl<K, V, H, A: Allocator> Drop for LeapfrogMap<K, V, H, A> {
    fn drop(&mut self) {
        let bucket_ptr = self.buckets.load(Ordering::SeqCst);
        let bucket_count = self.bucket_count();
        deallocate_buckets(&self.allocator, bucket_ptr, bucket_count);

        // We don't need to deallocate the buckets for the migrator, since that
        // has already been handled.
        let migrator_ptr = self.migrator.load(Ordering::SeqCst);
        deallocate_migrator(&self.allocator, migrator_ptr);
    }
}

/// A struct for a migration source, which stores a pointer to the source buckets
/// to migrate from, and the index in the source table.
struct MigrationSource<K, V> {
    /// The source buckets to migrate from.
    buckets: AtomicPtr<Bucket<K, V>>,
    /// The index of the source.
    index: AtomicUsize,
    /// The size mask for the bucket to migrate.
    size_mask: usize,
}

impl<K, V> MigrationSource<K, V> {
    pub const fn size(&self) -> usize {
        self.size_mask + 1
    }
}

/// A struct which migrates the storage for a [ConcurrentHashMap].
struct Migrator<K, V> {
    /// Pointer to the destination buckets to migrate to.
    dst_buckets: AtomicPtr<Bucket<K, V>>,
    /// Size mask for the destination:
    dst_size_mask: usize,
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
}

impl<K, V: Value> Migrator<K, V> {
    /// Creates a new table migrator.
    pub fn new() -> Migrator<K, V> {
        Migrator {
            dst_buckets: AtomicPtr::new(std::ptr::null_mut()),
            dst_size_mask: 0,
            sources: vec![],
            status: AtomicUsize::new(0),
            remaining_units: AtomicUsize::new(0),
            overflowed: AtomicBool::new(false),
            num_source_tables: AtomicU32::new(0),
        }
    }

    /// If the migrator has completed the migration.
    pub fn finished(&self) -> bool {
        self.status.load(Ordering::Relaxed) & 1 == 1
    }

    /// Performs the migration of a range of the buckets.
    pub fn migrate_range<H, A>(
        &self,
        src_index: usize,
        start_index: usize,
        end_index: usize,
    ) -> bool
    where
        K: Hash + Eq + Clone,
        H: BuildHasher + Default,
        A: Allocator,
    {
        let source = &self.sources[src_index];
        let src_size_mask = source.size_mask;
        let src_bucket_ptr = source.buckets.load(Ordering::Relaxed);
        let src_buckets =
            unsafe { std::slice::from_raw_parts_mut(src_bucket_ptr, (src_size_mask + 1) >> 2) };

        let dst_size_mask = self.dst_size_mask;
        let dst_bucket_ptr = self.dst_buckets.load(Ordering::Relaxed);
        let dst_buckets =
            unsafe { std::slice::from_raw_parts_mut(dst_bucket_ptr, (dst_size_mask + 1) >> 2) };

        for index in start_index..end_index {
            let mut cell = get_cell_mut(src_buckets, index, src_size_mask);

            loop {
                let src_hash = cell.hash.load(Ordering::Relaxed);

                // Check if we have an unused cell, in which case we need to put
                // a redirect marker in its place.
                if src_hash == HashedKey::default() {
                    match cell.value.compare_exchange(
                        V::default(),
                        V::redirect(),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        // We placed the redirect
                        Ok(_) => break,
                        Err(old) => {
                            // Either redirect has already been placed
                            if old == V::redirect() {
                                break;
                            }
                        }
                    }

                    // Somone else just claimed the cell, read the hash again
                } else {
                    // Check for deleted/uninitialized value ...
                    let mut src_value = cell.value.load(Ordering::Relaxed);
                    if src_value == V::default() {
                        // Need to place a redirect as above:
                        match cell.value.compare_exchange(
                            src_value,
                            V::redirect(),
                            Ordering::Relaxed,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => break,
                            Err(old) => {
                                if old == V::redirect() {
                                    // Should never happen, this would be a race to place
                                    // a redirect on the cell, each thread should be
                                    // working on its own migration unit.
                                    break;
                                }
                            }
                        }
                    } else if src_value == V::redirect() {
                        // Already marked redirect from previous migration
                        break;
                    }

                    // We need to perform a migration of the cell. This should
                    // change. We actually want to get a reference to the cell
                    // here, and then try to exchange it here, rather than
                    // having insert_or_find perform the insert.
                    loop {
                        match LeapfrogMap::<K, V, H, A>::insert_or_find(
                            src_hash,
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
                                    Ok(old) => {
                                        debug_assert!(old == src_value);
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
                }

                // Migrated the cell, proceed to next cell:
                break;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core_affinity::CoreId;
    use rand::{thread_rng, Rng};
    use std::sync::Arc;

    const NUM_THREADS: u64 = 32;
    const KEYS_TO_INSERT: u64 = (1 << 24) / NUM_THREADS; //204_800_000;

    fn insert_keys(
        map: &Arc<LeapfrogMap<u64, u64>>,
        relative_prime: u64,
        start_index: u64,
        thread_index: u64,
    ) {
        let mut index = start_index + thread_index * (KEYS_TO_INSERT + 2);
        for _ in 0..KEYS_TO_INSERT {
            let key = index.wrapping_mul(relative_prime);
            let key = key ^ (key >> 16);
            if key != u64::default() && key != u64::MAX {
                match map.insert(key, key) {
                    Some(_) => {
                        // Replaced key ..
                    }
                    None => {}
                }
            }
            index += 1;
        }
    }

    #[test]
    fn create_map() {
        const ELEMENTS: usize = 100;
        let leapfrog_map = Arc::new(LeapfrogMap::<u32, u32>::with_capacity(ELEMENTS));

        let mut threads = vec![];
        for _ in 0..4 {
            let map = leapfrog_map.clone();
            threads.push(std::thread::spawn(move || {
                core_affinity::set_for_current(CoreId { id: 0 });
                assert_eq!(map.capacity(), ELEMENTS);
            }));
        }

        for t in threads {
            t.join().unwrap();
        }
    }

    #[test]
    fn insert_different_keys() {
        let leapfrog_map = Arc::new(LeapfrogMap::<u64, u64>::with_capacity(
            KEYS_TO_INSERT as usize,
        ));

        let mut rng = thread_rng();
        let start_index: u64 = rng.gen();
        let value: u64 = rng.gen();
        let relative_prime: u64 = value.wrapping_mul(2) + 1;

        let mut threads = vec![];
        let start_flag = Arc::new(AtomicU64::new(0));

        for i in 0..NUM_THREADS {
            let map = leapfrog_map.clone();
            let flag = start_flag.clone();
            threads.push(std::thread::spawn(move || {
                core_affinity::set_for_current(CoreId { id: i as usize });

                flag.fetch_add(1, Ordering::Relaxed);
                while flag.load(Ordering::Relaxed) < NUM_THREADS {
                    std::hint::spin_loop();
                }
                let start = std::time::Instant::now();
                insert_keys(&map, relative_prime, start_index, i);

                let end = std::time::Instant::now();
                let time = (end - start).as_millis();
                println!(
                    "Thread: {}, {} ms, {} keys/sec",
                    i,
                    time,
                    KEYS_TO_INSERT as f32 * (1000 as f32 / time as f32)
                );
            }));
        }

        for t in threads {
            t.join().unwrap();
        }
    }
}
