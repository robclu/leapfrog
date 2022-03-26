use crate::{
    leapmap::{AtomicCell, LeapMap},
    Value,
};
use core::alloc::Allocator;
use core::hash::{BuildHasher, Hash};
use core::sync::atomic::Ordering;

/// A reference to an atomic cell in a [LeapMap], which cannot mutate
/// the referenced cell value.
pub struct Ref<'a, K, V, H, A: Allocator> {
    /// The atomic value which is being referenced.
    cell: &'a AtomicCell<K, V>,
    /// Reference to the map in which the cell belongs.
    map: &'a LeapMap<K, V, H, A>,
    /// The hash for the cell at the point when the cell was found
    pub(crate) hash: u64,
}

impl<'a, K, V, H, A> Ref<'a, K, V, H, A>
where
    A: Allocator,
    V: Value,
{
    /// Creates a new ref type referencing the specified `cell` and `map`.
    pub fn new(
        map: &'a LeapMap<K, V, H, A>,
        cell: &'a AtomicCell<K, V>,
        hash: u64,
    ) -> Ref<'a, K, V, H, A> {
        Ref { map, cell, hash }
    }

    /// Loads the key for the referenced cell.
    ///
    /// This requires `&mut self` since it's possible that the underlying data
    /// for the map has been migrated, and that therefore the referenced cell
    /// is out of date, and returning the current value will be incorrect. In
    /// such a case, the cell needs to be updated to reference the correct cell,
    /// hence `mut self`. This ensures that the returned value is always the
    /// most up to date value.
    ///
    /// It is also possible that the cell has been deleted, in which case the
    /// returned value will be `None`
    pub fn key(&mut self) -> Option<K>
    where
        K: Eq + Hash + Copy,
        H: BuildHasher + Default,
    {
        self.key_value().map(|(k, _v)| k)
    }

    /// Loads the value for the referenced cell.
    ///
    /// This requires `&mut self` since it's possible that the underlying data
    /// for the map has been migrated, and that therefore the referenced cell
    /// is out of date, and returning the current value will be incorrect. In
    /// such a case, the cell needs to be updated to reference the correct cell,
    /// hence `mut self`. This ensures that the returned value is always the
    /// most up to date value.
    ///
    /// It is also possible that the cell has been deleted, in which case the
    /// returned value will be `None`
    pub fn value(&mut self) -> Option<V>
    where
        K: Eq + Hash + Copy,
        H: BuildHasher + Default,
    {
        self.key_value().map(|(_k, v)| v)
    }

    /// Loads the key-value pair for the referenced cell.
    ///
    /// This requires `&mut self` since it's possible that the underlying data
    /// for the map has been migrated, and that therefore the referenced cell
    /// is out of date, and returning the current value will be incorrect. In
    /// such a case, the cell needs to be updated to reference the correct cell,
    /// hence `mut self`. This ensures that the returned value is always the
    /// most up to date value.
    ///
    /// It is also possible that the cell has been deleted, in which case the
    /// returned value will be `None`.
    pub fn key_value(&mut self) -> Option<(K, V)>
    where
        K: Eq + Hash + Copy,
        H: BuildHasher + Default,
    {
        loop {
            let value = self.cell.value.load(Ordering::Relaxed);
            let key = self.cell.key.load(Ordering::Relaxed);
            if value.is_redirect() || self.hash != self.cell.hash.load(Ordering::Relaxed) {
                // Map has/is being migrated, help and then try again ...
                self.map.participate_in_migration();
                if let Some(new_cell) = self.map.find(&key, self.hash) {
                    self.cell = new_cell;
                } else {
                    // Migration caused removal of cell:
                    return None;
                }
            } else {
                return Some((key, value));
            }
        }
    }
}

/// A reference type to a cell in a [`LeapMap`] which can mutate the referenced
/// cell value.
pub struct RefMut<'a, K, V, H, A: Allocator> {
    /// The atomic value which is being referenced.
    cell: &'a AtomicCell<K, V>,
    /// Reference to the map in which the cell belongs.
    map: &'a LeapMap<K, V, H, A>,
    /// The hash for the cell at the point when the cell was found
    pub(crate) hash: u64,
}

impl<'a, K, V, H, A> RefMut<'a, K, V, H, A>
where
    A: Allocator,
    V: Value,
{
    /// Creates a new mutable reference type referencing the specified `cell`
    /// and `map`.
    pub fn new(
        map: &'a LeapMap<K, V, H, A>,
        cell: &'a AtomicCell<K, V>,
        hash: u64,
    ) -> RefMut<'a, K, V, H, A> {
        RefMut { map, cell, hash }
    }

    /// Loads the key for the referenced cell.
    ///
    /// This requires `&mut self` since it's possible that the underlying data
    /// for the map has been migrated, and that therefore the referenced cell
    /// is out of date, and returning the current value will be incorrect. In
    /// such a case, the cell needs to be updated to reference the correct cell,
    /// hence `mut self`. This ensures that the returned value is always the
    /// most up to date value.
    ///
    /// It is also possible that the cell has been deleted, in which case the
    /// returned value will be `None`
    pub fn key(&mut self) -> Option<K>
    where
        K: Eq + Hash + Copy,
        H: BuildHasher + Default,
    {
        self.key_value().map(|(k, _v)| k)
    }

    /// Loads the value for the referenced cell.
    ///
    /// This requires `&mut self` since it's possible that the underlying data
    /// for the map has been migrated, and that therefore the referenced cell
    /// is out of date, and returning the current value will be incorrect. In
    /// such a case, the cell needs to be updated to reference the correct cell,
    /// hence `mut self`. This ensures that the returned value is always the
    /// most up to date value.
    ///
    /// It is also possible that the cell has been deleted, in which case the
    /// returned value will be `None`
    pub fn value(&mut self) -> Option<V>
    where
        K: Eq + Hash + Copy,
        H: BuildHasher + Default,
    {
        self.key_value().map(|(_k, v)| v)
    }

    /// Loads the key-value pair for the referenced cell.
    ///
    /// This requires `&mut self` since it's possible that the underlying data
    /// for the map has been migrated, and that therefore the referenced cell
    /// is out of date, and returning the current value will be incorrect. In
    /// such a case, the cell needs to be updated to reference the correct cell,
    /// hence `mut self`. This ensures that the returned value is always the
    /// most up to date value.
    ///
    /// It is also possible that the cell has been deleted, in which case the
    /// returned value will be `None`.
    pub fn key_value(&mut self) -> Option<(K, V)>
    where
        K: Eq + Hash + Copy,
        H: BuildHasher + Default,
    {
        loop {
            let value = self.cell.value.load(Ordering::Relaxed);
            let key = self.cell.key.load(Ordering::Relaxed);
            if value.is_redirect() || self.hash != self.cell.hash.load(Ordering::Relaxed) {
                // Map has/is being migrated, help and then try again ...
                self.map.participate_in_migration();
                if let Some(new_cell) = self.map.find(&key, self.hash) {
                    self.cell = new_cell;
                } else {
                    // Migration caused removal of cell:
                    return None;
                }
            } else {
                return Some((key, value));
            }
        }
    }

    /// Sets the value for the referenced cell, returning the old value if the
    /// cell is still valid, or `None` if the cell has been deleted.
    ///
    /// This requires `&mut self` since it's possible that the underlying data
    /// for the map has been migrated, and that therefore the referenced cell
    /// is out of date, and returning the current value will be incorrect. In
    /// such a case, the cell needs to be updated to reference the correct cell,
    /// hence `mut self`. This ensures that the store is only performed if the
    /// referenced cell is still valid.
    pub fn set_value(&mut self, value: V) -> Option<V>
    where
        K: Eq + Hash + Copy,
        H: BuildHasher + Default,
    {
        loop {
            let current = self.cell.value.load(Ordering::Relaxed);

            if current.is_redirect() || self.hash != self.cell.hash.load(Ordering::Relaxed) {
                // Map has/is being migrated, help and then try again ...
                self.map.participate_in_migration();
                let key = self.cell.key.load(Ordering::Relaxed);
                if let Some(new_cell) = self.map.find(&key, self.hash) {
                    self.cell = new_cell;
                } else {
                    // Cell has been removed
                    return None;
                }
            } else if current.is_null() {
                // Value has been erased, we can just return.
                return None;
            } else if self
                .cell
                .value
                .compare_exchange_weak(current, value, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok()
            {
                return Some(current);
            }
        }
    }

    /// Updates the value for the referenced cell, using the `func` to compute
    /// the new value, returning the old value if the cell is still in the map,
    /// and `None` if the cell has been deleted.
    ///
    /// # Examples
    ///
    /// ```
    /// let map = leapfrog::LeapMap::new();
    /// map.insert(1, 12);
    /// if let Some(mut kv_ref) = map.get_mut(&1) {
    ///     kv_ref.update(|mut v| {
    ///         *v += 1;    
    ///     });
    /// }
    ///
    /// assert_eq!(map.get(&1).unwrap().value(), Some(13));
    pub fn update<F>(&mut self, mut func: F) -> Option<V>
    where
        K: Eq + Hash + Copy,
        H: BuildHasher + Default,
        F: FnMut(&mut V),
    {
        loop {
            let current = self.cell.value.load(Ordering::Relaxed);
            let mut updated = current;
            func(&mut updated);

            if current.is_redirect() || self.hash != self.cell.hash.load(Ordering::Relaxed) {
                // Map has/is being migrated, help and then try again ...
                self.map.participate_in_migration();
                let key = self.cell.key.load(Ordering::Relaxed);
                if let Some(new_cell) = self.map.find(&key, self.hash) {
                    self.cell = new_cell;
                } else {
                    // Cell has been removed:
                    return None;
                }
            } else if current.is_null() {
                // Value has been erased.
                return None;
            } else if self
                .cell
                .value
                .compare_exchange_weak(current, updated, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok()
            {
                return Some(current);
            }

            // Lost the race to update the cell, go and try again
        }
    }
}
