use crate::{
    leapmap::{AtomicCell, LeapMap},
    Value,
};
use std::alloc::Allocator;
use std::hash::{BuildHasher, Hash};
use std::sync::atomic::Ordering;

/// Areference to an atomic cell in a [leapfrog::LeapMap], which cannot mutate
/// the referenced cell value.
pub struct Ref<'a, K, V, H, A: Allocator> {
    /// The atomic value which is being referenced.
    cell: &'a AtomicCell<V>,
    /// Reference to the map in which the cell belongs.
    map: &'a LeapMap<K, V, H, A>,
    /// The hash for the cell at the point when the cell was found
    hash: u64,
}

impl<'a, K, V, H, A> Ref<'a, K, V, H, A>
where
    A: Allocator,
    V: Value,
{
    /// Creates a new ref type referencing the specified `cell` and `map`.
    pub fn new(
        map: &'a LeapMap<K, V, H, A>,
        cell: &'a AtomicCell<V>,
        hash: u64,
    ) -> Ref<'a, K, V, H, A> {
        Ref { map, cell, hash }
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
    /// returned value will be `V::null()`.
    pub fn value(&mut self) -> V
    where
        K: Eq + Hash + Clone,
        H: BuildHasher + Default,
    {
        loop {
            let value = self.cell.value.load(Ordering::Relaxed);
            if value == V::redirect() || self.hash != self.cell.hash.load(Ordering::Relaxed) {
                // Map has/is being migrated, help and then try again ...
                self.map.participate_in_migration();
                if let Some(new_cell) = self.map.find(self.hash) {
                    self.cell = new_cell;
                } else {
                    assert!(false);
                }
            } else {
                return value;
            }
        }
    }
}

/// A reference type to a cell in a [leapfrog::LeapMap] which can mutate the
/// referenced cell value.
pub struct RefMut<'a, K, V, H, A: Allocator> {
    /// The atomic value which is being referenced.
    cell: &'a AtomicCell<V>,
    /// Reference to the map in which the cell belongs.
    map: &'a LeapMap<K, V, H, A>,
    /// The hash for the cell at the point when the cell was found
    hash: u64,
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
        cell: &'a AtomicCell<V>,
        hash: u64,
    ) -> RefMut<'a, K, V, H, A> {
        RefMut { map, cell, hash }
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
    /// returned value will be `V::null()`.
    pub fn value(&mut self) -> V
    where
        K: Eq + Hash + Clone,
        H: BuildHasher + Default,
    {
        loop {
            let value = self.cell.value.load(Ordering::Relaxed);
            if value == V::redirect() || self.hash != self.cell.hash.load(Ordering::Relaxed) {
                // Map has/is being migrated, help and then try again ...
                self.map.participate_in_migration();
                if let Some(new_cell) = self.map.find(self.hash) {
                    self.cell = new_cell;
                } else {
                    assert!(false);
                }
            } else {
                return value;
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
        K: Eq + Hash + Clone,
        H: BuildHasher + Default,
    {
        loop {
            let current = self.cell.value.load(Ordering::Relaxed);

            if current == V::redirect() || self.hash != self.cell.hash.load(Ordering::Relaxed) {
                // Map has/is being migrated, help and then try again ...
                self.map.participate_in_migration();
                if let Some(new_cell) = self.map.find(self.hash) {
                    self.cell = new_cell;
                } else {
                    assert!(false);
                }
            } else if current == V::null() {
                // Value has been erased, we can just return.
                return None;
            } else {
                if self
                    .cell
                    .value
                    .compare_exchange_weak(current, value, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
                {
                    return Some(current);
                }
                // Lost a race to update the cell, go and try again
            }
        }
    }

    /// Updates the value for the referenced cell, using the `func` to compute
    /// the new value, returning the old value if the cell is still in the map,
    /// and `None` if the cell has been deleted.
    pub fn update<F>(&mut self, mut func: F) -> Option<V>
    where
        K: Eq + Hash + Clone,
        H: BuildHasher + Default,
        F: FnMut(&mut V),
    {
        loop {
            let current = self.cell.value.load(Ordering::Relaxed);
            let mut updated = current;
            func(&mut updated);

            if current == V::redirect() || self.hash != self.cell.hash.load(Ordering::Relaxed) {
                // Map has/is being migrated, help and then try again ...
                self.map.participate_in_migration();
                if let Some(new_cell) = self.map.find(self.hash) {
                    self.cell = new_cell;
                } else {
                    assert!(false);
                }
            } else if current == V::null() {
                // Value has been erased, return None.
                return None;
            } else {
                if self
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
}
