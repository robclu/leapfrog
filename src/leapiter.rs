use core::{
    alloc::Allocator,
    hash::{BuildHasher, Hash},
};

use crate::LeapMap;
use crate::Value;
use crate::{leapmap::null_hash, Ref, RefMut};

/// Iterator over a [`LeapMap`] which yields key-value pairs.
///
/// # Examples
///
/// ```
/// use leapfrog::HashMap;
///
/// let mut map = HashMap::new();
///
/// map.insert(12u32, 17u64);
/// map.insert(42u32, 92u64);
///
/// let pairs = map.into_iter().collect::<Vec<(u32, u64)>>();
/// assert_eq!(pairs.len(), 2);
/// ```
pub struct OwnedIter<K, V, H: BuildHasher, A: Allocator> {
    map: LeapMap<K, V, H, A>,
    current: usize,
}

impl<K, V, H, A> OwnedIter<K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher,
    A: Allocator,
{
    pub(crate) fn new(map: LeapMap<K, V, H, A>) -> Self {
        Self {
            map,
            current: 0usize,
        }
    }
}

impl<K, V, H, A> Iterator for OwnedIter<K, V, H, A>
where
    K: Eq + Hash + Copy,
    V: Value,
    H: BuildHasher + Default,
    A: Allocator,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.current;
            if let Some(mut cell_ref) = self.map.get_cell_at_index(current) {
                self.current = current + 1;
                if cell_ref.hash == null_hash() {
                    continue;
                }

                // We don't just return cell_ref.key_value() here since if this
                // is None then we want to continue until we find a cell which
                // is in the map.
                if let Some((k, v)) = cell_ref.key_value() {
                    return Some((k, v));
                }
            } else {
                return None;
            }
        }
    }
}

unsafe impl<K, V, H, A> Send for OwnedIter<K, V, H, A>
where
    K: Send,
    V: Send,
    H: BuildHasher + Send,
    A: Allocator + Send,
{
}

unsafe impl<K, V, H, A> Sync for OwnedIter<K, V, H, A>
where
    K: Sync,
    V: Sync,
    H: BuildHasher + Sync,
    A: Allocator + Sync,
{
}

/// Iterator over a [`LeapMap`] which yields immutable key-value pairs. The
/// iterator returns a [`Ref`], which allows safe concurrent access of the key
/// and the value from multiple threads.
///
/// # Examples
///
/// ```
/// use leapfrog::LeapMap;
///
/// let mut map = LeapMap::new();
///
/// map.insert(12, 17);
/// map.insert(42, 23);
///
/// assert_eq!(map.iter().count(), 2);
/// ```
pub struct Iter<'a, K, V, H: BuildHasher, A: Allocator> {
    map: &'a LeapMap<K, V, H, A>,
    current: usize,
}

impl<'a, K, V, H, A> Clone for Iter<'a, K, V, H, A>
where
    K: Eq + Hash + Copy,
    V: Value,
    H: BuildHasher + Default,
    A: Allocator,
{
    fn clone(&self) -> Self {
        Iter::new(self.map)
    }
}

impl<'a, K, V, H, A> Iter<'a, K, V, H, A>
where
    K: Eq + Hash + Copy,
    V: Value,
    H: BuildHasher + 'a,
    A: Allocator + 'a,
{
    pub(crate) fn new(map: &'a LeapMap<K, V, H, A>) -> Self {
        Self {
            map,
            current: 0usize,
        }
    }
}

impl<'a, K, V, H, A> Iterator for Iter<'a, K, V, H, A>
where
    K: Eq + Hash + Copy,
    V: Value,
    H: BuildHasher + Default + 'a,
    A: Allocator + 'a,
{
    type Item = Ref<'a, K, V, H, A>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.current;
            if let Some(cell) = self.map.get_cell_at_index(current) {
                self.current = current + 1;
                if cell.hash == null_hash() {
                    continue;
                }

                return Some(cell);
            } else {
                return None;
            }
        }
    }
}

unsafe impl<'a, K, V, H, A> Send for Iter<'a, K, V, H, A>
where
    K: Send,
    V: Send,
    H: BuildHasher + Send,
    A: Allocator + Send,
{
}

unsafe impl<'a, K, V, H, A> Sync for Iter<'a, K, V, H, A>
where
    K: Sync,
    V: Sync,
    H: BuildHasher + Sync,
    A: Allocator + Sync,
{
}

/// Iterator over a [`LeapMap`] which yields mutable key-value pairs. The iterator
/// returns a [`RefMut`], which allows the iterated cell's value to be modified.
///
/// # Examples
///
/// ```
/// use leapfrog::LeapMap;
///
/// let mut map = LeapMap::new();
///
/// map.insert(12, 17);
/// map.insert(42, 23);
///
/// assert_eq!(map.iter_mut().count(), 2);
/// ```
pub struct IterMut<'a, K, V, H: BuildHasher, A: Allocator> {
    map: &'a LeapMap<K, V, H, A>,
    current: usize,
}

impl<'a, K, V, H, A> Clone for IterMut<'a, K, V, H, A>
where
    K: Eq + Hash + Copy,
    V: Value,
    H: BuildHasher + Default,
    A: Allocator,
{
    fn clone(&self) -> Self {
        IterMut::new(self.map)
    }
}

impl<'a, K, V, H, A> IterMut<'a, K, V, H, A>
where
    K: Eq + Hash + Copy,
    V: Value,
    H: BuildHasher + 'a,
    A: Allocator + 'a,
{
    pub(crate) fn new(map: &'a LeapMap<K, V, H, A>) -> Self {
        Self {
            map,
            current: 0usize,
        }
    }
}

impl<'a, K, V, H, A> Iterator for IterMut<'a, K, V, H, A>
where
    K: Eq + Hash + Copy,
    V: Value,
    H: BuildHasher + Default + 'a,
    A: Allocator + 'a,
{
    type Item = RefMut<'a, K, V, H, A>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.current;
            if let Some(cell) = self.map.get_cell_at_index_mut(current) {
                self.current = current + 1;
                if cell.hash == null_hash() {
                    continue;
                }

                return Some(cell);
            } else {
                return None;
            }
        }
    }
}

unsafe impl<'a, K, V, H, A> Send for IterMut<'a, K, V, H, A>
where
    K: Send,
    V: Send,
    H: BuildHasher + Send,
    A: Allocator + Send,
{
}

unsafe impl<'a, K, V, H, A> Sync for IterMut<'a, K, V, H, A>
where
    K: Sync,
    V: Sync,
    H: BuildHasher + Sync,
    A: Allocator + Sync,
{
}
