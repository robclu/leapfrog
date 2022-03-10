use core::{
    alloc::Allocator,
    hash::{BuildHasher, Hash},
};

use crate::hashmap::HashMap;
use crate::Value;

/// Iterator over a [`HashMap`] which yields key-value pairs.
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
    map: HashMap<K, V, H, A>,
    current: usize,
}

impl<K, V, H, A> OwnedIter<K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher,
    A: Allocator,
{
    pub(crate) fn new(map: HashMap<K, V, H, A>) -> Self {
        Self {
            map,
            current: 0usize,
        }
    }
}

impl<K, V, H, A> Iterator for OwnedIter<K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + Default,
    A: Allocator,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.current;
            if let Some(cell) = self.map.get_cell_at_index(current) {
                self.current = current + 1;
                if cell.is_empty() {
                    continue;
                }

                return Some((cell.key.clone(), cell.value));
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

/// Iterator over a [`HashMap`] which yields immutable key-value reference pairs.
///
/// # Examples
///
/// ```
/// use leapfrog::HashMap;
///
/// let mut map = HashMap::new();
///
/// map.insert(12, 17);
/// map.insert(42, 23);
///
/// assert_eq!(map.iter().count(), 2);
/// ```
pub struct Iter<'a, K, V, H: BuildHasher, A: Allocator> {
    map: &'a HashMap<K, V, H, A>,
    current: usize,
}

impl<'a, K, V, H, A> Clone for Iter<'a, K, V, H, A>
where
    K: Eq + Hash + Clone,
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
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + 'a,
    A: Allocator + 'a,
{
    pub(crate) fn new(map: &'a HashMap<K, V, H, A>) -> Self {
        Self {
            map,
            current: 0usize,
        }
    }
}

impl<'a, K, V, H, A> Iterator for Iter<'a, K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + Default + 'a,
    A: Allocator + 'a,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.current;
            if let Some(cell) = self.map.get_cell_at_index(current) {
                self.current = current + 1;
                if cell.is_empty() {
                    continue;
                }

                return Some((&cell.key, &cell.value));
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
    H: BuildHasher + Send + 'a,
    A: Allocator + Send + 'a,
{
}

unsafe impl<'a, K, V, H, A> Sync for Iter<'a, K, V, H, A>
where
    K: Sync,
    V: Sync,
    H: BuildHasher + Sync + 'a,
    A: Allocator + Sync + 'a,
{
}

/// Iterator over a [`HashMap`] which yields mutable key-value reference pairs.
///
/// # Examples
///
/// ```
/// use leapfrog::HashMap;
///
/// let mut map = HashMap::new();
///
/// map.insert(12, 17);
/// map.insert(42, 23);
///
/// assert_eq!(map.iter_mut().count(), 2);
/// ```
pub struct IterMut<'a, K, V, H: BuildHasher, A: Allocator> {
    map: &'a mut HashMap<K, V, H, A>,
    current: usize,
}

impl<'a, K, V, H, A> IterMut<'a, K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + 'a,
    A: Allocator + 'a,
{
    pub(crate) fn new(map: &'a mut HashMap<K, V, H, A>) -> Self {
        Self {
            map,
            current: 0usize,
        }
    }
}

impl<'a, K, V, H, A> Iterator for IterMut<'a, K, V, H, A>
where
    K: Eq + Hash + Clone,
    V: Value,
    H: BuildHasher + Default + 'a,
    A: Allocator + 'a,
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let current = self.current;
            if let Some(cell) = self.map.get_cell_at_index_mut(current) {
                self.current = current + 1;
                if cell.is_empty() {
                    continue;
                }

                return Some((&cell.key, &mut cell.value));
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
    H: BuildHasher + Send + 'a,
    A: Allocator + Send + 'a,
{
}

unsafe impl<'a, K, V, H, A> Sync for IterMut<'a, K, V, H, A>
where
    K: Sync,
    V: Sync,
    H: BuildHasher + Sync + 'a,
    A: Allocator + Sync + 'a,
{
}
