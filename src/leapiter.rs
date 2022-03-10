use core::{
    alloc::Allocator,
    hash::{BuildHasher, Hash},
};

use crate::leapmap::null_hash;
use crate::LeapMap;
use crate::Value;

/// Iterator over a [`LeaphMap`] which yields key-value pairs.
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
