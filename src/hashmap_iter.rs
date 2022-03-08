use std::{
    alloc::Allocator,
    hash::{BuildHasher, Hash},
};

use crate::hashmap::HashMap;
use crate::Value;

/// Iterator over a [`HashMap`] which yeilds key-value pairs.
///
/// # Examples
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
