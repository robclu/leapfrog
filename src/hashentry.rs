use crate::hashmap::{DefaultHash, HashMap};
use crate::Value;

use core::alloc::Allocator;
use core::hash::{BuildHasher, BuildHasherDefault, Hash};
use std::alloc::Global;

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This enum is constructed from the `entry` method on a [`HashMap`].
pub enum Entry<'a, K, V, H = BuildHasherDefault<DefaultHash>, A: Allocator = Global> {
    Occupied(OccupiedEntry<'a, K, V, H, A>),
    Vacant(VacantEntry<'a, K, V, H, A>),
}

impl<'a, K, V, H, A> Entry<'a, K, V, H, A>
where
    K: Eq + Hash + Clone + 'a,
    V: Value + 'a,
    H: BuildHasher + Default,
    A: Allocator,
{
    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// let mut map: HashMap<u32, u32> = HashMap::new();
    ///
    /// map.entry(1).or_insert(3);
    /// assert_eq!(map.get(&1), Some(&3));
    ///
    /// *map.entry(1).or_insert(10) *= 2;
    /// assert_eq!(map.get(&1), Some(&6));
    /// ```
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(mut v) => v.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// let mut map: HashMap<u32, u32> = HashMap::new();
    /// let new = 12u32;
    ///
    /// map.entry(1).or_insert_with(|| new);
    /// assert_eq!(map.get(&1), Some(&12));
    /// ```
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(mut v) => v.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the
    /// default function. This method allows for generating key-derived values for
    /// insertion by providing the default function a reference to the key that was
    /// moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the
    /// key is unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// let mut map: HashMap<u32, u32> = HashMap::new();
    ///
    /// map.entry(1).or_insert_with_key(|key| *key * 2);
    ///
    /// assert_eq!(map.get(&1), Some(&2));
    /// ```
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(mut v) => v.insert(default(v.key())),
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// let mut map: HashMap<u32, u32> = HashMap::new();
    ///
    /// assert_eq!(map.entry(1).key(), &1);
    /// ```
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(o) => o.key(),
            Entry::Vacant(v) => v.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential
    /// inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// let mut map: HashMap<u32, u32> = HashMap::new();
    ///
    /// map.entry(1)
    ///     .and_modify(|e| *e += 1)
    ///     .or_insert(42);
    /// assert_eq!(map.get(&1), Some(&42));
    ///
    /// map.entry(1)
    ///     .and_modify(|e| *e += 1)
    ///     .or_insert(42);
    /// assert_eq!(map.get(&1), Some(&43));
    /// ```
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut o) => {
                f(o.get_mut());
                Entry::Occupied(o)
            }
            Entry::Vacant(v) => Entry::Vacant(v),
        }
    }

    /// Sets the value of the entry, and returns an [`OccupiedEntry`].
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    /// let entry = map.entry(1).insert_entry(12);
    ///
    /// assert_eq!(entry.key(), &1);
    /// ```
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, H, A> {
        match self {
            Entry::Occupied(mut o) => {
                o.insert(value);
                o
            }
            Entry::Vacant(v) => v.insert_entry(value),
        }
    }

    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// let mut map: HashMap<u32, u32> = HashMap::new();
    /// map.entry(1).or_default();
    ///
    /// assert_eq!(*map.get(&1).unwrap(), u32::default());
    /// ```
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert(V::default())
    }
}

/// A view into an occupied entry in a [`HashMap`]. It is part of the [`Entry`] enum.
pub struct OccupiedEntry<'a, K, V, H, A: Allocator> {
    pub(crate) map: &'a mut HashMap<K, V, H, A>,
    pub(crate) key: K,
    pub(crate) value: &'a mut V,
}

impl<'a, K, V, H, A> OccupiedEntry<'a, K, V, H, A>
where
    K: Eq + Hash + Clone + 'a,
    V: Value + 'a,
    H: BuildHasher + Default,
    A: Allocator,
{
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::<i32, i32>::new();
    /// map.entry(1).or_insert(12);
    /// assert_eq!(map.entry(1).key(), &1);
    /// ```
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Takes ownership of the key and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    /// map.entry(1).or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry(1) {
    ///     // Delete the entry from the map
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key(&1), false);
    /// ```
    pub fn remove_entry(self) -> (K, V) {
        let value = self.map.remove(&self.key).unwrap();
        (self.key, value)
    }

    /// Gets a reference to the value in the [`Entry`].
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    /// map.entry(1).or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry(1) {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    pub fn get(&self) -> &V {
        self.value
    }

    /// Gets a mutable reference to the value in the [`Entry`].
    ///
    /// If you need a reference to an `OccupiedEntry` which may outlive the destruction
    /// of the [`Entry`] value, see `into_mut`.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    /// map.entry(1).or_insert(12);
    ///
    /// assert_eq!(map.get(&1), Some(&12));
    ///
    /// if let Entry::Occupied(mut o) = map.entry(1) {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same entry multiple times
    ///     *o.get_mut() += 2;
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&24));
    /// ```
    pub fn get_mut(&mut self) -> &mut V {
        self.value
    }

    /// Converts the [`OccupiedEntry`] into a mutable reference to the value in
    /// the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see `get_mut`.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    /// map.entry(1).or_insert(12);
    ///
    /// assert_eq!(map.get(&1), Some(&12));
    ///
    /// if let Entry::Occupied(o) = map.entry(1) {
    ///     *o.into_mut() += 10;
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&22));
    /// ```
    pub fn into_mut(self) -> &'a mut V {
        self.value
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    /// map.entry(1).or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry(1) {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&15));
    /// ```
    pub fn insert(&mut self, value: V) -> V {
        let old = *self.value;
        *self.value = value;
        old
    }

    /// Takes the value out of the entry and returns it.
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    /// map.entry(1).or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry(1) {
    ///     assert_eq!(o.remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key(&1), false);
    /// ```
    pub fn remove(self) -> V {
        self.map.remove(&self.key).unwrap()
    }
}

/// A view into a vacant entry in a [`HashMap`]. It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, K, V, H, A: Allocator> {
    pub(crate) map: &'a mut HashMap<K, V, H, A>,
    pub(crate) key: K,
}

impl<'a, K, V, H, A> VacantEntry<'a, K, V, H, A>
where
    K: Eq + Hash + Clone + 'a,
    V: Value + 'a,
    H: BuildHasher + Default,
    A: Allocator,
{
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = leapfrog::HashMap::<i32, i32>::new();
    /// assert_eq!(map.entry(1).key(), &1);
    /// ```
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Takes ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    ///
    /// if let Entry::Vacant(v) = map.entry(1) {
    ///     v.into_key();
    /// }
    /// ```
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the [`VacantEntry`]'s key, and returns a
    /// mutable reference to it.
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    ///
    /// if let Entry::Vacant(mut o) = map.entry(1) {
    ///     o.insert(37);
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&37));
    /// ```
    pub fn insert(&mut self, value: V) -> &'a mut V {
        self.map.insert(self.key.clone(), value);
        self.map.get_mut(&self.key).unwrap()
    }

    /// Sets the value of the entry with the [`VacantEntry`]'s key, and returns an
    /// [`OccupiedEntry`].
    ///
    /// ```
    /// use leapfrog::HashMap;
    /// use leapfrog::hashmap::Entry;
    ///
    /// let mut map = HashMap::<i32, i32>::new();
    ///
    /// if let Entry::Vacant(o) = map.entry(1) {
    ///     o.insert_entry(37);
    /// }
    ///
    /// assert_eq!(map.get(&1), Some(&37));
    /// ```
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, H, A> {
        self.map.insert(self.key.clone(), value);
        let value = self.map.get_mut(&self.key).unwrap();
        OccupiedEntry {
            map: self.map,
            key: self.key,
            value,
        }
    }
}
