use crate::{LeapMap, Value};
use core::alloc::Allocator;
use core::fmt;
use core::hash::{BuildHasher, Hash};
use core::marker::PhantomData;
use serde_crate::de::{Deserialize, MapAccess, Visitor};
use serde_crate::ser::{Serialize, SerializeMap, Serializer};
use serde_crate::Deserializer;
use std::alloc::Global;

pub struct LeapMapVisitor<K, V, H> {
    marker: PhantomData<fn() -> LeapMap<K, V, H, Global>>,
}

impl<K, V, H> LeapMapVisitor<K, V, H>
where
    K: Eq + Hash,
    V: Value,
    H: BuildHasher + Clone,
{
    fn new() -> Self {
        LeapMapVisitor {
            marker: PhantomData,
        }
    }
}

impl<'de, K, V, H> Visitor<'de> for LeapMapVisitor<K, V, H>
where
    K: Deserialize<'de> + Eq + Hash + Copy + std::fmt::Debug,
    V: Deserialize<'de> + Value,
    H: BuildHasher + Clone + Default,
{
    type Value = LeapMap<K, V, H, Global>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a LeapMap")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let size = access.size_hint().unwrap_or(4);
        let map = LeapMap::with_capacity_and_hasher(size, Default::default());

        while let Some((key, value)) = access.next_entry()? {
            map.insert(key, value);
        }

        Ok(map)
    }
}

impl<'de, K, V, H> Deserialize<'de> for LeapMap<K, V, H, Global>
where
    K: Deserialize<'de> + Eq + Hash + Copy + std::fmt::Debug,
    V: Deserialize<'de> + Value,
    H: BuildHasher + Clone + Default,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(LeapMapVisitor::<K, V, H>::new())
    }
}

impl<K, V, H, A> Serialize for LeapMap<K, V, H, A>
where
    K: Serialize + Eq + Hash + Copy,
    V: Serialize + Value,
    H: BuildHasher + Clone + Default,
    A: Allocator,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.len()))?;

        for mut item_ref in self.iter() {
            if let Some((k, v)) = item_ref.key_value() {
                map.serialize_entry(&k, &v)?;
            }
        }

        map.end()
    }
}

#[cfg(test)]
mod test {
    use crate::LeapMap;

    #[test]
    fn leapmap_serde() {
        let map = LeapMap::<u32, u8>::new();

        map.insert(0, 11);
        map.insert(1, 12);
        map.insert(2, 13);
        map.insert(3, 14);
        map.insert(4, 15);
        map.insert(5, 16);

        let serialized = serde_json::to_string(&map).expect("Couldn't serialize map");
        let deserialized: LeapMap<u32, u8> =
            serde_json::from_str(&serialized).expect("Couldn't deserialize map");

        assert_eq!(deserialized.get(&0).unwrap().value(), Some(11));
        assert_eq!(deserialized.get(&1).unwrap().value(), Some(12));
        assert_eq!(deserialized.get(&2).unwrap().value(), Some(13));
        assert_eq!(deserialized.get(&3).unwrap().value(), Some(14));
        assert_eq!(deserialized.get(&4).unwrap().value(), Some(15));
        assert_eq!(deserialized.get(&5).unwrap().value(), Some(16));
    }
}
