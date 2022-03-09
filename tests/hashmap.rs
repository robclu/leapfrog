use leapfrog::hashmap::*;
use rand::{thread_rng, Rng};
use std::collections::BTreeMap;

const KEYS_TO_INSERT: usize = 2048;

#[test]
fn hashmap_creation() {
    const ELEMENTS: usize = 8;
    let map = HashMap::<u32, u32>::with_capacity(ELEMENTS);

    assert!(map.capacity() >= ELEMENTS);
}

#[test]
fn hashmap_insert() {
    let mut map = HashMap::<u64, u64>::with_capacity(KEYS_TO_INSERT);

    let mut rng = thread_rng();
    let start_index: u32 = rng.gen();
    let value: u32 = rng.gen();
    let relative_prime: u64 = value as u64 * 2 + 1;

    let mut inserted: usize = 0;
    let mut index = start_index;
    let mut insert_checksum = 0u64;
    while inserted < KEYS_TO_INSERT {
        let mut key: u64 = (index as u64).wrapping_mul(relative_prime);
        key = key ^ (key >> 16);

        // Don't add keys which are 0 or 1
        if key >= 2 {
            // Map is empty, we should only have None here:
            if let Some(_old) = map.insert(key, key) {
                panic!("HashMap value found which should not be present");
            }
            inserted += 1;
            insert_checksum = insert_checksum.wrapping_add(key);
        }
        index += 1;
    }

    let mut removed: usize = 0;
    let mut index = start_index;
    let mut remove_checksum = 0u64;
    while removed < KEYS_TO_INSERT {
        let mut key: u64 = (index as u64).wrapping_mul(relative_prime);
        key = key ^ (key >> 16);

        if key >= 2 {
            if let Some(value) = map.get(&key) {
                assert!(*value == key);
                remove_checksum = remove_checksum.wrapping_add(key);
                removed += 1;
            } else {
                panic!("Value should be found");
            }

            // Check get mut as well
            if let Some(value) = map.get_mut(&key) {
                assert!(*value == key);
            } else {
                panic!("Value should be found");
            }
        }
        index += 1;
    }

    assert_eq!(insert_checksum, remove_checksum);
    assert_eq!(inserted, removed);
}

fn generate_kvs(keys: usize) -> BTreeMap<u64, u64> {
    let mut map = BTreeMap::new();

    let mut rng = thread_rng();
    let start_index: u32 = rng.gen();
    let value: u32 = rng.gen();
    let relative_prime: u64 = value as u64 * 2 + 1;

    let mut index = start_index;
    for _ in 0..keys {
        let mut key: u64 = (index as u64).wrapping_mul(relative_prime);
        key = key ^ (key >> 16);
        map.insert(key, key + 1);

        index += 1;
    }

    map
}

#[test]
fn hashmap_into_iter() {
    const KEYS: usize = 150;
    let mut map = HashMap::new();
    let kv_map = generate_kvs(KEYS);

    for (k, v) in kv_map.iter() {
        let val = *v;
        let key = *k;
        map.insert(key, val);
    }

    assert_eq!(map.len(), KEYS);

    let mut count = 0usize;
    for (k, v) in map.into_iter() {
        if let Some(val) = kv_map.get(&k) {
            assert_eq!(v, *val);
        } else {
            panic!("HashMap value is incorrect");
        }
        count += 1;
    }

    assert_eq!(count, KEYS);
}

#[test]
fn hashmap_iter() {
    const KEYS: usize = 150;
    let mut map = HashMap::new();
    let kv_map = generate_kvs(KEYS);

    for (k, v) in kv_map.iter() {
        let val = *v;
        let key = *k;
        map.insert(key, val);
    }

    assert_eq!(map.len(), KEYS);

    let mut count = 0usize;
    for (k, v) in map.iter() {
        if let Some(val) = kv_map.get(k) {
            assert_eq!(*v, *val);
        } else {
            panic!("HashMap value is incorrect");
        }
        count += 1;
    }

    assert_eq!(count, KEYS);
}

#[test]
fn hashmap_iter_mut() {
    const KEYS: usize = 150;
    let mut map = HashMap::new();
    let kv_map = generate_kvs(KEYS);

    for (k, v) in kv_map.iter() {
        let val = *v;
        let key = *k;
        map.insert(key, val);
    }

    assert_eq!(map.len(), KEYS);

    map.iter_mut().for_each(|(_k, v)| *v += 1);

    let mut count = 0usize;
    for (k, v) in map.iter() {
        if let Some(val) = kv_map.get(k) {
            assert_eq!(*v, *val + 1);
        } else {
            panic!("HashMap value is incorrect");
        }
        count += 1;
    }

    assert_eq!(count, KEYS);
}
