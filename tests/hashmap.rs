use leapfrog::hashmap::*;
use rand::{thread_rng, Rng};

const KEYS_TO_INSERT: usize = 2048;

#[test]
fn create_hash_map() {
    const ELEMENTS: usize = 8;
    let map = HashMap::<u32, u32>::with_capacity(ELEMENTS);

    assert!(map.capacity() >= ELEMENTS);
}

#[test]
fn hash_map_key_insert() {
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
                assert!(false);
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
                assert!(false);
            }

            // Check get mut as well
            if let Some(value) = map.get_mut(&key) {
                assert!(*value == key);
            } else {
                assert!(false);
            }
        }
        index += 1;
    }

    assert_eq!(insert_checksum, remove_checksum);
    assert_eq!(inserted, removed);
}
