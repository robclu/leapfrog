use core::sync::atomic::{AtomicU64, Ordering};
use core_affinity::CoreId;
use leapfrog::{LeapMap, Value};
use rand::{thread_rng, Rng};
use std::sync::Arc;

const NUM_THREADS: u64 = 16;
const KEYS_TO_INSERT: u64 = (1 << (NUM_THREADS + 9)) / NUM_THREADS;

#[test]
fn create_map() {
    const ELEMENTS: usize = 100;
    let leapmap = Arc::new(LeapMap::<u32, u32>::with_capacity(ELEMENTS));

    let mut threads = vec![];
    for _ in 0..4 {
        let map = leapmap.clone();
        threads.push(std::thread::spawn(move || {
            core_affinity::set_for_current(CoreId { id: 0 });
            assert_eq!(map.capacity(), ELEMENTS);
        }));
    }

    for t in threads {
        t.join().unwrap();
    }
}

fn insert_keys(
    map: &Arc<LeapMap<u64, u64>>,
    relative_prime: u64,
    start_index: u64,
    thread_index: u64,
) -> u64 {
    let mut index = start_index + thread_index * (KEYS_TO_INSERT + 2);
    let mut checksum = 0u64;
    for _ in 0..KEYS_TO_INSERT {
        let key = index.wrapping_mul(relative_prime);
        let key = key ^ (key >> 16);
        if key != u64::default() && key != <u64 as Value>::redirect() {
            match map.insert(key, key) {
                Some(old) => {
                    // This can only happen if we have generated a key which
                    // hashes to the same value:
                    assert!(map.hash_usize(&key) == map.hash_usize(&old));
                }
                None => {
                    checksum = checksum.wrapping_add(key);
                }
            }
        }
        index += 1;
    }
    checksum
}

fn remove_keys(
    map: &Arc<LeapMap<u64, u64>>,
    relative_prime: u64,
    start_index: u64,
    thread_index: u64,
) -> u64 {
    let mut index = start_index + thread_index * (KEYS_TO_INSERT + 2);
    let mut checksum = 0u64;
    for _ in 0..KEYS_TO_INSERT {
        let key = index.wrapping_mul(relative_prime);
        let key = key ^ (key >> 16);
        if key != u64::default() && key != <u64 as Value>::redirect() {
            match map.get(&key) {
                Some(mut value_ref) => {
                    checksum = checksum.wrapping_add(value_ref.value());
                    /*
                    match value_ref.value() {
                        Some(v) => {
                            checksum = checksum.wrapping_add(v);
                        }
                        None => {
                            // This can only happen when map is migrating,
                            // which should not be happening here;
                            assert!(key == 0);
                        }
                    }
                    */
                }
                None => {
                    // Didn't find the key, which should not happen!
                    assert!(key == 0);
                }
            }
        }
        index += 1;
    }
    checksum
}

#[test]
fn insert_different_keys() {
    let leapmap = Arc::new(LeapMap::<u64, u64>::with_capacity(1 << 24));

    let mut rng = thread_rng();
    let start_index: u64 = rng.gen();
    let value: u64 = rng.gen();
    let relative_prime: u64 = value.wrapping_mul(2) + 1;

    let mut threads = vec![];
    let insert_checksum = Arc::new(AtomicU64::new(0));
    let remove_checksum = Arc::new(AtomicU64::new(0));
    let insert_flag = Arc::new(AtomicU64::new(0));
    let remove_flag = Arc::new(AtomicU64::new(0));

    for i in 0..NUM_THREADS / 2 {
        let map = leapmap.clone();
        let start_flag = insert_flag.clone();
        let end_flag = remove_flag.clone();
        let sum = insert_checksum.clone();
        threads.push(std::thread::spawn(move || {
            core_affinity::set_for_current(CoreId { id: i as usize });

            start_flag.fetch_add(1, Ordering::Relaxed);
            while start_flag.load(Ordering::Relaxed) < NUM_THREADS / 2 {
                std::hint::spin_loop();
            }
            let start = std::time::Instant::now();
            let local_sum = insert_keys(&map, relative_prime, start_index, i);

            sum.fetch_add(local_sum, Ordering::Relaxed);
            end_flag.fetch_add(1, Ordering::Relaxed);

            let end = std::time::Instant::now();
            let time = (end - start).as_millis();
            println!(
                "[Insert] Thread: {0:<2}, {1} ms, {2} keys/sec",
                i,
                time,
                KEYS_TO_INSERT as f32 * (1000_f32 / time as f32),
            );
        }));
    }

    for i in NUM_THREADS / 2..NUM_THREADS {
        let map = leapmap.clone();
        let start_flag = remove_flag.clone();
        let sum = remove_checksum.clone();
        threads.push(std::thread::spawn(move || {
            core_affinity::set_for_current(CoreId { id: i as usize });

            while start_flag.load(Ordering::Relaxed) < NUM_THREADS / 2 {
                std::hint::spin_loop();
            }
            let start = std::time::Instant::now();
            let local_sum = remove_keys(&map, relative_prime, start_index, i - NUM_THREADS / 2);

            sum.fetch_add(local_sum, Ordering::Relaxed);

            let end = std::time::Instant::now();
            let time = (end - start).as_millis();
            println!(
                "[Remove] Thread: {0:<2}, {1} ms, {2} keys/sec ",
                i,
                time,
                KEYS_TO_INSERT as f32 * (1000_f32 / time as f32),
            );
        }));
    }

    for t in threads {
        t.join().unwrap();
    }

    let insert = insert_checksum.load(Ordering::Relaxed);
    let remove = remove_checksum.load(Ordering::Relaxed);

    println!(
        "Insert {} : Remove {} : Diff {}{}",
        insert,
        remove,
        if insert > remove { "+" } else { "-" },
        insert.max(remove) - insert.min(remove)
    );
    assert!(insert == remove);
}
