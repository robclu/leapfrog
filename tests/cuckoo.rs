use leapfrog::LeapMap;
use rand::distributions::{Distribution, Uniform};
use std::sync::{
    atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
    Arc,
};
use std::thread;

/// Number of keys and values to work with.
const NUM_KEYS: usize = 1 << 12;
/// Number of threads that should be started.
const NUM_THREADS: usize = 4;
/// How long the stress test will run (in milliseconds).
const TEST_LEN: u64 = 5000;

type Key = u64;
type Value = u64;

struct Environment {
    table1: LeapMap<Key, Value>,
    table2: LeapMap<Key, Value>,
    keys: Vec<Key>,
    vals1: Vec<AtomicU64>,
    vals2: Vec<AtomicU64>,
    ind_dist: Uniform<usize>,
    val_dist1: Uniform<Value>,
    val_dist2: Uniform<Value>,
    in_table: Vec<AtomicBool>,
    in_use: Vec<AtomicBool>,
    finished: AtomicBool,
    num_inserts: AtomicUsize,
    num_deletes: AtomicUsize,
    num_updates: AtomicUsize,
    num_finds: AtomicUsize,
}

impl Environment {
    pub fn new() -> Self {
        let mut keys = Vec::with_capacity(NUM_KEYS);
        let mut in_use = Vec::with_capacity(NUM_KEYS);
        let mut in_table = Vec::with_capacity(NUM_KEYS);
        let mut vals1 = Vec::with_capacity(NUM_KEYS);
        let mut vals2 = Vec::with_capacity(NUM_KEYS);

        for i in 1..NUM_KEYS + 1 {
            keys.push(i as u64);
            vals1.push(AtomicU64::new(0));
            vals2.push(AtomicU64::new(0));
            in_use.push(AtomicBool::new(false));
            in_table.push(AtomicBool::new(false));
        }

        Self {
            table1: LeapMap::new(),
            table2: LeapMap::new(),
            keys,
            vals1,
            vals2,
            ind_dist: Uniform::from(0..NUM_KEYS - 1),
            val_dist1: Uniform::from(Value::min_value()..Value::max_value() - 2),
            val_dist2: Uniform::from(Value::min_value()..Value::max_value() - 2),
            in_table,
            in_use,
            finished: AtomicBool::new(false),
            num_inserts: AtomicUsize::new(0),
            num_deletes: AtomicUsize::new(0),
            num_updates: AtomicUsize::new(0),
            num_finds: AtomicUsize::new(0),
        }
    }
}

fn stress_insert_thread(env: Arc<Environment>) {
    let mut rng = rand::thread_rng();
    while !env.finished.load(Ordering::SeqCst) {
        let idx = env.ind_dist.sample(&mut rng);
        if env.in_use[idx]
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
        {
            let key = env.keys[idx];
            let val1 = env.val_dist1.sample(&mut rng);
            let val2 = env.val_dist2.sample(&mut rng);
            let res1 = if !env.table1.contains_key(&key) {
                env.table1.insert(key, val1).map_or(true, |_| false)
            } else {
                false
            };

            let res2 = if !env.table2.contains_key(&key) {
                match env.table2.insert(key, val2) {
                    Some(_) => false,
                    None => true,
                }
            } else {
                false
            };

            let in_table = env.in_table[idx].load(Ordering::Relaxed);
            assert_ne!(res1, in_table);
            assert_ne!(res2, in_table);
            if res1 {
                assert_eq!(env.table1.get(&key).unwrap().value(), Some(val1));
                assert_eq!(env.table2.get(&key).unwrap().value(), Some(val2));
                env.vals1[idx].store(val1, Ordering::Relaxed);
                env.vals2[idx].store(val2, Ordering::Relaxed);
                env.in_table[idx].store(true, Ordering::Relaxed);
                env.num_inserts.fetch_add(2, Ordering::Relaxed);
            }
            env.in_use[idx].store(false, Ordering::SeqCst);
        }
    }
}

fn stress_delete_thread(env: Arc<Environment>) {
    let mut rng = rand::thread_rng();
    while !env.finished.load(Ordering::SeqCst) {
        let idx = env.ind_dist.sample(&mut rng);
        if env.in_use[idx]
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
        {
            let key = env.keys[idx];
            let in_table = env.in_table[idx].load(Ordering::Relaxed);
            let res1 = env.table1.remove(&key).map_or(false, |_| true);
            let res2 = env.table2.remove(&key).map_or(false, |_| true);
            if res1 != in_table {
                println!("Error: {} {}", key, env.vals1[idx].load(Ordering::Relaxed));
            }
            assert_eq!(res1, in_table);
            assert_eq!(res2, in_table);
            if res1 {
                assert!(env.table1.get(&key).is_none());
                assert!(env.table2.get(&key).is_none());
                env.in_table[idx].store(false, Ordering::Relaxed);
                env.num_deletes.fetch_add(2, Ordering::Relaxed);
            }
            env.in_use[idx].store(false, Ordering::SeqCst);
        }
    }
}

fn stress_find_thread(env: Arc<Environment>) {
    let mut rng = rand::thread_rng();
    while !env.finished.load(Ordering::SeqCst) {
        let idx = env.ind_dist.sample(&mut rng);
        if env.in_use[idx]
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
        {
            let key = env.keys[idx];
            let val1 = env.vals1[idx].load(Ordering::Relaxed);
            let val2 = env.vals2[idx].load(Ordering::Relaxed);

            let value = env.table1.get(&key);
            if value.is_some() {
                assert_eq!(Some(val1), value.unwrap().value());
                assert!(env.in_table[idx].load(Ordering::Relaxed));
            }
            let value = env.table2.get(&key);
            if value.is_some() {
                assert_eq!(Some(val2), value.unwrap().value());
                assert!(env.in_table[idx].load(Ordering::Relaxed));
            }
            env.num_finds.fetch_add(2, Ordering::Relaxed);
            env.in_use[idx].swap(false, Ordering::SeqCst);
        }
    }
}

fn stress_update_thread(env: Arc<Environment>) {
    let mut rng = rand::thread_rng();

    while !env.finished.load(Ordering::SeqCst) {
        let idx = env.ind_dist.sample(&mut rng);
        if env.in_use[idx]
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
        {
            let key = env.keys[idx];
            let val1 = env.val_dist1.sample(&mut rng);
            let val2 = env.val_dist2.sample(&mut rng);
            let in_table = env.in_table[idx].load(Ordering::Relaxed);

            // Change this if we add update_fn and/or upsert_fn
            let res = {
                let res1 = env.table1.update(&key, val1).map_or(false, |_| true);
                let res2 = env.table2.update(&key, val2).map_or(false, |_| true);
                assert_eq!(res1, in_table);
                assert_eq!(res2, in_table);
                res1
            };
            if res {
                assert_eq!(Some(val1), env.table1.get(&key).unwrap().value());
                assert_eq!(Some(val2), env.table2.get(&key).unwrap().value());
                env.vals1[idx].store(val1, Ordering::Relaxed);
                env.vals2[idx].store(val2, Ordering::Relaxed);
                env.num_updates.fetch_add(2, Ordering::Relaxed);
            }

            env.in_use[idx].swap(false, Ordering::SeqCst);
        }
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn stress_test() {
    let root = Arc::new(Environment::new());
    let mut threads = Vec::new();
    for _ in 0..NUM_THREADS {
        let env = Arc::clone(&root);
        threads.push(thread::spawn(move || stress_insert_thread(env)));
        let env = Arc::clone(&root);
        threads.push(thread::spawn(move || stress_delete_thread(env)));
        let env = Arc::clone(&root);
        threads.push(thread::spawn(move || stress_find_thread(env)));
        let env = Arc::clone(&root);
        threads.push(thread::spawn(move || stress_update_thread(env)));
    }
    thread::sleep(std::time::Duration::from_millis(TEST_LEN));
    root.finished.swap(true, Ordering::SeqCst);

    for t in threads {
        t.join().expect("failed to join thread");
    }
    let in_table = &*root.in_table;
    let num_filled = in_table
        .iter()
        .filter(|b| b.load(Ordering::Relaxed))
        .count();
    assert_eq!(num_filled, root.table1.len());
    assert_eq!(num_filled, root.table2.len());
}
