//! Benchmarks for [`LeapMap`] concurrent operations.
//!
//! Each group runs the same workload across multiple map implementations so
//! Criterion can produce side-by-side comparisons:
//!
//! | Baseline            | Rationale                                                  |
//! |---------------------|------------------------------------------------------------|
//! | `DashMap`           | Popular sharded concurrent map                             |
//! | `Mutex<HashMap>`    | Coarse-grained lock; all ops serialize (floor for writes)  |
//! | `RwLock<HashMap>`   | Concurrent reads, exclusive writes (floor for reads)       |

use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::Throughput;
use criterion::{criterion_group, criterion_main};
use dashmap::DashMap;
use leapfrog::LeapMap;
use rand::{thread_rng, Rng};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};

const NUM_KEYS: usize = 1 << 14; // 16 384, pre-population size for get bench
const OPS_PER_THREAD: usize = 10_000;

fn num_threads() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
}

// ---------------------------------------------------------------------------
// concurrent_insert
// ---------------------------------------------------------------------------

/// N threads each insert `OPS_PER_THREAD` unique keys into a fresh map.
///
/// Thread creation is included in the measurement (conservative / slightly
/// pessimistic), but is consistent across all variants so comparisons are fair.
fn bench_concurrent_insert(c: &mut Criterion) {
    let n = num_threads();
    let mut group = c.benchmark_group("concurrent_insert");
    group.throughput(Throughput::Elements((n * OPS_PER_THREAD) as u64));
    group.sample_size(10);

    group.bench_function("leapmap", |b| {
        b.iter(|| {
            let map: Arc<LeapMap<usize, usize>> = Arc::new(LeapMap::new());
            let handles: Vec<_> = (0..n)
                .map(|t| {
                    let m = Arc::clone(&map);
                    std::thread::spawn(move || {
                        let base = t * OPS_PER_THREAD;
                        for i in 0..OPS_PER_THREAD {
                            m.insert(base + i, i);
                        }
                    })
                })
                .collect();
            for h in handles {
                h.join().unwrap();
            }
        });
    });

    group.bench_function("dashmap", |b| {
        b.iter(|| {
            let map: Arc<DashMap<usize, usize>> = Arc::new(DashMap::new());
            let handles: Vec<_> = (0..n)
                .map(|t| {
                    let m = Arc::clone(&map);
                    std::thread::spawn(move || {
                        let base = t * OPS_PER_THREAD;
                        for i in 0..OPS_PER_THREAD {
                            m.insert(base + i, i);
                        }
                    })
                })
                .collect();
            for h in handles {
                h.join().unwrap();
            }
        });
    });

    group.bench_function("mutex_hashmap", |b| {
        b.iter(|| {
            let map: Arc<Mutex<HashMap<usize, usize>>> =
                Arc::new(Mutex::new(HashMap::new()));
            let handles: Vec<_> = (0..n)
                .map(|t| {
                    let m = Arc::clone(&map);
                    std::thread::spawn(move || {
                        let base = t * OPS_PER_THREAD;
                        for i in 0..OPS_PER_THREAD {
                            m.lock().unwrap().insert(base + i, i);
                        }
                    })
                })
                .collect();
            for h in handles {
                h.join().unwrap();
            }
        });
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// concurrent_get
// ---------------------------------------------------------------------------

/// N threads each perform `OPS_PER_THREAD` random reads on a pre-populated map.
///
/// Maps are filled once outside the timed loop so setup cost is excluded.
/// `RwLock<HashMap>` allows concurrent reads; `Mutex<HashMap>` degenerates to
/// serial reads and is omitted here since it would be dominated by `RwLock`.
fn bench_concurrent_get(c: &mut Criterion) {
    let n = num_threads();

    // Pre-populate all maps identically outside the benchmark loop.
    let leapmap: Arc<LeapMap<usize, usize>> = Arc::new(LeapMap::new());
    let dashmap: Arc<DashMap<usize, usize>> = Arc::new(DashMap::new());
    let rwmap: Arc<RwLock<HashMap<usize, usize>>> =
        Arc::new(RwLock::new(HashMap::with_capacity(NUM_KEYS)));

    for i in 0..NUM_KEYS {
        leapmap.insert(i, i);
        dashmap.insert(i, i);
        rwmap.write().unwrap().insert(i, i);
    }

    let mut group = c.benchmark_group("concurrent_get");
    group.throughput(Throughput::Elements((n * OPS_PER_THREAD) as u64));
    group.sample_size(10);

    group.bench_function("leapmap", |b| {
        b.iter(|| {
            let handles: Vec<_> = (0..n)
                .map(|_| {
                    let m = Arc::clone(&leapmap);
                    std::thread::spawn(move || {
                        let mut rng = thread_rng();
                        for _ in 0..OPS_PER_THREAD {
                            let _ = m.get(&(rng.gen::<usize>() % NUM_KEYS));
                        }
                    })
                })
                .collect();
            for h in handles {
                h.join().unwrap();
            }
        });
    });

    group.bench_function("dashmap", |b| {
        b.iter(|| {
            let handles: Vec<_> = (0..n)
                .map(|_| {
                    let m = Arc::clone(&dashmap);
                    std::thread::spawn(move || {
                        let mut rng = thread_rng();
                        for _ in 0..OPS_PER_THREAD {
                            let _ = m.get(&(rng.gen::<usize>() % NUM_KEYS));
                        }
                    })
                })
                .collect();
            for h in handles {
                h.join().unwrap();
            }
        });
    });

    group.bench_function("rwlock_hashmap", |b| {
        b.iter(|| {
            let handles: Vec<_> = (0..n)
                .map(|_| {
                    let m = Arc::clone(&rwmap);
                    std::thread::spawn(move || {
                        let mut rng = thread_rng();
                        for _ in 0..OPS_PER_THREAD {
                            let _ = m.read().unwrap().get(&(rng.gen::<usize>() % NUM_KEYS));
                        }
                    })
                })
                .collect();
            for h in handles {
                h.join().unwrap();
            }
        });
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// resize
// ---------------------------------------------------------------------------

/// Single-threaded fill from empty to N elements with no pre-allocated capacity.
///
/// Measures the amortised cost of insert including resize/migration overhead
/// and `Drop` cleanup. Primarily a regression baseline for LeapMap; DashMap
/// provides a competitive reference point.
fn bench_resize(c: &mut Criterion) {
    let mut group = c.benchmark_group("resize");
    group.sample_size(10);

    for &n in &[1_000usize, 10_000, 100_000] {
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(BenchmarkId::new("leapmap", n), &n, |b, &n| {
            b.iter(|| {
                let map: LeapMap<usize, usize> = LeapMap::new();
                for i in 0..n {
                    map.insert(i, i);
                }
                // drop included; should be O(resizes), not O(n)
            });
        });

        group.bench_with_input(BenchmarkId::new("dashmap", n), &n, |b, &n| {
            b.iter(|| {
                let map: DashMap<usize, usize> = DashMap::new();
                for i in 0..n {
                    map.insert(i, i);
                }
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_concurrent_insert, bench_concurrent_get, bench_resize);
criterion_main!(benches);
