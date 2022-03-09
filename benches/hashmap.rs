use criterion::Criterion;
use criterion::Throughput;
use criterion::{criterion_group, criterion_main};
use rand::{thread_rng, Rng};
use std::hash::BuildHasherDefault;

const NUM_KEYS: usize = 1 << 14;
const NUM_OPS: u64 = 10_000_000;

type HashFn = std::collections::hash_map::DefaultHasher;

fn bench_leapfrog_hashmap(c: &mut Criterion) {
    let mut group = c.benchmark_group("leapfrog_hashmap");
    group.throughput(Throughput::Elements(NUM_OPS * 6 * 2_u64));
    group.sample_size(10);
    group.bench_function("insert_and_remove", |b| {
        let mut map = leapfrog::HashMap::with_capacity_and_hasher(
            NUM_KEYS,
            BuildHasherDefault::<HashFn>::default(),
        );

        let mut rng = thread_rng();
        let mut bits: u64 = rng.gen();
        let mut mask = 0u64;

        b.iter(|| {
            for _ in 0..6 {
                // Add 4 random bits
                mask <<= 4;
                mask |= bits & 0b00001111;
                bits >>= 4;

                for i in 0..NUM_OPS {
                    let key: u64 = rng.gen::<u64>() & mask;
                    map.insert(key, i);
                    let key: u64 = rng.gen::<u64>() & mask;
                    map.remove(&key);
                }
            }
        })
    });
    group.finish();
}

fn bench_std_hashmap(c: &mut Criterion) {
    let mut group = c.benchmark_group("std_hashmap");
    group.throughput(Throughput::Elements(NUM_OPS * 6 * 2_u64));
    group.sample_size(10);
    group.bench_function("insert_and_remove", |b| {
        let mut map = std::collections::HashMap::with_capacity_and_hasher(
            NUM_KEYS,
            BuildHasherDefault::<HashFn>::default(),
        );

        let mut rng = thread_rng();
        let mut bits: u64 = rng.gen();
        let mut mask = 0u64;

        b.iter(|| {
            for _ in 0..6 {
                // Add 4 random bits
                mask <<= 4;
                mask |= bits & 0b00001111;
                bits >>= 4;

                for i in 0..NUM_OPS {
                    let key: u64 = rng.gen::<u64>() & mask;
                    map.insert(key, i);
                    let key: u64 = rng.gen::<u64>() & mask;
                    map.remove(&key);
                }
            }
        })
    });
    group.finish();
}

fn bench_std_hashmap_rwlock(c: &mut Criterion) {
    let mut group = c.benchmark_group("std_hashmap_rw_lock");
    group.throughput(Throughput::Elements(NUM_OPS * 6 * 2_u64));
    group.sample_size(10);
    group.bench_function("insert_and_remove", |b| {
        let map = std::sync::RwLock::new(std::collections::HashMap::with_capacity_and_hasher(
            NUM_KEYS,
            BuildHasherDefault::<HashFn>::default(),
        ));

        let mut rng = thread_rng();
        let mut bits: u64 = rng.gen();
        let mut mask = 0u64;

        b.iter(|| {
            let mut map_write = map.write().unwrap();
            for _ in 0..6 {
                // Add 4 random bits
                mask <<= 4;
                mask |= bits & 0b00001111;
                bits >>= 4;

                for i in 0..NUM_OPS {
                    let key: u64 = rng.gen::<u64>() & mask;
                    map_write.insert(key, i);
                    let key: u64 = rng.gen::<u64>() & mask;
                    map_write.remove(&key);
                }
            }
        })
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_leapfrog_hashmap,
    bench_std_hashmap,
    bench_std_hashmap_rwlock
);
criterion_main!(benches);
