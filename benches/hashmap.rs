use criterion::Criterion;
use criterion::Throughput;
use criterion::{criterion_group, criterion_main};
use leapfrog::MurmurHasher;
use rand::{thread_rng, Rng};
use std::hash::BuildHasherDefault;

const NUM_KEYS: usize = 1 << 14;
const NUM_OPS: u64 = 5_000_000;

fn bench_leapfrog_hashmap(c: &mut Criterion) {
    let mut group = c.benchmark_group("leapfrog_hashmap");
    group.throughput(Throughput::Elements(NUM_OPS * 6 as u64));
    group.sample_size(10);
    group.bench_function("insert_and_remove", |b| {
        let mut map = leapfrog::HashMap::with_capacity_and_hasher(
            NUM_KEYS,
            BuildHasherDefault::<MurmurHasher>::default(),
        );

        let mut rng = thread_rng();
        let mut bits: u64 = rng.gen();
        let mut mask = 0u64;

        b.iter(|| {
            for _ in 0..6 {
                // Add 4 random bits
                mask = mask << 4;
                mask = mask | (bits & 0b00001111);
                bits = bits >> 4;

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
    group.throughput(Throughput::Elements(NUM_OPS * 6 as u64));
    group.sample_size(10);
    group.bench_function("insert_and_remove", |b| {
        let mut map = std::collections::HashMap::with_capacity_and_hasher(
            NUM_KEYS,
            BuildHasherDefault::<MurmurHasher>::default(),
        );

        let mut rng = thread_rng();
        let mut bits: u64 = rng.gen();
        let mut mask = 0u64;

        b.iter(|| {
            for _ in 0..6 {
                // Add 4 random bits
                mask = mask << 4;
                mask = mask | (bits & 0b00001111);
                bits = bits >> 4;

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

criterion_group!(benches, bench_std_hashmap, bench_leapfrog_hashmap);
criterion_main!(benches);
