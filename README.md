[![version](https://img.shields.io/crates/v/leapfrog)](https://crates.io/crates/leapfrog) [![documentation](https://docs.rs/leapfrog/badge.svg)](https://docs.rs/leapfrog)

# Leapfrog

The leapfrog crate contains two hash map implementations, `HashMap`, which is a single-threaded HashMap, and `LeapMap`, which is fast, concurrent version of the `HashMap`, where all operations can be performed concurrently from any number of threads. If the key and value types support atomic operations then the map is lock-free, and when there is no atomic support for either the key or value, then operations within the map on that non-atomic type use an efficient spinlock and the locking is very fine-grained.

The performance of both maps is good on the benchmarks it's been tested on. The `HashMap` is between 1.2 and 1.5x the `std::collections::HashMap`. Compared to `RwLock<HashMap>`, on 16 cores the `LeapMap` is around 13.5x faster. It also scales very well up to high core counts, for multiple workloads.  Benchmark results can be found at [rust hashmap benchmarks](https://github.com/robclu/conc-map-bench). These bechmarks, however, are limited in the use cases that they cover, and  should be extended to cover a much wider scope. Nevertheless, for those bechmarks, the `LeapMap` is the fastest map. 

For more details on the API and the differences compared to `std::collections::HashMap`, please see the crate documentation.

# Recent Changes

The implementations of these maps have recently been updated to store keys, so the API for both is much closer to `std::collections::HashMap`. There is now also support for serde with the optional "serde" feature. The maps also now have iterator support. The default hasher has been changed to be the DOS resistant hasher from the standard library.

The "stable_alloc" feature flag has been added to allow the crate to be used with the stable toolchain.

# Current Limitations

These is not yet support for rayon, and there are not yet `Set` versions of the `Map`s.

# Performance

A snapshot of the results for the LeapMap on a read heavy workload using a 16 core AMD 3950x CPU are the following (with throughput in Mops/second, cores in brackets, and  performance realtive to `std::collections::HashMap` with RwLock):

| Map              | Throughput (1) | Relative (1) | Throughput (16) | Relative (16) |
|------------------|----------------|--------------|-----------------|---------------|
| RwLock + HashMap | 19.4           | 1.0          | 11.7            | 0.60          |
| Flurry           | 11.2           | 0.58         | 80.8            | 4.16          |
| DashMap          | 14.1           | 0.72         | 87.5            | 4.51          |
| LeapMap          | 17.8           | 0.92         | 148.0           | 7.62          |

On a 12-core M2 Max the results are the following (again values are all relative to `std::collections::HashMap`):

| Map              | Throughput (1) | Relative (1) | Throughput (12) | Relative (12) |
|------------------|----------------|--------------|-----------------|---------------|
| RwLock + HashMap | 21.2           | 1.0          | 3.4             | 0.16          |
| Flurry           | 8.0            | 0.37         | 64.5            | 3.04          |
| DashMap          | 10.4           | 0.49         | 42.2            | 2.00          |
| Evmap            | 13.5           | 0.64         | 18.7            | 0.88          |
| LeapMap          | 13.9           | 0.66         | 106.1           | 5.00          |

On benchmarks of other use cases, leapfrog's `LeapMap` is faster by even higher factors.

For the single threaded leapfrog `HashMap`, a benchmark of random inserts and deletes (a port of [this](https://martin.ankerl.com/2019/04/01/hashmap-benchmarks-03-03-result-RandomInsertErase/) benchmark of C++ hashmaps) has the rust std HashMap at around 40Mops/s and the leapfrog HashMap at around 50Mops/s, with default hasher from the standard library, which are competitive with the C++ hash maps from the linked benchmark.

# Probing

Both maps use the same leapfrog probing strategy, for which you can find more information on Jeff Preshing's [leapfrog probing blog post](https://preshing.com/20160314/leapfrog-probing/). A c++ implementation of the map can be found at his [Junction library](https://github.com/preshing/junction), which was the starting point for this implementation. Those maps don't have support for keys and therefore collisions, which these maps do. The probing strategy requires 8 bytes per key-value pair and and additional 8 bytes are stored for the hashed key so that it doesn't have to be rehashed for comparisons.

# Features

There is optional support for serde, via the `"serde"` feature.

## Usage with stable

This crate requires the `allocator_api` feature, which is only available on nightly. To enable use of the crate with the stable toolchain, the `"stable_alloc"` feature has been added.

If/when the `allocator_api` feature is no longer experimental, this feature flag will be removed.

# License

This crate is licensed under either the Apache License, Version 2.0, see [here](LICENSE-APACHE) or [here](http://www.apache.org/licenses/LICENSE-2.0) or the MIT license see [here](LICENSE-MIT) or [here](http://opensource.org/licenses/MIT), at your chosing. It can be used freely for both commercial and non-commercial applications, so long as you publish the contents of your chosen license file somewhere in your documentation.