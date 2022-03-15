[![version](https://img.shields.io/crates/v/leapfrog)](https://crates.io/crates/leapfrog)
[![documentation](https://docs.rs/leapfrog/badge.svg)](https://docs.rs/leapfrog)

# Leapfrog

The leapfrog crate contains two hash map implementations, `HashMap`, which is
a single-threaded HashMap, and `LeapMap`, which is fast, concurrent 
version of the `HashMap`, where all operations can be performed concurrently 
from any number of threads. If the key and value types support atomic operations
then the map is lock-free, and when there is no atomic support for either the key
or value, then operations within the map on that non-atomic type use an efficient
spinlock and the locking is very fine-grained.

The performance of both maps is good on the benchmarks it's been tested on. The
`HashMap` is between 1.2 and 1.5x the `std::collections::HashMap`. Compared to
`RwLock<HashMap>`, on 16 cores the `LeapMap` is around 13.5x faster. It also
scales very well up to high core counts, for multiple workloads.  Benchmark results 
can be found at [rust hashmap benchmarks](https://github.com/robclu/conc-map-bench).
These bechmarks, however, are limited in the use cases that they cover, and 
should be extended to cover a much wider scope. Nevertheless, for those bechmarks,
the `LeapMap` is the fastest map. 

For more details on the API and the differences compared to `std::collections::HashMap`,
please see the crate documentation.

# Recent Changes

The implementations of these maps have recently been updated to store keys, so the API
for both is much closer to `std::collections::HashMap`. There is now also support for
serde with the optional "serde" feature. The maps also now have iterator support. The
default hasher has been changed to be the DOS resistant hasher from the standard library.

# Current Limitations

These is not yet support for rayon, but it will be added next. There are also no set
versions of the maps, which are also planned next.

# Performance

A snapshot of the results for the LeapMap on a read heavy workload using a 16 core 
AMD 3950x CPU are the following (with throughput in Mops/second, cores in brackets, 
and  performance realtive to `std::collections::HashMap` with RwLock):

| Map              | Throughput (1) | Relative (1) | Throughput (16) | Relative (16) |
|------------------|----------------|--------------|-----------------|---------------|
| RwLock + HashMap | 19.4           | 1.0          | 11.7            | 0.60          |
| Flurry           | 11.2           | 0.58         | 80.8            | 4.16          |
| DashMap          | 14.1           | 0.72         | 87.5            | 4.51          |
| LeapMap          | 17.8           | 0.92         | 148.0           | 7.62          |

For the single threaded leapfrog `HashMap`, a benchmark of random inserts and deletes (a port of
[this](https://martin.ankerl.com/2019/04/01/hashmap-benchmarks-03-03-result-RandomInsertErase/)
benchmark of C++ hashmaps) has the rust std HashMap at around 40Mops/s and
the leapfrog HashMap at around 50Mops/s, with default hasher from the standard library,
which are competitive with the C++ hash maps from the linked benchmark.

# Probing

Both maps use the same leapfrog probing strategy, for which you can find more
information on Jeff Preshing's [leapfrog probing blog post](https://preshing.com/20160314/leapfrog-probing/),
A c++ implementation of the map can be found at his [Junction library](https://github.com/preshing/junction),
which was the starting point for this implementation. Those maps don't have support for keys and
therefore collisions, which these maps do. The probing strategy requires 8 bytes per key-value pair
and and additional 8 bytes are stored for the hashed key so that it doesn't have to be rehashed for
comparisons.

# License

This crate is licensed under either the Apache License, Version 2.0, see 
[here](LICENSE-APACHE) or [here](http://www.apache.org/licenses/LICENSE-2.0) or
the MIT license see [here](LICENSE-MIT) or [here](http://opensource.org/licenses/MIT),
at your chosing. It can be used freely for both commercial and non-commercial 
applications, so long as you publish the contents of your chosen license file
somewhere in your documentation.

