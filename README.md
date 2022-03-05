[![version](https://img.shields.io/crates/v/leapfrog)](https://crates.io/crates/leapfrog)
[![documentation](https://docs.rs/leapfrog/badge.svg)](https://docs.rs/leapfrog)

# Leapfrog

The leapfrog crate contains two HashMap implementations, `HashMap`, which is
a single-threaded HashMap, which can be used as an alternative to rusts built
in HashMap (with somewhat limited functionality but better performance), and 
`LeapMap`, which is fast, lock-free concurrent version of the `HashMap`, where
all operations can be used concurrently from any number of threads. The
performance for most real-world use cases is around 2x the next fastest Rust
hashmap, and around 13.6x `std::collections::HashMap` wrapped with RwLock for 16
cores. It also scales better than other hash map implementations. Benchmark results 
can be found at [rust hashmap benchmarks](https://github.com/robclu/conc-map-bench).
These bechmarks, however, are limited in the use cases that they cover, and likely
should be extended to cover a much wider scope. Nevertheless, for those bechamarks,
these maps are the fastest. Please see the crate documentation for more details,
specifically the limtiations.

**If the value type for the map supports atomic operations then this map will not 
lock, while if the value type does not support atomic perations then accessing the 
value uses an efficient spinlock implementation.**

In their current form, while the API is similar to the `std` HashMap implementation,
these maps are not drop-in replacements for the `HashMap`, `RwLock<HashMap>`, `DashMap`,
etc.

# Planned Extensions

Based on feedback, not storing the keys introduces problems for many use cases. However,
for the cases where such a limitation is acceptable for increased performance, I plan
on keeping the `LeapMap` as is, and adding support for iterators, rayon, serde, and any 
other requested features, as well as a `LeapSet`.

I also plan on adding a map which uses the same probing strategy, but which does store
keys. This wont be as fast as the `LeapMap`, but should be a drop-in replacement for
other maps (with hopefully better performance). I will also add a `Set` version of that,
with the same support as the mentioned above.

# Performance

A snapshot of the results for the LeapMap on a read heavy workload using a 16 core 
AMD 3950x CPU are the following (with throughput in Mops/second, cores in brackets, 
and  performance realtive to `std::collections::HashMap` with RwLock):

| Map              | Throughput (1) | Relative (1) | Throughput (16) | Relative (16) |
|------------------|----------------|--------------|-----------------|---------------|
| RwLock + HashMap | 17.6           | 1.0          | 12.3            | 0.69          |
| Flurry           | 10.2           | 0.58         | 76.3            | 4.34          |
| DashMap          | 14.1           | 0.80         | 84.5            | 4.8           |
| LeapMap          | 16.8           | 0.95         | 167.8           | 9.53          |

For the single threaded leapfrog HashMap, a benchmark of random inserts and deletes (a port of
[this](https://martin.ankerl.com/2019/04/01/hashmap-benchmarks-03-03-result-RandomInsertErase/)
benchmark of C++ hashmaps) has the rust std HashMap at around 57Mops/s and
the leapfrog HashMap at around 80Mops/s, with Murmur as the hash function. The
leapfrog HashMap has performance which is at least comparable to, if not better
than, the fastest C++ hash maps from the linked benchmark.

# Probing

Both maps use the same leapfrog probing strategy, for which you can find more
information on Jeff Preshing's [leapfrog probing blog post](https://preshing.com/20160314/leapfrog-probing/),
A c++ implementation of the map can be found at his [Junction library](https://github.com/preshing/junction),
which was the starting point for this implementation.

# Additional Notes

For a more detailed description of the limitations and behaviour of the maps,
see the crate documentation: 

# License

This crate is licensed under either the Apache License, Version 2.0, see 
[here](LICENSE-APACHE) or [here](http://www.apache.org/licenses/LICENSE-2.0) or
the MIT license see [here](LICENSE-MIT) or [here](http://opensource.org/licenses/MIT),
at your chosing. It can be used freely for both commercial and non-commercial 
applications, so long as you publish the contents of your chosen license file
somewhere in your documentation.

