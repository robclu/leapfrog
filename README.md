# Leapfrog

The leapfrog crate contains two HashMap implementations, `HashMap`, which is
a single-threaded HashMap, which can be used as an alternative to rust's built
in HashMap (without somewhat limited functionality but better performance), and 
`LeapMap`, which is fast, lock-free concurrent version of the `HashMap`, where
all operations can be used concurrently from any number of threads. The
performance for most real-world use cases is around 2x the next fastest Rust
hashmap, and around 13.6x `std::collections::HashMap` wrapped with RwLock for 16
cores. It also scales better than other hash map implementations. Benchmark results 
can be found at [rust hashmap benchmarks](https://github.com/robclu/conc-map-bench).

# Performance

A snapshot of the results for a read heavy workload using a 16 core AMD 3950x
CPU are the following (with throughput in Mops/second, cores in brackets, and 
performance realtive to `std::collections::HashMap` with RwLock):

| Map              | Throughput (1) | Relative (1) | Throughput (16) | Relative (16) |
|------------------|----------------|--------------|-----------------|---------------|
| RwLock + HashMap | 17.6           | 1.0          | 12.3            | 0.69          |
| Flurry           | 10.2           | 0.58         | 76.3            | 4.34          |
| DashMap          | 14.1           | 0.80         | 84.5            | 4.8           |
| LeapMap          | 16.8           | 0.95         | 167.8           | 9.53          |

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
[here](LICENSE-APACHE) or[here](http://www.apache.org/licenses/LICENSE-2.0) or
the MIT license see [here](LICENSE-MIT) or [here](http://opensource.org/licenses/MIT)
at your chosing. It can fe used freely for both commercial and non-commercial 
applications, so long as you publish the contents of your chosen license file
somewhere in your documentation.

