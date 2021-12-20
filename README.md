# Leapfrog

The leapfrog crate contains two HashMap implementations, `HashMap`, which is
a single-threaded HashMap, which can be used as an alternative to rust's built
in HashMap (without some of the functionality), and `LeapMap`, which is concurrent
version of the `HashMap` and can be used concurrently from any number of threads.

Both maps use the same probing strategy, which is Jeff Preshing's [leapfrog probing](https://preshing.com/20160314/leapfrog-probing/),
for which you can read more about on his blog by following the link. The implementation's
of the maps here are simply rust implementations of the code in his [Junction library](https://github.com/preshing/junction),
and credit should go to him. The HashMaps are very fast!

# License

This crate is licensed under the simplified BSD license, so you may use it freely for both
commercial and non-commercial applications, so long as you publish the contents of the `LICENSE`
file somewhere in your documentation.

