About
=====


Forked repository of the <a href="https://github.com/grigoryfedyukovich/aeval">AE-VAL Skolemizer</a>, enhanced with support for nondeterministic synthesis.


Installation
============

Compiles with gcc-5 (on Linux) and clang-700 (on Mac). Assumes preinstalled Gmp and Boost (libboost-system1.55-dev) packages.

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3 and LLVM)
* `make` to build AE-VAL

The binary of AE-VAL can be found in `build/tools/aeval/`.

Benchmarks
==========

Each benchmark is split into two files (for the universal and the existential parts of the formula). AE-VAL either returns `Valid` (with a skolem) or `Invalid`. Collection of the formulas can be found at `bench/tasks/` and the expected skolems at `bench/skolems/`.

For example, if AE-VAL is run with the following input:

`./build/tools/aeval/aeval bench/tasks/fast_1_e8_747_extend_s_part.smt2 bench/tasks/fast_1_e8_747_extend_t_part.smt2 `

Then, the output is `Valid` and the synthesized skolem should be close enough to the formula in `bench/skolems/fast_1_e8_747_extend_skolem.smt2`.

For a synthesized skolem that enables nondeterministic behavior, use option `--nondet`. 