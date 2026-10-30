# Comparing `dist_sqr` with other libraries

A comparison of SimplexCellLists.jl's simplex distance functions with CGAL and Geometric
Tools, for speed and accuracy, in Float64.

SimplexCellLists.jl is pinned by `Project.toml` to version
[0.3.0](https://github.com/medyan-dev/SimplexCellLists.jl/tree/v0.3.0),
the version [`../distance-accuracy`](../distance-accuracy) analyzes. Paths like
`src/distances.jl` below are in SimplexCellLists.jl.

## Results

Each run is recorded in [`results/runs/`](results/runs), one file per run named by its local
time, with the machine, the commit, and every result.

## What is compared

| name | library | notes |
|---|---|---|
| `SimplexCellLists` | SimplexCellLists.jl's `dist_sqr` | on `SIMD.Vec{8, Float64}` lanes, 8 pairs per call, as `src/neighbor-lists-grid.jl` does |
| `cgal_epick` | CGAL 6.2.1, `Exact_predicates_inexact_constructions_kernel` | double arithmetic with exact predicates |
| `cgal_epeck` | CGAL 6.2.1, `Exact_predicates_exact_constructions_kernel` | exact rationals on GMP; the exact d² is rounded to double |
| `gte_robust` | Geometric Tools Engine, commit `e09f5b3` | the robust `DCPQuery` variants where GTE has one: `ComputeRobust` for seg_seg, `UseConjugateGradient` for point_tri; its default seg_seg and point_tri are not in the same accuracy class, so they are left out |

Cases: point–segment, segment–segment, point–triangle, segment–triangle and triangle–triangle.
Every library runs all five. Where a library has no query for a case, it is built from one it
has with degenerate inputs: a segment as the triangle (P0, P1, P1), or a point as a zero-length
segment.

| case | SimplexCellLists | CGAL (both kernels) | Geometric Tools (`gte_robust`) |
|---|---|---|---|
| point_seg | `dist_sqr` | `squared_distance(Point_3, Segment_3)` | `DCPQuery<Vector3, Segment3>` |
| seg_seg | `dist_sqr` | `squared_distance(Segment_3, Segment_3)` | `DCPQuery<Segment3, Segment3>::ComputeRobust` |
| point_tri | `dist_sqr` | `squared_distance(Point_3, Triangle_3)` | `DCPQuery<Vector3, Triangle3>::UseConjugateGradient` |
| seg_tri | `dist_sqr` | `squared_distance(Triangle_3, Triangle_3)`, the segment as the triangle (P0, P1, P1) | `DCPQuery<Segment3, Triangle3>`, after removing exactly repeated vertices (see below) |
| tri_tri | `dist_sqr` | `squared_distance(Triangle_3, Triangle_3)` | `DCPQuery<Triangle3, Triangle3>`, after removing exactly repeated vertices |

Each shim in `shims/` states its mapping and details in a comment at the top.

Geometric Tools' segment–triangle and triangle–triangle queries throw on a zero-length segment or
triangle edge (a precondition, not a rounding failure). So `shims/gte.cpp` first removes exactly
repeated vertices from both simplexes and calls the Geometric Tools query for the shapes that remain,
as a careful user would: a zero-length segment is a point, a triangle with a repeated vertex is a
segment or a point.

MuJoCo is not included: its segment and triangle distance helpers (`mjc_segWeights`,
`mjc_triWeights`) are internal, not part of its public API, and its public distance query
(`mj_geomDistance`) needs a full model per query.

## How

The unit of work is a batch of 10,000 independent pairs. Every library has, per case, one C ABI
function that converts the pairs to the library's types, and two to run and free the result
(`shims/batch.hpp`):

    void* <lib>_<case>(const double* in, int64_t n)    // convert; not timed
    void batch_run(const void* batch, double* out)     // out[i] = squared distance of pair i; timed
    void batch_free(void* batch)

where `in` holds the pairs exactly as in the data files. The timed part is a plain loop of
queries over the converted pairs. Where a library returns closest points, `|p - q|²` is computed
in the loop; where it returns a distance, it is squared. A C++ exception that still escapes a
library gives NaN for that pair. SimplexCellLists has the same in Julia (`prepare` and
`scl_run!` in `harness/libs.jl`): the conversion copies the pairs to one array per coordinate, and
the timed loop runs `dist_sqr` on `SIMD.Vec` lanes, 8 pairs at a time. Its output is checked to be
bit identical to the scalar `dist_sqr` loop.

Everything is built from Julia, so the compiler and dependencies are pinned by this directory's
`Project.toml` and the workspace's shared `../Manifest.toml`:

- C and C++: clang 20.1.8 from Clang_jll (the LLVM of Julia 1.13), with
  `-O3 -march=native -DNDEBUG`, no `-ffast-math`, using the system's gcc 11 libstdc++ headers
  (linked statically) and linker. Each shim is a single translation unit, so library code can
  inline into the loop: CGAL and Geometric Tools are header only.
- Boost headers from boost_jll (1.87). GMP 6.3.0 and MPFR 4.2.2, with headers, from the full
  artifacts listed by Julia's GMP_jll and MPFR_jll stdlibs, copied into `build/deps`.
- CGAL and Geometric Tools sources are downloaded from pinned URLs, checked
  against their SHA-256 (see `SOURCES` in `build.jl`).

### Inputs and accuracy

`harness/gen.jl` writes two sets per case, all Float64:

- `random`: 10,000 pairs uniform in the unit cube.
- `hard`: 10,000 pairs of nearly parallel segments, sliver and degenerate simplexes, coplanar
  touching triangles, a vertex over a sliver's face, and translations up to 1e5. A quarter of
  them are scaled by 2^-500 and a quarter by 2^-270, exact powers of two, so that squares or
  fourth powers underflow. Then the pairs that SimplexCellLists.jl's tests and
  [`../distance-accuracy/counterexample.jl`](../distance-accuracy/counterexample.jl) found over
  8·eps·ℓ in Float32: one point–triangle, one segment–segment pair in both orders, and one
  segment–triangle. Their coordinates are exact in Float64.

Each set also has a reference: `dist_sqr` evaluated in 512-bit BigFloat. The error of a result
is `|√d² - d|` as a fraction of the bound that `src/distances.jl` states and
[`../distance-accuracy`](../distance-accuracy) proves, `64·eps·ℓ + floatmin^(1/4)`, where `ℓ`
is the largest absolute coordinate in the pair. So an error over 1 is outside the bound, and a
nonfinite result has error Inf. `harness/score.jl` gives the `median`, `p99` and `max` of each
set.

### Timing

`harness/bench.jl` times the random sets in one Julia process, pinned to one CPU with
`taskset`, on an otherwise idle machine. Each measurement is Chairmarks' minimum time of a timed batch
(the query loop) over all pairs of a set, sampled for 1 s (`BENCH_SECONDS`). There are two rounds, the second
in the opposite order, so the two minimums of each measurement show the noise.

## Requirements outside Julia

Julia's package manager provides the C and C++ compiler (Clang_jll), Boost, GMP and MPFR. The
rest has to be on the machine. Tested on Pop!_OS 22.04 (Ubuntu 22.04), x86_64:

- **Julia 1.13**, e.g. from [juliaup](https://github.com/JuliaLang/juliaup). Clang_jll is pinned
  to 20.1.8, the LLVM of Julia 1.13; other Julia versions need the matching Clang_jll.
- **gcc 11's C++ standard library and the C runtime**, which Clang_jll's clang compiles and links
  against (headers, `libstdc++.a` for static linking, crt files), and the **GNU linker**:

      sudo apt install libstdc++-11-dev libgcc-11-dev libc6-dev binutils

  On another distribution or gcc version, set `GCC_INSTALL_DIR` in `build.jl` to the directory
  holding that gcc's `crtbegin.o`.
- **tar and xz**, to unpack the downloaded sources (`sudo apt install tar xz-utils`).
- **taskset**, to pin the timing run to one CPU (`sudo apt install util-linux`).
- **Network access** to github.com (library sources) and Julia's package servers, for the
  first build.

`build.jl` checks for the build requirements (all but taskset and network access) before
building, and stops with a message naming what is missing.

## Running

From this directory:

    julia --project=. -e 'using Pkg; Pkg.instantiate()'
    julia --project=. build.jl                  # downloads and builds into build/
    julia --project=. harness/gen.jl            # writes data/
    julia --project=. harness/accuracy.jl       # writes results/accuracy.csv
    taskset -c 2 julia --project=. harness/bench.jl   # writes results/timing.csv
    julia --project=. harness/record.jl         # writes results/runs/<YYYY-MM-DD-HHMM>.md

`build.jl` skips what is up to date, and prints the version of every tool and library at the end.
`BENCH_SECONDS=0.05 julia --project=. harness/bench.jl` checks that the timing runs in a few
seconds (it overwrites `results/timing.csv`).

## Layout

| path | contents |
|---|---|
| `build.jl` | fetches sources and builds every shim into `build/lib` |
| `shims/` | the C ABI batch functions: `cgal.cpp` (built as Epick and, with `-DEXACT`, Epeck), `gte.cpp`, and `batch.hpp`, the loop the C++ shims share |
| `harness/gen.jl` | the inputs and BigFloat references |
| `harness/libs.jl` | the table of libraries, how to call each batch function, and the SimplexCellLists batch |
| `harness/score.jl` | the error measures above |
| `harness/accuracy.jl` | runs every library on every case and set, and writes `results/accuracy.csv` |
| `harness/bench.jl` | the timing, writing `results/timing.csv` |
| `harness/record.jl` | writes a record of a run to `results/runs/`, named by the local time: `versioninfo()` (with the CPU), the commit of this repository, and one table of both CSVs |
| `results/` | `runs/`, one record per run, and the git-ignored `accuracy.csv` and `timing.csv` of the latest run |

`data/` and `build/` are generated, and git-ignored.
