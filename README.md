# line-segment-triangle-distance-AI-proofs

AI-written proofs about the floating-point accuracy of the distance kernels in
[SimplexCellLists.jl](https://github.com/medyan-dev/SimplexCellLists.jl).

## Contents

| Directory | Result | Status |
| --- | --- | --- |
| [distance-accuracy](distance-accuracy) | Claim 4 of `dist_sqr_r_s_t`: `\|sqrt(d²) - d\| ≤ 64*eps(T)*ℓ + floatmin(T)^(1/4)` for `Float32` and `Float64` | Proved in Lean 4, no `sorry` or custom axioms |
| [Reciprocal-and-multiply revision](distance-accuracy/README.md#reciprocal-and-multiply-revision) | Same constant-64 bound for the clamp-and-reproject segment kernel of SimplexCellLists.jl commit `287e746`, with reciprocal/multiply second and third segment solves, including the higher kernels | Proved in Lean 4, no `sorry` or custom axioms |
| [library-comparison](library-comparison) | Speed and accuracy of `dist_sqr` against CGAL and Geometric Tools in `Float64`, with errors as a fraction of the claim 4 bound | Results of each run in [library-comparison/results/runs](library-comparison/results/runs) |

The Lean proofs in `distance-accuracy` were written by Codex GPT-6 Astra and
independently reviewed by Claude Opus 5.5. The original proof also shows that
the constant 8 originally stated in the source is false, so the source
contract was loosened to 64. See
[distance-accuracy/README.md](distance-accuracy/README.md) for the exact
theorem, what it trusts, and how to check it.

## Layout

- `distance-accuracy/`: the Lean project, natural-language proofs, and
  independent Python and Julia checks.
- `library-comparison/`: a Julia project that builds CGAL and Geometric Tools
  shims and compares them with `dist_sqr`.
- `Project.toml`, `Manifest.toml`: a Julia workspace of `distance-accuracy`
  and `library-comparison`, with one shared Manifest that pins
  SimplexCellLists.jl to commit `287e746`, the version the
  reciprocal-and-multiply theorem analyzes. The original theorem analyzes
  version 0.3.0.

## Quick check

Requires [elan](https://github.com/leanprover/elan). From `distance-accuracy/`:

```sh
lake exe cache get   # download prebuilt Mathlib instead of compiling it
lake build
lake env lean Audit.lean            # SimplexCellLists.jl 0.3.0
lake env lean InvMultiplyAudit.lean # commit 287e746, the pinned version
```

The final theorems should report only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.
