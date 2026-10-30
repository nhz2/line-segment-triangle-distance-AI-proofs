# line-segment-triangle-distance-AI-proofs

AI-written proofs about the floating-point accuracy of the distance kernels in
[SimplexCellLists.jl](https://github.com/medyan-dev/SimplexCellLists.jl).

## Contents

| Directory | Result | Status |
| --- | --- | --- |
| [distance-accuracy](distance-accuracy) | Claim 4 of `dist_sqr_r_s_t`: `\|sqrt(d²) - d\| ≤ 64*eps(T)*ℓ + floatmin(T)^(1/4)` for `Float32` and `Float64` | Proved in Lean 4, no `sorry` or custom axioms |

The Lean proof in `distance-accuracy` was written by Codex GPT-6 Astra and
independently reviewed by Claude Opus 5.5. It also shows that the constant 8
originally stated in the source is false, so the source contract was loosened
to 64. See [distance-accuracy/README.md](distance-accuracy/README.md) for the
exact theorem, what it trusts, and how to check it.

## Layout

- `distance-accuracy/`: the Lean project, natural-language proofs, and
  independent Python and Julia checks.
- `Project.toml`, `Manifest.toml`: a Julia workspace that pins
  SimplexCellLists.jl to the commit the proof analyzes.

## Quick check

Requires [elan](https://github.com/leanprover/elan). From `distance-accuracy/`:

```sh
lake exe cache get   # download prebuilt Mathlib instead of compiling it
lake build
lake env lean Audit.lean
```

The final theorems should report only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.
