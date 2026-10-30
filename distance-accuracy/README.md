# Distance accuracy: claim 4 with constant 64

This directory contains a natural-language proof and a complete Lean proof of
claim 4 for the executable IEEE-word transcription of `dist_sqr_r_s_t`:

```
|sqrt(q) - d| ≤ 64 * eps(T) * L + floatmin(T)^(1/4).
```

`d` is the exact Euclidean distance between the input convex hulls, `q` is the
actual returned squared-distance word decoded as a real number, and `L` bounds
all absolute input coordinates. The theorem covers binary32 and binary64,
all nine ordered point/segment/triangle pairings, and all degeneracies. Its
only input assumptions are finite coordinates and
`0 ≤ L < floatmax(T)^(1/4)/4`. The square root in the theorem is the real square
root. Arithmetic uses round-to-nearest/ties-to-even, correctly rounded FMA,
and gradual underflow.

The original constant 8 is false. The included exact-intersection example
also disproves constant 9, including its underflow allowance.

## Final theorems

[FinalClaim4.lean](DistanceAccuracy/FinalClaim4.lean) declares:

- `DistanceAccuracy.finalClaim4`
- `DistanceAccuracy.finalClaim4_binary32`
- `DistanceAccuracy.finalClaim4_binary64`

The latter two prove `Geometry.accuracyStatement fp32` and
`Geometry.accuracyStatement fp64`. They take no output-accuracy certificates,
local rounding estimates, geometric coverage assumptions, or finite-intermediate
hypotheses. Those obligations are proved from the admissible inputs.

[Audit.lean](Audit.lean) prints the final theorem types and checks their logical
axioms. The dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`, custom axioms, or `native_decide` proofs in this development.
The older `format_claim4_conditional` theorem remains as a separate formalization
of the earlier certificate-based proof; the final theorem does not use it.

## Proof and model boundaries

- [ieee-proof.md](ieee-proof.md) is the natural-language proof corresponding
  to the completed Lean theorem.
- [formalization-notes.md](formalization-notes.md) maps that proof route to
  its implementation-level lemmas and constants.
- [proof.md](proof.md) is a superseded historical draft. Its rounded-intersection
  argument has a gap; it should not be used as the proof of claim 4. The completed
  proof does not use that argument, the implementation comments, or an external
  compensated-determinant accuracy theorem.
- [crossing-proof.md](crossing-proof.md) details the thin-triangle, plane-root,
  and missed-root endpoint cases.
- [lower-bound.md](lower-bound.md) explains the independently proved lower
  inequality and the small-coordinate case.
- [reconstruction.md](reconstruction.md) records the separate claim-5 argument.
  The final claim-4 theorem does not assume claim 5.

[IEEEAlgorithm.lean](DistanceAccuracy/IEEEAlgorithm.lean) explicitly transcribes
the arithmetic, exceptional-value handling, clamps, candidate comparisons,
weight remappings, and folds in `src/distances.jl` and `src/util.jl`. Lean proves
the theorem about this transcription and the pinned FP library's IEEE semantics.
The correspondence between the Julia source and the transcription is reviewed
and regression-tested; it is not a verified Julia compiler or a machine-checked
source translation. The source hashes are recorded in `proof.md`.

`ModelFixtures.lean` checks 42 fixtures against Julia bit-for-bit, including
squared distance, separation vector, and weights, in both formats and argument
orders. These fixtures check transcription regressions; the universal accuracy
result comes from the Lean proof.

## Build and audit

Lean is pinned to `v4.33.1`; FP to commit
`0658f8595a1771da24b4a55f1daed7cf1d99dda6`; Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`.
From this directory:

```sh
lake build
lake env lean Audit.lean
lake env lean ModelFixtures.lean
```

For a fresh checkout, `lake update` obtains the pinned dependencies first.
The IEEE reference encoder makes the fixture run take several minutes.

Independent checks, from the repository root:

```sh
python3 distance-accuracy/check_constants.py
julia --project=distance-accuracy distance-accuracy/check_reconstruction.jl
julia --project=distance-accuracy distance-accuracy/counterexample.jl
```

The Julia scripts use the `distance-accuracy` project, a member of the root
workspace. The root `Manifest.toml` pins SimplexCellLists.jl to commit
`f15f96a19c1aa36f02a224557f4628c4437944cb`; run
`julia --project=distance-accuracy -e 'using Pkg; Pkg.instantiate()'` once first.
That commit's `src/util.jl` matches
the analyzed hash in `proof.md`. Its `src/distances.jl` differs from the analyzed
file (commit `aaff918c16d8a7ed3c804f7caaf74bcfbee618a9`) only in docstrings.

These check rational constant estimates, reconstruction inequalities, and the
counterexample. They supplement the formal proof. Fixtures can be regenerated
with `julia --project=distance-accuracy distance-accuracy/generate_model_fixtures.jl`.

## Validation

The complete default `lake build` and `lake env lean Audit.lean` pass. The final
binary32/binary64 theorems have only the three standard logical dependencies
listed above. The 42 model fixtures and all three independent numerical checks
also passed during this proof session; the algorithm transcription and the
analyzed source hashes were unchanged afterward.
