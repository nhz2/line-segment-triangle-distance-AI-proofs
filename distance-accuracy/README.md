# Distance accuracy: claim 4 with constant 64

This directory contains a natural-language proof and a complete Lean proof of
claim 4 for the executable IEEE-word transcription of `dist_sqr_r_s_t` in
SimplexCellLists.jl:

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

## Authorship

The proofs, Lean development, and checks in this directory were written by
Codex GPT-6 Astra. Claude Opus 5.5 independently reviewed them; see
[Independent review](#independent-review).

## Final theorems

[FinalClaim4.lean](DistanceAccuracy/FinalClaim4.lean) declares:

- `DistanceAccuracy.finalClaim4`
- `DistanceAccuracy.finalClaim4_binary32`
- `DistanceAccuracy.finalClaim4_binary64`

The latter two prove `Geometry.accuracyStatement fp32` and
`Geometry.accuracyStatement fp64`, defined in
[Geometry.lean](DistanceAccuracy/Geometry.lean). They take no output-accuracy
certificates, local rounding estimates, geometric coverage assumptions, or
finite-intermediate hypotheses. Those obligations are proved from the
admissible inputs.

In the statement, `2 * I.format.unitRoundoff` is `eps(T)` (`2^-23` or `2^-52`),
`I.format.minNormal` is `floatmin(T)`, and `I.format.maxFinite` is
`floatmax(T)`, as defined by the pinned FP library.

[Audit.lean](Audit.lean) prints the final theorem types and checks their logical
axioms. The dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`, custom axioms, or `native_decide` proofs in this development.
The older `format_claim4_conditional` theorem remains as a separate formalization
of the earlier certificate-based proof; the final theorem does not use it.

## Trusted base and scope

Lean checks every step from the definitions to the final theorem. The result
relies on these unverified links:

- **FP library semantics.** The theorem is about the IEEE operations of the
  pinned [lean-ieee754](https://github.com/tunnellm/lean-ieee754) library, not
  about hardware. A rounding bug in that library would make the theorem
  describe the wrong arithmetic. The model fixtures compare it with hardware
  results on 42 inputs.
- **Transcription.** [IEEEAlgorithm.lean](DistanceAccuracy/IEEEAlgorithm.lean)
  transcribes the arithmetic, exceptional-value handling, clamps, candidate
  comparisons, weight remappings, and folds in `src/distances.jl` and
  `src/util.jl`. The correspondence is reviewed and regression-tested; it is
  not a verified Julia compiler or a machine-checked source translation.
- **Julia runtime.** The theorem assumes default IEEE behavior. It does not
  hold under `@fastmath` or with `set_zero_subnormals(true)`, which removes
  the gradual underflow behind the `floatmin(T)^(1/4)` term.

Not covered:

- The `SIMD.Vec` code path. The source states it is bit identical to the
  scalar path, but that is not proved here.
- Element types other than `Float32` and `Float64`, such as `Float16`.
- Claim 5, the accuracy of `r` and the weights. [reconstruction.md](reconstruction.md)
  argues it separately; the claim-4 theorem does not assume it.

## Documents

- [ieee-proof.md](ieee-proof.md) is the natural-language proof corresponding
  to the completed Lean theorem.
- [formalization-notes.md](formalization-notes.md) maps that proof route to
  its implementation-level lemmas and constants.
- [crossing-proof.md](crossing-proof.md) details the thin-triangle, plane-root,
  and missed-root endpoint cases.
- [lower-bound.md](lower-bound.md) explains the independently proved lower
  inequality and the small-coordinate case.
- [reconstruction.md](reconstruction.md) records the separate claim-5 argument.
- [proof.md](proof.md) is a superseded historical draft. Its rounded-intersection
  argument has a gap; it should not be used as the proof of claim 4. The completed
  proof does not use that argument, the implementation comments, or an external
  compensated-determinant accuracy theorem. It records the analyzed source hashes.

## Build and audit

Lean is pinned to `v4.33.1`; FP to commit
`0658f8595a1771da24b4a55f1daed7cf1d99dda6`; Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`.
From this directory:

```sh
lake exe cache get   # download prebuilt Mathlib instead of compiling it
lake build
lake env lean Audit.lean
lake env lean ModelFixtures.lean
```

With the Mathlib cache, `lake build` takes a few minutes. The fixture run uses
the library's IEEE reference encoder and takes about a minute.

`ModelFixtures.lean` checks 42 fixtures against Julia bit for bit, including
squared distance, separation vector, and weights, in both formats and argument
orders. These fixtures catch transcription regressions; the universal accuracy
result comes from the Lean proof. Regenerate them with
`julia --project=distance-accuracy distance-accuracy/generate_model_fixtures.jl`.

### Independent numerical checks

From the repository root, after
`julia --project=distance-accuracy -e 'using Pkg; Pkg.instantiate()'`:

```sh
python3 distance-accuracy/check_constants.py
julia --project=distance-accuracy distance-accuracy/check_reconstruction.jl
julia --project=distance-accuracy distance-accuracy/counterexample.jl
```

These check rational constant estimates, reconstruction inequalities, and the
counterexample. They supplement the formal proof.

The Julia scripts use the `distance-accuracy` project, a member of the root
workspace. The root `Manifest.toml` pins SimplexCellLists.jl to commit
`f15f96a19c1aa36f02a224557f4628c4437944cb`. The proof was written against
commit `aaff918c16d8a7ed3c804f7caaf74bcfbee618a9`; the two commits differ only
in docstrings. `proof.md` records the SHA-256 hashes of `src/distances.jl` and
`src/util.jl` at both commits. To check the pinned copy:

```sh
julia --project=distance-accuracy -e 'using SimplexCellLists, SHA; for f in ("distances.jl", "util.jl"); println(f, " ", bytes2hex(open(sha256, joinpath(pkgdir(SimplexCellLists), "src", f)))); end'
```

## Independent review

On 2026-10-29, Claude Opus 5.5 reviewed this development from a fresh checkout:

- `lake build` and `lake env lean Audit.lean` pass. The final theorems depend
  only on `propext`, `Classical.choice`, and `Quot.sound`. Neither this
  project nor the FP library uses `sorry`, custom axioms, `native_decide`,
  `implemented_by`, or `extern`.
- A restatement of `finalClaim4_binary64` with literal constants (`2^-52`,
  `2^-1022`) and the explicit premises type-checks against the theorem.
- `IEEEAlgorithm.lean` was compared line by line with `src/distances.jl` and
  `src/util.jl`, and matches: FMA nesting, NaN clamping, candidate order and
  tie-breaking, weight remapping, and argument-swap dispatch.
- Regenerating the fixtures from Julia reproduced `ModelFixtures.lean` exactly,
  and all 42 fixtures pass. The three independent numerical checks pass.
