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

## Reciprocal-and-multiply revision

**The same constant 64 is proved for SimplexCellLists.jl commit
[`287e746`](https://github.com/medyan-dev/SimplexCellLists.jl/commit/287e746639b4e6aa63dba105cdd023fdd6dfe086)
(#30), the commit the root workspace pins**, in binary32 and binary64, for
all nine ordered point/segment/triangle pairings, including degeneracies and
the same admissible coordinate range. Its segment kernel clamps and
reprojects: the first segment parameter uses direct division, and the second
and third use `fma(...)*inv(dot(direction,direction))`.

[InvMultiplyFinal.lean](DistanceAccuracy/InvMultiplyFinal.lean) declares:

- `DistanceAccuracy.invMultiplyClaim4`: the complete two-sided bound.
- `DistanceAccuracy.invMultiplyClaim4_binary32` and
  `DistanceAccuracy.invMultiplyClaim4_binary64`: the format specializations.
- `DistanceAccuracy.invMultiplyUpper`: the upper inequality alone.

`invMultiplyAccuracyStatement` is `Geometry.accuracyStatement` with the
revised model in place of the old one. Like the original theorem, these take
only the finite-coordinate admissibility assumptions, with no local rounding,
finite-intermediate, coverage, or output-accuracy certificates:

```
|sqrt(q) - d| ≤ 64 * eps(T) * L + floatmin(T)^(1/4).
```

The model is [InvMultiplyAlgorithm.lean](DistanceAccuracy/InvMultiplyAlgorithm.lean).
It was transcribed from an uncommitted checkout of `src/distances.jl` on
2026-11-02, SHA256
`faa7bc862d6ddfd2d00c868fcf06eb87e9eb747d79ca40b75481fadd0b0ebc18`. The
code of `src/distances.jl` at `287e746`, SHA256
`06acfcfef240ea8b03db01a1072141cf0d568c449806ec982471a08a9254fd2c`, was
then compared with the model line by line and matches: only comments
changed. Between 0.3.0 and `287e746` the other kernels changed only by
`_clamp01_div(n, d)` and `_inv0(x)`, which are `clamp01nan(n/d)` and
`inv(x)` for floats, and `src/util.jl` did not change, so the shared
`IEEEAlgorithm` kernels still match. Only the segment/segment kernel is
redefined; the segment/triangle and triangle/triangle kernels are textually
the old ones calling it. The old model and its theorem remain separate.
Reciprocal means correctly rounded `1/a`, followed by a separately rounded
multiplication, under the same IEEE/FMA assumptions as the earlier proof.

### Why clamp-and-reproject still fits 64

The old proof selected an explicit endpoint candidate when the relaxed line
solution left the segment. The kernel at `287e746` has no endpoint
candidates, so the proof replaces that argument as follows. It was first
developed for an unmerged draft that divided directly in all three solves;
the modules shared with that draft, which don't depend on how the division
is rounded, are named `Reproject*`.

1. [ReprojectGeometry.lean](DistanceAccuracy/ReprojectGeometry.lean) proves
   exact-real segment optimality of clamp-and-reproject, including parallel
   and zero directions, and identifies the three scalar formulas with the
   source formulas.
2. [ReprojectProjection.lean](DistanceAccuracy/ReprojectProjection.lean),
   [InvMultiplyProjection.lean](DistanceAccuracy/InvMultiplyProjection.lean),
   [InvMultiplyWord.lean](DistanceAccuracy/InvMultiplyWord.lean), and
   [InvMultiplyAdmissible.lean](DistanceAccuracy/InvMultiplyAdmissible.lean)
   prove that the rounded second solve either selects the correct clipped
   endpoint or has a bounded displacement from the unconstrained line
   solution. In the latter case, orthogonality makes its contribution a
   **squared** loss. The third solve has a second squared-loss estimate.
   The shared `P·Q` word retains its actual operand order.
3. [InvMultiplyArithmetic.lean](DistanceAccuracy/InvMultiplyArithmetic.lean)
   composes reciprocal and multiplication errors into a relative factor at
   most `2.001rho`, where `rho = eps/2`, plus the usual subnormal product
   error. This enlarges the local projection coefficient from **8.38**, its
   value for a single division, to **9.38**.
   [InvMultiplyDots.lean](DistanceAccuracy/InvMultiplyDots.lean) and its
   reversed counterpart discharge reciprocal normality, reciprocal
   finiteness, and product range from the coordinate assumptions for
   non-short directions. Short directions need no accurate reciprocal: their
   entire geometric contribution is covered by the underflow budget.
4. [ReprojectCoverage.lean](DistanceAccuracy/ReprojectCoverage.lean) and
   [InvMultiplyRaw.lean](DistanceAccuracy/InvMultiplyRaw.lean) combine those
   estimates with boundary interpolation. They also handle either direction
   being shorter than the fourth root of the least subnormal.
5. [ReprojectStored.lean](DistanceAccuracy/ReprojectStored.lean) sharpens
   reconstruction and norm evaluation. With `D = 3.5L` and `n` the exact
   residual norm at the computed weights, the stored root score is at most
   `(1 + 2.52rho)n + 1.001rho D + 3eta + sqrt(2eta)`.
   Keeping the dependence on `n` saves enough error budget at small
   distances to pay for the extra projection.
6. [ReprojectEnvelope.lean](DistanceAccuracy/ReprojectEnvelope.lean) proves
   that the squared-loss function `G(z) = hypot(F(z), 8.38)` and this sharper
   reconstruction fit the old envelope `rho D F(d/(rho D)) + 3.55rho D + 6h`.
   [InvMultiplyEnvelope.lean](DistanceAccuracy/InvMultiplyEnvelope.lean)
   redoes this for coefficient 9.38 with `FI(z) = max(F(z), 20)`: the
   direct segment budget increases from `19rho*D + 6h` to `24rho*D + 6h`.
   All constants are exact rational numbers checked by Lean.
7. [InvMultiplyKernelUpper.lean](DistanceAccuracy/InvMultiplyKernelUpper.lean)
   discharges that envelope for the actual IEEE kernel. The separate
   `InvMultiply*Upper` and assembly modules carry it through the existing
   nearest-feature and crossing geometry. At the critical triangle crossing
   argument `z = 24.2`, `FI(z) = F(z)`, so the final triangle budget stays
   **`36.4rho*(3.5L) + 32h`**, which fits `128rho L + floatmin^(1/4)`.

[InvMultiplyEvaluation.lean](DistanceAccuracy/InvMultiplyEvaluation.lean)
supplies the independently checked lower and small-coordinate bounds.

### Revision checks

From this directory:

```sh
lake build
lake env lean InvMultiplyAudit.lean
julia --project=. --startup-file=no generate_model_fixtures.jl --inv-multiply
lake env lean InvMultiplyFixtures.lean
julia --project=. --startup-file=no check_segment_kernel.jl 10000
```

The axiom audit checks the actual executable-model theorem and reports only
`propext`, `Classical.choice`, and `Quot.sound`. The 54 runtime fixtures
compare squared distance, separation, and weights against Julia, including
reciprocal overflow for tiny directions, directions just above the
short-direction cutoff, and large coordinates. These are regression checks;
the universal accuracy result is kernel-checked.

[check_segment_kernel.jl](check_segment_kernel.jl) exercises whichever
package is loaded. At `287e746` it passed 20,000 segment cases against an
independent exact-rational enumeration and 4,000 segment/triangle and
triangle/triangle cases whose reference results pass exact supporting-plane
optimality certificates. Its largest sampled error was 2.81% of the
constant-64 bound. SimplexCellLists.jl's complete `test/test-mindistance.jl`
also passed at `287e746`. These checks supplement the universal Lean
theorem; they are not its justification.

### Examples approaching 10 epsilon

[rounding_examples.jl](rounding_examples.jl) contains explicit
segment/triangle inputs, found by search. All coordinates are exactly
representable integers, and both pairs intersect exactly (`d = 0`). With
`ell` the largest absolute input coordinate and real square root, at
`287e746`:

| Format | `abs(sqrt(q) - d) / (eps(T) * ell)` | `ell` |
| --- | ---: | ---: |
| Float32 | 9.415350423342458560 | 10312324 |
| Float64 | 9.185377033506981696 | 5552362190545168 |

Multiplying all coordinates by `2^-24` and `2^-53`, respectively, makes
their magnitudes less than one and preserves these coefficients. The script
checks exact rational intersection, rational squared-error inequalities, and
power-of-two rescaling. Even after adding the theorem's underflow allowance,
constants 9.415 and 9.185, respectively, are insufficient on these inputs.
These are examples found by search, not claimed worst cases; neither reaches 10.

From this directory:

```sh
julia --project=. --startup-file=no rounding_examples.jl
lake env lean RoundingExamples.lean
```

[RoundingExamples.lean](RoundingExamples.lean) kernel-checks the exact
intersection and strict coefficient intervals `(9.415, 9.416)` and
`(9.185, 9.186)`, with only the standard Lean axioms. A separate runtime
fixture checks that the squared-distance output bits of the reciprocal IEEE
model match Julia; that bit comparison is not a kernel theorem. Regenerate
the file with `rounding_examples.jl --generate-lean`. The deterministic
mutation search is in [search_rounding_examples.jl](search_rounding_examples.jl);
its optional argument sets the iteration count per format (default 50 million).

## Authorship

The original three-candidate proof, the reciprocal-and-multiply revision,
their Lean development, and checks were written by Codex GPT-6 Astra.
Claude Opus 5.5 independently reviewed both; see
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
  results on 42 inputs, and the revision's fixtures on 54.
- **Transcription.** [IEEEAlgorithm.lean](DistanceAccuracy/IEEEAlgorithm.lean)
  transcribes the arithmetic, exceptional-value handling, clamps, candidate
  comparisons, weight remappings, and folds in `src/distances.jl` and
  `src/util.jl` of SimplexCellLists.jl 0.3.0, and
  [InvMultiplyAlgorithm.lean](DistanceAccuracy/InvMultiplyAlgorithm.lean)
  replaces its segment kernel with that of `287e746`. The correspondence is
  reviewed and regression-tested; it is not a verified Julia compiler or a
  machine-checked source translation.
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
  compensated-determinant accuracy theorem.

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
result comes from the Lean proof. They were generated with
SimplexCellLists.jl 0.3.0, which `IEEEAlgorithm.lean` transcribes. The root
workspace now pins `287e746`, whose new segment kernel gives a different `t`
weight in the `parallel-segments` fixture, so regenerate them in an
environment with 0.3.0 rather than with `--project=distance-accuracy`.

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
`287e746`. All three checks also pass there; the counterexample uses the
segment/triangle crossing path, which did not change.

## Independent review

On 2026-10-30, Claude Opus 5.5 reviewed this development against
SimplexCellLists.jl 0.3.0:

- After a clean `lake build`, `lake env lean Audit.lean` passes. The final
  theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
  Neither this project nor the FP library uses `sorry`, custom axioms,
  `native_decide`, `implemented_by`, or `extern`.
- A restatement of `finalClaim4_binary64` with literal constants (`2^-52`,
  `2^-1022`, `(2^53 - 1) * 2^971`) and the explicit premises type-checks
  against the theorem.
- `IEEEAlgorithm.lean` was compared line by line with `src/distances.jl` and
  `src/util.jl`, and matches: FMA nesting, NaN clamping, candidate order and
  tie-breaking, weight remapping, and argument-swap dispatch.
- Regenerating the fixtures from Julia reproduced `ModelFixtures.lean` exactly,
  and all 42 fixtures pass. The three independent numerical checks pass.

On 2026-11-02, Claude Opus 5.5 reviewed the reciprocal-and-multiply revision
against SimplexCellLists.jl `287e746`:

- After a clean `lake build`, `lake env lean InvMultiplyAudit.lean` passes.
  The final theorems depend only on `propext`, `Classical.choice`, and
  `Quot.sound`. The revision's modules use no `sorry`, axioms,
  `native_decide`, `implemented_by`, `extern`, `opaque`, or custom
  elaborators, and change no earlier module, so `Geometry.lean`'s distance
  and admissibility definitions are the ones reviewed above.
- `invMultiplyAccuracyStatement` is `Geometry.accuracyStatement` with only
  the evaluator replaced. A restatement of `invMultiplyClaim4_binary64` with
  literal constants and the explicit premises type-checks against the theorem.
- The SHA256 of `src/distances.jl` at `287e746` matches the one above, and
  `287e746` is on SimplexCellLists.jl's `main`. `InvMultiplyAlgorithm.lean`
  was compared line by line with it and matches, including operand order in
  `fma(t, b, dot3(P, Q0mP0))*inv(a)`. The source diff from 0.3.0 confirms
  the other kernels changed only by `_clamp01_div` and `_inv0`.
- In the compiled LLVM IR of the Julia segment kernel, in both formats, the
  arithmetic is two `fdiv 1.0, x` reciprocals and one direct `fdiv`, with
  no fast-math, contraction, or reciprocal flags.
- Regenerating `InvMultiplyFixtures.lean` from Julia reproduced it exactly,
  and all 54 fixtures pass. `RoundingExamples.lean`,
  `check_segment_kernel.jl`, and the three older numerical checks pass.
- A separate adversarial search of the segment kernel, 300,000 random
  nearly parallel, crossing, short, long/short, and far-from-origin cases
  per format plus hill climbing, against an exact rational reference, found
  errors of at most `3.85*eps(T)*ell`.
