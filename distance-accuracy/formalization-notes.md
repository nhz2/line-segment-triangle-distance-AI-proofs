# The completed implementation-level proof

The final theorem is `DistanceAccuracy.finalClaim4` in `FinalClaim4.lean`.
It proves the real-square-root interpretation of claim 4 for all admissible
binary32 and binary64 inputs to `IEEEAlgorithm.evaluate`. The full natural-language
proof is [ieee-proof.md](ieee-proof.md); this note maps its argument to the Lean
modules and estimates. The historical `proof.md` is superseded and contains a
gap in its rounded-intersection argument. The completed proof uses the
conservative budgets and exact geometric coverage described below.

Write `rho = eps(T)/2`, `eta` for the least positive subnormal,
`h = eta^(1/4)`, `H = floatmin(T)^(1/4)`, and `D = 3.5 L`. All coordinates are
finite, and `L < floatmax(T)^(1/4)/4`. Exact distances and norms in this note
are real quantities.

## Actual floating-point operations

The FP library supplies executable IEEE encodings, arithmetic, comparisons,
and their mathematical semantics. `IEEEBridge` and `OperationBounds` derive
local error bounds and decoding facts from those semantics. Under the proved
range conditions, each rounded arithmetic result has the mixed error bound

```
|fl(z) - z| ≤ rho |z| + eta/2.
```

The range lemmas are proved from the original coordinate cutoff. The admissible-input candidate bounds do not require their callers to certify
intermediate accuracy or finiteness. Some local lemmas expose such premises for reuse;
`FaceLocalAdmissible`, `SecondSolveAdmissible`, `CrossReducedAdmissible`, and
related wrappers discharge them before the final assembly.

Clamping remains meaningful when a quotient or reciprocal is exceptional.
`OperationBounds` proves that `clamp01nan` returns a finite value in `[0,1]`
for every input word. `TotalProjection` handles overflowing quotients directly:
the clamped endpoint satisfies the relevant variational inequality. Short
or zero directions are treated geometrically, so division by zero does not
create a proof precondition.

## Lower inequality and small coordinates

Each candidate reconstructs a pair of feasible convex-hull points from its
clamped parameters. A rounded triangular cap can differ from the exact cap;
the proof repairs the second parameter with `min(v,1-u)` in real arithmetic.
`ReconstructionIEEE`, `CandidateLower`, and `BCLower` follow the actual
subtractions and FMAs and bound their deviations from these feasible points.
This does not require the computed projection parameters to be accurate.

The resulting conservative bound is

```
d - sqrt(q) ≤ 120 rho L
```

in the large-coordinate regime `L ≥ H/64`. The actual stored squared norm is
finite and nonnegative. The bound is preserved by candidate selection,
reversal, weight remapping, and the triangle folds. `EvaluateLower.large_lower`
proves it for all shape pairings from input admissibility alone.

For `L ≤ H/64`, the same candidate magnitude and reconstruction estimates,
applied at scale `H/64`, prove `|sqrt(q)-d| ≤ H` directly.
`EvaluateLower.small_accuracy` covers every pairing. This case removes the
need for relative-error arguments at arbitrarily small input scales.

## Projection and determinant estimates

For a clamped scalar projection, the exact variational inequality makes
parameter error enter as a squared residual loss. `Projection` and
`ReducedProjection` establish this geometrically. Concrete dot products,
quotients, reciprocal products, and FMAs then supply the coefficient errors.
The weighted dot bounds use the coordinate geometry, including cancellation
and the operation order; they do not assume associativity of floating-point
arithmetic. The principal relative coefficients are 7.02 for a reduced solve,
7.22 for a face's second solve, and 8.38 for a segment's second solve.
Absolute terms are retained and absorbed using explicit format inequalities.

The compensated determinant proof does not import an unproved relative-error
theorem. For `z = ab-cd`, it derives

```
|computed-z| ≤ (2 rho + rho²)|z| + rho²(1+rho)|cd| + 2 eta.
```

`DeterminantFinite`, `WordDeterminantVector`, and `OrdinaryCross` connect these
bounds to the actual cross-product words and establish all required ranges.
The joint cross-vector perturbations have coefficients 3.17 and 3.60 for
ordinary and compensated normals, respectively. The latter includes the
second-order product term above.

In a thick triangle, the exact normal magnitude satisfies
`N ≥ 16 rho ||E|| D` and `N ≥ h²`. Its normalized error is then at most
`2.037 rho + 4 h²`. The actual clamped affine crossing parameter yields plane
height at most `8.4 rho D + h`. In the complementary thin case, exact triangle
geometry gives an AC or BC witness within the corresponding thickness bound.
Short bases and zero normals have their own direct geometric alternatives.

## Covering the actual candidates

The proof follows the candidates that the implementation really computes.
`KernelCoverage` converts exact projection geometry into an interior-candidate
or boundary-witness alternative. `FaceBudget` combines both actual face solves,
rounded capping, and stored-norm evaluation. `WordGeometryTransfer` and
`ComputedBCTransfer` account for differences between common rounded geometry,
independently anchored edges, and the computed BC subtraction/addition.

`SegmentUpper` proves segment–segment bounds for arbitrary feasible witnesses,
including all degenerate directions. `PointTriangleUpper` proves both
point–triangle orders, including the implementation's distinct AC/BC dot
operand orders. Its large-coordinate upper budget is `112 rho L + 7 h`.

For a compensated face, `AccurateFaceBoundary` proves one of two statements:
the actual face score is at most `d + 21 rho D + 5 h`, or there is an exact
original AC/BC boundary witness with norm at most `d + 18.01 rho D + 5 h`.
That boundary witness is passed to the actual segment kernel included in the
parent selection. It is not substituted for an uncomputed candidate.

`GeometryFeatures` supplies exact feature coverage. For positive distance,
supporting planes give a vertex/face or edge/edge feature. For intersecting
simplexes, sparse convex representations give a contained vertex or a
segment/triangle crossing. These statements include repeated vertices and
lower-dimensional hulls. `PositiveFeatureUpper`, `CrossingUpper`, `CrossingFinal`, and
`TriangleUpper` connect those witnesses to the actual candidate list, while
`UpperSelection` proves that its nested comparisons and folds retain the
upper bound. The all-pairings large-coordinate upper envelope is

```
sqrt(q) ≤ d + 36.4 rho D + 32 h.
```

The scalar envelopes used along the way are monotone and one-sided Lipschitz.
Their radical inequalities and underflow allowances are proved in Lean,
including the bounds used for thin and thick crossing branches.

## Final assembly

For both formats, `32 h ≤ H`. Since `D = 3.5 L`,

```
36.4 rho D = 127.4 rho L ≤ 128 rho L = 64 eps(T) L.
120 rho L ≤ 128 rho L.
```

The lower and upper inequalities therefore give the desired absolute error
in the large regime, and the small-regime result already fits the bound.
`AccuracyAssembly.of_upper` performs this combination. `FinalClaim4` dispatches
all nine ordered shape pairs and specializes the result to binary32 and
binary64. No implementation-level certificates are premises of these final
theorems.

## Verification scope

Lean checks the universal theorem about the explicit IEEE-word program, with
only its standard logical axioms. It does not invoke the Julia implementation
during the proof. The transcription includes IEEE exceptional values and all
candidate-selection code, and 42 bit-for-bit Julia fixtures check its regression
behavior. A verified translation from Julia source is outside this repository;
source correspondence is established by review and those tests. The theorem
uses the real square root and does not assert a separately rounded-square-root
variant or a complete proof of claim 5.
