# Checked lower bound and small-coordinate case

This note describes the results proved in `DistanceAccuracy/EvaluateLower.lean`.
It does not assert that the large-coordinate upper bound has been completed.

Let ρ be the IEEE unit roundoff, η the least positive subnormal, and
H = floatmin(T)^(1/4). Thus the requested 64·eps(T)·L term is 128ρL.
All arithmetic below concerns exact real values decoded from IEEE words.

## Local calculations

The clamping routine produces a finite value in [0,1], even when its input is
NaN or infinity. Consequently the lower-bound argument needs no accuracy or
finiteness assertion for the normal, reciprocal, determinant, or quotient
calculations preceding a clamp. A rounded complement of u in [0,1] remains
in [0,1]. Its mixed rounding bound implies

    |fl(1-u) - (1-u)| ≤ 3ρ/2

because η ≤ ρ for both supported formats. Therefore the two face weights are
nonnegative, at most one individually, and their exact sum is at most
1 + 3ρ/2. This bound concerns the exact sum, not a floating-point summation.

For L ≥ H/64, the exact format parameters imply η ≤ ρ²L and
2√η ≤ ρL. The local rounded affine calculations then have these component
error bounds:

* segment/segment interior and endpoint: 15ρL;
* point/triangle BC boundary: 21ρL;
* face and segment/face crossing: 23ρL.

These are proved from the mixed operation error
|fl(z)-z| ≤ ρ|z| + η/2, with the actual operation order. All finite outputs
and no-overflow premises are derived from input coordinate bounds. The proof
uses the slightly larger uniform allowance 29ρL, including the BC complement
embedding. It does not depend on the sharper reconstruction claim 5.

The actual squared-norm multiply/FMA/FMA schedule produces a finite,
nonnegative decoded q and satisfies, for R = ‖r‖,

    |q-R²| ≤ 3ρ(1+ρ)²R² + 2η.

This implies |√q-R| ≤ 2ρR + 2√η. These statements include gradual underflow.

## From a local candidate to the exact distance

Every candidate uses vertices belonging to the two original convex hulls.
Changing a candidate's returned weight encoding does not change q, so these
weight-record updates need no accuracy argument for claim 4.

Write the local exact affine points as

    X = A + u(B-A) + v(C-A),
    Y = D + s(E-D) + t(F-D).

Repeated vertices include points and segments in this notation. Repair the
weights by replacing v with min(v,1-u), and likewise for t. The repaired
points X′ and Y′ belong to the original hulls. Each repair moves its point by
at most 9ρL: the weight change is at most 3ρ/2, and an edge has norm at most
6L using the elementary bound ‖z‖₂ ≤ 3 maxᵢ|zᵢ|.

The uniform component reconstruction allowance gives

    ‖r-(Y-X)‖ ≤ 87ρL.

The exact distance d between the original hulls is at most ‖Y′-X′‖, hence

    d ≤ ‖r‖ + 105ρL.

Each affine point has coordinates at most (1+3ρ)L in absolute value.
Combining this with reconstruction gives ‖r‖ ≤ (6+105ρ)L ≤ 7L, since
ρ ≤ 1/1024. Therefore squared-norm evaluation costs at most

    2ρ‖r‖ + 2√η ≤ 15ρL.

It follows that every local candidate satisfies

    d - √q ≤ 120ρL < 128ρL.

The actual selection routine always returns one of its candidates. Reversal
and weight-record updates preserve q. The checked selection lemmas cover all
nested folds in triangle/triangle and segment/triangle evaluation. Thus this
bound applies to every simplex pairing without further assumptions.

## Small coordinates and the final lower bound

The same local argument also proves the magnitude reserve √q ≤ 10L.
To handle L ≤ H/64, apply it at the larger analysis scale L′ = H/64. The
input words and evaluated result do not change, and this analysis scale is
below the allowed coordinate ceiling for both formats. It gives

    d - √q ≤ 120ρH/64 ≤ H,
    √q - d ≤ √q ≤ 10H/64 ≤ H.

Hence the full two-sided error is at most H in this regime. For larger L,
the lower estimate above gives the requested lower side with room to spare.
`EvaluateLower.lower` proves the lower side for all admissible inputs;
`EvaluateLower.small_accuracy` proves both sides for L ≤ H/64.

`LowerVerification.lean` checks the dependency lists of these end-to-end
results. They use only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`, with no custom axioms, `sorry`, or `native_decide`.
