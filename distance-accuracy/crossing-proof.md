# Crossing coverage used in the checked proof

This note describes the crossing argument implemented in `CrossingUpper.lean`.
It supplements the earlier derivation in `proof.md`: an intersection of the
original simplexes does **not** imply an intersection after rounding their
coordinate differences.

Write `ρ` for unit roundoff, `η` for the least positive subnormal, `h=η^(1/4)`,
`D=3.5 L`, and `S=ρD`. This argument is for the large-coordinate regime
`L ≥ floatmin(T)^(1/4)/64`; the small regime has a separate proof. All words
below are the actual IEEE results, interpreted as exact real numbers.

Let `E=fl(B−A)`, `F=fl(C−A)`, `P=fl(P₁−P₀)`, and `R=fl(A−P₀)`.
An original segment/triangle intersection gives feasible parameters `s,u,v`
with `s∈[0,1]`, `u,v≥0`, `u+v≤1`. The actual common residual obeys

    ‖R − sP + uE + vF‖ ≤ 3S.

This is a proved forward-error result for the four subtractions, not an
assumption that the rounded geometry intersects (`intersection_common`).
Let `N=E×F` denote the exact cross product of the rounded edges.

If `‖E‖≤h`, `‖N‖≤16ρ‖E‖D`, or `‖N‖≤h²`, a feasible point on AC or BC is
within `16S+h` of the common triangle witness. For a nonshort base this
follows by projecting the triangle onto its base line and using its altitude
`‖N‖/‖E‖`; the short-base case instead uses distance at most `‖E‖/2`.
Consequently the segment has a common edge witness of norm at most `19S+h`.
No normal division occurs in the short-base case.

Otherwise `N≠0`. Cauchy–Schwarz and `N⊥E,F` bound the plane height of the
common segment witness by `3S`. An elementary affine fact gives a complete
case split: either the plane-height numerator has a root on the common
segment, or one of its endpoints has height at most `3S`. This follows
because a real affine function without an interval root has a constant sign
and its smallest absolute value occurs at an endpoint.

In the root case, the proved IEEE crossing calculation produces a clamped
parameter and stored affine origin `Q` with plane height at most `8.4S+h`.
Its displacement from the common segment point is at most `S+η`. Orthogonal
projection of `Q` onto the triangle's plane has unrestricted affine
barycentric coordinates and residual norm equal to that plane height.
If this projection lies outside the triangle, interpolate it with the
original feasible common witness. The first point on the triangle boundary
is a common segment/edge witness. Convexity of the Euclidean norm preserves
the bound, including the displacement from `Q` to the common segment.

If the projection is feasible, apply the actual face kernel. Its proved
candidate-or-edge envelope is, with `z=d/S`,

    face score's square root ≤ S (V(z)+4.532) + 5h,
    or common face-edge residual ≤ S (V(z)+0.002) + 5h,

where `V(z)=hypot(J(3.60,z),7.22)` and
`J(c,z)=hypot(z+c,7.02)+c`. These alternatives use the actual quotient,
clamping, reciprocal, FMA and squared-norm evaluation operations. The
functions are nondecreasing and 1-Lipschitz for nonnegative arguments, so
the `h` in the plane-height bound costs only one further `h`. The root path
therefore supplies a face score bounded by `S(V(8.4)+4.54)+6h`, or a common
edge witness bounded by `S(V(8.4)+1.01)+7h`.

For the missed-root case, use the corresponding endpoint face candidate.
Its actual anchor `fl(A−Pᵢ)` differs from the common endpoint by at most
`3S`, so its plane height is at most `6S`. The same projection/interpolation
argument gives an endpoint face score bounded by `S(V(6)+4.54)+5h`, or a
common segment/edge witness bounded by `S(V(6)+3.002)+5h`.

The checked rational inequalities

    V(8.4)+4.54 < 24,       V(6)+4.54 < 24,
    V(8.4)+1.01 < 20.2,     V(6)+3.002 < 20.2

combine all cases: an actual crossing or endpoint-face candidate has score
square root at most `24S+7h`, or a common boundary witness has norm at most
`20.2S+7h`.

Finally, transferring any of the three common edges to the actual
segment/segment input differences costs at most `4S`, in either operand
order. The sharp segment kernel then gives

    S F(24.2) + 3.55S + 13h < 36.4S + 13h,

where `F(z)=hypot(J(3.17,z),8.38)`. This proves crossing coverage by actual
candidates, preserving the fixed operand order used by triangle/triangle
selection. `CrossingFinal.large_cover` is the checked original-input
statement. Its only assumptions are input admissibility, the large-regime
inequality, and zero exact segment/triangle distance. Its axiom report lists
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
