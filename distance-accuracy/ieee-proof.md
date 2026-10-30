# Claim 4: proof corresponding to the IEEE Lean development

This is the natural-language companion to `FinalClaim4.lean`. It follows the
implemented formal proof, rather than the earlier argument in `proof.md`.
The result concerns **constant 64**, not the original constant 8.

Let the coordinates be finite binary32 or binary64 values, interpreted as
exact real numbers. Let their absolute values be bounded by `L`, where

\[
0\le L<\operatorname{maxFinite}^{1/4}/4.
\]

Let `q` be the squared-distance word returned by `IEEEAlgorithm.evaluate`,
interpreted as a real number, and let `d` be the distance between the convex
hulls of the original vertices. We prove

\[
|\sqrt q-d|\le128\rho L+H,
\qquad \rho=\operatorname{eps}(T)/2,
\quad H=\operatorname{minNormal}^{1/4}.
\]

The square root here is the real square root. IEEE operations in the
algorithm use round-to-nearest, ties-to-even, with gradual underflow and
correctly rounded FMA. The theorem is about all words satisfying the input
condition, including degenerate simplices. It does not require a nonzero
edge, a nonzero determinant, or finite quotients.

## 1. What is formalized

`IEEEAlgorithm.lean` transcribes the arithmetic, comparisons, clamps, candidate
selection, and ordered dispatch of the Julia methods. `Geometry.lean` defines
convex-hull distance independently of that algorithm. The FP dependency gives
word-level IEEE semantics; successful decoding is required before a word is
used as a real value.

The theorem proves the transcription correct. The connection to the Julia
source is a source correspondence, supported by source hashes and bitwise
fixtures; it is not a formal verification of the Julia compiler or hardware.
The implementation comments are not hypotheses.

## 2. Elementary floating-point facts

Write `η` for the least positive subnormal and `h = η^(1/4)`. For each rounded
finite operation the proof derives the mixed error bound

\[
|\operatorname{fl}(z)-z|\le\rho|z|+\eta/2.
\]

Every use is accompanied by an overflow-range proof. This is especially
important for dot products of cross products, whose intermediates have
fourth-degree dependence on the coordinate scale. `FormatRange.lean` derives
these range bounds from the stated input limit; no intermediate range is
assumed by the final theorem.

Clamping is treated on words before converting to reals. The actual
`clamp01nan` produces a finite parameter in `[0,1]`, even for NaN or infinite
input. `TotalProjection.lean` handles overflowed quotients and zero
denominators explicitly. It does not apply a relative-error division model
to infinity.

For either supported format, exact arithmetic proves

\[
32h\le H.
\]

In the large-coordinate regime `L ≥ H/64`, it also proves
`η ≤ ρ²L`, `2√η ≤ ρL`, and the stronger absorption inequalities needed by the
cross-product estimates. These are format-specific numerical theorems,
not asymptotic small-error assertions.

## 3. Common rounded geometry

Set

\[
D=\tfrac72 L,\qquad S=\rho D.
\]

The independently rounded edge differences and origins have norm at most
`D`; the required component bounds are `D/√3`. Segment residuals with any
feasible pair of parameters also have norm at most `D`. Analogous bounds
hold for the face residuals, their endpoint shifts, and the actual crossing
origin after FMA. They are derived from the original coordinates in
`SegmentCoordinates`, `FaceCoordinates`, `CrossingCoordinates`, and
`BCUpperGeometry`.

Each original-coordinate subtraction changes its exact vector by at most
`S`. Consequently:

* an original segment/segment witness transfers to its common rounded
  geometry with error at most `3S`;
* a point/triangle witness transfers in either direction with error at most
  `2S`, because its two nonbase barycentric weights sum to at most one;
* a common triangle-boundary witness transfers to an actual edge-kernel
  geometry with error at most `4S`, in either ordered orientation.

The last bound uses the shared coordinate differences and their cycle
cancellations. Adding independent worst-case bounds would lose the required
constant. `WordGeometryTransfer` and `BoundaryEdgeUpper` prove these estimates
for the actual subtraction words, including independently rounded anchors.

## 4. Local numerical envelopes

Define, for nonnegative `z`,

\[
J_c(z)=\sqrt{(z+c)^2+7.02^2}+c,\quad
F(z)=\sqrt{J_{3.17}(z)^2+8.38^2},\quad
V(z)=\sqrt{J_{3.60}(z)^2+7.22^2}.
\]

These functions are increasing and satisfy `F(z+a) ≤ F(z)+a` and
`V(z+a) ≤ V(z)+a` for `a ≥ 0`. Thus absolute underflow allowances pass through
the envelopes without amplification.

The constants come from operation-level proofs. The ordinary pair of cross
products has joint error at most `3.17ρ‖E‖D`; the pair using the compensated
normal has joint error at most `3.60ρ‖E‖D`. The latter is proved directly from
IEEE multiply and FMA semantics, without assuming an external compensated
arithmetic theorem. Weighted dot-product estimates and the clamped
projection variational inequality yield the `7.02`, `7.22`, and `8.38`
squared-loss terms. Keeping the squared loss, instead of adding parameter
errors linearly, is essential.

The resulting segment theorem is particularly useful: if any feasible
witness in the common rounded segment geometry has norm at most `b`, the
actual selected squared-distance word satisfies

\[
\sqrt q\le S F(b/S)+3.55S+6h.                 \tag{1}
\]

`SegmentKernelUpper.kernel_upper` proves (1). A short first edge is handled
by an endpoint candidate. Otherwise, the reduced first solve is followed by
the second solve. If its unrestricted comparison point leaves the segment,
convexity supplies a boundary witness and an endpoint candidate. Every
candidate participating in the minimum is proved finite.

For faces, the corresponding alternative is an actual face-score bound or
a feasible AC/BC boundary witness. The short-base case supplies a boundary
witness directly. `FaceBudget` keeps the sharper `V` envelope, while
`AccurateFaceBoundary` gives the simpler original-coordinate alternative

\[
\sqrt{q_{face}}\le d+21S+5h
\quad\hbox{or}\quad
\text{an original boundary witness of norm}\le d+18.01S+5h.       \tag{2}
\]

Here `d` can be the exact point/triangle distance. Combining the second
alternative with the `3S` transfer and (1) gives an actual edge score at
most `d+36S+11h`. This works in both orientations, using original witnesses;
it does not assume that swapping floating-point operands preserves a score.

## 5. Intersections and nearly singular triangles

The crossing analysis must not assume that an original intersection remains
an intersection after the edge subtractions are rounded. An original
intersection first gives a feasible common witness of norm at most `3S`.

If the base is short, the exact common normal is sufficiently small relative
to the base, or the normal is below its absolute underflow threshold, the
thin-triangle lemma replaces that witness by an edge witness. The distance
allowance is at most `16S+h`, so the resulting common boundary witness has
norm at most `19S+h`.

Otherwise the normal is thick. There are two possibilities:

1. The common segment meets the common plane. The actual rounded crossing
   solve produces a point whose plane-height bound is `8.4S+h`. The face
   envelope yields either a score or a boundary witness.
2. It does not meet that plane. For the affine signed plane function,
   a small value somewhere on the segment implies a comparably small value
   at one of its endpoints. The endpoint face alternative therefore covers
   this case, including the change of rounded anchor at the second endpoint.

After accounting for these anchors and the absolute allowances, all cases
supply either an actual crossing/endpoint-face score at most `24S+7h`, or a
common boundary witness of norm at most `20.2S+7h`.

The `4S` boundary transfer and (1) then give an actual edge score at most

\[
S F(24.2)+3.55S+13h <36.4S+13h.             \tag{3}
\]

All radical comparisons are proved with rational inequalities and squaring
nonnegative bounds. For example the relevant bounds include
`V(8.4) ≤ 18.935`, `V(6) ≤ 17.094`, and `F(24.2)+3.55 < 36.4`.
They are not numerical experiments.

## 6. Geometric coverage and selection

The exact convex-hull geometry supplies the required candidates:

* for positive distance, a closest feature pair is vertex/face or edge/edge;
* for an intersection, an edge of one simplex intersects the other simplex.

`GeometryFeatures` proves these assertions using sparse convex
representations and a supporting plane, and handles lower-dimensional and
repeated-vertex cases. No general-position hypothesis is present.

Equation (2) covers vertex/face pairs; (1) covers edge/edge pairs; (3) covers
intersections. The actual folds and comparisons select a candidate no larger
than the useful one, because all candidates are finite. For all triangle
pairings this yields the deliberately uniform bound

\[
\sqrt q-d\le36.4S+32h=127.4\rho L+32h.      \tag{4}
\]

The point and standalone segment pairings have separate, smaller bounds.

## 7. Lower bound and small coordinates

The lower proof reconstructs feasible comparison points from the actual
clamped parameters and bounds the actual residual and stored squared norm.
The slight excess possible in the computed face weight sum is handled in
that reconstruction; it is not silently treated as exact feasibility.
`EvaluateLower.large_lower` proves, for every pairing,

\[
d-\sqrt q\le120\rho L.                     \tag{5}
\]

It also proves finite, nonnegative output. This proof is independent of the
upper-bound feature coverage.

If `L ≤ H/64`, perform the range and magnitude analysis at the larger scale
`H/64`. This changes the bounds, not the actual input words or execution.
The reconstruction estimate gives `√q ≤ 10H/64`; together with the lower
estimate and nonnegative distance, this proves `|√q-d| ≤ H` directly.
This handles all very small coordinates without dividing by a small edge.

## 8. Final inequality

For `L ≥ H/64`, combine (4), (5), and `32h ≤ H`. Since
`36.4 × 3.5 = 127.4 < 128` and `120 < 128`, both sides are bounded by
`128ρL+H`. For `L ≤ H/64`, use the preceding small-coordinate theorem.
Since `2ρ = eps(T)`, the result is exactly the requested constant-64 version
of claim 4.

The public theorem is `DistanceAccuracy.finalClaim4`, with specializations
`DistanceAccuracy.finalClaim4_binary32` and
`DistanceAccuracy.finalClaim4_binary64`. Its only premise, after selecting
a format, is `Geometry.admissible`; it assumes no numerical certificates,
branch accuracy bounds, or nondegeneracy conditions.
