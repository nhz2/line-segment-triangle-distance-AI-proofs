> **Superseded historical draft.** This argument contains a gap: an original
> intersection need not survive the independently rounded coordinate changes.
> Use [ieee-proof.md](ieee-proof.md) for the corrected proof corresponding to
> the completed Lean theorem. The missing-root endpoint case is also explained
> in [crossing-proof.md](crossing-proof.md). This file is retained for provenance,
> including the hashes of the analyzed Julia source.

# Claim 4: distance accuracy with constant 64

## Statement and arithmetic assumptions

This proof concerns the implementation currently in `src/distances.jl`, for
Float32 and Float64, with round-to-nearest/ties-to-even, correctly rounded
FMA, and gradual underflow. The input coordinates are finite and satisfy

    L = maximum absolute input coordinate < floatmax(T)^(1/4)/4.

Let d be the exact distance and q the returned squared distance. The full
claim established by this write-up is

    |sqrt(q) - d| <= 64 eps(T) L + floatmin(T)^(1/4).

The main sections prove the upper side; Appendix A proves the lower side
and handles small coordinates. In particular, we prove

    sqrt(q) - d <= 64 eps(T) L + floatmin(T)^(1/4).

The bound also holds when sqrt(q) is rounded to T. Together with the lower bound in Appendix A, this proves the proposed
two-sided bound. It does not reinstate the disproved constant 8.

All inequalities and the decimal constants below denote exact real numbers;
finite decimal constants are rational numbers. Put

    rho=eps(T)/2, eta=nextfloat(zero(T)),
    H=floatmin(T)^(1/4), h=eta^(1/4), D=2sqrt(3)L.

D bounds every distance between original vertices. The previously established
small-coordinate argument covers L<=H/64, even without optimality of the
selected candidate. Hence assume L>H/64 below.

The only imported numerical theorem is the 2rho relative-error bound for
Kahan's compensated 2-by-2 determinant in arithmetic without underflow or
overflow. The implementation has exactly that algorithm. See Jeannerod,
Louvet, and Muller, *Further analysis of Kahan's algorithm for the accurate
computation of 2x2 determinants*, Mathematics of Computation 82 (2013),
2245-2264, Theorem 1.2. The result and algorithm are also stated in (1.3a) of
https://perso.ens-lyon.fr/jean-michel.muller/MathsComp2015.pdf . The extension
needed for gradual underflow is proved below.

## 1. A projection lemma: errors enter the squared distance

For a>0, define phi(t)=a t^2+2bt+c on an interval I contained in [0,1].
Suppose t minimizes a perturbed quadratic with coefficients ahat>=0,bhat,
and let t* minimize phi. At the computed point define

    e=(ahat-a)t+(bhat-b)=e_rel+e_abs.

The variational inequality for the perturbed minimizer gives

    phi(t)-phi(t*)
      <=2|e_rel||t-t*|-a|t-t*|^2+2|e_abs||t-t*|
      <=e_rel^2/a+2|e_abs|.                         (1)

This remains valid when ahat=0: t need only minimize the resulting linear
function. If the true direction vector is zero, the true objective is
constant and no estimate is needed.

A rounded quotient followed by clamp can be treated in (1) by a perturbation
of bhat of magnitude at most rho*ahat*t/(1-rho), apart from an absolute
underflow term. If rounding does not change the clamped endpoint, choose
that extra perturbation to be zero. Otherwise the quotient lies at, or
inside, the clamping interval and the relative rounding bound gives the
stated estimate. The same observation applies to a rounded FMA producing
an unclamped parameter. It applies to any upper endpoint of I, not only 1.

In particular, clamping does not force us to add a full first-order
parameter error to the distance: (1) bounds an increase in squared distance.

## 2. Floating-point estimates used in the proof

Write

    W(a,b)=3|a1 b1|+2|a2 b2|+|a3 b3|.

Direct expansion of the three operations in dot3 gives

    |dot3(a,b)-a dot b| <=rho(1+rho)^2 W(a,b)+2eta.   (2)

Let kappa=sqrt(14/3) and lambda=5/sqrt(6). For vectors whose components
are bounded by 2L, Cauchy-Schwarz gives

    W(a,b)/||a|| <= kappa D.

Also

    W(a,a)/||a|| <= lambda D.                       (3)

To verify the second inequality, maximize
(3x+2y+z)/sqrt(x+y+z) over 0<=x,y,z<=(2L)^2. For each variable separately,
any interior stationary point is a minimum, so a maximum is at a cube
vertex. The largest value is (2L)*5/sqrt(2)=lambda D.

The ordinary cross product satisfies

    ||cross3(a,b)-a cross b||
      <=rho ||a cross b||
        +rho(1+rho) sqrt((a3 b2)^2+(a1 b3)^2+(a2 b1)^2)
        +2eta.                                    (4)

If ||a||=A and the components of b are bounded by 2L, the square-root term
is at most 2LA=AD/sqrt(3). Thus (4) divided by A has first-order bound
rho(w+D/sqrt(3)), where w=||a cross b||/A<=D.

For the compensated cross product,

    ||cross3_accurate(a,b)-a cross b||
      <=(2rho+rho^2)||a cross b||+6eta.             (5)

Here is the underflow extension of the imported determinant theorem.
For one component let z=pq-uv, w=fl(uv), epsilon=w-uv,
e=fl(epsilon), f=fl(z-epsilon), and output=fl(f+e).
The product residual is exact whenever representable; otherwise its error
is at most eta/2. This follows directly by splitting the product significand
into its rounded high part and residual low part. If the product itself
underflows, |epsilon|<=eta/2, giving the same residual-error bound.

If |epsilon|<=2floatmin(T), use rho|epsilon|<=eta in the elementary rounding
bounds for f and the final addition. They give

    |output-z| <=(2rho+rho^2)|z|+3eta.

If f is in the underflow range, its absolute error is at most eta/2; together
with the residual error, the final-addition bound gives at most rho|z|+2eta.
In the remaining case the first three operations agree with unbounded-
exponent arithmetic, so the imported 2rho theorem applies. A difference
in the final underflow rounding costs at most eta. Combining the components
proves (5).

### Explicit allowances for higher-order and absolute errors

Here are explicit multiplicative bounds; no unspecified operation-count
estimate is needed. Put U=1+rho, V=1/(1-rho), B=1+16rho and K=BD.
Absolute errors are accounted for separately below. The auxiliary geometry
bounds used in Section 5 give component bounds 2LB for differences and
norm bounds K for separations of feasible points. The following envelopes
bound the relative part of each row, after division by rho K:

| Row | Envelope |
|---|---|
| direct projection | (kappa+lambda+1) U^2 V |
| second/endpoint projection | (2kappa+lambda+2) U^3 V |
| face parameter | (kappa+lambda+3) U^3 V^2 |
| reduced projection | 7 U^2 V (1+4rho) |
| ordinary cross perturbations | (2+2/sqrt(3)) U |
| face cross perturbations | (3+1/sqrt(3)) U |
| crossing plane height | (2kappa+4) U^4 V |
| evaluation | (7/2) U^4 V^2 |
| face evaluation | 4 U^4 V^2 |

To derive the first two envelopes, absorb quotient rounding into the
quadratic coefficient: aeff=ahat/(1+delta), |delta|<=rho. The effective
coefficient error at t is bounded by

    V |ahat-a| t + rho V a t.

For the direct numerator use (2). For a numerator fma(t,bhat,dhat), use

    |numerator-(tb+d)|
      <= U(|bhat-b|t+|dhat-d|)+rho|tb+d|,
    |tb+d| <= A K.

The same bound applies to fl(bhat-ehat) at an endpoint. Substitution of
(2)-(3) gives the first two envelopes.

For the face solve, let a=E dot E, b=E dot F, d=E dot R. Ignoring only
the separately budgeted absolute errors, write the reciprocal, the two
products and final FMA with rounding factors 1+delta_i, 1+delta_c,
1+delta_m, 1+delta_q. Its unclamped result is exactly

    -[(d+Delta_d)(1+delta_m)
        +v(b+Delta_b)(1+delta_c)]
      *(1+delta_i)*(1+delta_q)/(a+Delta_a).

Consequently it is a minimizer for the quadratic with coefficients

    aeff=(a+Delta_a)/[(1+delta_i)(1+delta_q)],
    beff=(d+Delta_d)(1+delta_m)+v(b+Delta_b)(1+delta_c).

This remains the correct representation after clamping to [0,1-v]. At
its minimizer u, the relative gradient error, divided by A*rho*K, is at most

    (kappa U^3+1)(1+v)
       +[lambda U^2 V^2+(2-rho)V^2]u.

Use u+v<=1. The maximum occurs at (u,v)=(1,0), rather than (0,1), and
is bounded by (kappa+lambda+3)U^3 V^2. This derivation does not assume the
unclamped parameter lies inside the interval.

For the reduced projection, (2) with W(a,b)<=3||a||||b|| gives
3 U^2 rho ||ktilde||+(3 U^2 V+V)rho ||ntilde||. The cross bounds give
||ktilde||/A, ||ntilde||/A <=K(1+4rho), apart from absolute errors. This
proves its envelope. Equations (4)-(5) give the two cross envelopes directly.
For the plane height, the explicit coefficient before enlargement is

    (2+rho)+1+2kappa U^4+V <=(2kappa+4)U^4 V.

The terms are respectively the normal error, AX rounding, the two dots,
and quotient rounding. Finally,

    sqrt(dot3(r,r)) <= ||r||*(1+(3/2)rho U^2)+sqrt(2eta)

and each affine rounding has norm error at most rho times the norm of its
exact result, plus sqrt(3)eta/2. Two such roundings give the evaluation
envelope. The rounded weight cap adds at most rho K/2, giving the last row.

Every envelope in the table, including B, is bounded by its first-order
coefficient times

    M=(1+16rho) U^4 V^2 (1+4rho).

All first-order coefficients are below 10. Direct rational arithmetic at
0<=rho<=2^-24 gives

    10(M-1) <= 2^16 rho.

For example expand the numerator after multiplying by (1-rho)^2; each
positive higher-degree term is bounded using rho<=2^-24. This is also
checked by the accompanying script. Thus the relative remainder is at
most 2^16 rho^2 D.

Here is the absolute-error budget. In a direct projection, the two dot
errors contribute at most 2eta each to the effective gradient, and quotient
underflow adds at most eta*ahat/2. Multiplying the coefficient error by
t<=1 and applying the factors V above gives a squared-distance loss at
most 12eta+4eta*a, and hence less than 64eta(1+a). A second-solve numerator
has two dot errors and one scalar rounding error; its larger budget is
still less than 64eta(1+a). In the face solve the reciprocal is normal
and finite when A>h. The absolute errors in its two products and FMA,
converted back to quadratic coefficients by aeff, contribute less than
4eta*a; the dot errors contribute less than 8eta. Thus its total is also
below 64eta(1+a). By (1), these losses add at most
8sqrt(eta)(1+A) to distance.

For the reduced projection, the same direct-projection budget, divided
by A^2, splits into 12eta/A^2 and at most
4eta*||ntilde||^2/A^2. The latter contributes less than
3sqrt(eta)(1+D); retain the former separately. Absolute cross errors,
divided by A>h, are at most 8eta/A<8sqrt(eta). Their contribution to the
relative gradient envelope is smaller still. For the plane estimate,
||E cross F||>h^2 implies that the absolute normal errors (at most 6eta)
and the two dot errors (at most 2eta each), after normalization, contribute
less than 16sqrt(eta)(1+D), including the rounding factors above.
Coordinate differences and affine evaluations each add at most
sqrt(3)eta/2; the norm evaluation adds sqrt(2eta). These bounds, including
the at most eight differences in the change-of-anchor estimates, total
less than 128sqrt(eta)(1+D) for every row. Absolute contributions to the
auxiliary geometry bounds are included in this budget rather than in B.

Thus the uniform remainder for a row is bounded by

    R=2^16 rho^2 D+128sqrt(eta)(1+D) <0.01rho D.      (6)

This last inequality is uniform, including near the lower end of the range.
For Float32, using D>sqrt(3)H/32 and sqrt(3)>17/10 gives

    R/(rho D) < 1/256 + 10/2176 + 2^(-43) < 1/100.

The corresponding three terms are smaller for Float64.

The exception is the reduced solve using n=a cross b and k=a cross R,
whose squared-distance loss from (1) includes at most 12eta/||a||^2 after
normalization. When ||a||>h this adds less than 4h to its distance bound.
When ||a||<=h we use an endpoint/edge instead, as described below.

### Constants, all including (6)

The following constants multiply rho D, unless indicated otherwise.

| Quantity | First-order coefficient | Bound used |
|---|---:|---:|
| ordinary point-to-segment projection, before evaluation | kappa+lambda+1 | 5.22 |
| segment interior second solve or P1 endpoint solve | 2kappa+lambda+2 | 8.38 |
| face solve for u on [0,1-v] | kappa+lambda+3 | 7.22 |
| reduced n,k projection, after division by A | 7 | 7.02, plus 4h |
| combined n,k cross perturbation, ordinary normal | 2+2/sqrt(3) | 3.17 |
| combined cross perturbation, accurate or ordinary face normal | 3+1/sqrt(3) | 3.60 |
| crossing point's plane height, including AX rounding | 2kappa+4 | 8.34 |
| evaluation: at most two affine roundings plus sqrt(dot3) | 7/2 | 3.53 |
| face evaluation, also allowing the final weight cap | 4 | 4.03 |

Every upward rounding in this table exceeds 0.01.

For clarity, the projection rows follow from (1) as follows. For a direction
E with length A, the relative part of the effective gradient perturbation
for a direct dot quotient, divided by A, is bounded to first order by

    rho[W(E,R)/A + t W(E,E)/A + t A].

This gives the first row. A numerator fl(b-e) or fma(t,b,d) contributes two
dot errors and one additional rounding of an exact scalar product with a
separation vector of length at most D. This gives 2kappa+lambda+2.

For the face solve, write v for the initially clamped v and consider the
virtual output ubar=clamp(qhat,0,1-v), where qhat is the actual unclamped
floating-point expression used for u. The reciprocal, products, and FMA
give the first-order gradient-error bound

    rho D[(kappa+1)(1+v)+(lambda+2)ubar].

Because ubar+v<=1 and lambda+2>kappa+1, this is at most
(kappa+lambda+3)rho D. Applying (1) proves the face row. In particular, the
bound is for the shortened interval [0,1-v], not the larger square.

For the n,k projection, the unweighted version of (2) gives the physical
bound 3rho||k||+4rho||n||. Dividing by A gives 7rho D, together with the
explicit 12eta/A^2 squared loss. The two cross-perturbation rows follow
from (4)-(5), using ||n||/A,||k||/A<=D. All these bounds allow dot-product
cancellation and zero computed denominators. If the computed squared norm
is zero, clamp selects a minimizer of the corresponding perturbed linear
quadratic; (1) still applies.

Finally, sqrt(dot3(r,r)) differs upwards from ||r|| by
(3/2)rho||r|| plus the included higher-order and absolute terms. Each affine
rounding costs at most rho D to first order. The last cap changes a weight
by at most rho/2 relative to the exact cap, explaining the extra 1/2 in
the face-evaluation row.

## 3. Combining cross perturbations with the projection lemma

Let E!=0, A=||E||, n=E cross F, k=E cross R. For v in [0,1],

    ||k+v n||/A = min_u ||R+uE+vF||.

Let ntilde,ktilde be the computed cross vectors and suppose
(||ntilde-n||+||ktilde-k||)/A<=c rho D. If the true reduced minimum is at
most d, the computed reduced parameter satisfies

    min_u ||R+uE+vhat F||
      <= hypot(d+c rho D, 7.02rho D)+c rho D+4h.     (7)

Indeed the perturbed minimum is at most A(d+c rho D); apply the squared-
distance projection bound to it, and then the triangle inequality to
return from the perturbed vectors. This is not a claim that the parameter
itself is accurate when the vectors are nearly parallel.

Set, for nonnegative dimensionless z,

    J_c(z)=hypot(z+c,7.02)+c,
    F(z)=hypot(J_3.17(z),8.38),
    V(z)=hypot(J_3.60(z),7.22).                      (8)

These functions and every further function built below are nondecreasing
and 1-Lipschitz. Hence an additive geometric or underflow error propagates
with multiplier at most one. Also G(z)-z<=G(0) for any such composition G.

## 4. Exact geometric coverage of the constraints

### Segments

For fixed t, minimize ||R+tQ-sP|| over the infinite line in s. The minimizing
s(t) is affine in t. If an exact closest pair has s at an endpoint, an
endpoint candidate suffices. Otherwise, if the computed reduced t gives
s(t) outside [0,1], join it to the exact closest pair's t. At the first exit
from the interval in s, an endpoint of the first segment is reached.
Convexity of the reduced norm bounds the separation there by the bound
in (7). The endpoint projection's squared-distance loss is at most
(8.38rho D)^2. If s(t) is inside, the second solve has the same loss bound.

Thus, for the exact geometry specified by the rounded P,Q,R vectors, one
of the segment kernel's candidates has root-distance at most

    rho D F(d/(rho D)) + 3.53rho D +4h.              (9)

### A point and a triangle

Use the triangle parameter domain u>=0,v>=0,u+v<=1. Edges AC and BC are
available. If an exact closest point is on one of those edges, use it.
Otherwise its u is an unconstrained line minimizer at its v.

If the computed v gives an unconstrained u outside the triangle, join
that affine line minimizer to the exact closest point in parameter space.
The first boundary encountered is AC or BC. Convexity again gives a
boundary witness with norm bounded by (7).

If the unconstrained u is feasible, apply (1) on [0,1-v] to the virtual
ubar from the table. Its distance is at most

    rho D V(d/(rho D))+4h.                          (10)

When ubar is interior to that interval, the actual face candidate agrees
with this virtual candidate, up to the final cap-rounding allowance.
When the implementation's final cap would instead change v, ubar is on
BC and supplies an edge witness. Endpoint cases are covered in the same
way. Therefore (10) bounds either a face candidate before evaluation, or
an exact boundary witness. This is the coupled face/edge argument; it
does not add full first-order projection errors to the distance.

If A=||E||<=h, every point of the triangle is within A/2 of AC or BC, so
use the edges at an additional cost at most h/2. No accuracy of the
potentially overflowing reciprocal is assumed in this case.

## 5. Geometry represented by rounded differences

Here and below the small upward allowances include (6). A rounded difference
has norm error at most rho D to first order. These give the following
bounds, with constants multiplying rho D.

* A point/triangle face kernel represents a triangle with its two non-anchor
  vertices displaced by at most rho D, and the point displaced by at most
  rho D: its exact distance differs from the original by at most 2.02rho D.
* A segment kernel's common rounded P,Q,R represents two segments with total
  Hausdorff displacement at most 3.02rho D.
* A crossing face kernel has a common exact triangle and a shifted exact
  segment representing its rounded P,AP and its final AX FMA. Total
  Hausdorff displacement from the original pair is at most 4.02rho D.

The edge candidates may use a different anchor. The following stronger,
shared-input bounds avoid adding two independent Hausdorff bounds.

For a crossing, write eAX for the error of fma(-s,P,AP). The common exact
triangle is (A,A+E,A+F), and the exact segment is

    X'(z)=A-AP+zP-eAX.

For AB and AC, the associated segment-edge kernel uses the same P,AP and
E or F. Its exact separation differs from this common geometry by only
eAX, at most rho D to first order.

For BC, at edge weight t, the additional discrepancy is

    [fl(B-P0)+t fl(C-B)]
      -[fl(A-P0)+(1-t)fl(B-A)+t fl(C-A)].            (11)

The exact terms cancel. For one coordinate its rounding-error budget is

    |B-P0|+t|C-B|+|A-P0|+(1-t)|B-A|+t|C-A|.

At t=0 this is a triangle perimeter, at most 4L; at t=1 it is a four-edge
cycle, at most 8L. Convexity in t gives at most 8L throughout. Its vector
bound is 4rho D; adding eAX gives the bound 5.02rho D used below.

For a point-face candidate embedded as either endpoint of a segment, the
same calculation includes the endpoint subtraction. At the second endpoint
the scalar budget is

    |B-P0|+|P1-P0|+|A-P1|
      +(1-t)|B-A|+t|C-A|+t|C-B|.

Its endpoint cases are cycles of four and five edges; each has maximum
8L for coordinates in [-L,L]. (An odd five-edge cycle crosses the two
ends of the interval at most four times.) Thus the point-face boundary
witness transfers to the available endpoint projection with discrepancy
at most 4.02rho D. This covers vertex 3, which is never the first endpoint
of an ordered triangle edge. The standalone point-triangle BC candidate,
which rounds E2 and BX instead, has a smaller discrepancy and is covered
by the same bound.

## 6. Primitive bounds, including embedded vertex-face candidates

For point-face candidates with the available edge/endpoint projections,
define

    P(z)=max(V(z+2.02)+4.03,
             hypot(V(z+2.02)+4.02,8.38)+3.53).

The first term covers the face; the second covers the boundary witness,
its change of anchor, and the squared loss of the available projection.
Then the computed root-distance is at most

    d + rho D P(0) +4h,
    P(0)<24.47.                                    (12)

For segment-segment, (9) and the 3.02 input displacement give

    d + rho D [F(3.02)+3.53]+4h,
    F(3.02)+3.53<19.                               (13)

If ||P||<=h, choose a nearer endpoint: its true distance is at most d+h/2,
and the endpoint projection is covered by the same bound. Thus (13) does
not assume a nondegenerate first segment. Point-point and point-segment
are smaller instances of these bounds.

## 7. A segment crossing a triangle

Use the shifted common geometry X'(z) from Section 5. If the triangle is
degenerate, or ||E||<=h, or ||E cross F||<=h^2, use its edges. For the last
condition every triangle point is within h of AC or BC: its distance is
at most both ||E||/2 and ||E cross F||/||E||, hence at most
sqrt(||E cross F||/2). One way to verify the second bound is to project C
onto AB; on each side of that projection, the corresponding incident edge
has distance at most the height over AB. Homothety toward C reduces the
claim for interior points to points on AB.

Henceforth ||E||>h and ||E cross F||>h^2.

If the shifted common segment and triangle are disjoint, an exact closest
pair can be chosen on an endpoint/face or segment/edge. If both points
were interior, their separation would be normal to the face and the
segment would be parallel to it; sliding until a boundary preserves the
distance. Transfer that feature pair back to the original geometry.
The two transfers cost at most 8.04rho D. Equations (12)-(13) give

    root-distance <=d+[8.04+max(P(0),F(3.02)+3.53)]rho D+4h.   (14)

The bracket is below 32.52. The degenerate/small-area case has the same
bound with an additional h, using segment/edge candidates.

Now suppose the shifted common segment intersects the common triangle.
Let N0=E cross F and let Nhat be its compensated computation.

We need the following elementary affine-root fact. If affine f has a zero
on [0,1], g=f+e is affine, and s minimizes |g| on [0,1], then

    |f(s)| <=max(sup|e|, max e-min e).              (15)

If g has a zero, use f(s)=-e(s). Otherwise suppose g>0. At a zero s* of f,
g(s)<=g(s*), so f(s)<=e(s*)-e(s); also f(s)>=-sup|e|. The case g<0 is
symmetric. A constant g causes no exception.

Apply this to the exact plane function

    f(z)=N0 dot(AP-zP+eAX)

and to the affine function with the two computed dot products as its
coefficients. Divide by ||N0||. The normal error contributes 2rho D to
first order; AX rounding contributes rho D; the two dot errors contribute
2kappa rho D. The oscillation bound is smaller. Rounding and clamping the
quotient moves its exact clamped root by at most rho/(1-rho), adding rho D.
Including (6) proves that the computed point has height at most

    8.34rho D                                      (16)

over the common triangle plane. This bound permits a zero computed plane
slope. The normal-norm condition ensures the absolute errors in (5) and
(2) are covered by the stated remainder; it does not impose an angle
condition between the segment and the plane.

If the orthogonal projection of X'(s) is outside the triangle, join X'(s)
to an intersection point along X'. Project this path onto the plane. Its
first exit from the triangle lies on an edge, and the associated point of
X' has height no larger than (16). Thus there is a segment/edge witness.

If the projection is inside, apply the point/triangle coverage argument
with d bounded by (16). It produces either a face candidate or a
segment/edge witness whose exact separation is at most

    rho D V(8.34)+4h.                              (17)

Transfer that witness to the corresponding actual edge kernel using the
shared-input bound 5.02rho D, not two independent geometry perturbations.
Apply (9), then its evaluation allowance. The worst upper bound is

    rho D {F(V(8.34)+5.02)+3.53}+8h,
    F(V(8.34)+5.02)+3.53 <35.8.                    (18)

The direct face alternative V(8.34)+4.03 is smaller. Equations (14), (18),
and the small-area alternative show that 35.8rho D+8h is a valid common
upper error bound for a segment and triangle.

## 8. Triangles, selection, and the final constants

For two disjoint triangles a closest pair can be chosen as vertex/face or
edge/edge, by the same sliding argument. For intersecting triangles, either
there is a vertex/face containment, an edge/edge intersection, or an edge
crosses the other triangle. This also covers coplanar overlap; degenerate
triangles are unions of their edges.

The triangle-triangle routine contains every candidate needed for those
cases. In particular it contains the endpoint projections needed for
(12), not merely the face candidates. For an edge crossing a face, its
candidate set contains the segment-triangle candidates analyzed above.
Argument reversal preserves squared distances. Selecting the minimum
squared distance can only improve an upper bound, because square root is
monotone. We have therefore proved for every implemented pairing

    sqrt(q)-d <35.8rho D+8h.                       (19)

The constants are checked by rational upper bounds for all square roots in
`check_constants.py`; this checks the constants, not input samples.
The largest exact-real expression in (18) is approximately 35.77847910.

If sqrt(q) is rounded to T, its additional error is at most 1.01rho D in
the present range. For example the reconstruction result and feasibility
repair bound ||r|| by D(1+16rho); (2) then bounds sqrt(q) by
D(1+20rho) plus the absorbed absolute term. Consequently the rounded-root
upper error is bounded by

    36.81rho D+8h.

Finally

    36.81*2sqrt(3)<128,
    32h < H,

where the second inequality follows by fourth powers from
32^4*(2rho)<=1/8<1. We can conservatively replace 8h by 32h and conclude

    sqrt(q)-d <=128rho L+H=64eps(T)L+H,

also for the rounded square root. The small-coordinate regime was already
covered, and the earlier lower bound is stronger than required. This proves
the two-sided claim with constant 64 under the stated arithmetic assumptions.


# Appendix A: small coordinates and the lower bound

The reconstruction estimate used here is proved in [reconstruction.md](reconstruction.md).
For L>H/64 it gives, for every candidate,

    ||r-(Y(t)-X(s))|| <=16 rho L.

## 1. Rounding the squared norm

For q=fl(r3^2+fl(r2^2+fl(r1^2))), with the indicated FMAs, standard direct
propagation of |fl(z)-z|<=rho|z|+eta/2 gives

    |q-||r||^2| <= gamma_3 ||r||^2+2eta,
    gamma_3=3rho/(1-3rho).

The absolute underflow term follows by summing the three eta/2 terms and their
subsequent factors (1+rho). At rho<=2^-24 their sum is below 2eta.

The identities for differences of square roots give, at these values of rho,

    |sqrt(q)-||r||| <=2rho||r||+2sqrt(eta).             (2)

For the lower inequality one can use
sqrt(max(a-b,0))>=sqrt(a)-sqrt(b), with a=(1-gamma_3)||r||^2.
For the upper inequality use sqrt(a+b)<=sqrt(a)+sqrt(b). The relative
square-root factors obey

    1-sqrt(1-gamma_3)<=2rho,
    sqrt(1+gamma_3)-1<=2rho.

## 2. Small coordinates: both sides of claim 4 hold

If L=0, d=q=0. If 0<L<=H/64, every separation component in the implementation
is bounded by 16L. This is a direct bound through the differences and at most
three FMAs, using the representable upper bounds 2L,4L,8L,16L. Thus

    sqrt(q) <=sqrt(1+gamma_3)*16sqrt(3)L+sqrt(2eta)
            <28L+2sqrt(eta)<H.

Here 2sqrt(eta)/H is 2^-42 for Float32 and 2^-280.5 for Float64, whereas
28L/H<=7/16. Also d<=2sqrt(3)L<H. Since both distances are nonnegative,

    |sqrt(q)-d|<H.                                    (3)

No optimality of the selected candidate is needed for this small-coordinate
case.

## 3. Repairing the exact barycentric points

The floating-point weight constraints imply that the exact sum of a triangle's
two returned weights is at most 1+rho/2. If the sum exceeds 1, reduce one
weight by the excess. The point then belongs to the triangle, and moves by at
most

    (rho/2)*2sqrt(3)L = sqrt(3)rho L.

For a point or a segment there is no repair cost. With R=Y(t)-X(s), repairing
both simplexes therefore proves

    ||R|| >= d-2sqrt(3)rho L.                         (4)

Also, each exact barycentric point has every coordinate bounded by (1+rho)L:
the sum of absolute values of its full weights is at most 1+rho. Hence

    ||R|| <=2sqrt(3)(1+rho)L.

## 4. Lower bound for all implemented pairings

Assume L>H/64. Equations (1) and (4) give

    ||r|| >= d-(16+2sqrt(3))rho L.                     (5)

They also give

    ||r|| <=[2sqrt(3)(1+rho)+16rho]L<4L.

Furthermore 2sqrt(eta)<=rho L in this regime. At its lower endpoint the ratio
2sqrt(eta)/(rho L) is at most 2^-12 for Float32 and 2^-221.5 for Float64.
Equation (2) now yields

    |sqrt(q)-||r||| <=9rho L.

Together with (5),

    d-sqrt(q) <=(25+2sqrt(3))rho L
              <32rho L
              =16 eps(T)L.                            (6)

Combining (3) and (6) proves, globally,

    d-sqrt(q) <=16 eps(T)L+H.                         (7)

Thus underestimation already satisfies a stronger bound than the proposed 64.
If the square root is itself rounded to T, its additional error is less than
5rho L in the large-coordinate case. The analogous global one-sided bound
with 20 eps(T)L+H therefore holds for that interpretation as well.



# Source and formalization scope

This is the earlier natural-language analysis. The completed Lean proof of
claim 4 uses alternative conservative local estimates, documented in
[formalization-notes.md](formalization-notes.md), and proves the real-square-root
bound for every admissible input to the explicit IEEE-word transcription.
`FinalClaim4.lean` states the universal binary32 and binary64 theorems without
accuracy certificates. The transcription's correspondence to the Julia source
is reviewed and regression-tested; it is not a verified source translation.
See [README.md](README.md) for the theorem statements and validation scope.

SHA-256 hashes of the SimplexCellLists.jl source. This analysis was written
against commit `aaff918c16d8a7ed3c804f7caaf74bcfbee618a9`. The repository pins
commit `f15f96a19c1aa36f02a224557f4628c4437944cb`, whose `src/distances.jl`
differs from the analyzed file only in docstrings.

| File | Analyzed (`aaff918`) | Pinned (`f15f96a`) |
| --- | --- | --- |
| `src/distances.jl` | `3187326dc90b39ba6f002d6d071b51a3f09df879b0523e73a83201ad67c5d9fb` | `2a86a7b408c1a7219ee67ae803313442d0c4f1c56dfdd3e8c23113d837ab8c88` |
| `src/util.jl` | `ddcdc2d36f85328454a8246389de082ce558766f5d8b79078208aa2005db65df` | `ddcdc2d36f85328454a8246389de082ce558766f5d8b79078208aa2005db65df` |
