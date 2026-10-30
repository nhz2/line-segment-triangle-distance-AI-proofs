# Proof of claim 5 for the current implementation

This proof is for Float32 and Float64, IEEE round-to-nearest/ties-to-even,
correctly rounded FMA, and gradual underflow. All input coordinates are finite
and have absolute value at most L, with

    L < floatmax(T)^(1/4)/4.

All arithmetic in this document, except explicitly marked floating operations,
is real arithmetic on the exact values of the floating-point inputs/outputs.
Put

    rho = eps(T)/2,
    eta = nextfloat(zero(T)),
    H = floatmin(T)^(1/4).

We prove

    norm(r - (Y(t) - X(s))) <= 16*rho*L + H.

The proof does not assume accuracy of the cross products, their quotients, or
candidate selection. It does use the particular computation of `u` in
`_tri_face_candidate`, in addition to bounded weights.

## 1. Elementary rounding facts and small coordinates

For every non-overflowing elementary rounded operation,

    |fl(z)-z| <= rho*|z| + eta/2.                         (1)

Every clamped weight is in [0,1]. For w in [0,1],

    c = fl(1-w) - (1-w)

satisfies |c| <= rho/2; furthermore c=0 when w>=1/2, by exact subtraction
of these floating-point numbers. In particular a returned face pair satisfies
u+v <= 1+rho/2 in real arithmetic.

If L=0 the result and its exact reconstruction are zero. If 0<L<=H/64,
a direct magnitude bound suffices: every computed separation component has
absolute value <=16L. This follows by propagating bounds 2L, 4L, 8L, 16L
through the differences and at most three FMAs; these power-of-two multiples
are representable. Every exactly reconstructed simplex point has each
component <=(1+rho)L in absolute value. Consequently the discrepancy is
at most 20*sqrt(3)*L < H.

Henceforth L>H/64. For both formats,

    eta <= rho^2 L,             eta <= rho^2 L^2.        (2)

For example, for Float32, H/64=2^(-37.5), rho=2^-24,
eta=2^-149. For Float64 these are 2^(-261.5), 2^-53,
2^-1074. These inequalities allow the absolute terms in (1) to be absorbed
in explicit second-order bounds below.

## 2. Affine evaluation error accounting

Temporarily hold all returned/computed parameters fixed as exact real numbers.
The arithmetic constructing r is then an affine computation in the vertex
coordinates. For one coordinate, let F be the sum, over its rounded operations,
of the absolute exact result at that operation multiplied by the absolute
coefficient with which that operation's rounding error enters the final result.
Here the exact result means the result with prior operations made exact, while
keeping the parameters fixed.

For the expressions in this implementation the componentwise error is bounded by

    rho F + 4096 rho^2 L.                               (3)

Here is conservative bookkeeping for the explicit remainder, rather than an
asymptotic convention. There are at most eight affine operations; each local
error has final or intermediate coefficient of absolute value at most one.
Computed magnitudes are at most 16L, so each local error is at most 17 rho L
using (1)-(2). A prior-error contribution at any node is therefore at most
136 rho L. Applying (1) to that node introduces at most 136 rho^2 L plus
eta/2 beyond its first-order term. Summing eight nodes gives at most
1092 rho^2 L. The larger constant 4096 also covers the following adjustment.

For face candidates, write v0 for the initially clamped v, and define

    vbar = min(v0, 1-u).

The actual v differs from vbar by at most rho/2. Use vbar when forming F,
so that u+vbar<=1 exactly. This changes F by at most 2 rho L: only its
v-weighted edge term and its final affine-value term change. This contributes
at most 2 rho^2 L to (3). The discrepancy being bounded is still the one for
the *actual returned* weights, not for adjusted weights.

The coefficient assertion above includes the reused E0 in the point-triangle
BC candidate: its final coefficient is 1-t, not 1+t. This cancellation is
algebraic and exact in the error representation.

If an edge (B,C) is embedded in a triangle (A,B,C), the returned weights are
(fl(1-w),w), rather than the exact pair (1-w,w). The resulting change in the
exact reconstructed point is

    [fl(1-w)-(1-w)] (B-A).

It costs at most rho L in each coordinate, and costs zero if w>=1/2.
These embedding costs are included explicitly below, not hidden in (3).

## 3. Candidates other than segment-face crossings

All letters in the following formulas denote one coordinate, with absolute
value <=L. P0,P1 and Q0,Q1 are segment vertices. Put

    X=(1-s)P0+sP1,    Y=(1-t)Q0+tQ1.

The first-order expressions are:

* Point-point: |Q0-P0|.
* Point-segment: |Q0-P0|+t|Q1-Q0|+|Y-P0|.
* Ordinary face candidate:
  |A-X|+u|B-A|+vbar|C-A|+|A+u(B-A)-X|+|A+u(B-A)+vbar(C-A)-X|.
* Point-triangle BC candidate:
  |A-X|+(1-t)|B-A|+t|C-A|+|B-X|+t|C-B|+|(1-t)B+tC-X|.
* Segment-segment interior candidate:
  |Q0-P0|+t|Q1-Q0|+s|P1-P0|+|Y-P0|+|Y-X|.
* Segment-segment P1 candidate:
  |Q0-P0|+|P1-P0|+t|Q1-Q0|+|Q0-P1|+|Y-P1|.

The other segment endpoint is a point-segment expression. The first three
expressions are bounded by 2L, 4L, and 6L respectively.

For the segment interior expression, upper bounds on F/L on the indicated
weight rectangles are:

| s range | t range | upper bound on F/L | possible embedding cost/(rho L) |
|---|---|---:|---:|
| [0,1/2] | [0,1/2] | 6 | 2 |
| [0,1/2] | [1/2,1] | 7 | 1 |
| [1/2,1] | [0,1/2] | 7 | 1 |
| [1/2,1] | [1/2,1] | 8 | 0 |

For the BC and P1 expressions, F<=7L when t<=1/2, and F<=8L otherwise.
There is at most one nonzero embedding cost in these cases. The point-segment
endpoint candidate also stays below 8L after its possible embedding cost.

These are finite convexity calculations, not numerical sampling: for fixed
weights each expression is convex in the vertex coordinates, so its maximum
occurs with each coordinate equal to +/-L. For fixed coordinates it is convex
in the parameter rectangle (or the face-weight triangle). Evaluate its vertices.
The accompanying `check_reconstruction.jl` enumerates these small sets using
rational arithmetic. Vertex embeddings themselves are exact.

Thus every non-crossing candidate, including all triangle edge embeddings,
has discrepancy at most

    (8 sqrt(3) + 4096 sqrt(3) rho) rho L < 16 rho L.       (4)

## 4. The crossing candidate: an exact scalar lemma

Lemma. Let a,b,c,x belong to [-1,1], and let u,v0 belong to [0,1]. Put

    e=b-a, h=c-a, v=min(v0,1-u),
    G=u|e|+v|h|+|a+ue-x|+|a+ue+vh-x|,
    Rpre=a+ue+v0h-x.

Then

    G^2 <= 20 + 5u e Rpre.                              (5)

Proof. Maximize J=G^2-5ueRpre. It is convex in x: G is nonnegative and convex
in x, and the subtracted term is affine in x. Thus take x=+/-1; reflection
reduces to x=-1. It is also convex in c, so take c=+/-1.

Set A=a+1 in [0,2]. Since a+ue and a+ue+vh are in [-1,1], their differences
from x=-1 are nonnegative, giving

    G=2A+u(2e+|e|)+2v max(h,0).

For e>=0, J is a convex quadratic in e (quadratic coefficient 4u^2), so
only e=0 and e=2-A need consideration. At e=0, J<=16.

At e=2-A=:D:

* If c=-1, then h=-A. J increases with v0, so set v0=1. The result
  4A^2+12AuD+4u^2D^2 increases with u; at u=1 it is
  16+8D-4D^2 = 20-4(D-1)^2 <=20.
* If c=+1 and v0<=1-u, put k=1-u-v0. Then
  J=16-2uD-16kD+D^2(u^2+uk+4k^2).
  This is convex in D in [0,2]. Its value at D=0 is 16; at D=2 it is <=16,
  since -4u+4u^2<=0 and -32k+4uk+16k^2<=0.
* If c=+1 and v0>=1-u, v=1-u is fixed and J decreases with v0.
  Its maximum is the preceding case v0=1-u, again <=16.

For e<=0 set w=ue<=0, K=2v max(h,0), and B=-A+2K-5v0h. Then

    J=(2A+K)^2 + Bw - 4w^2.

If c=-1, K=0 and B=A(5v0-1). For B>=0 the last two terms are nonpositive.
For B<0, completing the square bounds J by (4+1/16)A^2<=65/4.

If c=+1 and v=v0, let D=A+v0(2-A)<=2. Then 2A+K=2D and B=-D;
completing the square gives J<=65 D^2/16<=65/4.

Finally, if c=+1 and v=1-u, J increases with v0 because w<=0, so set v0=1.
With t=u(2-A) in [0,2], completing the square gives

    J <= (4-2t)^2+(2+4t)^2/16
       = 65/4-15t+5t^2 <=65/4.

Every case is <=20, proving (5).

## 5. Applying the lemma to the crossing arithmetic

Use exact vertices A,B,C,P0,P1 in three dimensions and exact weights s,u,v0.
Define

    E=B-A, F=C-A, X=(1-s)P0+sP1,
    W=A+uE, Y=A+uE+vbar F,
    Rpre=A-X+uE+v0 F.

The first-order affine error expression in coordinate k is H_k+G_k, where

    H_k=|A_k-P0_k|+s|P1_k-P0_k|+|A_k-X_k|,
    G_k=u|E_k|+vbar|F_k|+|W_k-X_k|+|Y_k-X_k|.

The interval triangle-perimeter inequality gives H_k<=4L. Applying (5) in
each coordinate and summing gives

    ||G||^2 <=60L^2+5u E dot Rpre.                      (6)

There are three cases.

### 5a. s<1/2

Direct convexity bounds H_k+G_k<=8L: take s at 0 or 1/2, (u,vbar) at
(0,0),(1,0),(0,1), and scalar vertex coordinates at +/-L. All six parameter
choices have maximum 8L. There may be one edge embedding cost rho L for the
segment. By (3),

    discrepancy <= (9 sqrt(3)+4096 sqrt(3)rho)rho L
                < 15.589 rho L <16 rho L.              (7)

### 5b. s>=1/2 and ||E||<=2L

There is no segment embedding error, since fl(1-s)=1-s exactly.
Convexity in (u,vbar) gives

    G_k <=4L+u|E_k|.

Indeed the u=0 endpoint expression is a scalar triangle perimeter <=4L,
and the u=1 expression is |E_k|+2|B_k-X_k|<=|E_k|+4L; the v=0 boundary
satisfies the same bound. Therefore

    ||H+G|| <=8 sqrt(3)L+u||E|| <=(8 sqrt(3)+2)L.

Using (3), the discrepancy is less than 15.857 rho L <16 rho L.

### 5c. s>=1/2 and ||E||>2L

Here the particular computation of u supplies the needed information. Set

    a=E dot E, b=E dot F, d=E dot (A-X),
    q=-(d+v0 b)/a, u*=clamp(q,0,1).

We show

    |u-u*| <=300 rho,
    u E dot Rpre <=10000 rho L^2.                      (8)

The rounded edge vectors differ from E,F in norm by at most 4 rho L.
The computed AX supplied to `_tri_face_candidate` differs from A-X in norm
by at most (4 sqrt(3)+4096 sqrt(3)rho)rho L <7 rho L. This uses the H bound
above and (3), and does not require accuracy of s.

Let ahat,bhat,dhat denote the three computed dot products. A three-term FMA
dot product has absolute error at most gamma_3 ||v||||w|| plus its three
propagated eta/2 terms, where gamma_3=3rho/(1-3rho). Each rounded vector
has norm below 4L. Including the vector-input errors, (1)-(2) give, conservatively,

    |ahat-a|, |bhat-b|, |dhat-d| <=128 rho L^2.

Also 4L^2<a<=12L^2 and |b|,|d|<=12L^2. Thus
ahat>=(4-128rho)L^2. Its reciprocal is normal and finite throughout the
assumed range: the lower bound L>H/64 and the upper bound on L establish
this directly. Each of |bhat/ahat| and |dhat/ahat| is less than 4.

The reciprocal, two products, and final FMA computing the unclamped qhat
therefore introduce at most 40rho absolute error beyond
-(dhat+v0 bhat)/ahat. Meanwhile |q|<=6 gives

    |-(dhat+v0 bhat)/ahat - q|
      <=1024rho/(4-128rho) <257rho.

Clamping is 1-Lipschitz, proving |u-u*|<297rho<300rho.

If u*>0, then d+v0 b+a u*<=0 by the elementary scalar projection condition.
Consequently u(d+v0 b+a u)<=3600rho L^2. If u*=0, then u<=300rho, and
|d+v0 b|<=24L^2 gives

    u(d+v0 b+a u) <=7200rho L^2+1080000rho^2 L^2
                  <10000rho L^2.

This proves (8), including when the parameter clamps to an endpoint.

Combining (3), (6), (8), and ||H||<=4sqrt(3)L gives

    discrepancy <= [4sqrt(3)+sqrt(60+50000rho)
                     +4096sqrt(3)rho] rho L
                <14.675 rho L <16 rho L.               (9)

The displayed numerical inequalities (4), (7), and (9), and the short-edge
bound are valid at the largest unit roundoff under consideration,
rho=2^-24, hence also at rho=2^-53.

## 6. Conclusion

All individual candidates produced by the actual kernels satisfy claim 5.
This includes triangle edge embeddings, because their possible complement
rounding was included. Selecting a candidate does not change its discrepancy;
argument reversal negates both the separation and its exact reconstruction.
Thus every implemented simplex pairing satisfies

    ||r-(Y(t)-X(s))|| <=8 eps(T)L+floatmin(T)^(1/4).

This proof is independent of claim 4 with constant 8, which the exact-integer example disproves. In particular, accurate reconstruction of a selected pair does not
establish that the selected pair is sufficiently close to the true minimizer.
