// Geometric Tools Engine (David Eberly) DCPQuery<double, ...>, as gte_robust_*, using the
// robust variant of each query where GTE has one.
//
// Case mapping:
//   point_seg  DCPQuery<double, Vector3, Segment3>
//   seg_seg    DCPQuery<double, Segment3, Segment3>::ComputeRobust
//   point_tri  DCPQuery<double, Vector3, Triangle3>::UseConjugateGradient
//   seg_tri    DCPQuery<double, Segment3, Triangle3>
//   tri_tri    DCPQuery<double, Triangle3, Triangle3>
//
// GTE's segment-triangle and triangle-triangle queries require a nonzero segment and nonzero
// triangle edges: their line-segment step LogAsserts it, which throws. So for those two cases,
// exactly repeated vertices are removed first, and the simplexes that remain go to the GTE query
// for their shapes (a segment of zero length is a point, a triangle with a repeated vertex is a
// segment or a point). That check is inside the timed query. The batch still records NaN if anything
// else throws.
#include "batch.hpp"
#include <Mathematics/DistPointSegment.h>
#include <Mathematics/DistPointTriangle.h>
#include <Mathematics/DistSegment3Triangle3.h>
#include <Mathematics/DistSegmentSegment.h>
#include <Mathematics/DistTriangle3Triangle3.h>

using Vector = gte::Vector3<double>;
using Segment = gte::Segment3<double>;
using Triangle = gte::Triangle3<double>;

static Vector point(const double* p) { return Vector{p[0], p[1], p[2]}; }
static Segment segment(const double* p) { return Segment(point(p), point(p + 3)); }
static Triangle triangle(const double* p) { return Triangle(point(p), point(p + 3), point(p + 6)); }

static double point_seg(const Vector& p, const Segment& s) {
    return gte::DCPQuery<double, Vector, Segment>{}(p, s).sqrDistance;
}
static double seg_seg(const Segment& s, const Segment& t) {
    return gte::DCPQuery<double, Segment, Segment>{}.ComputeRobust(s, t).sqrDistance;
}
static double point_tri(const Vector& p, const Triangle& t) {
    return gte::DCPQuery<double, Vector, Triangle>{}.UseConjugateGradient(p, t).sqrDistance;
}

// The vertices of a simplex, as converted before timing.
struct Vertices {
    Vector v[3];
    int n = 0;
};
template <int N>
static Vertices vertices(const double* p) {
    Vertices u;
    for (int i = 0; i < N; ++i) u.v[i] = point(p + 3 * i);
    u.n = N;
    return u;
}

// The distinct vertices of a simplex, in order: exactly repeated vertices removed. This check is
// part of the timed query.
static Vertices distinct(const Vertices& s) {
    Vertices u;
    for (int i = 0; i < s.n; ++i) {
        bool repeated = false;
        for (int j = 0; j < u.n; ++j) repeated = repeated || u.v[j] == s.v[i];
        if (!repeated) u.v[u.n++] = s.v[i];
    }
    return u;
}

// The squared distance of two simplexes with distinct vertices, by the GTE query for their shapes.
static double distinct_dist2(const Vertices& a, const Vertices& b) {
    if (a.n > b.n) return distinct_dist2(b, a);
    const Vector* x = a.v;
    const Vector* y = b.v;
    if (a.n == 1 && b.n == 1) { Vector d = x[0] - y[0]; return gte::Dot(d, d); }
    if (a.n == 1 && b.n == 2) return point_seg(x[0], Segment(y[0], y[1]));
    if (a.n == 1) return point_tri(x[0], Triangle(y[0], y[1], y[2]));
    if (b.n == 2) return seg_seg(Segment(x[0], x[1]), Segment(y[0], y[1]));
    if (a.n == 2) return gte::DCPQuery<double, Segment, Triangle>{}(Segment(x[0], x[1]), Triangle(y[0], y[1], y[2])).sqrDistance;
    return gte::DCPQuery<double, Triangle, Triangle>{}(Triangle(x[0], x[1], x[2]), Triangle(y[0], y[1], y[2])).sqrDistance;
}

// The queries as lambdas, so they inline into the batch loop.
static auto q_point_seg = [](const Vector& p, const Segment& s) { return point_seg(p, s); };
static auto q_seg_seg = [](const Segment& s, const Segment& t) { return seg_seg(s, t); };
static auto q_point_tri = [](const Vector& p, const Triangle& t) { return point_tri(p, t); };
static auto q_distinct = [](const Vertices& a, const Vertices& b) { return distinct_dist2(distinct(a), distinct(b)); };

EXPORT void* gte_robust_point_seg(const double* in, int64_t n) { return prepare<1, 2>(in, n, point, segment, q_point_seg); }
EXPORT void* gte_robust_seg_seg(const double* in, int64_t n) { return prepare<2, 2>(in, n, segment, segment, q_seg_seg); }
EXPORT void* gte_robust_point_tri(const double* in, int64_t n) { return prepare<1, 3>(in, n, point, triangle, q_point_tri); }
EXPORT void* gte_robust_seg_tri(const double* in, int64_t n) { return prepare<2, 3>(in, n, vertices<2>, vertices<3>, q_distinct); }
EXPORT void* gte_robust_tri_tri(const double* in, int64_t n) { return prepare<3, 3>(in, n, vertices<3>, vertices<3>, q_distinct); }
