// CGAL 6.2.1 `CGAL::squared_distance`, built twice:
//   default:  Exact_predicates_inexact_constructions_kernel (Epick, double), as cgal_epick_*.
//   -DEXACT:  Exact_predicates_exact_constructions_kernel (Epeck, lazy exact rationals on GMP),
//             as cgal_epeck_*. The exact squared distance is rounded to double.
//
// Case mapping:
//   point_seg  squared_distance(Point_3, Segment_3)
//   seg_seg    squared_distance(Segment_3, Segment_3)
//   point_tri  squared_distance(Point_3, Triangle_3)
//   seg_tri    CGAL has no Segment_3-Triangle_3 distance, so squared_distance(Triangle_3,
//              Triangle_3) with the segment as the degenerate triangle (P0, P1, P1).
//   tri_tri    squared_distance(Triangle_3, Triangle_3)
#include "batch.hpp"

#ifdef EXACT
#include <CGAL/Exact_predicates_exact_constructions_kernel.h>
using K = CGAL::Exact_predicates_exact_constructions_kernel;
#define NAME(c) cgal_epeck_##c
static double to_double(const K::FT& d2) { return CGAL::to_double(CGAL::exact(d2)); }
#else
#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
using K = CGAL::Exact_predicates_inexact_constructions_kernel;
#define NAME(c) cgal_epick_##c
static double to_double(double d2) { return d2; }
#endif
#include <CGAL/squared_distance_3.h>

using Point = K::Point_3;
using Segment = K::Segment_3;
using Triangle = K::Triangle_3;

static Point point(const double* p) { return Point(p[0], p[1], p[2]); }
static Segment segment(const double* p) { return Segment(point(p), point(p + 3)); }
static Triangle triangle(const double* p) { return Triangle(point(p), point(p + 3), point(p + 6)); }
static Triangle segment_as_triangle(const double* p) { return Triangle(point(p), point(p + 3), point(p + 3)); }

// The query, the same for every case.
static auto query = [](const auto& a, const auto& b) { return to_double(CGAL::squared_distance(a, b)); };

EXPORT void* NAME(point_seg)(const double* in, int64_t n) { return prepare<1, 2>(in, n, point, segment, query); }
EXPORT void* NAME(seg_seg)(const double* in, int64_t n) { return prepare<2, 2>(in, n, segment, segment, query); }
EXPORT void* NAME(point_tri)(const double* in, int64_t n) { return prepare<1, 3>(in, n, point, triangle, query); }
EXPORT void* NAME(seg_tri)(const double* in, int64_t n) { return prepare<2, 3>(in, n, segment_as_triangle, triangle, query); }
EXPORT void* NAME(tri_tri)(const double* in, int64_t n) { return prepare<3, 3>(in, n, triangle, triangle, query); }
