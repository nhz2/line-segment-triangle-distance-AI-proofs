// The batch interface shared by the C++ shims. Each shim exports, per case,
//
//     void* <lib>_<case>(const double* in, int64_t n)
//
// which converts n pairs to the library's types and returns them as a batch (this is not timed).
// `in` holds the pairs as in the data files: (na + nb) vertices of 3 doubles each, the vertices
// of simplex a, then of simplex b. The batch is then used with
//
//     void batch_run(const void* batch, double* out)   // out[i] = squared distance of pair i (timed)
//     void batch_free(void* batch)
#pragma once
#include <cstddef>
#include <cstdint>
#include <limits>
#include <vector>

// The shims are built with -fvisibility=hidden, so only these functions are exported.
#define EXPORT extern "C" __attribute__((visibility("default")))

struct Batch {
    virtual ~Batch() = default;
    virtual void run(double* out) const = 0;
};

// The converted pairs, and the query `dist2(a, b)` that returns their squared distance.
template <class A, class B, class F>
struct Pairs final : Batch {
    std::vector<A> as;
    std::vector<B> bs;
    F dist2;

    explicit Pairs(F f) : dist2(f) {}

    // A plain loop of queries. An exception (a library throwing on some input) gives NaN for that
    // pair, so none crosses the C ABI.
    void run(double* out) const override {
        for (std::size_t i = 0; i < as.size(); ++i) {
            try {
                out[i] = dist2(as[i], bs[i]);
            } catch (...) {
                out[i] = std::numeric_limits<double>::quiet_NaN();
            }
        }
    }
};

// Convert every pair with `make_a` and `make_b`, which take a pointer to the first coordinate of
// a simplex. `dist2` should be a lambda, so the query is inlined into the loop.
template <int NA, int NB, class MakeA, class MakeB, class F>
Batch* prepare(const double* in, int64_t n, MakeA make_a, MakeB make_b, F dist2) {
    auto* p = new Pairs<decltype(make_a(in)), decltype(make_b(in)), F>(dist2);
    p->as.reserve(n);
    p->bs.reserve(n);
    for (int64_t i = 0; i < n; ++i) {
        const double* pair = in + i * 3 * (NA + NB);
        p->as.push_back(make_a(pair));
        p->bs.push_back(make_b(pair + 3 * NA));
    }
    return p;
}

EXPORT void batch_run(const void* batch, double* out) { static_cast<const Batch*>(batch)->run(out); }
EXPORT void batch_free(void* batch) { delete static_cast<Batch*>(batch); }
