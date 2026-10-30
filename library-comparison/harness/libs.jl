# The libraries under test, and how to call each one's batch.
#
# For each library and case, prepare(lib, case, raw) converts the raw pairs of a data file
# (`raw`, the contents of a .bin file) to the library's types; this is not timed. It returns
# `(; run!, free)`: `run!(out)` writes the squared distance of every pair into `out` (this is what
# is timed), and `free()` releases the converted pairs.
using Libdl: dlopen, dlsym
using StaticArrays: SVector
using SimplexCellLists: dist_sqr
import SIMD

# (case, vertices of simplex a, vertices of simplex b)
const CASES = [("point_seg", 1, 2), ("seg_seg", 2, 2), ("point_tri", 1, 3), ("seg_tri", 2, 3), ("tri_tri", 3, 3)]

# Library name => shared library in build/lib, or `nothing` for the Julia SimplexCellLists.
# A shared library exports, per case, `void* <name>_<case>(const double* in, int64_t n)`, which
# converts the pairs, and `batch_run(const void*, double* out)` and `batch_free(void*)`
# (shims/batch.hpp).
const LIBS = [
    "SimplexCellLists" => nothing,
    "cgal_epick" => "libcgal_epick.so",
    "cgal_epeck" => "libcgal_epeck.so",
    "gte_robust" => "libgte_robust.so",
]

const LIBDIR = joinpath(@__DIR__, "..", "build", "lib")

function prepare(lib, case, raw::Vector{Float64})
    _, na, nb = only(filter(c -> c[1] == case, CASES))
    n = length(raw) ÷ (3 * (na + nb))
    so = Dict(LIBS)[lib]
    so === nothing && return scl_prepare(raw, n, Val(na), Val(nb))
    h = dlopen(joinpath(LIBDIR, so))
    batch = ccall(dlsym(h, "$(lib)_$(case)"), Ptr{Cvoid}, (Ptr{Float64}, Int64), raw, n)
    run_fn, free_fn = dlsym(h, :batch_run), dlsym(h, :batch_free)
    run!(out) = (length(out) == n || error("expected $n outputs");
                 ccall(run_fn, Cvoid, (Ptr{Cvoid}, Ptr{Float64}), batch, out))
    free() = ccall(free_fn, Cvoid, (Ptr{Cvoid},), batch)
    (; run!, free)
end

# SimplexCellLists: dist_sqr on SIMD.Vec{8, Float64} lanes, 8 pairs at a time, as
# SimplexCellLists.jl's src/neighbor-lists-grid.jl does. The conversion copies the pairs to one
# array per coordinate, so that 8 consecutive pairs of a coordinate are adjacent. A leftover of
# fewer than 8 pairs uses the scalar dist_sqr, which gives the same bits.
const W = 8

# The pairs of `raw` as an array of (na + nb) vertices each.
pairs_of(raw, ::Val{NA}, ::Val{NB}) where {NA, NB} = reinterpret(SVector{NA + NB, SVector{3, Float64}}, raw)

# Simplex a (vertices 1:NA) and simplex b (vertices NA+1:NA+NB) of a pair.
split_pair(p, ::Val{NA}, ::Val{NB}) where {NA, NB} =
    SVector(ntuple(v -> p[v], Val(NA))), SVector(ntuple(v -> p[NA + v], Val(NB)))

# Vertices `first + 1 : first + NV` of pairs `i : i + W - 1`, with a lane per pair, from `cols`,
# which holds the n values of each coordinate one after the other.
@inline function lanes(cols, n, i, first, ::Val{NV}) where NV
    SVector(ntuple(Val(NV)) do v
        SVector(ntuple(Val(3)) do axis
            @inbounds SIMD.vload(SIMD.Vec{W, Float64}, cols, i + (3 * (first + v - 1) + axis - 1) * n)
        end)
    end)
end

function scl_prepare(raw, n, va::Val{NA}, vb::Val{NB}) where {NA, NB}
    k = 3 * (NA + NB)
    cols = Vector{Float64}(undef, k * n)
    for i in 1:n, j in 1:k
        cols[i + (j - 1) * n] = raw[j + (i - 1) * k]
    end
    pairs = pairs_of(raw, va, vb)
    run!(out) = scl_run!(out, cols, pairs, n, va, vb)
    free() = nothing
    (; run!, free)
end

function scl_run!(out, cols, pairs, n, va::Val{NA}, vb::Val{NB}) where {NA, NB}
    length(out) == n || error("expected $n outputs")
    nfull = n - n % W
    for i in 1:W:nfull
        d2 = dist_sqr(lanes(cols, n, i, 0, va), lanes(cols, n, i, NA, vb))
        @inbounds SIMD.vstore(d2, out, i)
    end
    for i in nfull+1:n
        @inbounds out[i] = dist_sqr(split_pair(pairs[i], va, vb)...)
    end
    out
end

# The plain scalar loop, to check the SimplexCellLists batch against.
function scl_scalar!(out::Vector{Float64}, raw::Vector{Float64}, va::Val, vb::Val)
    pairs = pairs_of(raw, va, vb)
    for i in eachindex(out, pairs)
        out[i] = dist_sqr(split_pair(pairs[i], va, vb)...)
    end
    out
end
