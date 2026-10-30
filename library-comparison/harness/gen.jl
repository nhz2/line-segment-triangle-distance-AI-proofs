# Generate the inputs and their BigFloat references, all Float64.
# Run from library-comparison with: julia --project=. harness/gen.jl [datadir]
# The default datadir is library-comparison/data.
#
# Each set is two files. <case>_<set>.bin: per pair, the (na + nb) vertices of the two simplexes,
# 3 little-endian Float64 each. <case>_<set>.ref: per pair, the reference distance (dist_sqr in
# 512-bit BigFloat, square rooted, rounded to Float64) and ℓ, the largest absolute coordinate.
using StaticArrays, LinearAlgebra, Random
using SimplexCellLists: dist_sqr

const DATA = isempty(ARGS) ? joinpath(@__DIR__, "..", "data") : ARGS[1]
const CASES = [("point_seg", 1, 2), ("seg_seg", 2, 2), ("point_tri", 1, 3), ("seg_tri", 2, 3), ("tri_tri", 3, 3)]
const NPAIRS = 10_000
# Exact powers of two that half of the hard pairs are scaled by, a quarter each, so only
# underflow can change a scale-invariant method's error. ℓ of a hard pair is about 0.5 to 1.4e5, so:
#   2^-500: ℓ ~ 1e-151; squares of separations underflow.
#   2^-270: ℓ ~ 1e-82; squares fine, fourth powers underflow.
const TINY_SCALES = (-500, -270)

V3 = SVector{3, Float64}

# Pairs that SimplexCellLists.jl's tests and ../distance-accuracy/counterexample.jl found over
# 8*eps(Float32)*ℓ in Float32, added to the hard sets as they are. Their Float32 coordinates are
# exact in Float64, where the errors are far smaller.
const OVER_8_EPS_FLOAT32 = Dict(
    # test-mindistance.jl, "Float32 point on the face of a triangle with large coordinates": 8.07.
    "point_tri" => [(V3(9718146, 10124128, 10000623),
        V3(-10351314, -10323355, -10169968), V3(10351314, 6399932, 9067019), V3(9871146, 10323356, 10169969))],
    # test-mindistance.jl, "Float32 end point of a long line segment near a short one": 8.12 with
    # the short segment first, so both orders.
    "seg_seg" => let x = (V3(1.9877764f6, 9.505106f6, 9.729709f6), V3(-9.696928f6, -5.704686f6, -9.494322f6)),
                     y = (V3(-9.676423f6, -5.6547575f6, -9.56445f6), V3(-9.731833f6, -5.7896785f6, -9.374942f6))
        [(x..., y...), (y..., x...)]
    end,
    # counterexample.jl, a line segment through the face of a triangle: 9.16.
    "seg_tri" => [(V3(-9373420, -7754638, -8416905), V3(9778836, 10196786, 10057847),
        V3(-10350544, -10332076, -10169968), V3(10350545, 7004759, 9067019), V3(9871916, 10332077, 10169969))],
)

logu(rng, a, b) = 10.0^(a + (b - a)*rand(rng))
function randrot(rng)
    Q, R = qr(randn(rng, 3, 3))
    SMatrix{3,3}(Matrix(Q) * Diagonal(sign.(diag(R))))
end

# Place canonical-frame vertices in space: random rotation, then a translation
# whose magnitude is drawn from {0, 1, 1e3, 1e5}, to force cancellation.
function place(rng, verts)
    R = randrot(rng)
    O = rand(rng, (0.0, 1.0, 1e3, 1e5)) * normalize(randn(rng, V3))
    map(v -> V3(R * v + O), verts)
end

rv(rng) = randn(rng, V3)
function sliver(rng)
    # Triangle with C within h of line AB.
    h = rand(rng, (0.0, logu(rng, -14, -2)))
    t = rand(rng) * 1.4 - 0.2
    (V3(0,0,0), V3(1,0,0), V3(t, h, 0.0))
end
function degenerate_tri(rng)
    a, b = rv(rng), rv(rng)
    k = rand(rng, 1:3)
    k == 1 ? (a, a, b) : k == 2 ? (a, b, a + 0.37*(b - a)) : (a, a, a)
end
nicetri(rng) = (V3(-0.9,-0.6,0.0), V3(0.8,-0.2,0.0), V3(-0.2,0.9,0.0))

# A sliver with nonzero height, and a point over its face at distance δ, so
# the face, not an edge, is closest. GJK codes stop early here.
function sliver_with_point_over_face(rng)
    h = logu(rng, -12, -3)
    t = rand(rng) * 1.4 - 0.2
    A, B, C = V3(0,0,0), V3(1,0,0), V3(t, h, 0.0)
    w = rand(rng, 3); w /= sum(w)
    δ = rand(rng, (-1, 1)) * logu(rng, -14, -1)
    (A, B, C), w[1]*A + w[2]*B + w[3]*C + V3(0, 0, δ), sign(δ)
end

function hard_pair(rng, case)
    # seg_tri and tri_tri have a fifth kind; the others keep their old streams.
    k = rand(rng, case in ("seg_tri", "tri_tri") ? (1:5) : (1:4))
    if case == "point_seg"
        if k == 1      # zero length segment
            a = rv(rng); verts = (rv(rng), a, a)
        elseif k == 2  # point extremely close to the interior of the line
            h = logu(rng, -15, -1)
            verts = (V3(rand(rng)*2 - 1, h, 0), V3(-1, 0, 0), V3(1, 0, 0))
        elseif k == 3  # point just beyond an end point, near the line
            verts = (V3(1 + logu(rng, -12, -1), logu(rng, -12, -1), 0), V3(-1, 0, 0), V3(1, 0, 0))
        else           # very short segment far away
            s = logu(rng, -12, -3)
            verts = (rv(rng), V3(0,0,0), V3(s,0,0))
        end
    elseif case == "seg_seg"
        if k == 1      # nearly parallel, small separation, overlapping
            θ = rand(rng, (0.0, logu(rng, -12, -2))); h = rand(rng, (0.0, logu(rng, -10, 0)))
            o = rand(rng) * 2 - 1
            verts = (V3(-1,0,0), V3(1,0,0), V3(o - cos(θ), -sin(θ), h), V3(o + cos(θ), sin(θ), h))
        elseif k == 2  # crossing (distance near 0), random angle
            θ = rand(rng) * π; h = rand(rng, (0.0, logu(rng, -14, -4)))
            verts = (V3(-1,0,0), V3(1,0,0), V3(-cos(θ), -sin(θ), h), V3(cos(θ), sin(θ), h))
        elseif k == 3  # zero length segment(s)
            a = rv(rng)
            verts = rand(rng, Bool) ? (a, a, rv(rng), rv(rng)) : (a, a, rv(rng) .* 0 .+ a .+ 1e-3, a .+ 1e-3)
        else           # collinear, possibly overlapping or end-to-end
            g = rand(rng, (-0.5, 0.0, logu(rng, -12, -2)))
            verts = (V3(-1,0,0), V3(0,0,0), V3(g,0,0), V3(1 + g,0,0))
        end
    elseif case == "point_tri"
        if k == 1      # sliver triangle, point near it
            T = sliver(rng); p = V3(rand(rng), logu(rng, -12, 0) * randn(rng), logu(rng, -12, 0) * randn(rng))
            verts = (p, T...)
        elseif k == 2  # degenerate triangle
            verts = (rv(rng), degenerate_tri(rng)...)
        elseif k == 3  # point very near the plane over the face
            T = nicetri(rng); p = V3(-0.05 + 0.1rand(rng), 0.1rand(rng), rand(rng, (-1, 1)) * logu(rng, -15, 0))
            verts = (p, T...)
        else           # point near an edge/vertex region border
            T = nicetri(rng); p = V3(0.88, -0.54, 0.3) + 1e-9 * rv(rng)
            verts = (p, T...)
        end
    elseif case == "seg_tri"
        T = rand(rng) < 0.3 ? sliver(rng) : nicetri(rng)
        if k == 1      # segment parallel to the plane, h over the face
            h = rand(rng, (0.0, logu(rng, -14, 0)))
            verts = (V3(-0.3, -0.1, h), V3(0.3, 0.2, h), T...)
        elseif k == 2  # segment in the plane beside the triangle (Möller-Trumbore trap)
            verts = (V3(0.9, 0.5, 0.0), V3(1.5, 1.0, 0.0), T...)
        elseif k == 3  # segment piercing the triangle or nearly so
            o = V3(rand(rng) * 0.2 - 0.1, rand(rng) * 0.2, 0.0)
            d = normalize(rv(rng)) * 0.5
            verts = (o - d, o + d + V3(0, 0, rand(rng, (0.0, logu(rng, -12, -2)))), T...)
        elseif k == 5  # an end point over a sliver's face, the segment leaning away
            S3, p, s = sliver_with_point_over_face(rng)
            q = p + V3(0.3, 0.2, s*0.5)
            verts = ((rand(rng, Bool) ? (p, q) : (q, p))..., S3...)
        else           # degenerate triangle or segment
            verts = rand(rng, Bool) ? (rv(rng), rv(rng), degenerate_tri(rng)...) : (V3(0.1,0.1,0.2), V3(0.1,0.1,0.2), T...)
        end
    else # tri_tri
        T = rand(rng) < 0.3 ? sliver(rng) : nicetri(rng)
        if k == 1      # coplanar, gap g
            g = rand(rng, (0.0, logu(rng, -12, -1)))
            verts = (T..., V3(1.0 + g, 0.5, 0.0), V3(2.0, 1.0, 0.0), V3(1.5, -0.5, 0.0))
        elseif k == 2  # parallel planes, offset h, overlapping footprint
            h = rand(rng, (0.0, logu(rng, -14, 0)))
            verts = (T..., V3(-0.5, -0.3, h), V3(0.5, -0.1, h), V3(0.0, 0.5, h))
        elseif k == 3  # piercing
            verts = (T..., V3(0.0, 0.0, -0.5), V3(0.1, 0.1, 0.5), V3(1.5, 1.5, rand(rng) - 0.5))
        elseif k == 5  # a vertex of a well-shaped triangle over a sliver's face, leaning away
            S3, p, s = sliver_with_point_over_face(rng)
            U = (p, p + V3(0.3, 0.0, s*0.5), p + V3(0.0, 0.3, s*0.5))
            verts = rand(rng, Bool) ? (U..., S3...) : (S3..., U...)
        else           # degenerate
            verts = (degenerate_tri(rng)..., (rand(rng, Bool) ? degenerate_tri(rng) : (rv(rng), rv(rng), rv(rng)))...)
        end
    end
    place(rng, verts)
end

function write_set(name, na, nb, pairs)
    open(joinpath(DATA, name * ".bin"), "w") do io
        for p in pairs, v in p, c in v
            write(io, htol(c))
        end
    end
    setprecision(BigFloat, 512) do
        open(joinpath(DATA, name * ".ref"), "w") do io
            for p in pairs
                a = SVector{na}(map(v -> big.(v), p[1:na]))
                b = SVector{nb}(map(v -> big.(v), p[na+1:end]))
                d = sqrt(dist_sqr(a, b))
                ℓ = maximum(v -> maximum(abs, v), p)
                write(io, htol(Float64(d)), htol(Float64(ℓ)))
            end
        end
    end
end

mkpath(DATA)
for (case, na, nb) in CASES
    rng = Xoshiro(hash(case))
    # Uniform in the unit cube, like SimplexCellLists.jl's benchmark/distancesbench.jl.
    rnd = [Tuple(rand(rng, V3) for _ in 1:(na + nb)) for _ in 1:NPAIRS]
    write_set(case * "_random", na, nb, rnd)
    hard = [Tuple(hard_pair(rng, case)) for _ in 1:NPAIRS]
    for i in eachindex(hard)
        k = rand(rng, 1:4)
        k <= length(TINY_SCALES) && (hard[i] = map(v -> ldexp.(v, TINY_SCALES[k]), hard[i]))
    end
    append!(hard, get(OVER_8_EPS_FLOAT32, case, []))
    write_set(case * "_hard", na, nb, hard)
    println("wrote ", case)
end
