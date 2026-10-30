# Score squared distances against the BigFloat reference written by gen.jl.
#
# score(datadir, set, d2) returns the median, 99th percentile and maximum error, for `d2` the
# Float64 squared distances of the pairs of `<datadir>/<set>.bin`.
#
# The error of a pair is |√d² - d_ref| as a fraction of the bound that SimplexCellLists.jl's
# src/distances.jl states, and ../distance-accuracy proves, for ℓ = max |coordinate| of the
# pair below floatmax^(1/4)/4:
#
#     |√d² - d| ≤ K*eps*ℓ + floatmin^(1/4), K = 64.
#
# So an error over 1 is outside the bound. A nonfinite d² has error Inf.

const K = 64
const FLOOR = floatmin(Float64)^(1/4)

# Read the reference distances and ℓ of a set.
function read_ref(datadir, set)
    ref = reinterpret(Float64, read(joinpath(datadir, set * ".ref")))
    ref[1:2:end], ref[2:2:end]
end

function score(datadir, set, d2::Vector{Float64})
    dref, ℓ = read_ref(datadir, set)
    length(d2) == length(dref) || error("expected $(length(dref)) outputs, got $(length(d2))")
    err = [isfinite(x) ? abs(sqrt(max(x, 0.0)) - r) / (K*eps(Float64)*l + FLOOR) : Inf
           for (x, r, l) in zip(d2, dref, ℓ)]
    s = sort(err)
    q(p) = s[clamp(ceil(Int, p * length(s)), 1, length(s))]
    (median = q(0.5), p99 = q(0.99), max = s[end])
end
