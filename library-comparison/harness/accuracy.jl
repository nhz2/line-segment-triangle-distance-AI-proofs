# Run every library on every case and Float64 set, score the results, and write
# results/accuracy.csv. Also checks that the SimplexCellLists SIMD.Vec batch gives the same
# bits as the scalar dist_sqr loop on every set.
#
# Run from library-comparison, after build.jl and harness/gen.jl, with
#     julia --project=. harness/accuracy.jl [datadir]
include("libs.jl")
include("score.jl")

const DATA = isempty(ARGS) ? joinpath(@__DIR__, "..", "data") : ARGS[1]
const SETS = ["random", "hard"]
const OUT = normpath(joinpath(@__DIR__, "..", "results", "accuracy.csv"))

# Read the pairs of a data file, as raw Float64s, and their number.
function read_set(case, set)
    _, na, nb = only(filter(c -> c[1] == case, CASES))
    raw = reinterpret(Float64, read(joinpath(DATA, "$(case)_$(set).bin")))
    collect(raw), length(raw) ÷ (3 * (na + nb))
end

function check_simd_matches_scalar()
    for (case, na, nb) in CASES, set in SETS
        raw, n = read_set(case, set)
        simd = prepare("SimplexCellLists", case, raw).run!(zeros(n))
        scalar = scl_scalar!(zeros(n), raw, Val(na), Val(nb))
        reinterpret(UInt64, simd) == reinterpret(UInt64, scalar) ||
            error("SIMD.Vec batch differs from the scalar loop on $(case)_$set")
    end
    println("SimplexCellLists SIMD.Vec batch is bit identical to the scalar loop on all sets")
end

function main()
    check_simd_matches_scalar()
    rows = []
    for (lib, _) in LIBS, (case, _, _) in CASES, set in SETS
        raw, n = read_set(case, set)
        out = fill(NaN, n)
        batch = prepare(lib, case, raw)
        batch.run!(out)
        batch.free()
        s = score(DATA, "$(case)_$(set)", out)
        push!(rows, (; lib, case, set, s...))
        println(rpad(lib, 18), rpad(case, 11), rpad(set, 8), "median=", round(s.median; sigdigits = 3),
            " p99=", round(s.p99; sigdigits = 3), " max=", round(s.max; sigdigits = 3))
    end
    mkpath(dirname(OUT))
    open(OUT, "w") do io
        println(io, join(keys(first(rows)), ","))
        for r in rows
            println(io, join(values(r), ","))
        end
    end
    println("wrote ", OUT)
end

main()
