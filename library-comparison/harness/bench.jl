# Time every library's batch function on every case, on the random sets, and write
# results/timing.csv. Run from library-comparison, after build.jl and harness/gen.jl,
# pinned to one CPU of an otherwise idle machine:
#
#     taskset -c 2 julia --project=. harness/bench.jl
#
# The conversion of the pairs to each library's types is done before timing (prepare in
# libs.jl). Each measurement is Chairmarks' minimum time of a batch over all pairs of a set, sampled for
# BENCH_SECONDS (default 1) seconds. There are two rounds, the second in the opposite order, so
# the two minimums of each measurement show the noise.
include("libs.jl")
using Chairmarks: @b

const SECONDS = parse(Float64, get(ENV, "BENCH_SECONDS", "1"))
const SETS = ["random"]
const DATA = joinpath(@__DIR__, "..", "data")
const OUT = normpath(joinpath(@__DIR__, "..", "results", "timing.csv"))

# The pairs of a data file, as raw Float64s, and their number.
function read_set(case, set)
    _, na, nb = only(filter(c -> c[1] == case, CASES))
    raw = collect(reinterpret(Float64, read(joinpath(DATA, "$(case)_$(set).bin"))))
    raw, length(raw) ÷ (3 * (na + nb))
end

function main()
    runs = [(lib, case, set) for (lib, _) in LIBS for (case, _, _) in CASES for set in SETS]
    mkpath(dirname(OUT))
    open(OUT, "w") do io
        println(io, "round,lib,case,set,npairs,min_ns_per_pair")
        for (r, order) in ((1, runs), (2, reverse(runs)))
            for (lib, case, set) in order
                raw, n = read_set(case, set)
                out = zeros(n)
                batch = prepare(lib, case, raw)
                ns = (@b batch.run!(out) seconds = SECONDS).time * 1e9 / n
                batch.free()
                println(io, join((r, lib, case, set, n, ns), ","))
                flush(io)
                println("round $r  ", rpad(lib, 18), rpad(case, 11), rpad(set, 8), round(ns; sigdigits = 4), " ns/pair")
            end
        end
    end
    println("wrote ", OUT)
end

main()
