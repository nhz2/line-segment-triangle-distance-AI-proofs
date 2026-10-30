# Record a run: write results/runs/<YYYY-MM-DD-HHMM>.md, named by the local time now, with
# versioninfo() (which names the CPU), the commit of this repository, and one table of
# results/accuracy.csv and results/timing.csv. Run from library-comparison right after
# harness/accuracy.jl and harness/bench.jl, with
#
#     julia --project=. harness/record.jl
#
# It refuses to overwrite a record, so wait a minute between runs.
using InteractiveUtils: versioninfo
using Pkg: Pkg
using Printf: @sprintf

const RESULTS = normpath(joinpath(@__DIR__, "..", "results"))
const RUNS = joinpath(RESULTS, "runs")
const HERE = normpath(joinpath(@__DIR__, ".."))

# The header and the rows of a CSV file with no quoted fields.
function read_csv(path)
    lines = readlines(path)
    split(lines[1], ","), [split(l, ",") for l in lines[2:end] if !isempty(l)]
end

# A CSV field for a table: integers as they are, other numbers to 4 significant digits.
function cell(s)
    tryparse(Int, s) !== nothing && return s
    x = tryparse(Float64, s)
    x === nothing ? s : @sprintf("%.4g", x)
end

# A markdown table padded to line up in plain text: the first `ntext` columns left aligned,
# the rest, numbers, right aligned.
function print_table(io, head, rows; ntext)
    w = [maximum(textwidth, [head[j]; [r[j] for r in rows]]) for j in eachindex(head)]
    pad(s, j) = j <= ntext ? rpad(s, w[j]) : lpad(s, w[j])
    line(cells) = println(io, "| ", join((pad(c, j) for (j, c) in enumerate(cells)), " | "), " |")
    line(head)
    println(io, "|", join((j <= ntext ? ":" * "-"^(w[j] + 1) : "-"^(w[j] + 1) * ":" for j in eachindex(w)), "|"), "|")
    foreach(line, rows)
end

function main()
    t = time()
    out = joinpath(RUNS, Libc.strftime("%Y-%m-%d-%H%M", t) * ".md")
    ispath(out) && error("$out exists")

    repo = readchomp(`git -C $HERE rev-parse --show-toplevel`)
    commit = readchomp(`git -C $repo rev-parse HEAD`)
    status = readchomp(`git -C $repo status --short`)
    scl = only(p for p in values(Pkg.dependencies()) if p.name == "SimplexCellLists")

    acc_head, acc = read_csv(joinpath(RESULTS, "accuracy.csv"))
    _, tim = read_csv(joinpath(RESULTS, "timing.csv"))
    # timing.csv columns: round, lib, case, set, npairs, min_ns_per_pair.
    ns = Dict((r[1], r[2], r[3], r[4]) => r[6] for r in tim)
    rounds = sort(unique(r[1] for r in tim))

    mkpath(RUNS)
    open(out, "w") do io
        println(io, "# Run of ", Libc.strftime("%Y-%m-%d %H:%M %Z", t), "\n")
        println(io, "## Commit\n")
        println(io, "`", commit, "`", isempty(status) ? "" : ", with uncommitted changes:", "\n")
        isempty(status) || println(io, "```\n", status, "\n```\n")
        println(io, "SimplexCellLists.jl: `", scl.git_source, "` at `", scl.git_revision, "`\n")
        println(io, "## versioninfo()\n")
        println(io, "```")
        versioninfo(io)
        println(io, "```\n")
        println(io, "## Results\n")
        println(io, "From `results/accuracy.csv` and `results/timing.csv`. `ns_r<k>` is the minimum ns per")
        println(io, "pair in timing round k, `-` where the set is not timed. `median`, `p99` and `max` are")
        println(io, "errors as a fraction of the bound `64*eps*ℓ + floatmin^(1/4)`, so over 1 is outside it;")
        println(io, "see `README.md`.\n")
        # accuracy.csv columns: lib, case, set, then the measures. Sort by set, case, then lib,
        # each in the order it first appears in accuracy.csv, and put those columns first.
        rank(j) = (o = unique(r[j] for r in acc); v -> findfirst(==(v), o))
        rlib, rcase, rset = rank(1), rank(2), rank(3)
        sort!(acc; by = r -> (rset(r[3]), rcase(r[2]), rlib(r[1])))
        head = vcat(acc_head[[3, 2, 1]], ["ns_r$r" for r in rounds], acc_head[4:end])
        rows = [vcat(r[[3, 2, 1]], [cell(get(ns, (k, r[1], r[2], r[3]), "-")) for k in rounds], cell.(r[4:end]))
                for r in acc]
        print_table(io, head, rows; ntext = 3)
    end
    println("wrote ", out)
end

main()
