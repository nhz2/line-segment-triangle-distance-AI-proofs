# Build the library shims into build/lib. Run from this directory with
#
#     julia --project=. build.jl
#
# It downloads the pinned library sources into build/src (checking their SHA-256), gets the
# GMP and MPFR headers and libraries from Julia's artifacts, and compiles each shim with
# Clang_jll. Each step is skipped when its output is up to date, so
# running it again is cheap (a shim is rebuilt when its source is newer than its library;
# delete build/lib to rebuild after changing flags here). It ends by printing the version of
# every tool and library.
using Clang_jll, boost_jll
using Downloads: download
using SHA: sha256
using Pkg.Artifacts: artifact_hash, ensure_artifact_installed, artifact_path
using Base.BinaryPlatforms: HostPlatform

const ROOT = @__DIR__
const BUILD = joinpath(ROOT, "build")
const SRC = joinpath(BUILD, "src")    # downloaded sources
const LIB = joinpath(BUILD, "lib")    # the built shims
const SHIMS = joinpath(ROOT, "shims")

# Clang_jll's clang has no C++ standard library of its own, so it uses the system's gcc-11
# libstdc++ headers (and the system linker). The shims link libstdc++ statically.
const GCC_INSTALL_DIR = "/usr/lib/gcc/x86_64-linux-gnu/11"

# Pinned sources: the directory each tarball unpacks to, its URL and its SHA-256.
const SOURCES = [
    ("CGAL-6.2.1",
     "https://github.com/CGAL/cgal/releases/download/v6.2.1/CGAL-6.2.1-library.tar.xz",
     "8e7ce1e30e8ffcb3e69d153c3a561bb1f38bbb4becd8e6544cbaa0fb2889af62"),
    ("GeometricTools-e09f5b39a33da6b4bfd0ff8dbb64ddcb7fdfc763",
     "https://github.com/davideberly/GeometricTools/archive/e09f5b39a33da6b4bfd0ff8dbb64ddcb7fdfc763.tar.gz",
     "0aab5288ef68c4e0e99ef228f88a8bb8d8bf1932f322f2d5c054d03706eae41d"),
]

# Download and unpack a source tarball into SRC/dir, unless it is there already.
function fetch_source(dir, url, sha)
    dest = joinpath(SRC, dir)
    isdir(dest) && return dest
    println("downloading ", url)
    mkpath(SRC)
    tmp = mktempdir(SRC)
    tarball = download(url, joinpath(tmp, basename(url)))
    got = open(io -> bytes2hex(sha256(io)), tarball)
    got == sha || error("SHA-256 of $url is $got, expected $sha")
    run(`tar -xf $tarball -C $tmp`)
    mv(joinpath(tmp, dir), dest)
    rm(tmp; recursive = true)
    dest
end

# Copy the full GMP or MPFR artifact (with include/ and lib/) that Julia's stdlib lists into
# build/deps/<name>, unless it is there already. The stdlib itself only ships the shared
# library, without headers. The copy is needed as no manifest refers to the artifact, so
# Pkg's garbage collection may delete it.
function install_stdlib_artifact(name)
    dest = joinpath(BUILD, "deps", name)
    isdir(dest) && return dest
    toml = joinpath(Sys.STDLIB, "$(name)_jll", "StdlibArtifacts.toml")
    ensure_artifact_installed(name, toml; platform = HostPlatform())
    mkpath(dirname(dest))
    cp(artifact_path(artifact_hash(name, toml; platform = HostPlatform())), dest)
    dest
end

# True if `out` is missing or older than any of `inputs`.
stale(out, inputs...) = !isfile(out) || any(f -> mtime(f) > mtime(out), inputs)

const CLANG = Clang_jll.clang()
# No -ffast-math. -fvisibility=hidden exports only the shims' batch functions.
const COMMON_FLAGS = `-O3 -march=native -DNDEBUG -shared -fPIC -fvisibility=hidden -Wl,--no-undefined`

# Compile one C++ translation unit into a shared library. libstdc++ is linked statically, and
# --exclude-libs keeps its symbols out of the library's exports, so they can't mix with the
# libstdc++ Julia has loaded.
function compile_cxx(src, out, flags)
    stale(out, src, joinpath(SHIMS, "batch.hpp")) || return
    println("building ", basename(out))
    run(`$CLANG --driver-mode=g++ -std=c++17 --gcc-install-dir=$GCC_INSTALL_DIR $COMMON_FLAGS
         -static-libstdc++ -static-libgcc -Wl,--exclude-libs,ALL $flags $src -o $out`)
end

# Stop early, naming what is missing, if something that Julia's package manager can't install is
# absent. See "Requirements outside Julia" in README.md.
function check_requirements()
    problems = String[]
    (VERSION.major, VERSION.minor) == (1, 13) ||
        push!(problems, "Julia 1.13, whose LLVM Clang_jll 20.1.8 matches (this is Julia $VERSION)")
    for file in ("crtbeginS.o", "libstdc++.a")
        isfile(joinpath(GCC_INSTALL_DIR, file)) ||
            push!(problems, "$file in $GCC_INSTALL_DIR: install libstdc++-11-dev and libgcc-11-dev, or set GCC_INSTALL_DIR")
    end
    isfile("/usr/include/stdio.h") || push!(problems, "the C library headers: install libc6-dev")
    for (tool, install) in (("ld", "binutils"), ("tar", "tar"), ("xz", "xz-utils"))
        Sys.which(tool) === nothing && push!(problems, "$tool: install $install")
    end
    isempty(problems) || error("missing requirements (see README.md):\n  " * join(problems, "\n  "))
end

function build()
    check_requirements()
    mkpath(LIB)
    cgal, gte = (fetch_source(s...) for s in SOURCES)
    gmp, mpfr = install_stdlib_artifact("GMP"), install_stdlib_artifact("MPFR")
    boost = boost_jll.artifact_dir

    # CGAL, header only. It enables GMP and MPFR when it finds their headers. -isystem hides
    # warnings from library headers. GMP and MPFR come as shared libraries only, so link
    # those, with an rpath relative to build/lib. (Inside Julia, the libgmp Julia has loaded,
    # the same version, is used.)
    cgal_flags = `-isystem $cgal/include -isystem $boost/include -isystem $gmp/include -isystem $mpfr/include
                  -L$gmp/lib -L$mpfr/lib -Wl,-rpath,\$ORIGIN/../deps/GMP/lib -Wl,-rpath,\$ORIGIN/../deps/MPFR/lib
                  -lmpfr -lgmp`
    compile_cxx(joinpath(SHIMS, "cgal.cpp"), joinpath(LIB, "libcgal_epick.so"), cgal_flags)
    compile_cxx(joinpath(SHIMS, "cgal.cpp"), joinpath(LIB, "libcgal_epeck.so"), `-DEXACT $cgal_flags`)

    # Geometric Tools, header only.
    compile_cxx(joinpath(SHIMS, "gte.cpp"), joinpath(LIB, "libgte_robust.so"), `-isystem $gte/GTE`)

    print_versions(; cgal, gte, gmp, mpfr, boost)
end

function print_versions(; cgal, gte, gmp, mpfr, boost)
    first_line(cmd) = first(eachline(cmd))
    header_define(file, name) = strip(match(Regex("#define $name\\s+(\\S+)"), read(file, String))[1], '"')
    println("\nVersions")
    println("  julia      ", VERSION)
    println("  clang      ", first_line(`$CLANG --version`), " (Clang_jll ", pkgversion(Clang_jll), ")")
    println("  libstdc++  gcc 11's, from ", GCC_INSTALL_DIR)
    println("  boost      ", header_define("$boost/include/boost/version.hpp", "BOOST_LIB_VERSION"), " (boost_jll ", pkgversion(boost_jll), ")")
    gmp_h = "$gmp/include/gmp.h"
    println("  GMP        ", join((header_define(gmp_h, "__GNU_MP_VERSION" * s) for s in ("", "_MINOR", "_PATCHLEVEL")), "."))
    println("  MPFR       ", header_define("$mpfr/include/mpfr.h", "MPFR_VERSION_STRING"))
    println("  CGAL       ", header_define("$cgal/include/CGAL/version.h", "CGAL_VERSION"))
    println("  ", basename(gte))
end

build()
