# Run: julia --project=distance-accuracy --startup-file=no distance-accuracy/check_three_divide.jl
using SimplexCellLists, StaticArrays, LinearAlgebra, Random, Test, SHA
const R = Rational{BigInt}
proj(n, d) = iszero(d) ? zero(n) : clamp(n/d, zero(n), one(n))
function reference(x, y)
    p, q, r = x[2]-x[1], y[2]-y[1], y[1]-x[1]
    a,b,c,d,e = dot(p,p),dot(p,q),dot(q,q),dot(p,r),dot(q,r)
    candidates = [(zero(a),proj(-e,c)), (one(a),proj(b-e,c)),
                  (proj(d,a),zero(a)), (proj(d+b,a),one(a))]
    det = a*c-b*b
    if det > 0
        s,t = (c*d-b*e)/det,(b*d-a*e)/det
        if 0 <= s <= 1 && 0 <= t <= 1
            push!(candidates,(s,t))
        end
    end
    minimum(dot(r+t*q-s*p,r+t*q-s*p) for (s,t) in candidates)
end
function certified_reference(x, y)
    d2,r,s,t = dist_sqr_r_s_t(x,y)
    X,Y = sum(x .* [1-sum(s);s]),sum(y .* [1-sum(t);t])
    @assert all(>=(0),s) && sum(s) <= 1
    @assert all(>=(0),t) && sum(t) <= 1
    @assert r == Y-X && d2 == dot(r,r)
    # Exact supporting-plane optimality certificate, independent of the solver.
    @assert all(p -> dot(p-X,r) <= 0,x)
    @assert all(q -> dot(q-Y,r) >= 0,y)
    d2
end
function main(n=10000)
    rng = Xoshiro(0x3d171de)
    src = joinpath(dirname(pathof(SimplexCellLists)), "distances.jl")
    println("source = ",src,"\nsha256 = ",bytes2hex(sha256(read(src))))
    for T in (Float32,Float64)
        worst = 0.0
        for i in 1:n
            v() = SVector{3,T}(randn(rng,3))
            a,p,q,r = v(),v(),v(),v()
            mode = i % 6
            if mode == 0
                q = T(randn(rng))*p + T(2.0^(-rand(rng,1:60)))*q
            elseif mode == 1
                r = T(rand(rng))*p - T(rand(rng))*q
            elseif mode == 2
                p = zero(p)
            elseif mode == 3
                q = T(randn(rng))*p
            elseif mode == 4
                p *= T(2.0^(-rand(rng,1:60)))
            end
            exponent = T == Float32 ? rand(rng,-70:25) : rand(rng,-530:245)
            scale = T(2)^exponent
            x,y = SA[a*scale,(a+p)*scale], SA[(a+r)*scale,(a+r+q)*scale]
            xr,yr = map(z->R.(z),x),map(z->R.(z),y)
            exact = reference(xr,yr)
            @test dist_sqr_r_s_t(xr,yr)[1] == exact
            d2,sep,s,t = dist_sqr_r_s_t(x,y)
            @test isfinite(d2) && 0 <= s[1] <= 1 && 0 <= t[1] <= 1
            ell = maximum(z->maximum(abs,z), (x...,y...))
            err = abs(sqrt(BigFloat(d2))-sqrt(BigFloat(exact)))
            budget = 64BigFloat(eps(T))*ell + sqrt(sqrt(BigFloat(floatmin(T))))
            @test err <= budget
            worst = max(worst, Float64(err/budget))
        end
        println(T,": ",n," cases; maximum error / full bound = ",worst)
        for N in (2,3)
            worst = 0.0
            count = max(1,div(n,10))
            for i in 1:count
                v() = SVector{3,T}(randn(rng,3))
                a,p,q = v(),v(),v()
                thin = T(2.0^(-rand(rng,1:(T == Float32 ? 35 : 65))))
                y = SA[a,a+p,a+T(rand(rng))*p+thin*q]
                hit = a+T(0.3)*p+T(0.3)*thin*q
                direction = v()
                x = N == 2 ? SA[hit-direction,hit+direction] :
                    SA[hit-direction,hit+direction,hit+v()]
                if i % 4 == 0
                    x = map(z -> z+q,x)
                end
                exponent = T == Float32 ? rand(rng,-70:25) : rand(rng,-530:245)
                scale = T(2)^exponent
                x,y = x .* scale,y .* scale
                exact = certified_reference(map(z->R.(z),x),map(z->R.(z),y))
                d2 = dist_sqr_r_s_t(x,y)[1]
                @test isfinite(d2)
                ell = maximum(z->maximum(abs,z),(x...,y...))
                err = abs(sqrt(BigFloat(d2))-sqrt(BigFloat(exact)))
                budget = 64BigFloat(eps(T))*ell+sqrt(sqrt(BigFloat(floatmin(T))))
                @test err <= budget
                worst = max(worst,Float64(err/budget))
            end
            println(T,": ",count," ",N,"-vertex/triangle cases; maximum error / full bound = ",worst)
        end
    end
    println("Exact reference and floating-point checks passed. Sampling is not a proof.")
end
main(isempty(ARGS) ? 10000 : parse(Int,ARGS[1]))
