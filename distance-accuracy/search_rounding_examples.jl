# Deterministic search used for rounding_examples.jl.
# julia --project=distance-accuracy --startup-file=no distance-accuracy/search_rounding_examples.jl
# Mutate integer vertices, recenter, and vary vertex/axis order. A fast floating
# intersection filter is followed by an exact certificate for every new best.
using SimplexCellLists, StaticArrays, Random, LinearAlgebra
function unpack(z)
    vs=ntuple(i->SVector(z[3i-2],z[3i-1],z[3i]),5)
    shift=-fld.(min.(vs...)+max.(vs...),2)
    x=SA[vs[1]+shift,vs[2]+shift];y=SA[vs[3]+shift,vs[4]+shift,vs[5]+shift]
    x,y
end
function hit(x,y)
    P=Float64.(x[2]-x[1]);E=Float64.(y[2]-y[1]);F=Float64.(y[3]-y[1]);R=Float64.(y[1]-x[1])
    N=cross(E,F);den=dot(N,P)
    t=dot(N,R)/den;u=dot(cross(F,R),P)/den;v=dot(cross(R,E),P)/den
    0<t<1 && u>0 && v>0 && u+v<1
end
function exacthit(x,y)
    P=BigInt.(x[2]-x[1]);E=BigInt.(y[2]-y[1]);F=BigInt.(y[3]-y[1]);R=BigInt.(y[1]-x[1])
    N=cross(E,F);den=dot(N,P)
    den==0 && return false
    t=dot(N,R)//den;u=dot(cross(F,R),P)//den;v=dot(cross(R,E),P)//den
    0<t<1 && u>0 && v>0 && u+v<1
end
function vscore(::Type{T},z) where T
    x,y=unpack(z)
    ell=maximum(v->maximum(abs,v),(x...,y...))
    ell <= (T == Float32 ? 2^24 : 2^53) || return -Inf
    hit(x,y) || return -Inf
    d2=dist_sqr_r_s_t(map(v->T.(v),x),map(v->T.(v),y))[1]
    sqrt(Float64(d2))/(Float64(eps(T))*ell)
end
function runsearch(::Type{T},n) where T
    rng=Xoshiro(T==Float32 ? 71032 : 71064)
    sc=T==Float32 ? 0 : 29
    seed = T == Float32 ? SVector{15,Int64}(-9371687,-7754511,-8416905,9780570,10196788,10057851,-10348299,-10332078,-10169968,10348299,7004759,9067020,9873649,10332079,10169968) : SVector{15,Int64}(-5305399339007970,-4197878618699932,-4564727400136850,4977993621024429,5474911713697635,5399940106562222,-5552362190545168,-5546991333408768,-5459960263606271,5552362190545168,3761752207528962,4726806124953601,5021360885063409,5546991333408768,5459960263606272)
    pool=fill(seed,64);scores=fill(vscore(T,seed),64);best=scores[1];bestz=seed
    for i in 1:n
        k=rand(rng,1:64);z=pool[k]
        p=rand(rng,0:(sc+15));j=rand(rng,1:15)
        z=setindex(z,z[j]+rand(rng,(-1,1))*(Int64(1)<<p),j)
        if rand(rng)<0.1
            mode=rand(rng,1:4)
            if mode==1
                ax=rand(rng,1:3)
                z=SVector{15,Int64}(ntuple(j-> mod1(j,3)==ax ? -z[j] : z[j],15))
            elseif mode==2
                ax,bx=rand(rng,1:3),rand(rng,1:3)
                z=SVector{15,Int64}(ntuple(j->z[j-mod1(j,3)+(mod1(j,3)==ax ? bx : mod1(j,3)==bx ? ax : mod1(j,3))],15))
            else
                a,b=mode==3 ? (1,2) : (rand(rng,3:5),rand(rng,3:5))
                z=SVector{15,Int64}(ntuple(j->z[3*((cld(j,3)==a ? b : cld(j,3)==b ? a : cld(j,3))-1)+mod1(j,3)],15))
            end
        end
        val=vscore(T,z)
        if val>best && exacthit(unpack(z)...)
            best,bestz=val,z
            println(T," best=",best," i=",i," z=",Tuple(z));flush(stdout)
        end
        if val>=scores[k] || rand(rng)<0.0005
            pool[k],scores[k]=z,val
        end
        if i%10000==0
            k=rand(rng,1:64);pool[k]=bestz;scores[k]=best
        end
    end
    x,y=unpack(bestz)
    println("FINAL ",T," ",best," x=",Tuple.(x)," y=",Tuple.(y))
    println("result=",dist_sqr_r_s_t(map(v->T.(v),x),map(v->T.(v),y)))
end
if abspath(PROGRAM_FILE)==@__FILE__
    n=isempty(ARGS) ? 50000000 : parse(Int,ARGS[1])
    runsearch(Float32,n)
    runsearch(Float64,n)
end
