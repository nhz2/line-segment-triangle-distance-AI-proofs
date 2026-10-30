using SimplexCellLists, StaticArrays, LinearAlgebra, Test
q=SA[40353,33795,37499];r=SA[39420,40281,39649]
n=513;i=2;j=501;w=SA[299254,280491,288668];k=63;m=64
A=SA[0,0,0];B=n*q;C=n*r;P=i*q+j*r
P0=P-k*w;P1=P+(m-k)*w
shift=-div.(min.(A,B,C,P0,P1)+max.(A,B,C,P0,P1),2)
A+=shift;B+=shift;C+=shift;P+=shift;P0+=shift;P1+=shift
@assert 513*P==10*A+2*B+501*C
@assert 64*P==P0+63*P1
@assert maximum(v->maximum(abs,v),(A,B,C,P0,P1))<=2^24
x=SA[Float32.(P0),Float32.(P1)];y=SA[Float32.(A),Float32.(B),Float32.(C)]
result=dist_sqr_r_s_t(x,y);d2,rr,s,t=result
ell=maximum(v->maximum(abs,v),(A,B,C,P0,P1))
R=Rational{BigInt};unit=R(eps(Float32))*ell
@assert R(d2) == BigInt(4181413)//32768  # q used by Counterexample.lean
@assert R(d2)>(R(9155)//1000*unit)^2
# H=2^(-31.5)<2^(-31), so this also disproves constant 9 with H included.
@assert R(d2) > (9*unit + BigInt(1)//2^31)^2
@assert ell < 2^29  # safely below floatmax(Float32)^(1/4)/4
println("A=",A,"\nB=",B,"\nC=",C,"\nP0=",P0,"\nP1=",P1,"\nP=",P)
println("result=",result,"\nell=",ell,"\nd2 exact=",R(d2))
setprecision(256) do
 d=sqrt(BigFloat(d2));println("distance=",d,"\ncoefficient=",d/BigFloat(unit),"\nbound64=",64BigFloat(unit)+sqrt(sqrt(BigFloat(floatmin(Float32)))))
end
println("Exact certificate passed: d = 0 and returned root distance > 9.155 eps(Float32)*ell.")
