using Test
const half = 1//2
const signs4 = collect(Iterators.product(ntuple(_ -> (-1,1),4)...))
const signs5 = collect(Iterators.product(ntuple(_ -> (-1,1),5)...))
function seginterior(p0,p1,q0,q1,s,t)
 x=(1-s)*p0+s*p1;y=(1-t)*q0+t*q1
 abs(q0-p0)+t*abs(q1-q0)+s*abs(p1-p0)+abs(y-p0)+abs(y-x)
end
for (sr,tr,want) in (((0,half),(0,half),6),((0,half),(half,1),7),((half,1),(0,half),7),((half,1),(half,1),8))
 got=maximum(seginterior(v...,s,t) for v in signs4 for s in sr for t in tr)
 @test got<=want
 println("segment interior ",sr," ",tr,": ",got)
end
function bc(a,b,c,x,t)
 abs(a-x)+(1-t)*abs(b-a)+t*abs(c-a)+abs(b-x)+t*abs(c-b)+abs((1-t)*b+t*c-x)
end
function segend(p0,p1,q0,q1,t)
 y=(1-t)*q0+t*q1
 abs(q0-p0)+abs(p1-p0)+t*abs(q1-q0)+abs(q0-p1)+abs(y-p1)
end
for f in (bc,segend), (tr,want) in (((0,half),7),((half,1),8))
 got=maximum(f(v...,t) for v in signs4 for t in tr)
 @test got<=want
 println(f," ",tr,": ",got," <= ",want)
end
function crossing(a,b,c,p0,p1,s,u,v)
 x=(1-s)*p0+s*p1
 abs(a-p0)+s*abs(p1-p0)+u*abs(b-a)+v*abs(c-a)+abs(a-x)+abs(a+u*(b-a)-x)+abs(a+u*(b-a)+v*(c-a)-x)
end
for s in (0,half), (u,v) in ((0,0),(1,0),(0,1))
 got=maximum(crossing(q...,s,u,v) for q in signs5)
 @test got<=8
 println("crossing ",(s,u,v),": ",got)
end
setprecision(256) do
 rho=BigFloat(2)^(-24)
 for c in (8sqrt(BigFloat(3)),9sqrt(BigFloat(3)),8sqrt(BigFloat(3))+2,4sqrt(BigFloat(3))+sqrt(60+50000rho))
  coefficient=c+4096sqrt(BigFloat(3))*rho
  @test coefficient<16
  println("coefficient: ",coefficient)
 end
end
