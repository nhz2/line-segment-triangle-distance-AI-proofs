"""Exact rational certification of the numerical constants in the upper proof.
This is not an input search or a floating-point test of the distance routine.
"""
from fractions import Fraction as Q
from math import isqrt

SCALE = 10**12

def sqrt_up(x):
    x = Q(x)
    k = isqrt((x.numerator * SCALE*SCALE)//x.denominator)
    y = Q(k, SCALE)
    if y*y < x:
        y += Q(1, SCALE)
    assert y*y >= x
    return y

def hypot_up(x,y):
    return sqrt_up(x*x+y*y)

rho = Q(1,2**24)
# R/(rho D) bound using sqrt(3)>17/10 and the Float32 exponents.
remainder = Q(1,256)+Q(10,2176)+Q(1,2**43)
assert remainder < Q(1,100)
# (M-1)/rho has a power series with nonnegative coefficients,
# so its maximum over [0,2^-24] is attained at this endpoint.
M=(1+16*rho)*(1+rho)**4/(1-rho)**2*(1+4*rho)
assert 10*(M-1) <= 65536*rho

kappa = sqrt_up(Q(14,3))
lambda_ = sqrt_up(Q(25,6))
inv_sqrt3 = sqrt_up(Q(1,3))
U=1+rho
Vinv=1/(1-rho)
# Check the explicit envelope reductions at the largest unit roundoff.
assert (2+rho)+1+2*kappa*U**4+Vinv <= (2*kappa+4)*U**4*Vinv
face_first=kappa*U**3+1
face_second=lambda_*U**2*Vinv**2+(2-rho)*Vinv**2
face_envelope=(kappa+lambda_+3)*U**3*Vinv**2
assert max(2*face_first,face_first+face_second) <= face_envelope
rows = [
    ('point projection', kappa+lambda_+1, Q('5.22')),
    ('line parameter', 2*kappa+lambda_+2, Q('8.38')),
    ('face parameter', kappa+lambda_+3, Q('7.22')),
    ('reduced projection', Q(7), Q('7.02')),
    ('ordinary cross perturbations', 2+2*inv_sqrt3, Q('3.17')),
    ('face cross perturbations', 3+inv_sqrt3, Q('3.60')),
    ('plane height', 2*kappa+4, Q('8.34')),
    ('evaluation', Q('3.5'), Q('3.53')),
    ('face evaluation', Q(4), Q('4.03')),
]
for name, leading, allowance in rows:
    assert leading+remainder < allowance, name
    print(f'{name}: leading + remainder < {allowance}')

# Values are rigorous upper bounds, because sqrt_up is monotone and rounded up.
def J(z,c):
    return hypot_up(z+c,Q('7.02'))+c

def F(z):
    return hypot_up(J(z,Q('3.17')),Q('8.38'))

def V(z):
    return hypot_up(J(z,Q('3.60')),Q('7.22'))

def P(z):
    return max(V(z+Q('2.02'))+Q('4.03'),
               hypot_up(V(z+Q('2.02'))+Q('4.02'),Q('8.38'))+Q('3.53'))

p = P(Q(0))
l = F(Q('3.02'))+Q('3.53')
separated = Q('8.04')+max(p,l)
face = V(Q('8.34'))+Q('4.03')
crossing = F(V(Q('8.34'))+Q('5.02'))+Q('3.53')
assert p < Q('24.47')
assert l < 19
assert separated < Q('32.52')
for name,value in [('vertex-face',p),('segment-segment',l),
                   ('separated auxiliary pair',separated),
                   ('crossing face',face),('crossing edge fallback',crossing)]:
    assert value < Q('35.8'), (name,value)
    print(name, '<=', float(value))

# D=2sqrt(3)L; also reserve 1.01 rho D for an actually rounded sqrt.
assert 12*Q('36.81')**2 < 128**2
for r in (Q(1,2**24),Q(1,2**53)):
    assert 32**4*(2*r) < 1  # 32*eta^(1/4) < floatmin^(1/4)
print('All rational constant checks passed.')
