"""Exact certificates for direct finiteness in odd characteristic (Section 7 of the paper, Theorem C).

For p = 3, 5, 7, 11, 13, with q = p^5, in exact integer and rational arithmetic:
  * PG(2,p) and its blocks (complements of lines): every block has p^2 points and every extra
    letter lies in p^2 blocks;
  * the extra-plane vector z (Lemma 7.4): every line sum is divisible by p, beta(l) = 1 - (line sum)/p
    is an integer, z = M beta for the block matrix M, the values of z sum to p^2, they form p copies of
    each integer in {-u, ..., h} plus one kappa, and together with 1 - kappa they pair to sums 1;
  * the uniform family of Proposition 7.6 is positive: p^2 v - s(q+1) > 0;
  * the two row bounds of the Perron certificate (Lemma 7.8): A < rho and B < rho p^2,
    rho = 1 - 1/(2(q+1)).
Printed per prime: p, s = p^2+p+1, q, lam = rho, A_margin = rho - A, B_ratio = B/p^2.
Finally, for p = 3, the constant stated after the proof of Theorem C: with delta = -(1/4) log rho and
a_0 = 2 log(q+1) + 1, eps = min{1/4, delta/(16(1+a_0))} and the area constant 16/(13 eps) of Theorem B.
"""
from fractions import Fraction as Fr
from collections import Counter
import itertools
import math
def plane(p):
    pts=[]
    for x in range(p):
        for y in range(p): pts.append((x,y,1))
    for m in range(p): pts.append((m,1,0))
    pts.append((1,0,0))
    # lines = same normalized triples (duality); incidence dot=0 mod p
    return pts
def centered(x,p):
    x%=p; u=(p-1)//2
    return x if x<=u else x-p
def check(p):
    pts=plane(p); s=len(pts); assert s==p*p+p+1
    lines=pts
    N0=[[1 if sum(a*b for a,b in zip(P,L))%p==0 else 0 for L in lines] for P in pts]
    assert all(sum(r)==p+1 for r in N0)
    M=[[1-N0[i][j] for j in range(s)] for i in range(s)]
    u=(p-1)//2; h=(p+1)//2; R=p*u; tau=1-R
    z=[]
    for (x,y,w) in pts:
        if w==1: z.append(centered(x-h*(1 if y==0 else 0),p))
        elif (x,y,w)==(1,0,0): z.append(R)
        else: z.append(h)
    # line sums divisible by p
    lsum=[sum(N0[i][j]*z[i] for i in range(s)) for j in range(s)]
    assert all(t%p==0 for t in lsum), 'line sums'
    beta=[1-t//p for t in lsum]
    Mb=[sum(M[i][j]*beta[j] for j in range(s)) for i in range(s)]
    assert Mb==z, 'M beta = z'
    assert sum(z)==p*p
    ms=Counter(z); ms[tau]+=1
    assert all(ms[a]==ms[1-a] for a in ms) and all(ms[a]%2==0 for a in ms if 2*a==1), 'pairing'
    # expected multiset
    exp=Counter({j:p for j in range(-u,h+1)}); exp[R]+=1
    assert Counter(z)==exp, 'multiset'
    q=p**5; v=q*q+q+1; pi=Fr(q+1,v); gam=Fr(p-1,p); lam=1-Fr(1,2*(q+1))
    A=Fr(q,q+1)+s*pi**2+Fr(s*(p*p-1),(q+1)**2)
    B=(s-1)*gam**2+(v+s*(p*p-1))*pi**2
    assert A<lam and B<lam*p*p, 'perron'
    assert p*p*v - s*(q+1) > 0
    # each extra in p^2 complementary blocks; block size p^2; pair intersection p^2-p
    cols=[[M[i][j] for i in range(s)] for j in range(s)]
    assert all(sum(c)==p*p for c in cols)
    assert all(sum(M[i])==p*p for i in range(s))
    return dict(p=p,s=s,q=q,lam=lam,A_margin=float(lam-A),B_ratio=float(B/(p*p)))
for p in (3,5,7,11,13):
    print(check(p))
# Explicit constant for p = 3 (q = 243), stated after the proof of Theorem C.
q = 3**5
rho = 1 - Fr(1, 2*(q+1))
delta = -0.25*math.log(rho.numerator/rho.denominator)
a0 = 2*math.log(q+1) + 1
eps = min(0.25, delta/(16*(1+a0)))
area = 16/(13*eps)
print(f'p=3: rho={rho}, delta={delta:.6e}, a_0={a0:.4f}, eps={eps:.6e}, 16/(13 eps)={area:.1f}')
assert 2.46e-6 < eps < 2.47e-6 and area < 5.0e5, 'explicit constant for p = 3'
print('ALL PASS')
