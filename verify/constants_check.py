#!/usr/bin/env python3
"""Exact checks of the numerical bookkeeping in Section 3 (equations (2), (3), Lemmas 3.5, 3.6),
Proposition 4.4 and Corollary 5.4 of
"Kaplansky's conjectures fail for torsion-free hyperbolic groups in positive characteristic".

What is checked (exact rational arithmetic; C_sep with 60-digit decimals):
  (3)    3*D0/U <= eps/32,  2*eta*U <= 1/16,  2*eta*U <= eps/32,  C_sep/sqrt(K0) <= eta
         for the choices (2), over a grid of eps in (0,1] and D0 in 1..300;
  Prop 4.4 bookkeeping:
         2*D0/U + 2*eta*U <= eps/16,   1 - 2*eta*U >= 15/16,
         (L/192) * (12*H0/L) = H0/16,  6(k'+1) <= 12k' for k' >= 1,
         15/16 - 1/16 - 1/16 = 13/16, and the conclusion of the chain (6);
  Splitting: for every integer UL in [6, 400] and every h in (UL, 12*UL],
         m = ceil(h/UL) segments of lengths differing by at most one have
         lengths in [UL/3, UL], and m <= 2h/UL.
  Interval-pair cutoff: I_Z <= 192*H_Z/L and H_Z <= C*L give I_Z <= 192*C <= I.
These are elementary; the script exists so that a reader can re-run them.
"""
from fractions import Fraction as Fr
from decimal import Decimal, getcontext
import math, itertools

getcontext().prec = 60
CSEP = Decimal(2) * Decimal(2).sqrt() / (Decimal(1) - (Decimal(2) / Decimal(3)).sqrt())

def ceil_fr(x: Fr) -> int:
    return -((-x.numerator) // x.denominator)

def constants(eps: Fr, D0: int):
    U = max(3, ceil_fr(96 * D0 / eps))
    eta = min(Fr(1, 32 * U), eps / (64 * U))
    # K0 = max(1, ceil((C_sep/eta)^2)), computed with high-precision decimals
    q = (CSEP / (Decimal(eta.numerator) / Decimal(eta.denominator))) ** 2
    K0 = max(1, int(q.to_integral_value(rounding="ROUND_CEILING")))
    C = K0 * (U + D0)
    I = math.ceil(192 * C)
    return U, eta, K0, C, I

eps_grid = [Fr(1), Fr(1, 2), Fr(1, 3), Fr(3, 7), Fr(1, 10), Fr(1, 64), Fr(1, 97),
            Fr(1, 1000), Fr(7, 10**5), Fr(1, 10**6)]
D_grid = list(range(1, 301))
n = 0
for eps, D0 in itertools.product(eps_grid, D_grid):
    U, eta, K0, C, I = constants(eps, D0)
    assert Fr(3 * D0, U) <= eps / 32
    assert 2 * eta * U <= Fr(1, 16)
    assert 2 * eta * U <= eps / 32
    etaD = Decimal(eta.numerator) / Decimal(eta.denominator)
    assert CSEP / Decimal(K0).sqrt() <= etaD
    # Prop 4.4 (unified count; deleted occurrences bounded by 2*eta*U*H)
    assert Fr(2 * D0, U) + 2 * eta * U <= eps / 16
    assert 1 - 2 * eta * U >= Fr(15, 16)
    assert 192 * C <= I
    n += 1
print(f"(3) and Prop 4.4 constant inequalities: OK on {n} (eps, D0) pairs")

# generic identities
assert Fr(15, 16) - Fr(1, 16) - Fr(1, 16) == Fr(13, 16)
for kp in range(1, 10**4):
    assert 6 * (kp + 1) <= 12 * kp
print("15/16 - 1/16 - 1/16 = 13/16 and 6(k'+1) <= 12k' (k' >= 1): OK")

# The chain (6) of Prop 4.4: if |w| < (13/16) eps H0 then the good clusters have positive length.
for eps in eps_grid:
    for H0 in (Fr(1), Fr(37), Fr(1000)):
        for frac in (Fr(0), Fr(1, 2), Fr(99, 100)):
            w = frac * Fr(13, 16) * eps * H0
            good_lower = Fr(15, 16) * H0 - (H0 / 16 + w / eps) - H0 / 16
            assert good_lower == Fr(13, 16) * H0 - w / eps and good_lower > 0
print("chain (6): |w| < (13/16) eps H0 forces a good cluster: OK")

# splitting
cnt = 0
for UL in range(6, 401):
    for h in range(UL + 1, 12 * UL + 1):
        m = -(-h // UL)
        lo, hi = h // m, -(-h // m)
        assert Fr(UL, 3) <= lo and hi <= UL, (UL, h)
        assert m <= Fr(2 * h, UL)
        cnt += 1
print(f"splitting into segments of length in [UL/3, UL], m <= 2h/UL: OK on {cnt} cases")
# Prop 4.4, interval count: rooted case 6k' with k'L <= 2H; free case 6(k'+1) with k'L <= H
for L in range(3, 60):
    for H in range(L, 40 * L):
        for kp in range(1, 2 * H // L + 1):           # rooted: k'L <= 2H
            assert Fr(6 * kp) <= Fr(12 * H, L)
        for kp in range(1, H // L + 1):               # free/spherical: k'L <= H
            assert Fr(6 * (kp + 1)) <= Fr(12 * H, L)
print("interval-pair count <= 12H/L in the rooted, free and spherical cases: OK")
assert Fr(13, 16) - Fr(1, 2) == Fr(5, 16) > 0
print("rooted case: 13/16 - 1/2 = 5/16 > 0: OK")

# Lemma 3.6: k = ceil(log2|V|)+1 <= lambda*L + 2 when log2|V| <= lambda*L, and
# 3*2^(k-1) > |V|; added length d*L + 4k <= D0*L with D0 = ceil(d + 4*lambda + 8)
for V in range(2, 5000):
    k = math.ceil(math.log2(V)) + 1
    assert 3 * 2 ** (k - 1) > V
    for L in (1, 2, 3, 7, 20):
        lam = Fr(math.ceil(math.log2(V) * 1000) + 1, 1000 * L)   # any lambda with log2 V <= lambda L
        assert math.log2(V) <= lam * L
        assert k <= lam * L + 2
        for d in (1, 2, 5, 40):
            D0 = math.ceil(d + 4 * lam + 8)
            assert d * L + 4 * k <= D0 * L
print("Lemma 3.6 arithmetic (walk count, D0 = ceil(d + 4 lambda + 8)): OK")

# Lemma 3.5: with L = floor(c0 ln n) and lambda = 1 + 2/(c0 ln 2), log2(2n) <= lambda L once ln n >= 2/c0
for c0 in (Fr(1, 100), Fr(1, 20), Fr(1, 3)):
    lam = 1 + 2 / (float(c0) * math.log(2))
    for t in [2 / float(c0) * (1 + j / 50) for j in range(0, 2000)]:   # t = ln n
        L = math.floor(float(c0) * t)
        if L < 3: continue
        assert math.log2(2) + t / math.log(2) <= lam * L + 1e-9
print("Lemma 3.5: log2|V| <= lambda L for |V| <= 2n and ln n >= 2/c0: OK")

# Corollary 5.4: Lean's eps = StageFusion.epsilon (1/600) 256 = min(1/4, (1/600)/(16*(1+256)))
eps_star = min(Fr(1, 4), Fr(1, 600) / (16 * 257))
assert eps_star == Fr(1, 2467200)
const = Fr(16, 13) / eps_star
assert const == Fr(39475200, 13) and const < 3036554
print(f"Corollary 5.4: eps* = 1/2467200 and 16/(13 eps*) = {float(const):.2f} < 3,036,554: OK")
print("ALL CHECKS PASSED")
