"""Constants for Section 6 of the paper: the girth-scale conditions (eq:c) for p = 3, and an alternative
analytic Perron certificate for the matrix M of Lemma 6.4 (weight 2e-1 in place of e+2).

Analytic claim: with f = 2e-1 on states t whose inverse tbar is extra, f = 1 otherwise,
  row O0 <= 1 - (q + e - 2e^2)/N,   row X <= 1 - (q + 3e - 2 - 2e^2)/N,   row O1 <= (e + 0.03)/(2e - 1),
for every q = p^k >= 2e(e+2), where N = (q+1)^2.  Here we check these against the exact rows.
"""
from fractions import Fraction as Fr
import math
from decay_quotient import certificate

def check(p, q):
    e = 2 * p - 1
    v = q * q + q + 1
    N = (q + 1) ** 2
    r = Fr(q + 1, v)
    T = v + e
    _, _, rows = certificate(q, e, 2 * e - 1)   # order: [O0, O1, X]
    b0 = 1 - Fr(q + e - 2 * e * e, N)
    bX = 1 - Fr(q + 3 * e - 2 - 2 * e * e, N)
    b1 = Fr(e * 100 + 3, 100 * (2 * e - 1))
    ok = rows[0] <= b0 and rows[2] <= bX and rows[1] <= b1 and max(b0, bX, b1) < 1
    return ok, [float(x) for x in rows], [float(b0), float(bX), float(b1)]

for p in [3, 5, 7, 11, 13, 17, 19, 23]:
    e = 2 * p - 1
    qs = []
    q = p
    while q < 2 * e * (e + 2):
        q *= p
    for k in range(4):
        qs.append(q * p ** k)
    for q in qs:
        ok, rows, bounds = check(p, q)
        print(f'p={p:2d} q={q:12d} analytic bounds hold and <1: {ok}   rows={[round(x,8) for x in rows]}  bounds={[round(x,8) for x in bounds]}')

# c-conditions for p = 3 (A pools nr/2): c*log(4|T|/r) < 1 and 2c*log(d_*) < 1, d_* = q + 1 + e
p, q, e = 3, 81, 5
v = q * q + q + 1; T = v + e; r = (q + 1) / v; dstar = q + 1 + e
print(f'p=3: |T|={T}, r={r:.8f}, d_*={dstar}; c < {1/math.log(4*T/r):.5f} and c < {1/(2*math.log(dstar)):.5f}; c = 1/100 ok: {0.01*math.log(4*T/r) < 1 and 0.02*math.log(dstar) < 1}')
print(f'    diameter lemma: r/k in [{(q+1)/2}, {(q+1)/2 + 0.5}] -> exponent r/k - 2 >= {(q+1)/2 - 2}')
# delta = 1/600 certificate with F = 9 (p = 3)
_, _, rows = certificate(81, 5, 9)
lam = max(rows)
sumf = T + 8 * e
a = -math.log(float(lam)) - 1 / 300
h0 = math.ceil((math.log(sumf) - math.log(float(lam))) / a)
print(f'p=3, F=9: lambda={float(lam):.10f}, sum f={sumf}: sum_W P(W)^2 <= sumf*lambda^(h-1) <= exp(-h/300) for h >= {h0}; 149/150={149/150:.10f}')
