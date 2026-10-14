"""Engine 1: squared-word decay via the exact 3x3 equitable quotient of M = w^2.

Letter classes:
  O0 = ordinary letters paired with ordinary letters   (v - e of them)
  O1 = ordinary letters paired with extras              (e of them)
  X  = extra letters (paired with O1)                   (e of them)
Turn weight w(t,u) depends on whether tbar / u are ordinary or extra (B side):
  tbar ord, u ord (u != tbar): 1/(q+1);  tbar ord, u extra: r;
  tbar extra, u ord: r;                  tbar extra, u extra (u != tbar): 1;  u = tbar: 0.
Row class of t: t in O0 -> tbar in O0 (ord); t in O1 -> tbar in X (extra); t in X -> tbar in O1 (ord).
Sum over u in a class of M[t,u] is constant on the row class (equitable partition), so the
Perron root of M equals the Perron root of the 3x3 quotient Q.
"""
from fractions import Fraction as Fr
import sympy as sp
import mpmath as mp

mp.mp.dps = 50


def quotient(q, e):
    v = q * q + q + 1
    r = Fr(q + 1, v)
    N = (q + 1) ** 2
    O0 = v - e
    # order: [O0, O1, X]
    Q = [[Fr(O0 - 1, N), Fr(e, N), e * r * r],      # t in O0  (tbar ordinary, in O0)
         [O0 * r * r,   e * r * r, Fr(e - 1)],       # t in O1  (tbar extra)
         [Fr(O0, N),    Fr(e - 1, N), e * r * r]]    # t in X   (tbar ordinary, in O1)
    return v, r, Q


def perron(Q):
    M = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in row] for row in Q])
    lam = sp.symbols('lam')
    cp = sp.Poly(M.charpoly(lam).as_expr(), lam)
    roots = [complex(z) for z in sp.Poly(cp, lam).nroots(n=40)]
    rho = max(abs(z) for z in roots)
    return cp, rho


def certificate(q, e, F):
    """f = F on O1 states (tbar extra), 1 elsewhere.  Returns exact row ratios (Mf)(t)/f(t)."""
    v, r, Q = quotient(q, e)
    f = [Fr(1), Fr(F), Fr(1)]
    rows = []
    for i in range(3):
        s = sum(Q[i][j] * f[j] for j in range(3))
        rows.append(s / f[i])
    return v, r, rows


def smallest_admissible_q(p):
    e = 2 * p - 1
    q = p
    while q < 2 * e * (e + 2):
        q *= p
    return q


if __name__ == '__main__':
    print('=== Sanity: OpenAI char-2 design q=128, e=3 (paper claims Mf <= (149/150) f with F=5) ===')
    v, r, rows = certificate(128, 3, 5)
    print('v =', v, ' rows (Mf)/f =', [float(x) for x in rows])
    print('exact rows:', rows)
    print('max row < 149/150 ?', max(rows) < Fr(149, 150))
    # compare with the two fractions printed in the paper (their bounds were upper bounds)
    print('paper fraction 1 =', 500731261911 / 504183783481, ' paper fraction 2 =', 820350863 / 1363395845)
    _, _, Q = quotient(128, 3)
    cp, rho = perron(Q)
    print('Perron root rho(M) for OpenAI design =', rho)

    print()
    print('=== New design: e = 2p-1 extras, q = smallest power of p with q >= 2e(e+2) ===')
    for p in [3, 5, 7, 11, 13]:
        e = 2 * p - 1
        q = smallest_admissible_q(p)
        v, r, Q = quotient(q, e)
        cp, rho = perron(Q)
        T = v + e
        out = [f'p={p} e={e} q={q} v={v} |T|={T} r={r}']
        out.append(f'  Perron root rho(M) = {rho:.12f}   -> admissible delta < -log(rho)/2 = {-mp.log(rho)/2}')
        for F in [2 * e - 1, 2 * e]:
            _, _, rows = certificate(q, e, F)
            lam = max(rows)
            sumf = T + (F - 1) * e
            out.append(f'  certificate F={F}: rows = {[round(float(x), 9) for x in rows]}  max = {float(lam):.9f}  sum f = {sumf}')
        print('\n'.join(out))
    print()
    print('=== p=3 exact data ===')
    v, r, Q = quotient(81, 5)
    print('Q (exact) =')
    for row in Q:
        print('  ', row)
    cp, rho = perron(Q)
    print('char poly:', cp.as_expr())
    print('rho =', rho)
    v, r, rows = certificate(81, 5, 9)
    print('F=9 rows exact:', rows, [float(x) for x in rows])
    lam = max(rows)
    sumf = v + 5 + 8 * 5
    print('sum f =', sumf, ' lambda =', lam, float(lam))
    # find h0 with sumf*lam^(h-1) <= exp(-h/K) for a clean delta
    import math
    for K in [20, 25, 30, 40, 50, 60, 100]:
        # need log(sumf) + (h-1)log(lam) <= -h/K  <=>  h*(-log lam - 1/K) >= log(sumf) - log(lam)
        a = -math.log(float(lam)) - 1.0 / K
        if a > 0:
            h0 = math.ceil((math.log(sumf) - math.log(float(lam))) / a)
            print(f'  sum_W P(W)^2 <= exp(-h/{K}) for h >= {h0}  (delta = 1/{2*K})')

    print()
    print('=== Threshold: smallest power of p with rho < 1, and real threshold in q (for information) ===')
    for p in [3, 5, 7, 11, 13]:
        e = 2 * p - 1
        q = p
        while True:
            _, _, Q = quotient(q, e)
            _, rho = perron(Q)
            if rho < 1:
                break
            q *= p
        # real threshold by scanning integer q (formula valid for any integer q as a kernel)
        lo = 2
        qq = 2
        while True:
            _, _, Q = quotient(qq, e)
            _, rho2 = perron(Q)
            if rho2 < 1:
                break
            qq += 1
        print(f'p={p} e={e}: smallest p-power q with rho<1: {q} (rho={rho:.6f}); smallest integer q (formal kernel) with rho<1: {qq}; 2e(e+2) = {2*e*(e+2)}; 2e^2 = {2*e*e}')
