"""Explicit PG(2,81) and the full 6648-letter turn kernel for the p=3 design of Section 6 of the paper.

1. Build F_81 = F_3[x]/(irreducible quartic), the 6643 points and lines, and the incidence matrix.
   Check: each line has 82 points, each point on 82 lines, two distinct lines meet in exactly 1 point
   (so ordinary cross-intersections are 1 or 82).
2. Build the exact joint letter frequencies J_B, J_{A+} (= J_{A-}) from the type distribution
   (line uniform, extras independent of line as prescribed), with a random fixed-point-free
   inversion pairing extras to distinct ordinary letters.
3. Turn weights w(t,u) = J_B(tbar,u)/r (0 if u = tbar); check A-weights <= w; check w(t,u) = w(ubar,tbar).
4. M = w^2; check Mf <= (199/200) f for the f of the proof of Lemma 6.4; Perron root by power iteration;
   compare 1^T M^(h-1) 1 against the claimed bound 6678 (199/200)^(h-1).
"""
import numpy as np
import itertools, math, sys

p = 3
# --- F_81 as polynomials over F_3 of degree < 4, encoded base 3 ---
def poly_mul_mod(a, b, mod):
    # a, b: lists of 4 coeffs (low->high); mod: monic quartic coeffs low->high (5 entries)
    prod = [0] * 7
    for i in range(4):
        for j in range(4):
            prod[i + j] = (prod[i + j] + a[i] * b[j]) % p
    for d in range(6, 3, -1):
        c = prod[d]
        if c:
            for k in range(5):
                prod[d - 4 + k] = (prod[d - 4 + k] - c * mod[k]) % p
    return prod[:4]

def enc(c):
    return c[0] + 3 * c[1] + 9 * c[2] + 27 * c[3]

def dec(x):
    return [x % 3, (x // 3) % 3, (x // 9) % 3, (x // 27) % 3]

def is_field(mod):
    # field iff every nonzero element has an inverse (multiplication by a is injective)
    for a in range(1, 81):
        da = dec(a)
        seen = set(enc(poly_mul_mod(da, dec(b), mod)) for b in range(81))
        if len(seen) != 81:
            return False
    return True

mod = None
for c0, c1, c2, c3 in itertools.product(range(3), repeat=4):
    cand = [c0, c1, c2, c3, 1]
    if c0 == 0:
        continue
    if is_field(cand):
        mod = cand
        break
print('irreducible quartic (low->high):', mod)
ADD = np.zeros((81, 81), dtype=np.int64)
MUL = np.zeros((81, 81), dtype=np.int64)
for a in range(81):
    for b in range(81):
        da, db = dec(a), dec(b)
        ADD[a, b] = enc([(da[i] + db[i]) % 3 for i in range(4)])
        MUL[a, b] = enc(poly_mul_mod(da, db, mod))

q = 81
pts = [(1, a, b) for a in range(q) for b in range(q)] + [(0, 1, a) for a in range(q)] + [(0, 0, 1)]
pts = np.array(pts, dtype=np.int64)
v = len(pts)
assert v == q * q + q + 1 == 6643
X, Y, Z = pts[:, 0], pts[:, 1], pts[:, 2]
Inc = np.zeros((v, v), dtype=np.float32)  # Inc[line, point]
for li in range(v):
    a, b, c = pts[li]
    s = ADD[ADD[MUL[X, a], MUL[Y, b]], MUL[Z, c]]
    Inc[li] = (s == 0)
row = Inc.sum(1); col = Inc.sum(0)
print('points per line: min/max', row.min(), row.max(), '; lines per point: min/max', col.min(), col.max())
G = Inc @ Inc.T  # line-line intersection sizes
off = G[~np.eye(v, dtype=bool)]
print('distinct-line intersections: min/max', off.min(), off.max(), '; diagonal min/max', np.diag(G).min(), np.diag(G).max())
Gp = Inc.T @ Inc  # point-point: number of lines through both
offp = Gp[~np.eye(v, dtype=bool)]
print('distinct-point common lines: min/max', offp.min(), offp.max())
del G, Gp

# --- letters: 0..v-1 ordinary points, v..v+4 extras ---
e = 5
T = v + e
r = (q + 1) / v
rng = np.random.default_rng(12345)
ordinary = rng.permutation(v)
inv = -np.ones(T, dtype=np.int64)
for i in range(e):
    o = ordinary[i]; x = v + i
    inv[o] = x; inv[x] = o
rest = ordinary[e:]
assert len(rest) % 2 == 0
for i in range(0, len(rest), 2):
    a, b = rest[i], rest[i + 1]
    inv[a] = b; inv[b] = a
assert (inv >= 0).all() and (inv[inv] == np.arange(T)).all() and (inv != np.arange(T)).all()

# joint frequencies (exact structure computed from incidence; floats are exact enough here)
def joint(side):
    J = np.zeros((T, T))
    # ordinary-ordinary: Pr(line contains a and b) = (#lines through a,b)/v
    Gp = (Inc.T.astype(np.float64) @ Inc.astype(np.float64)) / v
    J[:v, :v] = Gp
    # extras independent of line: Pr(a ordinary in S, x extra in S) = r * Pr(x in extras)
    if side == 'B':
        ex = np.full((e, e), r)  # all extras together with prob r
    else:
        # each 3-subset of the 5 extras with prob r/6
        ex = np.zeros((e, e))
        for sub in itertools.combinations(range(e), p):
            for i in sub:
                for j in sub:
                    ex[i, j] += r / 6
    J[v:, v:] = ex
    marg_extra = np.diag(ex)
    J[:v, v:] = r * marg_extra[None, :]
    J[v:, :v] = J[:v, v:].T
    return J

JB = joint('B'); JA = joint('A')
print('letter marginals B: min/max', np.diag(JB).min(), np.diag(JB).max(), ' A: min/max', np.diag(JA).min(), np.diag(JA).max(), ' r =', r)
# w(t,u) = J(tbar,u)/r, zero at u = tbar
def weights(J):
    W = J[inv, :] / r
    W[np.arange(T), inv] = 0.0
    return W
wB = weights(JB); wA = weights(JA)
print('dominance max(wA - wB):', (wA - wB).max())
print('distinct positive values of wB:', sorted(set(np.round(wB[wB > 0], 12))))
print('distinct positive values of wA:', sorted(set(np.round(wA[wA > 0], 12))))
# reversal symmetry w(t,u) = w(ubar, tbar)
sym = np.abs(wB - wB[np.ix_(inv, inv)].T).max()
print('reversal symmetry max |w(t,u) - w(ubar,tbar)|:', sym)
M = wB ** 2
f = np.ones(T); f[inv[v:]] = 7.0  # f(t)=7 iff tbar is extra, i.e. t is the ordinary partner of an extra
assert f.sum() == 6678
ratio = (M @ f) / f
print('max (Mf)(t)/f(t):', ratio.max(), ' bound 199/200 =', 199 / 200, ' ok:', ratio.max() <= 199 / 200)
print('max ratio over tbar ordinary:', ratio[f == 1].max(), ' over tbar extra:', ratio[f == 7].max())
# Perron root by power iteration
x = np.ones(T)
for it in range(3000):
    y = M @ x
    lam = y.sum() / x.sum()
    x = y / y.sum()
print('Perron root of M (power iteration):', lam)
# Sum of squared word weights for a few h, versus the claimed bound
vec = np.ones(T)
for h in range(1, 4001):
    if h in (1, 2, 10, 100, 1000, 2000, 3000, 4000):
        s = vec.sum()
        print(f'h={h}: sum_W P(W)^2 = {s:.6e};  6678*(199/200)^(h-1) = {6678*(199/200)**(h-1):.6e};  e^(-h/400) = {math.exp(-h/400):.6e}')
    vec = M @ vec
