"""Engine 2: build the p=3 design explicitly (PG(2,81), 5 extras) and recompute everything from the type tables.

Checks:
 (1) GF(81) is a field; PG(2,81) has 6643 points/lines, 82 points per line, 82 lines per point, lines meet in 1 point.
 (2) fixed-point-free involution on the 6648 letters (extras paired with 5 distinct ordinary letters).
 (3) exact type counts at n = 12 v^2; every letter has frequency r = 82/6643 on A_+ (= A_-) and on B.
 (4) all cross intersections |S_x cap S_y| (x an A-type, y a B-type) lie in {1,4,82,85}, all = 1 mod 3.
 (5) conditional frequencies c_side(u | a) computed from the joint incidence of the type tables; A <= B entrywise.
 (6) turn kernel M[t,u] = c_B(u | tbar)^2 (u != tbar), Perron root by power iteration on the full 6648x6648 matrix,
     and direct evaluation of sum_{W in T^h} P(W)^2 = 1^T M^(h-1) 1.
"""
import itertools, math, random, sys, time
import numpy as np

P = 3
DEG = 4
Q = P ** DEG  # 81
t0 = time.time()

# ---------- GF(81) ----------
def to_digits(a):
    return [(a // P ** i) % P for i in range(DEG)]

def from_digits(d):
    return sum(int(d[i]) * P ** i for i in range(DEG))

def polymulmod(a, b, f):  # a,b digit lists (deg<4); f monic quartic coefficient list length 5 (low->high)
    prod = [0] * (2 * DEG - 1)
    for i in range(DEG):
        for j in range(DEG):
            prod[i + j] = (prod[i + j] + a[i] * b[j]) % P
    for k in range(2 * DEG - 2, DEG - 1, -1):
        c = prod[k]
        if c:
            for i in range(DEG + 1):
                prod[k - DEG + i] = (prod[k - DEG + i] - c * f[i]) % P
    return prod[:DEG]

def build_field():
    for coeffs in itertools.product(range(P), repeat=DEG):
        f = list(coeffs) + [1]
        if f[0] == 0:
            continue
        mul = np.zeros((Q, Q), dtype=np.int64)
        D = [to_digits(a) for a in range(Q)]
        for a in range(Q):
            for b in range(Q):
                mul[a, b] = from_digits(polymulmod(D[a], D[b], f))
        # field test: no zero divisors among nonzero elements
        if np.all(mul[1:, 1:] != 0):
            add = np.zeros((Q, Q), dtype=np.int64)
            for a in range(Q):
                for b in range(Q):
                    add[a, b] = from_digits([(x + y) % P for x, y in zip(D[a], D[b])])
            return f, add, mul
    raise RuntimeError('no irreducible quartic found')

f, ADD, MUL = build_field()
# extra field checks: every nonzero element has an inverse, multiplicative group cyclic of order 80
assert all((MUL[a] == 1).sum() == 1 for a in range(1, Q))
print('GF(81) modulus (low->high):', f, ' field ok', flush=True)

# ---------- PG(2,81) ----------
pts = [(1, a, b) for a in range(Q) for b in range(Q)] + [(0, 1, b) for b in range(Q)] + [(0, 0, 1)]
pts = np.array(pts, dtype=np.int64)
v = len(pts)
assert v == Q * Q + Q + 1 == 6643
lines = pts.copy()  # dual coordinates
Nm = np.zeros((v, v), dtype=np.float64)  # Nm[line, point]
for i in range(v):
    a, b, c = lines[i]
    s = ADD[ADD[MUL[a, pts[:, 0]], MUL[b, pts[:, 1]]], MUL[c, pts[:, 2]]]
    Nm[i] = (s == 0)
assert np.all(Nm.sum(1) == Q + 1) and np.all(Nm.sum(0) == Q + 1)
LL = Nm @ Nm.T
off = LL[~np.eye(v, dtype=bool)]
assert np.all(np.diag(LL) == Q + 1) and np.all(off == 1)
PP = Nm.T @ Nm
offp = PP[~np.eye(v, dtype=bool)]
assert np.all(np.diag(PP) == Q + 1) and np.all(offp == 1)
del PP, offp, off
print(f'PG(2,81): v={v}, lines of size 82, point degree 82, line-line meets = 1, point-point joined by 1 line: ok', flush=True)

# ---------- letters and involution ----------
e = 5
nT = v + e
ext = list(range(v, v + e))
bar = np.full(nT, -1, dtype=np.int64)
for k in range(e):          # extra k paired with ordinary letter k
    bar[v + k] = k
    bar[k] = v + k
rest = list(range(e, v))
assert len(rest) % 2 == 0
for i in range(0, len(rest), 2):
    bar[rest[i]] = rest[i + 1]
    bar[rest[i + 1]] = rest[i]
assert np.all(bar >= 0) and np.all(bar[bar] == np.arange(nT)) and np.all(bar != np.arange(nT))
print('involution: fixed-point-free, extras paired with distinct ordinary letters 0..4: ok', flush=True)

# ---------- type tables at n = 12 v^2 ----------
n = 12 * v * v
r_num, r_den = Q + 1, v
A_extra_types = [()] + [tuple(c) for c in itertools.combinations(range(e), 3)]
B_extra_types = [(), tuple(range(e))]
perA = n // (2 * v)      # vertices per line class on A_+ (and A_-)
perB = n // v
cntA = {E: (perA * r_num) // (r_den * 6) for E in A_extra_types if E}
assert all((perA * r_num) % (r_den * 6) == 0 for _ in [0])
cntA[()] = perA - sum(cntA.values())
cntB = {tuple(range(e)): perB * r_num // r_den}
assert (perB * r_num) % r_den == 0
cntB[()] = perB - cntB[tuple(range(e))]
print('A_+ per line class:', perA, ' counts:', {k: v_ for k, v_ in cntA.items() if k in [(), (0, 1, 2)]}, '(each 3-subset same)')
print('B   per line class:', perB, ' counts:', cntB, flush=True)
assert min(cntA.values()) >= 0 and min(cntB.values()) >= 0
sizeA, sizeB = v * perA, v * perB
assert sizeA == n // 2 and sizeB == n

# ---------- cross intersections ----------
vals = set()
for E in A_extra_types:
    for F in B_extra_types:
        x = len(set(E) & set(F))
        for lv in (1, Q + 1):
            vals.add(lv + x)
print('cross-intersection values (line-line in {1,82}, extras in {0,3}):', sorted(vals), ' mod 3:', sorted({x % 3 for x in vals}))
# direct set-based check on random type pairs (independent of the decomposition)
line_sets = [set(np.nonzero(Nm[i])[0].tolist()) for i in range(v)]
rng = random.Random(1)
seen = set()
for _ in range(20000):
    la, lb = rng.randrange(v), rng.randrange(v)
    if rng.random() < 0.05:
        lb = la
    E = rng.choice(A_extra_types); F = rng.choice(B_extra_types)
    Sx = line_sets[la] | {v + k for k in E}
    Sy = line_sets[lb] | {v + k for k in F}
    seen.add(len(Sx & Sy))
print('random direct |S_x cap S_y| values seen:', sorted(seen), ' all = 1 mod 3:', all(x % 3 == 1 for x in seen), flush=True)

# ---------- joint incidence from the type tables ----------
def joint(counts):
    J = np.zeros((nT, nT), dtype=np.float64)
    for E, c in counts.items():
        S = np.zeros((v, nT), dtype=np.float64)
        S[:, :v] = Nm
        for k in E:
            S[:, v + k] = 1.0
        J += S.T @ (c * S)
    return J

JA = joint(cntA)
JB = joint(cntB)
print('joint matrices built', flush=True)
for name, J, size in (('A_+', JA, sizeA), ('B', JB, sizeB)):
    d = np.diag(J)
    ok = np.all(d * r_den == r_num * size)
    print(f'letter frequency on {name} equals 82/6643 for every letter: {ok}')
    assert ok

CA = JA / np.diag(JA)[:, None]   # CA[a,u] = freq of u among A-vertices containing a
CB = JB / np.diag(JB)[:, None]
mask = ~np.eye(nT, dtype=bool)
print('A conditional <= B conditional for all a != u:', bool(np.all(CA[mask] <= CB[mask] + 1e-15)))
def distinct(x):
    return sorted({round(float(t), 12) for t in np.unique(np.round(x, 12))})
print('distinct B conditional values (a != u):', distinct(CB[mask]), ' expected', [1 / 82, 82 / 6643, 1.0])
print('distinct A conditional values (a != u):', distinct(CA[mask]), ' expected', [1 / 82, 82 / 6643, 0.5])
# reversal symmetry w(t,u) = w(ubar, tbar)
W = np.zeros((nT, nT))
for t in range(nT):
    W[t] = CB[bar[t]]
    W[t, bar[t]] = 0.0
rev = W[bar][:, bar].T   # rev[t,u] = W[bar u, bar t]
print('reversal symmetry max |w(t,u) - w(ubar,tbar)| =', float(np.max(np.abs(W - rev))), flush=True)
del JA, JB, CA, rev

M = W * W
del W
# power iteration
x = np.ones(nT)
for it in range(400):
    y = M @ x
    lam = y.sum() / x.sum()
    x = y / np.linalg.norm(y)
y = M @ x
rho = float(np.dot(x, y) / np.dot(x, x))
print(f'power iteration Perron root of full M: {rho:.13f}  (engine-1 quotient value 0.9915818850353568)')
# direct squared-word sums 1^T M^(h-1) 1
z = np.ones(nT)
logs = {}
for h in range(1, 6001):
    if h > 1:
        z = M @ z
    if h in (1, 2, 10, 100, 1000, 2000, 3000, 4000, 5000, 6000):
        logs[h] = math.log(z.sum())
for h, lg in logs.items():
    print(f'  h={h:5d}: log sum_W P(W)^2 = {lg: .6f}   ( -h/300 = {-h/300: .3f}; -h/600*2 = {-h/300: .3f})')
print('done')
