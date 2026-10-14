"""Numerical sanity test of the signed cancellation lemma (part (a)).

Builds the random bipartite Gamma_A and the random Gamma_B exactly as in the model (independent uniform
bijections per inverse pair; A-pools A_{+,t} -> A_{-,tbar}, A_{-,t} -> A_{+,tbar}; B-pools B_t -> B_tbar),
WITHOUT girth conditioning (the lemma does not need it), forms the simultaneous-step graph on A' x B', and checks:
  * the half-edge pairing (x,y,t) <-> (x',y',tbar) is a fixed-point-free involution, no loops,
  * deg(x,y) = |S_x cap S_y| = 1 mod p,
  * sigma flips along every edge,
  * sum_{(x,y) in C} sigma(x) = 0 mod p for every component C  (the claim),
and, as controls: unsigned sums |C| mod p, and a NON-bipartite A (OpenAI-style single pool on A) with
arbitrary signs, where the signed identity has no reason to hold.

Instances:
  p=3: faithful design with q=3 (PG(2,3)), 5 extras, n = 1014 (exact proportions of the claimed design).
  p=5: q=5, 9 extras; A_+ = A_- = each line 5 times, 54 of them carrying cyclic 5-subsets of Z_9 (each 6 times);
       B = each line once, 6 lines carrying all 9 extras (balanced frequencies; cross intersections in {1,6}+{0,5}).
  p=7: q=7, 13 extras; A_+ = A_- = each line 7 times, 104 carrying cyclic 7-subsets of Z_13 (each 8 times);
       B = each line once, 8 lines carrying all 13 extras.
"""
import itertools, random, sys
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components


def pg2_prime(q):
    pts = [(1, a, b) for a in range(q) for b in range(q)] + [(0, 1, b) for b in range(q)] + [(0, 0, 1)]
    lines = []
    for (a, b, c) in pts:
        lines.append(frozenset(i for i, (x, y, z) in enumerate(pts) if (a * x + b * y + c * z) % q == 0))
    v = len(pts)
    assert all(len(L) == q + 1 for L in lines)
    return v, lines


def make_involution(v, e):
    bar = {}
    for k in range(e):
        bar[v + k] = k
        bar[k] = v + k
    rest = list(range(e, v))
    for i in range(0, len(rest), 2):
        bar[rest[i]] = rest[i + 1]
        bar[rest[i + 1]] = rest[i]
    assert all(bar[bar[t]] == t and bar[t] != t for t in bar)
    return bar


def random_side(types_by_class, bar, rng, bipartite=True):
    """types_by_class: dict colour -> list of letter-sets. Returns (S list, colour list, nbr dict-list)."""
    S, col = [], []
    for c, lst in types_by_class.items():
        for s in lst:
            S.append(frozenset(s)); col.append(c)
    nV = len(S)
    nbr = [dict() for _ in range(nV)]
    letters = sorted(bar)
    done = set()
    for t in letters:
        tb = bar[t]
        if (tb, t) in done:
            continue
        done.add((t, tb))
        if bipartite:
            for (c1, c2) in ((+1, -1), (-1, +1)):
                src = [x for x in range(nV) if col[x] == c1 and t in S[x]]
                dst = [y for y in range(nV) if col[y] == c2 and tb in S[y]]
                assert len(src) == len(dst), (t, len(src), len(dst))
                rng.shuffle(dst)
                for x, y in zip(src, dst):
                    nbr[x][t] = y
                    nbr[y][tb] = x
        else:
            src = [x for x in range(nV) if t in S[x]]
            dst = [y for y in range(nV) if tb in S[y]]
            assert len(src) == len(dst)
            rng.shuffle(dst)
            for x, y in zip(src, dst):
                nbr[x][t] = y
                nbr[y][tb] = x
    for x in range(nV):
        assert set(nbr[x]) == set(S[x])   # immersion: each outgoing letter used exactly once
    return S, col, nbr


def component(nbr, root):
    seen = {root}; stack = [root]
    while stack:
        x = stack.pop()
        for y in nbr[x].values():
            if y not in seen:
                seen.add(y); stack.append(y)
    return sorted(seen)


def test(name, p, SA, colA, nbrA, SB, nbrB, xA, xB, sign):
    Ap = component(nbrA, xA); Bp = component(nbrB, xB)
    ia = {x: i for i, x in enumerate(Ap)}; ib = {y: j for j, y in enumerate(Bp)}
    nb = len(Bp)
    rows, cols = [], []
    deg_ok = True; involution_ok = True; loops = 0; flip_ok = True; degs = set()
    for x in Ap:
        for y in Bp:
            common = SA[x] & SB[y]
            d = 0
            for t in common:
                x2, y2 = nbrA[x][t], nbrB[y][t]
                # inverse half-edge exists and returns
                if nbrA[x2].get(BAR[t]) != x or nbrB[y2].get(BAR[t]) != y:
                    involution_ok = False
                if x2 == x and y2 == y:
                    loops += 1
                if sign[x2] != -sign[x]:
                    flip_ok = False
                rows.append(ia[x] * nb + ib[y]); cols.append(ia[x2] * nb + ib[y2])
                d += 1
            degs.add(d)
            if d % p != 1:
                deg_ok = False
    N = len(Ap) * nb
    G = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(N, N)).tocsr()
    ncomp, lab = connected_components(G, directed=False)
    sig = np.array([sign[Ap[k // nb]] for k in range(N)], dtype=np.int64)
    sums = np.bincount(lab, weights=sig, minlength=ncomp).astype(np.int64)
    sizes = np.bincount(lab, minlength=ncomp)
    signed_ok = bool(np.all(sums % p == 0))
    nonzero_Z = int(np.sum(sums != 0))
    unsigned_bad = int(np.sum(sizes % p != 0))
    print(f'[{name}] p={p} |A\'|={len(Ap)} |B\'|={nb} step-graph vertices={N} components={ncomp}')
    print(f'    degrees seen={sorted(degs)}  all deg=1 mod p: {deg_ok}  involution ok: {involution_ok}  loops: {loops}  sigma flips on every edge: {flip_ok}')
    print(f'    signed sums = 0 mod p on every component: {signed_ok}   (components with signed sum != 0 over Z: {nonzero_Z}; '
          f'example sums {sorted(set(sums.tolist()))[:8]})')
    print(f'    control: components with |C| != 0 mod p (unsigned sum fails in char p): {unsigned_bad}')
    return signed_ok


rng = random.Random(20261013)
results = []

# ---------------- p = 3 faithful design, q = 3, n = 1014 ----------------
p, q, e = 3, 3, 5
v, lines = pg2_prime(q)
BAR = make_involution(v, e)
ext = [v + k for k in range(e)]
n = 1014
perA = n // (2 * v); per3 = (perA * (q + 1)) // (v * 6)
assert perA * (q + 1) % (v * 6) == 0
perB = n // v; perBx = perB * (q + 1) // v
assert perB * (q + 1) % v == 0
Atypes = []
for L in lines:
    for E in itertools.combinations(ext, 3):
        Atypes += [set(L) | set(E)] * per3
    Atypes += [set(L)] * (perA - 10 * per3)
Btypes = []
for L in lines:
    Btypes += [set(L) | set(ext)] * perBx + [set(L)] * (perB - perBx)
print(f'p=3 design: v={v}, A_+=A_-={len(Atypes)}, B={len(Btypes)}, per line class on A: {per3} per 3-subset, {perA-10*per3} empty')
SA, colA, nbrA = random_side({+1: Atypes, -1: Atypes}, BAR, rng)
SB, _, nbrB = random_side({0: Btypes}, BAR, rng, bipartite=False)
xA = 0; xB = 0
assert colA[xA] == +1
results.append(test('p3 bipartite', 3, SA, colA, nbrA, SB, nbrB, xA, xB, colA))
# control: non-bipartite A (one pool on all of A), signs = the arbitrary +/- labels
SA2, colA2, nbrA2 = random_side({+1: Atypes, -1: Atypes}, BAR, rng, bipartite=False)
print('  control (non-bipartite A, same signs):')
test('p3 NON-bipartite control', 3, SA2, colA2, nbrA2, SB, nbrB, xA, xB, colA2)

# ---------------- p = 5, q = 5 ----------------
for (p, q, kA) in ((5, 5, 5), (7, 7, 7)):
    e = 2 * p - 1
    v, lines = pg2_prime(q)
    BAR = make_involution(v, e)
    ext = [v + k for k in range(e)]
    # A: each line kA times; cyclic p-subsets of Z_e, each used m times, total extra incidences = e*(q+1)*kA
    tot = e * (q + 1) * kA
    assert tot % p == 0
    nwith = tot // p
    assert nwith % e == 0
    m = nwith // e
    cyc = [frozenset(ext[(i + j) % e] for j in range(p)) for i in range(e)]
    Atypes = []
    lineslist = [L for L in lines for _ in range(kA)]
    rng.shuffle(lineslist)
    extras_assign = [E for E in cyc for _ in range(m)] + [frozenset()] * (len(lineslist) - nwith)
    rng.shuffle(extras_assign)
    for L, E in zip(lineslist, extras_assign):
        Atypes.append(set(L) | set(E))
    # B: each line once, q+1 of them carry all extras
    Btypes = []
    carry = set(rng.sample(range(v), q + 1))
    for i, L in enumerate(lines):
        Btypes.append(set(L) | (set(ext) if i in carry else set()))
    # check cross intersections
    vals = {len(a & b) for a in map(frozenset, Atypes) for b in map(frozenset, Btypes)}
    print(f'p={p} q={q} e={e}: A_+=A_-={len(Atypes)}, B={len(Btypes)}; cross-intersection values {sorted(vals)} mod p {sorted({x % p for x in vals})}')
    SA, colA, nbrA = random_side({+1: Atypes, -1: Atypes}, BAR, rng)
    SB, _, nbrB = random_side({0: Btypes}, BAR, rng, bipartite=False)
    results.append(test(f'p{p} bipartite', p, SA, colA, nbrA, SB, nbrB, 0, 0, colA))

print('ALL SIGNED CHECKS PASSED:', all(results))
