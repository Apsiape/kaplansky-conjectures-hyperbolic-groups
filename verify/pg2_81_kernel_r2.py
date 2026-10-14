"""Explicit PG(2,81) build + full 6648x6648 turn-kernel check for the p=3 design of Section 6 of the paper.

Independent of the lumped/Fraction computation: the plane is constructed from GF(81)
arithmetic, all incidence facts are checked by matrix products, and the turn kernels
w_A (one colour class) and w_B are assembled letter-by-letter from the explicit
incidence and the per-line type table at n0 = 12 v^2. Then:
  * letter marginals equal r in A_+ (=A_-) and in B;
  * domination w_A <= w_B entrywise;  reversal w_B(t,u) = w_B(ubar,tbar) entrywise;
  * all cross-intersection sizes |S_x cap S_y| are 1 mod 3;
  * (M f)/f row maxima for M = w_B^2, f = 7 on {t : tbar extra};
  * spectral radius of M by power iteration.
"""
import itertools
import numpy as np

Q, P = 81, 3


def gf81():
    # find an irreducible monic quartic over GF(3) by testing for zero divisors
    def polymul(a, b, mod):
        # a, b: lists of 4 coeffs; mod: [m0,m1,m2,m3] for x^4 = -(m0 + m1 x + m2 x^2 + m3 x^3)
        prod = [0] * 7
        for i in range(4):
            for j in range(4):
                prod[i + j] = (prod[i + j] + a[i] * b[j]) % 3
        for d in range(6, 3, -1):
            c = prod[d]
            if c:
                prod[d] = 0
                for k in range(4):
                    prod[d - 4 + k] = (prod[d - 4 + k] - c * mod[k]) % 3
        return prod[:4]

    def digits(n):
        return [(n // 3 ** i) % 3 for i in range(4)]

    def num(d):
        return sum(d[i] * 3 ** i for i in range(4))

    for m in itertools.product(range(3), repeat=4):
        if m[0] == 0:
            continue
        mul = np.zeros((81, 81), dtype=np.uint8)
        ok = True
        for a in range(81):
            da = digits(a)
            for b in range(81):
                mul[a, b] = num(polymul(da, digits(b), list(m)))
        # field iff no zero divisors
        if np.all(mul[1:, 1:] != 0):
            add = np.zeros((81, 81), dtype=np.uint8)
            for a in range(81):
                for b in range(81):
                    add[a, b] = num([(x + y) % 3 for x, y in zip(digits(a), digits(b))])
            return m, add, mul
    raise RuntimeError("no irreducible quartic found")


def main():
    m, add, mul = gf81()
    print("GF(81) modulus x^4 + %d x^3 + %d x^2 + %d x + %d (coeffs low->high %s)" % (m[3], m[2], m[1], m[0], m))
    # normalized projective points
    pts = []
    for x1 in range(Q):
        for x2 in range(Q):
            pts.append((1, x1, x2))
    for x2 in range(Q):
        pts.append((0, 1, x2))
    pts.append((0, 0, 1))
    pts = np.array(pts, dtype=np.int64)
    v = len(pts)
    assert v == Q * Q + Q + 1
    mulf = mul.reshape(-1)
    addf = add.reshape(-1)
    N = np.zeros((v, v), dtype=bool)  # N[line, point]
    B = 512
    for s in range(0, v, B):
        a = pts[s:s + B]
        acc = mulf[a[:, 0:1] * 81 + pts[None, :, 0]].astype(np.int64)
        for k in (1, 2):
            term = mulf[a[:, k:k + 1] * 81 + pts[None, :, k]].astype(np.int64)
            acc = addf[acc * 81 + term].astype(np.int64)
        N[s:s + B] = (acc == 0)
    rs, cs = N.sum(1), N.sum(0)
    print("points/lines:", v, "; points per line:", set(rs.tolist()), "; lines per point:", set(cs.tolist()))
    Nf = N.astype(np.float32)
    LL = Nf @ Nf.T  # line-line intersections
    PP = Nf.T @ Nf  # point-point: number of common lines
    offL = LL[~np.eye(v, dtype=bool)]
    offP = PP[~np.eye(v, dtype=bool)]
    print("line intersections: diag", set(np.diag(LL).astype(int).tolist()), "offdiag", set(np.unique(offL).astype(int).tolist()))
    print("lines through 2 points: diag", set(np.diag(PP).astype(int).tolist()), "offdiag", set(np.unique(offP).astype(int).tolist()))
    del offL, offP, Nf

    e = 5
    T = v + e
    r_num, r_den = Q + 1, v
    # involution: extra i <-> point i (i<5); remaining points paired consecutively
    inv = np.empty(T, dtype=np.int64)
    for i in range(e):
        inv[v + i] = i
        inv[i] = v + i
    rest = list(range(e, v))
    assert len(rest) % 2 == 0
    for a, b in zip(rest[0::2], rest[1::2]):
        inv[a], inv[b] = b, a
    assert np.all(inv[inv] == np.arange(T)) and np.all(inv != np.arange(T))

    n0 = 12 * v * v
    # per-line type tables at n0
    triples = list(itertools.combinations(range(e), 3))
    A_line_total = n0 // (2 * v)
    A_ext = {X: 82 for X in triples}
    A_ext[()] = A_line_total - 82 * len(triples)
    B_line_total = n0 // v
    B_ext = {tuple(range(e)): 984, (): B_line_total - 984}
    print("A_+ per line:", A_line_total, "types", {k: c for k, c in A_ext.items() if k == () or k == (0, 1, 2)}, "...")
    print("B per line:", B_line_total, B_ext)

    def joint(line_total, ext):
        ev = np.zeros(e)
        EM = np.zeros((e, e))
        for X, c in ext.items():
            for i in X:
                ev[i] += c
                for j in X:
                    EM[i, j] += c
        J = np.zeros((T, T))
        J[:v, :v] = PP.astype(np.float64) * line_total   # common lines x vertices per line
        J[:v, v:] = np.outer(cs, ev)                        # lines through point x extras per line
        J[v:, :v] = J[:v, v:].T
        J[v:, v:] = v * EM
        return J

    def kernel(J):
        diag = np.diag(J).copy()
        W = J[inv, :] / diag[inv][:, None]   # W[t,u] = J[tbar,u]/J[tbar,tbar]
        W[np.arange(T), inv] = 0.0           # cancelling turn
        return W, diag

    JA = joint(A_line_total, A_ext)
    WA, dA = kernel(JA)
    del JA
    JB = joint(B_line_total, B_ext)
    WB, dB = kernel(JB)
    del JB
    r = r_num / r_den
    print("marginals: A_+ letters/|A_+| in", set(np.round(dA / (n0 // 2) / r, 12).tolist()),
          "(units of r);  B:", set(np.round(dB / n0 / r, 12).tolist()))
    print("distinct w_B values:", sorted(set(np.round(np.unique(WB), 12).tolist())),
          " expected {0, 1/82=%.12f, r=%.12f, 1}" % (1 / 82, r))
    print("distinct w_A values:", sorted(set(np.round(np.unique(WA), 12).tolist())))
    print("domination w_A <= w_B entrywise:", bool(np.all(WA <= WB + 1e-15)),
          "; max(w_A - w_B) =", float((WA - WB).max()))
    rev = np.abs(WB - WB[np.ix_(inv, inv)].T).max()
    print("reversal symmetry max |w_B(t,u) - w_B(ubar,tbar)| =", float(rev))
    del WA
    # cross intersections: |l1 cap l2| in {1,82}, extras A-part (triple or empty) vs B-part (all or none)
    lineint = {1, 82}  # verified above
    extint = {len(set(X) & set(Y)) for X in A_ext for Y in B_ext}
    cross = sorted({a + b for a in lineint for b in extint})
    print("cross-intersection sizes:", cross, "mod 3:", [c % 3 for c in cross])
    # row ratios
    M = WB * WB
    del WB
    f = np.ones(T)
    f[inv >= v] = 7.0      # tbar extra
    ratio = (M @ f) / f
    is_tbar_extra = inv >= v
    print("max (Mf)/f over tbar ordinary: %.15f  (claimed 73664436152/74181603769 = %.15f)"
          % (ratio[~is_tbar_extra].max(), 73664436152 / 74181603769))
    print("max (Mf)/f over tbar extra:    %.15f  (claimed 221387048/308906143 = %.15f)"
          % (ratio[is_tbar_extra].max(), 221387048 / 308906143))
    print("all ratios < 199/200:", bool(ratio.max() < 199 / 200), "; sum f =", f.sum())
    # spectral radius of M (nonnegative, irreducible): power iteration
    x = np.ones(T)
    lam = 0.0
    for it in range(3000):
        y = M @ x
        lam_new = y.sum() / x.sum()
        x = y / y.max()
        if abs(lam_new - lam) < 1e-15:
            break
        lam = lam_new
    print("power-iteration spectral radius of M: %.12f (iterations %d)" % (lam_new, it))


if __name__ == "__main__":
    main()
