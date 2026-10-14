"""Exact re-derivation of the row bounds in the proof of Lemma 6.4 of the paper (independent of the other scripts).

Letters are lumped into three classes, which is exact because every row of
w depends only on the class of t and every successor class has a known size:
  X = extra letters            (t extra,  tbar ordinary partner)   size e
  Y = partners of extras       (t ordinary, tbar extra)            size e
  Z = other ordinary letters   (t ordinary, tbar ordinary)         size v-e
w(t,u) := frequency of u among vertices containing tbar (B-based kernel),
          0 for u = tbar.
Class-level joint frequencies are derived from the type table (line part and
extra part) with Fractions; we also derive the A-colour-class kernel and test
domination w_A <= w_B entrywise at class level.
"""
from fractions import Fraction as Fr
from math import comb, log, exp, ceil
import itertools
import numpy as np


def smallest_q(p):
    e = 2 * p - 1
    q = p
    while q < 2 * e * (e + 2):
        q *= p
    return q


def kernels(p, q):
    e = 2 * p - 1
    v = q * q + q + 1
    r = Fr(q + 1, v)
    cp = comb(e - 1, p - 1)
    if comb(e, p) <= 400000:
        subs = list(itertools.combinations(range(e), p))
        # extra-part distributions (independent of the line, exact proportions)
        distA = {s: r / cp for s in subs}
        distA[()] = 1 - sum(distA.values())
    else:
        distA = None  # too many p-subsets to enumerate; use the closed-form counts below
    distB = {tuple(range(e)): r, (): 1 - r}
    assert distB[()] >= 0 and (distA is None or distA[()] >= 0)
    assert 1 - comb(e, p) * r / cp >= 0

    def joint(dist):
        # frequencies of: an ordinary letter; an extra; two distinct ordinary;
        # ordinary+extra; two distinct extras (extras 0 and 1 by symmetry; check symmetry)
        fo = Fr(q + 1, v)  # a point lies on q+1 of v lines
        fe = [sum(pr for s, pr in dist.items() if i in s) for i in range(e)]
        assert len(set(fe)) == 1
        foo = Fr(1, v)  # two points: exactly one line
        foe = fo * fe[0]  # line part and extra part are independent per line class
        fee = {}
        for i in range(e):
            for j in range(e):
                if i != j:
                    fee[(i, j)] = sum(pr for s, pr in dist.items() if i in s and j in s)
        assert len(set(fee.values())) == 1
        return fo, fe[0], foo, foe, fee[(0, 1)]

    out = {}
    for name, dist in (("A", distA), ("B", distB)):
        if dist is None:
            # closed form: an extra lies in C(e-1,p-1)=c_p subsets, a pair of extras in C(e-2,p-2)
            fo, fe, foo = Fr(q + 1, v), comb(e - 1, p - 1) * r / cp, Fr(1, v)
            foe, fee = fo * fe, comb(e - 2, p - 2) * r / cp
        else:
            fo, fe, foo, foe, fee = joint(dist)
            if name == "A":  # cross-check enumeration against the closed form
                assert fe == comb(e - 1, p - 1) * r / cp and fee == comb(e - 2, p - 2) * r / cp
        # conditional frequency of u given tbar
        out[name] = dict(
            marg_o=fo, marg_e=fe,
            oo=foo / fo,       # tbar ordinary, u ordinary (distinct)
            oe=foe / fo,       # tbar ordinary, u extra
            eo=foe / fe,       # tbar extra, u ordinary
            ee=fee / fe,       # tbar extra, u extra (distinct)
        )
    return e, v, r, cp, out


def lumped_M(p, q, w):
    """3x3 matrix L[c][d] = sum over successors u in class d of w(t,u)^2, t in class c.
    For t in X: tbar in Y (ordinary).  For t in Z: tbar in Z.  For t in Y: tbar in X (extra)."""
    e = 2 * p - 1
    v = q * q + q + 1
    sz = {"X": e, "Y": e, "Z": v - e}
    L = {}
    # tbar ordinary rows (t in X or Z): u extra -> w=oe ; u ordinary != tbar -> w=oo
    for c in ("X", "Z"):
        L[(c, "X")] = sz["X"] * w["oe"] ** 2
        L[(c, "Y")] = (sz["Y"] - (1 if c == "X" else 0)) * w["oo"] ** 2
        L[(c, "Z")] = (sz["Z"] - (1 if c == "Z" else 0)) * w["oo"] ** 2
    # tbar extra row (t in Y): u extra != tbar -> w=ee ; u ordinary -> w=eo
    L[("Y", "X")] = (sz["X"] - 1) * w["ee"] ** 2
    L[("Y", "Y")] = sz["Y"] * w["eo"] ** 2
    L[("Y", "Z")] = sz["Z"] * w["eo"] ** 2
    return L


def main():
    print("=== p = 3, q = 81: exact row bounds (proof of Lemma 6.4) ===")
    p, q = 3, 81
    e, v, r, cp, K = kernels(p, q)
    wB, wA = K["B"], K["A"]
    print("v =", v, " r =", r, " c_p =", cp, " |T| =", v + e)
    print("B kernel:", {k: str(x) for k, x in wB.items()})
    print("A kernel:", {k: str(x) for k, x in wA.items()})
    dom = all(wA[k] <= wB[k] for k in ("oo", "oe", "eo", "ee"))
    print("domination A <= B at class level:", dom, "; A extra-extra =", wA["ee"])
    rev = (wB["oe"] == wB["eo"])
    print("reversal symmetry (mixed entries equal):", rev)
    ord_bound = Fr(q, q + 1) + e * r**2 + Fr(e * (e + 1), (q + 1) ** 2)
    ext_bound = (e - 1 + (v + e * (e + 1)) * r**2) / (e + 2)
    print("ordinary row bound =", ord_bound, "=", float(ord_bound))
    print("extra row bound    =", ext_bound, "=", float(ext_bound))
    print("claimed ordinary   = 73664436152/74181603769 ->", ord_bound == Fr(73664436152, 74181603769))
    print("claimed extra      = 221387048/308906143     ->", ext_bound == Fr(221387048, 308906143))
    print("both < 199/200:", ord_bound < Fr(199, 200) and ext_bound < Fr(199, 200))
    # exact f-certificate on the lumped matrix: f = e+2 on Y (tbar extra), 1 on X, Z
    L = lumped_M(p, q, wB)
    f = {"X": 1, "Y": e + 2, "Z": 1}
    ratios = {c: sum(L[(c, d)] * f[d] for d in "XYZ") / f[c] for c in "XYZ"}
    print("exact (Mf)/f per class:", {c: float(x) for c, x in ratios.items()})
    print("max class ratio equals claimed ordinary bound:", max(ratios.values()) == ord_bound,
          "; Y-ratio equals extra bound:", ratios["Y"] == ext_bound)
    # Perron root of the lumped matrix (true exponential rate of sum P(W)^2)
    # (Mg)(t) = sum_d L[c][d] g_d for t in class c; 1^T M^{h-1} 1 grows like the Perron root.
    Mn = np.array([[float(L[(c, d)]) for d in "XYZ"] for c in "XYZ"])
    rho = max(abs(np.linalg.eigvals(Mn)))
    print("spectral radius of lumped M (= decay base of sum P(W)^2):", rho)
    sumf = (v + e) + e * (e + 1)
    print("sum f =", sumf)
    # h threshold for sumf*(199/200)^(h-1) <= exp(-h/400)
    h = 1
    while sumf * (199 / 200) ** (h - 1) > exp(-h / 400):
        h += 1
    print("smallest h with 6678*(199/200)^(h-1) <= e^{-h/400}:", h, "(the paper states h >= 3508)")
    # check monotone beyond
    print("holds at h=4000:", sumf * (199 / 200) ** 3999 <= exp(-4000 / 400))
    # type counts at n0 = 2 c_p v^2
    n0 = 2 * cp * v * v
    perlineA = Fr(n0, 2 * v)
    print("n0 =", n0, "; per line on A_+: each p-subset", perlineA * r / cp,
          ", empty", perlineA * (1 - comb(e, p) * r / cp), "; per line on B: all extras",
          Fr(n0, v) * r, ", empty", Fr(n0, v) * (1 - r), "; A-pool nr/2 =", n0 * r / 2)
    cross = sorted({a + b for a in (1, q + 1) for b in (0, p)})
    print("cross sizes:", cross, "mod p:", [x % p for x in cross])

    print()
    print("=== General odd p (proof of Lemma 6.4), smallest admissible q = p^k >= 2e(e+2) ===")
    for p in (3, 5, 7, 11, 13):
        q = smallest_q(p)
        e, v, r, cp, K = kernels(p, q)
        wB, wA = K["B"], K["A"]
        assert wA["ee"] == Fr(1, 2) and wA["oo"] == wB["oo"] and wA["oe"] == wB["oe"] and wA["eo"] == wB["eo"]
        assert wB["oo"] == Fr(1, q + 1) and wB["oe"] == r and wB["eo"] == r and wB["ee"] == 1
        assert r < Fr(1, q)
        U = Fr(q, q + 1) + e * r**2 + Fr(e * (e + 1), (q + 1) ** 2)
        V = (e - 1 + (v + e * (e + 1)) * r**2) / (e + 2)
        Ub1 = 1 - Fr(1, q + 1) + Fr(e * (e + 2), q * q)
        Ub2 = 1 - Fr(1, q + 1) + Fr(1, 2 * q)
        Vb = (e + Fr(1, q) + Fr(e * (e + 1), q * q)) / (e + 2)
        L = lumped_M(p, q, wB)
        f = {"X": 1, "Y": e + 2, "Z": 1}
        ratios = {c: sum(L[(c, d)] * f[d] for d in "XYZ") / f[c] for c in "XYZ"}
        Mn = np.array([[float(L[(c, d)]) for d in "XYZ"] for c in "XYZ"])
        rho = max(abs(np.linalg.eigvals(Mn)))
        n0 = 2 * cp * v * v
        integral = all(x.denominator == 1 for x in (Fr(n0, 2 * v) * r / cp, Fr(n0, v) * r, n0 * r / 2,
                                                         Fr(n0, 2 * v) * (1 - comb(e, p) * r / cp)))
        cross = sorted({a + b for a in (1, q + 1) for b in (0, p)})
        print(f"p={p:2d} e={e:2d} q={q:5d} 2e(e+2)={2*e*(e+2):5d} v={v} c_p={cp}")
        print(f"   U={float(U):.9f} (<{float(Ub1):.9f} <= {float(Ub2):.9f} < 1: {U < Ub1 <= Ub2 < 1})"
              f"  V={float(V):.9f} (< {float(Vb):.9f} < 1: {V < Vb < 1})")
        print(f"   exact lumped (Mf)/f: X={float(ratios['X']):.9f} Y={float(ratios['Y']):.9f} Z={float(ratios['Z']):.9f};"
              f" max==U: {max(ratios['X'], ratios['Z']) == U}, Y==V: {ratios['Y'] == V}")
        print(f"   Perron root of lumped M = {rho:.9f};  A-extra-extra freq = {wA['ee']};"
              f" integrality at 2c_p v^2: {integral};  cross mod p: {[x % p for x in cross]};"
              f" min degree q+1 = {q+1}, d_* = {q+1+e}")


if __name__ == "__main__":
    main()
