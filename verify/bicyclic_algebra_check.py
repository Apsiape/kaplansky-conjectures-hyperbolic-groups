#!/usr/bin/env python3
"""Verification of the algebra in Section 2 (Lemmas 2.1-2.3) of the paper.  (The script writes n for the
square-zero element that the paper calls nu.)

PART 1 (Lemma 2.1).  The bicyclic monoid B = < a, b | ab = 1 > has normal forms b^i a^j (i, j >= 0),
with product  (b^i a^j)(b^k a^l) = b^(i + k - m) a^(j + l - m),  m = min(j, k)   (cancel a b = 1).
Its monoid ring R[B] is the *universal* ring with a one-sided inverse: for every ring S (with 1) and
elements a', b' in S with a'b' = 1 there is a unique unital ring homomorphism Z[B] -> S with
a -> a', b -> b' (the monoid map B -> (S, .) exists because the only relation ab = 1 holds in S).
Hence every identity between non-commutative polynomials in a, b with integer coefficients that
holds in Z[B] holds in EVERY ring in which ab = 1, and identities checked in F2[B] hold in every
F2-algebra with ab = 1.  We therefore verify the equalities of Lemma 2.1 in Z[B] (all rings) and in
F2[B] (characteristic two).

The "!=" assertions of Lemma 2.1 (e != 0, 1;  n != 0) are NOT consequences of identities: in a ring
where ab = 1 they follow from the hypothesis ba != 1 by the short arguments in the proof
(a e b = 1, a n = 1 - e).  In B itself ba != 1, so these checks merely illustrate them in the
universal example; we also verify the two identities a e b = 1 and a n = 1 - e that the proof uses.

PART 2 (Lemma 2.2).  For g != 1 in a torsion-free group, n = lam*g - 1 has n^2 = lam^2 g^2 - 2 lam g + 1,
whose identity coefficient is 1 because 1, g, g^2 are pairwise distinct.  We verify the expansion
symbolically (sympy, non-commuting symbol g, generic lam) and compute the identity coefficient in
concrete group rings: Z = <t> (Laurent polynomials, over Z and over F2) and the free group F(x,y)
(reduced words), for several g and lam.  (Z[Z] is a domain, so no square-zero element exists there;
the point of the check is the coefficient computation used in the proof.)

PART 3 (Lemma 2.3).  The identity (beta g alpha)^2 = beta g (alpha beta) g alpha, which gives n^2 = 0
from alpha beta = 0, is checked with non-commuting sympy symbols.
"""
import itertools
from collections import defaultdict
import sympy as sp


# ---------- PART 1: the monoid ring of the bicyclic monoid ----------
def bmul(u, v):
    (i, j), (k, l) = u, v
    m = min(j, k)
    return (i + k - m, j + l - m)


class BElt:
    """Element of R[B] with R = Z (mod=None) or Z/mod; stored as dict {(i, j): coeff}."""
    def __init__(self, d=None, mod=None):
        self.mod = mod
        self.d = {}
        for key, c in (d or {}).items():
            self._add(key, c)

    def _add(self, key, c):
        c = self.d.get(key, 0) + c
        if self.mod:
            c %= self.mod
        if c:
            self.d[key] = c
        else:
            self.d.pop(key, None)

    def __add__(self, o):
        r = BElt(self.d, self.mod)
        for k, c in o.d.items():
            r._add(k, c)
        return r

    def __neg__(self):
        return BElt({k: -c for k, c in self.d.items()}, self.mod)

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        r = BElt({}, self.mod)
        for (u, c), (v, e) in itertools.product(self.d.items(), o.d.items()):
            r._add(bmul(u, v), c * e)
        return r

    def __eq__(self, o):
        return self.d == o.d

    def __repr__(self):
        if not self.d:
            return "0"
        return " + ".join(f"{c}*b^{i}a^{j}" for (i, j), c in sorted(self.d.items()))


def check_lemma21(mod):
    one = BElt({(0, 0): 1}, mod)
    zero = BElt({}, mod)
    a = BElt({(0, 1): 1}, mod)
    b = BElt({(1, 0): 1}, mod)
    e = b * a
    n = b * (one - e)
    res = {}
    res["ab = 1"] = (a * b == one)
    res["ba != 1 (in B)"] = (b * a != one)
    res["e^2 = e"] = (e * e == e)
    res["e(1-e) = 0"] = (e * (one - e) == zero)
    res["(1-e)e = 0"] = ((one - e) * e == zero)
    res["(1-e)b = 0"] = ((one - e) * b == zero)
    res["n^2 = 0"] = (n * n == zero)
    res["(1+n)(1-n) = 1"] = ((one + n) * (one - n) == one)
    res["(1-n)(1+n) = 1"] = ((one - n) * (one + n) == one)
    res["a n = 1 - e"] = (a * n == one - e)
    res["a e b = 1"] = (a * e * b == one)
    res["e != 0 (illustrative)"] = (e != zero)
    res["e != 1 (illustrative)"] = (e != one)
    res["n != 0 (illustrative)"] = (n != zero)
    return res, e, n


# ---------- PART 2: identity coefficient of (lam g - 1)^2 ----------
def symbolic_expansion():
    lam = sp.Symbol("lam", commutative=True)
    g = sp.Symbol("g", commutative=False)
    expr = sp.expand((lam * g - 1) ** 2)
    target = sp.expand(lam ** 2 * g ** 2 - 2 * lam * g + 1)
    return expr, sp.simplify(expr - target) == 0


def laurent_identity_coeff(k, lam, mod=None):
    """In R[Z], Z = <t>, take g = t^k (k != 0); return the coefficient of t^0 in (lam t^k - 1)^2."""
    poly = defaultdict(int)
    terms = {k: lam, 0: -1}
    for (e1, c1), (e2, c2) in itertools.product(terms.items(), terms.items()):
        poly[e1 + e2] += c1 * c2
    c0 = poly[0]
    return c0 % mod if mod else c0


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == x.swapcase():
            out.pop()
        else:
            out.append(x)
    return "".join(out)


def free_group_identity_coeff(g, lam, mod=None):
    """In R[F(x,y)] (letters x,y; inverses X,Y): identity coefficient of (lam g - 1)^2."""
    elt = {g: lam, "": -1}
    prod = defaultdict(int)
    for (w1, c1), (w2, c2) in itertools.product(elt.items(), elt.items()):
        prod[free_reduce(w1 + w2)] += c1 * c2
    c = prod[""]
    return c % mod if mod else c


# ---------- PART 3: the identity behind Lemma 2.3 ----------
def connell_identity():
    al, be, g = sp.symbols("alpha beta g", commutative=False)
    lhs = sp.expand((be * g * al) ** 2)
    rhs = sp.expand(be * g * (al * be) * g * al)
    return sp.simplify(lhs - rhs) == 0


if __name__ == "__main__":
    allok = True
    for mod, name in [(None, "Z[B] (universal: holds in every ring with ab = 1)"),
                      (2, "F2[B] (holds in every F2-algebra with ab = 1)")]:
        res, e, n = check_lemma21(mod)
        print(f"== Lemma 2.1 in {name} ==")
        print(f"   e = ba = {e};   n = b(1-e) = {n}")
        for k, v in res.items():
            print(f"   {k:28s} {v}")
            allok &= v
    expr, ok = symbolic_expansion()
    print("== Lemma 2.2 ==")
    print(f"   (lam g - 1)^2 expands to {expr};  equals lam^2 g^2 - 2 lam g + 1: {ok}")
    allok &= ok
    for k in (1, 2, -3):
        for lam in (1, 2, 5):
            c = laurent_identity_coeff(k, lam)
            c2 = laurent_identity_coeff(k, lam, 2) if lam % 2 else None
            print(f"   Z-group ring, g = t^{k}, lam = {lam}: identity coeff of n^2 = {c}"
                  + (f"; over F2 = {c2}" if c2 is not None else ""))
            allok &= (c == 1) and (c2 in (None, 1))
    for g in ("x", "xy", "xYxY", "xyXY"):
        c = free_group_identity_coeff(g, 1)
        c2 = free_group_identity_coeff(g, 1, 2)
        print(f"   free group, g = {g}, lam = 1: identity coeff of n^2 = {c}; over F2 = {c2}")
        allok &= (c == 1 and c2 == 1)
    ok3 = connell_identity()
    print("== Lemma 2.3 ==")
    print(f"   (beta g alpha)^2 == beta g (alpha beta) g alpha  (non-commutative symbols): {ok3}")
    allok &= ok3
    print("ALL CHECKS PASSED" if allok else "SOME CHECK FAILED")
