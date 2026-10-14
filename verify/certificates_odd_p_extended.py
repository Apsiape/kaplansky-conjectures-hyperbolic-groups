"""Exact checks for Section 7 of the paper (Theorem C) at the actual parameter q = p^5, without enumerating PG(2,q).

  * The extra plane PG(2,p), enumerated for every odd prime p <= 43: the projective-plane identity
    N N^T = pI + J, blocks of size p^2 meeting pairwise in p^2 - p points, every extra letter in p^2
    blocks and every pair of extra letters in p^2 - p blocks; the extra-plane vector z (line sums
    divisible by p, z = M beta with beta = 1 - (line sum)/p for the block matrix M = J - N, and for
    p <= 13 the explicit inverse M^-1 = J/p^2 - N^T/p); and the pairing of the values of z with 1 - kappa.
  * The residue bookkeeping for the involution at q = p^5, for every odd prime p <= 199: the residues
    of xi are invariant under y -> 1 - y, the self-complementary residue h_q occurs exactly 2q times
    (no value of z, and not 1 - kappa, is congruent to h_q), every extra letter finds an affine partner,
    and the remaining residues are still invariant.
  * For every odd prime p <= 199, in exact rational arithmetic: both row bounds of the Perron
    certificate, the inequality 2 s p^2 (q+1)/q^2 <= 6344/6561 and the other inequalities of its proof,
    the smallest turn weight 1/(q+1), positivity of the uniform family, and the congruences of the
    intersection lemma.
In the code, tau = 1 - kappa and pi is the letter frequency lambda = (q+1)/v of Section 7.
"""
from fractions import Fraction as Fr
from collections import Counter
import numpy as np


def primes(lo, hi):
    return [n for n in range(lo, hi + 1) if n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))]


def pg2_prime(p):
    """points [x:y:1]->x+p*y, [m:1:0]->p^2+m, [1:0:0]->p^2+p ; lines as point lists"""
    s = p * p + p + 1
    lines = []
    for c in range(p):
        for b in range(p):                       # x + b y + c z = 0
            pts = [((-(b * y + c)) % p) + p * y for y in range(p)] + [p * p + (-b) % p]
            lines.append(pts)
    for c in range(p):                           # y + c z = 0
        lines.append([x + p * ((-c) % p) for x in range(p)] + [p * p + p])
    lines.append([p * p + m for m in range(p)] + [p * p + p])
    return s, lines


def centered(x, p):
    u = (p - 1) // 2
    x %= p
    return x if x <= u else x - p


def zvec(p):
    s = p * p + p + 1
    h, R = (p + 1) // 2, p * (p - 1) // 2
    z = [0] * s
    for y in range(p):
        for x in range(p):
            z[x + p * y] = centered(x - (h if y == 0 else 0), p)
    for m in range(p):
        z[p * p + m] = h
    z[p * p + p] = R
    return z


def extra_plane_checks(p):
    s, lines = pg2_prime(p)
    inc = np.zeros((s, s), dtype=np.float64)
    for j, L in enumerate(lines):
        assert len(set(L)) == p + 1
        inc[L, j] = 1
    assert (inc.sum(0) == p + 1).all() and (inc.sum(1) == p + 1).all()
    NNt = inc @ inc.T
    assert (NNt == p * np.eye(s) + 1).all(), "projective plane"
    comp = 1 - inc
    assert (comp.sum(0) == p * p).all()                       # block size p^2
    assert (comp.sum(1) == p * p).all()                       # each extra in p^2 blocks
    CC = comp.T @ comp
    off = CC[~np.eye(s, dtype=bool)]
    assert (off == p * p - p).all()                           # |D cap D'| = p^2 - p
    PP = comp @ comp.T
    assert (PP[~np.eye(s, dtype=bool)] == p * p - p).all()    # two extras in p^2-p blocks
    z = np.array(zvec(p), dtype=np.int64)
    inci = inc.astype(np.int64)
    ls = inci.T @ z
    assert (ls % p == 0).all()
    beta = 1 - ls // p
    assert ((1 - inci) @ beta == z).all(), "z = M beta"
    if p <= 13:   # explicit rational inverse of the block matrix
        Minv = Fr(1, p * p) * np.ones((s, s), dtype=object) - Fr(1, p) * inci.T.astype(object)
        Mo = (1 - inci).astype(object)
        I = Mo.dot(Minv)
        assert all(I[i, j] == (1 if i == j else 0) for i in range(s) for j in range(s))
        assert all(x.denominator == 1 for x in Minv.dot(z.astype(object)))
    pool = Counter(z.tolist() + [1 - p * (p - 1) // 2])
    for val, c in pool.items():
        assert pool[1 - val] == c
    return True


def residue_level(p):
    q = p ** 5
    s = p * p + p + 1
    R = p * (p - 1) // 2
    tau = 1 - R
    hq = (q + 1) // 2
    z = zvec(p)
    # special (non-uniform) residues; the affine part is q copies of every residue
    special = Counter()
    special[hq % q] += q            # ordinary points at infinity other than H
    special[tau % q] += 1           # H
    for x in z:
        special[x % q] += 1         # extras
    # invariance of the whole multiset = invariance of the special part
    for r, c in special.items():
        assert special[(1 - r) % q] == c, ("not complement-invariant", p, r)
    # self-complementary residue: unique solution of 2r = 1 mod q
    assert (2 * hq) % q == 1
    assert special[hq % q] == q and (q + special[hq % q]) % 2 == 0   # total 2q at h_q
    # no extra and no tau at h_q
    assert all(x % q != hq for x in z) and tau % q != hq
    # availability: extras needing affine partners of residue 1 - z_e
    need = Counter((1 - x) % q for x in z)
    assert max(need.values()) <= q
    # after removing extras + their partners, remaining ordinary multiset invariant:
    rem = Counter(special)
    for x in z:
        rem[x % q] -= 1
    aff = Counter()
    for r, c in need.items():
        aff[r] -= c                 # affine copies consumed
    tot = Counter()
    for r in set(rem) | set(aff):
        tot[r] = rem[r] + aff[r]    # deviation from uniform q
    for r, c in tot.items():
        assert tot[(1 - r) % q] == c, ("remaining not invariant", p, r)
    assert (q + tot[hq % q]) % 2 == 0
    return True


def perron(p):
    q = p ** 5
    s = p * p + p + 1
    v = q * q + q + 1
    pi = Fr(q + 1, v)
    gam = Fr(p - 1, p)
    lam = 1 - Fr(1, 2 * (q + 1))
    A = Fr(q, q + 1) + s * pi ** 2 + Fr(s * (p * p - 1), (q + 1) ** 2)
    B = (s - 1) * gam ** 2 + (v + s * (p * p - 1)) * pi ** 2
    b6 = Fr(2 * s * p * p * (q + 1), q * q)
    assert b6 < 1 and b6 <= Fr(6344, 6561)
    assert A < lam, ("ordinary row", p)
    assert B < lam * p * p, ("extra row", p)
    assert pi < Fr(1, q) and Fr(1, q + 1) < pi < gam      # min turn weight is 1/(q+1)
    assert (s - 1) * gam ** 2 == p * p - p - 1 + Fr(1, p)
    assert v * pi ** 2 < 1 + Fr(1, q)
    m_empty = p * p * v - s * (q + 1)
    assert m_empty == p * p * q * q - (p + 1) * (q + 1) > 0
    # congruences of the intersection lemma
    assert (q + 1) % p == 1 and s % p == 1 and (p * p) % p == 0 and (p * p - p) % p == 0
    assert (q + 1 + s) % p == 2
    # constants used in the transfer
    assert q - 1 >= 3 and (q - 3) / 2 > 0 and p * p % 1 == 0 and q % (p * p) == 0 and q > s
    return lam - A, lam * p * p - B


if __name__ == "__main__":
    for p in primes(3, 43):
        extra_plane_checks(p)
    print("extra-plane PG(2,p) checks PASS for odd primes 3..43")
    for p in primes(3, 199):
        residue_level(p)
    print("residue bookkeeping for the involution at q=p^5 PASS for odd primes 3..199")
    worst = None
    for p in primes(3, 199):
        ga, gb = perron(p)
        if p in (3, 5, 7, 11, 13):
            print(p, "ordinary-row slack", float(ga), " extra-row slack", float(gb))
    print("Perron row bounds, key inequality, min turn weight, m_empty, congruences PASS for odd primes 3..199")
