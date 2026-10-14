#!/usr/bin/env python3
"""Randomized check of the interval lemma (Lemma 3.8 / Appendix A).

A picture of N0 disks on a sphere with E arcs is a connected planar combinatorial
map: vertices = disks, half-edges = letter occurrences, sigma = boundary order,
alpha = arc involution. A gap is the corner between x and sigma(x); the region
through a corner is its orbit under psi(x) = alpha(sigma(x)).

We generate random planar maps (a random plane tree, then edges added inside
faces, which preserves planarity), label arcs by letters so that every boundary
word is cyclically reduced, cut circles into N' >= N0 pieces at random, and check:
  * Euler identity  sum_Q (l_Q - 2) = 2 N0 - 4  (all regions are discs here);
  * monogon regions occur only at the break (at most one); fewer than 7 N0 non-good gaps;
  * half of the pictures carry a break: one corner of one circle where the two letters may be
    inverse (we force this when possible); the break is always cut;
  * the cut set of Appendix A is partner-invariant, has <= 9 N' elements;
  * every run is carried by the arcs onto a run, in reversed order, never itself;
  * hence at most 9N'/2 <= 6N' interval pairs.
"""
import random, sys

def random_picture(rng, N0, extra, alphabet=40, with_break=False):
    sigma = {}            # half-edge -> next half-edge at its vertex
    vert = {}             # half-edge -> vertex
    alpha = {}
    rot = {v: [] for v in range(N0)}
    he = 0
    def new_edge(u, v, after_u=None, after_v=None):
        nonlocal he
        a, b = he, he + 1; he += 2
        alpha[a], alpha[b] = b, a
        vert[a], vert[b] = u, v
        for h, w, aft in ((a, u, after_u), (b, v, after_v)):
            r = rot[w]
            if aft is None:
                r.insert(rng.randrange(len(r) + 1), h)
            else:
                r.insert(r.index(aft) + 1, h)
        return a, b
    # random plane tree
    for v in range(1, N0):
        new_edge(rng.randrange(v), v)
    if N0 == 1:
        # a single disk needs at least one arc: a loop around the far side
        a, b = new_edge(0, 0)
    def rebuild():
        sigma.clear()
        for v, r in rot.items():
            for i, h in enumerate(r):
                sigma[h] = r[(i + 1) % len(r)]
    rebuild()
    for _ in range(extra):
        corners = list(sigma.keys())
        x = rng.choice(corners)
        # corners of the same face as x
        face, y = [], x
        while True:
            face.append(y); y = alpha[sigma[y]]
            if y == x: break
        cand = [y for y in face if y != x]
        if not cand: continue
        y = rng.choice(cand)
        new_edge(vert[x], vert[y], after_u=x, after_v=y)
        rebuild()
    # thicken random arcs into bundles of parallel arcs (creates good digons, long runs)
    for _ in range(rng.randint(0, 3 * N0 + 6)):
        a = rng.choice([h for h in alpha if h < alpha[h]]); b = alpha[a]
        u, v = vert[a], vert[b]
        rb = rot[v]; pred_b = rb[(rb.index(b) - 1) % len(rb)]
        if pred_b == a or (u == v and pred_b in (a,)):
            continue
        new_edge(u, v, after_u=a, after_v=pred_b)
        rebuild()
    brk = None
    monogon_loop = None
    if with_break and rng.random() < 0.5:
        # a loop whose two ends are consecutive on circle 0: an empty monogon region at the break
        x = rng.choice(rot[0])
        a, b = new_edge(0, 0, after_u=x, after_v=None)
        rot[0].remove(b); rot[0].insert(rot[0].index(a) + 1, b)
        rebuild()
        monogon_loop = (a, b)
    # labels: edge e=(a,b) gets t; lab(a)=t, lab(b)=-t; require lab(sigma x) != -lab(x)
    lab = {}
    for e in alpha:
        if e < alpha[e]:
            t = rng.randint(1, alphabet) * rng.choice((1, -1)); lab[e], lab[alpha[e]] = t, -t
    if monogon_loop is not None:
        brk = monogon_loop[0]               # corner between a and b: inverse letters, allowed only here
    elif with_break:
        brk = rng.choice(rot[0])            # corner after brk (on circle 0) is the break
        # force inverse letters across the break when possible, to exercise the monogon case
        y = sigma[brk]
        if monogon_loop is None and y != brk and alpha[y] != brk:
            a = min(y, alpha[y]); t = -lab[brk]
            if a == y: lab[y], lab[alpha[y]] = t, -t
            else: lab[alpha[y]], lab[y] = -t, t
    for _ in range(10000):
        bad = [x for x in sigma if lab[sigma[x]] == -lab[x] and x != brk]
        if not bad: break
        x = rng.choice(bad)
        a = min(x, alpha[x])
        if monogon_loop is not None and a == min(monogon_loop):
            a = min(sigma[x], alpha[sigma[x]])   # resample the other letter at this corner instead
        t = rng.randint(1, alphabet) * rng.choice((1, -1))
        lab[a], lab[alpha[a]] = t, -t
    else:
        return None
    return rot, sigma, alpha, lab, brk

def check(rng, N0, extra, with_break=False):
    pic = random_picture(rng, N0, extra, with_break=with_break)
    if pic is None: return None
    rot, sigma, alpha, lab, brk = pic
    psi = lambda x: alpha[sigma[x]]
    edge = lambda h: min(h, alpha[h])
    # regions
    seen, faces = set(), []
    for x in sigma:
        if x in seen: continue
        f, y = [], x
        while y not in seen:
            seen.add(y); f.append(y); y = psi(y)
        faces.append(f)
    E = len(alpha) // 2
    assert sum(len(f) - 2 for f in faces) == 2 * N0 - 4, "Euler identity"
    monogons = [f for f in faces if len(f) == 1]
    assert len(monogons) <= (1 if brk is not None else 0), "monogon away from the break"
    assert all(f[0] == brk for f in monogons), "monogon not at the break"
    good, partner = set(), {}
    for f in faces:
        if len(f) == 2 and edge(sigma[f[0]]) != edge(sigma[f[1]]):
            good.update(f); partner[f[0]], partner[f[1]] = f[1], f[0]
    nongood = [x for x in sigma if x not in good]
    assert len(nongood) < 7 * N0, ("non-good gaps", len(nongood), N0)
    # pieces
    cut = set(nongood); Nprime = 0
    if brk is not None: cut.add(brk)
    for v, r in rot.items():
        d = len(r); p = rng.randint(1, d); Nprime += p
        starts = sorted(rng.sample(range(d), p))
        for s in starts:               # cut the gap just before position s
            cut.add(r[(s - 1) % d])
    for x in list(cut):
        if x in good: cut.add(partner[x])
    assert all(partner[x] in cut for x in cut if x in good), "invariance"
    assert len(cut) <= 9 * Nprime
    # runs: start after each cut corner
    runs, run_of = [], {}
    for v, r in rot.items():
        d = len(r)
        cuts_here = [i for i, h in enumerate(r) if h in cut]
        assert cuts_here, "every circle is cut"
        for j, ci in enumerate(cuts_here):
            nxt = cuts_here[(j + 1) % len(cuts_here)]
            seq, i = [], (ci + 1) % d
            while True:
                seq.append(r[i])
                if i == nxt: break
                i = (i + 1) % d
            for h in seq: run_of[h] = len(runs)
            runs.append(seq)
    assert len(runs) <= 9 * Nprime
    for k, seq in enumerate(runs):
        img = [alpha[h] for h in seq][::-1]
        tgt = run_of[img[0]]
        assert runs[tgt] == img, "run not carried onto a run in reversed order"
        assert tgt != k, "run carried onto itself"
        for i in range(len(seq) - 1):
            assert seq[i] != brk, "break inside a run"
    pairs = len(runs) // 2
    assert 2 * pairs <= 9 * Nprime <= 12 * Nprime
    return N0, E, Nprime, pairs, len(monogons)

def main():
    rng = random.Random(20261014)
    done = 0
    nb = 0; nm = 0
    while done < 4000:
        N0 = rng.randint(1, 12); extra = rng.randint(0, 40)
        wb = (done % 2 == 1)
        r = check(rng, N0, extra, with_break=wb)
        if r:
            done += 1; nb += wb; nm += r[4]
    print(f"interval lemma: {done} random planar pictures checked (N0 <= 12, up to ~90 arcs, with bundles of parallel arcs), {nb} of them with a break, {nm} with a monogon at the break")
    print("ALL CHECKS PASSED")

if __name__ == "__main__":
    main()
