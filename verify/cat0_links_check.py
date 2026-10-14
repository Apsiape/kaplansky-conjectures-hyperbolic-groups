#!/usr/bin/env python3
"""Verification of the link computations in Section 9 (Theorem 9.1, used for Theorem D) of the paper.

Complex of groups over the cone K on the incidence graph I of (V, F):
  vertices O (apex), f in F, v in V;  one triangle (O, f, v) per incidence v in f.
  Local groups: K_v = (Z/l)^2 at v, L_f = Z/l at f and on the edge {f, v} (mapped into K_v
  by iota_vf, whose images are the l+1 distinct order-l subgroups of K_v), trivial elsewhere.

Link of a vertex sigma in the development (Bridson-Haefliger II.12):
  vertices  = cosets G_sigma / G_e  for edges e of K at sigma,
  edges     = cosets G_sigma / G_T  for triangles T at sigma, joining gG_e and gG_e'.

Checks:
 (1) l in {3,5,7}: the v-link (points x in F_l^2 = K_v/1, "lines" x + iota(L_f) = K_v/iota(L_f),
     edges x -- x + L) is the point-line incidence graph of AG(2,l): l^2 points, l(l+1) lines,
     point degree l+1, line degree l, any two points on exactly one common line; girth 6.
 (2) the f-link is K_{l,|f|} (|f| = q in 197b; q = 4, 8): girth 4.
 (3) if two lines through v had the same image subgroup, the v-link acquires a 4-cycle.
 (4) angle bookkeeping (exact, sympy): pi/6+pi/2+pi/3 = pi (Euclidean), pi/7+pi/2+pi/3 < pi
     (hyperbolic), link inequalities girth*angle >= 2 pi for g = 12 and g = 14, and the fact
     that girth exactly 12 forces angle sum >= pi (no single-shape CAT(-1) metric on this complex).
"""
import itertools
import networkx as nx
import sympy as sp


def lines_of_plane(l):
    """The l+1 one-dimensional subspaces of F_l^2, each as a frozenset of vectors."""
    dirs = [(1, m) for m in range(l)] + [(0, 1)]
    return [frozenset(((t * d[0]) % l, (t * d[1]) % l) for t in range(l)) for d in dirs]


def v_link(l, subgroup_images):
    """Link at v of the development: bipartite graph points / cosets.
    subgroup_images: list (indexed by the members f through v) of subgroups of F_l^2."""
    G = nx.Graph()
    pts = [(x, y) for x in range(l) for y in range(l)]
    for p in pts:
        G.add_node(("pt", p))
    for fi, S in enumerate(subgroup_images):
        cosets = set()
        for p in pts:
            coset = frozenset(((p[0] + s[0]) % l, (p[1] + s[1]) % l) for s in S)
            cosets.add(coset)
        for c in cosets:
            node = ("line", fi, c)        # coset of the subgroup attached to member f_i
            G.add_node(node)
            for p in c:
                G.add_edge(("pt", p), node)   # edge = triangle (O,f,v) coset g*1 joining g to g*iota(L_f)
    return G


def check_affine_plane(l):
    L = lines_of_plane(l)
    assert len(L) == l + 1 and len(set(L)) == l + 1
    G = v_link(l, L)
    pts = [n for n in G if n[0] == "pt"]
    lines = [n for n in G if n[0] == "line"]
    assert len(pts) == l * l and len(lines) == l * (l + 1)
    assert all(G.degree(p) == l + 1 for p in pts)
    assert all(G.degree(L_) == l for L_ in lines)
    # any two distinct points lie on exactly one common line
    for p, q in itertools.combinations(pts, 2):
        common = set(G[p]) & set(G[q])
        assert len(common) == 1, (p, q, common)
    # compare with the textbook AG(2,l): lines {(x,y): y = m x + c} and {x = c}
    ag = nx.Graph()
    for x in range(l):
        for y in range(l):
            ag.add_node(("P", x, y))
    for m in range(l):
        for c in range(l):
            for x in range(l):
                ag.add_edge(("P", x, (m * x + c) % l), ("L", m, c))
    for c in range(l):
        for y in range(l):
            ag.add_edge(("P", c, y), ("V", c))
    # explicit isomorphism: each coset vertex <-> the textbook line with the same point set
    ag_lines = {}
    for n in ag:
        if n[0] != "P":
            ag_lines[frozenset((p[1], p[2]) for p in ag[n])] = n
    coset_sets = [n[2] for n in lines]
    iso = (len(ag_lines) == len(coset_sets) and set(coset_sets) == set(ag_lines)
           and all(set(ag[ag_lines[c]]) == {("P",) + p for p in c} for c in coset_sets))
    g = nx.girth(G)
    return iso, g


def check_f_link(l, q):
    G = nx.complete_bipartite_graph(l, q)   # L_f/1 (l vertices) versus one vertex per point v in f
    return nx.girth(G)


def check_coincident_lines(l):
    L = lines_of_plane(l)
    bad = [L[0], L[0]] + L[2:]          # member f_1 mapped onto the same subgroup as f_0
    G = v_link(l, bad)
    return nx.girth(G)


def angles():
    pi = sp.pi
    out = {}
    out["euclid_sum"] = sp.nsimplify(pi / 6 + pi / 2 + pi / 3)
    out["hyp_sum"] = sp.nsimplify(pi / 7 + pi / 2 + pi / 3)
    out["hyp_sum_lt_pi"] = bool(sp.simplify(pi / 7 + pi / 2 + pi / 3 - pi) < 0)
    # link conditions: shortest injective loop = girth * angle  >= 2 pi
    out["v_link"] = sp.simplify(6 * pi / 3 - 2 * pi)
    out["f_link"] = sp.simplify(4 * pi / 2 - 2 * pi)
    out["O_link_g12"] = sp.simplify(12 * pi / 6 - 2 * pi)
    out["O_link_g14"] = sp.simplify(14 * pi / 7 - 2 * pi)
    # girth exactly 12: link condition forces alpha_O >= 2pi/12, alpha_f >= 2pi/4, alpha_v >= 2pi/6
    out["min_sum_g12"] = sp.simplify(2 * pi / 12 + 2 * pi / 4 + 2 * pi / 6)
    out["min_sum_g14"] = sp.simplify(2 * pi / 14 + 2 * pi / 4 + 2 * pi / 6)
    return out


if __name__ == "__main__":
    ok = True
    for l in (3, 5, 7):
        iso, g = check_affine_plane(l)
        print(f"l={l}: v-link isomorphic to incidence graph of AG(2,{l}): {iso}; girth = {g}")
        ok &= iso and g == 6
        gb = check_coincident_lines(l)
        print(f"l={l}: two members mapped to the same subgroup -> v-link girth = {gb} (4-cycle created)")
        ok &= gb == 4
        for q in (4, 8):
            gf = check_f_link(l, q)
            print(f"l={l}, q={q}: f-link K_(l,q) girth = {gf}")
            ok &= gf == 4
    A = angles()
    print("pi/6+pi/2+pi/3 =", A["euclid_sum"], "(Euclidean (2,3,6) triangle)")
    print("pi/7+pi/2+pi/3 =", A["hyp_sum"], "< pi:", A["hyp_sum_lt_pi"], "(hyperbolic (2,3,7) triangle)")
    print("girth*angle - 2pi:  v-link 6*pi/3:", A["v_link"], " f-link 4*pi/2:", A["f_link"],
          " O-link 12*pi/6:", A["O_link_g12"], " O-link 14*pi/7:", A["O_link_g14"])
    print("girth 12 forces angle sum >=", A["min_sum_g12"], "(= pi: Euclidean at best);",
          "girth 14 allows angle sum", A["min_sum_g14"], "< pi")
    ok &= A["euclid_sum"] == sp.pi and A["hyp_sum_lt_pi"] and A["v_link"] == 0 and A["f_link"] == 0
    ok &= A["O_link_g12"] == 0 and A["O_link_g14"] == 0 and A["min_sum_g12"] == sp.pi
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
