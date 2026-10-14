#!/usr/bin/env python3
"""Randomized check of the short-closure construction (Lemma 3.6).

On random simple graphs with minimum degree >= 5 we run the construction of the proof exactly:
for a vertex z and at most two forbidden undirected edges at z, find two distinct
non-backtracking walks of length k = ceil(log2 |V|) + 1 from z (avoiding the forbidden edges)
with the same endpoint, and freely reduce P Q^{-1}; then close an immersed path S from a to b
as S J_b R J_a, with R a geodesic from b to a.  We check that the result is a closed,
cyclically non-backtracking edge path that starts with S, and that the added length is at most
|R| + 4k, i.e. at most diam + 4k (in the paper: dL + 4k <= D0 L).
Edges are undirected pairs; a path is a list of vertices (consecutive vertices adjacent).
"""
import random, math, itertools
import networkx as nx

def nb_ok(path):            # no backtracking inside a vertex path
    return all(path[i] != path[i + 2] for i in range(len(path) - 2))

def loop_at(G, z, forbidden, k, rng):
    H = G.copy()
    H.remove_edges_from(forbidden)
    assert min(dict(H.degree()).values()) >= 3
    # enumerate non-backtracking walks of length k from z, grouped by endpoint
    by_end = {}
    stack = [[z]]
    while stack:
        w = stack.pop()
        if len(w) == k + 1:
            e = w[-1]
            if e in by_end and by_end[e] != w:
                P, Q = by_end[e], w
                break
            by_end.setdefault(e, w)
            continue
        nbrs = list(H.neighbors(w[-1])); rng.shuffle(nbrs)
        for v in nbrs:
            if len(w) >= 2 and v == w[-2]:
                continue
            stack.append(w + [v])
    else:
        raise AssertionError("no two walks with a common endpoint")
    # free reduction of P Q^{-1}: remove the common terminal segment
    i = 0
    while i < k and P[-1 - i] == Q[-1 - i] and P[-2 - i] == Q[-2 - i]:
        i += 1
    loop = P[:len(P) - i] + Q[:len(Q) - i - 1][::-1]
    assert loop[0] == z and loop[-1] == z and len(loop) >= 3
    assert nb_ok(loop) and len(loop) - 1 <= 2 * k
    for e in forbidden:     # first and last edges avoid the forbidden edges
        assert {loop[0], loop[1]} != set(e) and {loop[-2], loop[-1]} != set(e)
    return loop

def close(G, S, rng):
    n = G.number_of_nodes(); k = math.ceil(math.log2(n)) + 1
    a, b = S[0], S[-1]
    R = nx.shortest_path(G, b, a)
    first_S, last_S = (S[0], S[1]), (S[-2], S[-1])
    if len(R) >= 2:
        Jb = loop_at(G, b, [last_S, (R[0], R[1])], k, rng)
        Ja = loop_at(G, a, [(R[-2], R[-1]), first_S], k, rng)
        C = S + Jb[1:] + R[1:] + Ja[1:]
    else:
        Ja = loop_at(G, a, [last_S, first_S], k, rng)
        C = S + Ja[1:]
    added = len(C) - len(S)
    return C, added, len(R) - 1, k

def main():
    rng = random.Random(14102026)
    trials = 0
    for n in (16, 32, 64, 128):
        for deg in (5, 6):
            for seed in range(15):
                G = nx.random_regular_graph(deg, n, seed=rng.randrange(10**9))
                if not nx.is_connected(G):
                    continue
                diam = nx.diameter(G)
                for _ in range(10):
                    # random immersed path S of length 1..12
                    L = rng.randint(1, 12)
                    S = [rng.randrange(n)]
                    S.append(rng.choice(list(G.neighbors(S[0]))))
                    while len(S) < L + 1:
                        nxt = [v for v in G.neighbors(S[-1]) if v != S[-2]]
                        S.append(rng.choice(nxt))
                    C, added, r, k = close(G, S, rng)
                    assert C[0] == C[-1], "not closed"
                    assert C[:len(S)] == S, "S not retained"
                    assert nb_ok(C), "backtracking inside"
                    assert C[-2] != C[1], "backtracking at the closing turn"
                    assert added <= r + 4 * k <= diam + 4 * k, "too long"
                    trials += 1
    print(f"short closures: {trials} random immersed paths closed in random 5- and 6-regular graphs (n <= 128)")
    print("ALL CHECKS PASSED")

if __name__ == "__main__":
    main()
