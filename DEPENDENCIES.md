# Dependency map

"OAI" means an input from OpenAI's unrefereed, AI-generated preprints, taken as stated and not re-proved in the
paper. Everything else is proved in the paper or is classical. Numbers refer to `paper/main.pdf`.

## The four inputs (Theorem 3.4, Table 2)

| Input | [OAI-196] | [OAI-197a] | Lean, model of [OAI-196] (commit adc7f12; unchanged at 1581d4c) | odd p, zero divisors (Section 6) | odd p, direct finiteness (Section 7) |
|---|---|---|---|---|---|
| (a) types: degrees; parity or congruence of the intersections | Section 2.1, (2.1) | Section 3.1, Prop. 3.1 | `degreeA_bounds`, `degreeB_bounds`, `odd_cross_intersections` (PatternCount.lean) | Lemma 6.3 | Lemma 7.2 |
| (b) a matching with girth >= L exists | Lemma 2.2 | Section 3.3 | `TypedGraphs.eventual_nonempty` (TypedGraphs.lean) | Lemma 6.5 | Prop. 7.9(a) |
| (c) component diameter <= dL with probability 1 - o(1) | Lemma 2.3 | Prop. 3.4 | `diameterA_tendsto`, `diameterB_tendsto` (TypedDiameter.lean) | Lemma 6.6 | Prop. 7.9(b) |
| (d) bounded-pattern estimate | Prop. 3.1 | Thm. 4.1 | `SampleGraph.exists_avoiding` (BoundedSystem.lean): existence form, (b)-(c) included, eps = 1/2467200, `I` counts interval sides | Prop. 6.7 | Prop. 7.9(c) |

Status of the inputs:
- **[OAI-196] model:** formalized in OpenAI's Lean development, in the existence form used in Corollary 5.4. The
  development was read, not rebuilt.
- **[OAI-197a] model:** not formalized. The authors re-derived Lemma 3.3, the switching argument of Section 3.3,
  Proposition 3.4, Theorem 4.1 with Lemmas 4.2-4.4, and Lemma 5.3 of [OAI-197a] step by step, and confirmed the
  model-specific constants by exact computation; no gap was found.
- **Sections 6 and 7:** (a) is proved directly. (b)-(d) are proved by rerunning the proofs of [OAI-196,
  Lemmas 2.2, 2.3, Prop. 3.1] and [OAI-197a, Section 3.3, Lemma 3.3, Prop. 3.4, Thm. 4.1] with the
  model-dependent counts replaced (pool sizes, turn counts, decay, colour data); the model-independent parts of
  those proofs are used as stated. Ivanov (arXiv:2610.17662, Lemmas 4.2, 4.4, Props. 5.3, 6.1)
  did the same for his own type design; the two-colour transfer was found first by Ivanov and independently by the
  authors.

[OAI-197b] is used only for Theorem D: Section 3.1 (the glued group N), Lemma 3.2, Sections 4.2, 4.5, 4.6
(H = N x <z>, the multiple HNN extension, G = L x F), Section 5 (incidence data of girth >= 12).

## Statements of the paper

| Statement | Depends on | Mechanical checks |
|---|---|---|
| Lemmas 2.1-2.3, remark on order p, base change | ring axioms; torsion-freeness; Connell's theorem | `bicyclic_algebra_check.py` |
| Lemma 2.4 | Gromov, Weiss, Elek-Szabo; [OAI-197b, Prop. 7.2] | - |
| Lemma 3.1, presentation (1) | spanning trees; [OAI-196, proof of Lemma 5.2] | - |
| Constants (2), (3) | - | `constants_check.py` |
| Lemma 3.5 (E_n has probability 1 - o(1)) | OAI inputs (a)-(d) | `constants_check.py` (arithmetic) |
| Lemma 3.6 (short closures) | (P1), (P2) | `closure_lemma_check.py`, `constants_check.py` |
| Lemma 3.7 (separation) | Lipton-Tarjan | - |
| Lemma 3.8, Appendix A (interval lemma, with break) | planarity | `interval_lemma_check.py` |
| Lemma 4.2 (pictures, area, pi_2) | van Kampen and picture duality; [OAI-196, Lemma 5.2] | - |
| Lemma 4.3 (minimal pictures are reduced) | contractibility of cones; additivity in pi_2 | - |
| Proposition 4.4 (key estimate) | (P1)-(P3); Lemmas 3.6-3.8, 4.3 | `constants_check.py` |
| Theorem B (criterion) | Lemmas 4.2, 4.3, Prop. 4.4; Hurewicz-Whitehead; Brown | - |
| Theorem A | Theorem B, Lemma 3.5; linear Dehn function implies hyperbolic | - |
| Proposition 5.1 (parity certificates) | handshake lemma | - |
| Corollary 5.2 (case p = 2) | Theorem B, Prop. 5.1, OAI-197a inputs, Lemmas 2.1, 2.2, 2.4 | - |
| Corollary 5.3 | Theorem B, Prop. 5.1, OAI-196 inputs, Lemmas 2.2, 2.3 | - |
| Corollary 5.4 (explicit constant) | Lean declarations above, Theorem B, Prop. 5.1 | `constants_check.py` |
| Lemma 6.1 (signed cancellation; Ivanov, Lemma 2.2) | involution on darts | `signed_cancellation_test.py` |
| Lemma 6.3 (design, p odd) | PG(2,q) incidences | `design_p3_explicit.py`, `pg281_kernel.py`, `pg2_81_kernel_r2.py` |
| Lemma 6.4 (squared-word decay) | Perron vector f = e + 2 on the partners of extras | `exact_rows_r2.py`, `decay_quotient.py`, `decay_constants_check.py`, the three PG(2,81) engines |
| Lemmas 6.5, 6.6, Prop. 6.7 | proofs of [OAI-196, Lemmas 2.2, 2.3, Prop. 3.1] rerun with the bipartite counts and colour data | `decay_constants_check.py` (girth-scale conditions (8)) |
| Corollary 6.8, Proposition 6.9 | Theorem B, Lemmas 6.1, 6.3, 2.2, 2.3 | - |
| Remark 6.10 (Ivanov's model) | Theorem B; Ivanov's estimates (arXiv:2610.17662, Lemmas 4.2, 4.4, Prop. 6.1) | - |
| Lemmas 7.2-7.5, Prop. 7.6 (types, lattice, z-certificate, involution, colour balance) | PG(2,p), PG(2,q) incidences; integer lattice | `certificates_odd_p.py`, `certificates_odd_p_extended.py` |
| Lemmas 7.7, 7.8 (turn counts, Perron certificate) | uniform family; inequality (15) | `certificates_odd_p.py`, `certificates_odd_p_extended.py` |
| Prop. 7.9 | proofs of [OAI-197a, Section 3.3, Lemma 3.3, Prop. 3.4, Thm. 4.1] rerun with the two-colour counts and colour data | - |
| Corollary 7.10, Prop. 7.11, Theorem C | Theorem B; identity (7) of Lemma 6.1 with B' = A'; Lemma 7.2; Lemmas 2.1, 2.2, 2.4; base change | `certificates_odd_p.py` (explicit constant for p = 3) |
| Corollary 7.13 | Elek-Szabo; Agol; Fisher-Sanchez-Peralta; Arzhantseva-Paunescu | - |
| Theorem 8.1, Corollary 8.2, Prop. 8.3 | linear algebra (weighted trace bound); Perron-Frobenius; weak Nullstellensatz | - |
| Theorem 9.1, Theorem D | link condition, developability, gluing (Bridson-Haefliger); [OAI-197b] | `cat0_links_check.py` |
