# Dependency map

"OAI" means an input from OpenAI's unrefereed, AI-generated preprints, taken as stated and not re-proved in the
paper. Everything else is proved in the paper or is classical. Numbers refer to `paper/main.pdf`.

## The four inputs (Theorem 3.4, Table 2)

| Input | [OAI-196] | [OAI-197a] | OpenAI's Lean, model of [OAI-196] (commit adc7f12; unchanged at 1581d4c) | odd p, zero divisors (Section 6) | odd p, direct finiteness (Section 7) | Lean [Mgh26], models of [OAI-197a] and Section 7 |
|---|---|---|---|---|---|---|
| (a) types: degrees; parity or congruence of the intersections | Section 2.1, (2.1) | Section 3.1, Prop. 3.1 | `degreeA_bounds`, `degreeB_bounds`, `odd_cross_intersections` (PatternCount.lean) | Lemma 6.3 | Lemma 7.2 | `Random.OAI197a.degree_bounds`, `parity_AA`, `parity_root`, `parity_AB`; `OddDesign.cong_allTypes` |
| (b) a matching with girth >= L exists | Lemma 2.2 | Section 3.3 | `TypedGraphs.eventual_nonempty` (TypedGraphs.lean) | Lemma 6.5 | Prop. 7.9(a) | in `exists_patternFree` below |
| (c) component diameter <= dL with probability 1 - o(1) | Lemma 2.3 | Prop. 3.4 | `diameterA_tendsto`, `diameterB_tendsto` (TypedDiameter.lean) | Lemma 6.6 | Prop. 7.9(b) | in `exists_patternFree` below |
| (d) bounded-pattern estimate | Prop. 3.1 | Thm. 4.1 | `SampleGraph.exists_avoiding` (BoundedSystem.lean): existence form, (b)-(c) included, eps = 1/2467200, `I` counts interval sides | Prop. 6.7 | Prop. 7.9(c) | `Random.OAI197a.exists_patternFree`, `Random.Odd.exists_patternFree`: existence form, (b)-(c) included |

Status of the inputs:
- **[OAI-196] model:** formalized in OpenAI's Lean development, in the existence form used in Corollary 5.4. These
  modules are included, unchanged except for import lines, in the Lean formalization [Mgh26] and built with it.
- **[OAI-197a] model:** formalized in [Mgh26], (a) as stated and (b)-(d) in existence form, for the model of
  [OAI-197a, Section 3.1] with one of the type assignments allowed there, along the admissible sizes
  n = v(4v(m+1)+1). The probabilistic form used in Theorem A is not formalized; for it, the authors re-derived
  Lemma 3.3, the switching argument of Section 3.3, Proposition 3.4, Theorem 4.1 with Lemmas 4.2-4.4, and
  Lemma 5.3 of [OAI-197a] step by step, and confirmed the model-specific constants by exact computation; no gap
  was found.
- **Section 7 model:** formalized in [Mgh26], (a) as stated and (b)-(d) in existence form.
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

## The Lean formalization [Mgh26]

Nidhal Mghirbi's Lean 4 development (Lean v4.34.1, Mathlib `d13f23b`). Statements in `Kaplansky/Challenge.lean`
(definitions of torsion-freeness, finite two-dimensional classifying space and word-hyperbolicity copied verbatim
from OpenAI's Comparator challenges `TorsionFreeZeroDivisors.lean` and `TorsionFreeHyperbolic.lean`, specialised
to `Type`). Build record of 25 October 2026: `lake build Kaplansky.Final.Main` succeeds; `#print axioms` =
[propext, Classical.choice, Quot.sound] for the main theorems; no `sorry` outside the statement file. Vendored
OpenAI modules (Apache-2.0): the import closure of `OAI.Algebra.GroupRing.Main`, four files of
`OAI.GroupTheory.Hyperbolic` (one of them lines 1-39 of `CayleyMetric.lean`) and `OAI.Algebra.OddKaplansky.Cellular`
(not used), with no line changed except import lines (checked against openai/math commit adc7f12;
OpenAI's files used are unchanged at 1581d4c). Names below are relative to the namespace `Kaplansky`.

| Paper | Lean declarations | Form |
|---|---|---|
| Main Theorem | `Final.mainTheorem_proof`, `Final.mainTheoremConsequences_proof` | as stated |
| Lemmas 2.1, 2.2, order p, base change | `Algebra.onesided`, `Algebra.one_add_ne_single`, `Algebra.orderOf_unitOfSqZero`, `Algebra.baseChange_injective` | as stated |
| Lemma 2.3 | `Algebra.sqZero_of_zeroDivisor_of_prime` | primeness of K[G] (Connell) assumed |
| Definition 3.3 | `Exclusion.PatternFree` | degree >= 7 in (P1) |
| Lemmas 3.6-3.8, Appendix A | OpenAI's formal versions in `OAI.Algebra.GroupRing` | closure lemma for degree >= 7 |
| Proposition 4.4 | `Exclusion.MapSystem.key_estimate`, `Exclusion.Capped.cone_bound` | as stated |
| Theorem B | `Main.theoremB`, `Main.theoremB_coneLength` | area bound as a cone-length bound; degree >= 7 |
| Proposition 5.1 | `Parity.parity_product_zero`, `Parity.parity_mul_star_eq_one`, `Parity.parity_star_mul_ne_one` | as stated |
| Corollary 5.2 | `Final.two_counterexample` | some b in place of a*; not "neither sofic nor surjunctive" |
| Corollary 5.4 | `Main.hyperbolicZeroDivisors_proof` | a single example (one outcome at one size, not for all large n); without the unit and the explicit constant |
| Lemma 6.1 | `Parity.signed_handshake`, `Parity.signed_product_zero`, `Parity.sum_single_ne_zero` | as stated |
| Definition 7.1, Lemma 7.2 | `OddDesign.cong_types`, `OddDesign.cong_root_type`, `OddDesign.rootSet_card_mod`, `OddDesign.cong_allTypes` | as stated |
| Lemma 7.3 | `OddDesign.lattice_a`, `lattice_b`, `lattice_c_q`, `lattice_c_ord` | as stated |
| Lemma 7.4 | `OddDesign.dvd_lineSum`, `sum_z`, `zVec_eq_sum`, `card_z_eq_of_mem`, `zz_zpair` | as stated |
| Lemma 7.5 | `OddDesign.exists_bar` | as stated |
| Proposition 7.6 | `OddDesign.inLL_rootVec`, `OddDesign.balance`, `OddDesign.balance_card` | as stated |
| Lemma 7.7 | `OddDesign.pairU_real`, `OddDesign.pair_Ap`, `pair_Am`, `pair_B` | as stated |
| Lemma 7.8 | `OddDesign.perron_certificate`, `OddDesign.squared_word_bound`, `OddDesign.decay_paper` | as stated |
| Proposition 7.9, Corollary 7.10 | `Random.Odd.exists_patternFree` | existence form, with a smaller explicit eps and scale L (delta = 1/(8(q+1)), a_0 = 2(q+1)) |
| Proposition 7.11 | `Parity.oddWitness`, `Final.exists_not_directlyFinite` | the second sums over all of A |
| Theorem C | `Final.odd_counterexample` | without c; not "neither sofic nor surjunctive" |
| Inputs (a)-(d) for [OAI-197a] | `Random.OAI197a.degree_bounds`, `parity_AA`, `parity_root`, `parity_AB`, `decays`, `exists_patternFree` | (b)-(d) in existence form |

Not formalized: the probability statement of Theorem A; Lemma 2.4 (soficity, surjunctivity); Connell's theorem
(Lemma 2.3), used for the units of Corollaries 5.3, 5.4 and Proposition 6.9; Lemma 4.2(a) and the explicit
constants of Theorem A and Corollary 5.4, and the quantifier over all large n in Corollary 5.4; Section 6 apart
from Lemma 6.1; Corollary 7.13 and Remark 7.14; Section 8; Theorem 9.1 and Theorem D. The units of the Main
Theorem come from Lemmas 2.1 and 2.2 and are formalized.
