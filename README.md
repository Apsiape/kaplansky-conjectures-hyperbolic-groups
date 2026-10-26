# Kaplansky's conjectures fail for torsion-free hyperbolic groups in positive characteristic

Nidhal Mghirbi and Seth Douglas

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23374263.svg)](https://doi.org/10.5281/zenodo.23374263)

Version 1.0.2 (26 October 2026; [doi:10.5281/zenodo.23673698](https://doi.org/10.5281/zenodo.23673698)) reports Nidhal Mghirbi's Lean 4 formalization of the Main Theorem, whose source
is included in this repository, corrects a sentence of the introduction (Agol's theorem gives the zero-divisor
conjecture for cubulated *hyperbolic* groups, not for all cubulated groups), cites work posted since version 1.0.0
and updates the references; no mathematical statement changes. Version 1.0.1 ([doi:10.5281/zenodo.23374592](https://doi.org/10.5281/zenodo.23374592))
corrected the author order (Nidhal Mghirbi, Seth Douglas) of version 1.0.0
([doi:10.5281/zenodo.23374264](https://doi.org/10.5281/zenodo.23374264)). All versions:
[doi:10.5281/zenodo.23374263](https://doi.org/10.5281/zenodo.23374263).

## Summary

*A short summary for this page. The abstract is the one in the paper; the Zenodo record carries the same text.*

Do Kaplansky's group-ring conjectures hold for torsion-free word-hyperbolic groups? In positive characteristic,
no. For every prime p there is a finitely presented, torsion-free, word-hyperbolic group G with a finite
two-dimensional classifying space and a, b in F_p[G] with ab = 1 but ba != 1. So over every field of
characteristic p the group algebra of G is not directly finite, and it has a non-trivial idempotent, a zero
divisor and a non-trivial unit. For every prime p, a single group fails all four. This statement, for every
prime p and over every field of characteristic p, is formalized in Lean 4, including existence forms of the
random-graph estimates it uses (see below).

| Conjecture, for torsion-free hyperbolic groups | characteristic 0 | characteristic 2 | odd characteristic |
|---|---|---|---|
| units | open | fails | fails |
| zero divisors | open | fails | fails |
| idempotents | holds | fails | fails |
| direct finiteness | holds | fails | fails |

## What the paper proves

- **Characteristic 2 (Corollary 5.2).** OpenAI's torsion-free group whose group algebra over F_2 is not directly
  finite is word-hyperbolic for every outcome of its random choices in an event of probability 1 - o(1). The
  group and the elements are OpenAI's, and OpenAI note that the group is not sofic; hyperbolicity is new. One
  group fails all four conjectures; it is neither sofic nor surjunctive.
- **Theorem A.** OpenAI's zero-divisor and direct-finiteness groups are word-hyperbolic with probability
  1 - o(1), with an explicit linear isoperimetric inequality.
- **Theorem B (deterministic criterion).** If a labelled graph is *pattern-free*, the group obtained by coning
  off its components is aspherical, protects its roots and has a linear isoperimetric inequality. Asphericity
  and root protection are OpenAI's argument, run for a fixed graph; the isoperimetric inequality is new.
- **Theorem C (direct finiteness, odd p).** For every odd p, a torsion-free hyperbolic group H_p with F_p[H_p]
  not directly finite. As far as we know, these are the first torsion-free counterexamples to direct
  finiteness and to the idempotent conjecture in odd characteristic. The construction signs OpenAI's
  direct-finiteness certificate, with one exception at a root, and needs an exact solution of a colour-balance
  problem and a rational Perron certificate. On 15 October 2026, the day after version 1.0.0, Bunina, Lee,
  Miasnikov and Muliarchyk (arXiv:2610.22536) independently gave, for every odd p, a finitely presented group
  whose group algebra over F_p is not directly finite; torsion-freeness and hyperbolicity are not claimed there.
- **Zero divisors, odd p (Proposition 6.9).** Torsion-free zero divisors in odd characteristic were found first
  by S. V. Ivanov (arXiv:2610.17662) and independently by the authors, by the same signed mechanism; Ivanov has
  precedence. For hyperbolic groups they are subsumed by Theorem C; Proposition 6.9 adds that groups built with
  the signed zero-divisor mechanism are hyperbolic, and Remark 6.10 that Theorem B applies to Ivanov's own
  model, given his estimates.
- **Characteristic zero (Section 8).** The decay estimate that makes the groups torsion-free forces the type
  incidence matrices to have large real rank, which rules out every cancellation built into the vertex types.
  This settles, in the negative, Ivanov's remark that he knew no design combining exact constancy with that
  estimate (his Section 8.2).
- **Theorem D.** OpenAI's characteristic-two counterexample with torsion is a CAT(0) group.

## The Lean formalization

Nidhal Mghirbi has formalized the Main Theorem in Lean 4 (Lean v4.34.1, Mathlib `d13f23b`; reference [Mgh26] of
the paper). The development is in [`lean/KaplanskyLean/`](lean/KaplanskyLean/), with build instructions in its
README; the release of version 1.0.2 archives it on Zenodo with the paper
([doi:10.5281/zenodo.23374263](https://doi.org/10.5281/zenodo.23374263), all versions). The statements are in one
file, [`Kaplansky/Challenge.lean`](lean/KaplanskyLean/Kaplansky/Challenge.lean), whose definitions of
torsion-freeness, of a finite two-dimensional classifying space and of word-hyperbolicity are copied verbatim from
OpenAI's public Comparator challenges. In
[`Kaplansky/Final/Main.lean`](lean/KaplanskyLean/Kaplansky/Final/Main.lean), `Kaplansky.Final.mainTheorem_proof`
proves, for every prime p, the existence of G, a and b, and `Kaplansky.Final.mainTheoremConsequences_proof` proves
the failure of all four conjectures over every field of characteristic p; [`Audit.lean`](lean/KaplanskyLean/Audit.lean)
checks their types and prints their axioms. The build record (25 October 2026) reports
`lake build Kaplansky.Final.Main` succeeding and `#print axioms` = [propext, Classical.choice, Quot.sound] for both.
The development includes OpenAI's Lean modules for their zero-divisor result and parts of two other OpenAI
developments (the non-residually-finite hyperbolic group, and odd-characteristic direct finiteness). They retain the
upstream source except for the import adaptations and the excerpt of `CayleyMetric.lean` as `GraphMetric.lean`, each
modified file carrying a notice, as documented in `lean/KaplanskyLean/OAI/VENDOR.md`; they are redistributed under
OpenAI's Apache License 2.0. Corollary 5.4 is formalized as a single example (one
outcome at one size), without the unit and the area constant. Not formalized: the probability statement of
Theorem A, non-soficity and non-surjunctivity, the explicit area constants, Section 6 apart from Lemma 6.1,
Corollary 7.13, Section 8 and Theorem D. Appendix C of the paper and `DEPENDENCIES.md` list what is formalized.
The remaining point of trust is that the definitions in the statement file mean what the paper means. Nidhal
Mghirbi's files are under the Apache License 2.0, and the vendored OpenAI modules under OpenAI's Apache License 2.0.

## What rests on OpenAI's preprints

The probabilistic inputs are four statements about random graphs (types, girth, diameter, bounded-pattern
estimate; Theorem 3.4 and Table 2 of the paper). In the existence form used by the Main Theorem they are formalized
for both models it uses (OpenAI's direct-finiteness model and the model of Section 7), so the Main Theorem does not
rest on any unformalized OpenAI text. In the probabilistic form used by Theorem A: for OpenAI's zero-divisor model
they are formalized by OpenAI in the existence form used in Corollary 5.4, and checked line by line by Ivanov; for
OpenAI's direct-finiteness model the authors have checked OpenAI's proofs independently. For the paper's two
odd-characteristic models they are proved in Sections 6 and 7 by rerunning OpenAI's proofs with the model-dependent
counts replaced, as Ivanov did for his two-colour model. Everything else is proved in the paper or classical.
`DEPENDENCIES.md` maps every statement to its inputs.

## Contents

| Path | Contents |
|---|---|
| `paper/main.tex`, `paper/main.pdf` | the paper |
| `paper/build.py` | build script |
| `verify/` | the verification scripts, their recorded outputs (`*.out`) and `run_all.sh` |
| `lean/KaplanskyLean/` | Nidhal Mghirbi's Lean 4 formalization of the Main Theorem |
| `tools/check_abstract.py` | checks that the paper and the Zenodo metadata carry the same abstract |
| `DEPENDENCIES.md` | statement-by-statement dependency map |
| `SOURCES.md` | the external sources read, with hashes |

## Building the paper

With `pdflatex` (packages mathpazo, tcolorbox, tikz, cleveref, aliascnt, xurl, array and placeins), run

```
python paper/build.py
```

It runs three passes and stops if a reference is undefined, a label is duplicated or a box is overfull.
`python tools/check_abstract.py` compares the abstract of the paper with the description in `.zenodo.json`.

## The verification package

Run `sh verify/run_all.sh` (Python 3 with numpy, scipy, sympy, mpmath and networkx; set `PYTHON` to choose the
interpreter). It reruns every script and overwrites its recorded output, so `git diff verify/` shows any change.
The scripts check finite arithmetic and sample instances; they do not replace the proofs.

| Script | What it checks | Paper |
|---|---|---|
| `bicyclic_algebra_check.py` | every identity of Lemma 2.1 in the bicyclic monoid ring over Z and F_2 (universal for ab = 1); the computations behind Lemmas 2.2 and 2.3 | Section 2 |
| `constants_check.py` | the inequalities (3) for the constants (2); the bookkeeping of Proposition 4.4; the arithmetic of Lemmas 3.5 and 3.6; the constant of Corollary 5.4 | Sections 3-5 |
| `closure_lemma_check.py` | the closure construction of Lemma 3.6 on random immersed paths in random 5- and 6-regular graphs | Lemma 3.6 |
| `interval_lemma_check.py` | the interval lemma on random planar pictures, with and without a break | Lemma 3.8, Appendix A |
| `cat0_links_check.py` | the vertex links of Theorem 9.1 for l = 3, 5, 7, their girths and angle sums | Section 9 |
| `design_p3_explicit.py` | F_81, PG(2,81) and the exact type tables of Definition 6.2 for p = 3; letter frequencies, cross-intersections {1,4,82,85}, domination of the A-side turn frequencies; spectral radius of the full 6648 x 6648 matrix M | Lemmas 6.3, 6.4 |
| `pg281_kernel.py`, `pg2_81_kernel_r2.py` | two further, independently written constructions of PG(2,81) and the turn kernel for p = 3 | Lemma 6.4 |
| `decay_quotient.py` | the exact 3 x 3 equitable quotient of M, with OpenAI's design as a control; spectral radii for p = 3, 5, 7, 11, 13 | Lemma 6.4 |
| `decay_constants_check.py` | an alternative analytic Perron certificate for M, exactly, for odd p <= 23; the girth-scale conditions (8) for p = 3 | Section 6 |
| `exact_rows_r2.py` | the exact rational row bounds in the proof of Lemma 6.4 | Lemma 6.4 |
| `signed_cancellation_test.py` | random bipartite models for p = 3, 5, 7: every component of the simultaneous-step graph has signed count divisible by p; non-bipartite control fails | Lemma 6.1 |
| `certificates_odd_p.py` | for p = 3, 5, 7, 11, 13 and q = p^5, exactly: the certificate of Lemma 7.4, the block counts, positivity of the uniform family, the Perron row bounds of Lemma 7.8; the explicit constant for p = 3 | Section 7 |
| `certificates_odd_p_extended.py` | Lemma 7.4 and the block counts for odd p <= 43; the residue bookkeeping of Lemma 7.5 at q = p^5 for odd p <= 199; the inequalities of Lemma 7.8, the smallest turn weight and the congruences of Lemma 7.2 for odd p <= 199 | Section 7 |

## Credits

The cone-on-graphs construction, the random models and their estimates, the parity certificates, the vertex
types built from projective planes and extra letters, and the groups of Corollaries 5.2-5.4 and Theorems A and D
are OpenAI's ("A Torsion-Free Group Algebra with Zero Divisors", 23 September 2026; "A Torsion-Free Group Algebra
That Is Not Directly Finite", 4 October 2026; "A Counterexample to Kaplansky's Direct-Finiteness Conjecture in
Characteristic Two", 23 September 2026; all in [openai/math](https://github.com/openai/math)). So are the
accounting that turns a bounded counting estimate into a linear isoperimetric inequality, used by OpenAI for a
different random complex ("A hyperbolic group with no geometric CAT(0) action"), and the developability route
through the link computation behind Theorem D, recorded in OpenAI's reasoning trace. The signed cancellation,
the two-colour model and the transfer of OpenAI's estimates to that model, with the colour data in the pattern
count, were found first by S. V. Ivanov (arXiv:2610.17662) and independently by the authors; Ivanov has
precedence, and his decay estimate for his own design uses an explicit test vector. The sign rule appears
earlier as Mineyev's signature condition. The Lean formalization of the Main Theorem is Nidhal Mghirbi's; it
builds on OpenAI's Lean development. Section 11 of the paper gives a sentence-level account, including how the
work was done.

## License

The paper and documentation are licensed CC BY 4.0, and the scripts MIT or Apache 2.0, at your option; see
[RIGHTS.md](RIGHTS.md) and [NOTICE](NOTICE). To cite this work, see [CITATION.cff](CITATION.cff).
