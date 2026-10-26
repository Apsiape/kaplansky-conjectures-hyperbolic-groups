# KaplanskyLean

A Lean 4 formalization, by Nidhal Mghirbi, of the Main Theorem of the paper *Kaplansky's conjectures fail for
torsion-free hyperbolic groups in positive characteristic* (Nidhal Mghirbi and Seth Douglas). It is reference [Mgh26]
of the paper. Appendix C of the paper maps each statement to its Lean declarations and lists what is not formalized.

## What is proved

The statements are in one file, `Kaplansky/Challenge.lean`. It is the only file that contains `sorry`, by design: it
states the theorems, and the rest of the development proves them.
- **Its definitions are copied verbatim** from OpenAI's public Comparator challenges (openai/math, commit `1581d4c`).
  These are torsion-freeness, a finite two-dimensional classifying space and word-hyperbolicity, specialised to `Type`.
- **`Kaplansky.Final.mainTheorem_proof : Kaplansky.MainTheorem`.** For every prime p there are a finitely presented,
  torsion-free, word-hyperbolic group G with a finite two-dimensional classifying space and a, b in F_p[G] with
  ab = 1 ≠ ba.
- **`Kaplansky.Final.mainTheoremConsequences_proof : Kaplansky.MainTheoremConsequences`.** For the same groups, over
  every field K of characteristic p, K[G] is not directly finite, and it contains a nontrivial idempotent, a zero
  divisor, and a unit of order p that is not of the form λg.
- **`Kaplansky.Main.hyperbolicZeroDivisors_proof : Kaplansky.HyperbolicZeroDivisors`.** The characteristic-two
  zero-divisor corollary (Corollary 5.4 of the paper) as a single example: one finitely presented, torsion-free,
  word-hyperbolic group with a finite two-dimensional classifying space and nonzero α, β in F_2[G] with αβ = 0.
  It does not state the corollary for all large sizes, the unit, or the area constant.

`Audit.lean` checks that each proof has exactly the type of its statement in the challenge file, and prints the axioms.
The build record of 25 October 2026 reports `lake build Kaplansky.Final.Main` succeeding. It also reports
`#print axioms` = `[propext, Classical.choice, Quot.sound]` for both main proofs, and for the auxiliary results checked
there.

The remaining point of trust is that the definitions in `Kaplansky/Challenge.lean` mean what the paper means.

## Building

The toolchain is pinned in `lean-toolchain` (Lean v4.34.1) and Mathlib in `lakefile.lean` (commit `d13f23b`).
With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get
lake build
lake env lean Audit.lean
```

## Contents and licences

- `Kaplansky/` and `Audit.lean`: Nidhal Mghirbi's development. Copyright 2026 Nidhal Mghirbi. Licensed under the
  Apache License 2.0 (`LICENSE`).
- `OAI/`: Lean modules vendored from OpenAI's repository https://github.com/openai/math (commit
  `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, directory `lean/`). They are redistributed under OpenAI's Apache
  License 2.0 (`OAI/LICENSE-APACHE-2.0-OpenAI`). No line is changed except import lines and a per-file modification notice, and `GraphMetric.lean` is
  an excerpt of OpenAI's `CayleyMetric.lean`, as recorded in `OAI/VENDOR.md`.
