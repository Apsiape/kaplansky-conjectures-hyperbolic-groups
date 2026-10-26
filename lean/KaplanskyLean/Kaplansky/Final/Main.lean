import Kaplansky.Final.Odd
import Kaplansky.Final.Two
import Kaplansky.Algebra.Consequences

/-!
# The Main Theorem and its consequences

`Kaplansky.Final.mainTheorem_proof : Kaplansky.MainTheorem` and
`Kaplansky.Final.mainTheoremConsequences_proof : Kaplansky.MainTheoremConsequences`, for the
statements of `Kaplansky/Challenge.lean` (verbatim).

* `p = 2`: `Final.two_counterexample` (OAI197a model, Theorem B, Prop. 5.1(b),(c));
* `p` odd: `Final.odd_counterexample` (Section 7 design, two-colour model, Theorem B,
  Prop. 7.11 with Lemma 7.2);
* consequences: `Algebra.mainTheoremConsequences_of_mainTheorem` (Lemmas 2.1, 2.2, base change).
-/

namespace Kaplansky.Final

/-- **Main Theorem** (paper, boxed statement). -/
theorem mainTheorem_proof : Kaplansky.MainTheorem := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    exact two_counterexample
  · exact odd_counterexample p hp h2

/-- **Main Theorem, consequences.** -/
theorem mainTheoremConsequences_proof : Kaplansky.MainTheoremConsequences :=
  Algebra.mainTheoremConsequences_of_mainTheorem mainTheorem_proof

end Kaplansky.Final
