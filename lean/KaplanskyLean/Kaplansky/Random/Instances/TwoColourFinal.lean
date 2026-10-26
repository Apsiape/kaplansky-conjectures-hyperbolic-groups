import Kaplansky.Random.PatternFree
import Kaplansky.Random.Instances.TwoColour

/-!
# The two-colour odd-`p` model is pattern-free (Theorem 3.4 (b)–(d), odd `p`)

For any `TwoColourData` (in particular the design of agent AC for an odd prime `p`, see
`Instances/OddModel.lean`), for all large size parameters and every choice of roots, some
girth-conditioned sample is pattern-free (Definition 3.3).  The side `A = A₊ ⊔ A₋` is a disjoint
union; its vertices are `Sum.inl x` (`x ∈ A₊`, colour `true`) and `Sum.inr x` (`x ∈ A₋`, colour
`false`); every edge of the `A`-graph joins `A₊` to `A₋` (`colour_flip`).
-/

namespace Kaplansky.Random.TwoColourData

open OAI.TorsionFreeZeroDivisors
open Filter

variable (X : TwoColourData)

/-- **Theorem 3.4 (b)–(d) for the two-colour model.** -/
theorem exists_patternFree :
    ∀ᶠ m in atTop, ∀ (x : X.model.SA.V m) (y : X.model.SB.V m),
      ∃ r ∈ ActualPatternEvent.samples X.model m,
        Exclusion.PatternFree (SampleGraph.graph X.model m r) (SampleGraph.label X.model m)
          X.inv (SampleGraph.isRoot X.model m x y)
          X.model.ε (TypedDiameter.D₀ X.model : ℝ) X.model.lam (X.model.L m) :=
  X.model.exists_patternFree

/-- Every edge of the `A`-graph of a sample reverses the colour (`A₊ ↔ A₋`). -/
theorem colour_flip (m : ℕ) (r : ActualPatternEvent.Match X.model m) (d : SampleGraph.DA X.model m) :
    X.model.SA.col m ((SampleGraph.A X.model m r).origin ((SampleGraph.A X.model m r).reverse d)) =
      !X.model.SA.col m ((SampleGraph.A X.model m r).origin d) :=
  SampleGraph.colourA_flip X.model m r d

end Kaplansky.Random.TwoColourData
