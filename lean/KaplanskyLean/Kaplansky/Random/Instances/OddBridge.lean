import Kaplansky.Random.Instances.TwoColourFinal
import Kaplansky.Random.Instances.OddModel

/-!
# The odd-`p` two-colour model is pattern-free (paper Prop 7.9, Cor 7.10)

For every odd prime `p`, the random model `Odd.model (data p hp)` of agent AC's design
(`Instances/OddModel.lean`) is pattern-free in the existence form: for all large size parameters
and every root `y ∈ B`, some girth-conditioned sample, rooted at the root `r ∈ A₊` of the design
and at `y`, is `(ε, d, λ)`-pattern-free (Definition 3.3) with the constants of the model.

The witness-level facts (congruences, colour classes, root) are in `Instances/OddModel.lean`.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter

noncomputable section

namespace Odd

open Kaplansky.OddDesign

/-- The odd-`p` model of Section 7 for an odd prime `p` (`q = p^5`, `GaloisField p 5`). -/
def oddModel (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : Model := model (data p hp)

/-- **Corollary 7.10 (existence form).**  For every odd prime `p`, for all large `m` and every
root `y` of side `B`, some girth-conditioned sample of the two-colour model, rooted at the root
`r ∈ A₊` of the design and at `y`, is pattern-free (Definition 3.3), with the constants
`ε, d, λ` of the model. -/
theorem exists_patternFree (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∀ᶠ m in atTop, ∀ y : (oddModel p hp).SB.V m,
      ∃ r ∈ ActualPatternEvent.samples (oddModel p hp) m,
        Exclusion.PatternFree (SampleGraph.graph (oddModel p hp) m r)
          (SampleGraph.label (oddModel p hp) m) (data p hp).inv
          (SampleGraph.isRoot (oddModel p hp) m
            (Sum.inl ((data p hp).root (m + (data p hp).m₀))) y)
          (oddModel p hp).ε (TypedDiameter.D₀ (oddModel p hp) : ℝ) (oddModel p hp).lam
          ((oddModel p hp).L m) := by
  filter_upwards [(oddModel p hp).exists_patternFree] with m h
  intro y
  exact h _ y

end Odd

end

end Kaplansky.Random
