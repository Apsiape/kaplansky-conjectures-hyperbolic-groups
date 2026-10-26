import Kaplansky.Main.ModelBridge
import Kaplansky.Exclusion.FreeCone

/-!
# Milestone 1: paper Corollary 5.4 (`cor:lean`)

A finitely presented, torsion-free, word-hyperbolic group with a finite two-dimensional
classifying space whose group algebra over `𝔽₂` has zero divisors: OpenAI's Result-196 group
`ConcreteGroup.G rep r` for a suitable sample. Finite presentation, torsion-freeness, the
classifying space and the zero divisors are OpenAI's; hyperbolicity is
`Exclusion.wordHyperbolic_of_patternFree` (the free-outer-disk case of Proposition 4.4) applied
through `Main.patternFree`.
-/

namespace Kaplansky.Main

open OAI.TorsionFreeZeroDivisors
open SampleGraph GirthAsymptotics TypedGraphs ActualPatternEvent Filter

/-- A sample satisfying all of OpenAI's conditions at scale `L ≥ 3`, with both factors nonzero. -/
theorem exists_sample :
    ∃ (rep : ℕ) (r : Match rep) (x : VA rep) (y : VB rep),
      r ∈ samples rep ∧ 3 ≤ L (size rep) ∧ GraphSample.Diameters rep r ∧
      IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
        (PlanarParameters.K PathSystem.ε ClosedWords.D)
        (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y) ∧
      ConcreteFactors.alpha rep r x ≠ 0 ∧ ConcreteFactors.beta rep r y ≠ 0 ∧
      ConcreteFactors.alpha rep r x * ConcreteFactors.beta rep r y = 0 := by
  have he := exists_avoiding (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D)
    (PlanarParameters.sides PathSystem.ε ClosedWords.D)
    (PlanarParameters.K_pos _ _) (PlanarParameters.sides_pos _ _)
  have hL := (L_tendsto.comp size_tendsto).eventually (eventually_ge_atTop 3)
  obtain ⟨rep, hrep, hL, hpos⟩ := (he.and (hL.and (eventually_ge_atTop 1))).exists
  let : NeZero rep := ⟨by omega⟩
  let x : VA rep := Classical.choice inferInstance
  let y : VB rep := Classical.choice inferInstance
  obtain ⟨r, hr, hd, ha⟩ := hrep x y
  have hL2 : 2 ≤ L (size rep) := le_trans (by norm_num) hL
  obtain ⟨hx, hy⟩ := ConcreteFactors.both_nonzero r x y hL2 hd hr ha
  exact ⟨rep, r, x, y, hr, hL, hd, ha, hx, hy, ConcreteFactors.product_zero rep r x y⟩

/-- The group of the sample is word-hyperbolic. -/
theorem concrete_wordHyperbolic {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (hL : 3 ≤ L (size rep)) (hd : GraphSample.Diameters rep r) (hsample : r ∈ samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D)
      (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) :
    Kaplansky.WordHyperbolic (ConcreteGroup.G rep r) := by
  have h := Exclusion.wordHyperbolic_of_patternFree (ConcreteGroup.routes rep r)
    (patternFree hL hd hsample havoid)
  have hlab : GraphPresentation.roseLabel (ConcreteTorsion.signedLabels rep) =
      ConcreteGroup.labels rep :=
    funext fun d => ConcreteGroup.letter_signed d
  unfold Exclusion.ConeGroup at h
  rw [hlab] at h
  exact h

/-- **Milestone 1 (paper Corollary 5.4).** -/
theorem hyperbolicZeroDivisors_proof : Kaplansky.HyperbolicZeroDivisors := by
  obtain ⟨rep, r, x, y, hr, hL, hd, ha, hx, hy, hz⟩ := exists_sample
  have hL2 : 2 ≤ L (size rep) := le_trans (by norm_num) hL
  refine ⟨ConcreteGroup.G rep r, inferInstance, ⟨inferInstance, ?_, ?_, ?_⟩,
    ConcreteFactors.alpha rep r x, ConcreteFactors.beta rep r y, hx, hy, hz⟩
  · exact ConcreteTorsion.torsion_free rep r x y hL2 hd hr ha
  · exact concrete_wordHyperbolic hL hd hr ha
  · exact ConcreteModel.has_model rep r x y hL2 hd hr ha

end Kaplansky.Main
