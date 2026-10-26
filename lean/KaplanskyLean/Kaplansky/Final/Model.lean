import Kaplansky.Final.Witness
import Kaplansky.Final.Relabel
import Kaplansky.Main.TheoremB
import Kaplansky.Random.PatternFree

/-!
# From a pattern-free sample of a random model to a counterexample

Let `M` be a random model (`Kaplansky.Random.Model`), `r` a sample at size `m` with roots
`x ∈ A`, `y ∈ B`, and `e : M.α → S₀ × Bool` a signing of the letters such that the sample
(relabelled by `e`) is pattern-free (Definition 3.3). Theorem B makes the cone group
`G = ConeGroup Γ (e ∘ label) (routes Γ)` finitely presented, torsion-free, word-hyperbolic, with a
finite two-dimensional `K(G,1)`, and protects the roots. The route values
`GraphPresentation.value` are path labels `g_x` with `g_{x·t} = g_x t` (`GraphPresentation.edge`).
With a sign `σ` on `A` reversing along edges and the type congruences, Prop. 7.11 /
Prop. 5.1 (`Final.exists_not_directlyFinite`) give `a, b ∈ 𝔽_p[G]` with `ab = 1 ≠ ba`.

Main result: `Final.model_counterexample`.
-/

namespace Kaplansky.Final

open OAI.TorsionFreeZeroDivisors
open PortSubdivision
open Kaplansky.Random Kaplansky.Random.SampleGraph Kaplansky.Random.ActualPatternEvent

section ModelWitness

variable {M : Model} {m : ℕ}

/-- The letters of the darts of `Γ_A` at `x` form the type `S_x`. -/
theorem labels_at_A (r : Match M m) (x : VA M m) :
    (Finset.univ.filter fun d : DA M m => (A M m r).origin d = x).image
      (fun d : DA M m => d.val.2.1) = M.SA.out m x := by
  ext t
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd' : d.val.1 = x := hd
    have h := (Side.mem_out' M.SA).mp d.property
    rw [← hd']
    exact h.1
  · intro ht
    exact ⟨⟨(x, (t, M.SA.col m x)), (Side.mem_out' M.SA).mpr ⟨ht, rfl⟩⟩, rfl, rfl⟩

/-- The letters of the darts of `Γ_B` at `y` form the type `S_y`. -/
theorem labels_at_B (r : Match M m) (y : VB M m) :
    (Finset.univ.filter fun d : DB M m => (B M m r).origin d = y).image
      (fun d : DB M m => d.val.2.1) = M.SB.out m y := by
  ext t
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd' : d.val.1 = y := hd
    have h := (Side.mem_out' M.SB).mp d.property
    rw [← hd']
    exact h.1
  · intro ht
    exact ⟨⟨(y, (t, M.SB.col m y)), (Side.mem_out' M.SB).mpr ⟨ht, rfl⟩⟩, rfl, rfl⟩

/-- **A pattern-free sample with the type congruences gives a counterexample** (Theorem B +
Prop. 7.11 / Prop. 5.1). -/
theorem model_counterexample {r : Match M m} {x : VA M m} {y : VB M m}
    {S₀ : Type} [DecidableEq S₀] [Finite S₀] (e : M.α → S₀ × Bool)
    {ε d lam : ℝ} {L : ℕ}
    (pf : Exclusion.PatternFree (graph M m r) (e ∘ label M m) WordPairing.inverseLetter
      (isRoot M m x y) ε d lam L)
    {p : ℕ} [Fact p.Prime] (σ : VA M m → ZMod p)
    (hσ : ∀ dd : DA M m,
      σ ((A M m r).origin ((A M m r).reverse dd)) = -σ ((A M m r).origin dd))
    (hσroot : σ x = 1)
    (hself : ∀ x₁ x₂, (x₁, x₂) ≠ (x, x) → (M.SA.out m x₁ ∩ M.SA.out m x₂).card ≡ 1 [MOD p])
    (hroot : (M.SA.out m x).card ≡ 2 [MOD p])
    (hcross : ∀ x₁ y₁, (M.SA.out m x₁ ∩ M.SB.out m y₁).card ≡ 1 [MOD p]) :
    ∃ (G : Type) (_ : Group G), Kaplansky.GoodHyperbolic G ∧
      ∃ a b : MonoidAlgebra (ZMod p) G, a * b = 1 ∧ b * a ≠ 1 := by
  classical
  -- the darts are nonempty (degrees are at least 7)
  have : Nonempty (DA M m ⊕ DB M m) := by
    have h := pf.degree (Sum.inl x)
    obtain ⟨dd, -⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) h)
    exact ⟨dd⟩
  obtain ⟨hgood, hprot⟩ := Main.theoremB pf
  set Γ := graph M m r with hΓ
  set R := GraphPresentation.routes Γ with hR
  refine ⟨Exclusion.ConeGroup Γ (e ∘ label M m) R, inferInstance, hgood, ?_⟩
  let letters := GraphPresentation.roseLabel (e ∘ label M m)
  let val : VA M m ⊕ VB M m → Exclusion.ConeGroup Γ (e ∘ label M m) R :=
    GraphPresentation.value Γ letters R
  let letter : M.α → Exclusion.ConeGroup Γ (e ∘ label M m) R :=
    fun t => PresentedGroup.mk _ (FreeGroup.mk [e t])
  have hedge : ∀ dd, val (Γ.origin (Γ.reverse dd)) = val (Γ.origin dd) * letter (label M m dd) :=
    fun dd => GraphPresentation.edge Γ letters R dd
  refine exists_not_directlyFinite (T := M.α)
    (A M m r).origin (A M m r).reverse (fun dd => dd.val.2.1)
    (B M m r).origin (B M m r).reverse (fun dd => dd.val.2.1) M.inv
    (A M m r).reverse_reverse (B M m r).reverse_reverse
    (fun dd => label_reverse M m r (Sum.inl dd)) (fun dd => label_reverse M m r (Sum.inr dd))
    M.inv_ne
    (fun d₁ d₂ ho hl => Sum.inl.inj (immersed M m r (Sum.inl d₁) (Sum.inl d₂)
      (congrArg Sum.inl ho) hl))
    (fun d₁ d₂ ho hl => Sum.inr.inj (immersed M m r (Sum.inr d₁) (Sum.inr d₂)
      (congrArg Sum.inr ho) hl))
    (M.SA.out m) (M.SB.out m) (labels_at_A r) (labels_at_B r)
    letter (fun x₁ => val (Sum.inl x₁)) (fun y₁ => val (Sum.inr y₁))
    (fun dd => hedge (Sum.inl dd)) (fun dd => hedge (Sum.inr dd))
    σ hσ x hσroot hself hroot hcross
    (fun y₁ => (ShortClosure.simpleGraph Γ).Reachable (Sum.inr y) (Sum.inr y₁)) y
    (SimpleGraph.Reachable.refl _)
    (fun dd h => h.trans (ShortClosure.dart_reachable Γ (Sum.inr dd))) ?_
  intro y₁ hreach heq
  by_contra hne
  obtain ⟨w⟩ := hreach
  apply hprot (z := Sum.inr y) (w := Sum.inr y₁) (Or.inr rfl)
    (fun h => hne (Sum.inr.inj h).symm) (GraphPresentation.Path.ofWalk w)
  rw [GraphPresentation.path_value]
  change (val (Sum.inr y))⁻¹ * val (Sum.inr y₁) = 1
  rw [heq, inv_mul_cancel]

end ModelWitness

end Kaplansky.Final
