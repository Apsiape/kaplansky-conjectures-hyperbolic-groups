import Kaplansky.Final.Model
import Kaplansky.Random.Instances.OddBridge

/-!
# The Main Theorem for odd `p` (paper Theorem C, §7)

For an odd prime `p`, the two-colour model of Section 7 (`Random.Odd.oddModel p = Random.Odd.model (data p)`,
built from `OddDesign.data p` through `Random.Odd.twoColour`) has, for large `m`, a pattern-free sample
rooted at the design root `r ∈ A₊` and any `y ∈ B` (`Random.Odd.exists_patternFree`,
Cor. 7.10). After signing the letters (`Final.patternFree_signed`), Theorem B and Prop. 7.11
apply:

* the sign is `σ = +1` on `A₊`, `-1` on `A₋`: every edge of `Γ_A` joins `A₊` to `A₋`
  (`SampleGraph.colourA_flip`);
* the congruences are Lemma 7.2 (`OddDesign.Data.cong`): `|S ∩ S'| ≡ 1 (mod p)` unless
  `S = S' = S_r`, `|S_r| ≡ 2`, and `S_r` is the type of the root only.

Main results: `Final.twoColour_counterexample` (any two-colour model whose types satisfy the
congruences of Lemma 7.2) and `Final.odd_counterexample`.
-/

namespace Kaplansky.Final

open OAI.TorsionFreeZeroDivisors
open Kaplansky.Random Kaplansky.Random.SampleGraph Kaplansky.Random.ActualPatternEvent
open Kaplansky.OddDesign Filter

/-- The sign of the two-colouring: `+1` on `A₊`, `-1` on `A₋`. -/
def twoSign {α β : Type} (p : ℕ) : α ⊕ β → ZMod p := Sum.elim (fun _ => 1) (fun _ => -1)

/-- The two-colouring of a two-colour model is proper: every edge of `Γ_A` changes the sign. -/
theorem twoSign_flip (X : TwoColourData) {p : ℕ} {m : ℕ} (r : Match X.model m)
    (dd : DA X.model m) :
    twoSign (α := X.VAp (m + X.m₀)) (β := X.VAm (m + X.m₀)) p
        ((A X.model m r).origin ((A X.model m r).reverse dd)) =
      -twoSign (α := X.VAp (m + X.m₀)) (β := X.VAm (m + X.m₀)) p
        ((A X.model m r).origin dd) := by
  have key : ∀ v w : X.VAp (m + X.m₀) ⊕ X.VAm (m + X.m₀),
      Sum.elim (fun _ => true) (fun _ => false) w = !(Sum.elim (fun _ => true) (fun _ => false) v) →
        twoSign p w = -twoSign p v := by
    rintro (v | v) (w | w) h <;> simp [twoSign] at h ⊢
  exact key _ _ (colourA_flip X.model m r dd)

/-- **A two-colour model with the type congruences of Lemma 7.2 gives a counterexample.** -/
theorem twoColour_counterexample (X : TwoColourData) {p : ℕ} [Fact p.Prime] {m : ℕ}
    {r : Match X.model m} {x₀ : X.VAp (m + X.m₀)} {y : X.VB (m + X.m₀)}
    {S₀ : Type} [DecidableEq S₀] [Finite S₀] (e : X.α → S₀ × Bool) {ε d lam : ℝ} {L : ℕ}
    (pf : Exclusion.PatternFree (graph X.model m r) (e ∘ label X.model m)
      WordPairing.inverseLetter (isRoot X.model m (Sum.inl x₀) y) ε d lam L)
    (types : Finset (Finset X.α)) (rootSet : Finset X.α)
    (hcong : ∀ S ∈ types, ∀ S' ∈ types,
      (S ∩ S').card % p = if S = rootSet ∧ S' = rootSet then 2 % p else 1)
    (hAp : ∀ a, X.outAp (m + X.m₀) a ∈ types) (hAm : ∀ a, X.outAm (m + X.m₀) a ∈ types)
    (hB : ∀ b, X.outB (m + X.m₀) b ∈ types)
    (hroot : X.outAp (m + X.m₀) x₀ = rootSet)
    (huniq : ∀ a, X.outAp (m + X.m₀) a = rootSet → a = x₀)
    (hAm_ne : ∀ a, X.outAm (m + X.m₀) a ≠ rootSet) (hB_ne : ∀ b, X.outB (m + X.m₀) b ≠ rootSet)
    (hp : 1 < p) :
    ∃ (G : Type) (_ : Group G), Kaplansky.GoodHyperbolic G ∧
      ∃ a b : MonoidAlgebra (ZMod p) G, a * b = 1 ∧ b * a ≠ 1 := by
  classical
  -- the types of the vertices of `A`
  have houtA : ∀ v : X.VAp (m + X.m₀) ⊕ X.VAm (m + X.m₀),
      Sum.elim (X.outAp (m + X.m₀)) (X.outAm (m + X.m₀)) v ∈ types ∧
        (Sum.elim (X.outAp (m + X.m₀)) (X.outAm (m + X.m₀)) v = rootSet → v = Sum.inl x₀) := by
    rintro (a | a)
    · exact ⟨hAp a, fun h => congrArg Sum.inl (huniq a h)⟩
    · exact ⟨hAm a, fun h => absurd h (hAm_ne a)⟩
  have hone : ∀ {S S' : Finset X.α}, S ∈ types → S' ∈ types → ¬(S = rootSet ∧ S' = rootSet) →
      (S ∩ S').card ≡ 1 [MOD p] := by
    intro S S' hS hS' h
    have hc := hcong S hS S' hS'
    rw [ite_eq_right h] at hc
    unfold Nat.ModEq
    rw [hc, Nat.mod_eq_of_lt hp]
  have hrootc : rootSet.card ≡ 2 [MOD p] := by
    have hc := hcong rootSet (hroot ▸ hAp x₀) rootSet (hroot ▸ hAp x₀)
    rw [ite_eq_left ⟨rfl, rfl⟩, Finset.inter_self] at hc
    exact hc
  exact model_counterexample (M := X.model) (x := Sum.inl x₀) e pf (twoSign p)
    (twoSign_flip X r) (by simp [twoSign])
    (fun x₁ x₂ hx => hone (houtA x₁).1 (houtA x₂).1 (fun h =>
      hx (Prod.ext ((houtA x₁).2 h.1) ((houtA x₂).2 h.2))))
    (by
      show (X.outAp (m + X.m₀) x₀).card ≡ 2 [MOD p]
      rw [hroot]
      exact hrootc)
    (fun x₁ y₁ => hone (houtA x₁).1 (hB y₁) (fun h => hB_ne y₁ h.2))

/-- **Main Theorem, odd `p`** (paper Theorem C). -/
theorem odd_counterexample (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ (G : Type) (_ : Group G), Kaplansky.GoodHyperbolic G ∧
      ∃ a b : MonoidAlgebra (ZMod p) G, a * b = 1 ∧ b * a ≠ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ p := three_le_of_prime hp h2
  obtain ⟨m, hm, hm1⟩ := ((Odd.exists_patternFree p h2).and (eventually_ge_atTop 1)).exists
  let D := data p h2
  -- the side `B` is nonempty
  have hcardB : 0 < Fintype.card (D.VB (m + D.m₀)) := by
    rw [D.card_VB]
    have hv : 0 < v p := v_pos p
    have : 0 < m + D.m₀ := by omega
    positivity
  obtain ⟨y⟩ := Fintype.card_pos_iff.mp hcardB
  obtain ⟨r, -, pf⟩ := hm y
  have hinv : Function.Involutive D.inv := pf.inv_involutive
  have hfin : Finite (Orbit D.inv hinv) := inferInstance
  exact twoColour_counterexample (Odd.twoColour D)
    (S₀ := Orbit D.inv hinv) (signing D.inv hinv) (patternFree_signed pf) D.types D.rootSet D.cong
    (D.outAp_mem (m + D.m₀)) (D.outAm_mem (m + D.m₀)) (D.outB_mem (m + D.m₀))
    (D.out_root (m + D.m₀)) (D.root_unique (m + D.m₀)) (D.outAm_ne_root (m + D.m₀))
    (D.outB_ne_root (m + D.m₀)) (by omega)

end Kaplansky.Final
