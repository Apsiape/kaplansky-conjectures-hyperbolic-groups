import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A pairing lemma

If a function `r : X → R` has fibres on a finite set `S` that are symmetric under an
involution `φ` of `R`, and the fibres over the fixed points of `φ` have even size, then `S`
carries a fixed-point-free involution `σ` with `r ∘ σ = φ ∘ r`.

This is the combinatorial step in the proof of Lemma 7.5 (`lem:pairing`) of the paper:
"pair the remaining letters with residue `y ≠ h_q` with those with residue `1 - y`, and the
`2q` letters with residue `h_q` among themselves".
-/

namespace Kaplansky.OddDesign

open Finset

variable {X R : Type*} [DecidableEq X] [DecidableEq R]

omit [DecidableEq R] in
/-- Removing one element from a finset changes each filtered count by the indicator of that
element. -/
theorem card_filter_erase_add (S : Finset X) (a : X) (P : X → Prop) [DecidablePred P] :
    ((S.erase a).filter P).card + (if a ∈ S ∧ P a then 1 else 0) = (S.filter P).card := by
  rw [filter_erase]
  by_cases h : a ∈ S ∧ P a
  · rw [card_erase_of_mem (mem_filter.2 h)]
    simp only [h, and_self, ite_true]
    have : 0 < (S.filter P).card := card_pos.2 ⟨a, mem_filter.2 h⟩
    omega
  · simp only [h, ite_false]
    rw [erase_eq_of_notMem]
    · simp
    · simpa [mem_filter] using h

/-- **Pairing lemma.** Fibre-symmetric functions on finite sets admit fixed-point-free
involutions intertwining them with `φ`. -/
theorem exists_pairing (r : X → R) (φ : R → R) (hφ : Function.Involutive φ) :
    ∀ S : Finset X,
      (∀ y, (S.filter (fun x => r x = y)).card = (S.filter (fun x => r x = φ y)).card) →
      (∀ y, φ y = y → Even (S.filter (fun x => r x = y)).card) →
      ∃ σ : X → X, ∀ x ∈ S, σ x ∈ S ∧ σ x ≠ x ∧ σ (σ x) = x ∧ r (σ x) = φ (r x) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hcount heven
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨id, by simp⟩
    -- a partner for `x`
    have hpartner : ∃ x' ∈ S, x' ≠ x ∧ r x' = φ (r x) := by
      by_cases hfix : φ (r x) = r x
      · have he := heven (r x) hfix
        have hmem : x ∈ S.filter (fun z => r z = r x) := by simp [hx]
        have h1 : 0 < (S.filter (fun z => r z = r x)).card := card_pos.mpr ⟨x, hmem⟩
        have h2 : 1 < (S.filter (fun z => r z = r x)).card := by
          rcases he with ⟨k, hk⟩
          omega
        obtain ⟨x', hx', hne⟩ := exists_mem_ne h2 x
        rw [mem_filter] at hx'
        exact ⟨x', hx'.1, hne, hx'.2.trans hfix.symm⟩
      · have hc := hcount (r x)
        have hpos : 0 < (S.filter (fun z => r z = φ (r x))).card := by
          rw [← hc]
          exact card_pos.mpr ⟨x, by simp [hx]⟩
        obtain ⟨x', hx'⟩ := card_pos.mp hpos
        rw [mem_filter] at hx'
        refine ⟨x', hx'.1, ?_, hx'.2⟩
        rintro rfl
        exact hfix hx'.2.symm
    obtain ⟨x', hx'S, hne, hr⟩ := hpartner
    have hx'S' : x' ∈ S.erase x := mem_erase.2 ⟨hne, hx'S⟩
    -- the counting identity for the smaller set
    have hcnt : ∀ y, (((S.erase x).erase x').filter (fun z => r z = y)).card
        + (if r x' = y then 1 else 0) + (if r x = y then 1 else 0)
        = (S.filter (fun z => r z = y)).card := by
      intro y
      have h1 := card_filter_erase_add (S.erase x) x' (fun z => r z = y)
      have h2 := card_filter_erase_add S x (fun z => r z = y)
      simp only [hx'S', hx, true_and] at h1 h2
      omega
    have hsub : (S.erase x).erase x' ⊂ S :=
      (erase_ssubset hx'S').trans_le (erase_subset _ _)
    have hcount' : ∀ y, (((S.erase x).erase x').filter (fun z => r z = y)).card
        = (((S.erase x).erase x').filter (fun z => r z = φ y)).card := by
      intro y
      have a1 := hcnt y
      have a2 := hcnt (φ y)
      have a3 := hcount y
      have e1 : (r x' = φ y) ↔ (r x = y) := by
        rw [hr]; exact hφ.injective.eq_iff
      have e2 : (r x = φ y) ↔ (r x' = y) := by
        rw [hr]
        constructor
        · intro h; rw [h, hφ y]
        · intro h; rw [← h, hφ (r x)]
      simp only [e1, e2] at a2
      omega
    have heven' : ∀ y, φ y = y →
        Even (((S.erase x).erase x').filter (fun z => r z = y)).card := by
      intro y hy
      have a1 := hcnt y
      have a3 := heven y hy
      have e1 : (r x' = y) ↔ (r x = y) := by
        rw [hr]
        constructor
        · intro h; rw [← hφ (r x), h, hy]
        · intro h; rw [h, hy]
      simp only [e1] at a1
      rcases a3 with ⟨k, hk⟩
      split_ifs at a1
      · exact ⟨k - 1, by omega⟩
      · exact ⟨k, by omega⟩
    obtain ⟨σ, hσ⟩ := ih _ hsub hcount' heven'
    refine ⟨fun z => if z = x then x' else if z = x' then x else σ z, ?_⟩
    intro z hz
    by_cases hzx : z = x
    · subst hzx
      refine ⟨by simpa using hx'S, by simpa using hne, ?_, by simpa using hr⟩
      simp [hne]
    by_cases hzx' : z = x'
    · subst hzx'
      refine ⟨by simpa [hzx] using hx, by simpa [hzx] using Ne.symm hne, by simp [hzx], ?_⟩
      simp only [hzx, ite_false, ite_true]
      rw [hr, hφ]
    have hzS : z ∈ (S.erase x).erase x' := mem_erase.2 ⟨hzx', mem_erase.2 ⟨hzx, hz⟩⟩
    obtain ⟨h1, h2, h3, h4⟩ := hσ z hzS
    have hσx : σ z ≠ x := fun h => by
      rw [h] at h1; simp at h1
    have hσx' : σ z ≠ x' := fun h => by
      rw [h] at h1; simp at h1
    simp only [hzx, hzx', ite_false, hσx, hσx', h3]
    exact ⟨(mem_erase.1 (mem_erase.1 h1).2).2, h2, trivial, h4⟩

/-- The pairing lemma on a whole finite type, as an involutive permutation. -/
theorem exists_involution [Fintype X] (r : X → R) (φ : R → R) (hφ : Function.Involutive φ)
    (hcount : ∀ y, (univ.filter (fun x => r x = y)).card
      = (univ.filter (fun x => r x = φ y)).card)
    (heven : ∀ y, φ y = y → Even (univ.filter (fun x => r x = y)).card) :
    ∃ σ : X → X, Function.Involutive σ ∧ (∀ x, σ x ≠ x) ∧ ∀ x, r (σ x) = φ (r x) := by
  obtain ⟨σ, hσ⟩ := exists_pairing r φ hφ univ hcount heven
  exact ⟨σ, fun x => (hσ x (mem_univ x)).2.2.1, fun x => (hσ x (mem_univ x)).2.1,
    fun x => (hσ x (mem_univ x)).2.2.2⟩

end Kaplansky.OddDesign
