import Kaplansky.Exclusion.Capped
import Kaplansky.Exclusion.Sphere

/-!
# The free outer disk (paper Proposition 4.4, free case; RECON gap G1b)

A reduced capped picture for a cyclically reduced word `u` in a pattern-free graph has at most
`16/(13ε)·|u|` occurrences on its cone disks.
-/

namespace Kaplansky.Exclusion

open OAI.TorsionFreeZeroDivisors
open PortSubdivision PermutationCycles

section
variable {S₀ : Type}

/-- In a cyclically reduced word, a letter is never followed (cyclically) by its inverse. -/
lemma cyclic_next_ne {u : List (S₀ × Bool)} (hu : FreeGroup.IsCyclicallyReduced u)
    (i : Fin u.length) :
    u.get (finRotate u.length i) ≠ WordPairing.inverseLetter (u.get i) := by
  intro h
  have hn : 0 < u.length := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  by_cases hi : i.val + 1 < u.length
  · have hrot := finRotate_val_succ i hi
    have hc := (List.isChain_iff_getElem.mp hu.1) i.val hi
    have he : u[i.val + 1] = WordPairing.inverseLetter u[i.val] := by
      have := h
      simp only [List.get_eq_getElem, hrot] at this
      exact this
    rw [he] at hc
    simp [WordPairing.inverseLetter] at hc
  · have hlast : i.val = u.length - 1 := by omega
    have hrot := finRotate_val_last i (by omega)
    have hne : u ≠ [] := List.ne_nil_of_length_pos hn
    have hc := hu.2 (u.getLast hne) (List.getLast_mem_getLast? hne) (u.head hne)
      (List.head_mem_head? hne)
    have he : u.head hne = WordPairing.inverseLetter (u.getLast hne) := by
      have := h
      simp only [List.get_eq_getElem, hrot] at this
      rw [List.head_eq_getElem, List.getLast_eq_getElem]
      simpa [hlast] using this
    rw [he] at hc
    simp [WordPairing.inverseLetter] at hc

end

variable {V D S₀ : Type} [Fintype V] [Fintype D] {Γ : PortGraph V D} {label : D → S₀ × Bool}
  {u : List (S₀ × Bool)} {G : Type} [Group G] {eval : S₀ × Bool → G}
  {O : Type} [Fintype O]
  {a : SphericalPicture.Data (O := O) (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter}
  {l : PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter eval a}

lemma Capped.rotation_dart (hc : Capped eval a l) {o : O} {i : Fin u.length}
    (ho : a.dart o = Sum.inr (i, true)) :
    a.dart (a.rotation o) = Sum.inr (finRotate u.length i, true) := by
  have hcons := a.consistent o
  rw [ho] at hcons
  cases hd : a.dart (a.rotation o) with
  | inl d =>
    rw [hd] at hcons
    simp [plusGraph, SumPort.graph, cycleGraph] at hcons
  | inr y =>
    rcases y with ⟨j, b⟩
    rw [hd] at hcons
    cases b
    · exact absurd hd (hc.no_back _ j)
    · have h2 : finRotate u.length i = j := by
        simpa [plusGraph, SumPort.graph, cycleGraph] using hcons
      rw [← h2]

/-- The occurrence reading the `i`-th letter of the outer word. -/
noncomputable def Capped.occ (hc : Capped eval a l) (i : Fin u.length) : O := (hc.unique i).exists.choose
lemma Capped.occ_dart (hc : Capped eval a l) (i : Fin u.length) :
    a.dart (hc.occ i) = Sum.inr (i, true) := (hc.unique i).exists.choose_spec
lemma Capped.occ_eq (hc : Capped eval a l) {o : O} {i : Fin u.length}
    (ho : a.dart o = Sum.inr (i, true)) : o = hc.occ i :=
  (hc.unique i).unique ho (hc.occ_dart i)

lemma Capped.outer_same_cycle (hc : Capped eval a l) (hn : 0 < u.length) :
    ∀ k (hk : k < u.length), a.rotation.SameCycle (hc.occ ⟨0, hn⟩) (hc.occ ⟨k, hk⟩) := by
  intro k
  induction k with
  | zero => intro _; exact Equiv.Perm.SameCycle.refl _ _
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hd := hc.rotation_dart (hc.occ_dart ⟨k, by omega⟩)
    have hrot : finRotate u.length ⟨k, by omega⟩ = ⟨k + 1, hk⟩ :=
      Fin.ext (finRotate_val_succ _ hk)
    rw [hrot] at hd
    have he := hc.occ_eq hd
    rw [← he]
    exact hprev.trans (Equiv.Perm.SameCycle.refl _ _ |>.apply_right)

/-- The outer occurrences form at most one boundary circle. -/
lemma Capped.outer_cycles (hc : Capped eval a l) :
    (Finset.univ.filter (fun c : Cycle a.rotation => PictureMap.keepC a c = false)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  have key : ∀ c ∈ Finset.univ.filter (fun c : Cycle a.rotation => PictureMap.keepC a c = false),
      ∃ hn : 0 < u.length, c = cycle a.rotation (hc.occ ⟨0, hn⟩) := by
    intro c hc'
    obtain ⟨o, rfl⟩ := cycle_surjective a.rotation c
    have hk := (Finset.mem_filter.mp hc').2
    rw [PictureMap.keepC_cycle] at hk
    cases hd : a.dart o with
    | inl d => rw [hd] at hk; simp at hk
    | inr y =>
      rcases y with ⟨i, b⟩
      cases b
      · exact absurd hd (hc.no_back o i)
      · have hn : 0 < u.length := lt_of_le_of_lt (Nat.zero_le _) i.isLt
        refine ⟨hn, ?_⟩
        rw [hc.occ_eq hd]
        exact ((cycle_eq a.rotation).mpr (hc.outer_same_cycle hn i.val i.isLt)).symm
  intro c hc₁ c' hc₂
  obtain ⟨hn, rfl⟩ := key c hc₁
  obtain ⟨hn', rfl⟩ := key c' hc₂
  rfl

/-- The outer occurrences are indexed by the letters of the outer word. -/
noncomputable def Capped.outerEquiv (hc : Capped eval a l) :
    {o : O // ¬(a.dart o).isLeft = true} ≃ Fin u.length where
  toFun o := ((a.dart o.val).getRight (by simpa using o.property)).1
  invFun i := ⟨hc.occ i, by rw [hc.occ_dart]; simp⟩
  left_inv := by
    rintro ⟨o, ho⟩
    apply Subtype.ext
    cases hd : a.dart o with
    | inl d => rw [hd] at ho; simp at ho
    | inr y =>
      rcases y with ⟨i, b⟩
      cases b
      · exact absurd hd (hc.no_back o i)
      · simp only [hd]
        exact (hc.occ_eq hd).symm
  right_inv := by
    intro i
    simp only [hc.occ_dart]
    rfl

@[simp] lemma Capped.outerEquiv_symm_val (hc : Capped eval a l) (i : Fin u.length) :
    (hc.outerEquiv.symm i).val = hc.occ i := rfl

lemma Capped.outer_count (hc : Capped eval a l) :
    (Finset.univ.filter (fun o : O => ¬(a.dart o).isLeft = true)).card = u.length := by
  classical
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr hc.outerEquiv).trans (Fintype.card_fin _)

variable {isRoot : V → Prop} {ε d lam : ℝ} {L : ℕ}

/-- **Proposition 4.4, free case.** In a pattern-free graph, a reduced capped picture for a
cyclically reduced word `u` has at most `16/(13ε)·|u|` cone occurrences. -/
theorem Capped.cone_bound (pf : PatternFree Γ label WordPairing.inverseLetter isRoot ε d lam L)
    (hu : FreeGroup.IsCyclicallyReduced u) (hc : Capped eval a l) (hr : a.Reduced) :
    (13 / 16 : ℝ) * ε * (Finset.univ.filter (fun o : O => (a.dart o).isLeft = true)).card ≤
      u.length := by
  classical
  by_cases hΓ : ∃ o : O, (a.dart o).isLeft = true
  · obtain ⟨o₀, ho₀⟩ := hΓ
    have hmonoΩ : ∀ o x y, a.dart o = Sum.inr x → a.dart (a.rotation o) = Sum.inr y →
        cycleLabel u y ≠ WordPairing.inverseLetter (cycleLabel u x) := by
      intro o x y hx hy
      rcases x with ⟨i, b⟩
      cases b
      · exact absurd hx (hc.no_back o i)
      · have hy' := hc.rotation_dart hx
        rw [hy] at hy'
        cases hy'
        simpa [cycleLabel] using cyclic_next_ne hu i
    obtain ⟨d₀, -⟩ : ∃ d, a.dart o₀ = Sum.inl d := by
      cases h : a.dart o₀ with
      | inl d => exact ⟨d, rfl⟩
      | inr _ => rw [h] at ho₀; simp at ho₀
    let m := PictureMap.toMap a hr pf.inv_ne pf.inv_involutive pf.immersed pf.label_reverse
      hmonoΩ hc.outer_cycles isRoot d₀
    have hk := m.key_free pf rfl ⟨cycle a.rotation o₀, by
      change PictureMap.keepC a (cycle a.rotation o₀) = true
      rw [PictureMap.keepC_cycle]; exact ho₀⟩
    rw [PictureMap.toMap_keptLength, PictureMap.toMap_outerLength, hc.outer_count] at hk
    exact hk
  · push Not at hΓ
    have h0 : (Finset.univ.filter (fun o : O => (a.dart o).isLeft = true)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro o _; simpa using hΓ o
    rw [h0]
    simp

end Kaplansky.Exclusion
