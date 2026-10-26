import Kaplansky.Exclusion.Basic

/-!
# Signed alphabets

Theorem B is stated for labels in `S₀ × Bool` with `WordPairing.inverseLetter` (the letters of
the free group on `S₀`). A model whose alphabet is an arbitrary finite type `A` with a
fixed-point-free involution (paper: "a signed alphabet") is transported along the bijection
`A ≃ {pairs} × Bool` of `signedEquiv`; pattern-freeness is invariant (`PatternFree.relabel`).
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.Exclusion

noncomputable section

open OAI.TorsionFreeZeroDivisors
open PortSubdivision ComparedBlocks

section Signed
variable {A : Type} (inv : A → A) (hinv : Function.Involutive inv) (hne : ∀ a, inv a ≠ a)

/-- The generators: pairs `{t, t̄}`. -/
abbrev Pairs := PlanarRuns.CutSystem.PairOrbit.Orbit inv hinv

include hne in
lemma out_mem (a : A) : Quotient.out (Quotient.mk (PlanarRuns.CutSystem.PairOrbit.relation inv hinv) a) = a ∨
    Quotient.out (Quotient.mk (PlanarRuns.CutSystem.PairOrbit.relation inv hinv) a) = inv a := by
  have h : (PlanarRuns.CutSystem.PairOrbit.relation inv hinv).r
      (Quotient.out (Quotient.mk (PlanarRuns.CutSystem.PairOrbit.relation inv hinv) a)) a :=
    Quotient.exact (Quotient.out_eq _)
  rcases h with h | h
  · exact Or.inl h
  · right; exact (hinv _).symm.trans (congrArg inv h)

open Classical in
/-- An orientation of the signed alphabet. -/
noncomputable def signedEquiv : A ≃ Pairs inv hinv × Bool where
  toFun a := (Quotient.mk _ a, decide (a = Quotient.out (Quotient.mk (PlanarRuns.CutSystem.PairOrbit.relation inv hinv) a)))
  invFun x := if x.2 then Quotient.out x.1 else inv (Quotient.out x.1)
  left_inv a := by
    rcases out_mem inv hinv hne a with h | h
    · simp [h]
    · have hne' : ¬(a = inv a) := fun h' => hne a h'.symm
      simp only [h, hne', decide_false, Bool.false_eq_true, ite_false, hinv a]
  right_inv x := by
    rcases x with ⟨s, b⟩
    cases b
    · have hs : Quotient.mk (PlanarRuns.CutSystem.PairOrbit.relation inv hinv) (inv (Quotient.out s)) = s := by
        conv_rhs => rw [← Quotient.out_eq s]
        apply Quotient.sound
        exact Or.inr (hinv _)
      simp only [Bool.false_eq_true, ite_false, hs, Prod.mk.injEq, true_and]
      simp [hne]
    · simp

lemma signedEquiv_inv (a : A) :
    signedEquiv inv hinv hne (inv a) = WordPairing.inverseLetter (signedEquiv inv hinv hne a) := by
  classical
  have hq : Quotient.mk (PlanarRuns.CutSystem.PairOrbit.relation inv hinv) (inv a) =
      Quotient.mk (PlanarRuns.CutSystem.PairOrbit.relation inv hinv) a :=
    Quotient.sound (Or.inr (hinv a))
  simp only [signedEquiv, Equiv.coe_fn_mk, WordPairing.inverseLetter, hq, Prod.mk.injEq,
    true_and]
  rcases out_mem inv hinv hne a with h | h
  · rw [h]; simp [hne a]
  · rw [h]; simp [(hne a).symm]

end Signed

section Relabel
variable {V D A B : Type} [Fintype V] [Fintype D] {Γ : PortGraph V D} {label : D → A}
  {inv : A → A} {isRoot : V → Prop} {ε d lam : ℝ} {L : ℕ}

/-- Pattern-freeness is invariant under an involution-compatible relabelling of the alphabet. -/
theorem PatternFree.relabel (pf : PatternFree Γ label inv isRoot ε d lam L) (e : A ≃ B)
    (inv' : B → B) (he : ∀ a, e (inv a) = inv' (e a)) :
    PatternFree Γ (e ∘ label) inv' isRoot ε d lam L where
  inv_involutive b := by
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← he, ← he, pf.inv_involutive]
  inv_ne b := by
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← he]
    exact fun h => pf.inv_ne a (e.injective h)
  label_reverse x := by
    simp only [Function.comp_apply, pf.label_reverse, he]
  immersed x y ho hl := pf.immersed x y ho (e.injective hl)
  eps_pos := pf.eps_pos
  eps_le := pf.eps_le
  one_le_d := pf.one_le_d
  one_le_lam := pf.one_le_lam
  scale := pf.scale
  degree := pf.degree
  girth := pf.girth
  diameter := pf.diameter
  size := pf.size
  avoid := by
    refine ⟨fun s => pf.avoid.false ?_⟩
    exact
      { P := s.P, E := s.E, fP := s.fP, fE := s.fE, paths := s.paths, nonempty := s.nonempty
        root := s.root, path_bound := s.path_bound, comparison_bound := s.comparison_bound
        path_chain := s.path_chain, cyclic_chain := s.cyclic_chain, length_le := s.length_le
        length_ge := s.length_ge, comparisons := s.comparisons, lower := s.lower
        upper := s.upper, lower_eq := s.lower_eq, upper_eq := s.upper_eq
        lower_le := s.lower_le, upper_le := s.upper_le, reduced := s.reduced
        unpaired_le := s.unpaired_le, root_start := s.root_start
        compatible := by
          intro p x hx
          have h := s.compatible p x hx
          simp only [Function.comp_apply] at h
          apply e.injective
          rw [h]
          split_ifs <;> simp [he] }

end Relabel

end

end Kaplansky.Exclusion
