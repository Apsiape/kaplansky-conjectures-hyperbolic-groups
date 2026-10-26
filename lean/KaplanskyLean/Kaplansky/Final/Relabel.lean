import Kaplansky.Exclusion.Basic

/-!
# Signing an alphabet with a fixed-point-free involution

Theorem B (`Kaplansky.Main.theoremB`) is stated for graphs labelled by *signed letters*
`S₀ × Bool` with OpenAI's inversion `WordPairing.inverseLetter (a, b) = (a, !b)`. The odd-`p`
model of Section 7 labels its darts by an abstract alphabet `T` with a fixed-point-free involution
`t ↦ t̄`. This file

* builds a signing `signing : T → Orbit inv × Bool` (injective, `signing (inv t) =
  inverseLetter (signing t)`), where `Orbit inv` is the set of `{t, t̄}`-orbits;
* transports pattern-freeness (Definition 3.3) along any injective, involution-compatible
  relabelling (`patternFree_relabel`): every field except the reduction-compatibility of path
  systems is label-independent, and compatibility pulls back along an injection.
-/

namespace Kaplansky.Final

open OAI.TorsionFreeZeroDivisors
open PortSubdivision
open Kaplansky.Exclusion

/-! ### Orbits of a fixed-point-free involution -/

section Orbits

variable {T : Type} (inv : T → T) (hinv : Function.Involutive inv)

/-- The orbit relation `{t, t̄}` of an involution. -/
def orbitSetoid : Setoid T where
  r a b := b = a ∨ b = inv a
  iseqv := by
    refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
    · intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; exact (hinv a).symm)
    · intro a b c hab hbc
      rcases hab with hab | hab <;> rcases hbc with hbc | hbc
      · exact Or.inl (hbc.trans hab)
      · exact Or.inr (by rw [hbc, hab])
      · exact Or.inr (hbc.trans hab)
      · exact Or.inl (by rw [hbc, hab]; exact hinv a)

/-- The orbits `{t, t̄}`. -/
def Orbit : Type := Quotient (orbitSetoid inv hinv)

theorem out_mk_eq (t : T) :
    (Quotient.mk (orbitSetoid inv hinv) t).out = t ∨
      (Quotient.mk (orbitSetoid inv hinv) t).out = inv t := by
  have h : (orbitSetoid inv hinv) t (Quotient.mk (orbitSetoid inv hinv) t).out :=
    Quotient.exact (Quotient.out_eq _).symm
  exact h

theorem mk_inv (t : T) :
    Quotient.mk (orbitSetoid inv hinv) (inv t) = Quotient.mk (orbitSetoid inv hinv) t :=
  Quotient.sound (Or.inr (hinv t).symm)

instance [Finite T] : Finite (Orbit inv hinv) := Quotient.finite _

noncomputable instance : DecidableEq (Orbit inv hinv) := Classical.decEq _

variable [DecidableEq T]

/-- Signed letters: the orbit of `t`, and whether `t` is the chosen representative. -/
noncomputable def signing (t : T) : Orbit inv hinv × Bool :=
  (Quotient.mk (orbitSetoid inv hinv) t,
    decide ((Quotient.mk (orbitSetoid inv hinv) t).out = t))

variable (hne : ∀ t, inv t ≠ t)
include hne

theorem signing_inv (t : T) :
    signing inv hinv (inv t) = WordPairing.inverseLetter (signing inv hinv t) := by
  refine Prod.ext (mk_inv inv hinv t) ?_
  show decide ((Quotient.mk (orbitSetoid inv hinv) (inv t)).out = inv t) =
    !decide ((Quotient.mk (orbitSetoid inv hinv) t).out = t)
  rw [mk_inv inv hinv t]
  rcases out_mk_eq inv hinv t with h | h
  · rw [h]
    simp [(hne t).symm]
  · rw [h]
    simp [hne t]

theorem signing_injective : Function.Injective (signing inv hinv) := by
  intro a b hab
  have h1 : Quotient.mk (orbitSetoid inv hinv) a = Quotient.mk (orbitSetoid inv hinv) b :=
    congrArg Prod.fst hab
  have h2 : decide ((Quotient.mk (orbitSetoid inv hinv) a).out = a) =
      decide ((Quotient.mk (orbitSetoid inv hinv) b).out = b) := congrArg Prod.snd hab
  have hr : (orbitSetoid inv hinv) a b := Quotient.exact h1
  rcases hr with hr | hr
  · exact hr.symm
  · exfalso
    rw [← h1, hr] at h2
    rcases out_mk_eq inv hinv a with h | h
    · rw [h] at h2
      simp [(hne a).symm] at h2
    · rw [h] at h2
      simp [hne a] at h2

end Orbits

/-! ### Relabelling pattern-free graphs -/

section Relabel

variable {V D A A' : Type} [Fintype V] [Fintype D] {Γ : PortGraph V D} {label : D → A}
  {inv : A → A} {inv' : A' → A'} {isRoot : V → Prop}

/-- A bounded path system for the relabelled graph is one for the original graph. -/
def unrelabel (e : A → A') (he : Function.Injective e) (hinv : ∀ a, e (inv a) = inv' (e a))
    {Bnd K I L : ℕ} {ε : ℝ}
    (s : GBoundedSystem Γ (e ∘ label) inv' isRoot Bnd K I L ε) :
    GBoundedSystem Γ label inv isRoot Bnd K I L ε where
  P := s.P
  E := s.E
  fP := s.fP
  fE := s.fE
  paths := s.paths
  nonempty := s.nonempty
  root := s.root
  path_bound := s.path_bound
  comparison_bound := s.comparison_bound
  path_chain := s.path_chain
  cyclic_chain := s.cyclic_chain
  length_le := s.length_le
  length_ge := s.length_ge
  comparisons := s.comparisons
  lower := s.lower
  upper := s.upper
  lower_eq := s.lower_eq
  upper_eq := s.upper_eq
  lower_le := s.lower_le
  upper_le := s.upper_le
  reduced := s.reduced
  unpaired_le := s.unpaired_le
  root_start := s.root_start
  compatible := by
    intro p x hx
    apply he
    have h := s.compatible p x hx
    simp only [Function.comp_apply] at h
    rw [h]
    split_ifs
    · rw [hinv]
    · rfl

/-- **Pattern-freeness is invariant under injective, involution-compatible relabelling.** -/
theorem patternFree_relabel {ε d lam : ℝ} {L : ℕ}
    (pf : PatternFree Γ label inv isRoot ε d lam L) (e : A → A') (he : Function.Injective e)
    (hinv : ∀ a, e (inv a) = inv' (e a)) (hinv' : Function.Involutive inv')
    (hne' : ∀ a, inv' a ≠ a) :
    PatternFree Γ (e ∘ label) inv' isRoot ε d lam L where
  inv_involutive := hinv'
  inv_ne := hne'
  label_reverse x := by
    simp only [Function.comp_apply, pf.label_reverse, hinv]
  immersed x y ho hl := pf.immersed x y ho (he hl)
  eps_pos := pf.eps_pos
  eps_le := pf.eps_le
  one_le_d := pf.one_le_d
  one_le_lam := pf.one_le_lam
  scale := pf.scale
  degree := pf.degree
  girth := pf.girth
  diameter := pf.diameter
  size := pf.size
  avoid := ⟨fun s => pf.avoid.false (unrelabel e he hinv s)⟩

/-- Pattern-free graphs over an alphabet with a fixed-point-free involution are pattern-free over
signed letters, via `signing`. -/
theorem patternFree_signed [DecidableEq A] {ε d lam : ℝ} {L : ℕ}
    (pf : PatternFree Γ label inv isRoot ε d lam L) :
    PatternFree Γ (signing inv pf.inv_involutive ∘ label) WordPairing.inverseLetter isRoot
      ε d lam L :=
  patternFree_relabel pf _ (signing_injective inv pf.inv_involutive pf.inv_ne)
    (signing_inv inv pf.inv_involutive pf.inv_ne) WordPairing.inverseLetter_involutive
    (fun a h => by
      rcases a with ⟨a, b⟩
      cases b <;> simp [WordPairing.inverseLetter] at h)

end Relabel

end Kaplansky.Final
