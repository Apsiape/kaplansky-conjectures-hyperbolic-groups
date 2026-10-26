import OAI.Algebra.GroupRing.PictureChains

/-!
# Capped pictures

A *capped picture* for a word `u` (paper Definition 4.1, free case) is encoded as a lifted spherical
picture over `Γ⁺ = Γ ⊔ C_u`, where `C_u` is the cycle graph reading `u`, such that

* no occurrence uses a backward dart of `C_u`;
* every forward dart `(i, true)` of `C_u` occurs exactly once (the outer disk reads `u`);
* the lift places the occurrence of `(i, true)` at the value of the prefix `u.take i`.

OpenAI's surgery moves `band` and `tighten` (and their lifted versions) only ever act on
`Γ`-occurrences of such a picture, so they preserve these invariants. Hence a capped picture of
least size is reduced (paper Lemma 4.3, case (F)).
-/

namespace Kaplansky.Exclusion

open OAI.TorsionFreeZeroDivisors
open PortSubdivision

/-- The cycle graph of length `n`: the dart `(i, true)` runs from `i` to `i+1`. -/
def cycleGraph (n : ℕ) : PortGraph (Fin n) (Fin n × Bool) where
  origin d := if d.2 then d.1 else finRotate n d.1
  reverse d := (d.1, !d.2)
  reverse_reverse d := by simp
  reverse_ne d := by
    intro h
    have := congrArg Prod.snd h
    cases hd : d.2 <;> simp_all

lemma finRotate_val_succ {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    (finRotate n i).val = i.val + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact coe_finRotate_of_ne_last (fun he => by rw [he, Fin.val_last] at hi; omega)

lemma finRotate_val_last {n : ℕ} (i : Fin n) (hi : i.val + 1 = n) :
    (finRotate n i).val = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have he : i = Fin.last k := Fin.ext (by simp; omega)
  rw [he, finRotate_last]
  rfl

section Capped
open scoped Classical
variable {S₀ : Type}

/-- The labels of the cycle reading `u`. -/
def cycleLabel (u : List (S₀ × Bool)) (d : Fin u.length × Bool) : S₀ × Bool :=
  if d.2 then u.get d.1 else WordPairing.inverseLetter (u.get d.1)

variable {V D : Type} [Fintype D] (Γ : PortGraph V D) (label : D → S₀ × Bool)
  (u : List (S₀ × Bool))

abbrev plusGraph : PortGraph (V ⊕ Fin u.length) (D ⊕ (Fin u.length × Bool)) :=
  SumPort.graph Γ (cycleGraph u.length)
abbrev plusLabel : D ⊕ (Fin u.length × Bool) → S₀ × Bool := Sum.elim label (cycleLabel u)

lemma plusLabel_reverse (hl : ∀ d, label (Γ.reverse d) = WordPairing.inverseLetter (label d))
    (d : D ⊕ (Fin u.length × Bool)) :
    plusLabel label u ((plusGraph Γ u).reverse d) = WordPairing.inverseLetter (plusLabel label u d) := by
  rcases d with d | ⟨i, b⟩
  · exact hl d
  · cases b <;> simp [plusLabel, plusGraph, SumPort.graph, cycleGraph, cycleLabel,
      WordPairing.inverseLetter]

variable {G : Type} [Group G] (eval : S₀ × Bool → G)

/-- The prefix values along the outer word. -/
def prefixValue (k : ℕ) : G := ((u.take k).map eval).prod

variable {Γ label u}

/-- The capped invariants of a lifted picture over `Γ⁺`. -/
structure Capped {O : Type} [Fintype O]
    (a : SphericalPicture.Data (O := O) (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter)
    (l : PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter eval a) :
    Prop where
  no_back : ∀ o i, a.dart o ≠ Sum.inr (i, false)
  unique : ∀ i, ∃! o, a.dart o = Sum.inr (i, true)
  pos : ∀ o i, a.dart o = Sum.inr (i, true) → l.position o = prefixValue u eval i.val

variable {eval}
variable {O : Type} [Fintype O]
  {a : SphericalPicture.Data (O := O) (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter}
  {l : PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter eval a}

lemma Capped.inl_of_reverse (hc : Capped eval a l) {p q : O}
    (he : a.dart q = (plusGraph Γ u).reverse (a.dart p)) :
    (∃ d, a.dart p = Sum.inl d) ∧ ∃ d, a.dart q = Sum.inl d := by
  cases hp : a.dart p with
  | inl d =>
    rw [hp] at he
    exact ⟨⟨d, rfl⟩, ⟨Γ.reverse d, by simpa [plusGraph, SumPort.graph] using he⟩⟩
  | inr x =>
    rcases x with ⟨i, b⟩
    rw [hp] at he
    cases b
    · exact absurd hp (hc.no_back p i)
    · have : a.dart q = Sum.inr (i, false) := by simpa [plusGraph, SumPort.graph, cycleGraph] using he
      exact absurd this (hc.no_back q i)

lemma Capped.ne_of_inl (hc : Capped eval a l) {p o : O} (hp : ∃ d, a.dart p = Sum.inl d)
    {i : Fin u.length} (ho : a.dart o = Sum.inr (i, true)) : o ≠ p := by
  rintro rfl
  obtain ⟨d, hd⟩ := hp
  rw [hd] at ho
  cases ho

variable (heval : ∀ x, eval (WordPairing.inverseLetter x) = (eval x)⁻¹)
  (hl : ∀ d, label (Γ.reverse d) = WordPairing.inverseLetter (label d))

/-- Band surgery preserves the capped invariants. -/
theorem Capped.band (hc : Capped eval a l) (p q : O) (hpq : p ≠ q) (hpair : a.partner p = q)
    (he : a.dart q = (plusGraph Γ u).reverse (a.dart p)) :
    Capped eval (a.band p q hpq hpair he)
      (PictureChains.band heval (plusLabel_reverse Γ label u hl) a l p q hpq hpair he) := by
  obtain ⟨hp, hq⟩ := hc.inl_of_reverse he
  refine ⟨?_, ?_, ?_⟩
  · intro o i
    exact hc.no_back _ i
  · intro i
    obtain ⟨o, ho, huniq⟩ := hc.unique i
    have hop : o ≠ p := hc.ne_of_inl hp ho
    have hoq : o ≠ q := hc.ne_of_inl hq ho
    refine ⟨⟨⟨o, hop⟩, fun h => hoq (congrArg Subtype.val h)⟩, ho, ?_⟩
    intro r hr
    have := huniq (BandEuler.val p q hpq r) hr
    apply Subtype.ext; apply Subtype.ext
    exact this
  · intro o i ho
    exact hc.pos _ i ho

/-- Tightening preserves the capped invariants. -/
theorem Capped.tighten (hc : Capped eval a l) (p q : O) (hpq : p ≠ q) (hsp : a.rotation p = q)
    (he : a.dart q = (plusGraph Γ u).reverse (a.dart p)) :
    Capped eval (a.tighten p q hpq WordPairing.inverseLetter_involutive
        (plusLabel_reverse Γ label u hl) hsp he)
      (PictureChains.tighten heval (plusLabel_reverse Γ label u hl) a l p q hpq
        WordPairing.inverseLetter_involutive hsp he) := by
  obtain ⟨hp, hq⟩ := hc.inl_of_reverse he
  refine ⟨?_, ?_, ?_⟩
  · intro o i
    exact hc.no_back _ i
  · intro i
    obtain ⟨o, ho, huniq⟩ := hc.unique i
    have hop : o ≠ p := hc.ne_of_inl hp ho
    have hoq : o ≠ q := hc.ne_of_inl hq ho
    refine ⟨⟨o, hop, hoq⟩, ho, ?_⟩
    intro r hr
    exact Subtype.ext (huniq r.val hr)
  · intro o i ho
    exact hc.pos _ i ho

/-- Relabel the occurrences of a lifted picture. -/
def liftReindex {O' : Type} [Fintype O'] (e : O ≃ O') :
    PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter eval
      (a.reindex e) where
  position i := l.position (e.symm i)
  next i := by
    change l.position (e.symm (e.permCongr a.rotation i)) = _
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact l.next _
  pair i := by
    change l.position (e.symm (e.permCongr a.partner i)) = _
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact l.pair _

theorem Capped.reindex (hc : Capped eval a l) {O' : Type} [Fintype O'] (e : O ≃ O') :
    Capped eval (a.reindex e) (liftReindex (l := l) e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro o i
    exact hc.no_back _ i
  · intro i
    obtain ⟨o, ho, huniq⟩ := hc.unique i
    refine ⟨e o, by simpa [SphericalPicture.Data.reindex] using ho, ?_⟩
    intro r hr
    have := huniq (e.symm r) hr
    rw [← this, Equiv.apply_symm_apply]
  · intro o i ho
    exact hc.pos _ i ho

include heval hl in
/-- A capped lifted picture that is not reduced can be shrunk by two occurrences (band or
tightening), staying capped. -/
theorem Capped.shrink (hc : Capped eval a l) (hn : ¬a.Reduced) :
    ∃ k, k + 2 = Fintype.card O ∧
      ∃ (b : SphericalPicture.Data (O := Fin k) (plusGraph Γ u) (plusLabel label u)
          WordPairing.inverseLetter)
        (lb : PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter
          eval b),
        Capped eval b lb := by
  simp only [SphericalPicture.Data.Reduced, not_and_or, not_forall, Classical.not_not] at hn
  rcases hn with ⟨p, hp⟩ | ⟨p, hp⟩
  · let q := a.partner p
    have hpq : p ≠ q := (a.fixed_free p).symm
    have hc' := hc.band heval hl p q hpq rfl hp
    exact ⟨_, BandEuler.two_fewer p q hpq, _, _, hc'.reindex (Fintype.equivFin _)⟩
  · let q := a.rotation p
    have hpq : p ≠ q := a.unequal_backtrack p q hp
    have hc' := hc.tighten heval hl p q hpq rfl hp
    exact ⟨_, SphericalPicture.Data.remaining_two_fewer p q hpq, _, _,
      hc'.reindex (Fintype.equivFin _)⟩

include heval hl in
/-- A capped lifted picture of least size is reduced. -/
theorem exists_reduced_capped (hc : Capped eval a l) :
    ∃ (k : ℕ) (b : SphericalPicture.Data (O := Fin k) (plusGraph Γ u) (plusLabel label u)
        WordPairing.inverseLetter)
      (lb : PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter eval b),
      Capped eval b lb ∧ b.Reduced := by
  classical
  let P : ℕ → Prop := fun k => ∃ (b : SphericalPicture.Data (O := Fin k) (plusGraph Γ u)
      (plusLabel label u) WordPairing.inverseLetter)
    (lb : PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter eval b),
    Capped eval b lb
  have hex : ∃ k, P k :=
    ⟨Fintype.card O, a.reindex (Fintype.equivFin O), liftReindex (l := l) (Fintype.equivFin O),
      hc.reindex (Fintype.equivFin O)⟩
  obtain ⟨b, lb, hb⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, b, lb, hb, ?_⟩
  by_contra hn
  obtain ⟨k, hk, b', lb', hb'⟩ := hb.shrink heval hl hn
  have hmin := Nat.find_min' hex ⟨b', lb', hb'⟩
  simp only [Fintype.card_fin] at hk
  omega

end Capped

end Kaplansky.Exclusion
