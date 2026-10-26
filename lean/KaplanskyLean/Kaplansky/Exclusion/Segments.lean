import Kaplansky.Exclusion.Localize

/-!
# Boundary maps, balanced segments and interval comparisons

A `MapSystem` is the combinatorial content of a reduced cone picture, after reading its boundary
circles as words: boundaries `T`, each a nonempty list of darts, a full genus-zero pairing `α` of
all boundary positions, and a predicate `keep` selecting the *graph boundaries* (cone disks, and the
rooted boundary if any). Boundaries outside `keep` are free outer boundaries: their darts are
irrelevant, and the arcs ending on them are discarded (paper, proof of Proposition 4.4).

This file follows OpenAI's `SampleGraph.FullPairing` (balanced segmentation, cut system, interval
comparisons), with the boundary words arbitrary, and adds the restriction to kept pieces and the
interval count `cuts ≤ 8·#boundaries + 2·#pieces` (`PlanarRotation.bad_gaps_le`, `cardinal_cuts`).
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.Exclusion

noncomputable section

open OAI.TorsionFreeZeroDivisors
open PortSubdivision ComparedBlocks BlockAlignment PermutationCycles PlanarRotation
open scoped Classical

section MapSystem
variable {V D A : Type} [Fintype D] (Γ : PortGraph V D) (label : D → A) (inv : A → A)
  (isRoot : V → Prop)

/-- The boundary map of a cone picture. -/
structure MapSystem where
  T : Type
  [fT : Fintype T]
  w : T → List D
  nonempty : ∀ t, w t ≠ []
  α : Equiv.Perm (Position (fun t => (w t).length))
  involutive : Function.Involutive α
  fixed_free : ∀ x, α x ≠ x
  genusZero : MapEuler.GenusZero (BoundaryRotation.perm (fun t => (w t).length)) α
  keep : T → Prop
  root : Option T
  root_keep : ∀ t, root = some t → keep t
  root_only : root ≠ none → ∀ t, keep t
  chain : ∀ t, keep t → (w t).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse)
  cyclic : ∀ t, keep t → root ≠ some t →
    ∀ᵉ (x ∈ (w t).getLast?) (y ∈ (w t).head?), WeightedMoore.PortWalk.step Γ.origin Γ.reverse x y
  root_start : ∀ t, root = some t → isRoot (Γ.origin ((w t).head (nonempty t)))
  compatible : ∀ x, keep x.1 → keep (α x).1 →
    label (RawDecomposition.dart w (α x)) = inv (label (RawDecomposition.dart w x))
  reduced : ∀ x, keep x.1 → keep (α x).1 →
    RawDecomposition.dart w x ≠ RawDecomposition.dart w (α x) ∧
    RawDecomposition.dart w x ≠ Γ.reverse (RawDecomposition.dart w (α x))
  monogons : (fixed (opposite (BoundaryRotation.perm (fun t => (w t).length)) α)).card ≤ 1
  outer_le : (Finset.univ.filter (fun t => ¬keep t)).card ≤ 1

attribute [instance] MapSystem.fT

namespace MapSystem
variable {Γ label inv isRoot}
variable (m : MapSystem Γ label inv isRoot)

open scoped Classical BigOperators

/-- Total length of the kept (graph) boundaries. -/
noncomputable def keptLength : ℕ := ∑ t ∈ Finset.univ.filter m.keep, (m.w t).length
/-- Total length of the free outer boundaries. -/
noncomputable def outerLength : ℕ := ∑ t ∈ Finset.univ.filter (fun t => ¬m.keep t), (m.w t).length

variable (cap : ℕ) (hc : 0 < cap)

abbrev Piece := BalancedWords.Piece m.w cap
abbrev seg (p : m.Piece cap) : List D := BalancedWords.segment m.w cap hc p
abbrev slen := BalancedRotation.len m.w cap hc
abbrev e := BalancedRotation.e m.w cap hc

/-- The pairing, transported to segment positions. -/
def α' : Equiv.Perm (Position (BalancedRotation.len m.w cap hc)) :=
  (BalancedRotation.e m.w cap hc).symm.permCongr m.α
lemma α'_involutive : Function.Involutive (m.α' cap hc) :=
  PermutationTransport.involutive (BalancedRotation.e m.w cap hc).symm m.α m.involutive
lemma α'_fixed_free (p : Position (BalancedRotation.len m.w cap hc)) : m.α' cap hc p ≠ p :=
  PermutationTransport.fixed_free (BalancedRotation.e m.w cap hc).symm m.α m.fixed_free p
lemma transport (p : Position (BalancedRotation.len m.w cap hc)) :
    BalancedRotation.e m.w cap hc (m.α' cap hc p) = m.α (BalancedRotation.e m.w cap hc p) := by
  simp only [α', Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

def cuts : PlanarRuns.CutSystem (BalancedRotation.perm m.w cap hc) :=
  PlanarRuns.CutSystem.ofMarks (m.α' cap hc) (BoundaryRotation.ends (BalancedRotation.len m.w cap hc))
    (BalancedRotation.hits m.w cap hc)
theorem paired : (m.cuts cap hc).Paired (m.α' cap hc) :=
  PlanarRuns.CutSystem.ofMarks_paired (m.α' cap hc)
    (BoundaryRotation.ends (BalancedRotation.len m.w cap hc))
    (BalancedRotation.hits m.w cap hc) (m.α'_involutive cap hc) (m.α'_fixed_free cap hc)
lemma step (p : Position (BalancedRotation.len m.w cap hc)) (hp : p ∉ (m.cuts cap hc).cut) :
    (BalancedRotation.perm m.w cap hc p).1 = p.1 ∧
      (BalancedRotation.perm m.w cap hc p).2.val = p.2.val + 1 := by
  apply BalancedRotation.step
  have hb := WordPositions.bounds p.2
  have hn : p ∉ BoundaryRotation.ends (BalancedRotation.len m.w cap hc) := by
    intro hm
    apply hp
    simp only [cuts, PlanarRuns.CutSystem.ofMarks, PlanarRotation.cuts, Finset.mem_union]
    exact Or.inl (Or.inr hm)
  have hn : p.2.val + 1 ≠ (BalancedRotation.len m.w cap hc p.1 : ℤ) := by
    intro he
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  omega
abbrev Side := {p // p ∈ (m.cuts cap hc).cut}
/-- The interval comparisons of all runs of the whole map. -/
def comparisons : Comparisons (E := m.Side cap hc) (BalancedRotation.len m.w cap hc) :=
  PlanarIntervals.comparisons (m.cuts cap hc) (m.paired cap hc) (m.step cap hc)
def lower (d : m.Side cap hc) : ℕ := (PlanarIntervals.lower (m.cuts cap hc) (m.paired cap hc) d).toNat
def upper (d : m.Side cap hc) : ℕ := (PlanarIntervals.upper (m.cuts cap hc) d).toNat
lemma bounds (d : m.Side cap hc) :
    0 ≤ PlanarIntervals.lower (m.cuts cap hc) (m.paired cap hc) d ∧
    PlanarIntervals.lower (m.cuts cap hc) (m.paired cap hc) d < PlanarIntervals.upper (m.cuts cap hc) d ∧
    PlanarIntervals.upper (m.cuts cap hc) d ≤
      BalancedRotation.len m.w cap hc ((m.paired cap hc).first d).1 :=
  PlanarIntervals.bounds (m.cuts cap hc) (m.paired cap hc) (m.step cap hc) d
lemma lower_eq (d : m.Side cap hc) : (m.comparisons cap hc).lo d = m.lower cap hc d := by
  change (PlanarIntervals.lower (m.cuts cap hc) (m.paired cap hc) d : ℝ) = _
  rw [lower, ← Int.cast_natCast, Int.toNat_of_nonneg (m.bounds cap hc d).1]
lemma upper_eq (d : m.Side cap hc) : (m.comparisons cap hc).hi d = m.upper cap hc d := by
  change (PlanarIntervals.upper (m.cuts cap hc) d : ℝ) = _
  rw [upper, ← Int.cast_natCast, Int.toNat_of_nonneg (by have := m.bounds cap hc d; omega)]
lemma lower_le (d : m.Side cap hc) : m.lower cap hc d ≤ m.upper cap hc d := by
  have := m.bounds cap hc d
  dsimp only [lower, upper]
  omega
lemma upper_le (d : m.Side cap hc) :
    m.upper cap hc d ≤ BalancedRotation.len m.w cap hc ((m.comparisons cap hc).source d) := by
  exact Int.toNat_le.mpr (m.bounds cap hc d).2.2
lemma dart (p : Position (BalancedRotation.len m.w cap hc)) :
    RawDecomposition.dart (BalancedWords.segment m.w cap hc) p =
      RawDecomposition.dart m.w (BalancedRotation.e m.w cap hc p) :=
  WordPositions.segments_dart m.w cap hc p

lemma comparisons_partner (p : Position (BalancedRotation.len m.w cap hc)) :
    (m.comparisons cap hc).pairing.partner p = m.α' cap hc p := rfl

/-! ### Counting cuts -/

lemma opposite_transport (p : Position (BalancedRotation.len m.w cap hc)) :
    BalancedRotation.e m.w cap hc (opposite (BalancedRotation.perm m.w cap hc) (m.α' cap hc) p) =
      opposite (BoundaryRotation.perm (fun t => (m.w t).length)) m.α
        (BalancedRotation.e m.w cap hc p) := by
  change BalancedRotation.e m.w cap hc (m.α' cap hc (BalancedRotation.perm m.w cap hc p)) = _
  rw [m.transport, BalancedRotation.transport]
  rfl

lemma monogons' :
    (fixed (opposite (BalancedRotation.perm m.w cap hc) (m.α' cap hc))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  apply (BalancedRotation.e m.w cap hc).injective
  apply Finset.card_le_one.mp m.monogons
  · simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← m.opposite_transport, hp]
  · simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← m.opposite_transport, hq]

lemma opposite_eq : opposite (BalancedRotation.perm m.w cap hc) (m.α' cap hc) =
    (BalancedRotation.e m.w cap hc).symm.permCongr
      (opposite (BoundaryRotation.perm (fun t => (m.w t).length)) m.α) :=
  (PermutationTransport.mul (BalancedRotation.e m.w cap hc).symm m.α _).symm

lemma balanced_euler [Nonempty (Position (fun t => (m.w t).length))] :
    Fintype.card (Position (BalancedRotation.len m.w cap hc)) + 4 ≤
      2 * Fintype.card (Cycle (BalancedRotation.perm m.w cap hc)) +
      2 * Fintype.card (Cycle (opposite (BalancedRotation.perm m.w cap hc) (m.α' cap hc))) := by
  have h := MapEuler.euler_of_genusZero _ _ m.genusZero m.fixed_free
  rw [m.opposite_eq, PermutationTransport.card_cycles]
  change _ ≤ 2 * Fintype.card (Cycle ((BalancedRotation.e m.w cap hc).symm.permCongr
    (BoundaryRotation.perm (fun t => (m.w t).length)))) + _
  rw [PermutationTransport.card_cycles, Fintype.card_congr (BalancedRotation.e m.w cap hc)]
  exact h

lemma cycles_le_T : Fintype.card (Cycle (BalancedRotation.perm m.w cap hc)) ≤ Fintype.card m.T := by
  change Fintype.card (Cycle ((BalancedRotation.e m.w cap hc).symm.permCongr
    (BoundaryRotation.perm (fun t => (m.w t).length)))) ≤ _
  rw [PermutationTransport.card_cycles]
  exact BoundaryRotation.cycles_le _

/-- `cuts ≤ 8·#boundaries + 2·#pieces`. -/
lemma cuts_card :
    (m.cuts cap hc).cut.card ≤ 8 * Fintype.card m.T + 2 * Fintype.card (m.Piece cap) := by
  by_cases hne : Nonempty (Position (fun t => (m.w t).length))
  · have := hne
    have hb := bad_gaps_le (BalancedRotation.perm m.w cap hc) (m.α' cap hc)
      (m.balanced_euler cap hc) (m.monogons' cap hc)
    have hcc := cardinal_cuts (BalancedRotation.perm m.w cap hc) (m.α' cap hc)
      (BoundaryRotation.ends (BalancedRotation.len m.w cap hc))
    have hT := m.cycles_le_T cap hc
    have he := BoundaryRotation.ends_le (BalancedRotation.len m.w cap hc)
    have hP : Fintype.card (BalancedWords.Piece m.w cap) = Fintype.card (m.Piece cap) :=
      Fintype.card_congr (Equiv.refl _)
    change (PlanarRotation.cuts _ _ _).card ≤ _
    omega
  · have hempty : IsEmpty (Position (BalancedRotation.len m.w cap hc)) := by
      have : IsEmpty (Position (fun t => (m.w t).length)) := not_nonempty_iff.mp hne
      exact (BalancedRotation.e m.w cap hc).isEmpty
    have : (m.cuts cap hc).cut = ∅ := by
      ext x; exact hempty.elim x
    rw [this, Finset.card_empty]
    exact Nat.zero_le _

/-! ### Restriction to kept pieces -/

/-- A piece is kept when its boundary is a graph boundary. -/
def keepP (p : m.Piece cap) : Prop := m.keep p.1

/-- The comparisons between kept pieces. -/
def keptComparisons :=
  RestrictComparisons.comparisons (m.comparisons cap hc) (m.keepP cap)

lemma kept_card_le :
    Fintype.card {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e} ≤
      (m.cuts cap hc).cut.card := by
  calc
    _ ≤ Fintype.card (m.Side cap hc) := Fintype.card_subtype_le _
    _ = _ := Fintype.card_coe _

lemma positions_filter_card {T' : Type} [Fintype T'] (l : T' → ℕ) (P : T' → Prop)
    [DecidablePred P] :
    (Finset.univ.filter (fun x : Position l => P x.1)).card = ∑ t ∈ Finset.univ.filter P, l t := by
  rw [← Fintype.card_subtype]
  have e : {x : Position l // P x.1} ≃ (t : {t // P t}) × Fin (l t.val) :=
    { toFun := fun x => ⟨⟨x.val.1, x.property⟩, WordPositions.fin l x.val |>.2⟩
      invFun := fun y => ⟨(WordPositions.fin l).symm ⟨y.1.val, y.2⟩, y.1.property⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        change (WordPositions.fin l).symm ⟨(WordPositions.fin l x).1, (WordPositions.fin l x).2⟩ = x
        exact (WordPositions.fin l).symm_apply_apply x
      right_inv := by
        rintro ⟨⟨t, ht⟩, i⟩
        rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) l).symm

lemma sigma_filter_card {T' : Type} [Fintype T'] (n : T' → ℕ) (P : T' → Prop)
    [DecidablePred P] :
    Fintype.card {x : (t : T') × Fin (n t) // P x.1} = ∑ t ∈ Finset.univ.filter P, n t := by
  have e : {x : (t : T') × Fin (n t) // P x.1} ≃ (t : {t // P t}) × Fin (n t.val) :=
    { toFun := fun x => ⟨⟨x.val.1, x.property⟩, x.val.2⟩
      invFun := fun y => ⟨⟨y.1.val, y.2⟩, y.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) n).symm

/-- Positions of discarded pieces: exactly the outer length. -/
lemma unkept_positions :
    (Finset.univ.filter (fun x : Position (BalancedRotation.len m.w cap hc) => ¬m.keepP cap x.1)).card =
      m.outerLength := by
  have h1 : (Finset.univ.filter (fun x : Position (BalancedRotation.len m.w cap hc) =>
      ¬m.keepP cap x.1)).card =
      (Finset.univ.filter (fun y : Position (fun t => (m.w t).length) => ¬m.keep y.1)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    apply Fintype.card_congr
    exact (BalancedRotation.e m.w cap hc).subtypeEquiv (fun x => by
      simp only [keepP]
      rw [BalancedRotation.source])
  rw [h1]
  exact positions_filter_card (fun t => (m.w t).length) (fun t => ¬m.keep t)

/-- Unpaired positions after discarding the outer pieces: at most the outer length. -/
lemma kept_fixed_le :
    (Finset.univ.filter (fun x => (m.keptComparisons cap hc).pairing.partner x = x)).card ≤
      m.outerLength := by
  have h := RestrictComparisons.fixed_card (m.comparisons cap hc) (m.keepP cap)
  have h0 : ∀ x, ¬((m.comparisons cap hc).pairing.partner x = x) :=
    fun x => m.α'_fixed_free cap hc x
  simp only [h0, Finset.filter_false, Finset.card_empty, zero_add] at h
  have h' := h.trans_eq (m.unkept_positions cap hc)
  convert h' using 3
  exact Iff.rfl

/-! ### Pieces -/

include hc in
lemma kept_boundaries_le :
    (Finset.univ.filter m.keep).card ≤ Fintype.card {p : m.Piece cap // m.keepP cap p} := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_le_of_injective
    (fun t => (⟨⟨t.val, ⟨0, BalancedPieces.number_pos hc⟩⟩, t.property⟩ :
      {p : m.Piece cap // m.keepP cap p}))
    (fun a b h => Subtype.ext (congrArg (fun q : {p : m.Piece cap // m.keepP cap p} => q.val.1) h))

lemma unkept_pieces (hcap : 6 ≤ cap) :
    Fintype.card {p : m.Piece cap // ¬m.keepP cap p} * cap ≤
      (Finset.univ.filter (fun t => ¬m.keep t)).card * cap + 3 * m.outerLength := by
  have he : Fintype.card {p : m.Piece cap // ¬m.keepP cap p} =
      ∑ t ∈ Finset.univ.filter (fun t => ¬m.keep t), BalancedPieces.number (m.w t).length cap := by
    exact sigma_filter_card (fun t => BalancedPieces.number (m.w t).length cap) (fun t => ¬m.keep t)
  rw [he, Finset.sum_mul, outerLength, Finset.card_eq_sum_ones, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  have h := BalancedPieces.number_charge (h := (m.w t).length) hcap
  by_cases hs : cap < (m.w t).length
  · rw [ite_eq_left hs] at h
    linarith
  · have hn : BalancedPieces.number (m.w t).length cap = 1 := by
      simp only [BalancedPieces.number]
      rw [ite_eq_left (show (m.w t).length ≤ cap by omega)]
    rw [hn]
    linarith

lemma card_pieces :
    Fintype.card (m.Piece cap) = Fintype.card {p : m.Piece cap // m.keepP cap p} +
      Fintype.card {p : m.Piece cap // ¬m.keepP cap p} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter_add_card_filter_not,
    Finset.card_univ]

/-- The interval count used in the localisation step. -/
lemma sides_count (hcap : 6 ≤ cap) :
    Fintype.card {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e} * cap ≤
      10 * Fintype.card {p : m.Piece cap // m.keepP cap p} * cap +
      10 * (Finset.univ.filter (fun t => ¬m.keep t)).card * cap + 6 * m.outerLength := by
  have h1 := m.kept_card_le cap hc
  have h2 := m.cuts_card cap hc
  have h3 : Fintype.card m.T = (Finset.univ.filter m.keep).card +
      (Finset.univ.filter (fun t => ¬m.keep t)).card := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have h4 := m.kept_boundaries_le cap hc
  have h5 := m.unkept_pieces cap hcap
  have h6 := m.card_pieces cap
  have hmul := Nat.mul_le_mul_right cap (h1.trans h2)
  have h4' := Nat.mul_le_mul_right cap h4
  rw [h3, h6] at hmul
  nlinarith

end MapSystem
end MapSystem

end

end Kaplansky.Exclusion
