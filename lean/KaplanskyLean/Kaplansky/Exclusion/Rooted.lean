import Kaplansky.Exclusion.KeyEstimate
import OAI.Algebra.GroupRing.ConcreteGroup

/-!
# Root protection (paper Theorem B(ii); Proposition 4.4, rooted case)

A reduced rooted disc picture (OpenAI's `FinitePicture.Data` with its break marker deleted) is read
as a rooted boundary map (generic version of OpenAI's `SampleGraph.Picture.system`/`pairing`), and
the key estimate excludes it. Consequently no path from a root to a different vertex has trivial
label in the cone group.
-/

namespace Kaplansky.Exclusion

open OAI.TorsionFreeZeroDivisors
open PortSubdivision ComparedBlocks BlockAlignment PermutationCycles

namespace RootedMap
open scoped Classical

variable {V D A : Type} [Fintype V] [Fintype D] {Γ : PortGraph V D} {label : D → A}
  {inv : A → A} {z w : V} {O : Type} [Fintype O]
  (a : FinitePicture.Data (O := O) Γ label inv z w) (hzw : z ≠ w)

noncomputable def coordinates : Position (fun c => (a.paths hzw c).length) ≃ a.Occ :=
  (WordPositions.fin _).trans (a.pathCoordinates hzw)

lemma dart (p : Position (fun c => (a.paths hzw c).length)) :
    RawDecomposition.dart (a.paths hzw) p = a.edge (coordinates a hzw p) := by
  rw [← (WordPositions.fin _).symm_apply_apply p, WordPositions.dart_fin]
  exact a.paths_dart hzw _

lemma rotation (p : Position (fun c => (a.paths hzw c).length)) :
    coordinates a hzw (BoundaryRotation.perm (fun c => (a.paths hzw c).length) p) =
      a.closedRotation (coordinates a hzw p) := by
  generalize he : (WordPositions.fin (fun c => (a.paths hzw c).length)) p = q
  have hp : p = (WordPositions.fin _).symm q := by rw [← he, Equiv.symm_apply_apply]
  rw [hp]
  rcases q with ⟨c, i⟩
  rw [BoundaryRotation.apply_fin]
  simp only [coordinates, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact a.pathCoordinates_rotate hzw c i

lemma rotation_conjugate : BoundaryRotation.perm (fun c => (a.paths hzw c).length) =
    (coordinates a hzw).symm.permCongr a.closedRotation := by
  apply Equiv.ext
  intro p
  apply (coordinates a hzw).injective
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact rotation a hzw p

lemma fixed_card_conj {X Y : Type} [Fintype X] [Fintype Y] (e : X ≃ Y) (f : Equiv.Perm X) :
    (fixed (e.permCongr f)).card = (fixed f).card := by
  simp only [fixed]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact (Fintype.card_congr (e.subtypeEquiv (fun x => by
    simp [Equiv.permCongr_apply]))).symm

variable (hr : a.Reduced) (hinv : ∀ x, inv x ≠ x) (hinvol : Function.Involutive inv)
  (hlabel : ∀ d, label (Γ.reverse d) = inv (label d))
  (himm : ∀ d e, Γ.origin d = Γ.origin e → label d = label e → d = e)
  (isRoot : V → Prop) (hz : isRoot z)

/-- The rooted boundary map of a reduced disc picture. -/
noncomputable def toMap : MapSystem Γ label inv isRoot where
  T := Cycle a.closedRotation
  w := a.paths hzw
  nonempty := a.paths_nonempty hzw
  α := (coordinates a hzw).symm.permCongr a.fullPartner
  involutive := PermutationTransport.involutive _ _ a.fullPartner_involutive
  fixed_free := PermutationTransport.fixed_free _ _ a.fullPartner_nonfixed
  genusZero := by
    rw [rotation_conjugate]
    exact MapConjugation.genusZero (coordinates a hzw).symm _ _ (a.closedRotation_genusZero hzw)
  keep _ := True
  root := some (a.rootCycle hzw)
  root_keep _ _ := trivial
  root_only _ _ := trivial
  chain c _ := a.paths_chain hzw hr c
  cyclic c _ hc := by
    have hd : c ≠ a.rootCycle hzw := fun he => hc (congrArg some he.symm)
    intro d hd' e he
    rw [List.getLast?_eq_some_getLast (a.paths_nonempty hzw c), Option.mem_some_iff] at hd'
    rw [List.head?_eq_some_head (a.paths_nonempty hzw c), Option.mem_some_iff] at he
    subst d e
    exact a.paths_closed hzw hr c hd
  root_start t ht := by
    have he : t = a.rootCycle hzw := (Option.some.inj ht).symm
    subst he
    rw [a.paths_root_begins hzw]
    exact hz
  compatible x _ _ := by
    rw [dart, dart]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact a.edge_compatible _
  reduced x _ _ := by
    rw [dart, dart]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact a.edge_reduced hr (fun d => hinv (label d)) _
  monogons := by
    have h := a.face_monogons_le hzw hr hlabel himm
    rw [rotation_conjugate]
    change (fixed ((coordinates a hzw).symm.permCongr a.fullPartner *
      (coordinates a hzw).symm.permCongr a.closedRotation)).card ≤ 1
    rw [← PermutationTransport.mul, fixed_card_conj]
    exact h
  outer_le := by simp

end RootedMap

variable {V D S₀ : Type} [Fintype V] [Fintype D] {Γ : PortGraph V D}
  {label : D → S₀ × Bool} {isRoot : V → Prop} {ε d lam : ℝ} {L : ℕ}

/-- **No reduced rooted picture** (Proposition 4.4, rooted case). -/
theorem no_reduced_rooted (pf : PatternFree Γ label WordPairing.inverseLetter isRoot ε d lam L)
    {z w : V} (hz : isRoot z) (hzw : z ≠ w) {O : Type} [Fintype O]
    (a : FinitePicture.Data (O := O) Γ label WordPairing.inverseLetter z w) : ¬a.Reduced := by
  intro hr
  let m := RootedMap.toMap a hzw hr pf.inv_ne pf.label_reverse pf.immersed isRoot hz
  apply m.key_closed pf
  · obtain ⟨c, hc⟩ := a.ordinary_boundary hzw hr pf.label_reverse pf.immersed
    exact ⟨c, trivial, fun he => hc (Option.some.inj he).symm⟩
  · intro _; trivial

/-- **Root protection** (paper Theorem B(ii)): in the cone group of a pattern-free graph, no path
from a root to a different vertex has trivial label. -/
theorem root_protected (pf : PatternFree Γ label WordPairing.inverseLetter isRoot ε d lam L)
    (R : GraphPresentation.Routes Γ) {z w : V} (hz : isRoot z) (hzw : z ≠ w)
    (p : GraphPresentation.Path Γ z w) :
    p.eval (GraphPresentation.letter Γ (GraphPresentation.roseLabel label) R) ≠ 1 := by
  intro h
  obtain ⟨O, hO, ⟨a⟩⟩ := GraphPresentation.route_picture Γ label pf.label_reverse R p hzw h
  obtain ⟨n, _, b, hb⟩ := a.exists_reduced pf.inv_involutive pf.label_reverse
  exact no_reduced_rooted pf hz hzw b hb

end Kaplansky.Exclusion
