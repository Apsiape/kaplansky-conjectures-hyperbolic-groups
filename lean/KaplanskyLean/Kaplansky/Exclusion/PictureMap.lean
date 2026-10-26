import Kaplansky.Exclusion.Segments
import OAI.Algebra.GroupRing.ConePicture

/-!
# From a reduced spherical picture over `Γ ⊔ Ω` to a boundary map

A spherical picture over the disjoint union `Γ ⊔ Ω` of the graph `Γ` and an *outer graph* `Ω`
(for a free outer disk, `Ω` is the cycle reading the outer word; for a spherical picture, `Ω` is
empty) is read as a `MapSystem` over `Γ`: its boundary circles are the cycles of the rotation;
those made of `Γ`-darts are the graph boundaries, the others are discarded.

The kept length is the number of `Γ`-occurrences, the outer length the number of
`Ω`-occurrences.
-/

namespace Kaplansky.Exclusion

open OAI.TorsionFreeZeroDivisors
open PortSubdivision ComparedBlocks BlockAlignment PermutationCycles

namespace PictureMap
open scoped Classical BigOperators

variable {V D A VΩ DΩ : Type} [Fintype D]
  {Γ : PortGraph V D} {Ω : PortGraph VΩ DΩ} {label : D → A} {labelΩ : DΩ → A} {inv : A → A}
  {O : Type} [Fintype O]
  (a : SphericalPicture.Data (O := O) (SumPort.graph Γ Ω) (Sum.elim label labelΩ) inv)

lemma isLeft_rotation (o : O) : (a.dart (a.rotation o)).isLeft = (a.dart o).isLeft := by
  have h := a.consistent o
  cases hd : a.dart o <;> cases hd' : a.dart (a.rotation o) <;>
    simp_all [SumPort.graph]

/-- A boundary circle is a graph boundary when it consists of `Γ`-darts. -/
def keepC (c : Cycle a.rotation) : Bool :=
  PermutationCycles.lift a.rotation (fun o => (a.dart o).isLeft) (isLeft_rotation a) c

lemma keepC_cycle (o : O) : keepC a (cycle a.rotation o) = (a.dart o).isLeft := rfl

/-- Projection of darts to `Γ`, with a default value for the discarded `Ω`-darts. -/
def proj (d₀ : D) : D ⊕ DΩ → D := Sum.elim id (fun _ => d₀)

noncomputable def words (d₀ : D) (c : Cycle a.rotation) : List D := (a.occurrences c).map (proj d₀ ∘ a.dart)

lemma words_length (d₀ : D) (c : Cycle a.rotation) :
    (words a d₀ c).length = (a.occurrences c).length := List.length_map _

lemma words_nonempty (d₀ : D) (c : Cycle a.rotation) : words a d₀ c ≠ [] := by
  intro h
  exact a.occurrences_nonempty c (List.map_eq_nil_iff.mp h)

/-- Coordinates of boundary positions. -/
noncomputable def coords (d₀ : D) : Position (fun c => (words a d₀ c).length) ≃ O :=
  (WordPositions.fin _).trans ((Equiv.sigmaCongrRight fun c => finCongr (words_length a d₀ c)).trans
    (CycleLists.coordinates a.rotation a.boundaryRep a.boundaryRep_cycle))

lemma coords_fin (d₀ : D) (c : Cycle a.rotation) (i : Fin (words a d₀ c).length) :
    coords a d₀ ((WordPositions.fin _).symm ⟨c, i⟩) =
      (a.occurrences c)[i.val]'(by rw [← words_length a d₀ c]; exact i.isLt) := by
  simp only [coords, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

lemma coords_dart (d₀ : D) (x : Position (fun c => (words a d₀ c).length)) :
    RawDecomposition.dart (words a d₀) x = proj d₀ (a.dart (coords a d₀ x)) := by
  rw [← (WordPositions.fin _).symm_apply_apply x, WordPositions.dart_fin]
  generalize WordPositions.fin _ x = y
  rcases y with ⟨c, i⟩
  rw [coords_fin]
  exact List.getElem_map _

lemma coords_cycle (d₀ : D) (x : Position (fun c => (words a d₀ c).length)) :
    cycle a.rotation (coords a d₀ x) = x.1 := by
  rw [← (WordPositions.fin _).symm_apply_apply x]
  generalize hy : WordPositions.fin _ x = y
  rcases y with ⟨c, i⟩
  have hx : ((WordPositions.fin _).symm ⟨c, i⟩ : Position (fun c => (words a d₀ c).length)).1 = c := rfl
  rw [hx, coords_fin]
  exact CycleLists.atIndex_cycle a.rotation a.boundaryRep a.boundaryRep_cycle
    ⟨c, finCongr (words_length a d₀ c) i⟩

lemma coords_rotation (d₀ : D) (x : Position (fun c => (words a d₀ c).length)) :
    coords a d₀ (BoundaryRotation.perm (fun c => (words a d₀ c).length) x) =
      a.rotation (coords a d₀ x) := by
  generalize he : (WordPositions.fin (fun c => (words a d₀ c).length)) x = q
  have hp : x = (WordPositions.fin _).symm q := by rw [← he, Equiv.symm_apply_apply]
  rw [hp]
  rcases q with ⟨c, i⟩
  rw [BoundaryRotation.apply_fin, coords_fin, coords_fin]
  have hh := CycleLists.orbit_rotate a.rotation (a.boundaryRep c)
    (Fin.cast (words_length a d₀ c) i)
  have key : ∀ {m n : ℕ} (h : m = n) (j : Fin m),
      (finRotate m j).val = (finRotate n (Fin.cast h j)).val := by
    intro m n h j
    subst h
    rfl
  have hv : (finRotate (words a d₀ c).length i).val =
      (finRotate (CycleLists.orbit a.rotation (a.boundaryRep c)).length
        (Fin.cast (words_length a d₀ c) i)).val :=
    key (words_length a d₀ c) i
  simp only [hv]
  exact hh

lemma rotation_conjugate (d₀ : D) :
    BoundaryRotation.perm (fun c => (words a d₀ c).length) =
      (coords a d₀).symm.permCongr a.rotation := by
  apply Equiv.ext
  intro p
  apply (coords a d₀).injective
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact coords_rotation a d₀ p

lemma isLeft_of_keep {o : O} (h : keepC a (cycle a.rotation o) = true) : ∃ d, a.dart o = Sum.inl d := by
  rw [keepC_cycle] at h
  cases hd : a.dart o with
  | inl d => exact ⟨d, rfl⟩
  | inr d => rw [hd] at h; simp at h

lemma dart_of_keep (d₀ : D) {o : O} (h : keepC a (cycle a.rotation o) = true) :
    a.dart o = Sum.inl (proj d₀ (a.dart o)) := by
  obtain ⟨d, hd⟩ := isLeft_of_keep a h
  rw [hd]; rfl

variable (hr : a.Reduced)

include hr in
lemma step_of_keep (d₀ : D) {o : O} (h : keepC a (cycle a.rotation o) = true) :
    WeightedMoore.PortWalk.step Γ.origin Γ.reverse (proj d₀ (a.dart o))
      (proj d₀ (a.dart (a.rotation o))) := by
  have h' : keepC a (cycle a.rotation (a.rotation o)) = true := by
    rw [cycle_apply]; exact h
  have h1 := dart_of_keep a d₀ h
  have h2 := dart_of_keep a d₀ h'
  have hc := a.consistent o
  have hb := hr.2 o
  rw [h1, h2] at hc hb
  refine ⟨?_, ?_⟩
  · simpa [SumPort.graph] using hc
  · intro he
    apply hb
    rw [he]
    try rfl

variable (hinv : ∀ x, inv x ≠ x) (hinvol : Function.Involutive inv)
  (himm : ∀ e e', Γ.origin e = Γ.origin e' → label e = label e' → e = e')
  (hlabel : ∀ e, label (Γ.reverse e) = inv (label e))
  (hmonoΩ : ∀ o x y, a.dart o = Sum.inr x → a.dart (a.rotation o) = Sum.inr y →
    labelΩ y ≠ inv (labelΩ x))
  (houter : (Finset.univ.filter (fun c : Cycle a.rotation => keepC a c = false)).card ≤ 1)
  (isRoot : V → Prop) (d₀ : D)

include hr in
lemma chain_of_keep (c : Cycle a.rotation) (hc : keepC a c = true) :
    (words a d₀ c).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse) := by
  rw [words, List.isChain_map, List.isChain_iff_getElem]
  intro i hi
  have hcyc : cycle a.rotation ((a.occurrences c)[i]) = c := by
    have hm : (a.occurrences c)[i] ∈ CycleLists.orbit a.rotation (a.boundaryRep c) := List.getElem_mem _
    exact ((cycle_eq a.rotation).mpr ((CycleLists.mem_orbit a.rotation).mp hm)).symm.trans
      (a.boundaryRep_cycle c)
  have hk : keepC a (cycle a.rotation ((a.occurrences c)[i])) = true := by rw [hcyc]; exact hc
  have hs := step_of_keep a hr d₀ hk
  rw [a.occurrences_succ c i hi] at hs
  exact hs

/-- The boundary map of the picture. -/
noncomputable def toMap : MapSystem Γ label inv isRoot where
  T := Cycle a.rotation
  w := words a d₀
  nonempty := words_nonempty a d₀
  α := (coords a d₀).symm.permCongr a.partner
  involutive := PermutationTransport.involutive _ _ a.involutive
  fixed_free := PermutationTransport.fixed_free _ _ a.fixed_free
  genusZero := by
    rw [rotation_conjugate]
    exact MapConjugation.genusZero (coords a d₀).symm _ _ a.genusZero
  keep c := keepC a c = true
  root := none
  root_keep := by simp
  root_only := by simp
  chain := chain_of_keep a hr d₀
  cyclic := by
    intro c hc _
    intro x hx y hy
    rw [List.getLast?_eq_some_getLast (words_nonempty a d₀ c), Option.mem_some_iff] at hx
    rw [List.head?_eq_some_head (words_nonempty a d₀ c), Option.mem_some_iff] at hy
    subst hx hy
    have hl := a.occurrences_last c
    have hcyc : cycle a.rotation ((a.occurrences c).getLast (a.occurrences_nonempty c)) = c := by
      have hm : (a.occurrences c).getLast (a.occurrences_nonempty c) ∈
          CycleLists.orbit a.rotation (a.boundaryRep c) := List.getLast_mem _
      exact ((cycle_eq a.rotation).mpr ((CycleLists.mem_orbit a.rotation).mp hm)).symm.trans
        (a.boundaryRep_cycle c)
    have hk : keepC a (cycle a.rotation ((a.occurrences c).getLast (a.occurrences_nonempty c))) =
        true := by rw [hcyc]; exact hc
    have hs := step_of_keep a hr d₀ hk
    rw [hl] at hs
    simpa only [words, List.getLast_map, List.head_map, Function.comp_apply] using hs
  root_start := by simp
  compatible := by
    intro x hx hax
    rw [coords_dart, coords_dart]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    have h1 : keepC a (cycle a.rotation (coords a d₀ x)) = true := by
      rw [coords_cycle]; exact hx
    have h2 : keepC a (cycle a.rotation (a.partner (coords a d₀ x))) = true := by
      have := coords_cycle a d₀ ((coords a d₀).symm (a.partner (coords a d₀ x)))
      rw [Equiv.apply_symm_apply] at this
      rw [this]; exact hax
    have hc := a.compatible (coords a d₀ x)
    rw [dart_of_keep a d₀ h1, dart_of_keep a d₀ h2] at hc
    simpa using hc
  reduced := by
    intro x hx hax
    rw [coords_dart, coords_dart]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    have h1 : keepC a (cycle a.rotation (coords a d₀ x)) = true := by
      rw [coords_cycle]; exact hx
    have h2 : keepC a (cycle a.rotation (a.partner (coords a d₀ x))) = true := by
      have := coords_cycle a d₀ ((coords a d₀).symm (a.partner (coords a d₀ x)))
      rw [Equiv.apply_symm_apply] at this
      rw [this]; exact hax
    have hc := a.compatible (coords a d₀ x)
    have hb := hr.1 (coords a d₀ x)
    rw [dart_of_keep a d₀ h1, dart_of_keep a d₀ h2] at hc hb
    simp only [Sum.elim_inl] at hc
    constructor
    · intro he
      rw [← he] at hc
      exact hinv _ hc.symm
    · intro he
      apply hb
      rw [he]
      simp [SumPort.graph]
  monogons := by
    apply le_of_eq_of_le _ (Nat.zero_le 1)
    rw [Finset.card_eq_zero]
    ext x
    simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro hx
    -- a monogon: the partner of the next occurrence is the occurrence itself
    have h1 : (coords a d₀).symm (a.partner (coords a d₀
        (BoundaryRotation.perm (fun c => (words a d₀ c).length) x))) = x := hx
    rw [coords_rotation] at h1
    have hx' : a.partner (a.rotation (coords a d₀ x)) = coords a d₀ x := by
      have h2 := congrArg (coords a d₀) h1
      rwa [Equiv.apply_symm_apply] at h2
    set o := coords a d₀ x
    have hc := a.compatible (a.rotation o)
    rw [hx'] at hc
    cases hd : a.dart o with
    | inl d =>
      have hk : keepC a (cycle a.rotation o) = true := by simp [keepC_cycle, hd]
      have hk' : keepC a (cycle a.rotation (a.rotation o)) = true := by rw [cycle_apply]; exact hk
      obtain ⟨e, he⟩ := isLeft_of_keep a hk'
      rw [hd, he] at hc
      simp only [Sum.elim_inl] at hc
      -- `label d = inv (label e)`, so `label e = label (reverse d)` and `e = reverse d`
      have hcons := a.consistent o
      rw [hd, he] at hcons
      have horig : Γ.origin (Γ.reverse d) = Γ.origin e := by simpa [SumPort.graph] using hcons
      have hlab : label (Γ.reverse d) = label e := by
        rw [hlabel, hc, hinvol]
      have hee : Γ.reverse d = e := himm _ _ horig hlab
      have hb := hr.2 o
      rw [hd, he, ← hee] at hb
      exact hb rfl
    | inr y =>
      have hk : keepC a (cycle a.rotation o) = false := by simp [keepC_cycle, hd]
      have hk' : keepC a (cycle a.rotation (a.rotation o)) = false := by rw [cycle_apply]; exact hk
      rw [keepC_cycle] at hk'
      cases he : a.dart (a.rotation o) with
      | inl e => rw [he] at hk'; simp at hk'
      | inr z =>
        rw [hd, he] at hc
        simp only [Sum.elim_inr] at hc
        apply hmonoΩ o y z hd he
        rw [hc, hinvol]
  outer_le := by simpa using houter

lemma toMap_keptLength :
    (toMap a hr hinv hinvol himm hlabel hmonoΩ houter isRoot d₀).keptLength =
      (Finset.univ.filter (fun o : O => (a.dart o).isLeft = true)).card := by
  unfold MapSystem.keptLength
  rw [← MapSystem.positions_filter_card, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr ((coords a d₀).subtypeEquiv (fun x => by
    show keepC a x.1 = true ↔ _
    rw [← keepC_cycle, coords_cycle]))

lemma toMap_outerLength :
    (toMap a hr hinv hinvol himm hlabel hmonoΩ houter isRoot d₀).outerLength =
      (Finset.univ.filter (fun o : O => ¬(a.dart o).isLeft = true)).card := by
  unfold MapSystem.outerLength
  rw [← MapSystem.positions_filter_card, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr ((coords a d₀).subtypeEquiv (fun x => by
    show ¬keepC a x.1 = true ↔ _
    rw [← keepC_cycle, coords_cycle]))

end PictureMap

end Kaplansky.Exclusion
