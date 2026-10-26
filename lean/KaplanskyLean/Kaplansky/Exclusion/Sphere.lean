import Kaplansky.Exclusion.PictureMap
import Kaplansky.Exclusion.KeyEstimate

/-!
# No reduced spherical picture in a pattern-free graph

Paper Proposition 4.4, spherical case, for an arbitrary pattern-free graph: a nonempty reduced
spherical picture (`SphericalPicture.Data`, OpenAI's cone pictures with the cone collapsed) is
read as a boundary map over `Γ ⊔ ∅` with all boundaries kept, and the key estimate gives a
contradiction.
-/

namespace Kaplansky.Exclusion

open OAI.TorsionFreeZeroDivisors
open PortSubdivision

/-- The empty port graph. -/
def emptyGraph : PortGraph Empty Empty where
  origin := Empty.elim
  reverse := Empty.elim
  reverse_reverse := fun d => d.elim
  reverse_ne := fun d => d.elim

namespace SphericalLift
variable {V D A : Type} {Γ : PortGraph V D} {label : D → A} {inv : A → A}
  {O : Type} [Fintype O] (a : SphericalPicture.Data (O := O) Γ label inv)

/-- A picture over `Γ` is a picture over `Γ ⊔ ∅`. -/
def toPlus : SphericalPicture.Data (O := O) (SumPort.graph Γ emptyGraph)
    (Sum.elim label (Empty.elim : Empty → A)) inv where
  rotation := a.rotation
  partner := a.partner
  involutive := a.involutive
  fixed_free := a.fixed_free
  dart o := Sum.inl (a.dart o)
  consistent o := by
    simp only [SumPort.graph, Sum.map_inl]
    exact congrArg Sum.inl (a.consistent o)
  compatible o := by
    simp only [Sum.elim_inl]
    exact a.compatible o
  genusZero := a.genusZero

lemma toPlus_reduced (hr : a.Reduced) : (toPlus a).Reduced := by
  constructor
  · intro i h
    apply hr.1 i
    simpa [toPlus, SumPort.graph] using h
  · intro i h
    apply hr.2 i
    simpa [toPlus, SumPort.graph] using h

end SphericalLift

variable {V D A : Type} [Fintype V] [Fintype D] {Γ : PortGraph V D} {label : D → A}
  {inv : A → A} {isRoot : V → Prop} {ε d lam : ℝ} {L : ℕ}

/-- **No reduced spherical picture** (paper Proposition 4.4, spherical case). -/
theorem no_reduced_sphere (pf : PatternFree Γ label inv isRoot ε d lam L)
    {O : Type} [Fintype O] [Nonempty O] (a : SphericalPicture.Data (O := O) Γ label inv) :
    ¬a.Reduced := by
  intro hr
  classical
  let b := SphericalLift.toPlus a
  have hb : b.Reduced := SphericalLift.toPlus_reduced a hr
  let o₀ : O := Classical.choice inferInstance
  have hall : ∀ c : PermutationCycles.Cycle b.rotation, PictureMap.keepC b c = true := by
    intro c
    obtain ⟨o, rfl⟩ := PermutationCycles.cycle_surjective b.rotation c
    rw [PictureMap.keepC_cycle]
    rfl
  have houter : (Finset.univ.filter (fun c : PermutationCycles.Cycle b.rotation =>
      PictureMap.keepC b c = false)).card ≤ 1 := by
    rw [Finset.filter_false_of_mem (fun c _ => by simp [hall c])]
    simp
  let m := PictureMap.toMap b hb pf.inv_ne pf.inv_involutive pf.immersed pf.label_reverse
    (fun _ x _ _ _ => x.elim) houter isRoot (a.dart o₀)
  apply m.key_closed pf
  · exact ⟨PermutationCycles.cycle b.rotation o₀, hall _, by simp [m, PictureMap.toMap]⟩
  · intro c
    exact hall c

end Kaplansky.Exclusion
