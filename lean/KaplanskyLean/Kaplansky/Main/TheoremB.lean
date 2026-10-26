import Kaplansky.Exclusion.FreeCone
import Kaplansky.Exclusion.Rooted
import Kaplansky.Topology.ConeModel

/-!
# Theorem B for abstract pattern-free graphs (paper Theorem 1.3 `thm:C`)

If `Γ` is `(ε,d,λ)`-pattern-free at scale `L` (`Exclusion.PatternFree`), then for the cone group
`G = ConeGroup Γ label (routes Γ)` (paper equation (3.1)):

1. the cone complex is aspherical: `G` is finitely presented, torsion-free, and has a finite
   two-dimensional classifying space;
2. roots are protected: no path from a root to a different vertex has trivial label in `G`;
3. every cyclically reduced null word `w` has a reduced capped picture of cone length at most
   `16/(13ε)·|w|` (the cone-length form of `Area(w) ≤ 16/(13ε)|w|`), hence `G` is word-hyperbolic.

This is the interface fed by the random models (agents C, D); see `docs/B_INTERFACE.md`.
-/

namespace Kaplansky.Main

open OAI.TorsionFreeZeroDivisors
open PortSubdivision GraphPresentation

/-- **Theorem B.** The cone group of a pattern-free graph is finitely presented, torsion-free,
word-hyperbolic, has a finite two-dimensional classifying space, and protects its roots. -/
theorem theoremB {V D S₀ : Type} [Fintype V] [Fintype D] [DecidableEq S₀] [Finite S₀] [Nonempty D]
    {Γ : PortGraph V D} {label : D → S₀ × Bool} {isRoot : V → Prop} {ε d lam : ℝ} {L : ℕ}
    (pf : Exclusion.PatternFree Γ label WordPairing.inverseLetter isRoot ε d lam L) :
    Kaplansky.GoodHyperbolic (Exclusion.ConeGroup Γ label (routes Γ)) ∧
    ∀ {z w : V}, isRoot z → z ≠ w → ∀ p : GraphPresentation.Path Γ z w,
      p.eval (GraphPresentation.letter Γ (GraphPresentation.roseLabel label) (routes Γ)) ≠ 1 := by
  have hex : ∀ {P : Type} [Fintype P] [Nonempty P]
      (a : SphericalPicture.Data (O := P) Γ label WordPairing.inverseLetter), ¬a.Reduced :=
    fun a => Exclusion.no_reduced_sphere pf a
  obtain ⟨hfp, htf, hmod⟩ := Topology.aspherical pf.label_reverse hex
  refine ⟨⟨hfp, htf, Exclusion.wordHyperbolic_of_patternFree (routes Γ) pf, hmod⟩, ?_⟩
  intro z w hz hzw p
  exact Exclusion.root_protected pf (routes Γ) hz hzw p

variable {V D S₀ : Type} [Fintype V] [Fintype D]
  {Γ : PortGraph V D} {label : D → S₀ × Bool} {isRoot : V → Prop} {ε d lam : ℝ} {L : ℕ}

/-- **Root protection, value form.** For a root `z` and a vertex `w ≠ z` in its component, the
vertex values `g_z`, `g_w` (`GraphPresentation.value`, for any routes) are distinct. This is the
form used by the parity certificates (`Factors.sum_nonzero`). -/
theorem root_value_ne (pf : Exclusion.PatternFree Γ label WordPairing.inverseLetter isRoot ε d lam L)
    (R : Routes Γ) {z w : V} (hz : isRoot z) (hzw : z ≠ w)
    (hr : (ShortClosure.simpleGraph Γ).Reachable z w) :
    GraphPresentation.value Γ (roseLabel label) R z ≠ GraphPresentation.value Γ (roseLabel label) R w := by
  obtain ⟨q⟩ := hr
  intro he
  apply Exclusion.root_protected pf R hz hzw (GraphPresentation.Path.ofWalk q)
  rw [GraphPresentation.path_value, he, inv_mul_cancel]

/-- **Theorem B (iii), cone-length form.** Every nonempty cyclically reduced word that is trivial
in the cone group has a reduced capped picture with at most `16/(13ε)·|w|` cone occurrences. -/
theorem theoremB_coneLength
    (pf : Exclusion.PatternFree Γ label WordPairing.inverseLetter isRoot ε d lam L)
    (R : Routes Γ) (w : List (S₀ × Bool)) (hne : w ≠ []) (hcr : FreeGroup.IsCyclicallyReduced w)
    (hw : PresentedGroup.mk _ (FreeGroup.mk w) = (1 : Exclusion.ConeGroup Γ label R)) :
    ∃ (k : ℕ) (b : SphericalPicture.Data (O := Fin k) (Exclusion.plusGraph Γ w)
        (Exclusion.plusLabel label w) WordPairing.inverseLetter),
      b.Reduced ∧ (Finset.univ.filter (fun o => (b.dart o).isLeft = true)).card ≤
        16 / (13 * ε) * w.length := by
  have hε := pf.eps_pos
  have hw1 : Hyperbolic.value (Exclusion.gen Γ label R) w = 1 := by rw [Exclusion.value_mk]; exact hw
  obtain ⟨O, _, a, l, hc⟩ := Exclusion.exists_capped pf.label_reverse R w hne hw1
  obtain ⟨k, b, lb, hcb, hr⟩ := Exclusion.exists_reduced_capped Exclusion.heval pf.label_reverse hc
  refine ⟨k, b, hr, ?_⟩
  have hb := hcb.cone_bound pf hcr hr
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (by norm_num) hε)]
  nlinarith

end Kaplansky.Main
