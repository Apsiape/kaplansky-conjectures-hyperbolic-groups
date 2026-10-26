import Kaplansky.Challenge
import OAI.Algebra.GroupRing.SplitModel
import OAI.Algebra.GroupRing.ConeTorsion

/-!
# The cone complex is a finite aspherical 2-complex

Generic versions of OpenAI's `ConcreteTorsion.torsion_free` and `ConcreteModel.has_model`:
for any finite port graph `Γ` with signed labels `label : D → S₀ × Bool` and routes `R` with
idempotent base map, if there is no nonempty reduced spherical picture (`hex`), the cone group
`GraphPresentation.Group Γ (roseLabel label) R` (= `Exclusion.ConeGroup Γ label R`, paper (3.1))
is finitely presented, torsion-free and has a finite two-dimensional classifying space, in the
sense of the Challenge definitions `Kaplansky.TorsionFree` and
`Kaplansky.HasFiniteTwoDimensionalClassifyingSpace`.

OpenAI prove both through identity sequences of zero area (`ConeTorsion.total_zero`), the
split CW model `RelationModel.has_model`, and the isomorphism
`GraphConePresentation.equivalence` between the edge-route and the triangular cone presentation.

This file depends only on vendored code. It also provides the transport lemmas along `≃*` and
the (definitional) identification of the Challenge definitions with OpenAI's.
-/

namespace Kaplansky.Topology

open OAI.TorsionFreeZeroDivisors
open PortSubdivision GraphPresentation

/-! ## Transport of the Challenge definitions -/

section Transport
variable {G H : Type} [Group G] [Group H]

/-- The Challenge `TorsionFree` is OpenAI's `TorsionFree` (textually identical definitions). -/
theorem torsionFree_iff_oai : Kaplansky.TorsionFree G ↔ OAI.TorsionFreeZeroDivisors.TorsionFree G :=
  Iff.rfl

/-- The Challenge classifying-space clause is OpenAI's (textually identical definitions). -/
theorem hasModel_iff_oai : Kaplansky.HasFiniteTwoDimensionalClassifyingSpace G ↔
    OAI.TorsionFreeZeroDivisors.HasFiniteTwoDimensionalClassifyingSpace G :=
  Iff.rfl

theorem torsionFree_of_mulEquiv (e : G ≃* H) (h : Kaplansky.TorsionFree H) :
    Kaplansky.TorsionFree G := by
  intro g n hn hg
  apply e.injective
  rw [map_one]
  exact h (e g) n hn (by rw [← map_pow, hg, map_one])

theorem hasModel_of_mulEquiv (e : G ≃* H)
    (h : Kaplansky.HasFiniteTwoDimensionalClassifyingSpace H) :
    Kaplansky.HasFiniteTwoDimensionalClassifyingSpace G := by
  rcases h with ⟨X, topX, hT, hP, cw, hf, hh, h2, x, ⟨k⟩, E, topE, hE, p, hp, hps⟩
  exact ⟨X, topX, hT, hP, cw, hf, hh, h2, x, ⟨e.trans k⟩, E, topE, hE, p, hp, hps⟩

theorem finitelyPresented_of_mulEquiv (e : G ≃* H) [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented G :=
  Group.IsFinitelyPresented.equiv e.symm

end Transport

/-! ## The cone group of a graph without reduced spherical pictures -/

section Cone
variable {V D S₀ : Type} (Γ : PortGraph V D) (label : D → S₀ × Bool) (R : Routes Γ)

/-- OpenAI's cone letters are the rose labels. -/
lemma freeLetter_comp : ConeSigned.freeLetter ∘ label = roseLabel label := rfl

/-- The cone group is finitely presented. -/
theorem cone_finitelyPresented [Finite S₀] [Finite D] :
    Group.IsFinitelyPresented (GraphPresentation.Group Γ (roseLabel label) R) :=
  inferInstance

variable {Γ label}
variable (hl : ∀ d, label (Γ.reverse d) = WordPairing.inverseLetter (label d))
  (hbase : ∀ v, R.base (R.base v) = R.base v)
  (hex : ∀ {P : Type} [Fintype P] [Nonempty P]
    (a : SphericalPicture.Data (O := P) Γ label WordPairing.inverseLetter), ¬a.Reduced)

include hl hbase hex in
/-- **Torsion-freeness.** Without reduced spherical pictures the cone group is torsion-free. -/
theorem cone_torsionFree :
    Kaplansky.TorsionFree (GraphPresentation.Group Γ (roseLabel label) R) :=
  ConeTorsion.graph_torsion_free Γ R label hl hbase hex

include hl hbase hex in
/-- **Finite 2-dimensional `K(G,1)`.** Without reduced spherical pictures (and with at least one
edge) the cone complex is a finite two-dimensional classifying space of the cone group. -/
theorem cone_hasModel [Finite V] [Finite D] [Finite S₀] [Nonempty D] :
    Kaplansky.HasFiniteTwoDimensionalClassifyingSpace
      (GraphPresentation.Group Γ (roseLabel label) R) := by
  obtain ⟨d⟩ := ‹Nonempty D›
  have : Nonempty (GraphConePresentation.Edge Γ) := ⟨GraphConePresentation.edge Γ d⟩
  have hm := RelationModel.has_model (ConeArea.words Γ R label)
    (ConeTorsion.total_zero Γ R label hl hex)
  unfold RelationArea.G at hm
  rw [ConeTorsion.relations_eq _ _ _ hl] at hm
  exact hasModel_of_mulEquiv
    (GraphConePresentation.equivalence Γ (ConeSigned.freeLetter ∘ label) R
      (ConeArea.letters_reverse Γ label hl) hbase) hm

end Cone

/-! ## Canonical routes -/

section Canonical
variable {V D S₀ : Type} {Γ : PortGraph V D} {label : D → S₀ × Bool}
  (hl : ∀ d, label (Γ.reverse d) = WordPairing.inverseLetter (label d))
  (hex : ∀ {P : Type} [Fintype P] [Nonempty P]
    (a : SphericalPicture.Data (O := P) Γ label WordPairing.inverseLetter), ¬a.Reduced)

include hl hex in
/-- Torsion-freeness for the canonical routes `GraphPresentation.routes Γ`. -/
theorem torsionFree :
    Kaplansky.TorsionFree (GraphPresentation.Group Γ (roseLabel label) (routes Γ)) :=
  cone_torsionFree (routes Γ) hl (GraphConePresentation.canonical_base Γ) hex

include hl hex in
/-- The finite two-dimensional `K(G,1)` for the canonical routes. -/
theorem hasModel [Finite V] [Finite D] [Finite S₀] [Nonempty D] :
    Kaplansky.HasFiniteTwoDimensionalClassifyingSpace
      (GraphPresentation.Group Γ (roseLabel label) (routes Γ)) :=
  cone_hasModel (routes Γ) hl (GraphConePresentation.canonical_base Γ) hex

include hl hex in
/-- Finitely presented, torsion-free, finite two-dimensional `K(G,1)`: the three topological
clauses of `Kaplansky.GoodHyperbolic`, for the canonical routes. -/
theorem aspherical [Finite V] [Finite D] [Finite S₀] [Nonempty D] :
    Group.IsFinitelyPresented (GraphPresentation.Group Γ (roseLabel label) (routes Γ)) ∧
    Kaplansky.TorsionFree (GraphPresentation.Group Γ (roseLabel label) (routes Γ)) ∧
    Kaplansky.HasFiniteTwoDimensionalClassifyingSpace
      (GraphPresentation.Group Γ (roseLabel label) (routes Γ)) :=
  ⟨cone_finitelyPresented Γ label (routes Γ), torsionFree hl hex, hasModel hl hex⟩

end Canonical

end Kaplansky.Topology
