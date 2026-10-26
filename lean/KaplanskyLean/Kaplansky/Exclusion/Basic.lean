import OAI.Algebra.GroupRing.ClosedWords

/-!
# Generic path systems and pattern-free graphs

OpenAI's `SampleGraph.PathSystem` and `SampleGraph.BoundedSystem` (vendored, Result 196) are
stated for the sampled graph `graph rep r`. This file re-instantiates them for an arbitrary finite
port graph `Γ` with labels `label : D → A`, an involution `inv` on the alphabet, and a set of root
vertices `isRoot`. The fields are copied verbatim, except that

* the two roots `x, y` of the model are replaced by the predicate `isRoot`;
* the scale `L` and the unpaired proportion `ε` are parameters (OpenAI hard-codes
  `L (size rep)` and `ε = StageFusion.epsilon (1/600) 256`).

`PatternFree` is paper Definition 3.3 (`def:patternfree`).
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.Exclusion

noncomputable section

open OAI.TorsionFreeZeroDivisors
open PortSubdivision ComparedBlocks BlockAlignment
open scoped Classical

section Systems
variable {V D A : Type} [Fintype D] (Γ : PortGraph V D) (label : D → A) (inv : A → A)
  (isRoot : V → Prop)

/-- Generic version of `SampleGraph.PathSystem`: a finite family of immersed paths in `Γ`, all
closed and cyclically immersed except possibly one root path, with interval comparisons
satisfying the reduction condition. -/
structure GPathSystem where
  P : Type
  E : Type
  [fP : Fintype P]
  [fE : Fintype E]
  paths : P → List D
  nonempty : ∀ p, paths p ≠ []
  root : Option P
  path_chain : ∀ p, (paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse)
  cyclic_chain : ∀ p, StageRoot.cyclic root p = true →
    ∀ᵉ (x ∈ (paths p).getLast?) (y ∈ (paths p).head?),
      WeightedMoore.PortWalk.step Γ.origin Γ.reverse x y
  comparisons : Comparisons (E := E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e, comparisons.lo e = lower e
  upper_eq : ∀ e, comparisons.hi e = upper e
  lower_le : ∀ e, lower e ≤ upper e
  upper_le : ∀ e, upper e ≤ (paths (comparisons.source e)).length
  reduced : ∀ x e, comparisons.side x = some e →
    RawDecomposition.dart paths x ≠ RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x ≠ Γ.reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  root_start : ∀ p, root = some p → isRoot (Γ.origin ((paths p).head (nonempty p)))
  compatible : ∀ p e, comparisons.side p = some e → label (RawDecomposition.dart paths p) =
    if comparisons.reverse e then inv (label (RawDecomposition.dart paths (comparisons.pairing.partner p)))
    else label (RawDecomposition.dart paths (comparisons.pairing.partner p))

attribute [instance] GPathSystem.fP GPathSystem.fE

/-- Generic version of `SampleGraph.BoundedSystem`: a path system with at most `K` paths, at most
`I` oriented interval sides, total length in `[L, Bnd·L]` and at most an `ε`-proportion of unpaired
occurrences. -/
structure GBoundedSystem (Bnd K I L : ℕ) (ε : ℝ) where
  P : Type
  E : Type
  [fP : Fintype P]
  [fE : Fintype E]
  paths : P → List D
  nonempty : ∀ p, paths p ≠ []
  root : Option P
  path_bound : Fintype.card P ≤ K
  comparison_bound : Fintype.card E ≤ I
  path_chain : ∀ p, (paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse)
  cyclic_chain : ∀ p, StageRoot.cyclic root p = true →
    ∀ᵉ (x ∈ (paths p).getLast?) (y ∈ (paths p).head?),
      WeightedMoore.PortWalk.step Γ.origin Γ.reverse x y
  length_le : (∑ p, (paths p).length : ℕ) ≤ Bnd * L
  length_ge : L ≤ (∑ p, (paths p).length : ℕ)
  comparisons : Comparisons (E := E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e, comparisons.lo e = lower e
  upper_eq : ∀ e, comparisons.hi e = upper e
  lower_le : ∀ e, lower e ≤ upper e
  upper_le : ∀ e, upper e ≤ (paths (comparisons.source e)).length
  reduced : ∀ x e, comparisons.side x = some e →
    RawDecomposition.dart paths x ≠ RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x ≠ Γ.reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x = x)).card : ℝ) ≤
    ε * (∑ p, (paths p).length : ℕ)
  root_start : ∀ p, root = some p → isRoot (Γ.origin ((paths p).head (nonempty p)))
  compatible : ∀ p e, comparisons.side p = some e → label (RawDecomposition.dart paths p) =
    if comparisons.reverse e then inv (label (RawDecomposition.dart paths (comparisons.pairing.partner p)))
    else label (RawDecomposition.dart paths (comparisons.pairing.partner p))

attribute [instance] GBoundedSystem.fP GBoundedSystem.fE

namespace GPathSystem
variable {Γ label inv isRoot}
variable (s : GPathSystem Γ label inv isRoot) (keep : s.P → Prop)

/-- Drop the paths outside `keep`; their partners become unpaired. -/
abbrev restrict : GPathSystem Γ label inv isRoot where
  P := {p // keep p}
  E := {e // RestrictComparisons.Active s.comparisons keep e}
  fP := inferInstance
  fE := inferInstance
  paths := fun p => s.paths p.val
  nonempty := fun p => s.nonempty p.val
  root := RestrictComparisons.rootPath s.root keep
  path_chain := fun p => s.path_chain p.val
  cyclic_chain := by
    intro p hp
    exact s.cyclic_chain p.val ((RestrictComparisons.rootPath_cyclic s.root keep p) ▸ hp)
  comparisons := RestrictComparisons.comparisons s.comparisons keep
  lower := fun e => s.lower e.val
  upper := fun e => s.upper e.val
  lower_eq := fun e => s.lower_eq e.val
  upper_eq := fun e => s.upper_eq e.val
  lower_le := fun e => s.lower_le e.val
  upper_le := fun e => s.upper_le e.val
  reduced := by
    intro p e he
    have hh := s.reduced (RestrictComparisons.embed keep p) e.val
      ((RestrictComparisons.side_some s.comparisons keep p e).mp he)
    rw [← RestrictComparisons.partner_image_of_side s.comparisons keep he] at hh
    exact hh
  root_start := by
    intro p hp
    exact s.root_start p.val ((RestrictComparisons.rootPath_some s.root keep p).mp hp)
  compatible := by
    intro p e he
    have hh := s.compatible (RestrictComparisons.embed keep p) e.val
      ((RestrictComparisons.side_some s.comparisons keep p e).mp he)
    rw [← RestrictComparisons.partner_image_of_side s.comparisons keep he] at hh
    exact hh

end GPathSystem
end Systems

/-! ## The constants of the paper, equation (3.2) -/

/-- `D₀ = ⌈d + 4λ + 8⌉`. -/
noncomputable def closureConst (d lam : ℝ) : ℕ := ⌈d + 4 * lam + 8⌉₊

/-- `I = ⌈192·C⌉ = 192·C` interval pairs. -/
noncomputable def pairs (ε : ℝ) (D : ℕ) : ℕ := 192 * PlanarParameters.C ε D

lemma two_pairs (ε : ℝ) (D : ℕ) : 2 * pairs ε D = PlanarParameters.sides ε D := by
  unfold pairs PlanarParameters.sides PlanarParameters.C₂
  ring

section PatternFree
variable {V D A : Type} [Fintype V] [Fintype D]

/-- **Pattern-free graphs** (paper Definition 3.3, `def:patternfree`), at scale `L` with parameters
`ε ∈ (0,1]`, `d`, `λ`. The constants `K₀ = PlanarParameters.K ε D₀`, `C = PlanarParameters.C ε D₀`
and `I = 192·C` (interval pairs, i.e. `2I` oriented sides) are those of equation (3.2) with
`D₀ = ⌈d + 4λ + 8⌉`. Deviation from the paper: the degree bound is `7` (as required by OpenAI's
closure lemma) instead of `5`. -/
structure PatternFree (Γ : PortGraph V D) (label : D → A) (inv : A → A) (isRoot : V → Prop)
    (ε d lam : ℝ) (L : ℕ) : Prop where
  /-- signed alphabet -/
  inv_involutive : Function.Involutive inv
  inv_ne : ∀ a, inv a ≠ a
  /-- labelled graph: reversed edges carry inverse labels -/
  label_reverse : ∀ e, label (Γ.reverse e) = inv (label e)
  /-- immersed: the labels of the edges leaving a vertex are distinct -/
  immersed : ∀ e e', Γ.origin e = Γ.origin e' → label e = label e' → e = e'
  eps_pos : 0 < ε
  eps_le : ε ≤ 1
  one_le_d : 1 ≤ d
  one_le_lam : 1 ≤ lam
  scale : 3 ≤ L
  /-- (P1) every vertex has degree at least 7 -/
  degree : ∀ v, 7 ≤ (Finset.univ.filter (fun e : D => Γ.origin e = v)).card
  /-- (P1) girth at least `L`: every non-empty cyclically immersed closed path has length `≥ L` -/
  girth : ∀ p : List D, p ≠ [] → p.IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse) →
    (∀ᵉ (x ∈ p.getLast?) (y ∈ p.head?), WeightedMoore.PortWalk.step Γ.origin Γ.reverse x y) →
    L ≤ p.length
  /-- (P2) every component has diameter at most `d·L` -/
  diameter : ∀ a b, (ShortClosure.simpleGraph Γ).Reachable a b →
    ((ShortClosure.simpleGraph Γ).dist a b : ℝ) ≤ d * L
  /-- (P2) `log₂ |V| ≤ λ L` -/
  size : Real.logb 2 (Fintype.card V) ≤ lam * L
  /-- (P3) no bounded nearly-paired path system -/
  avoid : IsEmpty (GBoundedSystem Γ label inv isRoot
    (PlanarParameters.C ε (closureConst d lam)) (PlanarParameters.K ε (closureConst d lam))
    (2 * pairs ε (closureConst d lam)) L ε)

/-- (P1) girth from OpenAI's form of the girth condition, `3L ≤ egirth` of the threefold
subdivision (e.g. `SampleGraph.girth`). -/
theorem girth_of_egirth (Γ : PortGraph V D) (L : ℕ) (hg : (3 * L : ℕ) ≤ Γ.subdivision.egirth) :
    ∀ p : List D, p ≠ [] → p.IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse) →
      (∀ᵉ (x ∈ p.getLast?) (y ∈ p.head?), WeightedMoore.PortWalk.step Γ.origin Γ.reverse x y) →
      L ≤ p.length :=
  fun _ hp hch hc => (ShortClosure.of_cyclic Γ hp hch hc).length_ge Γ hp L hg

end PatternFree

end

end Kaplansky.Exclusion
