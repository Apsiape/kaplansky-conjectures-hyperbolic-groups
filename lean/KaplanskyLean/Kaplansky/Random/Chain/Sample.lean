import Kaplansky.Random.Chain.Diameter
import OAI.Algebra.GroupRing.BoundedSystem

/-!
# Fork of `RawDecomposition.lean` (`RawSourcePattern`), `SupportedImage.lean` (`AmbientPattern`),
`WeightedGirth.lean` (`SampleGraph`) and `BoundedSystem.lean` for an abstract model

The final existence theorem `SampleGraph.exists_avoiding`: for every model `M`, all bounds
`Bnd K I`, all large `m` and all roots `x ∈ A`, `y ∈ B`, some girth-conditioned outcome has
component diameters at most `D₀·L` and carries no bounded nearly-paired path system.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

namespace RawSourcePattern
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity ActualPatternEvent

/-- A literal bounded family of immersed paths at scale `Lsc` with threshold `ε`. -/
structure Data (B K I Lsc : ℕ) (ε : ℝ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  no_isolated : Function.Surjective graph.origin
  side : V → Bool
  side_edge : ∀ d, side (graph.origin (graph.reverse d)) = side (graph.origin d)
  paths : P → List D
  nonempty : ∀ p, paths p ≠ []
  root : Option P
  path_bound : Fintype.card P ≤ K
  comparison_bound : Fintype.card E ≤ I
  image : ∀ d, ∃ p, d ∈ paths p ∨ graph.reverse d ∈ paths p
  path_chain : ∀ p, (paths p).IsChain (WeightedMoore.PortWalk.step graph.origin graph.reverse)
  cyclic_chain : ∀ p, StageRoot.cyclic root p = true →
    ∀ᵉ (x ∈ (paths p).getLast?) (y ∈ (paths p).head?),
      WeightedMoore.PortWalk.step graph.origin graph.reverse x y
  girth : ∀ a (c : graph.subdivision.Walk a a), c.IsCycle →
    (Lsc : ℝ) ≤ WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1 : ℝ))) c
  length_le : (∑ p, (paths p).length : ℕ) ≤ B * Lsc
  length_ge : Lsc ≤ (∑ p, (paths p).length : ℕ)
  comparisons : Comparisons (E := E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e, comparisons.lo e = lower e
  upper_eq : ∀ e, comparisons.hi e = upper e
  lower_le : ∀ e, lower e ≤ upper e
  upper_le : ∀ e, upper e ≤ (paths (comparisons.source e)).length
  reduced : ∀ x e, comparisons.side x = some e →
    RawDecomposition.dart paths x ≠ RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x ≠ graph.reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x = x)).card : ℝ) ≤
    ε * (∑ p, (paths p).length : ℕ)
attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {B K I Lsc : ℕ} {ε : ℝ} (a : Data B K I Lsc ε)
abbrev vertices := ActualComplexity.endpoints a.graph a.paths a.nonempty
abbrev mark := MarkedChainBound.marks a.graph a.vertices
abbrev degree_two := marks_degree_two a.graph a.vertices
abbrev decomposed := RawDecomposition.paths a.graph a.paths a.nonempty a.path_chain
abbrev decomposed_nonempty := RawDecomposition.nonempty a.graph a.paths a.nonempty a.path_chain
abbrev lengths_eq := RawDecomposition.lengths_eq a.graph a.paths a.nonempty a.path_chain
abbrev comparison := ComparisonGeometry.cast a.lengths_eq.symm a.comparisons
abbrev iso := ComparisonGeometry.castBackIso a.lengths_eq a.comparisons
abbrev position := RawDecomposition.position a.graph a.paths a.nonempty a.path_chain

lemma expands (p : a.P) : (a.decomposed p).flatMap (word a.graph a.mark a.degree_two) = a.paths p :=
  RawDecomposition.expands a.graph a.paths a.nonempty a.path_chain p
lemma length_eq (p : a.P) : pathLength (chunks a.graph a.mark a.degree_two a.decomposed)
    (chunkLength a.graph a.mark a.degree_two a.decomposed) p = (a.paths p).length :=
  RawDecomposition.length_eq a.graph a.paths a.nonempty a.path_chain p
lemma dart_eq (x : Position (pathLength (chunks a.graph a.mark a.degree_two a.decomposed)
    (chunkLength a.graph a.mark a.degree_two a.decomposed))) :
    originalDart a.graph a.mark a.degree_two a.decomposed x =
      RawDecomposition.dart a.paths (a.position x) :=
  RawDecomposition.dart_eq a.graph a.paths a.nonempty a.path_chain x
lemma position_iso : a.position = ComparisonGeometry.position a.iso.path a.iso.length_eq := rfl

def suppressed : SourcePattern.Data B K I Lsc ε where
  V := a.V
  D := a.D
  P := a.P
  E := a.E
  graph := a.graph
  vertices := a.vertices
  vertices_bound := (ActualComplexity.endpoints_card a.graph a.paths a.nonempty).trans
    (Nat.mul_le_mul_left 2 a.path_bound)
  no_isolated := a.no_isolated
  side := a.side
  side_edge := a.side_edge
  paths := a.decomposed
  nonempty := a.decomposed_nonempty
  root := a.root
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  image := by
    intro d
    simpa only [expands] using a.image d
  path_chain := by simpa only [expands] using a.path_chain
  cyclic_chain := by simpa only [expands] using a.cyclic_chain
  girth := a.girth
  length_le := by simpa only [expands] using a.length_le
  length_ge := by simpa only [expands] using a.length_ge
  comparisons := a.comparison
  lower := a.lower
  upper := a.upper
  lower_eq e := (a.iso.lo_eq e).trans (a.lower_eq e)
  upper_eq e := (a.iso.hi_eq e).trans (a.upper_eq e)
  lower_le := a.lower_le
  upper_le e := by
    rw [a.length_eq]
    have hs : a.comparison.source e = a.comparisons.source e := a.iso.source_eq e
    rw [hs]
    exact a.upper_le e
  reduced := by
    intro x e he
    have hh := a.reduced (a.position x) e ((a.iso.side_some x e).mpr he)
    rw [a.dart_eq, a.dart_eq, position_iso, a.iso.partner_eq]
    exact hh
  unpaired_le := by
    rw [a.iso.unpaired]
    simpa only [expands] using a.unpaired_le

variable (M : Model)

/-- The realization event of a raw pattern in the sample of a model. -/
def event (mm : ℕ) (x : M.SA.V mm) (y : M.SB.V mm) (r : Match M mm) : Prop :=
  ∃ label : a.D → M.α,
    (∀ d, label (a.graph.reverse d) = M.inv (label d)) ∧
    (∀ d e, a.graph.origin d = a.graph.origin e → label d = label e → d = e) ∧
    (∀ p e, a.comparisons.side p = some e → label (RawDecomposition.dart a.paths p) =
      if a.comparisons.reverse e then
        M.inv (label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p)))
      else label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p))) ∧
    CEmb (SideRestriction.graph a.graph a.side a.side_edge true) (fun d => label d.val)
      (M.SA.col mm) (M.SA.out mm)
      (RootPins.pin (SidePins.root a.side
        (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) true) x)
      (cbar M.inv M.SA.flip) r.1 ∧
    CEmb (SideRestriction.graph a.graph a.side a.side_edge false) (fun d => label d.val)
      (M.SB.col mm) (M.SB.out mm)
      (RootPins.pin (SidePins.root a.side
        (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) false) y)
      (cbar M.inv M.SB.flip) r.2

lemma suppressed_event (mm : ℕ) (x : M.SA.V mm) (y : M.SB.V mm) (r : Match M mm)
    (h : a.event M mm x y r) :
    OriginalPattern.Realized M a.graph a.mark a.degree_two a.side a.side_edge a.decomposed
      a.decomposed_nonempty a.root mm x y a.comparison r := by
  rcases h with ⟨label, hl, hn, hc, ha, hb⟩
  refine ⟨label, hl, hn, ?_, ?_, ?_⟩
  · intro p e he
    have hh := hc (a.position p) e ((a.iso.side_some p e).mpr he)
    rw [a.dart_eq, a.dart_eq, position_iso, a.iso.partner_eq, a.iso.reverse_eq]
    exact hh
  · simpa only [ActualPatternEvent.sourcePinA, RawDecomposition.source_eq] using ha
  · simpa only [ActualPatternEvent.sourcePinB, RawDecomposition.source_eq] using hb

end Data
end RawSourcePattern

namespace GraphSample
open scoped Classical
open ActualPatternEvent

/-- Bounded-pattern exclusion for arbitrary literal immersed path systems, together with the
diameter event. -/
theorem raw_with_diameter (M : Model) (B K I : ℕ) (hK : 0 < K) (hI : 0 < I) :
    ∀ᶠ mm in atTop, ∀ (x : M.SA.V mm) (y : M.SB.V mm),
      ∃ r ∈ samples M mm, Diameters M mm r ∧
        ∀ a : RawSourcePattern.Data B K I (M.L mm) M.ε, ¬a.event M mm x y r := by
  have hT : 0 < OAI.TorsionFreeZeroDivisors.SourcePattern.T B K :=
    Nat.mul_pos (OAI.TorsionFreeZeroDivisors.SourcePattern.R_pos B K) (by omega)
  filter_upwards [bounded_with_diameter M (OAI.TorsionFreeZeroDivisors.SourcePattern.R B K) K
    (OAI.TorsionFreeZeroDivisors.SourcePattern.T B K) I B
    (OAI.TorsionFreeZeroDivisors.SourcePattern.R B K)
    (OAI.TorsionFreeZeroDivisors.SourcePattern.T B K)
    (I * (OAI.TorsionFreeZeroDivisors.SourcePattern.T B K) ^ 2)
    (OAI.TorsionFreeZeroDivisors.SourcePattern.R_pos B K) hK hI hT,
    M.L_tendsto.eventually (eventually_ge_atTop 1)] with mm hr hL
  intro x y
  obtain ⟨r, hs, hd, ha⟩ := hr x y
  refine ⟨r, hs, hd, fun a he => ?_⟩
  exact ha (a.suppressed.bounded (by omega)) (a.suppressed.bounded_good (by omega))
    (a.suppressed_event M mm x y r he)

end GraphSample

namespace SupportedImage
open scoped Classical
open PortSubdivision

theorem cemb {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D) (Q : Finset D)
    (hQ : CoreStripping.Symmetric Γ Q)
    (side : V → Bool) (hs : ∀ d, side (Γ.origin (Γ.reverse d)) = side (Γ.origin d)) (b : Bool)
    {α TV Col : Type} [Fintype α] [Fintype TV] [Fintype Col]
    (label : D → α) (col : TV → Col) (out : TV → Finset α) (bar : α × Col → α × Col)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label (cout col out)) bar)
    (root : Option (OAI.TorsionFreeZeroDivisors.SupportedImage.vertices Γ Q)) (target : TV)
    (e : CEmb (SideRestriction.graph Γ side hs b) (fun d => label d.val) col out
      (RootPins.pin (SidePins.root side (root.map Subtype.val) b) target) bar r) :
    CEmb (SideRestriction.graph (OAI.TorsionFreeZeroDivisors.SupportedImage.graph Γ Q hQ)
        (fun v => side v.val) (fun d => hs d.val) b)
      (fun d => label d.val.val) col out
      (RootPins.pin (SidePins.root (fun v : OAI.TorsionFreeZeroDivisors.SupportedImage.vertices Γ Q =>
        side v.val) root b) target) bar r := by
  exact e.restrict _ (OAI.TorsionFreeZeroDivisors.SupportedImage.sideVertex Γ Q side b)
    (OAI.TorsionFreeZeroDivisors.SupportedImage.sideDart Γ Q hQ side b)
    (fun _ => rfl) (fun _ => rfl) _ (by
      intro v y hy
      rw [← OAI.TorsionFreeZeroDivisors.SupportedImage.side_root Γ Q side b root, RootPins.pin_map]
      exact hy)

end SupportedImage

namespace AmbientPattern
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ActualPatternEvent

/-- A path system in an ambient finite graph, at scale `Lsc` with threshold `ε`. -/
structure Data (B K I Lsc : ℕ) (ε : ℝ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  side : V → Bool
  side_edge : ∀ d, side (graph.origin (graph.reverse d)) = side (graph.origin d)
  paths : P → List D
  nonempty : ∀ p, paths p ≠ []
  root : Option P
  path_bound : Fintype.card P ≤ K
  comparison_bound : Fintype.card E ≤ I
  path_chain : ∀ p, (paths p).IsChain (WeightedMoore.PortWalk.step graph.origin graph.reverse)
  cyclic_chain : ∀ p, StageRoot.cyclic root p = true →
    ∀ᵉ (x ∈ (paths p).getLast?) (y ∈ (paths p).head?),
      WeightedMoore.PortWalk.step graph.origin graph.reverse x y
  girth : ∀ a (c : graph.subdivision.Walk a a), c.IsCycle →
    (Lsc : ℝ) ≤ WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1 : ℝ))) c
  length_le : (∑ p, (paths p).length : ℕ) ≤ B * Lsc
  length_ge : Lsc ≤ (∑ p, (paths p).length : ℕ)
  comparisons : Comparisons (E := E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e, comparisons.lo e = lower e
  upper_eq : ∀ e, comparisons.hi e = upper e
  lower_le : ∀ e, lower e ≤ upper e
  upper_le : ∀ e, upper e ≤ (paths (comparisons.source e)).length
  reduced : ∀ x e, comparisons.side x = some e →
    RawDecomposition.dart paths x ≠ RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x ≠ graph.reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x = x)).card : ℝ) ≤
    ε * (∑ p, (paths p).length : ℕ)
attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {B K I Lsc : ℕ} {ε : ℝ} (a : Data B K I Lsc ε)
abbrev used := OAI.TorsionFreeZeroDivisors.SupportedImage.used a.graph a.paths
abbrev symmetric := OAI.TorsionFreeZeroDivisors.SupportedImage.used_symmetric a.graph a.paths
abbrev supportedGraph := OAI.TorsionFreeZeroDivisors.SupportedImage.graph a.graph a.used a.symmetric
abbrev vertices := OAI.TorsionFreeZeroDivisors.SupportedImage.vertices a.graph a.used
abbrev pathUsed := OAI.TorsionFreeZeroDivisors.SupportedImage.path_in_used a.graph a.paths
abbrev supportedPaths := OAI.TorsionFreeZeroDivisors.SupportedImage.path a.used a.paths a.pathUsed
lemma lengths_eq : (fun p => (a.supportedPaths p).length) = (fun p => (a.paths p).length) :=
  funext (OAI.TorsionFreeZeroDivisors.SupportedImage.length a.used a.paths a.pathUsed)
abbrev comparison := ComparisonGeometry.cast a.lengths_eq.symm a.comparisons
abbrev iso := ComparisonGeometry.castBackIso a.lengths_eq a.comparisons
abbrev position : Position (fun p => (a.supportedPaths p).length) ≃
    Position (fun p => (a.paths p).length) :=
  ComparisonGeometry.position a.iso.path a.iso.length_eq
lemma dart_eq (x : Position (fun p => (a.supportedPaths p).length)) :
    (RawDecomposition.dart a.supportedPaths x).val = RawDecomposition.dart a.paths (a.position x) := by
  apply Option.some.inj
  rw [← Option.map_some (f := Subtype.val), ← RawDecomposition.dart_get, ← List.getElem?_map,
    OAI.TorsionFreeZeroDivisors.SupportedImage.path_val, ← RawDecomposition.dart_get]
  rfl

def supported : RawSourcePattern.Data B K I Lsc ε where
  V := a.vertices
  D := a.used
  P := a.P
  E := a.E
  graph := a.supportedGraph
  no_isolated := OAI.TorsionFreeZeroDivisors.SupportedImage.no_isolated a.graph a.used a.symmetric
  side := fun v => a.side v.val
  side_edge d := a.side_edge d.val
  paths := a.supportedPaths
  nonempty p := OAI.TorsionFreeZeroDivisors.SupportedImage.nonempty a.used a.paths a.pathUsed p
    (a.nonempty p)
  root := a.root
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  image := OAI.TorsionFreeZeroDivisors.SupportedImage.covered a.graph a.used a.symmetric a.paths
    a.pathUsed (fun d hd => (OAI.TorsionFreeZeroDivisors.SupportedImage.mem_used a.graph a.paths d).mp hd)
  path_chain p := OAI.TorsionFreeZeroDivisors.SupportedImage.chain a.graph a.used a.symmetric
    a.paths a.pathUsed p (a.path_chain p)
  cyclic_chain p hp := OAI.TorsionFreeZeroDivisors.SupportedImage.cyclic a.graph a.used a.symmetric
    a.paths a.pathUsed p (a.cyclic_chain p hp)
  girth := OAI.TorsionFreeZeroDivisors.SupportedImage.girth a.graph a.used a.symmetric (Lsc : ℝ) a.girth
  length_le := by simpa only [OAI.TorsionFreeZeroDivisors.SupportedImage.length] using a.length_le
  length_ge := by simpa only [OAI.TorsionFreeZeroDivisors.SupportedImage.length] using a.length_ge
  comparisons := a.comparison
  lower := a.lower
  upper := a.upper
  lower_eq e := (a.iso.lo_eq e).trans (a.lower_eq e)
  upper_eq e := (a.iso.hi_eq e).trans (a.upper_eq e)
  lower_le := a.lower_le
  upper_le e := by
    rw [OAI.TorsionFreeZeroDivisors.SupportedImage.length]
    have hs : a.comparison.source e = a.comparisons.source e := a.iso.source_eq e
    rw [hs]
    exact a.upper_le e
  reduced := by
    intro x e he
    have hh := a.reduced (a.position x) e ((a.iso.side_some x e).mpr he)
    constructor
    · intro h
      apply hh.1
      have hv := congrArg Subtype.val h
      rw [a.dart_eq, a.dart_eq, a.iso.partner_eq] at hv
      exact hv
    · intro h
      apply hh.2
      have hv := congrArg Subtype.val h
      change (RawDecomposition.dart a.supportedPaths x).val = a.graph.reverse
        (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner x)).val at hv
      rw [a.dart_eq, a.dart_eq, a.iso.partner_eq] at hv
      exact hv
  unpaired_le := by
    rw [a.iso.unpaired]
    simpa only [OAI.TorsionFreeZeroDivisors.SupportedImage.length] using a.unpaired_le

abbrev supportedRoot : Option a.vertices := a.root.map fun p =>
  a.supportedGraph.origin ((a.supportedPaths p).head (a.supported.nonempty p))
lemma supported_root : a.supportedRoot.map Subtype.val =
    a.root.map (fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) := by
  cases h : a.root with
  | none => simp only [supportedRoot, h, Option.map_none]
  | some p =>
    simp only [supportedRoot, h, Option.map_some]
    change some (a.graph.origin (((a.supportedPaths p).head (a.supported.nonempty p)).val)) = _
    rw [OAI.TorsionFreeZeroDivisors.SupportedImage.head_value]

variable (M : Model)

def event (mm : ℕ) (x : M.SA.V mm) (y : M.SB.V mm) (r : Match M mm) : Prop :=
  ∃ label : a.D → M.α,
    (∀ d, label (a.graph.reverse d) = M.inv (label d)) ∧
    (∀ d e, a.graph.origin d = a.graph.origin e → label d = label e → d = e) ∧
    (∀ p e, a.comparisons.side p = some e → label (RawDecomposition.dart a.paths p) =
      if a.comparisons.reverse e then
        M.inv (label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p)))
      else label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p))) ∧
    CEmb (SideRestriction.graph a.graph a.side a.side_edge true) (fun d => label d.val)
      (M.SA.col mm) (M.SA.out mm)
      (RootPins.pin (SidePins.root a.side
        (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) true) x)
      (cbar M.inv M.SA.flip) r.1 ∧
    CEmb (SideRestriction.graph a.graph a.side a.side_edge false) (fun d => label d.val)
      (M.SB.col mm) (M.SB.out mm)
      (RootPins.pin (SidePins.root a.side
        (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) false) y)
      (cbar M.inv M.SB.flip) r.2

lemma comparing (label : a.D → M.α)
    (hc : ∀ p e, a.comparisons.side p = some e → label (RawDecomposition.dart a.paths p) =
      if a.comparisons.reverse e then
        M.inv (label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p)))
      else label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p))) :
    ∀ (p : Position (fun p => (a.supportedPaths p).length)) (e : a.E), a.comparison.side p = some e →
      label (RawDecomposition.dart a.supportedPaths p).val =
      if a.comparison.reverse e then M.inv
        (label (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner p)).val)
      else label (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner p)).val := by
  intro p e he
  have hh := hc (a.position p) e ((a.iso.side_some p e).mpr he)
  have hr : a.comparison.reverse e = a.comparisons.reverse e := a.iso.reverse_eq e
  have hp : a.position (a.comparison.pairing.partner p) = a.comparisons.pairing.partner (a.position p) :=
    a.iso.partner_eq p
  simp only [a.dart_eq]
  rw [hr, hp]
  exact hh

lemma supported_event (mm : ℕ) (x : M.SA.V mm) (y : M.SB.V mm) (r : Match M mm)
    (h : a.event M mm x y r) : a.supported.event M mm x y r := by
  rcases h with ⟨label, hl, hn, hc, ha, hb⟩
  refine ⟨(fun d => label d.val), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun d => hl d.val
  · intro d e ho he
    exact Subtype.ext (hn d.val e.val (congrArg Subtype.val ho) he)
  · exact a.comparing M label hc
  · refine SupportedImage.cemb a.graph a.used a.symmetric a.side a.side_edge true label
      (M.SA.col mm) (M.SA.out mm) (cbar M.inv M.SA.flip) r.1 a.supportedRoot x ?_
    simpa only [a.supported_root] using ha
  · refine SupportedImage.cemb a.graph a.used a.symmetric a.side a.side_edge false label
      (M.SB.col mm) (M.SB.out mm) (cbar M.inv M.SB.flip) r.2 a.supportedRoot y ?_
    simpa only [a.supported_root] using hb

end Data

theorem with_diameter (M : Model) (B K I : ℕ) (hK : 0 < K) (hI : 0 < I) :
    ∀ᶠ mm in atTop, ∀ (x : M.SA.V mm) (y : M.SB.V mm),
      ∃ r ∈ samples M mm, GraphSample.Diameters M mm r ∧
        ∀ a : Data B K I (M.L mm) M.ε, ¬a.event M mm x y r := by
  filter_upwards [GraphSample.raw_with_diameter M B K I hK hI] with mm hr
  intro x y
  obtain ⟨r, hr, hd, ha⟩ := hr x y
  exact ⟨r, hr, hd, fun a he => ha a.supported (a.supported_event M mm x y r he)⟩

end AmbientPattern

namespace SampleGraph
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent
variable (M : Model) (mm : ℕ) (r : Match M mm)

abbrev VA := M.SA.V mm
abbrev VB := M.SB.V mm
abbrev DA := M.SA.Dart mm
abbrev DB := M.SB.Dart mm

/-- The sampled graph `Γ = Γ_A ⊔ Γ_B`. -/
def A : PortGraph (VA M mm) (DA M mm) := r.1.graph (PatternEmbeddings.origin (M.SA.out' mm))
def B : PortGraph (VB M mm) (DB M mm) := r.2.graph (PatternEmbeddings.origin (M.SB.out' mm))
def graph := SumPort.graph (A M mm r) (B M mm r)

/-- Letters of the darts (the colour of a port is forgotten). -/
def label : DA M mm ⊕ DB M mm → M.α := Sum.elim (fun e => e.val.2.1) (fun e => e.val.2.1)

lemma label_reverse (d : DA M mm ⊕ DB M mm) :
    label M mm ((graph M mm r).reverse d) = M.inv (label M mm d) := by
  cases d with
  | inl d => exact congrArg Prod.fst (r.1.label_reverse d)
  | inr d => exact congrArg Prod.fst (r.2.label_reverse d)

lemma immersed (d e : DA M mm ⊕ DB M mm)
    (ho : (graph M mm r).origin d = (graph M mm r).origin e) (hl : label M mm d = label M mm e) :
    d = e := by
  cases d with
  | inl d =>
    cases e with
    | inl e =>
      have ho' : d.val.1 = e.val.1 := Sum.inl.inj ho
      have hd := (Side.mem_out' M.SA).mp d.property
      have he := (Side.mem_out' M.SA).mp e.property
      exact congrArg Sum.inl (Subtype.ext (Prod.ext ho' (Prod.ext hl
        (hd.2.trans (ho' ▸ he.2.symm)))))
    | inr e => cases ho
  | inr d =>
    cases e with
    | inl e => cases ho
    | inr e =>
      have ho' : d.val.1 = e.val.1 := Sum.inr.inj ho
      have hd := (Side.mem_out' M.SB).mp d.property
      have he := (Side.mem_out' M.SB).mp e.property
      exact congrArg Sum.inr (Subtype.ext (Prod.ext ho' (Prod.ext hl
        (hd.2.trans (ho' ▸ he.2.symm)))))

lemma girth (hr : r ∈ samples M mm) : (3 * M.L mm : ℕ) ≤ (graph M mm r).subdivision.egirth := by
  have hm := Finset.mem_product.mp hr
  have hA := (Finset.mem_filter.mp hm.1).2.2
  have hB := (Finset.mem_filter.mp hm.2).2.2
  exact SumPort.girth _ _ _ hA hB

lemma weighted_girth (hr : r ∈ samples M mm) :
    ∀ a (p : (graph M mm r).subdivision.Walk a a), p.IsCycle →
      (M.L mm : ℝ) ≤ WeightedCycles.weight
        (WeightedPortMoore.edgeWeight (fun _ : DA M mm ⊕ DB M mm => (1 : ℝ))) p :=
  WeightedGirth.weighted_girth _ _ (girth M mm r hr)

/-- The left side of the sample embeds into side `A` with its own colours. -/
def colourA (v : SideRestriction.Vertex (@SumPort.side (VA M mm) (VB M mm)) true) : M.SA.Col :=
  M.SA.col mm (SumPort.leftV v)
def colourB (v : SideRestriction.Vertex (@SumPort.side (VA M mm) (VB M mm)) false) : M.SB.Col :=
  M.SB.col mm (SumPort.rightV v)

theorem embeddingA (root : Option (VA M mm ⊕ VB M mm)) (x : VA M mm)
    (hr : ∀ z, root = some (.inl z) → z = x) :
    CEmb (SideRestriction.graph (graph M mm r) SumPort.side (SumPort.side_edge _ _) true)
      (fun d => label M mm d.val) (M.SA.col mm) (M.SA.out mm)
      (RootPins.pin (SidePins.root SumPort.side root true) x) (cbar M.inv M.SA.flip) r.1 := by
  refine ⟨colourA M mm, ⟨{
    vertex := ⟨SumPort.leftV, SumPort.leftV_injective⟩
    port := ⟨SumPort.leftD _ _, SumPort.leftD_injective _ _⟩
    origin_eq := by rintro ⟨d, hd⟩; cases d with | inl d => rfl | inr d => cases hd
    label_eq := by
      rintro ⟨d, hd⟩
      cases d with
      | inl d =>
        have h := (Side.mem_out' M.SA).mp d.property
        exact Prod.ext rfl h.2
      | inr d => cases hd
    reverse_eq := by rintro ⟨d, hd⟩; cases d with | inl d => rfl | inr d => cases hd
    pin_eq := by
      apply RootPins.respects
      rintro ⟨v, hv⟩ h
      cases v with
      | inl v => exact hr v (SumPort.root_value SumPort.side root true _ h)
      | inr v => cases hv }⟩⟩

theorem embeddingB (root : Option (VA M mm ⊕ VB M mm)) (y : VB M mm)
    (hr : ∀ z, root = some (.inr z) → z = y) :
    CEmb (SideRestriction.graph (graph M mm r) SumPort.side (SumPort.side_edge _ _) false)
      (fun d => label M mm d.val) (M.SB.col mm) (M.SB.out mm)
      (RootPins.pin (SidePins.root SumPort.side root false) y) (cbar M.inv M.SB.flip) r.2 := by
  refine ⟨colourB M mm, ⟨{
    vertex := ⟨SumPort.rightV, SumPort.rightV_injective⟩
    port := ⟨SumPort.rightD _ _, SumPort.rightD_injective _ _⟩
    origin_eq := by rintro ⟨d, hd⟩; cases d with | inl d => cases hd | inr d => rfl
    label_eq := by
      rintro ⟨d, hd⟩
      cases d with
      | inl d => cases hd
      | inr d =>
        have h := (Side.mem_out' M.SB).mp d.property
        exact Prod.ext rfl h.2
    reverse_eq := by rintro ⟨d, hd⟩; cases d with | inl d => cases hd | inr d => rfl
    pin_eq := by
      apply RootPins.respects
      rintro ⟨v, hv⟩ h
      cases v with
      | inl v => cases hv
      | inr v => exact hr v (SumPort.root_value SumPort.side root false _ h) }⟩⟩

/-- A bounded, nearly paired, rooted path system in the sampled graph of a model
(OpenAI's `SampleGraph.BoundedSystem`, with the model's scale and threshold). -/
structure BoundedSystem (Bnd K I mm : ℕ) (r : Match M mm) (x : VA M mm) (y : VB M mm) where
  P : Type
  E : Type
  [fP : Fintype P]
  [fE : Fintype E]
  paths : P → List (DA M mm ⊕ DB M mm)
  nonempty : ∀ p, paths p ≠ []
  root : Option P
  path_bound : Fintype.card P ≤ K
  comparison_bound : Fintype.card E ≤ I
  path_chain : ∀ p, (paths p).IsChain
    (WeightedMoore.PortWalk.step (graph M mm r).origin (graph M mm r).reverse)
  cyclic_chain : ∀ p, StageRoot.cyclic root p = true →
    ∀ᵉ (x ∈ (paths p).getLast?) (y ∈ (paths p).head?),
      WeightedMoore.PortWalk.step (graph M mm r).origin (graph M mm r).reverse x y
  length_le : (∑ p, (paths p).length : ℕ) ≤ Bnd * M.L mm
  length_ge : M.L mm ≤ (∑ p, (paths p).length : ℕ)
  comparisons : ComparedBlocks.Comparisons (E := E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e, comparisons.lo e = lower e
  upper_eq : ∀ e, comparisons.hi e = upper e
  lower_le : ∀ e, lower e ≤ upper e
  upper_le : ∀ e, upper e ≤ (paths (comparisons.source e)).length
  reduced : ∀ x e, comparisons.side x = some e →
    RawDecomposition.dart paths x ≠ RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x ≠
      (graph M mm r).reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x = x)).card : ℝ) ≤
    M.ε * (∑ p, (paths p).length : ℕ)
  rootA : ∀ z, root.map (fun p => (graph M mm r).origin ((paths p).head (nonempty p))) =
    some (.inl z) → z = x
  rootB : ∀ z, root.map (fun p => (graph M mm r).origin ((paths p).head (nonempty p))) =
    some (.inr z) → z = y
  compatible : ∀ p e, comparisons.side p = some e →
    label M mm (RawDecomposition.dart paths p) =
      if comparisons.reverse e then
        M.inv (label M mm (RawDecomposition.dart paths (comparisons.pairing.partner p)))
      else label M mm (RawDecomposition.dart paths (comparisons.pairing.partner p))
attribute [instance] BoundedSystem.fP BoundedSystem.fE

namespace BoundedSystem
variable {M} {Bnd K I mm : ℕ} {r : Match M mm} {x : VA M mm} {y : VB M mm}
    (s : BoundedSystem M Bnd K I mm r x y)

def data (hr : r ∈ samples M mm) : AmbientPattern.Data Bnd K I (M.L mm) M.ε where
  V := VA M mm ⊕ VB M mm
  D := DA M mm ⊕ DB M mm
  P := s.P
  E := s.E
  graph := graph M mm r
  side := SumPort.side
  side_edge := SumPort.side_edge _ _
  paths := s.paths
  nonempty := s.nonempty
  root := s.root
  path_bound := s.path_bound
  comparison_bound := s.comparison_bound
  path_chain := s.path_chain
  cyclic_chain := s.cyclic_chain
  girth := weighted_girth M mm r hr
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

lemma event (hr : r ∈ samples M mm) : (s.data hr).event M mm x y r :=
  ⟨label M mm, label_reverse M mm r, immersed M mm r, s.compatible,
    embeddingA M mm r _ x s.rootA, embeddingB M mm r _ y s.rootB⟩

end BoundedSystem

/-- **Existence form of Theorem 3.4 (b)–(d)** for an abstract model: for every choice of
bounds, all large sizes and all roots, some girth-conditioned outcome has component diameters
at most `D₀·L` and carries no bounded nearly-paired path system (OpenAI's
`SampleGraph.exists_avoiding`, with `ε = M.ε` fixed by the model before `Bnd K I`). -/
theorem exists_avoiding (Bnd K I : ℕ) (hK : 0 < K) (hI : 0 < I) :
    ∀ᶠ mm in atTop, ∀ (x : VA M mm) (y : VB M mm),
      ∃ r ∈ samples M mm, GraphSample.Diameters M mm r ∧
        IsEmpty (BoundedSystem M Bnd K I mm r x y) := by
  filter_upwards [AmbientPattern.with_diameter M Bnd K I hK hI] with mm hrep
  intro x y
  obtain ⟨r, hr, hd, ha⟩ := hrep x y
  refine ⟨r, hr, hd, ⟨?_⟩⟩
  intro s
  exact ha (s.data hr) (s.event hr)

end SampleGraph

end

end Kaplansky.Random
