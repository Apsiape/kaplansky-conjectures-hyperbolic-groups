import Kaplansky.Random.Chain.PatternUniform
import OAI.Algebra.GroupRing.RawDecomposition

/-!
# Fork of the model-dependent parts of `Iso.lean`, `PatternTotalCoding.lean`, `ChainUsage.lean`

* `CEmb.sideIso` and `OriginalPatternIso.realized` for coloured embeddings;
* `BoundedPattern.Data.event`, `event_of_encode_eq`, `Good`, `probability_bound`,
  `probability_union`, `polynomial_exp_tendsto`, `eventually_avoids` for a `Model`;
* `SourcePattern.Data` parameterized by the scale `Lsc` and the threshold `ε` (OpenAI: by `rep`,
  with `L (size rep)` and `epsilon (1/600) 256`); it no longer depends on the model.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

section SideIso
open PortSubdivision
variable {α V D V' D' TV Col : Type} [Fintype V] [Fintype D] [Fintype V'] [Fintype D']
    [Fintype α] [Fintype TV] [Fintype Col] {Γ : PortGraph V D} {Γ' : PortGraph V' D'}
    (f : PortSubdivision.Iso Γ Γ') (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d, side (Γ.origin (Γ.reverse d)) = side (Γ.origin d))
    (hs' : ∀ d, side' (Γ'.origin (Γ'.reverse d)) = side' (Γ'.origin d))
    (hside : ∀ v, side v = side' (f.vertex v)) (b : Bool)
    (root : Option V) (root' : Option V') (hroot : root.map f.vertex = root')
    (label : D' → α) (col : TV → Col) (out : TV → Finset α) (target : TV)
    (bar : α × Col → α × Col)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label (cout col out)) bar)

include hside hroot in
/-- A side-preserving isomorphism transports coloured rooted embeddings. -/
theorem CEmb.sideIso (e : CEmb (SideRestriction.graph Γ' side' hs' b) (fun d => label d.val)
    col out (RootPins.pin (SidePins.root side' root' b) target) bar r) :
    CEmb (SideRestriction.graph Γ side hs b) (fun d => label (f.dart d.val)) col out
      (RootPins.pin (SidePins.root side root b) target) bar r := by
  let fv : SideRestriction.Vertex side b ↪ SideRestriction.Vertex side' b :=
    ⟨fun v => ⟨f.vertex v.val, (hside v.val).symm.trans v.property⟩,
      fun _ _ h => Subtype.ext (f.vertex.injective (congrArg Subtype.val h))⟩
  let fd : SideRestriction.Dart Γ side b ↪ SideRestriction.Dart Γ' side' b :=
    ⟨fun d => ⟨f.dart d.val, by rw [← f.origin_eq, ← hside]; exact d.property⟩,
      fun _ _ h => Subtype.ext (f.dart.injective (congrArg Subtype.val h))⟩
  have ho d : fv ((SideRestriction.graph Γ side hs b).origin d) =
      (SideRestriction.graph Γ' side' hs' b).origin (fd d) := Subtype.ext (f.origin_eq d.val)
  have hr d : fd ((SideRestriction.graph Γ side hs b).reverse d) =
      (SideRestriction.graph Γ' side' hs' b).reverse (fd d) := Subtype.ext (f.reverse_eq d.val)
  have hp v y : RootPins.pin (SidePins.root side root b) target v = some y →
      RootPins.pin (SidePins.root side' root' b) target (fv v) = some y := by
    simp only [RootPins.pin_some_iff, SidePins.root_eq_some]
    rintro ⟨hv, hy⟩
    refine ⟨?_, hy⟩
    rw [← hroot, hv]
    rfl
  exact e.restrict _ fv fd ho hr _ hp

end SideIso

namespace OriginalPatternIso
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
open OAI.TorsionFreeZeroDivisors.OriginalPatternIso (dart_eq)
variable (M : Model) {V D P E V' D' P' E' : Type} [Fintype V] [Fintype D] [Fintype P]
    [Fintype V'] [Fintype D'] [Fintype P']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card = 2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v, ¬mark' v → (out Γ'.origin v).card = 2)
    (paths : P → List {x : D // turn Γ.origin mark h2 x = x}) (hp : ∀ p, paths p ≠ [])
    (paths' : P' → List {x : D' // turn Γ'.origin mark' h2' x = x}) (hp' : ∀ p, paths' p ≠ [])
variable (f : PortSubdivision.Iso Γ Γ') (eP : P ≃ P')
    (hwords : ∀ p, ((paths p).flatMap (word Γ mark h2)).map f.dart =
      (paths' (eP p)).flatMap (word Γ' mark' h2'))
variable (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d, side (Γ.origin (Γ.reverse d)) = side (Γ.origin d))
    (hs' : ∀ d, side' (Γ'.origin (Γ'.reverse d)) = side' (Γ'.origin d))
    (hside : ∀ v, side v = side' (f.vertex v))
    (root : Option P) (root' : Option P')
    (hroot : (StageRoot.source Γ mark h2 paths hp root).map f.vertex =
      StageRoot.source Γ' mark' h2' paths' hp' root')
    (C : Comparisons (E := E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (C' : Comparisons (E := E') (pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths')))
    (g : ComparisonGeometry.Iso C C') (hg : g.path = eP)
    (mm : ℕ) (a : M.SA.V mm) (b : M.SB.V mm)

include hwords hside hroot hg in
omit [Fintype P] [Fintype P'] in
lemma realized (r : ActualPatternEvent.Match M mm)
    (he : OriginalPattern.Realized M Γ' mark' h2' side' hs' paths' hp' root' mm a b C' r) :
    OriginalPattern.Realized M Γ mark h2 side hs paths hp root mm a b C r := by
  subst eP
  rcases he with ⟨label, hl, hi, hc, ea, eb⟩
  refine ⟨label ∘ f.dart, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    dsimp only [Function.comp_apply]
    rw [f.reverse_eq, hl]
  · intro d e ho he
    apply f.dart.injective
    apply hi _ _ _ he
    rw [← f.origin_eq, ← f.origin_eq, ho]
  · intro x j hj
    have hh := hc (ComparisonGeometry.position g.path g.length_eq x) (g.comparison j)
      ((g.side_some x j).mpr hj)
    dsimp only [Function.comp_apply]
    rw [dart_eq Γ mark h2 Γ' mark' h2' paths paths' f g.path hwords x g.length_eq,
      dart_eq Γ mark h2 Γ' mark' h2' paths paths' f g.path hwords (C.pairing.partner x) g.length_eq,
      g.partner_eq, g.reverse_eq]
    exact hh
  · exact CEmb.sideIso f side side' hs hs' hside true _ _ hroot label _ _ a _ r.1 ea
  · exact CEmb.sideIso f side side' hs hs' hside false _ _ hroot label _ _ b _ r.2 eb

end OriginalPatternIso

namespace BoundedPattern.Data
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks RankedSuppressionIso
variable (M : Model) {R K T I H : ℕ} (a b : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data R K T I H)

def event (mm : ℕ) (x : M.SA.V mm) (y : M.SB.V mm) (r : ActualPatternEvent.Match M mm) : Prop :=
  OriginalPattern.Realized M a.graph a.mark a.degree_two a.side a.side_edge a.paths a.nonempty
    a.root mm x y a.comparisons r

theorem event_of_encode_eq (hR : 0 < R) (hK : 0 < K) (hI : 0 < I)
    (he : a.encode hR hK hI = b.encode hR hK hI)
    (mm : ℕ) (x : M.SA.V mm) (y : M.SB.V mm) (r : ActualPatternEvent.Match M mm)
    (hb : event M b mm x y r) : event M a mm x y r := by
  obtain ⟨f, g, hpg, hrank, hside⟩ := PatternTotalCoding.complete R K T I H hR hK hI
    a.dart_bound a.vertex_bound a.path_bound a.comparison_bound
    b.dart_bound b.vertex_bound b.path_bound b.comparison_bound
    a.graphData (fun v => a.side v.val) a.geometryData
    b.graphData (fun v => b.side v.val) b.geometryData he
  let f₀ : PortSubdivision.Iso (skeleton a.graph a.mark a.degree_two)
      (skeleton b.graph b.mark b.degree_two) :=
    ⟨f.vertex, f.dart, f.origin_eq, f.reverse_eq⟩
  have hlen (d : a.Seeds) : chainLength a.graph a.mark a.degree_two d =
      chainLength b.graph b.mark b.degree_two (f₀.dart d) := congrArg Fin.val (f.length_eq d)
  let F := full a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
  have words (p : a.P) : ((a.paths p).flatMap (word a.graph a.mark a.degree_two)).map F.dart =
      (b.paths (f.path p)).flatMap (word b.graph b.mark b.degree_two) :=
    full_words a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered
      f₀ hrank hlen a.paths b.paths f.path f.paths_eq p
  have hroot : a.root.map f.path = b.root := by
    have hh := congrArg (Option.map Prod.fst) f.root_eq
    simpa [OAI.TorsionFreeZeroDivisors.BoundedPattern.Data.graphData, Option.map_map,
      Function.comp_def] using hh
  have sides (v : a.V) : a.side v = b.side (F.vertex v) :=
    full_side a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
      a.side b.side a.side_edge b.side_edge hside v
  have roots : (StageRoot.source a.graph a.mark a.degree_two a.paths a.nonempty a.root).map F.vertex =
      StageRoot.source b.graph b.mark b.degree_two b.paths b.nonempty b.root :=
    full_source a.graph a.mark a.degree_two b.graph b.mark b.degree_two a.covered b.covered f₀ hrank hlen
      a.paths b.paths f.path f.paths_eq a.nonempty b.nonempty a.root b.root hroot
  let geometry : ComparisonGeometry.Iso a.comparisons b.comparisons := {
    path := f.path
    comparison := g.comparison
    length_eq := OAI.TorsionFreeZeroDivisors.OriginalPatternIso.length_eq a.graph a.mark
      a.degree_two b.graph b.mark b.degree_two a.paths b.paths F f.path words
    flip_eq := g.flip_eq
    source_eq := by intro e; rw [hpg]; exact g.source_eq e
    lo_eq := by
      intro e
      rw [a.lower_eq, b.lower_eq]
      exact_mod_cast congrArg Fin.val (g.lower_eq e)
    hi_eq := by
      intro e
      rw [a.upper_eq, b.upper_eq]
      exact_mod_cast congrArg Fin.val (g.upper_eq e)
    reverse_eq := g.reverse_eq
    offset_eq := by
      intro e
      rw [a.offset_eq, b.offset_eq]
      have ho := congrArg Fin.val (g.offset_eq e)
      exact congrArg (fun n : ℕ => (n : ℤ) - 2 * H) ho }
  exact OriginalPatternIso.realized M a.graph a.mark a.degree_two b.graph b.mark b.degree_two
    a.paths a.nonempty b.paths b.nonempty F f.path words a.side b.side a.side_edge b.side_edge
    sides a.root b.root roots a.comparisons b.comparisons geometry rfl mm x y r hb

open GridAsymptotics
open OAI.TorsionFreeZeroDivisors.BoundedPattern.Data (multiplicity totalLength)

/-- Deterministic hypotheses for the bounded first moment, at scale `Lsc` and threshold `ε`.
Compared with OpenAI's `Good`, it also bounds the number of marked vertices by `Q`. -/
structure Good (B Q Mst J Lsc : ℕ) (ε : ℝ) : Prop where
  multiplicity_le : ∀ c, a.multiplicity c ≤ Mst
  multiplicity_pos : ∀ c, 1 ≤ a.multiplicity c
  path_chain : ∀ p, List.IsChain (WeightedMoore.PortWalk.step
    (suppressed a.graph a.mark a.degree_two).origin (suppressed a.graph a.mark a.degree_two).reverse)
      (a.paths p)
  cyclic_chain : ∀ p, StageRoot.cyclic a.root p = true →
    ∀ᵉ (x ∈ (a.paths p).getLast?) (y ∈ (a.paths p).head?),
      WeightedMoore.PortWalk.step (suppressed a.graph a.mark a.degree_two).origin
        (suppressed a.graph a.mark a.degree_two).reverse x y
  reduced : ∀ x e, a.comparisons.side x = some e →
    originalDart a.graph a.mark a.degree_two a.paths x ≠
      originalDart a.graph a.mark a.degree_two a.paths (a.comparisons.pairing.partner x) ∧
    originalDart a.graph a.mark a.degree_two a.paths x ≠ a.graph.reverse
      (originalDart a.graph a.mark a.degree_two a.paths (a.comparisons.pairing.partner x))
  chains_le : Fintype.card (Rep a.graph a.mark a.degree_two) ≤ Q
  marks_le : Fintype.card (Mark a.mark) ≤ Q
  cut_comparisons_le : Fintype.card a.E * (Fintype.card (RepeatedBlocks.Traversal a.multiplicity)) ^ 2 ≤ J
  length_le : a.totalLength ≤ B * (Lsc : ℝ)
  length_ge : (Lsc : ℝ) ≤ a.totalLength
  unpaired_le : ((Finset.univ.filter (fun x => a.comparisons.pairing.partner x = x)).card : ℝ) ≤
    ε * a.totalLength

lemma probability_bound (B Q Mst J mm : ℕ) (hM : 0 < Mst)
    (hready : PatternUniform.Ready M B Mst Q J mm)
    (hg : Good a B Q Mst J (M.L mm) M.ε) (x : M.SA.V mm) (y : M.SB.V mm) :
    (((ActualPatternEvent.samples M mm).filter (event M a mm x y)).card : ℝ) /
        (ActualPatternEvent.samples M mm).card ≤
      Real.exp (-(M.L mm : ℝ) / (8 * M.D * Mst)) := by
  exact OriginalPattern.probability_bound M a.graph a.mark a.degree_two a.side a.side_edge a.paths
    a.nonempty a.root mm x y a.comparisons (fun e => (a.lower e).val) (fun e => (a.upper e).val)
    (by simpa only [Int.cast_natCast] using a.lower_eq)
    (by simpa only [Int.cast_natCast] using a.upper_eq)
    B Q Mst J hM hready hg.multiplicity_le hg.multiplicity_pos hg.path_chain hg.cyclic_chain
    hg.reduced hg.chains_le hg.marks_le hg.cut_comparisons_le hg.length_le hg.length_ge hg.unpaired_le

end BoundedPattern.Data

namespace BoundedPattern
open scoped Classical Topology
open GridAsymptotics ActualPatternEvent

theorem probability_union (M : Model) (R K T I H B Q Mst J mm : ℕ)
    (hR : 0 < R) (hK : 0 < K) (hI : 0 < I) (hM : 0 < Mst)
    (hs : (samples M mm).Nonempty) (hready : PatternUniform.Ready M B Mst Q J mm)
    (x : M.SA.V mm) (y : M.SB.V mm) :
    (((samples M mm).filter (fun r => ∃ a : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data R K T I H,
        Data.Good a B Q Mst J (M.L mm) M.ε ∧ Data.event M a mm x y r)).card : ℝ) /
      (samples M mm).card ≤
      (PatternTotalCoding.coefficient R K T I : ℝ) * (H + 1 : ℕ) ^ (R + 3 * I) *
        Real.exp (-(M.L mm : ℝ) / (8 * M.D * Mst)) := by
  have he := PatternFiniteUnion.bound (samples M mm) hs
    (fun a : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data R K T I H => a.encode hR hK hI)
    (fun a => Data.Good a B Q Mst J (M.L mm) M.ε) (fun a => Data.event M a mm x y) _
    (Real.exp_pos _).le
    (fun a b hab r ha => Data.event_of_encode_eq M b a hR hK hI hab.symm mm x y r ha)
    (fun a ha => Data.probability_bound M a B Q Mst J mm hM hready ha x y)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast PatternTotalCoding.card_code_bound R K T I H

lemma polynomial_exp_tendsto (M : Model) (c B d Mst : ℕ) (hM : 0 < Mst) :
    Tendsto (fun mm => (c : ℝ) * (B * M.L mm + 1 : ℕ) ^ d *
      Real.exp (-(M.L mm : ℝ) / (8 * M.D * Mst))) atTop (𝓝 0) := by
  have hD := M.D_pos'
  have hMst : (0 : ℝ) < Mst := by exact_mod_cast hM
  have hL : Tendsto (fun mm => (M.L mm : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp M.L_tendsto
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ)
    (1 / (8 * M.D * Mst)) (by positivity)).comp hL
  simp only [Function.comp_def, Real.rpow_natCast] at ht
  have ht' := ht.const_mul ((c : ℝ) * (B + 1 : ℝ) ^ d)
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht'
  filter_upwards [hL.eventually (eventually_ge_atTop (1 : ℝ))] with mm hr
  have hp : ((B * M.L mm + 1 : ℕ) : ℝ) ^ d ≤ ((B + 1 : ℝ) * (M.L mm : ℝ)) ^ d := by
    gcongr
    push_cast
    nlinarith
  calc
    _ ≤ (c : ℝ) * ((B + 1 : ℝ) * (M.L mm : ℝ)) ^ d *
        Real.exp (-(M.L mm : ℝ) / (8 * M.D * Mst)) := by gcongr
    _ = (c : ℝ) * (B + 1 : ℝ) ^ d * ((M.L mm : ℝ) ^ d *
        Real.exp (-(1 / (8 * M.D * Mst : ℝ)) * (M.L mm : ℝ))) := by
      have he : -(M.L mm : ℝ) / (8 * M.D * Mst) = -(1 / (8 * M.D * Mst : ℝ)) * (M.L mm : ℝ) := by
        ring
      rw [he, mul_pow]
      ring

lemma samples_eventually_nonempty (M : Model) : ∀ᶠ mm in atTop, (samples M mm).Nonempty := by
  filter_upwards [M.eventual_nonempty] with mm hr
  obtain ⟨a, ha⟩ := hr.1
  obtain ⟨b, hb⟩ := hr.2
  exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩⟩

end BoundedPattern

namespace SourcePattern
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity
open OAI.TorsionFreeZeroDivisors.SourcePattern (Seeds marked_bound R R_pos T)

/-- Suppressed form of source paths at scale `Lsc` with threshold `ε`. -/
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
  vertices : Finset V
  vertices_bound : vertices.card ≤ 2 * K
  no_isolated : Function.Surjective graph.origin
  side : V → Bool
  side_edge : ∀ d, side (graph.origin (graph.reverse d)) = side (graph.origin d)
  paths : P → List (Seeds graph vertices)
  nonempty : ∀ p, paths p ≠ []
  root : Option P
  path_bound : Fintype.card P ≤ K
  comparison_bound : Fintype.card E ≤ I
  image : ChainUsage.Used graph (marks graph vertices) (marks_degree_two graph vertices) paths
  path_chain : ∀ p, ((paths p).flatMap (word graph (marks graph vertices)
    (marks_degree_two graph vertices))).IsChain (WeightedMoore.PortWalk.step graph.origin graph.reverse)
  cyclic_chain : ∀ p, StageRoot.cyclic root p = true →
    ∀ᵉ (x ∈ ((paths p).flatMap (word graph (marks graph vertices)
        (marks_degree_two graph vertices))).getLast?)
        (y ∈ ((paths p).flatMap (word graph (marks graph vertices)
          (marks_degree_two graph vertices))).head?),
      WeightedMoore.PortWalk.step graph.origin graph.reverse x y
  girth : ∀ a (c : graph.subdivision.Walk a a), c.IsCycle →
    (Lsc : ℝ) ≤ WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1 : ℝ))) c
  length_le : (∑ p, ((paths p).flatMap (word graph (marks graph vertices)
    (marks_degree_two graph vertices))).length : ℕ) ≤ B * Lsc
  length_ge : Lsc ≤ (∑ p, ((paths p).flatMap (word graph (marks graph vertices)
    (marks_degree_two graph vertices))).length : ℕ)
  comparisons : Comparisons (E := E) (pathLength (chunks graph (marks graph vertices)
    (marks_degree_two graph vertices) paths)
    (chunkLength graph (marks graph vertices) (marks_degree_two graph vertices) paths))
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e, comparisons.lo e = lower e
  upper_eq : ∀ e, comparisons.hi e = upper e
  lower_le : ∀ e, lower e ≤ upper e
  upper_le : ∀ e, upper e ≤ pathLength (chunks graph (marks graph vertices)
    (marks_degree_two graph vertices) paths)
    (chunkLength graph (marks graph vertices) (marks_degree_two graph vertices) paths)
      (comparisons.source e)
  reduced : ∀ x e, comparisons.side x = some e →
    originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths x ≠
      originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths
        (comparisons.pairing.partner x) ∧
    originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths x ≠ graph.reverse
      (originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths
        (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x = x)).card : ℝ) ≤
    ε * (∑ p, ((paths p).flatMap (word graph (marks graph vertices)
      (marks_degree_two graph vertices))).length : ℕ)

attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {B K I Lsc : ℕ} {ε : ℝ} (a : Data B K I Lsc ε)
abbrev mark := marks a.graph a.vertices
abbrev degree_two := marks_degree_two a.graph a.vertices
abbrev words (p : a.P) := (a.paths p).flatMap (word a.graph a.mark a.degree_two)
abbrev totalLength : ℕ := ∑ p, (a.words p).length
abbrev lengths : a.P → ℕ := pathLength (chunks a.graph a.mark a.degree_two a.paths)
  (chunkLength a.graph a.mark a.degree_two a.paths)

lemma words_nonempty (p : a.P) : a.words p ≠ [] := by
  intro he
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil (a.paths p) (a.nonempty p)
  have hm : b.val ∈ a.words p := by
    apply List.mem_flatMap.mpr
    exact ⟨b, hb, start_mem_word a.graph a.mark a.degree_two b⟩
  simp [he] at hm

lemma lengths_le (p : a.P) : a.lengths p ≤ B * Lsc := by
  rw [lengths, pathLength_eq]
  apply le_trans (b := a.totalLength) _ a.length_le
  exact Finset.single_le_sum (f := fun p => (a.words p).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)

lemma upper_bound (e : a.E) : a.upper e ≤ B * Lsc :=
  (a.upper_le e).trans (a.lengths_le _)

lemma lower_bound (e : a.E) : a.lower e ≤ B * Lsc :=
  (a.lower_le e).trans (a.upper_bound e)

lemma covered : ∀ d, ChainCoverage.Covered a.graph.reverse (turn a.graph.origin a.mark a.degree_two)
    a.graph.reverse_reverse (turn_involutive a.graph.origin a.mark a.degree_two) d := by
  apply ActualMarkedChains.actual_image_covered a.graph a.mark a.degree_two a.words a.path_chain _ a.image
  intro p d hd
  rw [words, ChainPathTransport.flatMap_head] at hd
  obtain ⟨b, _hb, hbd⟩ := Option.mem_map.mp hd
  subst d
  exact (turn_fixed_iff a.graph.origin a.mark a.degree_two b.val).mp b.property

lemma mark_bounds (hL : 0 < Lsc) :
    Fintype.card (Seeds a.graph a.vertices) ≤ R B K ∧ Fintype.card (Mark a.mark) ≤ R B K := by
  apply (marked_bound B K).choose_spec.2 a.graph a.vertices a.vertices_bound a.words
    a.words_nonempty a.path_bound a.no_isolated a.path_chain a.image (Lsc : ℝ)
    (by exact_mod_cast hL) _ a.girth
  exact_mod_cast a.length_le

lemma total_traversals_le (hL : 0 < Lsc) : ∑ p, (a.paths p).length ≤ T B K := by
  have h := ChainPaths.bounded_chain_traversals a.graph a.mark a.degree_two
    (B : ℝ) (Nat.cast_nonneg _) K (R B K) a.path_bound (a.mark_bounds hL).1
    (Lsc : ℝ) (by exact_mod_cast hL) a.girth a.paths a.path_chain
    (by exact_mod_cast a.length_le)
  have he : (R B K : ℝ) * ((B : ℝ) + K) = (T B K : ℝ) := by
    simp only [T, Nat.cast_mul, Nat.cast_add]
  rw [he, Nat.ceil_natCast] at h
  exact h

lemma traversal_le (hL : 0 < Lsc) (p : a.P) : (a.paths p).length ≤ T B K :=
  (Finset.single_le_sum (f := fun p => (a.paths p).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)).trans (a.total_traversals_le hL)

lemma offset_bounds (e : a.E) :
    -(2 * (B * Lsc : ℕ) : ℤ) ≤ a.comparisons.offset e ∧
      a.comparisons.offset e ≤ (2 * (B * Lsc : ℕ) : ℤ) := by
  have hlo : (0 : ℝ) ≤ a.comparisons.lo e := by rw [a.lower_eq]; positivity
  have hhi : (0 : ℝ) ≤ a.comparisons.hi e := by rw [a.upper_eq]; positivity
  have hlb : a.comparisons.lo e ≤ (B * Lsc : ℕ) := by
    rw [a.lower_eq]; exact_mod_cast a.lower_bound e
  have hub : a.comparisons.hi e ≤ (B * Lsc : ℕ) := by
    rw [a.upper_eq]; exact_mod_cast a.upper_bound e
  have hlen : (a.lengths (a.comparisons.source (a.comparisons.flip e)) : ℝ) ≤ (B * Lsc : ℕ) :=
    by exact_mod_cast a.lengths_le _
  have hr := a.comparisons.target_range e
  have he : -2 * ((B * Lsc : ℕ) : ℝ) ≤ (a.comparisons.offset e : ℝ) ∧
      (a.comparisons.offset e : ℝ) ≤ 2 * ((B * Lsc : ℕ) : ℝ) := by
    cases hh : a.comparisons.reverse e <;> simp only [hh, Bool.false_eq_true, ↓reduceIte] at hr
    · constructor <;> linarith
    · constructor <;> linarith
  exact_mod_cast he

def bounded (hL : 0 < Lsc) :
    OAI.TorsionFreeZeroDivisors.BoundedPattern.Data (R B K) K (T B K) I (B * Lsc) where
  V := a.V
  D := a.D
  P := a.P
  E := a.E
  graph := a.graph
  mark := a.mark
  degree_two := a.degree_two
  covered := a.covered
  side := a.side
  side_edge := a.side_edge
  paths := a.paths
  nonempty := a.nonempty
  root := a.root
  comparisons := a.comparisons
  lower e := ⟨a.lower e, by have := a.lower_bound e; omega⟩
  upper e := ⟨a.upper e, by have := a.upper_bound e; omega⟩
  offset e := ⟨(a.comparisons.offset e + 2 * (B * Lsc : ℕ)).toNat, by
    obtain ⟨hl, hu⟩ := a.offset_bounds e
    omega⟩
  lower_eq := a.lower_eq
  upper_eq := a.upper_eq
  offset_eq e := by
    obtain ⟨hl, hu⟩ := a.offset_bounds e
    dsimp
    omega
  dart_bound := (a.mark_bounds hL).1
  vertex_bound := (a.mark_bounds hL).2
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  chain_length_bound d :=
    (ChainUsage.chain_length_le a.graph a.mark a.degree_two a.paths a.image d).trans a.length_le
  traversal_bound := a.traversal_le hL

lemma bounded_good (hL : 0 < Lsc) :
    BoundedPattern.Data.Good (a.bounded hL) B (R B K) (T B K) (I * (T B K) ^ 2) Lsc ε where
  multiplicity_le c := (ChainUsage.multiplicity_le a.graph a.mark a.degree_two a.paths c).trans
    (a.total_traversals_le hL)
  multiplicity_pos := ChainUsage.multiplicity_pos a.graph a.mark a.degree_two a.paths a.image
  path_chain p := ChainPathTransport.isChain a.graph a.mark a.degree_two (a.paths p) (a.path_chain p)
  cyclic_chain p hp :=
    ChainPathTransport.closing a.graph a.mark a.degree_two (a.paths p) (a.cyclic_chain p hp)
  reduced := a.reduced
  chains_le := (ChainUsage.rep_card_le a.graph a.mark a.degree_two).trans (a.mark_bounds hL).1
  marks_le := (a.mark_bounds hL).2
  cut_comparisons_le := by
    change Fintype.card a.E * (Fintype.card (RepeatedBlocks.Traversal
      (ChunkComparisons.multiplicity (color a.graph a.mark a.degree_two a.paths)))) ^ 2 ≤ _
    rw [ChainUsage.traversal_card]
    exact Nat.mul_le_mul a.comparison_bound (Nat.pow_le_pow_left (a.total_traversals_le hL) 2)
  length_le := by
    change (∑ p, (a.words p).length : ℝ) ≤ _
    exact_mod_cast a.length_le
  length_ge := by
    change _ ≤ (∑ p, (a.words p).length : ℝ)
    exact_mod_cast a.length_ge
  unpaired_le := by
    change _ ≤ ε * (∑ p, (a.words p).length : ℝ)
    exact_mod_cast a.unpaired_le

end Data
end SourcePattern

namespace BoundedPattern
open scoped Classical Topology
open ActualPatternEvent

/-- With the bounds fixed beforehand, for every sufficiently large size there is a sample
avoiding every bounded pattern; roots are quantified after the size threshold. -/
theorem eventually_avoids (M : Model) (R K T I B Q Mst J : ℕ)
    (hR : 0 < R) (hK : 0 < K) (hI : 0 < I) (hM : 0 < Mst) :
    ∀ᶠ mm in atTop, ∀ (x : M.SA.V mm) (y : M.SB.V mm),
      ∃ r ∈ samples M mm, ∀ a : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data R K T I (B * M.L mm),
        Data.Good a B Q Mst J (M.L mm) M.ε → ¬Data.event M a mm x y r := by
  have hsmall := (polynomial_exp_tendsto M (PatternTotalCoding.coefficient R K T I)
    B (R + 3 * I) Mst hM).eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, samples_eventually_nonempty M,
    PatternUniform.eventually_ready M B Mst Q J hM] with mm hb hs hr
  intro x y
  have hprob := (probability_union M R K T I (B * M.L mm) B Q Mst J mm hR hK hI hM hs hr x y).trans_lt hb
  by_contra hn
  have hall : ∀ r ∈ samples M mm, ∃ a : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data R K T I (B * M.L mm),
      Data.Good a B Q Mst J (M.L mm) M.ε ∧ Data.event M a mm x y r := by
    push_neg at hn
    exact hn
  have he : (samples M mm).filter (fun r => ∃ a : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data
      R K T I (B * M.L mm), Data.Good a B Q Mst J (M.L mm) M.ε ∧ Data.event M a mm x y r) =
      samples M mm := by
    apply Finset.filter_eq_self.mpr
    exact hall
  rw [he, div_self (by exact_mod_cast (Finset.card_pos.mpr hs).ne')] at hprob
  exact (lt_irrefl (1 : ℝ)) hprob

end BoundedPattern

end

end Kaplansky.Random
