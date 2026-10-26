import Kaplansky.Random.Chain.SideTransport
import OAI.Algebra.GroupRing.SidePins

/-!
# Fork of the model-dependent parts of `SidePins.lean`

`ActualStagePair` (the two prescribed sides of one multiplicity stage, now coloured) and
`ActualPatternEvent` (the realization event of an enlarged pattern, its stage counts and its
probability bound) for an abstract `Model`.  The size parameter is `mm`; OpenAI's stage count
`M` is called `Mst`.  Realization of a side is a coloured embedding `CEmb`.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

namespace ActualStagePair
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs
open OAI.TorsionFreeZeroDivisors.StageSideEmbedding (firstPoint lastPoint chain_card)
open ComparedBlocks RepeatedBlocks
variable (M : Model) {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card = 2)
    (side : V → Bool) (hsid : ∀ d, side (Γ.origin (Γ.reverse d)) = side (Γ.origin d))
    (paths : P → List {d : D // turn Γ.origin mark h2 d = d}) (hp : ∀ p, paths p ≠ [])
    (root : Option P) (mm : ℕ) (a : M.SA.V mm) (b : M.SB.V mm)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "cs" => ChainSide.chain Γ mark h2 side
local notation "vs" => ChainSide.vertex Γ mark h2 side paths
local notation "first" => ChainActiveStages.first Γ mark h2 paths
local notation "last" => ChainActiveStages.last Γ mark h2 paths
local notation "hf" => ChainSide.active_first Γ mark h2 side paths
local notation "hl" => ChainSide.active_last Γ mark h2 side hsid paths

abbrev pinA (j : ℕ) :=
  RootPins.pin (SidePins.root (vs j) (StageRoot.vertex Γ mark h2 paths hp root j) true) a
abbrev pinB (j : ℕ) :=
  RootPins.pin (SidePins.root (vs j) (StageRoot.vertex Γ mark h2 paths hp root j) false) b

abbrev A (j : ℕ) : TwoSideStage.Side M :=
  StagePartition.sideA M len m cs j M.SA.flip (M.SA.col mm)
    (firstPoint m j cs (vs j) (first j) (hf j) true)
    (lastPoint m j cs (vs j) (last j) (hl j) true)
    (M.SA.out mm) (pinA M Γ mark h2 side paths hp root mm a j)

abbrev B (j : ℕ) : TwoSideStage.Side M :=
  StagePartition.sideB M len m cs j M.SB.flip (M.SB.col mm)
    (firstPoint m j cs (vs j) (first j) (hf j) false)
    (lastPoint m j cs (vs j) (last j) (hl j) false)
    (M.SB.out mm) (pinB M Γ mark h2 side paths hp root mm b j)
local notation "SA" => A M Γ mark h2 side hsid paths hp root mm a
local notation "SB" => B M Γ mark h2 side hsid paths hp root mm b

lemma power_eq (j : ℕ) :
    ((((SA j).freeMarks + (SB j).freeMarks : ℕ) : ℝ) -
      (Fintype.card (SA j).C + Fintype.card (SB j).C : ℕ)) =
        (StageRoot.power Γ mark h2 paths hp vs root a b j : ℝ) := by
  have hc := chain_card m j cs
  unfold StageRoot.power
  dsimp only [TwoSideStage.Side.freeMarks, A, B, StagePartition.sideA, StagePartition.sideB]
  rw [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast,
    Nat.cast_add, ← hc]
  rfl

lemma edges_eq (j : ℕ) : (SA j).edges + (SB j).edges =
    ∑ c : {c : R // j < m c}, len c.val := by
  change (∑ c : {c : R // j < m c ∧ cs c = true}, len c.val) +
    (∑ c : {c : R // j < m c ∧ cs c = false}, len c.val) = _
  rw [← Finset.sum_subtype (Finset.univ.filter fun c => j < m c ∧ cs c = true) (by simp),
    ← Finset.sum_subtype (Finset.univ.filter fun c => j < m c ∧ cs c = false) (by simp),
    ← Finset.sum_subtype (Finset.univ.filter fun c => j < m c) (by simp)]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  cases cs c <;> simp

lemma edges_bound (j : ℕ) :
    ((SA j).edges + (SB j).edges : ℝ) ≤ OAI.TorsionFreeZeroDivisors.StageMass.totalLength len m := by
  rw [← Nat.cast_add, edges_eq, OAI.TorsionFreeZeroDivisors.StageMass.totalLength_eq]
  rw [← Finset.sum_subtype (Finset.univ.filter fun c => j < m c) (by simp)]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with hc
  · have h : (1 : ℝ) ≤ m c := by exact_mod_cast (show 1 ≤ m c by omega)
    nlinarith [show (0 : ℝ) ≤ len c from Nat.cast_nonneg (len c)]
  · positivity

lemma marked_card (j : ℕ) (b' : Bool) :
    Fintype.card {v : ActiveV (suppressed Γ mark h2) (ListStageExponents.mult
        (suppressed Γ mark h2) paths) j // vs j v = b'} ≤ Fintype.card (Mark mark) := by
  apply le_trans (Fintype.card_subtype_le _)
  refine Fintype.card_le_of_injective (fun v => (⟨v.val, ?_⟩ : Mark mark))
    (fun v w h => Subtype.ext (by simpa using congrArg Subtype.val h))
  obtain ⟨d, hd, _⟩ := v.property
  rw [← hd]
  exact (turn_fixed_iff Γ.origin mark h2 d.val).mp d.property

variable {E : Type}

def count (s : ℝ) (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (j : ℕ) : (SA j).Match × (SB j).Match → ℕ :=
  TwoSideStage.count (SA j) (SB j) (ChainStageLabels.fullWords M s len m j cmp d)
    (StagePartition.restrictA M len m cs j) (StagePartition.restrictB M len m cs j)

/-- Restricting actual coloured embeddings on the two prescribed sides witnesses the joint
stage count, with a single global label projection. -/
theorem count_pos (s : ℝ) (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (j : ℕ) (label : D → M.α)
    (hlabel : ∀ x, label (Γ.reverse x) = M.inv (label x))
    (pinA' : SideRestriction.Vertex side true → Option (M.SA.V mm))
    (pinB' : SideRestriction.Vertex side false → Option (M.SB.V mm))
    (r : (SA j).Match × (SB j).Match)
    (eA : CEmb (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (M.SA.col mm) (M.SA.out mm) pinA' (cbar M.inv M.SA.flip) r.1)
    (eB : CEmb (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (M.SB.col mm) (M.SB.out mm) pinB' (cbar M.inv M.SB.flip) r.2)
    (hpa : ∀ v y, pinA M Γ mark h2 side paths hp root mm a j v = some y →
      pinA' ⟨v.val.val, v.property⟩ = some y)
    (hpb : ∀ v y, pinB M Γ mark h2 side paths hp root mm b j v = some y →
      pinB' ⟨v.val.val, v.property⟩ = some y)
    (hw : ActualStageRealization.word M Γ mark h2 paths j label ∈
      ChainStageLabels.fullWords M s len m j cmp d) :
    0 < count M Γ mark h2 side hsid paths hp root mm a b s cmp d j r := by
  exact TwoSideStage.count_pos (SA j) (SB j) _ _ _ r _ hw
    (ActualSideRealization.embedding M Γ mark h2 side hsid paths j true label
      (M.SA.col mm) (M.SA.out mm) pinA' _ r.1 eA hlabel _ hpa)
    (ActualSideRealization.embedding M Γ mark h2 side hsid paths j false label
      (M.SB.col mm) (M.SB.out mm) pinB' _ r.2 eB hlabel _ hpb)

/-- The rooted, mixed-side, coloured stage first moment. -/
theorem mean_bound (s : ℝ) (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (hs : 0 < s) (j err K Q : ℕ)
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val))
    (hn : 0 < M.n mm)
    (hr : K * M.L mm + M.exclusion mm < M.carrier mm)
    (hQ : Fintype.card R ≤ Q) (hMark : Fintype.card (Mark mark) ≤ Q)
    (hH : OAI.TorsionFreeZeroDivisors.StageMass.totalLength len m ≤ K * (M.L mm : ℝ)) :
    TwoSideMean.mean (((SA j).samples (3 * M.L mm)) ×ˢ ((SB j).samples (3 * M.L mm)))
      (count M Γ mark h2 side hsid paths hp root mm a b s cmp d j) ≤
    Real.exp ((StageRoot.power Γ mark h2 paths hp vs root a b j : ℝ) * Real.log (M.n mm) +
      StageEntropy.labelCost M s hs len m cmp err d j + StageEntropy.looseCost M s len err +
        StageDenominator.error M K Q mm) := by
  have hE : (SA j).edges + (SB j).edges ≤ K * M.L mm := by
    exact_mod_cast (edges_bound M Γ mark h2 side hsid paths hp root mm a b j).trans hH
  have hA := StageDenominator.conditionsA M K mm hr (SA j).len (SA j).first (SA j).last (SA j).pin
    ((Nat.le_add_right _ _).trans hE)
  have hB := StageDenominator.conditionsB M K mm hr (SB j).len (SB j).first (SB j).last (SB j).pin
    ((Nat.le_add_left _ _).trans hE)
  have hq : Fintype.card (OAI.TorsionFreeZeroDivisors.StagePartition.CA m cs j) +
      Fintype.card (OAI.TorsionFreeZeroDivisors.StagePartition.CB m cs j) ≤ Q := by
    rw [chain_card]
    apply le_trans _ hQ
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have h := PartitionEntropy.mean_bound M s hs len m cs j M.SA.flip M.SB.flip
    (M.SA.col mm) (M.SB.col mm)
    (SA j).first (SA j).last (SB j).first (SB j).last
    (M.SA.out mm) (M.SB.out mm) (SA j).pin (SB j).pin cmp d err K Q mm
    hlarge hscale hreduced hn (Nat.sub_pos_of_lt hr) hA hB
    (fun c => chainLength_pos Γ mark h2 c.val) hq
    ((marked_card Γ mark h2 side paths j true).trans hMark)
    ((marked_card Γ mark h2 side paths j false).trans hMark) rfl rfl hE
  change TwoSideMean.mean _ (count M Γ mark h2 side hsid paths hp root mm a b s cmp d j) ≤
    Real.exp (((((SA j).freeMarks + (SB j).freeMarks : ℕ) : ℝ) -
      (Fintype.card (SA j).C + Fintype.card (SB j).C : ℕ)) * Real.log (M.n mm) +
      StageEntropy.labelCost M s hs len m cmp err d j + StageEntropy.looseCost M s len err +
        StageDenominator.error M K Q mm) at h
  rw [power_eq] at h
  exact h

end ActualStagePair

namespace ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs
open ComparedBlocks RepeatedBlocks

/-- The sample space: one girth-conditioned matching on each side. -/
abbrev Match (M : Model) (mm : ℕ) := M.SA.Match mm × M.SB.Match mm

def samples (M : Model) (mm : ℕ) : Finset (Match M mm) := M.samplesA mm ×ˢ M.samplesB mm

private lemma mem_profiles_iff (M : Model) {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)
    (d : Underlying s len → ℤ) :
    d ∈ BinProfiles.profiles M s len ↔ ∀ i, d i ∈ BinProfiles.values M s := by
  unfold BinProfiles.profiles
  exact Fintype.mem_piFinset

variable (M : Model) {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card = 2)
    (side : V → Bool) (hsid : ∀ x, side (Γ.origin (Γ.reverse x)) = side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x = x}) (hp : ∀ p, paths p ≠ [])
    (root : Option P) (mm : ℕ) (a : M.SA.V mm) (b : M.SB.V mm)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "vs" => ChainSide.vertex Γ mark h2 side paths
local notation "SA" => ActualStagePair.A M Γ mark h2 side hsid paths hp root mm a
local notation "SB" => ActualStagePair.B M Γ mark h2 side hsid paths hp root mm b

lemma samples_eq (j : ℕ) : samples M mm =
    (SA j).samples (3 * M.L mm) ×ˢ (SB j).samples (3 * M.L mm) := by
  ext r
  dsimp only [ActualStagePair.A, ActualStagePair.B, StagePartition.sideA, StagePartition.sideB,
    TwoSideStage.Side.samples]
  simp only [samples, Model.samplesA, Model.samplesB, Side.samples,
    ConditionedMatchings.Matching.conditioned, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and]
  erw [Finset.mem_product]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  try rfl

abbrev sourcePinA := RootPins.pin
  (SidePins.root side (StageRoot.source Γ mark h2 paths hp root) true) a
abbrev sourcePinB := RootPins.pin
  (SidePins.root side (StageRoot.source Γ mark h2 paths hp root) false) b

/-- Realization of an enlarged fixed pattern and its bin profile. -/
def Occurs (s : ℝ) (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match M mm) : Prop :=
  ∃ label : D → M.α,
    (∀ x, label (Γ.reverse x) = M.inv (label x)) ∧
    (∀ x y, Γ.origin x = Γ.origin y → label x = label y → x = y) ∧
    ActualStageLabels.Comparing M len m cmp (ActualStageFeasibility.globalWord M Γ mark h2 label) ∧
    ActualStageFeasibility.bins M s len (ActualStageFeasibility.globalWord M Γ mark h2 label) = d ∧
    CEmb (SideRestriction.graph Γ side hsid true) (fun x => label x.val) (M.SA.col mm)
      (M.SA.out mm) (sourcePinA M Γ mark h2 side paths hp root mm a) (cbar M.inv M.SA.flip) r.1 ∧
    CEmb (SideRestriction.graph Γ side hsid false) (fun x => label x.val) (M.SB.col mm)
      (M.SB.out mm) (sourcePinB M Γ mark h2 side paths hp root mm b) (cbar M.inv M.SB.flip) r.2

theorem count_pos (s : ℝ) (hs : 0 < s) (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match M mm)
    (hr : Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d r) (j : ℕ) :
    0 < ActualStagePair.count M Γ mark h2 side hsid paths hp root mm a b s cmp d j r := by
  rcases hr with ⟨label, hl, hi, hc, hd, eA, eB⟩
  apply ActualStagePair.count_pos M Γ mark h2 side hsid paths hp root mm a b s cmp d j label hl
    _ _ r eA eB
    (StageRoot.pin_compatible Γ mark h2 paths hp side root a true j)
    (StageRoot.pin_compatible Γ mark h2 paths hp side root b false j)
  have hw := ActualStageFeasibility.fullWords_of_comparing M s len m cmp j
    (ActualStageFeasibility.globalWord M Γ mark h2 label) hc
    (ActualStageFeasibility.immersed M s Γ mark h2 hs label hl hi)
  rw [hd] at hw
  exact hw

omit [Fintype V] in
theorem bin_bounds (s : ℝ) (hs : 0 < s) (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match M mm)
    (hr : Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d r)
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hscale' : ∀ i, (height s len i : ℝ) ≤ 2 * s) :
    (∀ i, (1 / (M.D : ℝ)) * s / 2 ≤ d i) ∧ (∀ i, (d i : ℝ) ≤ M.A₀ * s) := by
  rcases hr with ⟨label, hl, hi, _hc, hd, _⟩
  have hb := ActualStageFeasibility.mem_bin M s len
    (ActualStageFeasibility.globalWord M Γ mark h2 label)
    (ActualStageFeasibility.immersed M s Γ mark h2 hs label hl hi)
  rw [hd] at hb
  have h i := Alphabet.bin_full_bounds M.D_pos M.decays (M.A₀ : ℝ) M.A₀_ge (height s len i)
    (hlarge i) s (hscale i) (hscale' i) (d i) _ (hb i)
  exact ⟨fun i => (h i).1, fun i => (h i).2.1⟩

def Unbinned (s : ℝ) (cmp : Comparisons (E := E) (traversalLength len m))
    (r : Match M mm) : Prop :=
  ∃ d, Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d r

omit [Fintype V] in
lemma occurs_profile (s : ℝ) (hs : (M.smin : ℝ) ≤ s)
    (cmp : Comparisons (E := E) (traversalLength len m)) (d : Underlying s len → ℤ)
    (r : Match M mm) (hr : Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d r) :
    d ∈ BinProfiles.profiles M s len := by
  classical
  have hsm1 : ((M.h₀ + 1 : ℕ) : ℝ) ≤ s := le_trans (by exact_mod_cast le_max_left _ _) hs
  have hsm2 : ((2 * M.D + 2 : ℕ) : ℝ) ≤ s := le_trans (by exact_mod_cast le_max_right _ _) hs
  push_cast at hsm1 hsm2
  have hh (i : Underlying s len) :=
    OAI.TorsionFreeZeroDivisors.BinProfiles.height_bounds s (by linarith) len i
  have hl (i : Underlying s len) : M.h₀ ≤ height s len i := by
    have h : (M.h₀ : ℝ) ≤ height s len i := by linarith [hh i]
    exact_mod_cast h
  obtain ⟨hlo, hhi⟩ := bin_bounds M Γ mark h2 side hsid paths hp root mm a b s (by linarith)
    cmp d r hr hl (fun i => by linarith [hh i]) (fun i => by linarith [hh i])
  apply (mem_profiles_iff M s len d).mpr
  intro i
  exact Finset.mem_Icc.mpr ⟨by
    have h : (0 : ℝ) ≤ d i := (div_nonneg (mul_nonneg M.δ_pos.le (by linarith)) (by norm_num) :
      (0 : ℝ) ≤ (1 / (M.D : ℝ)) * s / 2).trans (hlo i)
    exact_mod_cast h, Int.le_floor.mpr (hhi i)⟩

omit [Fintype V] in
lemma unbinned_iff_profile (s : ℝ) (hs : (M.smin : ℝ) ≤ s)
    (cmp : Comparisons (E := E) (traversalLength len m)) (r : Match M mm) :
    Unbinned M Γ mark h2 side hsid paths hp root mm a b s cmp r ↔
      ∃ d : {d // d ∈ BinProfiles.profiles M s len},
        Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d.val r := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨⟨d, occurs_profile M Γ mark h2 side hsid paths hp root mm a b s hs cmp d r hd⟩, hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d.val, hd⟩

variable [Fintype E]
open OAI.TorsionFreeZeroDivisors.StageMass (totalLength uncovered totalLength_eq)

/-- One realized fixed-bin pattern is exponentially unlikely. -/
theorem probability_bound (s : ℝ) (hs : 0 < s)
    (cmp : Comparisons (E := E) (traversalLength len m)) (d : Underlying s len → ℤ)
    (err K Q Mst : ℕ) (hM : 0 < Mst) (hm : ∀ c, m c ≤ Mst)
    (hc : ∀ i, (paths i).IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse))
    (hclose : ∀ i, StageRoot.cyclic root i = true →
      ∀ᵉ (x ∈ (paths i).getLast?) (y ∈ (paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hscale' : ∀ i, (height s len i : ℝ) ≤ 2 * s)
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val))
    (hn : 1 ≤ M.n mm)
    (hr : K * M.L mm + M.exclusion mm < M.carrier mm)
    (hQ : Fintype.card R ≤ Q) (hMark : Fintype.card (Mark mark) ≤ Q)
    (hH : totalLength len m ≤ K * (M.L mm : ℝ))
    (ν : E → ℤ) (hsmall : 2 * (err : ℝ) < s - 1)
    (herr : ∀ e, 2 * |(cmp.offset e : ℝ) - (ν e : ℝ) * s| + 4 ≤ err)
    (hb : (uncovered s hs len m cmp err : ℝ) ≤ M.ε * totalLength len m)
    (he : StageMass.residual M (E := E) s len m err Mst Q (StageDenominator.error M K Q mm) ≤
      totalLength len m / (8 * M.D)) :
    (((samples M mm).filter (Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d)).card : ℝ) /
      (samples M mm).card ≤ Real.exp (-totalLength len m / (4 * M.D * Mst)) := by
  by_cases hex : ∃ r, Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d r
  · rcases hex with ⟨r, hr'⟩
    obtain ⟨hlow, hhigh⟩ := bin_bounds M Γ mark h2 side hsid paths hp root mm a b s hs cmp d
      r hr' hlarge hscale hscale'
    have hpw := StageRoot.power_nonpos Γ mark h2 paths hp vs root a b hc hclose Mst hM hm
    have hlgn : 0 ≤ Real.log (M.n mm) := Real.log_nonneg hn
    have hprod := StageMass.decay M s hs len m cmp err Mst Q hm hQ ν hsmall herr d hlow hhigh
      (Real.log (M.n mm)) (StageDenominator.error M K Q mm) hlgn
      (fun j : Fin Mst => (StageRoot.power Γ mark h2 paths hp vs root a b j.val : ℝ)) hpw hb he
    have h := StageFusion.one_pattern (samples M mm) Mst hM
      (Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d)
      (fun j : Fin Mst => ActualStagePair.count M Γ mark h2 side hsid paths hp root mm a b s cmp d j.val)
      (fun j : Fin Mst => (StageRoot.power Γ mark h2 paths hp vs root a b j.val : ℝ) *
        Real.log (M.n mm) + StageEntropy.labelCost M s hs len m cmp err d j.val +
          (StageEntropy.looseCost M s len err + StageDenominator.error M K Q mm))
      (totalLength len m / (4 * M.D))
      (fun j r _hr hr' => count_pos M Γ mark h2 side hsid paths hp root mm a b s hs cmp d r hr' j.val)
      (fun j => by
        have hmom := ActualStagePair.mean_bound M Γ mark h2 side hsid paths hp root mm a b
          s cmp d hs j err K Q hlarge hscale hreduced (by linarith) hr hQ hMark hH
        rw [← samples_eq M Γ mark h2 side hsid paths hp root mm a b j] at hmom
        convert hmom using 1
        congr 1; ring)
      (by
        have : -(totalLength len m / (4 * M.D)) = -totalLength len m / (4 * M.D) := by ring
        rw [this]; exact hprod)
    convert h using 1
    congr 1
    have hD := M.D_pos'
    field_simp
  · have hf : (samples M mm).filter (Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      exact fun _ => fun hr' => hex ⟨r, hr'⟩
    rw [hf, Finset.card_empty, Nat.cast_zero, zero_div]
    exact (Real.exp_pos _).le

/-- Union over all weight bins of an actual pattern. -/
theorem unbinned_probability_bound (s : ℝ) (hs : 0 < s) (hslarge : (M.smin : ℝ) ≤ s)
    (cmp : Comparisons (E := E) (traversalLength len m))
    (err K Q Mst : ℕ) (hM : 0 < Mst) (hm : ∀ c, m c ≤ Mst)
    (hc : ∀ i, (paths i).IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse))
    (hclose : ∀ i, StageRoot.cyclic root i = true →
      ∀ᵉ (x ∈ (paths i).getLast?) (y ∈ (paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hscale' : ∀ i, (height s len i : ℝ) ≤ 2 * s)
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val))
    (hn : 1 ≤ M.n mm)
    (hr : K * M.L mm + M.exclusion mm < M.carrier mm)
    (hQ : Fintype.card R ≤ Q) (hMark : Fintype.card (Mark mark) ≤ Q)
    (hH : totalLength len m ≤ K * (M.L mm : ℝ))
    (ν : E → ℤ) (hsmall : 2 * (err : ℝ) < s - 1)
    (herr : ∀ e, 2 * |(cmp.offset e : ℝ) - (ν e : ℝ) * s| + 4 ≤ err)
    (hb : (uncovered s hs len m cmp err : ℝ) ≤ M.ε * totalLength len m)
    (he : StageMass.residual M (E := E) s len m err Mst Q (StageDenominator.error M K Q mm) ≤
      totalLength len m / (8 * M.D))
    (hpositive : ∀ c, 1 ≤ m c)
    (hbins : Real.log (M.A₀ * s + 1) / s ≤ 1 / (8 * M.D * Mst : ℝ)) :
    (((samples M mm).filter (Unbinned M Γ mark h2 side hsid paths hp root mm a b s cmp)).card : ℝ) /
      (samples M mm).card ≤ Real.exp (-totalLength len m / (8 * M.D * Mst)) := by
  let H := totalLength len m
  have hD := M.D_pos'
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsum : (∑ c : R, (len c : ℝ)) ≤ H := by
    unfold H
    rw [totalLength_eq]
    apply Finset.sum_le_sum
    intro c _
    have hp : (1 : ℝ) ≤ m c := by exact_mod_cast hpositive c
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (len c) : (0 : ℝ) ≤ len c)
  have hA := M.A₀_nonneg
  have hcard : ((BinProfiles.profiles M s len).card : ℝ) ≤ Real.exp (H / (8 * M.D * Mst)) := by
    apply (BinProfiles.cardinal_bound M s hs len).trans
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (H / s) * Real.log (M.A₀ * s + 1) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hsum hs.le) (Real.log_nonneg (by nlinarith))
      _ = H * (Real.log (M.A₀ * s + 1) / s) := by ring
      _ ≤ H * (1 / (8 * M.D * Mst)) := mul_le_mul_of_nonneg_left hbins hH0
      _ = H / (8 * M.D * Mst) := by ring
  let Profiles := {d // d ∈ BinProfiles.profiles M s len}
  have hB (d : Profiles) := probability_bound M Γ mark h2 side hsid paths hp root mm a b
    s hs cmp d.val err K Q Mst hM hm hc hclose hlarge hscale hscale' hreduced hn hr hQ hMark hH
    ν hsmall herr hb he
  have hu : (((samples M mm).filter
      (Unbinned M Γ mark h2 side hsid paths hp root mm a b s cmp)).card : ℝ) / (samples M mm).card ≤
        ((BinProfiles.profiles M s len).card : ℝ) * Real.exp (-H / (4 * M.D * Mst)) := by
    by_cases hsamp : (samples M mm).Nonempty
    · have h := StageFusion.pattern_union (samples M mm) hsamp
        (fun d : Profiles => Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d.val)
        (Real.exp (-H / (4 * M.D * Mst))) hB
      have heq : (samples M mm).filter (Unbinned M Γ mark h2 side hsid paths hp root mm a b s cmp) =
          (samples M mm).filter (fun r => ∃ d : Profiles,
            Occurs M Γ mark h2 side hsid paths hp root mm a b s cmp d.val r) := by
        ext r
        simp only [Finset.mem_filter]
        exact and_congr_right (fun _ => unbinned_iff_profile M Γ mark h2 side hsid paths hp root
          mm a b s hslarge cmp r)
      rw [heq]
      convert h using 1
      congr 1
      exact_mod_cast (Fintype.card_coe (BinProfiles.profiles M s len)).symm
    · have heq := Finset.not_nonempty_iff_eq_empty.mp hsamp
      rw [heq, Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  calc
    _ ≤ ((BinProfiles.profiles M s len).card : ℝ) * Real.exp (-H / (4 * M.D * Mst)) := hu
    _ ≤ Real.exp (H / (8 * M.D * Mst)) * Real.exp (-H / (4 * M.D * Mst)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (-H / (8 * M.D * Mst)) := by
      rw [← Real.exp_add]; congr 1
      have hMst : (0 : ℝ) < Mst := by exact_mod_cast hM
      field_simp
      ring

end ActualPatternEvent

end

end Kaplansky.Random
