import Kaplansky.Random.Chain.Transport
import OAI.Algebra.GroupRing.PartitionEntropy

/-!
# Fork of the model-dependent parts of `PartitionEntropy.lean`

`PartitionEntropy.mean_bound` with the model's denominator, colours and scale;
`StageSideEmbedding.restrictWord`, `label_map`; and `ActualSideRealization.word`, `label_eq`,
`embedding` for coloured embeddings (`CEmb`).
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

namespace PartitionEntropy
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
open OAI.TorsionFreeZeroDivisors.ChainStageLabels (StagePosition activeBlocks)
open OAI.TorsionFreeZeroDivisors.StagePartition (CA CB)
variable (M : Model) {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB] [DecidableEq TA] [DecidableEq TB]
variable (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)
variable {ColA ColB : Type} [Fintype ColA] [DecidableEq ColA] [Fintype ColB] [DecidableEq ColB]
  (flipA : ColA → ColA) (flipB : ColB → ColB) (colA : TA → ColA) (colB : TB → ColB)
  (firstA lastA : CA m side j → VA) (firstB lastB : CB m side j → VB)
  (outA : TA → Finset M.α) (outB : TB → Finset M.α)
  (pinA : VA → Option TA) (pinB : VB → Option TB)
local notation "SA" => StagePartition.sideA M len m side j flipA colA firstA lastA outA pinA
local notation "SB" => StagePartition.sideB M len m side j flipB colB firstB lastB outB pinB

/-- A complete stage first moment with its signed vertex exponent. -/
theorem mean_bound (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (err K Q mm : ℕ)
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val))
    (hn : 0 < M.n mm) (hr : 0 < StageDenominator.denominator M K mm)
    (hA : TwoSideStage.Conditions SA (M.n mm) M.p (3 * M.L mm) M.dmax
      (StageDenominator.denominator M K mm))
    (hB : TwoSideStage.Conditions SB (M.n mm) M.p (3 * M.L mm) M.dmax
      (StageDenominator.denominator M K mm))
    (hlen : ∀ c, 0 < len c) (hQ : Fintype.card (CA m side j) + Fintype.card (CB m side j) ≤ Q)
    (hVA : Fintype.card VA ≤ Q) (hVB : Fintype.card VB ≤ Q)
    (hColA : Fintype.card ColA = Fintype.card M.SA.Col)
    (hColB : Fintype.card ColB = Fintype.card M.SB.Col)
    (hE : (SA).edges + (SB).edges ≤ K * M.L mm) :
    TwoSideMean.mean (((SA).samples (3 * M.L mm)) ×ˢ ((SB).samples (3 * M.L mm)))
      (TwoSideStage.count SA SB (ChainStageLabels.fullWords M s len m j cmp d)
        (StagePartition.restrictA M len m side j) (StagePartition.restrictB M len m side j)) ≤
      Real.exp (((((SA).freeMarks + (SB).freeMarks : ℕ) : ℝ) -
        (Fintype.card (CA m side j) + Fintype.card (CB m side j) : ℕ)) * Real.log (M.n mm) +
          StageEntropy.labelCost M s hs len m cmp err d j + StageEntropy.looseCost M s len err +
            StageDenominator.error M K Q mm) := by
  have hm := StagePartition.mean_bound M s hs len m side j flipA flipB colA colB
    firstA lastA firstB lastB outA outB pinA pinB cmp d err hlarge hscale hreduced
    (M.n mm) M.p _ M.dmax _ hA hB
  have hc := StageDenominator.joint_cost_bound M SA SB K Q mm hn hr
    (fun c => hlen c.val) (fun c => hlen c.val) hQ hVA hVB hColA hColB hE
  apply hm.trans
  apply (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  have e1 : Fintype.card (SA).C = Fintype.card (CA m side j) := rfl
  have e2 : Fintype.card (SB).C = Fintype.card (CB m side j) := rfl
  rw [e1, e2]
  unfold StageEntropy.labelCost StageEntropy.looseCost
  ring

end PartitionEntropy

namespace StageSideEmbedding
open scoped Classical BigOperators
open ChainSubdivision
open OAI.TorsionFreeZeroDivisors.StageSideEmbedding (length dart)
variable (M : Model) {C V : Type} (len m : C → ℕ) (j : ℕ) (side : C → Bool) (b : Bool)

/-- Restriction of a full stage string to this prescribed side. -/
def restrictWord (F : ComparedBlocks.Position
      (OAI.TorsionFreeZeroDivisors.StageExpectation.activeLen len m j) → M.α) :
    ComparedBlocks.Position (length len m j side b) → M.α :=
  fun x => F ⟨⟨x.1.val, x.1.property.1⟩, x.2⟩

lemma label_map (F : ComparedBlocks.Position
      (OAI.TorsionFreeZeroDivisors.StageExpectation.activeLen len m j) → M.α)
    (d : ChainSubdivision.Dart (length len m j side b)) :
    ChainRealization.label M (length len m j side b)
      (StageExpectation.readWord M (length len m j side b) (restrictWord M len m j side b F)) d =
    ChainRealization.label M (OAI.TorsionFreeZeroDivisors.StageExpectation.activeLen len m j)
      (StageExpectation.readWord M (OAI.TorsionFreeZeroDivisors.StageExpectation.activeLen len m j) F)
      (dart len m j side b d) := by
  rcases d with ⟨⟨c, i⟩, r⟩
  cases r <;> rfl

end StageSideEmbedding

namespace ActualSideRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons StageSubgraphs
open OAI.TorsionFreeZeroDivisors.ActualSideRealization (length Marked graph vertexMap dartMap
  vertex_injective dart_injective origin_map reverse_map vertex_side)
variable (M : Model) {V D : Type} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card = 2)
    (side : V → Bool) (hs : ∀ d, side (Γ.origin (Γ.reverse d)) = side (Γ.origin d))
    {P : Type} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d = d}) (j : ℕ)
    (b : Bool)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "cs" => ChainSide.chain Γ mark h2 side
local notation "Q" => graph Γ mark h2 side hs paths j b
local notation "l" => length Γ mark h2 side paths j b

def word (label : D → M.α) : ComparedBlocks.Position l → M.α :=
  StageSideEmbedding.restrictWord M len m j cs b (ActualStageRealization.word M Γ mark h2 paths j label)

lemma label_eq (label : D → M.α) (hlabel : ∀ d, label (Γ.reverse d) = M.inv (label d))
    (d : ChainSubdivision.Dart l) :
    ChainRealization.label M l (StageExpectation.readWord M l (word M Γ mark h2 side paths j b label)) d =
      label (dartMap Γ mark h2 side paths j b d) := by
  rw [show word M Γ mark h2 side paths j b label = StageSideEmbedding.restrictWord M len m j cs b
    (ActualStageRealization.word M Γ mark h2 paths j label) from rfl,
    StageSideEmbedding.label_map]
  exact ActualStageRealization.label_eq M Γ mark h2 paths j label hlabel _

variable [Fintype V] {TV Col : Type} [Fintype TV] [Fintype Col]
    (label : D → M.α) (col : TV → Col) (out : TV → Finset M.α)
    (pin : SideRestriction.Vertex side b → Option TV) (bar : M.α × Col → M.α × Col)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label (cout col out)) bar)

/-- The realization of a prescribed-side active stage follows from a coloured embedding of the
original prescribed side; all labels are restrictions of one global word. -/
theorem embedding (e : CEmb (SideRestriction.graph Γ side hs b) (fun d => label d.val)
      col out pin bar r)
    (hlabel : ∀ d, label (Γ.reverse d) = M.inv (label d))
    (pin' : Marked Γ mark h2 side paths j b → Option TV)
    (hp : ∀ v y, pin' v = some y → pin ⟨v.val.val, v.property⟩ = some y) :
    CEmb (Q) (ChainRealization.label M l (StageExpectation.readWord M l
        (word M Γ mark h2 side paths j b label)))
      col out (OAI.TorsionFreeZeroDivisors.ChainRealization.pin l pin') bar r := by
  let fv : ChainSubdivision.Vertex l ↪ V :=
    ⟨vertexMap Γ mark h2 side paths j b, vertex_injective Γ mark h2 side paths j b⟩
  let fd : ChainSubdivision.Dart l ↪ D :=
    ⟨dartMap Γ mark h2 side paths j b, dart_injective Γ mark h2 side paths j b⟩
  have hp' : ∀ v y, OAI.TorsionFreeZeroDivisors.ChainRealization.pin l pin' v = some y →
      pin (SideRestriction.vertex side b fv (vertex_side Γ mark h2 side hs paths j b) v) = some y := by
    intro v y hy
    cases v with
    | inl v => exact hp v y hy
    | inr v => cases hy
  apply CEmb.congrLabel _ _ (label_eq M Γ mark h2 side paths j b label hlabel)
  exact e.restrict (Q) (SideRestriction.vertex side b fv (vertex_side Γ mark h2 side hs paths j b))
    (SideRestriction.dart Γ side b (Q) fv fd (origin_map Γ mark h2 side hs paths j b)
      (vertex_side Γ mark h2 side hs paths j b))
    (SideRestriction.origin_map Γ side hs b (Q) fv fd (origin_map Γ mark h2 side hs paths j b)
      (vertex_side Γ mark h2 side hs paths j b))
    (SideRestriction.reverse_map Γ side hs b (Q) fv fd (origin_map Γ mark h2 side hs paths j b)
      (reverse_map Γ mark h2 side hs paths j b) (vertex_side Γ mark h2 side hs paths j b))
    _ hp'

end ActualSideRealization

end

end Kaplansky.Random
