import Kaplansky.Random.Chain.StageEntropy
import OAI.Algebra.GroupRing.RealizationTransport

/-!
# Fork of `RealizationTransport.lean` and `PartitionEntropy.lean` (model-dependent parts)

* `CEmb`: an embedding of an uncoloured pattern into a coloured side.  It is OpenAI's
  `RealizationTransport.Embedding` for the coloured labels `(label d, κ (origin d))`, for some
  vertex colouring `κ`.  For a one-colour side `κ` is unique.
* Colours alternate along every realized chain (`vcol_eq`), because matchings join inverse
  coloured ports.  This turns an actual embedding into a term of the colour-summed stage count
  (`TwoSideStage.count_pos`).
* Forks of `ActualStageRealization`, `ActualStageFeasibility`, `StagePartition`,
  `PartitionEntropy.mean_bound`, `StageSideEmbedding.restrictWord` and `ActualSideRealization`
  over `M.α` (OpenAI's `signedLetter` bridge disappears).
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

/-! ### Coloured embeddings -/

section CEmb
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {α PV PD TV Col : Type} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype α] [Fintype Col]

/-- An embedding of an uncoloured pattern into a coloured side, for some vertex colouring. -/
def CEmb (Γ : PortGraph PV PD) (plabel : PD → α) (col : TV → Col) (out : TV → Finset α)
    (pin : PV → Option TV) (bar : α × Col → α × Col)
    (r : Matching (label (cout col out)) bar) : Prop :=
  ∃ κ : PV → Col, Nonempty (RealizationTransport.Embedding Γ
    (fun d => (plabel d, κ (Γ.origin d))) (cout col out) pin bar r)

variable {Γ : PortGraph PV PD} {plabel : PD → α} {col : TV → Col} {out : TV → Finset α}
    {pin : PV → Option TV} {bar : α × Col → α × Col} {r : Matching (label (cout col out)) bar}

theorem CEmb.restrict {QV QD : Type} [Fintype QV] [Fintype QD]
    (e : CEmb Γ plabel col out pin bar r) (Q : PortGraph QV QD) (fv : QV ↪ PV) (fd : QD ↪ PD)
    (ho : ∀ d, fv (Q.origin d) = Γ.origin (fd d))
    (hr : ∀ d, fd (Q.reverse d) = Γ.reverse (fd d)) (pin' : QV → Option TV)
    (hp : ∀ v y, pin' v = some y → pin (fv v) = some y) :
    CEmb Q (plabel ∘ fd) col out pin' bar r := by
  obtain ⟨κ, ⟨e⟩⟩ := e
  refine ⟨κ ∘ fv, ⟨RealizationTransport.congrLabel
    (RealizationTransport.restrict e Q fv fd ho hr pin' hp) _ ?_⟩⟩
  intro d
  simp only [Function.comp_apply, ho]

theorem CEmb.congrLabel (e : CEmb Γ plabel col out pin bar r) (label' : PD → α)
    (hl : ∀ d, label' d = plabel d) : CEmb Γ label' col out pin bar r := by
  obtain ⟨κ, ⟨e⟩⟩ := e
  exact ⟨κ, ⟨RealizationTransport.congrLabel e _ (fun d => by simp only [hl])⟩⟩

theorem CEmb.immersed (e : CEmb Γ plabel col out pin bar r) :
    Function.Injective (fun d => (Γ.origin d, plabel d)) := by
  obtain ⟨κ, ⟨e⟩⟩ := e
  intro d f h
  apply RealizationTransport.immersed e
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only at h1 h2
  simp only [h1, h2]

end CEmb

/-- An embedding transports the matching relation to its labels. -/
theorem embedding_label_reverse {PV PD TV T : Type} [Fintype PV] [Fintype PD] [Fintype TV]
    [Fintype T] {Γ : PortSubdivision.PortGraph PV PD} {plabel : PD → T}
    {outgoing : TV → Finset T} {pin : PV → Option TV} {bar : T → T}
    {r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar}
    (e : RealizationTransport.Embedding Γ plabel outgoing pin bar r) (d : PD) :
    plabel (Γ.reverse d) = bar (plabel d) := by
  rw [← e.label_eq, ← e.label_eq, ← e.reverse_eq]
  exact r.label_reverse (e.port d)

/-! ### Colours alternate along realized chains -/

section Alternation
open ChainSubdivision
variable {C V Col : Type} (len : C → ℕ) (first last : C → V) (flip : Col → Col)

theorem point_colour (κ : Vertex len (V := V) → Col)
    (hrev : ∀ d : Dart len, κ ((graph len first last).origin ((graph len first last).reverse d)) =
      flip (κ ((graph len first last).origin d)))
    (c : C) : ∀ (k : ℕ) (hk : k ≤ len c),
      κ (point len first last c ⟨k, by omega⟩) = flip^[k] (κ (.inl (first c))) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Function.iterate_zero, id_eq]
    rw [at_zero]
  | succ k ih =>
    intro hk
    have h := hrev (⟨c, ⟨k, by omega⟩⟩, false)
    simp only [ChainSubdivision.reverse, Bool.not_false, origin_backward, origin_forward] at h
    rw [h, ih (by omega), Function.iterate_succ_apply']

theorem vcol_eq (κ : Vertex len (V := V) → Col)
    (hrev : ∀ d : Dart len, κ ((graph len first last).origin ((graph len first last).reverse d)) =
      flip (κ ((graph len first last).origin d))) :
    ∀ v, κ v = ChainRealization.vcol len first flip (κ ∘ Sum.inl) v := by
  intro v
  cases v with
  | inl v => rfl
  | inr v =>
    rcases v with ⟨c, i⟩
    have h := point_colour len first last flip κ hrev c (i.val + 1) (by omega)
    rw [at_interior] at h
    rw [h]
    rfl

end Alternation

namespace TwoSideStage
open scoped Classical BigOperators
variable {M : Model} {W : Type*}

/-- A coloured embedding of the chain pattern of a word is a term of the colour-summed
realization count. -/
theorem crealizations_pos (S : Side M) (F : S.Word) (r : S.Match)
    (e : CEmb (ChainSubdivision.graph S.len S.first S.last)
      (ChainRealization.label M S.len (StageExpectation.readWord M S.len F)) S.col S.out
      (OAI.TorsionFreeZeroDivisors.ChainRealization.pin S.len S.pin) (cbar M.inv S.flip) r) :
    0 < S.crealizations F r := by
  obtain ⟨κ, ⟨e⟩⟩ := e
  have hrev : ∀ d, κ ((ChainSubdivision.graph S.len S.first S.last).origin
      ((ChainSubdivision.graph S.len S.first S.last).reverse d)) =
      S.flip (κ ((ChainSubdivision.graph S.len S.first S.last).origin d)) := by
    intro d
    have h := embedding_label_reverse e d
    exact congrArg Prod.snd h
  have hκ := vcol_eq S.len S.first S.last S.flip κ hrev
  have he : RealizationTransport.Embedding (ChainSubdivision.graph S.len S.first S.last)
      (ChainRealization.clabel M S.len S.first S.last S.flip
        (StageExpectation.readWord M S.len F) (κ ∘ Sum.inl))
      S.outgoing (OAI.TorsionFreeZeroDivisors.ChainRealization.pin S.len S.pin)
      (cbar M.inv S.flip) r :=
    RealizationTransport.congrLabel e _ (fun d => by
      simp only [ChainRealization.clabel, hκ])
  have hp := RealizationTransport.realizations_pos he
  unfold Side.crealizations
  exact hp.trans_le (Finset.single_le_sum (f := fun κ' => S.realizations F κ' r)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (κ ∘ Sum.inl)))

theorem count_pos (A B : Side M) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (r : A.Match × B.Match) (w : W) (hw : w ∈ X)
    (eA : CEmb (ChainSubdivision.graph A.len A.first A.last)
      (ChainRealization.label M A.len (StageExpectation.readWord M A.len (WA w))) A.col A.out
      (OAI.TorsionFreeZeroDivisors.ChainRealization.pin A.len A.pin) (cbar M.inv A.flip) r.1)
    (eB : CEmb (ChainSubdivision.graph B.len B.first B.last)
      (ChainRealization.label M B.len (StageExpectation.readWord M B.len (WB w))) B.col B.out
      (OAI.TorsionFreeZeroDivisors.ChainRealization.pin B.len B.pin) (cbar M.inv B.flip) r.2) :
    0 < count A B X WA WB r := by
  have hm : w ∈ immersedLabels A B X WA WB :=
    Finset.mem_filter.mpr ⟨hw, eA.immersed, eB.immersed⟩
  have hp : 0 < A.crealizations (WA w) r.1 * B.crealizations (WB w) r.2 :=
    Nat.mul_pos (crealizations_pos A (WA w) r.1 eA) (crealizations_pos B (WB w) r.2 eB)
  apply hp.trans_le
  unfold count
  exact Finset.single_le_sum
    (f := fun w => A.crealizations (WA w) r.1 * B.crealizations (WB w) r.2)
    (fun _ _ => Nat.zero_le _) hm

end TwoSideStage

namespace ActualStageRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable (M : Model) {V D : Type} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card = 2)
    {P : Type} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d = d}) (j : ℕ)
local notation "len" => ChainStageEmbedding.length Γ mark h2 paths j
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)

/-- The actual labels at every position of every active chain. -/
def word (label : D → M.α) : ComparedBlocks.Position len → M.α :=
  fun x => label (F^[x.2.val.toNat] x.1.val.val.val)

lemma label_eq (label : D → M.α) (hl : ∀ d, label (Γ.reverse d) = M.inv (label d))
    (d : ChainSubdivision.Dart len) :
    ChainRealization.label M len (StageExpectation.readWord M len (word M Γ mark h2 paths j label)) d =
      label (ChainStageEmbedding.dartMap Γ mark h2 paths j d) := by
  rcases d with ⟨⟨c, i⟩, b⟩
  have hi := OAI.TorsionFreeZeroDivisors.ActualStageRealization.index_mem Γ mark h2 paths j c i
  cases b <;>
    simp only [ChainRealization.label, Bool.false_eq_true, ite_false, ite_true,
      StageExpectation.readWord, dite_eq_left hi, word, Int.toNat_natCast,
      ChainStageEmbedding.dartMap, Function.comp_apply, SubdivisionRestriction.dart,
      ChainIsomorphism.dartMap, hl]

end ActualStageRealization

namespace ActualStageFeasibility
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open BlockAlignment ComparedBlocks RepeatedBlocks
variable (M : Model) {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)

omit [Fintype C] in
lemma block_weight_pos (w : C → ℤ → M.α) (hw : ActualStageLabels.Immersed M s len w)
    (i : Underlying s len) : 0 < M.wordWeight (height s len i) (RepeatedBlocks.word s len w i) := by
  rw [ChainWeights.wordWeight_pred]
  apply Finset.prod_pos
  intro k _
  apply M.weight_pos
  have hq := (OAI.TorsionFreeZeroDivisors.ChainWeights.firstCoordinate s len i k).property
  have hq' := (OAI.TorsionFreeZeroDivisors.ChainWeights.nextCoordinate s len i k).property
  simp only [OAI.TorsionFreeZeroDivisors.ChainWeights.firstCoordinate_val, block_interval,
    Finset.mem_Ico] at hq
  simp only [OAI.TorsionFreeZeroDivisors.ChainWeights.nextCoordinate_val, block_interval,
    Finset.mem_Ico] at hq'
  have hh := hw i ((k.val : ℤ) + lower s len i) hq.1 (by omega)
  simpa only [RepeatedBlocks.word, Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
    add_left_comm] using hh

def bins (w : C → ℤ → M.α) (i : Underlying s len) : ℤ :=
  ⌊-Real.log (M.wordWeight (height s len i) (RepeatedBlocks.word s len w i))⌋

omit [Fintype C] in
lemma mem_bin (w : C → ℤ → M.α) (hw : ActualStageLabels.Immersed M s len w)
    (i : Underlying s len) :
    RepeatedBlocks.word s len w i ∈ M.binWords (height s len i) (bins M s len w i) :=
  M.mem_binWords.mpr ⟨block_weight_pos M s len w hw i, rfl⟩

lemma fullWords_of_comparing {E : Type*} (m : C → ℕ)
    (cmp : Comparisons (E := E) (RepeatedBlocks.traversalLength len m))
    (j : ℕ) (w : C → ℤ → M.α) (hw : ActualStageLabels.Comparing M len m cmp w)
    (hr : ActualStageLabels.Immersed M s len w) :
    (fun x : OAI.TorsionFreeZeroDivisors.ChainStageLabels.StagePosition len m j =>
        w x.1.val x.2.val) ∈
      ChainStageLabels.fullWords M s len m j cmp (bins M s len w) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, w, hw, hr, mem_bin M s len w hr, rfl⟩

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card = 2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d = d})
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "lenR" => repLength Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (ChainChunkTransport.color Γ mark h2 paths)

def globalWord (label : D → M.α) (c : R) (q : ℤ) : M.α :=
  label (F^[q.toNat] c.val.val)

lemma immersed (hs : 0 < s) (label : D → M.α)
    (hl : ∀ d, label (Γ.reverse d) = M.inv (label d))
    (hinj : ∀ d e, Γ.origin d = Γ.origin e → label d = label e → d = e) :
    ActualStageLabels.Immersed M s (lenR) (globalWord M Γ mark h2 label) := by
  intro i q hq hq'
  have hb : q ∈ block s i.2.val := by
    rw [block_interval s (lenR) i]; simp only [Finset.mem_Ico]; omega
  have hb' : q + 1 ∈ block s i.2.val := by
    rw [block_interval s (lenR) i]; simp only [Finset.mem_Ico]; omega
  have ht := full_subset s hs (lenR i.1) i.2 hb
  have ht' := full_subset s hs (lenR i.1) i.2 hb'
  rw [AffineIntervals.nat_positions, Finset.mem_Ico] at ht ht'
  exact normalized_immersed Γ mark h2 M.inv label hl hinj i.1 q ht.1 ht'.2

variable {E : Type*}
    (cmp : Comparisons (E := E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e, cmp.lo e = (lo e : ℝ)) (hhi : ∀ e, cmp.hi e = (hi e : ℝ))

lemma comparing (label : D → M.α)
    (hl : ∀ d, label (Γ.reverse d) = M.inv (label d))
    (hc : ∀ x e, cmp.side x = some e → label (originalDart Γ mark h2 paths x) =
      if cmp.reverse e then M.inv (label (originalDart Γ mark h2 paths (cmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    ActualStageLabels.Comparing M (lenR) (m)
      ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi)
      (globalWord M Γ mark h2 label) := by
  intro x a ha
  have hh := normalized_compatible Γ mark h2 paths cmp lo hi hlo hhi M.inv
    M.inv_inv label hl hc x a ha
  have hp : ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi).pairing =
      (repeatedChunks Γ mark h2 paths).pairing cmp := rfl
  rw [hp]
  exact hh

lemma fullWords_mem (hs : 0 < s) (j : ℕ) (label : D → M.α)
    (hl : ∀ d, label (Γ.reverse d) = M.inv (label d))
    (hinj : ∀ d e, Γ.origin d = Γ.origin e → label d = label e → d = e)
    (hc : ∀ x e, cmp.side x = some e → label (originalDart Γ mark h2 paths x) =
      if cmp.reverse e then M.inv (label (originalDart Γ mark h2 paths (cmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (cmp.pairing.partner x))) :
    (fun x : OAI.TorsionFreeZeroDivisors.ChainStageLabels.StagePosition (lenR) (m) j =>
        globalWord M Γ mark h2 label x.1.val x.2.val) ∈
      ChainStageLabels.fullWords M s (lenR) (m) j
        ((repeatedChunks Γ mark h2 paths).comparisons cmp lo hi hlo hhi)
        (bins M s (lenR) (globalWord M Γ mark h2 label)) := by
  exact fullWords_of_comparing M s (lenR) (m) _ j _
    (comparing M Γ mark h2 paths cmp lo hi hlo hhi label hl hc)
    (immersed M s Γ mark h2 hs label hl hinj)

end ActualStageFeasibility

namespace StagePartition
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks
open OAI.TorsionFreeZeroDivisors.ChainStageLabels (StagePosition activeBlocks)
open OAI.TorsionFreeZeroDivisors.StagePartition (CA CB lenA lenB indexA indexB bin_sum
  exponential_fusion)
variable (M : Model) {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB] [DecidableEq TA] [DecidableEq TB]
variable (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)

def restrictA (F : StagePosition len m j → M.α) : Position (lenA len m side j) → M.α :=
  fun x => F ⟨⟨x.1.val, x.1.property.1⟩, x.2⟩
def restrictB (F : StagePosition len m j → M.α) : Position (lenB len m side j) → M.α :=
  fun x => F ⟨⟨x.1.val, x.1.property.1⟩, x.2⟩

include hs in
theorem binsA (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → M.α)
    (hF : F ∈ ChainStageLabels.fullWords M s len m j cmp d) :
    ∀ i, word s (lenA len m side j) (StageExpectation.readWord M (lenA len m side j)
      (restrictA M len m side j F)) i ∈
        M.binWords (height s (lenA len m side j) i) (d (indexA s len m side j i)) := by
  obtain ⟨w, _, _, hb, rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (lenA len m side j) (StageExpectation.readWord M (lenA len m side j)
      (restrictA M len m side j (fun x => w x.1.val x.2.val))) i =
      word s len w (indexA s len m side j i) := by
    funext k
    dsimp only [word, StageExpectation.readWord]
    rw [dite_eq_left (OAI.TorsionFreeZeroDivisors.StageExpectation.word_position s hs
      (lenA len m side j) i k)]
    rfl
  rw [he]
  exact hb (indexA s len m side j i)

include hs in
theorem binsB (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → M.α)
    (hF : F ∈ ChainStageLabels.fullWords M s len m j cmp d) :
    ∀ i, word s (lenB len m side j) (StageExpectation.readWord M (lenB len m side j)
      (restrictB M len m side j F)) i ∈
        M.binWords (height s (lenB len m side j) i) (d (indexB s len m side j i)) := by
  obtain ⟨w, _, _, hb, rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (lenB len m side j) (StageExpectation.readWord M (lenB len m side j)
      (restrictB M len m side j (fun x => w x.1.val x.2.val))) i =
      word s len w (indexB s len m side j i) := by
    funext k
    dsimp only [word, StageExpectation.readWord]
    rw [dite_eq_left (OAI.TorsionFreeZeroDivisors.StageExpectation.word_position s hs
      (lenB len m side j) i k)]
    rfl
  rw [he]
  exact hb (indexB s len m side j i)

variable {ColA ColB : Type} [Fintype ColA] [DecidableEq ColA] [Fintype ColB] [DecidableEq ColB]
  (flipA : ColA → ColA) (flipB : ColB → ColB) (colA : TA → ColA) (colB : TB → ColB)
  (firstA lastA : CA m side j → VA) (firstB lastB : CB m side j → VB)
  (outA : TA → Finset M.α) (outB : TB → Finset M.α)
  (pinA : VA → Option TA) (pinB : VB → Option TB)

def sideA : TwoSideStage.Side M where
  C := CA m side j; V := VA; TV := TA
  fC := inferInstance; fV := inferInstance; fTV := inferInstance; dTV := inferInstance
  Col := ColA; fCol := inferInstance; dCol := inferInstance
  flip := flipA; col := colA
  len := lenA len m side j
  first := firstA; last := lastA; out := outA; pin := pinA

def sideB : TwoSideStage.Side M where
  C := CB m side j; V := VB; TV := TB
  fC := inferInstance; fV := inferInstance; fTV := inferInstance; dTV := inferInstance
  Col := ColB; fCol := inferInstance; dCol := inferInstance
  flip := flipB; col := colB
  len := lenB len m side j
  first := firstB; last := lastB; out := outB; pin := pinB

local notation "SA" => sideA M len m side j flipA colA firstA lastA outA pinA
local notation "SB" => sideB M len m side j flipB colB firstB lastB outB pinB

include hs in
/-- The joint matching expectation applied to the actual `fullWords` projection. -/
theorem mean_bound (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (err : ℕ)
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val))
    (n p : ℝ) (N D R : ℕ) (hA : TwoSideStage.Conditions SA n p N D R)
    (hB : TwoSideStage.Conditions SB n p N D R) :
    TwoSideMean.mean (((SA).samples N) ×ˢ ((SB).samples N))
      (TwoSideStage.count SA SB (ChainStageLabels.fullWords M s len m j cmp d)
        (restrictA M len m side j) (restrictB M len m side j)) ≤
      ((SA).colours * (SB).colours) * ((SA).cost n p R * (SB).cost n p R) *
        Real.exp ((∑ c : StageLabels.activeComponents
          (ActualStageLabels.L M s hs len m cmp err).graph.connectedComponentMk
            (activeBlocks s len m j),
          ActualStageLabels.cost M s hs len m cmp err d c.val) -
          (∑ i ∈ activeBlocks s len m j, (d i : ℝ)) +
          (2 * (err : ℝ) * Fintype.card (Underlying s len) + (s + 1) * Fintype.card C) *
            Real.log (Fintype.card M.α)) := by
  have h := TwoSideStage.mean_bound s hs SA SB (ChainStageLabels.fullWords M s len m j cmp d)
    (restrictA M len m side j) (restrictB M len m side j) n p N D R hA hB
    (fun i => d (indexA s len m side j i)) (fun i => d (indexB s len m side j i))
    (binsA M s hs len m side j cmp d) (binsB M s hs len m side j cmp d)
  have hc := ChainStageLabels.full_stage_count M s hs len m j cmp d err hlarge hscale hreduced
  have hn : 0 ≤ n := (Nat.cast_nonneg (Fintype.card TA)).trans hA.vertices
  have hp := hA.nonneg
  have hcost : 0 ≤ ((SA).colours * (SB).colours) * ((SA).cost n p R * (SB).cost n p R) := by
    have := (SA).colours_nonneg
    have := (SB).colours_nonneg
    unfold TwoSideStage.Side.cost; positivity
  have hstuff : 0 ≤ (((SA).colours * (SB).colours) * ((SA).cost n p R * (SB).cost n p R)) *
      Real.exp (-(∑ i, (d (indexA s len m side j i) : ℝ)) -
        (∑ i, (d (indexB s len m side j i) : ℝ))) := mul_nonneg hcost (Real.exp_pos _).le
  have h' := h.trans (mul_le_mul_of_nonneg_right hc hstuff)
  exact h'.trans_eq (exponential_fusion _ _ _ _ _ _ (bin_sum s len m side j d))

end StagePartition

end

end Kaplansky.Random
