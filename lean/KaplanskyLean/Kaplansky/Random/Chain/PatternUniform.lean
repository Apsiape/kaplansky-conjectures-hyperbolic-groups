import Kaplansky.Random.Chain.SidePins
import OAI.Algebra.GroupRing.PatternUniform

/-!
# Fork of the model-dependent parts of `PatternUniform.lean`

The uniform numerical conditions `Ready` (with `8D` in place of `4800`, `smin` in place of
`3003`), the unbinned realization event, and the probability bound for one original pattern.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

theorem Model.eventually_n_ge_one (M : Model) : ∀ᶠ mm in atTop, 1 ≤ M.n mm := by
  have hN := M.N_tendsto.eventually (eventually_ge_atTop ⌈1 / M.κ⌉₊)
  filter_upwards [M.carrier_lin, hN] with mm hc hN
  have hκ := M.κ_pos
  have h1 : 1 ≤ M.κ * M.N mm := by
    have hc' : (1 / M.κ) ≤ (M.N mm : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    rw [div_le_iff₀ hκ] at hc'
    linarith
  have h2 : (M.carrier mm : ℝ) ≤ M.n mm := by
    have := M.carrier_le mm
    have hp := M.p_le_one
    have hn : 0 ≤ M.n mm := by
      have := M.cardA_le_n mm
      exact le_trans (Nat.cast_nonneg _) this
    nlinarith
  linarith

namespace PatternUniform
open scoped Classical Topology BigOperators
open GridAsymptotics
variable (M : Model)

/-- Numerical conditions shared by every bounded pattern (OpenAI `PatternUniform.Ready`). -/
def Ready (K Mst Q J mm : ℕ) : Prop :=
  1 ≤ (M.L mm : ℝ) ∧ 1 ≤ M.n mm ∧
  K * M.L mm + M.exclusion mm < M.carrier mm ∧
  GridUniform.binRate M (M.L mm) ≤ 1 / (8 * M.D * Mst : ℝ) ∧
  ∀ d ≤ J,
    StageUniform.coefficient M d K Mst Q * OAI.TorsionFreeZeroDivisors.GridUniform.rate d (M.L mm) +
      Mst * StageDenominator.error M K Q mm / (M.L mm : ℝ) ≤ 1 / (8 * M.D) ∧
    ∀ offset : Fin d → ℤ, (M.smin : ℝ) ≤ chosenScale d (M.L mm) offset ∧
      2 * (letterError d (M.L mm) offset : ℝ) < chosenScale d (M.L mm) offset - 1

theorem eventually_ready (K Mst Q J : ℕ) (hM : 0 < Mst) :
    ∀ᶠ mm in atTop, Ready M K Mst Q J mm := by
  have hD := M.D_pos'
  have hL : Tendsto (fun mm => (M.L mm : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp M.L_tendsto
  have hb := ((GridUniform.binRate_tendsto M).comp hL).eventually_lt_const
    (show (0 : ℝ) < 1 / (8 * M.D * Mst : ℝ) by
      have : (0 : ℝ) < Mst := by exact_mod_cast hM
      positivity)
  have hd (d : Fin (J + 1)) : ∀ᶠ mm in atTop,
      StageUniform.coefficient M d.val K Mst Q *
          OAI.TorsionFreeZeroDivisors.GridUniform.rate d.val (M.L mm) +
        Mst * StageDenominator.error M K Q mm / (M.L mm : ℝ) ≤ 1 / (8 * M.D) ∧
      ∀ offset : Fin d.val → ℤ, (M.smin : ℝ) ≤ chosenScale d.val (M.L mm) offset ∧
        2 * (letterError d.val (M.L mm) offset : ℝ) < chosenScale d.val (M.L mm) offset - 1 := by
    have hr := ((OAI.TorsionFreeZeroDivisors.GridUniform.rate_tendsto d.val).comp hL).const_mul
      (StageUniform.coefficient M d.val K Mst Q)
    have he := (StageDenominator.error_ratio M K Q).const_mul (Mst : ℝ)
    have ht := hr.add he
    simp only [mul_zero, add_zero] at ht
    have hevent := ht.eventually_lt_const (show (0 : ℝ) < 1 / (8 * M.D) by positivity)
    filter_upwards [hevent, hL.eventually (GridUniform.eventually_geometry M d.val)] with mm hr hg
    refine ⟨?_, hg⟩
    simpa only [Function.comp_def, mul_div_assoc] using hr.le
  filter_upwards [eventually_all.mpr hd, hb, StageDenominator.eventually_room M K,
    hL.eventually (eventually_ge_atTop (1 : ℝ)), M.eventually_n_ge_one]
    with mm hd hb hr hL hn
  exact ⟨hL, hn, hr, hb.le, fun d hd' => hd ⟨d, by omega⟩⟩

variable {C E : Type*} [Fintype C] [Fintype E]
open OAI.TorsionFreeZeroDivisors.StageMass (totalLength)

theorem Ready.residual {M : Model} {K Mst Q J mm : ℕ} (h : Ready M K Mst Q J mm)
    (hE : Fintype.card E ≤ J) (offset : Fin (Fintype.card E) → ℤ)
    (len m : C → ℕ) (hQ : Fintype.card C ≤ Q)
    (hH : totalLength len m ≤ K * (M.L mm : ℝ))
    (hlo : (M.L mm : ℝ) ≤ totalLength len m) (hpos : ∀ c, 1 ≤ m c) :
    StageMass.residual M (E := E) (chosenScale (Fintype.card E) (M.L mm) offset) len m
      (letterError (Fintype.card E) (M.L mm) offset) Mst Q
      (StageDenominator.error M K Q mm) ≤ totalLength len m / (8 * M.D) := by
  have hD := M.D_pos'
  have hh := StageUniform.residual_bound M K Mst Q (M.L mm) h.1 offset len m hQ hH hpos
    (StageDenominator.error M K Q mm)
  have hb := (div_le_iff₀ (show (0 : ℝ) < M.L mm by linarith [h.1])).mp
    (hh.trans (h.2.2.2.2 (Fintype.card E) hE).1)
  have h8 : (1 / (8 * (M.D : ℝ))) * (M.L mm : ℝ) ≤ totalLength len m / (8 * M.D) := by
    rw [div_eq_mul_one_div (totalLength len m), mul_comm (totalLength len m)]
    exact mul_le_mul_of_nonneg_left hlo (by positivity)
  linarith

end PatternUniform

namespace ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs
open ComparedBlocks RepeatedBlocks GridAsymptotics
variable (M : Model) {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card = 2)
    (side : V → Bool) (hsid : ∀ x, side (Γ.origin (Γ.reverse x)) = side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x = x}) (hp : ∀ p, paths p ≠ [])
    (root : Option P) (mm : ℕ) (a : M.SA.V mm) (b : M.SB.V mm)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2

/-- The fixed-pattern event before any scale or bins are chosen. -/
def Realized (cmp : Comparisons (E := E) (traversalLength len m)) (r : Match M mm) : Prop :=
  ∃ label : D → M.α,
    (∀ x, label (Γ.reverse x) = M.inv (label x)) ∧
    (∀ x y, Γ.origin x = Γ.origin y → label x = label y → x = y) ∧
    ActualStageLabels.Comparing M len m cmp (ActualStageFeasibility.globalWord M Γ mark h2 label) ∧
    CEmb (SideRestriction.graph Γ side hsid true) (fun x => label x.val) (M.SA.col mm)
      (M.SA.out mm) (sourcePinA M Γ mark h2 side paths hp root mm a) (cbar M.inv M.SA.flip) r.1 ∧
    CEmb (SideRestriction.graph Γ side hsid false) (fun x => label x.val) (M.SB.col mm)
      (M.SB.out mm) (sourcePinB M Γ mark h2 side paths hp root mm b) (cbar M.inv M.SB.flip) r.2

omit [Fintype V] in
lemma unbinned_iff (s : ℝ) (cmp : Comparisons (E := E) (traversalLength len m)) (r : Match M mm) :
    Unbinned M Γ mark h2 side hsid paths hp root mm a b s cmp r ↔
      Realized M Γ mark h2 side hsid paths hp root mm a b cmp r := by
  constructor
  · rintro ⟨d, label, hl, hi, hc, _, ha, hb⟩
    exact ⟨label, hl, hi, hc, ha, hb⟩
  · rintro ⟨label, hl, hi, hc, ha, hb⟩
    exact ⟨_, label, hl, hi, hc, rfl, ha, hb⟩

variable [Fintype E]
open OAI.TorsionFreeZeroDivisors.StageMass (totalLength)

/-- Uniform probability bound for one fixed pattern. -/
theorem uniform_probability_bound (K Q Mst J : ℕ) (hM : 0 < Mst)
    (hready : PatternUniform.Ready M K Mst Q J mm)
    (cmp : Comparisons (E := E) (traversalLength len m))
    (hm : ∀ c, m c ≤ Mst) (hpositive : ∀ c, 1 ≤ m c)
    (hc : ∀ i, List.IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse) (paths i))
    (hclose : ∀ i, StageRoot.cyclic root i = true →
      ∀ᵉ (x ∈ (paths i).getLast?) (y ∈ (paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val))
    (hQ : Fintype.card R ≤ Q) (hMark : Fintype.card (Mark mark) ≤ Q) (hE : Fintype.card E ≤ J)
    (hH : totalLength len m ≤ K * (M.L mm : ℝ))
    (hlo : (M.L mm : ℝ) ≤ totalLength len m)
    (hb : (OAI.TorsionFreeZeroDivisors.ActualPatternEvent.defect Γ mark h2 paths cmp : ℝ) ≤
      M.ε * totalLength len m) :
    (((samples M mm).filter (Realized M Γ mark h2 side hsid paths hp root mm a b cmp)).card : ℝ) /
      (samples M mm).card ≤ Real.exp (-(M.L mm : ℝ) / (8 * M.D * Mst)) := by
  let eqv := Fintype.equivFin E
  let off : Fin (Fintype.card E) → ℤ := fun i => cmp.offset (eqv.symm i)
  let s := chosenScale (Fintype.card E) (M.L mm) off
  let err := letterError (Fintype.card E) (M.L mm) off
  have hs : 0 < s := chosenScale_pos _ hready.1 off
  obtain ⟨hl, he⟩ := (hready.2.2.2.2 (Fintype.card E) hE).2 off
  obtain ⟨ν, hν⟩ := uniform_alignment (Fintype.card E) hready.1 off
  have hν' (e : E) : 2 * |(cmp.offset e : ℝ) - (ν (eqv e) : ℝ) * s| + 4 ≤ err := by
    simpa only [off, Equiv.symm_apply_apply] using hν (eqv e)
  have hsm1 : ((M.h₀ + 1 : ℕ) : ℝ) ≤ s := le_trans (by exact_mod_cast le_max_left _ _) hl
  have hsm2 : ((2 * M.D + 2 : ℕ) : ℝ) ≤ s := le_trans (by exact_mod_cast le_max_right _ _) hl
  push_cast at hsm1 hsm2
  have hh (i : Underlying s len) :=
    OAI.TorsionFreeZeroDivisors.BinProfiles.height_bounds s hs.le len i
  have hlarge (i : Underlying s len) : M.h₀ ≤ height s len i := by
    have h : (M.h₀ : ℝ) ≤ height s len i := by linarith [hh i]
    exact_mod_cast h
  have hres := hready.residual hE off len m hQ hH hlo hpositive
  have hu := unbinned_probability_bound M Γ mark h2 side hsid paths hp root mm a b s hs hl cmp
    err K Q Mst hM hm hc hclose hlarge (fun i => by linarith [hh i])
    (fun i => by linarith [hh i]) hreduced hready.2.1 hready.2.2.1 hQ hMark hH
    (fun e => ν (eqv e)) he hν'
    (by simpa only [OAI.TorsionFreeZeroDivisors.ActualPatternEvent.uncovered_eq] using hb) hres
    hpositive
    ((GridUniform.bin_bound M (Fintype.card E) hready.1 off).trans hready.2.2.2.1)
  have heq : (samples M mm).filter (Realized M Γ mark h2 side hsid paths hp root mm a b cmp) =
      (samples M mm).filter (Unbinned M Γ mark h2 side hsid paths hp root mm a b s cmp) := by
    ext r
    simp only [Finset.mem_filter]
    exact and_congr_right
      (fun _ => (unbinned_iff M Γ mark h2 side hsid paths hp root mm a b s cmp r).symm)
  rw [heq]
  apply hu.trans
  apply Real.exp_le_exp.mpr
  have hD := M.D_pos'
  have hMst : (0 : ℝ) < Mst := by exact_mod_cast hM
  exact div_le_div_of_nonneg_right (neg_le_neg hlo) (by positivity)

end ActualPatternEvent

namespace OriginalPattern
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs
open ComparedBlocks RepeatedBlocks GridAsymptotics ActualPatternEvent
open OAI.TorsionFreeZeroDivisors.OriginalPattern (cut totalLength_eq defect_eq)
variable (M : Model) {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card = 2)
    (side : V → Bool) (hsid : ∀ x, side (Γ.origin (Γ.reverse x)) = side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x = x}) (hp : ∀ p, paths p ≠ [])
    (root : Option P) (mm : ℕ) (a : M.SA.V mm) (b : M.SB.V mm)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)

/-- Whole-path comparisons, before cutting at the marked vertices. -/
def Realized (patCmp : Comparisons (E := E) pl) (r : ActualPatternEvent.Match M mm) : Prop :=
  ∃ label : D → M.α,
    (∀ x, label (Γ.reverse x) = M.inv (label x)) ∧
    (∀ x y, Γ.origin x = Γ.origin y → label x = label y → x = y) ∧
    (∀ x e, patCmp.side x = some e → label (originalDart Γ mark h2 paths x) =
      if patCmp.reverse e then M.inv (label (originalDart Γ mark h2 paths (patCmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (patCmp.pairing.partner x))) ∧
    CEmb (SideRestriction.graph Γ side hsid true) (fun x => label x.val) (M.SA.col mm)
      (M.SA.out mm) (sourcePinA M Γ mark h2 side paths hp root mm a) (cbar M.inv M.SA.flip) r.1 ∧
    CEmb (SideRestriction.graph Γ side hsid false) (fun x => label x.val) (M.SB.col mm)
      (M.SB.out mm) (sourcePinB M Γ mark h2 side paths hp root mm b) (cbar M.inv M.SB.flip) r.2

omit [Fintype V] in
lemma normalized (patCmp : Comparisons (E := E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e, patCmp.lo e = (lo e : ℝ)) (hhi : ∀ e, patCmp.hi e = (hi e : ℝ))
    {r : ActualPatternEvent.Match M mm}
    (h : Realized M Γ mark h2 side hsid paths hp root mm a b patCmp r) :
    ActualPatternEvent.Realized M Γ mark h2 side hsid paths hp root mm a b
      (cut Γ mark h2 paths patCmp lo hi hlo hhi) r := by
  rcases h with ⟨label, hl, hn, hc, ha, hb⟩
  exact ⟨label, hl, hn, ActualStageFeasibility.comparing M Γ mark h2 paths patCmp lo hi hlo hhi
    label hl hc, ha, hb⟩

variable [Fintype E]

theorem probability_bound (patCmp : Comparisons (E := E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e, patCmp.lo e = (lo e : ℝ)) (hhi : ∀ e, patCmp.hi e = (hi e : ℝ))
    (K Q Mst J : ℕ) (hM : 0 < Mst)
    (hready : PatternUniform.Ready M K Mst Q J mm)
    (hm : ∀ c, m c ≤ Mst) (hpositive : ∀ c, 1 ≤ m c)
    (hc : ∀ i, List.IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse) (paths i))
    (hclose : ∀ i, StageRoot.cyclic root i = true →
      ∀ᵉ (x ∈ (paths i).getLast?) (y ∈ (paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hreduced : ∀ x e, patCmp.side x = some e →
      originalDart Γ mark h2 paths x ≠ originalDart Γ mark h2 paths (patCmp.pairing.partner x) ∧
      originalDart Γ mark h2 paths x ≠ Γ.reverse (originalDart Γ mark h2 paths (patCmp.pairing.partner x)))
    (hQ : Fintype.card R ≤ Q) (hMark : Fintype.card (Mark mark) ≤ Q)
    (hE : Fintype.card E * (Fintype.card (RepeatedBlocks.Traversal m)) ^ 2 ≤ J)
    (hH : (∑ p, (((paths p).flatMap (word Γ mark h2)).length : ℝ)) ≤ K * (M.L mm : ℝ))
    (hlength : (M.L mm : ℝ) ≤ ∑ p, (((paths p).flatMap (word Γ mark h2)).length : ℝ))
    (hb : ((Finset.univ.filter (fun x => patCmp.pairing.partner x = x)).card : ℝ) ≤
      M.ε * ∑ p, (((paths p).flatMap (word Γ mark h2)).length : ℝ)) :
    (((samples M mm).filter (Realized M Γ mark h2 side hsid paths hp root mm a b patCmp)).card : ℝ) /
      (samples M mm).card ≤ Real.exp (-(M.L mm : ℝ) / (8 * M.D * Mst)) := by
  have he : Fintype.card (E × RepeatedBlocks.Traversal m × RepeatedBlocks.Traversal m) ≤ J := by
    simpa only [Fintype.card_prod, pow_two, mul_assoc] using hE
  have h := ActualPatternEvent.uniform_probability_bound M Γ mark h2 side hsid paths hp root mm a b
    K Q Mst J hM hready (cut Γ mark h2 paths patCmp lo hi hlo hhi)
    hm hpositive hc hclose (normalized_reduced Γ mark h2 paths patCmp lo hi hlo hhi hreduced)
    hQ hMark he (by rwa [totalLength_eq]) (by rwa [totalLength_eq])
    (by simpa only [defect_eq, totalLength_eq] using hb)
  apply le_trans (b := (((samples M mm).filter (ActualPatternEvent.Realized M Γ mark h2 side hsid
      paths hp root mm a b (cut Γ mark h2 paths patCmp lo hi hlo hhi))).card : ℝ) /
      (samples M mm).card) _ h
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro r hr
  obtain ⟨hs, he⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hs, normalized M Γ mark h2 side hsid paths hp root mm a b patCmp
    lo hi hlo hhi he⟩

end OriginalPattern

end

end Kaplansky.Random
