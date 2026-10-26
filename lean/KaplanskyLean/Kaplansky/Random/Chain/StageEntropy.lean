import Kaplansky.Random.Chain.TypedGraphs
import OAI.Algebra.GroupRing.GridUniform

/-!
# Fork of the model-dependent parts of `StageEntropy.lean` and `GridUniform.lean`

Stage label costs, the stage-mass decay and the common-grid estimates with symbolic
constants: `δ = 1/M.D` (OpenAI `1/600`), `a₀ = M.A₀` (OpenAI `256`), and the derived
`2D, 4D, 8D` (OpenAI `1200, 2400, 4800`), `A₀ + 1` (`257`), `smin = max (h₀+1) (2D+2)`
(`3003`).  In this file the number of multiplicity stages is called `Mst` (OpenAI `M`).
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

/-- Minimal block scale (OpenAI: `3003`). -/
def Model.smin (M : Model) : ℕ := max (M.h₀ + 1) (2 * M.D + 2)

namespace StageEntropy
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
open OAI.TorsionFreeZeroDivisors.ChainStageLabels (activeBlocks)
variable (M : Model) {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ)
    (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)
    (d : Underlying s len → ℤ)

def labelCost (j : ℕ) : ℝ :=
  (∑ c : StageLabels.activeComponents
    (ActualStageLabels.L M s hs len m cmp err).graph.connectedComponentMk (activeBlocks s len m j),
      ActualStageLabels.cost M s hs len m cmp err d c.val) -
    ∑ i ∈ activeBlocks s len m j, (d i : ℝ)

theorem labelCost_eq (Mst : ℕ) (j : Fin Mst) :
    labelCost M s hs len m cmp err d j =
      LinkComponents.stageCost (multiplicity s len m) (ActualStageLabels.P s hs len m cmp err)
        Mst (fun i => (d i : ℝ)) (1 / (M.D : ℝ)) s j := by
  unfold labelCost
  change (∑ c : StageLabels.activeComponents
    (ActualStageLabels.L M s hs len m cmp err).graph.connectedComponentMk
    (Finset.univ.filter (fun i => j.val < multiplicity s len m i)),
      ActualStageLabels.cost M s hs len m cmp err d c.val) - _ = _
  rw [ActualStageLabels.cost_sum]
  simp only [activeBlocks, Finset.sum_filter, LinkComponents.stageCost,
    ActualStageLabels.cost, RepeatedBlocks.multiplicity]
  rw [sub_eq_add_neg]
  rw [add_comm]
  congr! 3

/-- Block-propagation and chain-tail error. -/
def looseCost : ℝ :=
  (2 * (err : ℝ) * Fintype.card (Underlying s len) + (s + 1) * Fintype.card C) *
    Real.log (Fintype.card M.α)

theorem sum_exponents (Mst : ℕ) (hm : ∀ c, m c ≤ Mst) (a logn : ℝ)
    (power error : Fin Mst → ℝ) (ha : 0 ≤ a) (hn : 0 ≤ logn)
    (hlow : ∀ i, (1 / (M.D : ℝ)) * s / 2 ≤ d i) (hhigh : ∀ i, (d i : ℝ) ≤ a * s)
    (hpower : ∑ j, power j ≤ 0) :
    (Finset.univ.sum (fun j : Fin Mst => power j * logn +
        labelCost M s hs len m cmp err d j.val + error j)) ≤
      a * s * Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched -
        (1 / (M.D : ℝ)) / 2 * s * (∑ i : Underlying s len, (multiplicity s len m i : ℝ)) +
          ∑ j : Fin Mst, error j := by
  simp_rw [labelCost_eq]
  have h := LinkComponents.sum_stageBound (multiplicity s len m)
    (ActualStageLabels.P s hs len m cmp err) Mst (fun i => hm i.1)
    (fun i => (d i : ℝ)) (1 / (M.D : ℝ)) s a logn power error
    M.δ_pos.le hs.le ha hn hlow hhigh hpower
  convert h

end StageEntropy

namespace StageMass
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
open OAI.TorsionFreeZeroDivisors.StageMass (totalLength uncovered unmatched_bound
  fullMass_lower_bounded)
variable (M : Model) {C E : Type*} [Fintype C] [Fintype E]
  (s : ℝ) (hs : 0 < s) (len m : C → ℕ)
  (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def residual (Mst Q : ℕ) (denError : ℝ) : ℝ :=
  M.A₀ * (22 * s * Fintype.card E + totalLength len m / s) +
    (1 / (M.D : ℝ)) / 2 * s * Mst * Q + Mst * (StageEntropy.looseCost M s len err + denError)

theorem exponent_sum_bound (Mst Q : ℕ) (hm : ∀ c, m c ≤ Mst) (hQ : Fintype.card C ≤ Q)
    (ν : E → ℤ) (hsmall : 2 * (err : ℝ) < s - 1)
    (herr : ∀ e, 2 * |(cmp.offset e : ℝ) - (ν e : ℝ) * s| + 4 ≤ err)
    (d : Underlying s len → ℤ) (hlow : ∀ i, (1 / (M.D : ℝ)) * s / 2 ≤ d i)
    (hhigh : ∀ i, (d i : ℝ) ≤ M.A₀ * s)
    (logn denError : ℝ) (hn : 0 ≤ logn) (power : Fin Mst → ℝ)
    (hpower : ∑ j, power j ≤ 0) :
    (Finset.univ.sum (fun j : Fin Mst => power j * logn +
      StageEntropy.labelCost M s hs len m cmp err d j.val +
      (StageEntropy.looseCost M s len err + denError))) ≤
        -((1 / (M.D : ℝ)) / 2) * totalLength len m + M.A₀ * uncovered s hs len m cmp err +
          residual M (E := E) s len m err Mst Q denError := by
  have h := StageEntropy.sum_exponents M s hs len m cmp err d Mst hm M.A₀ logn power
    (fun _ => StageEntropy.looseCost M s len err + denError) M.A₀_nonneg hn hlow hhigh hpower
  have hu := unmatched_bound s hs len m cmp err ν hsmall herr
  have hf := fullMass_lower_bounded s hs len m Mst Q hm hQ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hu' := mul_le_mul_of_nonneg_left hu M.A₀_nonneg
  have hδ : 0 ≤ (1 / (M.D : ℝ)) / 2 := by have := M.δ_pos; positivity
  have hf' := mul_le_mul_of_nonneg_left hf hδ
  unfold residual
  have e1 : (M.A₀ : ℝ) * s * Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched =
      M.A₀ * (s * Fintype.card (ActualStageLabels.P s hs len m cmp err).Unmatched) := by ring
  rw [e1] at h
  nlinarith

/-- Concrete finite selection input (OpenAI: `-H/2400` from `residual ≤ H/4800`). -/
theorem decay (Mst Q : ℕ) (hm : ∀ c, m c ≤ Mst) (hQ : Fintype.card C ≤ Q)
    (ν : E → ℤ) (hsmall : 2 * (err : ℝ) < s - 1)
    (herr : ∀ e, 2 * |(cmp.offset e : ℝ) - (ν e : ℝ) * s| + 4 ≤ err)
    (d : Underlying s len → ℤ) (hlow : ∀ i, (1 / (M.D : ℝ)) * s / 2 ≤ d i)
    (hhigh : ∀ i, (d i : ℝ) ≤ M.A₀ * s)
    (logn denError : ℝ) (hn : 0 ≤ logn) (power : Fin Mst → ℝ)
    (hpower : ∑ j, power j ≤ 0)
    (hb : (uncovered s hs len m cmp err : ℝ) ≤ M.ε * totalLength len m)
    (he : residual M (E := E) s len m err Mst Q denError ≤ totalLength len m / (8 * M.D)) :
    (Finset.univ.sum (fun j : Fin Mst => power j * logn +
      StageEntropy.labelCost M s hs len m cmp err d j.val +
      (StageEntropy.looseCost M s len err + denError))) ≤ -totalLength len m / (4 * M.D) := by
  have h := exponent_sum_bound M s hs len m cmp err Mst Q hm hQ ν hsmall herr
    d hlow hhigh logn denError hn power hpower
  have hH : 0 ≤ totalLength len m := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hD := M.D_pos'
  have he' : residual M (E := E) s len m err Mst Q denError ≤ (1 / (M.D : ℝ)) * totalLength len m / 8 := by
    refine he.trans_eq ?_
    field_simp
  have ha := StageFusion.absorb_errors (δ := 1 / (M.D : ℝ)) (a := M.A₀) M.δ_pos M.A₀_nonneg hH hb he'
  have hfin : -(1 / (M.D : ℝ)) * totalLength len m / 4 = -totalLength len m / (4 * M.D) := by
    field_simp
  rw [← hfin]
  have heq : -((1 / (M.D : ℝ)) / 2) * totalLength len m = -(1 / (M.D : ℝ)) / 2 * totalLength len m := by
    ring
  rw [heq] at h
  linarith

end StageMass

namespace BinProfiles
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable (M : Model)

def values (s : ℝ) : Finset ℤ := Finset.Icc 0 ⌊M.A₀ * s⌋
def profiles {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ) : Finset (Underlying s len → ℤ) :=
  Fintype.piFinset (fun _ => values M s)

theorem mem_values {h : ℕ} (hh : M.h₀ ≤ h) (s : ℝ) (hs : 0 ≤ s)
    (hscale : s + 2 * M.D ≤ 2 * h) (hscale' : (h : ℝ) ≤ 2 * s)
    (d : ℤ) (W : Fin h → M.α) (hW : W ∈ M.binWords h d) : d ∈ values M s := by
  obtain ⟨hl, hu, _⟩ := Alphabet.bin_full_bounds M.D_pos M.decays (M.A₀ : ℝ) M.A₀_ge h hh s
    hscale hscale' d W hW
  have hd : (0 : ℝ) ≤ d := (by have := M.δ_pos; positivity : (0 : ℝ) ≤ (1 / (M.D : ℝ)) * s / 2).trans hl
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hd, Int.le_floor.mpr hu⟩

theorem card_values (s : ℝ) (hs : 0 ≤ s) : ((values M s).card : ℝ) ≤ M.A₀ * s + 1 := by
  have hA := M.A₀_nonneg
  have hf : (0 : ℤ) ≤ ⌊M.A₀ * s⌋ := Int.floor_nonneg.mpr (by positivity)
  have hcast : ((⌊M.A₀ * s⌋ + 1).toNat : ℝ) = (⌊M.A₀ * s⌋ : ℝ) + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_add, Int.cast_one]
  simp only [values, Int.card_Icc, sub_zero]
  rw [hcast]
  linarith [Int.floor_le (M.A₀ * s)]

variable {C : Type*} [Fintype C]
theorem card_profiles (s : ℝ) (len : C → ℕ) (hs : 0 ≤ s) :
    ((profiles M s len).card : ℝ) ≤
      Real.exp (Fintype.card (Underlying s len) * Real.log (M.A₀ * s + 1)) := by
  have hA := M.A₀_nonneg
  have hp : 0 < (M.A₀ : ℝ) * s + 1 := by positivity
  rw [profiles, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Nat.cast_pow]
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (card_values M s hs) _).trans_eq
  rw [Real.exp_nat_mul, Real.exp_log hp]

theorem cardinal_bound (s : ℝ) (hs : 0 < s) (len : C → ℕ) :
    ((profiles M s len).card : ℝ) ≤ Real.exp
      (((∑ c, (len c : ℝ)) / s) * Real.log (M.A₀ * s + 1)) := by
  have hA := M.A₀_nonneg
  apply (card_profiles M s len hs.le).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right
  · exact (le_div_iff₀ hs).mpr (by simpa [mul_comm] using Comparisons.block_mass s hs len)
  · exact Real.log_nonneg (by nlinarith)

/-- Feasible blocks obey both cutoffs and lie in the profile family. -/
theorem feasible_bounds {E : Type*} (s : ℝ) (hs : (M.smin : ℝ) ≤ s) (len m : C → ℕ)
    (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (W : (i : Underlying s len) → Fin (height s len i) → M.α)
    (hW : ActualStageLabels.Feasible M s len m cmp d W) :
    d ∈ profiles M s len ∧ ∀ i, (1 / (M.D : ℝ)) * s / 2 ≤ d i ∧ (d i : ℝ) ≤ M.A₀ * s := by
  have hsm1 : ((M.h₀ + 1 : ℕ) : ℝ) ≤ s := le_trans (by exact_mod_cast le_max_left _ _) hs
  have hsm2 : ((2 * M.D + 2 : ℕ) : ℝ) ≤ s := le_trans (by exact_mod_cast le_max_right _ _) hs
  push_cast at hsm1 hsm2
  have hh (i : Underlying s len) : M.h₀ ≤ height s len i ∧
      s + 2 * M.D ≤ 2 * (height s len i : ℝ) ∧ (height s len i : ℝ) ≤ 2 * s := by
    have hb := OAI.TorsionFreeZeroDivisors.BinProfiles.height_bounds s (by linarith) len i
    have hn : (M.h₀ : ℝ) ≤ height s len i := by linarith
    exact ⟨by exact_mod_cast hn, by linarith, by linarith⟩
  refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), fun i => ?_⟩
  · exact mem_values M (hh i).1 s (by linarith) (hh i).2.1 (hh i).2.2 (d i) (W i) (hW.1 i)
  · have h := Alphabet.bin_full_bounds M.D_pos M.decays (M.A₀ : ℝ) M.A₀_ge (height s len i)
      (hh i).1 s (hh i).2.1 (hh i).2.2 (d i) (W i) (hW.1 i)
    exact ⟨h.1, h.2.1⟩

end BinProfiles

namespace GridUniform
open GridAsymptotics
open OAI.TorsionFreeZeroDivisors.GridUniform (rate rate_tendsto bounds scale_le)

/-- Uniform geometry over all integer offsets (OpenAI threshold `3003`). -/
theorem eventually_geometry (M : Model) (d : ℕ) : ∀ᶠ L in atTop, ∀ offset : Fin d → ℤ,
    (M.smin : ℝ) ≤ chosenScale d L offset ∧
    2 * (letterError d L offset : ℝ) < chosenScale d L offset - 1 := by
  have hr := (rate_tendsto d).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 12)
  have hroot := Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (M.smin : ℝ))
  filter_upwards [hr, hroot, eventually_ge_atTop (1 : ℝ)] with L hr hroot hL offset
  have hb := bounds d hL offset
  have hs := chosenScale_pos d hL offset
  have hlo := (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1
  change Real.sqrt L ≤ chosenScale d L offset at hlo
  have he := (div_le_iff₀ hs).mp hb.2.2.1
  have hi := (div_le_iff₀ hs).mp hb.2.1
  refine ⟨hroot.trans hlo, ?_⟩
  nlinarith

/-- Bin-profile rate (OpenAI: `log 257`). -/
def binRate (M : Model) (L : ℝ) : ℝ := (Real.log (M.A₀ + 1) + Real.log L) / Real.sqrt L

theorem binRate_tendsto (M : Model) : Tendsto (binRate M) atTop (𝓝 0) := by
  have hc : Tendsto (fun L : ℝ => Real.log (M.A₀ + 1) / Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have he : (fun L : ℝ => Real.log L / L ^ (1 / 2 : ℝ)) =
      (fun L : ℝ => Real.log L / Real.sqrt L) := by
    funext L
    rw [Real.sqrt_eq_rpow]
  rw [he] at hl
  unfold binRate
  simpa only [add_div, add_zero] using hc.add hl

theorem bin_bound (M : Model) (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    Real.log (M.A₀ * chosenScale d L offset + 1) / chosenScale d L offset ≤ binRate M L := by
  let s := chosenScale d L offset
  have hA := M.A₀_nonneg
  have hs : 0 < s := chosenScale_pos d hL offset
  have hsl : s ≤ L := scale_le d hL offset
  have hlo := (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1
  change Real.sqrt L ≤ s at hlo
  have hL0 : 0 < L := by linarith
  have hlog := Real.log_le_log (show 0 < (M.A₀ : ℝ) * s + 1 by positivity)
    (show (M.A₀ : ℝ) * s + 1 ≤ (M.A₀ + 1) * L by nlinarith)
  rw [Real.log_mul (by positivity : ((M.A₀ : ℝ) + 1) ≠ 0) hL0.ne'] at hlog
  calc
    _ ≤ (Real.log (M.A₀ + 1) + Real.log L) / s := div_le_div_of_nonneg_right hlog hs.le
    _ ≤ _ := div_le_div_of_nonneg_left (by
        have := Real.log_nonneg hL
        have := Real.log_nonneg (show (1 : ℝ) ≤ M.A₀ + 1 by linarith)
        positivity) (Real.sqrt_pos.mpr hL0) hlo

end GridUniform

namespace StageUniform
open scoped Classical BigOperators Topology
open BlockAlignment ComparedBlocks RepeatedBlocks GridAsymptotics
open OAI.TorsionFreeZeroDivisors.StageMass (totalLength totalLength_eq)
variable (M : Model)

def alphabetLog : ℝ := Real.log (Fintype.card M.α)

theorem alphabetLog_nonneg : 0 ≤ alphabetLog M := M.log_card_α_nonneg

/-- (OpenAI: `256*(22*D+K)+(1/1200)*M*Q+M*(10*K+2*Q)*alphabetLog`.) -/
def coefficient (dE K Mst Q : ℕ) : ℝ :=
  M.A₀ * (22 * dE + K) + (1 / (M.D : ℝ)) / 2 * Mst * Q + Mst * (10 * K + 2 * Q) * alphabetLog M

theorem scalar_bound (dE K Mst Q : ℕ) (L s H blocks err rate den : ℝ)
    (hL : 0 < L) (hs : 0 < s) (_hH : 0 ≤ H) (hb : 0 ≤ blocks)
    (hr : 0 ≤ rate) (hscale : s / L ≤ rate) (hinv : 1 / s ≤ rate)
    (hone : 1 / L ≤ rate) (he : err / s ≤ 5 * rate)
    (hsize : H ≤ K * L) (hblocks : s * blocks ≤ K * L) :
    (M.A₀ * (22 * s * dE + H / s) + (1 / (M.D : ℝ)) / 2 * s * Mst * Q +
      Mst * ((2 * err * blocks + (s + 1) * Q) * alphabetLog M + den)) / L ≤
        coefficient M dE K Mst Q * rate + Mst * den / L := by
  have hA := M.A₀_nonneg
  have hδ : 0 ≤ (1 / (M.D : ℝ)) / 2 := by have := M.δ_pos; positivity
  have hsl := (div_le_iff₀ hL).mp hscale
  have hon := (div_le_iff₀ hL).mp hone
  have he' := (div_le_iff₀ hs).mp he
  have hHl : H / s ≤ (K : ℝ) * L * rate := by
    calc
      _ ≤ ((K : ℝ) * L) / s := div_le_div_of_nonneg_right hsize hs.le
      _ = ((K : ℝ) * L) * (1 / s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  have heb := mul_le_mul_of_nonneg_right he' hb
  have hbc := mul_le_mul_of_nonneg_left hblocks (show 0 ≤ 10 * rate by positivity)
  have htail : (s + 1) * (Q : ℝ) ≤ 2 * rate * L * Q :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg Q)
  have hloss : 2 * err * blocks + (s + 1) * Q ≤ (10 * K + 2 * Q) * rate * L := by nlinarith
  have hlog := mul_le_mul_of_nonneg_right hloss (alphabetLog_nonneg M)
  have hst := mul_le_mul_of_nonneg_right hsl (show 0 ≤ 22 * (dE : ℝ) by positivity)
  have hsq := mul_le_mul_of_nonneg_right hsl
    (show 0 ≤ (1 / (M.D : ℝ)) / 2 * Mst * Q by positivity)
  have hM := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg Mst)
  have hA1 := mul_le_mul_of_nonneg_left (add_le_add hst hHl) hA
  apply (div_le_iff₀ hL).mpr
  have hcancel : (coefficient M dE K Mst Q * rate + Mst * den / L) * L =
      coefficient M dE K Mst Q * rate * L + Mst * den := by field_simp
  rw [hcancel]
  unfold coefficient
  nlinarith

variable {C E : Type*} [Fintype C] [Fintype E]

theorem residual_bound (K Mst Q : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (offset : Fin (Fintype.card E) → ℤ) (len m : C → ℕ) (hQ : Fintype.card C ≤ Q)
    (hH : totalLength len m ≤ K * L) (hpositive : ∀ c, 1 ≤ m c) (den : ℝ) :
    StageMass.residual M (E := E) (chosenScale (Fintype.card E) L offset) len m
      (letterError (Fintype.card E) L offset) Mst Q den / L ≤
        coefficient M (Fintype.card E) K Mst Q *
          OAI.TorsionFreeZeroDivisors.GridUniform.rate (Fintype.card E) L + Mst * den / L := by
  let s := chosenScale (Fintype.card E) L offset
  let err := letterError (Fintype.card E) L offset
  have hs : 0 < s := chosenScale_pos _ hL offset
  have hcard : s * Fintype.card (Underlying s len) ≤ (K : ℝ) * L := by
    apply (Comparisons.block_mass s hs len).trans
    apply le_trans ?_ hH
    rw [totalLength_eq]
    apply Finset.sum_le_sum
    intro c _
    have hp : (1 : ℝ) ≤ m c := by exact_mod_cast hpositive c
    have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (len c) : (0 : ℝ) ≤ len c)
    simpa only [one_mul] using hm
  have hr := OAI.TorsionFreeZeroDivisors.GridUniform.bounds (Fintype.card E) hL offset
  have h := scalar_bound M (Fintype.card E) K Mst Q L s (totalLength len m)
    (Fintype.card (Underlying s len)) err
    (OAI.TorsionFreeZeroDivisors.GridUniform.rate (Fintype.card E) L) den
    (by linarith) hs (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    (Nat.cast_nonneg _) (OAI.TorsionFreeZeroDivisors.GridUniform.rate_nonneg _ (by linarith))
    hr.1 hr.2.1 hr.2.2.2 hr.2.2.1 hH hcard
  apply le_trans ?_ h
  apply div_le_div_of_nonneg_right _ (by linarith)
  unfold StageMass.residual StageEntropy.looseCost alphabetLog
  have htail := mul_le_mul_of_nonneg_left (show (Fintype.card C : ℝ) ≤ Q by exact_mod_cast hQ)
    (show 0 ≤ s + 1 by linarith)
  have hlog := mul_le_mul_of_nonneg_right htail (alphabetLog_nonneg M)
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg Mst)
  dsimp only [alphabetLog] at hh
  linarith

end StageUniform

end

end Kaplansky.Random
