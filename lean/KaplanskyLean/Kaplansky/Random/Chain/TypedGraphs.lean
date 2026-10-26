import Kaplansky.Random.Chain.Girth
import OAI.Algebra.GroupRing.TypedGraphs

/-!
# Fork of `OAI/Algebra/GroupRing/TypedGraphs.lean` (`TypedStage`, `StageDenominator`)

The two prescribed sides of a `Model` at size parameter `m`, their stage conditions, and the
uniform denominator.  Differences with OpenAI:

* `size rep`, `129/16513`, `4260354·rep`, `132` become `M.n m`, `M.p`, `M.carrier m`, `M.dmax`;
* the scale is `M.L m = ⌊log (M.N m) / M.c⌋₊`;
* the error term contains `Q·log(|ColA|·|ColB|)`, which pays for the colourings of the marked
  vertices (at most `Q` per side).
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

/-! ### Fibres of coloured darts -/

section Fibres
variable {α TV Col : Type} [Fintype TV] [DecidableEq α] [DecidableEq Col]
  (col : TV → Col) (out : TV → Finset α)

/-- The origin fibre of a coloured side is the outgoing type. -/
def originFiber (v : TV) :
    {e : PatternEmbeddings.Dart (cout col out) // PatternEmbeddings.origin (cout col out) e = v} ≃
      {t // t ∈ cout col out v} where
  toFun e := ⟨e.val.val.2, by
    have h := e.val.property
    rw [show e.val.val.1 = v from e.property] at h
    exact h⟩
  invFun t := ⟨⟨(v, t.val), t.property⟩, rfl⟩
  left_inv e := by
    apply Subtype.ext; apply Subtype.ext
    exact Prod.ext e.property.symm rfl
  right_inv _ := rfl

theorem origin_card (v : TV) :
    Nat.card {e : PatternEmbeddings.Dart (cout col out) //
      PatternEmbeddings.origin (cout col out) e = v} = (out v).card := by
  rw [Nat.card_congr (originFiber col out v), Nat.card_eq_fintype_card, Fintype.card_coe,
    card_cout]

/-- The label fibre of a coloured port is its pool. -/
def labelFiber (y : α × Col) :
    {e : PatternEmbeddings.Dart (cout col out) // PatternEmbeddings.label (cout col out) e = y} ≃
      {x : TV // col x = y.2 ∧ y.1 ∈ out x} where
  toFun e := ⟨e.val.val.1, by
    have h := mem_cout.mp e.val.property
    have hy : e.val.val.2 = y := e.property
    rw [hy] at h
    exact ⟨h.2.symm, h.1⟩⟩
  invFun x := ⟨⟨(x.val, y), mem_cout.mpr ⟨x.property.2, x.property.1.symm⟩⟩, rfl⟩
  left_inv e := by
    apply Subtype.ext; apply Subtype.ext
    exact Prod.ext rfl e.property.symm
  right_inv _ := rfl

theorem label_card (y : α × Col) :
    Nat.card {e : PatternEmbeddings.Dart (cout col out) //
      PatternEmbeddings.label (cout col out) e = y} =
      Fintype.card {x : TV // col x = y.2 ∧ y.1 ∈ out x} := by
  rw [Nat.card_congr (labelFiber col out y), Nat.card_eq_fintype_card]

end Fibres

namespace Model
open scoped Classical BigOperators
variable (M : Model)

theorem L_tendsto : Tendsto M.L atTop atTop :=
  (GirthAsymptotics.L_tendsto M.c M.c_pos).comp M.N_tendsto

theorem dmax_two : 2 ≤ M.dmax := le_trans (by norm_num) M.dmax_ge

/-- Exclusion at the reference size, for subdivision girth `3L`. -/
def exclusion (m : ℕ) : ℕ := GirthAsymptotics.exclusion M.c M.dmax (M.N m)

theorem exclusion_eq (m : ℕ) : M.exclusion m = 4 * M.dmax ^ (2 * (3 * M.L m) + 1) := by
  unfold exclusion GirthAsymptotics.exclusion L
  congr 2
  omega

theorem eventually_exclusion (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ m in atTop, (M.exclusion m : ℝ) < κ * M.N m :=
  M.N_tendsto.eventually (GirthAsymptotics.eventual_small M.c M.dmax M.c_pos
    (le_trans (by norm_num) M.dmax_ge) M.log_dmax κ hκ)

/-- The sampled spaces of a side. -/
def samplesA (m : ℕ) := M.SA.samples m (3 * M.L m)
def samplesB (m : ℕ) := M.SB.samples m (3 * M.L m)

theorem poolA_card (m : ℕ) (y : M.α × M.SA.Col) :
    Nat.card {e : M.SA.Dart m // PatternEmbeddings.label (M.SA.out' m) e = y} =
      M.SA.pool m y.1 y.2 := by
  rw [Side.pool]
  exact label_card (M.SA.col m) (M.SA.out m) y

theorem poolB_card (m : ℕ) (y : M.α × M.SB.Col) :
    Nat.card {e : M.SB.Dart m // PatternEmbeddings.label (M.SB.out' m) e = y} =
      M.SB.pool m y.1 y.2 := by
  rw [Side.pool]
  exact label_card (M.SB.col m) (M.SB.out m) y

theorem samplesA_nonempty (m N : ℕ) (hsize : 4 * M.dmax ^ (2 * N + 1) < M.carrier m) :
    (M.SA.samples m N).Nonempty := by
  apply conditioned_nonempty M.inv M.inv_inv M.inv_ne M.SA.flip M.SA.flip_flip
    (M.SA.col m) (M.SA.out m) N M.dmax M.dmax_two (fun v => (M.degA m v).2)
  · intro y
    have h1 := label_card (M.SA.col m) (M.SA.out m) y
    have h2 := label_card (M.SA.col m) (M.SA.out m) (cbar M.inv M.SA.flip y)
    rw [Nat.card_eq_fintype_card] at h1 h2
    rw [h1, h2]
    exact M.balanceA m y.1 y.2
  · intro x
    rw [label_card]
    exact lt_of_lt_of_le hsize (M.poolA m _ _)

theorem samplesB_nonempty (m N : ℕ) (hsize : 4 * M.dmax ^ (2 * N + 1) < M.carrier m) :
    (M.SB.samples m N).Nonempty := by
  apply conditioned_nonempty M.inv M.inv_inv M.inv_ne M.SB.flip M.SB.flip_flip
    (M.SB.col m) (M.SB.out m) N M.dmax M.dmax_two (fun v => (M.degB m v).2)
  · intro y
    have h1 := label_card (M.SB.col m) (M.SB.out m) y
    have h2 := label_card (M.SB.col m) (M.SB.out m) (cbar M.inv M.SB.flip y)
    rw [Nat.card_eq_fintype_card] at h1 h2
    rw [h1, h2]
    exact M.balanceB m y.1 y.2
  · intro x
    rw [label_card]
    exact lt_of_lt_of_le hsize (M.poolB m _ _)

theorem eventual_carrier : ∀ᶠ m in atTop, M.exclusion m < M.carrier m := by
  filter_upwards [M.eventually_exclusion M.κ M.κ_pos, M.carrier_lin] with m h1 h2
  exact_mod_cast lt_of_lt_of_le h1 h2

/-- Both girth-conditioned spaces are nonempty for all large `m`. -/
theorem eventual_nonempty : ∀ᶠ m in atTop,
    (M.samplesA m).Nonempty ∧ (M.samplesB m).Nonempty := by
  filter_upwards [M.eventual_carrier] with m hm
  rw [exclusion_eq] at hm
  exact ⟨M.samplesA_nonempty m _ hm, M.samplesB_nonempty m _ hm⟩

end Model

namespace TypedStage
open scoped Classical BigOperators
open TwoSideStage
variable (M : Model) (m : ℕ)
variable {C V : Type} [Fintype C] [Fintype V] (len : C → ℕ) (first last : C → V)

abbrev sideA (pin : V → Option (M.SA.V m)) : TwoSideStage.Side M where
  C := C
  V := V
  TV := M.SA.V m
  fC := inferInstance
  fV := inferInstance
  fTV := inferInstance
  dTV := inferInstance
  Col := M.SA.Col
  fCol := inferInstance
  dCol := inferInstance
  flip := M.SA.flip
  col := M.SA.col m
  len := len
  first := first
  last := last
  out := M.SA.out m
  pin := pin

abbrev sideB (pin : V → Option (M.SB.V m)) : TwoSideStage.Side M where
  C := C
  V := V
  TV := M.SB.V m
  fC := inferInstance
  fV := inferInstance
  fTV := inferInstance
  dTV := inferInstance
  Col := M.SB.Col
  fCol := inferInstance
  dCol := inferInstance
  flip := M.SB.flip
  col := M.SB.col m
  len := len
  first := first
  last := last
  out := M.SB.out m
  pin := pin

theorem conditionsA (pin : V → Option (M.SA.V m)) (N R : ℕ) (hR : 0 < R)
    (hroom : R + ∑ c, len c + 4 * M.dmax ^ (2 * N + 1) ≤ M.carrier m) :
    Conditions (sideA M m len first last pin) (M.n m) M.p N M.dmax R := by
  refine ⟨M.p_pos.le, M.cardA_le_n m, ?_, M.dmax_two, hR, ?_, ?_, ?_⟩
  · intro c a b h
    exact M.tableA m c a b h
  · intro v
    rw [origin_card]
    exact (M.degA m v).2
  · intro x
    change R + ∑ c, len c + 4 * M.dmax ^ (2 * N + 1) ≤ Nat.card {a : PatternEmbeddings.Dart
      (cout (M.SA.col m) (M.SA.out m)) // PatternEmbeddings.label _ a = PatternEmbeddings.label _ x}
    rw [label_card]
    exact hroom.trans (M.poolA m _ _)
  · exact M.samplesA_nonempty m N (by have := hroom; have := hR; omega)

theorem conditionsB (pin : V → Option (M.SB.V m)) (N R : ℕ) (hR : 0 < R)
    (hroom : R + ∑ c, len c + 4 * M.dmax ^ (2 * N + 1) ≤ M.carrier m) :
    Conditions (sideB M m len first last pin) (M.n m) M.p N M.dmax R := by
  refine ⟨M.p_pos.le, M.cardB_le_n m, ?_, M.dmax_two, hR, ?_, ?_, ?_⟩
  · intro c a b h
    exact M.tableB m c a b h
  · intro v
    rw [origin_card]
    exact (M.degB m v).2
  · intro x
    change R + ∑ c, len c + 4 * M.dmax ^ (2 * N + 1) ≤ Nat.card {a : PatternEmbeddings.Dart
      (cout (M.SB.col m) (M.SB.out m)) // PatternEmbeddings.label _ a = PatternEmbeddings.label _ x}
    rw [label_card]
    exact hroom.trans (M.poolB m _ _)
  · exact M.samplesB_nonempty m N (by have := hroom; have := hR; omega)

end TypedStage

namespace StageDenominator
open scoped BigOperators Classical
open TwoSideStage
variable (M : Model)

def denominator (K m : ℕ) : ℕ := M.carrier m - (K * M.L m + M.exclusion m)

theorem L_ratio : Tendsto (fun m => (M.L m : ℝ) / M.N m) atTop (𝓝 0) := by
  have hc : (0 : ℝ) < M.c := by exact_mod_cast M.c_pos
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h := (hlog.div_const (M.c : ℝ)).comp M.N_tendsto
  simp only [zero_div] at h
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ h
  filter_upwards [M.N_tendsto.eventually (eventually_ge_atTop 1)] with m hm
  have hm' : (1 : ℝ) ≤ M.N m := by exact_mod_cast hm
  have hL : (M.L m : ℝ) ≤ Real.log (M.N m : ℝ) / M.c :=
    Nat.floor_le (by positivity [Real.log_nonneg hm'])
  calc
    (M.L m : ℝ) / M.N m ≤ (Real.log (M.N m : ℝ) / M.c) / M.N m :=
      div_le_div_of_nonneg_right hL (by positivity)
    _ = (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) / M.c) (M.N m) := by
      simp only; ring

theorem spent_ratio (K : ℕ) : Tendsto
    (fun m => ((K * M.L m + M.exclusion m : ℕ) : ℝ) / M.N m) atTop (𝓝 0) := by
  have hx := (GirthAsymptotics.exclusion_ratio M.c M.dmax M.c_pos
    (le_trans (by norm_num) M.dmax_ge) M.log_dmax).comp M.N_tendsto
  have h := ((L_ratio M).const_mul (K : ℝ)).add hx
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards with m
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_mul, add_div, mul_div_assoc]
  rfl

/-- Room for all prescriptions of a bounded pattern. -/
theorem eventually_room (K : ℕ) : ∀ᶠ m in atTop,
    K * M.L m + M.exclusion m < M.carrier m := by
  have h := (spent_ratio M K).eventually_lt_const M.κ_pos
  filter_upwards [h, M.carrier_lin, M.N_tendsto.eventually (eventually_ge_atTop 1)]
    with m hh hc hn
  have hn0 : (0 : ℝ) < M.N m := by exact_mod_cast (show 0 < M.N m by omega)
  have hh' := (div_lt_iff₀ hn0).mp hh
  exact_mod_cast lt_of_lt_of_le hh' hc

theorem eventually_pos (K : ℕ) : ∀ᶠ m in atTop, 0 < denominator M K m := by
  filter_upwards [eventually_room M K] with m hr
  exact Nat.sub_pos_of_lt hr

/-- `carrier / denominator → 1`. -/
theorem carrier_ratio (K : ℕ) : Tendsto
    (fun m => (M.carrier m : ℝ) / denominator M K m) atTop (𝓝 1) := by
  -- denominator / carrier = 1 - spent/carrier, and spent/carrier ≤ (spent/N)/κ → 0
  have hs := (spent_ratio M K).div_const M.κ
  simp only [zero_div] at hs
  have hsc : Tendsto (fun m => ((K * M.L m + M.exclusion m : ℕ) : ℝ) / M.carrier m)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hs
    filter_upwards [M.carrier_lin, M.N_tendsto.eventually (eventually_ge_atTop 1)] with m hc hn
    have hn0 : (0 : ℝ) < M.N m := by exact_mod_cast (show 0 < M.N m by omega)
    have hc0 : (0 : ℝ) < M.carrier m := lt_of_lt_of_le (mul_pos M.κ_pos hn0) hc
    rw [div_div, div_le_div_iff₀ hc0 (mul_pos hn0 M.κ_pos)]
    have hsp : (0 : ℝ) ≤ ((K * M.L m + M.exclusion m : ℕ) : ℝ) := by positivity
    nlinarith
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hsc
  simp only [sub_zero] at hq
  have hinv := hq.inv₀ (by norm_num)
  simp only [inv_one] at hinv
  apply hinv.congr'
  filter_upwards [eventually_room M K, M.carrier_lin,
    M.N_tendsto.eventually (eventually_ge_atTop 1)] with m hr hc hn
  have hn0 : (0 : ℝ) < M.N m := by exact_mod_cast (show 0 < M.N m by omega)
  have hc0 : (0 : ℝ) < M.carrier m := lt_of_lt_of_le (mul_pos M.κ_pos hn0) hc
  rw [denominator, Nat.cast_sub hr.le]
  field_simp

theorem relative_ratio (K : ℕ) : Tendsto
    (fun m => (M.n m * M.p) / denominator M K m) atTop (𝓝 1) := by
  have h := M.ratio.mul (carrier_ratio M K)
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_room M K, M.carrier_lin,
    M.N_tendsto.eventually (eventually_ge_atTop 1)] with m hr hc hn
  have hn0 : (0 : ℝ) < M.N m := by exact_mod_cast (show 0 < M.N m by omega)
  have hc0 : (0 : ℝ) < M.carrier m := lt_of_lt_of_le (mul_pos M.κ_pos hn0) hc
  field_simp

def penalty (K m : ℕ) : ℝ := Real.log ((M.n m * M.p) / denominator M K m)

theorem penalty_tendsto (K : ℕ) : Tendsto (penalty M K) atTop (𝓝 0) := by
  change Tendsto (fun m => Real.log ((M.n m * M.p) / denominator M K m)) _ _
  have h := (Real.continuousAt_log one_ne_zero).tendsto.comp (relative_ratio M K)
  simpa only [Real.log_one, Function.comp_def] using h

theorem denominator_le (K m : ℕ) : (denominator M K m : ℝ) ≤ M.n m * M.p :=
  (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (M.carrier_le m)

theorem penalty_nonneg (K m : ℕ) (hr : 0 < denominator M K m) : 0 ≤ penalty M K m := by
  apply Real.log_nonneg
  apply (le_div_iff₀ (show (0 : ℝ) < denominator M K m by exact_mod_cast hr)).mpr
  simpa only [one_mul] using denominator_le M K m

/-- Number of colours on both sides (at least one each). -/
def colourCount : ℕ := Fintype.card M.SA.Col * Fintype.card M.SB.Col

def error (K Q m : ℕ) : ℝ :=
  Q * (-Real.log M.p) + Q * Real.log (colourCount M) + (K : ℝ) * M.L m * penalty M K m

theorem error_ratio (K Q : ℕ) : Tendsto
    (fun m => error M K Q m / (M.L m : ℝ)) atTop (𝓝 0) := by
  have hL : Tendsto (fun m => (M.L m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp M.L_tendsto
  have hconst := (tendsto_inv_atTop_zero.comp hL).const_mul
    ((Q : ℝ) * (-Real.log M.p) + Q * Real.log (colourCount M))
  have hpen := (penalty_tendsto M K).const_mul (K : ℝ)
  have h := hconst.add hpen
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [M.L_tendsto.eventually (eventually_ge_atTop 1)] with m hn
  have hn0 : (M.L m : ℝ) ≠ 0 := by exact_mod_cast (show M.L m ≠ 0 by omega)
  simp only [error, Function.comp_def]
  field_simp

theorem room (K m e : ℕ) (hr : K * M.L m + M.exclusion m ≤ M.carrier m)
    (he : e ≤ K * M.L m) :
    denominator M K m + e + 4 * M.dmax ^ (2 * (3 * M.L m) + 1) ≤ M.carrier m := by
  rw [← M.exclusion_eq]
  dsimp only [denominator]
  omega

variable {C V : Type} [Fintype C] [Fintype V]

theorem conditionsA (K m : ℕ) (hr : K * M.L m + M.exclusion m < M.carrier m)
    (len : C → ℕ) (first last : C → V) (pin : V → Option (M.SA.V m))
    (he : ∑ c, len c ≤ K * M.L m) :
    Conditions (TypedStage.sideA M m len first last pin) (M.n m) M.p
      (3 * M.L m) M.dmax (denominator M K m) :=
  TypedStage.conditionsA M m len first last pin _ _ (Nat.sub_pos_of_lt hr)
    (room M K m _ hr.le he)

theorem conditionsB (K m : ℕ) (hr : K * M.L m + M.exclusion m < M.carrier m)
    (len : C → ℕ) (first last : C → V) (pin : V → Option (M.SB.V m))
    (he : ∑ c, len c ≤ K * M.L m) :
    Conditions (TypedStage.sideB M m len first last pin) (M.n m) M.p
      (3 * M.L m) M.dmax (denominator M K m) :=
  TypedStage.conditionsB M m len first last pin _ _ (Nat.sub_pos_of_lt hr)
    (room M K m _ hr.le he)

theorem colours_le (S : TwoSideStage.Side M) (Q : ℕ) (hC : 0 < Fintype.card S.Col)
    (hV : Fintype.card S.V ≤ Q) :
    S.colours ≤ (Fintype.card S.Col : ℝ) ^ Q := by
  unfold TwoSideStage.Side.colours
  exact pow_le_pow_right₀ (by exact_mod_cast hC) hV

/-- The edge/table cost, with the colourings, is `exp((f - q) log n + o(L))`. -/
theorem joint_cost_bound (A B : TwoSideStage.Side M) (K Q m : ℕ) (hn : 0 < M.n m)
    (hr : 0 < denominator M K m) (ha : ∀ c, 0 < A.len c) (hb : ∀ c, 0 < B.len c)
    (hQ : Fintype.card A.C + Fintype.card B.C ≤ Q)
    (hVA : Fintype.card A.V ≤ Q) (hVB : Fintype.card B.V ≤ Q)
    (hColA : Fintype.card A.Col = Fintype.card M.SA.Col)
    (hColB : Fintype.card B.Col = Fintype.card M.SB.Col)
    (hE : A.edges + B.edges ≤ K * M.L m) :
    (A.colours * B.colours) * (A.cost (M.n m) M.p (denominator M K m) *
      B.cost (M.n m) M.p (denominator M K m)) ≤
      Real.exp ((((A.freeMarks + B.freeMarks : ℕ) : ℝ) -
        (Fintype.card A.C + Fintype.card B.C : ℕ)) * Real.log (M.n m) + error M K Q m) := by
  have hAI := StageCost.internal_add_chains A.len ha
  have hBI := StageCost.internal_add_chains B.len hb
  have he : A.internal + B.internal + (Fintype.card A.C + Fintype.card B.C) = A.edges + B.edges := by
    dsimp only [TwoSideStage.Side.internal, TwoSideStage.Side.edges] at *
    omega
  have hrnp := denominator_le M K m
  have h := StageCost.uniform_bound (M.n m) M.p (denominator M K m)
    hn M.p_pos M.p_le_one (by exact_mod_cast hr) hrnp
    (A.freeMarks + B.freeMarks) (A.internal + B.internal) (A.edges + B.edges)
    (Fintype.card A.C + Fintype.card B.C) Q he hQ K (M.L m) (by exact_mod_cast hE)
  have hc : A.cost (M.n m) M.p (denominator M K m) * B.cost (M.n m) M.p (denominator M K m) =
      StageCost.cost (M.n m) M.p (denominator M K m)
        (A.freeMarks + B.freeMarks) (A.internal + B.internal) (A.edges + B.edges) := by
    rw [TwoSideStage.cost_product]
    unfold StageCost.cost
    have hex : A.freeMarks + A.internal + B.freeMarks + B.internal =
        (A.freeMarks + B.freeMarks) + (A.internal + B.internal) := by omega
    rw [hex]
  rw [hc]
  have hcolA := colours_le M A Q (by rw [hColA]; exact Fintype.card_pos) hVA
  have hcolB := colours_le M B Q (by rw [hColB]; exact Fintype.card_pos) hVB
  rw [hColA] at hcolA
  rw [hColB] at hcolB
  have hcA0 : (0 : ℝ) < Fintype.card M.SA.Col := by exact_mod_cast Fintype.card_pos
  have hcB0 : (0 : ℝ) < Fintype.card M.SB.Col := by exact_mod_cast Fintype.card_pos
  have hcc : A.colours * B.colours ≤ Real.exp (Q * Real.log (colourCount M)) := by
    have h1 : A.colours * B.colours ≤
        (Fintype.card M.SA.Col : ℝ) ^ Q * (Fintype.card M.SB.Col : ℝ) ^ Q :=
      mul_le_mul hcolA hcolB B.colours_nonneg (by positivity)
    rw [← mul_pow] at h1
    refine h1.trans_eq ?_
    rw [Real.exp_nat_mul, colourCount, Nat.cast_mul, Real.exp_log (mul_pos hcA0 hcB0)]
  have hcost0 : 0 ≤ StageCost.cost (M.n m) M.p (denominator M K m)
      (A.freeMarks + B.freeMarks) (A.internal + B.internal) (A.edges + B.edges) := by
    unfold StageCost.cost
    have := M.p_pos
    positivity
  calc
    (A.colours * B.colours) * StageCost.cost (M.n m) M.p (denominator M K m)
        (A.freeMarks + B.freeMarks) (A.internal + B.internal) (A.edges + B.edges)
        ≤ Real.exp (Q * Real.log (colourCount M)) *
          Real.exp ((((A.freeMarks + B.freeMarks : ℕ) : ℝ) - (Fintype.card A.C + Fintype.card B.C : ℕ)) *
            Real.log (M.n m) + (Q : ℝ) * (-Real.log M.p) +
            (K : ℝ) * (M.L m : ℝ) * Real.log (M.n m * M.p / (denominator M K m : ℝ))) :=
          mul_le_mul hcc h hcost0 (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      unfold error penalty
      ring

end StageDenominator

end

end Kaplansky.Random
