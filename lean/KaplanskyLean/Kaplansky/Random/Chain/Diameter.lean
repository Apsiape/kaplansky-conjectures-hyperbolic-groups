import Kaplansky.Random.Chain.Patterns
import OAI.Algebra.GroupRing.TypedDiameter

/-!
# Fork of `OAI/Algebra/GroupRing/TypedDiameter.lean` for an abstract model

Component diameters of both sides are at most `D₀ · L` with probability `1 - o(1)`.  OpenAI's
constants `p₀ = 129/(4·16513)`, `C₀`, `ρ`, `A₀`, `D₀ = (A₀+1)·803` are replaced by constants
depending only on the model's pool proportion `κ`, maximum degree and scale divisor `c`
(`D₀ = (A₀+1)·(8c+3)`).  The degree lower bound `129` of OpenAI's dense-witness count is a
hypothesis of the model (`degA`, `degB`).
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

namespace TypedDiameter
open scoped Classical BigOperators
open ConditionedMatchings MatchingDiameter DiameterProbability
variable (M : Model)

def κ' : ℝ := min M.κ 1
def p₀ : ℝ := κ' M / 4
def C₀ : ℝ := 9 * (12 * (M.dmax : ℝ) ^ 2 / p₀ M) ^ 65
def ρ : ℝ := min (1 / 4) (min (p₀ M / 65) (1 / (2 * C₀ M + 2)))
def Bn (n : ℕ) : ℕ := ⌊ρ M * n⌋₊
def Rn (n : ℕ) : ℕ := ⌈p₀ M * n⌉₊

theorem κ'_pos : 0 < κ' M := lt_min M.κ_pos one_pos
theorem κ'_le : κ' M ≤ M.κ := min_le_left _ _
theorem p₀_pos : 0 < p₀ M := by unfold p₀; have := κ'_pos M; positivity
theorem p₀_le_one : p₀ M ≤ 1 := by
  unfold p₀; have := min_le_right M.κ 1; unfold κ'; linarith
theorem C₀_pos : 0 < C₀ M := by
  unfold C₀
  have hd : (0 : ℝ) < M.dmax := by
    have := M.dmax_ge
    exact_mod_cast (show 0 < M.dmax by omega)
  exact mul_pos (by norm_num) (pow_pos (div_pos (mul_pos (by norm_num) (pow_pos hd 2)) (p₀_pos M)) 65)

theorem ρ_pos : 0 < ρ M := by
  unfold ρ
  exact lt_min (by norm_num) (lt_min (div_pos (p₀_pos M) (by norm_num))
    (div_pos (by norm_num) (by have := C₀_pos M; positivity)))

theorem ρ_le_quarter : ρ M ≤ 1 / 4 := min_le_left _ _
theorem ρ_le_one : ρ M ≤ 1 := (ρ_le_quarter M).trans (by norm_num)
theorem ρ_small : C₀ M * ρ M ^ 62 ≤ 1 / 2 := by
  have hle : ρ M ≤ 1 / (2 * C₀ M + 2) := (min_le_right _ _).trans (min_le_right _ _)
  have hmul : C₀ M * ρ M ≤ 1 / 2 := by
    have hx := (le_div_iff₀ (show 0 < 2 * C₀ M + 2 by have := C₀_pos M; positivity)).mp hle
    have := ρ_pos M
    nlinarith
  have hpow : ρ M ^ 62 ≤ ρ M := by
    simpa only [pow_one] using
      (pow_le_pow_of_le_one (le_of_lt (ρ_pos M)) (ρ_le_one M) (by norm_num : 1 ≤ 62))
  exact (mul_le_mul_of_nonneg_left hpow (le_of_lt (C₀_pos M))).trans hmul

theorem B_le (n : ℕ) : (Bn M n : ℝ) ≤ ρ M * n := Nat.floor_le (by have := ρ_pos M; positivity)

theorem twice_B_le (n : ℕ) : 2 * Bn M n ≤ n := by
  have h := B_le M n
  have hg := mul_le_mul_of_nonneg_right (ρ_le_quarter M) (Nat.cast_nonneg (α := ℝ) n)
  have : (2 : ℝ) * Bn M n ≤ n := by linarith
  exact_mod_cast this

theorem sixtyfive_B_le (n : ℕ) : (65 * Bn M n : ℝ) ≤ p₀ M * n := by
  have hρ : ρ M ≤ p₀ M / 65 := (min_le_right _ _).trans (min_le_left _ _)
  have h := B_le M n
  have hg := mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem R_ge (n : ℕ) : p₀ M * n ≤ Rn M n := Nat.le_ceil _
theorem R_le (n : ℕ) : (Rn M n : ℝ) ≤ p₀ M * n + 1 :=
  (Nat.ceil_lt_add_one (by have := p₀_pos M; positivity)).le

/-- The deterministic diameter constant. -/
def A₀' : ℕ := ⌈1 / ρ M⌉₊
def D₀ : ℕ := (A₀' M + 1) * (8 * M.c + 3)

theorem packing_bound (n : ℕ) : n / (Bn M n + 1) ≤ A₀' M := by
  have hρ := ρ_pos M
  have hfloor : ρ M * n ≤ (Bn M n : ℝ) + 1 := (Nat.lt_floor_add_one (ρ M * n)).le
  have hceil : 1 / ρ M ≤ (A₀' M : ℝ) := Nat.le_ceil _
  have hi : 1 ≤ ρ M * (A₀' M : ℝ) := by
    have := (div_le_iff₀ hρ).mp hceil
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg (α := ℝ) n)
  have h2 := mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg (α := ℝ) (A₀' M))
  have h3 : (n : ℝ) ≤ ((Bn M n : ℝ) + 1) * A₀' M := by nlinarith
  apply Nat.div_le_of_le_mul
  exact_mod_cast h3

theorem log_radius_bound (n : ℕ) (hL : 1 ≤ scaleL M.c n) :
    2 * (Nat.log 2 n + 1) + 1 ≤ (8 * M.c + 3) * scaleL M.c n := by
  have hc : (0 : ℝ) < M.c := by exact_mod_cast M.c_pos
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    simp [scaleL] at hL
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.natLog_le_logb n 2
    rw [Real.logb] at this
    norm_num only [Nat.cast_ofNat] at this
    exact (le_div_iff₀ (by linarith [Real.log_two_gt_d9])).mp this
  have hg := mul_le_mul_of_nonneg_left
    (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))
  have hl : Real.log n / M.c < (scaleL M.c n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hl' : Real.log n < M.c * ((scaleL M.c n : ℝ) + 1) := by
    rw [div_lt_iff₀ hc] at hl; linarith
  have hL' : (1 : ℝ) ≤ scaleL M.c n := by exact_mod_cast hL
  have hr : (Nat.log 2 n : ℝ) ≤ 4 * M.c * scaleL M.c n := by nlinarith
  have hr' : (Nat.log 2 n : ℝ) * 2 + 3 ≤ (8 * M.c + 3) * scaleL M.c n := by nlinarith
  have : ((2 * (Nat.log 2 n + 1) + 1 : ℕ) : ℝ) ≤ (((8 * M.c + 3) * scaleL M.c n : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

/-- Component diameter on the expansion complement. -/
theorem component_diameter {V D T : Type*} [Fintype V] [Fintype D]
    (origin : D → V) {label : D → T} {bar : T → T} (n N : ℕ)
    (hc : Fintype.card V = n) (hL : 1 ≤ scaleL M.c n) (r : Matching label bar)
    (hr : r ∈ Matching.conditioned (label := label) (bar := bar) origin N ∅)
    (hf : r ∉ failure (label := label) (bar := bar) origin (Bn M n) N)
    {u v : V} (huv : (simpleGraph origin r).Reachable u v) :
    (simpleGraph origin r).dist u v ≤ D₀ M * scaleL M.c n := by
  have hpow : Bn M n < 2 ^ (Nat.log 2 n + 1) :=
    (show Bn M n ≤ n by have := twice_B_le M n; omega).trans_lt
      (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hh := diameter_of_not_failure origin (Bn M n) N (Nat.log 2 n + 1) r hr hf hpow huv
  rw [hc] at hh
  have hm := Nat.mul_le_mul (Nat.add_le_add_right (packing_bound M n) 1)
    (log_radius_bound M n hL)
  unfold D₀
  calc
    _ ≤ (n / (Bn M n + 1) + 1) * (2 * (Nat.log 2 n + 1) + 1) := hh.le
    _ ≤ (A₀' M + 1) * ((8 * M.c + 3) * scaleL M.c n) := hm
    _ = _ := by ring

/-- Failure of expansion on one side of the model. -/
def bad (S : Side M.toAlphabet) (mm : ℕ) :=
  failure (label := PatternEmbeddings.label (S.out' mm)) (bar := S.bar)
    (PatternEmbeddings.origin (S.out' mm)) (Bn M (Fintype.card (S.V mm))) (3 * M.L mm)

theorem side_bound (S : Side M.toAlphabet)
    (hdeg : ∀ m x, 129 ≤ (S.out m x).card ∧ (S.out m x).card ≤ M.dmax) (mm : ℕ)
    (hcard : 0 < Fintype.card (S.V mm))
    (hroom : ∀ x : S.Dart mm, Rn M (Fintype.card (S.V mm)) + 65 * Bn M (Fintype.card (S.V mm)) +
      4 * M.dmax ^ (2 * (3 * M.L mm) + 1) ≤
        Nat.card {e : S.Dart mm // PatternEmbeddings.label (S.out' mm) e =
          PatternEmbeddings.label (S.out' mm) x})
    (hΩ : (S.samples mm (3 * M.L mm)).Nonempty) :
    (bad M S mm).card / ((S.samples mm (3 * M.L mm)).card : ℝ) ≤
      ∑' k : ℕ, witnessTerm (C₀ M) (ρ M) (Fintype.card (S.V mm)) k := by
  have hR0 : 0 < Rn M (Fintype.card (S.V mm)) := by
    apply Nat.ceil_pos.mpr
    have := p₀_pos M
    have : (0 : ℝ) < Fintype.card (S.V mm) := by exact_mod_cast hcard
    positivity
  have hh := failure_probability_bound (PatternEmbeddings.origin (S.out' mm))
    (Bn M (Fintype.card (S.V mm))) (3 * M.L mm) M.dmax (Rn M (Fintype.card (S.V mm))) (p₀ M) (ρ M)
    S.bar_ne M.dmax_two
    (fun v => (hdeg mm v).1.trans_eq (origin_card (S.col mm) (S.out mm) v).symm)
    (fun v => (origin_card (S.col mm) (S.out mm) v).trans_le (hdeg mm v).2)
    (twice_B_le M _) (B_le M _) (p₀_pos M) (p₀_le_one M) (ρ_le_one M)
    (R_ge M _) hR0 hroom ?_
    (by
      apply Summable.of_norm_bounded (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1))
      intro k
      exact witnessTerm_majorant (le_of_lt (C₀_pos M)) (ρ_small M) _ k hcard)
  · unfold bad Side.samples C₀
    convert hh
  · unfold Side.samples at hΩ
    convert hΩ

end TypedDiameter

namespace Model
open scoped Classical BigOperators
variable (M : Model)

theorem pool_le_cardA (mm : ℕ) (t : M.α) (c : M.SA.Col) :
    M.SA.pool mm t c ≤ Fintype.card (M.SA.V mm) := Fintype.card_subtype_le _
theorem pool_le_cardB (mm : ℕ) (t : M.α) (c : M.SB.Col) :
    M.SB.pool mm t c ≤ Fintype.card (M.SB.V mm) := Fintype.card_subtype_le _

theorem carrier_tendsto : Tendsto M.carrier atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hN := M.N_tendsto.eventually (eventually_ge_atTop ⌈(b : ℝ) / M.κ⌉₊)
  filter_upwards [M.carrier_lin, hN] with mm hc hN
  have hκ := M.κ_pos
  have h1 : (b : ℝ) ≤ M.κ * M.N mm := by
    have hc' : (b : ℝ) / M.κ ≤ (M.N mm : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    rw [div_le_iff₀ hκ] at hc'
    linarith
  exact_mod_cast h1.trans hc

theorem cardA_tendsto : Tendsto (fun mm => Fintype.card (M.SA.V mm)) atTop atTop := by
  apply tendsto_atTop_mono _ M.carrier_tendsto
  intro mm
  obtain ⟨t⟩ := (inferInstance : Nonempty M.α)
  obtain ⟨c⟩ := (inferInstance : Nonempty M.SA.Col)
  exact (M.poolA mm t c).trans (M.pool_le_cardA mm t c)

theorem cardB_tendsto : Tendsto (fun mm => Fintype.card (M.SB.V mm)) atTop atTop := by
  apply tendsto_atTop_mono _ M.carrier_tendsto
  intro mm
  obtain ⟨t⟩ := (inferInstance : Nonempty M.α)
  obtain ⟨c⟩ := (inferInstance : Nonempty M.SB.Col)
  exact (M.poolB mm t c).trans (M.pool_le_cardB mm t c)

/-- Room for the diameter union bound on a side of size at most `N`. -/
theorem eventually_diameter_room : ∀ᶠ mm in atTop, ∀ n ≤ M.N mm,
    TypedDiameter.Rn M n + 65 * TypedDiameter.Bn M n + 4 * M.dmax ^ (2 * (3 * M.L mm) + 1) ≤
      M.carrier mm := by
  have hκ := TypedDiameter.κ'_pos M
  have hN := M.N_tendsto.eventually (eventually_ge_atTop ⌈4 / TypedDiameter.κ' M⌉₊)
  filter_upwards [M.eventually_exclusion (TypedDiameter.κ' M / 4) (by positivity),
    M.carrier_lin, hN] with mm hx hc hN n hn
  rw [← M.exclusion_eq]
  have hn' : (n : ℝ) ≤ M.N mm := by exact_mod_cast hn
  have hR := TypedDiameter.R_le M n
  have hB := TypedDiameter.sixtyfive_B_le M n
  have hp0 : TypedDiameter.p₀ M = TypedDiameter.κ' M / 4 := rfl
  have hN4 : 4 ≤ TypedDiameter.κ' M * M.N mm := by
    have hc' : 4 / TypedDiameter.κ' M ≤ (M.N mm : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    rw [div_le_iff₀ hκ] at hc'
    linarith
  have hκle := TypedDiameter.κ'_le M
  have hcN : TypedDiameter.κ' M * M.N mm ≤ M.carrier mm :=
    le_trans (mul_le_mul_of_nonneg_right hκle (Nat.cast_nonneg _)) hc
  have hpn : TypedDiameter.p₀ M * n ≤ TypedDiameter.κ' M / 4 * M.N mm := by
    rw [hp0]; exact mul_le_mul_of_nonneg_left hn' (by positivity)
  have : ((TypedDiameter.Rn M n + 65 * TypedDiameter.Bn M n + M.exclusion mm : ℕ) : ℝ) ≤
      M.carrier mm := by
    push_cast
    nlinarith
  exact_mod_cast this

end Model

namespace GraphSample
open scoped Classical
open TypedDiameter ActualPatternEvent

/-- Both component-diameter conclusions, including disconnected graphs. -/
def Diameters (M : Model) (mm : ℕ) (r : Match M mm) : Prop :=
  (∀ u v, (MatchingDiameter.simpleGraph (PatternEmbeddings.origin (M.SA.out' mm)) r.1).Reachable u v →
    (MatchingDiameter.simpleGraph (PatternEmbeddings.origin (M.SA.out' mm)) r.1).dist u v ≤
      D₀ M * M.L mm) ∧
  (∀ u v, (MatchingDiameter.simpleGraph (PatternEmbeddings.origin (M.SB.out' mm)) r.2).Reachable u v →
    (MatchingDiameter.simpleGraph (PatternEmbeddings.origin (M.SB.out' mm)) r.2).dist u v ≤
      D₀ M * M.L mm)

/-- The A-side diameter failure event. -/
def diameterBadA (M : Model) (mm : ℕ) := (M.samplesA mm).filter fun r =>
  ∃ u v, (MatchingDiameter.simpleGraph (PatternEmbeddings.origin (M.SA.out' mm)) r).Reachable u v ∧
    D₀ M * M.L mm < (MatchingDiameter.simpleGraph (PatternEmbeddings.origin (M.SA.out' mm)) r).dist u v
def diameterBadB (M : Model) (mm : ℕ) := (M.samplesB mm).filter fun r =>
  ∃ u v, (MatchingDiameter.simpleGraph (PatternEmbeddings.origin (M.SB.out' mm)) r).Reachable u v ∧
    D₀ M * M.L mm < (MatchingDiameter.simpleGraph (PatternEmbeddings.origin (M.SB.out' mm)) r).dist u v

theorem diameterBadA_subset (M : Model) (mm : ℕ) (hL : 1 ≤ scaleL M.c (Fintype.card (M.SA.V mm))) :
    diameterBadA M mm ⊆ bad M M.SA mm := by
  intro r hr
  obtain ⟨hr, u, v, huv, hlt⟩ := Finset.mem_filter.mp hr
  by_contra hf
  unfold bad at hf
  unfold Model.samplesA Side.samples at hr
  have hd := component_diameter M (PatternEmbeddings.origin (M.SA.out' mm)) _ (3 * M.L mm) rfl hL r
    (by convert hr) (by convert hf) huv
  have hmono := GirthAsymptotics.L_mono M.c (M.cardA_le mm)
  have : D₀ M * scaleL M.c (Fintype.card (M.SA.V mm)) ≤ D₀ M * M.L mm :=
    Nat.mul_le_mul_left _ hmono
  omega

theorem diameterBadB_subset (M : Model) (mm : ℕ) (hL : 1 ≤ scaleL M.c (Fintype.card (M.SB.V mm))) :
    diameterBadB M mm ⊆ bad M M.SB mm := by
  intro r hr
  obtain ⟨hr, u, v, huv, hlt⟩ := Finset.mem_filter.mp hr
  by_contra hf
  unfold bad at hf
  unfold Model.samplesB Side.samples at hr
  have hd := component_diameter M (PatternEmbeddings.origin (M.SB.out' mm)) _ (3 * M.L mm) rfl hL r
    (by convert hr) (by convert hf) huv
  have hmono := GirthAsymptotics.L_mono M.c (M.cardB_le mm)
  have : D₀ M * scaleL M.c (Fintype.card (M.SB.V mm)) ≤ D₀ M * M.L mm :=
    Nat.mul_le_mul_left _ hmono
  omega

theorem diameterA_tendsto (M : Model) :
    Tendsto (fun mm => (diameterBadA M mm).card / ((M.samplesA mm).card : ℝ)) atTop (𝓝 0) := by
  have hw := (DiameterProbability.witness_sum_tendsto (le_of_lt (C₀_pos M)) (ρ_small M)).comp M.cardA_tendsto
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro mm; positivity)) _ hw
  filter_upwards [M.eventually_diameter_room, M.eventual_nonempty,
    ((GirthAsymptotics.L_tendsto M.c M.c_pos).comp M.cardA_tendsto).eventually
      (eventually_ge_atTop 1),
    M.cardA_tendsto.eventually (eventually_gt_atTop 0)] with mm hroom hne hL hpos
  have hsub := diameterBadA_subset M mm hL
  calc
    (diameterBadA M mm).card / ((M.samplesA mm).card : ℝ) ≤
        (bad M M.SA mm).card / ((M.samplesA mm).card : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
    _ ≤ _ := side_bound M M.SA M.degA mm hpos (fun x => by
        rw [Model.poolA_card]
        exact (hroom _ (M.cardA_le mm)).trans (M.poolA mm _ _)) hne.1

theorem diameterB_tendsto (M : Model) :
    Tendsto (fun mm => (diameterBadB M mm).card / ((M.samplesB mm).card : ℝ)) atTop (𝓝 0) := by
  have hw := (DiameterProbability.witness_sum_tendsto (le_of_lt (C₀_pos M)) (ρ_small M)).comp M.cardB_tendsto
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro mm; positivity)) _ hw
  filter_upwards [M.eventually_diameter_room, M.eventual_nonempty,
    ((GirthAsymptotics.L_tendsto M.c M.c_pos).comp M.cardB_tendsto).eventually
      (eventually_ge_atTop 1),
    M.cardB_tendsto.eventually (eventually_gt_atTop 0)] with mm hroom hne hL hpos
  have hsub := diameterBadB_subset M mm hL
  calc
    (diameterBadB M mm).card / ((M.samplesB mm).card : ℝ) ≤
        (bad M M.SB mm).card / ((M.samplesB mm).card : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
    _ ≤ _ := side_bound M M.SB M.degB mm hpos (fun x => by
        rw [Model.poolB_card]
        exact (hroom _ (M.cardB_le mm)).trans (M.poolB mm _ _)) hne.2

lemma diameters_of_not_bad (M : Model) (mm : ℕ) (r : Match M mm) (hr : r ∈ samples M mm)
    (ha : r.1 ∉ diameterBadA M mm) (hb : r.2 ∉ diameterBadB M mm) :
    Diameters M mm r := by
  have hm := Finset.mem_product.mp hr
  constructor
  · intro u v huv
    by_contra h
    exact ha (Finset.mem_filter.mpr ⟨hm.1, u, v, huv, Nat.lt_of_not_ge h⟩)
  · intro u v huv
    by_contra h
    exact hb (Finset.mem_filter.mpr ⟨hm.2, u, v, huv, Nat.lt_of_not_ge h⟩)

/-- The diameter event and the bounded-pattern avoidance event occur simultaneously. -/
theorem bounded_with_diameter (M : Model) (R K T I B Q Mst J : ℕ)
    (hR : 0 < R) (hK : 0 < K) (hI : 0 < I) (hM : 0 < Mst) :
    ∀ᶠ mm in atTop, ∀ (x : M.SA.V mm) (y : M.SB.V mm),
      ∃ r ∈ samples M mm, Diameters M mm r ∧
        ∀ a : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data R K T I (B * M.L mm),
        BoundedPattern.Data.Good a B Q Mst J (M.L mm) M.ε → ¬BoundedPattern.Data.event M a mm x y r := by
  have hp := (BoundedPattern.polynomial_exp_tendsto M (PatternTotalCoding.coefficient R K T I)
    B (R + 3 * I) Mst hM).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 3)
  have ha := (diameterA_tendsto M).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 3)
  have hb := (diameterB_tendsto M).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 3)
  filter_upwards [hp, ha, hb, BoundedPattern.samples_eventually_nonempty M,
    PatternUniform.eventually_ready M B Mst Q J hM] with mm hp ha hb hs hu
  intro x y
  have hprob := (BoundedPattern.probability_union M R K T I (B * M.L mm) B Q Mst J mm
    hR hK hI hM hs hu x y).trans_lt hp
  have hn := Finset.nonempty_product.mp hs
  have hprob' :
      (((M.samplesA mm ×ˢ M.samplesB mm).filter
        (fun r => ∃ a : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data R K T I (B * M.L mm),
          BoundedPattern.Data.Good a B Q Mst J (M.L mm) M.ε ∧
            BoundedPattern.Data.event M a mm x y r)).card : ℝ) /
        ((M.samplesA mm).card * (M.samplesB mm).card : ℕ) < 1 / 3 := by
    rw [← Finset.card_product]
    exact hprob
  obtain ⟨r, hr, hra, hrb, hrp⟩ := FiniteJointAvoidance.exists_outside
    (M.samplesA mm) (M.samplesB mm) (diameterBadA M mm) (diameterBadB M mm)
    (fun r => ∃ a : OAI.TorsionFreeZeroDivisors.BoundedPattern.Data R K T I (B * M.L mm),
      BoundedPattern.Data.Good a B Q Mst J (M.L mm) M.ε ∧ BoundedPattern.Data.event M a mm x y r)
    hn.1 hn.2 hprob' ha hb
  refine ⟨r, hr, diameters_of_not_bad M mm r hr hra hrb, ?_⟩
  exact fun a hg he => hrp ⟨a, hg, he⟩

end GraphSample

end

end Kaplansky.Random
