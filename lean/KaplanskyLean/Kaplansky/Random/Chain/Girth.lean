import Kaplansky.Random.Chain.StageExpectation
import OAI.Algebra.GroupRing.TwoSideFullStage

/-!
# Girth conditioning for an abstract model

Fork of the model-dependent parts of `OAI/Algebra/GroupRing/TwoSideFullStage.lean`
(`TypedGraphs.exists_conditioned`, `GirthAsymptotics`) and of `TypedGraphs.lean`
(`size`, `eventual_carrier`, `eventual_nonempty`):

* a generic existence lemma for label-respecting fixed-point-free involutions when every
  pool has the size of its inverse pool (replaces OpenAI's `MatchingTuple`);
* the girth-conditioned matching space of each side is nonempty once every pool exceeds
  `4·dmax^(2N+1)` (deterministic switching, OpenAI's `exists_typed_large_girth`);
* the scale `L = ⌊log n / c⌋₊` and the exclusion `4·dmax^(6L+1) = o(n)` when `12 log dmax < c`.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

noncomputable section

namespace MatchingExistence
open scoped Classical
variable {D T : Type*} [Fintype D] [Fintype T] [DecidableEq T] (label : D → T) (bar : T → T)

/-- A choice of one element in each `bar`-orbit, by rank. -/
def pos (t : T) : Prop := Fintype.equivFin T t < Fintype.equivFin T (bar t)

variable (hbal : ∀ t, Fintype.card {d // label d = t} = Fintype.card {d // label d = bar t})

def e (t : T) : {d // label d = t} ≃ {d // label d = bar t} :=
  Fintype.equivOfCardEq (hbal t)

theorem e_congr {t₁ t₂ : T} (h : t₁ = t₂) (x : D) (h1 : label x = t₁) (h2 : label x = t₂) :
    (e label bar hbal t₁ ⟨x, h1⟩).val = (e label bar hbal t₂ ⟨x, h2⟩).val := by
  subst h; rfl

theorem e_symm_congr {t₁ t₂ : T} (h : t₁ = t₂) (x : D) (h1 : label x = bar t₁)
    (h2 : label x = bar t₂) :
    ((e label bar hbal t₁).symm ⟨x, h1⟩).val = ((e label bar hbal t₂).symm ⟨x, h2⟩).val := by
  subst h; rfl

variable (hinv : ∀ t, bar (bar t) = t)

/-- The involution: forwards on positive pools, backwards on the others. -/
def r (d : D) : D :=
  if pos bar (label d) then (e label bar hbal (label d) ⟨d, rfl⟩).val
  else ((e label bar hbal (bar (label d))).symm ⟨d, (hinv (label d)).symm⟩).val

theorem r_label (d : D) : label (r label bar hbal hinv d) = bar (label d) := by
  unfold r
  split_ifs
  · exact (e label bar hbal (label d) ⟨d, rfl⟩).property
  · exact ((e label bar hbal (bar (label d))).symm ⟨d, (hinv (label d)).symm⟩).property

variable (hfree : ∀ t, bar t ≠ t)
include hfree hinv

theorem pos_bar (t : T) : pos bar (bar t) ↔ ¬pos bar t := by
  unfold pos
  rw [hinv t]
  have hne : Fintype.equivFin T t ≠ Fintype.equivFin T (bar t) :=
    fun h => hfree t ((Fintype.equivFin T).injective h).symm
  constructor
  · intro h h'
    exact absurd (lt_trans h h') (lt_irrefl _)
  · intro h
    exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)

omit hfree in
theorem r_pos (d : D) (h : pos bar (label d)) :
    r label bar hbal hinv d = (e label bar hbal (label d) ⟨d, rfl⟩).val := by
  unfold r; rw [if_pos h]

omit hfree in
theorem r_neg (d : D) (h : ¬pos bar (label d)) :
    r label bar hbal hinv d =
      ((e label bar hbal (bar (label d))).symm ⟨d, (hinv (label d)).symm⟩).val := by
  unfold r; rw [if_neg h]

theorem r_r (d : D) : r label bar hbal hinv (r label bar hbal hinv d) = d := by
  have hl := r_label label bar hbal hinv d
  by_cases hp : pos bar (label d)
  · have hq : ¬ pos bar (label (r label bar hbal hinv d)) := by
      rw [hl, pos_bar bar hinv hfree]; exact not_not.mpr hp
    rw [r_neg label bar hbal hinv _ hq,
      e_symm_congr label bar hbal (show bar (label (r label bar hbal hinv d)) = label d by
        rw [hl, hinv]) _ _ (by rw [hl])]
    have hx : (⟨r label bar hbal hinv d, hl⟩ : {x // label x = bar (label d)}) =
        e label bar hbal (label d) ⟨d, rfl⟩ :=
      Subtype.ext (r_pos label bar hbal hinv d hp)
    rw [hx, Equiv.symm_apply_apply]
  · have hq : pos bar (label (r label bar hbal hinv d)) := by
      rw [hl, pos_bar bar hinv hfree]; exact hp
    rw [r_pos label bar hbal hinv _ hq, e_congr label bar hbal hl _ rfl hl]
    have hx : (⟨r label bar hbal hinv d, hl⟩ : {x // label x = bar (label d)}) =
        (e label bar hbal (bar (label d))).symm ⟨d, (hinv (label d)).symm⟩ :=
      Subtype.ext (r_neg label bar hbal hinv d hp)
    rw [hx, Equiv.apply_symm_apply]

include hbal in
/-- Balanced pools admit a label-respecting fixed-point-free involution. -/
theorem exists_matching : Nonempty (ConditionedMatchings.Matching label bar) := by
  have hinvol : Function.Involutive (r label bar hbal hinv) := r_r label bar hbal hinv hfree
  refine ⟨⟨hinvol.toPerm _, hinvol, ?_, r_label label bar hbal hinv⟩⟩
  intro d h
  have hl := r_label label bar hbal hinv d
  change label (r label bar hbal hinv d) = _ at hl
  rw [show (hinvol.toPerm _) d = r label bar hbal hinv d from rfl] at h
  rw [h] at hl
  exact hfree _ hl.symm

end MatchingExistence

/-- The girth-conditioned matching space of a coloured side is nonempty when the pools are
balanced and large (OpenAI `TypedGraphs.exists_conditioned`). -/
theorem conditioned_nonempty {α TV Col : Type} [Fintype TV] [Fintype α] [Fintype Col]
    [DecidableEq α] [DecidableEq Col]
    (inv : α → α) (hinv : ∀ t, inv (inv t) = t) (hfree : ∀ t, inv t ≠ t)
    (flip : Col → Col) (hflip : ∀ c, flip (flip c) = c)
    (col : TV → Col) (out : TV → Finset α) (N dmax : ℕ) (h2 : 2 ≤ dmax)
    (hd : ∀ v, (out v).card ≤ dmax)
    (hbal : ∀ t, Fintype.card {d : PatternEmbeddings.Dart (cout col out) //
        PatternEmbeddings.label (cout col out) d = t} =
      Fintype.card {d : PatternEmbeddings.Dart (cout col out) //
        PatternEmbeddings.label (cout col out) d = cbar inv flip t})
    (hsize : ∀ x : PatternEmbeddings.Dart (cout col out), 4 * dmax ^ (2 * N + 1) <
      Nat.card {e : PatternEmbeddings.Dart (cout col out) //
        PatternEmbeddings.label (cout col out) e = PatternEmbeddings.label (cout col out) x}) :
    (ConditionedMatchings.Matching.conditioned (label := PatternEmbeddings.label (cout col out))
      (bar := cbar inv flip) (PatternEmbeddings.origin (cout col out)) N ∅).Nonempty := by
  classical
  have hcinv : ∀ t, cbar inv flip (cbar inv flip t) = t := by
    intro t; simp [cbar, hinv, hflip]
  have hcfree : ∀ t, cbar inv flip t ≠ t := fun t h => hfree t.1 (congrArg Prod.fst h)
  obtain ⟨r⟩ := MatchingExistence.exists_matching (PatternEmbeddings.label (cout col out))
    (cbar inv flip) hbal hcinv hcfree
  have hdeg : ∀ v, Nat.card {e : PatternEmbeddings.Dart (cout col out) //
      PatternEmbeddings.origin (cout col out) e = v} ≤ dmax := by
    intro v
    have heq : Nat.card {e : PatternEmbeddings.Dart (cout col out) //
        PatternEmbeddings.origin (cout col out) e = v} = (cout col out v).card := by
      rw [Nat.card_eq_fintype_card]
      rw [Fintype.card_congr (show {e : PatternEmbeddings.Dart (cout col out) //
          PatternEmbeddings.origin (cout col out) e = v} ≃ {t // t ∈ cout col out v} from
        { toFun := fun e => ⟨e.val.val.2, by
            have h := e.val.property
            rw [show e.val.val.1 = v from e.property] at h
            exact h⟩
          invFun := fun t => ⟨⟨(v, t.val), t.property⟩, rfl⟩
          left_inv := fun e => by
            apply Subtype.ext; apply Subtype.ext
            exact Prod.ext e.property.symm rfl
          right_inv := fun _ => rfl })]
      exact Fintype.card_coe _
    rw [heq, card_cout]
    exact hd v
  obtain ⟨Γ, hΓo, hΓl, hg⟩ := MatchingGraphs.exists_typed_large_girth
    (PatternEmbeddings.origin (cout col out)) (PatternEmbeddings.label (cout col out))
    (cbar inv flip) (r.graph (PatternEmbeddings.origin (cout col out))) rfl
    (fun e => r.label_reverse e) dmax N h2 hdeg hsize
  let r' : ConditionedMatchings.Matching (PatternEmbeddings.label (cout col out)) (cbar inv flip) :=
    ⟨Γ.reverse_reverse.toPerm Γ.reverse, Γ.reverse_reverse, Γ.reverse_ne, hΓl⟩
  refine ⟨r', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
  · intro a b h
    exact False.elim (Finset.notMem_empty _ h)
  · have he : r'.graph (PatternEmbeddings.origin (cout col out)) = Γ := by
      cases Γ
      simp_all only [ConditionedMatchings.Matching.graph]
      rfl
    rw [he]
    exact hg

namespace GirthAsymptotics

/-- Exclusion cost for the threefold port subdivision (OpenAI: `4·132^(6L+1)`). -/
def exclusion (c dmax n : ℕ) : ℕ := 4 * dmax ^ (6 * scaleL c n + 1)

theorem exclusion_bound (c dmax n : ℕ) (hc : 0 < c) (hdmax : 1 ≤ dmax)
    (hlog : 12 * Real.log dmax < c) (hn : 1 ≤ n) :
    (exclusion c dmax n : ℝ) ≤ 4 * dmax * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hd0 : (0 : ℝ) < dmax := by exact_mod_cast hdmax
  have hld : 0 ≤ Real.log dmax := Real.log_nonneg (by exact_mod_cast hdmax)
  have hf : (scaleL c n : ℝ) ≤ Real.log n / c := Nat.floor_le (by positivity)
  have he : ((6 * scaleL c n : ℕ) : ℝ) * Real.log dmax ≤ Real.log n / 2 := by
    push_cast
    have h1 : 6 * (scaleL c n : ℝ) * Real.log dmax ≤ 6 * (Real.log n / c) * Real.log dmax :=
      mul_le_mul_of_nonneg_right (by linarith) hld
    have h2 : 6 * (Real.log n / c) * Real.log dmax = Real.log n * (6 * Real.log dmax / c) := by
      field_simp
    have h3 : 6 * Real.log dmax / c ≤ 1 / 2 := by
      rw [div_le_iff₀ hc']; linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hl
    linarith
  rw [exclusion, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  have hpow : (dmax : ℝ) ^ (6 * scaleL c n) =
      Real.exp (((6 * scaleL c n : ℕ) : ℝ) * Real.log dmax) := by
    rw [Real.exp_nat_mul, Real.exp_log hd0]
  rw [hpow, Real.rpow_def_of_pos hn0]
  have hx : Real.exp (((6 * scaleL c n : ℕ) : ℝ) * Real.log dmax) ≤
      Real.exp (Real.log n * (1 / 2)) := Real.exp_le_exp.mpr (by linarith)
  nlinarith [Real.exp_pos (((6 * scaleL c n : ℕ) : ℝ) * Real.log dmax)]

theorem exclusion_ratio (c dmax : ℕ) (hc : 0 < c) (hdmax : 1 ≤ dmax)
    (hlog : 12 * Real.log dmax < c) :
    Tendsto (fun n : ℕ => (exclusion c dmax n : ℝ) / n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have ht' := ht.const_mul (4 * (dmax : ℝ))
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) _ ht'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (exclusion c dmax n : ℝ) / n ≤ (4 * dmax * (n : ℝ) ^ (1 / 2 : ℝ)) / n :=
      div_le_div_of_nonneg_right (exclusion_bound c dmax n hc hdmax hlog hn) (le_of_lt hn0)
    _ = 4 * dmax * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [show -(1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub hn0, Real.rpow_one]
      ring

theorem L_tendsto (c : ℕ) (hc : 0 < c) : Tendsto (scaleL c) atTop atTop := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ) / c) atTop atTop := by
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_mul_const
        (inv_pos.mpr hc')
  exact tendsto_nat_floor_atTop.comp hl

theorem L_mono (c : ℕ) {a b : ℕ} (hab : a ≤ b) : scaleL c a ≤ scaleL c b := by
  unfold scaleL
  apply Nat.floor_le_floor
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.cast_zero, Real.log_zero, zero_div]
    exact div_nonneg (Real.log_natCast_nonneg b) (Nat.cast_nonneg _)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)

theorem eventual_small (c dmax : ℕ) (hc : 0 < c) (hdmax : 1 ≤ dmax)
    (hlog : 12 * Real.log dmax < c) (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, (exclusion c dmax n : ℝ) < p * n := by
  filter_upwards [(exclusion_ratio c dmax hc hdmax hlog).eventually_lt_const hp,
    eventually_ge_atTop 1] with n h hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (div_lt_iff₀ hn0).mp h

end GirthAsymptotics

end

end Kaplansky.Random
