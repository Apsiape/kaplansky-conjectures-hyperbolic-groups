import Kaplansky.OddDesign.Params
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Turn weights, the Perron certificate and the squared-word bound (Lemma 7.8)

We work over an arbitrary finite alphabet `T` split into *ordinary* and *extra* letters,
with a fixed-point-free involution `bar` sending extra letters to ordinary ones. For the design
of Section 7 there are `v` ordinary and `s` extra letters.

* `turnW p bar extra t u` is the weight `w(t,u)` of `eq:oddw`;
* `testF p bar extra t` is the test vector `f` of Lemma 7.8;
* `perron_certificate`: `M f ≤ ρ f`, with `M_{t,u} = w(t,u)^2` and `ρ = 1 - 1/(2(q+1))`;
* `squared_word_bound`: `∑_{W ∈ T^{h+1}} P(W)^2 ≤ p^2 |T| ρ^h`.

The word weights `continuation`/`wordWeight` follow OpenAI's `WordEstimate` conventions.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

/-! ### Word weights for an arbitrary weight function -/

section Generic

variable {T : Type*}

/-- Product of the turn weights from a starting letter through a tail. -/
noncomputable def continuation (w : T → T → ℝ) : (n : ℕ) → T → (Fin n → T) → ℝ
  | 0, _, _ => 1
  | n + 1, t, W => w t (W 0) * continuation w n (W 0) (Fin.tail W)

/-- The word weight `P(W) = ∏_{i<h} w(t_i,t_{i+1})`, with empty products equal to one. -/
noncomputable def wordWeight (w : T → T → ℝ) : (h : ℕ) → (Fin h → T) → ℝ
  | 0, _ => 1
  | h + 1, W => continuation w h (W 0) (Fin.tail W)

theorem sum_fin_cons [Fintype T] {n : ℕ} (F : (Fin (n + 1) → T) → ℝ) :
    (∑ W, F W) = ∑ t, ∑ W, F (Fin.cons t W) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => T)).sum_comp F]
  rw [Fintype.sum_prod_type]
  rfl

theorem continuation_eq_product (w : T → T → ℝ) (n : ℕ) (t : T) (W : Fin n → T) :
    continuation w n t W =
      ∏ i : Fin n, w ((Fin.cons t W : Fin (n + 1) → T) i.castSucc)
        ((Fin.cons t W : Fin (n + 1) → T) i.succ) := by
  induction n generalizing t with
  | zero => simp [continuation]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simp only [continuation, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ih]
    simp only [Fin.cons_self_tail, Fin.castSucc_succ, Fin.cons_succ, Fin.tail]

theorem wordWeight_eq_product (w : T → T → ℝ) (h : ℕ) (W : Fin (h + 1) → T) :
    wordWeight w (h + 1) W = ∏ i : Fin h, w (W i.castSucc) (W i.succ) := by
  rw [wordWeight, continuation_eq_product]
  simp only [Fin.cons_self_tail]

/-- Iterating a Perron certificate `M f ≤ ρ f` controls all tails. -/
theorem continuation_mass [Fintype T] (w : T → T → ℝ) (f : T → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hf : ∀ t, 1 ≤ f t) (hM : ∀ t, ∑ u, w t u ^ 2 * f u ≤ ρ * f t) (n : ℕ) (t : T) :
    (∑ W : Fin n → T, continuation w n t W ^ 2) ≤ ρ ^ n * f t := by
  induction n generalizing t with
  | zero => simpa [continuation] using hf t
  | succ n ih =>
    rw [sum_fin_cons]
    simp only [continuation, Fin.cons_zero, Fin.tail_cons, mul_pow]
    simp_rw [← Finset.mul_sum]
    calc
      ∑ u, w t u ^ 2 * ∑ W : Fin n → T, continuation w n u W ^ 2
          ≤ ∑ u, w t u ^ 2 * (ρ ^ n * f u) := by
            apply Finset.sum_le_sum
            intro u _
            exact mul_le_mul_of_nonneg_left (ih u) (sq_nonneg _)
      _ = ρ ^ n * ∑ u, w t u ^ 2 * f u := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
      _ ≤ ρ ^ n * (ρ * f t) := by
            apply mul_le_mul_of_nonneg_left (hM t)
            positivity
      _ = ρ ^ (n + 1) * f t := by ring

/-- The matrix form of the squared-word estimate: `∑_W P(W)^2 = 1ᵀ M^h 1 ≤ ρ^h ∑_t f(t)`. -/
theorem squared_word_bound_of_perron [Fintype T] (w : T → T → ℝ) (f : T → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hf : ∀ t, 1 ≤ f t) (hM : ∀ t, ∑ u, w t u ^ 2 * f u ≤ ρ * f t) (h : ℕ) :
    (∑ W : Fin (h + 1) → T, wordWeight w (h + 1) W ^ 2) ≤ ρ ^ h * ∑ t, f t := by
  rw [sum_fin_cons]
  simp only [wordWeight, Fin.cons_zero, Fin.tail_cons]
  calc
    ∑ t, ∑ W : Fin h → T, continuation w h t W ^ 2 ≤ ∑ t, ρ ^ h * f t :=
      Finset.sum_le_sum fun t _ => continuation_mass w f ρ hρ hf hM h t
    _ = ρ ^ h * ∑ t, f t := by rw [Finset.mul_sum]

end Generic

/-! ### The turn weights of `eq:oddw` -/

section Split

variable {T : Type*}
variable (p : ℕ) (bar : T → T) (extra : T → Prop) [DecidablePred extra]

/-- The joint weight of two letters `a = t̄` and `b = u` before excluding cancellation:
`1/(q+1)` for two ordinary letters, `λ` for one ordinary and one extra, `γ` for two extras. -/
noncomputable def baseW (a b : T) : ℝ :=
  if extra a then (if extra b then gam p else lam p)
  else (if extra b then lam p else 1 / ((q p : ℝ) + 1))

theorem baseW_comm (a b : T) : baseW p extra a b = baseW p extra b a := by
  unfold baseW
  by_cases ha : extra a <;> by_cases hb : extra b <;> simp [ha, hb]

theorem baseW_nonneg {p : ℕ} (hp : 1 ≤ p) (a b : T) : 0 ≤ baseW p extra a b := by
  have := lam_pos p
  have := gam_nonneg hp
  unfold baseW
  split_ifs <;> first | linarith | positivity

theorem baseW_le_one (a b : T) : baseW p extra a b ≤ 1 := by
  have := lam_le_one p
  have := gam_le_one p
  have hq : (0 : ℝ) ≤ q p := Nat.cast_nonneg _
  unfold baseW
  split_ifs
  · exact this
  · assumption
  · assumption
  · rw [div_le_one (by positivity)]; linarith

theorem baseW_ge {p : ℕ} (hp : 2 ≤ p) (a b : T) :
    1 / ((q p : ℝ) + 1) ≤ baseW p extra a b := by
  have := inv_q_succ_le_lam p
  have := inv_q_succ_le_gam hp
  unfold baseW
  split_ifs <;> first | assumption | exact le_rfl

/-- The test vector `f` of Lemma 7.8: `p^2` if `t̄` is extra, `1` otherwise. -/
noncomputable def testF (t : T) : ℝ :=
  if extra (bar t) then (p : ℝ) ^ 2 else 1

theorem testF_ge_one {p : ℕ} (hp : 1 ≤ p) (t : T) : 1 ≤ testF p bar extra t := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  unfold testF
  split_ifs
  · nlinarith
  · exact le_rfl

theorem testF_le {p : ℕ} (hp : 1 ≤ p) (t : T) : testF p bar extra t ≤ (p : ℝ) ^ 2 := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  unfold testF
  split_ifs
  · exact le_rfl
  · nlinarith

/-! #### Exact row masses -/

variable {bar extra}

/-- Extra letters are carried to ordinary ones, and `bar` is involutive: then exactly as many
ordinary letters have extra partners as there are extra letters. -/
theorem card_ord_bar_extra [Fintype T] (hbar : Function.Involutive bar)
    (hbarE : ∀ t, extra t → ¬ extra (bar t)) :
    (univ.filter (fun u => ¬ extra u ∧ extra (bar u))).card = (univ.filter extra).card := by
  apply Finset.card_nbij' bar bar
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    exact hu.2
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    rw [hbar u]
    exact ⟨hbarE u hu, hu⟩
  · intro u _; exact hbar u
  · intro u _; exact hbar u

theorem sum_testF_extra [Fintype T] (hbarE : ∀ t, extra t → ¬ extra (bar t)) :
    ∑ u ∈ univ.filter extra, testF p bar extra u = (univ.filter extra).card := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [mem_filter] at hu
  simp [testF, hbarE u hu.2]

theorem sum_testF_ord [Fintype T] (hbar : Function.Involutive bar)
    (hbarE : ∀ t, extra t → ¬ extra (bar t)) :
    ∑ u ∈ univ.filter (fun u => ¬ extra u), testF p bar extra u =
      (univ.filter (fun u => ¬ extra u)).card +
        ((p : ℝ) ^ 2 - 1) * (univ.filter extra).card := by
  have h1 : ∀ u ∈ univ.filter (fun u => ¬ extra u), testF p bar extra u =
      1 + ((p : ℝ) ^ 2 - 1) * (if extra (bar u) then 1 else 0) := by
    intro u _
    unfold testF
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    filter_filter, card_ord_bar_extra hbar hbarE]
  simp

/-- The full (uncancelled) row mass at `a`. -/
theorem sum_baseW_sq [Fintype T] (hbar : Function.Involutive bar)
    (hbarE : ∀ t, extra t → ¬ extra (bar t)) (a : T) :
    ∑ u, baseW p extra a u ^ 2 * testF p bar extra u =
      (if extra a then gam p else lam p) ^ 2 * (univ.filter extra).card +
      (if extra a then lam p else 1 / ((q p : ℝ) + 1)) ^ 2 *
        ((univ.filter (fun u => ¬ extra u)).card +
          ((p : ℝ) ^ 2 - 1) * (univ.filter extra).card) := by
  rw [← Finset.sum_filter_add_sum_filter_not univ extra]
  congr 1
  · rw [← sum_testF_extra p hbarE, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [mem_filter] at hu
    unfold baseW
    by_cases ha : extra a <;> simp [ha, hu.2]
  · rw [← sum_testF_ord p hbar hbarE, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [mem_filter] at hu
    unfold baseW
    by_cases ha : extra a <;> simp [ha, hu.2]

variable (bar extra) [DecidableEq T]


/-- The turn weight `w(t,u)` of `eq:oddw`: zero on the cancelling turn `u = t̄`. -/
noncomputable def turnW (t u : T) : ℝ :=
  if u = bar t then 0 else baseW p extra (bar t) u

theorem turnW_nonneg {p : ℕ} (hp : 1 ≤ p) (t u : T) : 0 ≤ turnW p bar extra t u := by
  unfold turnW
  split_ifs
  · exact le_rfl
  · exact baseW_nonneg extra hp _ _

theorem turnW_le_one (t u : T) : turnW p bar extra t u ≤ 1 := by
  unfold turnW
  split_ifs
  · norm_num
  · exact baseW_le_one p extra _ _

/-- The smallest positive turn weight is `1/(q+1)`. -/
theorem turnW_pos_lower {p : ℕ} (hp : 2 ≤ p) (t u : T) (h : 0 < turnW p bar extra t u) :
    1 / ((q p : ℝ) + 1) ≤ turnW p bar extra t u := by
  unfold turnW at *
  split_ifs at * with h'
  · exact absurd h (lt_irrefl 0)
  · exact baseW_ge extra hp _ _

/-- `w(t,u) = w(ū,t̄)`. -/
theorem turnW_symm (hbar : Function.Involutive bar) (t u : T) :
    turnW p bar extra t u = turnW p bar extra (bar u) (bar t) := by
  unfold turnW
  rw [hbar u]
  by_cases h : u = bar t
  · simp [h]
  · have h' : ¬ bar t = u := fun e => h e.symm
    simp only [h, h', ↓reduceIte]
    exact baseW_comm p extra _ _

/-- Removing the cancelling turn removes exactly its diagonal summand. -/
theorem row_mass [Fintype T] (t : T) :
    ∑ u, turnW p bar extra t u ^ 2 * testF p bar extra u =
      ∑ u, baseW p extra (bar t) u ^ 2 * testF p bar extra u -
        baseW p extra (bar t) (bar t) ^ 2 * testF p bar extra (bar t) := by
  have h1 := Finset.sum_erase_add univ
    (fun u => turnW p bar extra t u ^ 2 * testF p bar extra u) (mem_univ (bar t))
  have h2 := Finset.sum_erase_add univ
    (fun u => baseW p extra (bar t) u ^ 2 * testF p bar extra u) (mem_univ (bar t))
  have h3 : ∑ u ∈ univ.erase (bar t), turnW p bar extra t u ^ 2 * testF p bar extra u =
      ∑ u ∈ univ.erase (bar t), baseW p extra (bar t) u ^ 2 * testF p bar extra u := by
    apply Finset.sum_congr rfl
    intro u hu
    simp only [turnW, Finset.ne_of_mem_erase hu, ↓reduceIte]
  have h4 : turnW p bar extra t (bar t) = 0 := by simp [turnW]
  rw [← h1, ← h2, h3, h4]
  ring

/-! #### The two row bounds -/

/-- Row bound when `t̄` is ordinary. -/
theorem row_bound_ord {p : ℕ} (hp : 3 ≤ p) :
    lam p ^ 2 * (s p : ℝ) + ((v p : ℝ) - 1 + ((p : ℝ) ^ 2 - 1) * s p) / ((q p : ℝ) + 1) ^ 2
      ≤ rho p := by
  have hq := q_real_pos (by omega : 0 < p)
  have hS : (0 : ℝ) < s p := by exact_mod_cast s_pos p
  have hP : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hl := lam_sq_le (by omega : 0 < p)
  have hkey := s_psq_div_le hp
  -- split off the main term `q/(q+1)`
  have hsplit : ((v p : ℝ) - 1 + ((p : ℝ) ^ 2 - 1) * s p) / ((q p : ℝ) + 1) ^ 2 =
      (q p : ℝ) / ((q p : ℝ) + 1) + ((p : ℝ) ^ 2 - 1) * s p / ((q p : ℝ) + 1) ^ 2 := by
    rw [v_real]; field_simp; ring
  have hrho : rho p = (q p : ℝ) / ((q p : ℝ) + 1) + 1 / (2 * ((q p : ℝ) + 1)) := by
    unfold rho; field_simp; ring
  have h3 : ((p : ℝ) ^ 2 - 1) * s p / ((q p : ℝ) + 1) ^ 2 ≤
      ((p : ℝ) ^ 2 - 1) * s p / (q p : ℝ) ^ 2 := by
    have hP2 : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
    apply div_le_div_of_nonneg_left (mul_nonneg hP2 hS.le) (by positivity) (by nlinarith)
  have h4 : lam p ^ 2 * (s p : ℝ) ≤ (s p : ℝ) / (q p : ℝ) ^ 2 := by
    calc lam p ^ 2 * (s p : ℝ) ≤ 1 / (q p : ℝ) ^ 2 * s p := by gcongr
      _ = (s p : ℝ) / (q p : ℝ) ^ 2 := by ring
  have h5 : (s p : ℝ) / (q p : ℝ) ^ 2 + ((p : ℝ) ^ 2 - 1) * s p / (q p : ℝ) ^ 2 =
      (s p : ℝ) * (p : ℝ) ^ 2 / (q p : ℝ) ^ 2 := by
    field_simp; ring
  rw [hsplit, hrho]
  linarith

/-- Row bound when `t̄` is extra. -/
theorem row_bound_extra {p : ℕ} (hp : 3 ≤ p) :
    gam p ^ 2 * ((s p : ℝ) - 1) + lam p ^ 2 * ((v p : ℝ) + ((p : ℝ) ^ 2 - 1) * s p)
      ≤ rho p * (p : ℝ) ^ 2 := by
  have hq := q_real_pos (by omega : 0 < p)
  have hS : (0 : ℝ) < s p := by exact_mod_cast s_pos p
  have hP : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hl := lam_sq_le (by omega : 0 < p)
  have hkey := s_psq_div_le hp
  have hvl := v_lam_sq_le (by omega : 0 < p)
  have hqP : (q p : ℝ) = (p : ℝ) ^ 5 := cast_q p
  have hsP : (s p : ℝ) = (p : ℝ) ^ 2 + p + 1 := cast_s p
  -- the extra–extra part
  have hg : gam p ^ 2 * ((s p : ℝ) - 1) = (p : ℝ) ^ 2 - p - 1 + 1 / p := by
    rw [gam, hsP]; field_simp; ring
  -- the small part
  have h1 : lam p ^ 2 * (((p : ℝ) ^ 2 - 1) * s p) ≤ 1 / (2 * ((q p : ℝ) + 1)) := by
    calc lam p ^ 2 * (((p : ℝ) ^ 2 - 1) * s p) ≤ 1 / (q p : ℝ) ^ 2 * (((p : ℝ) ^ 2 - 1) * s p) := by
          gcongr; nlinarith
      _ ≤ (s p : ℝ) * (p : ℝ) ^ 2 / (q p : ℝ) ^ 2 := by
          rw [div_mul_eq_mul_div, one_mul]
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
      _ ≤ _ := hkey
  have hexp : lam p ^ 2 * ((v p : ℝ) + ((p : ℝ) ^ 2 - 1) * s p) =
      (v p : ℝ) * lam p ^ 2 + lam p ^ 2 * (((p : ℝ) ^ 2 - 1) * s p) := by ring
  have hrho : rho p * (p : ℝ) ^ 2 = (p : ℝ) ^ 2 - (p : ℝ) ^ 2 / (2 * ((q p : ℝ) + 1)) := by
    unfold rho; ring
  -- the three error terms are each at most one
  have e1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have e2 : 1 / (q p : ℝ) ≤ 1 := by
    rw [div_le_one hq, hqP]
    have : (1 : ℝ) ≤ (p : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    linarith
  have e3 : 1 / (2 * ((q p : ℝ) + 1)) + (p : ℝ) ^ 2 / (2 * ((q p : ℝ) + 1)) ≤ 1 := by
    rw [← add_div, div_le_one (by positivity), hqP]
    have : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  rw [hg, hexp, hrho]
  linarith

variable {bar extra}

/-- **Perron certificate** (Lemma 7.8, `eq:perron`): `M f ≤ ρ f` for `M_{t,u} = w(t,u)^2`.
The hypotheses say that `bar` is an involution sending extra letters to ordinary ones, and that
there are `v` ordinary and `s` extra letters. -/
theorem perron_certificate [Fintype T] {p : ℕ} (hp : 3 ≤ p) (hbar : Function.Involutive bar)
    (hbarE : ∀ t, extra t → ¬ extra (bar t))
    (hO : (univ.filter (fun u => ¬ extra u)).card = v p)
    (hE : (univ.filter extra).card = s p) (t : T) :
    ∑ u, turnW p bar extra t u ^ 2 * testF p bar extra u ≤ rho p * testF p bar extra t := by
  rw [row_mass, sum_baseW_sq p hbar hbarE, hO, hE]
  by_cases ha : extra (bar t)
  · -- `t̄` extra: `f(t̄) = 1`, `f(t) = p^2`
    have hnt : ¬ extra t := by
      have := hbarE _ ha
      rwa [hbar t] at this
    have hf1 : testF p bar extra (bar t) = 1 := by
      simp [testF, hbar t, hnt]
    have hft : testF p bar extra t = (p : ℝ) ^ 2 := by simp [testF, ha]
    simp only [ha, ite_true, hf1, hft, baseW]
    have := row_bound_extra hp
    nlinarith
  · -- `t̄` ordinary: `f(t) = 1`, `f(t̄) ≥ 1`
    have hft : testF p bar extra t = 1 := by simp [testF, ha]
    have hf1 := testF_ge_one bar extra (by omega : 1 ≤ p) (bar t)
    simp only [ha, ite_false, hft, baseW, mul_one]
    have := row_bound_ord hp
    have hq : (0 : ℝ) ≤ q p := Nat.cast_nonneg _
    have hdiv : ((v p : ℝ) + ((p : ℝ) ^ 2 - 1) * s p) / ((q p : ℝ) + 1) ^ 2 -
        testF p bar extra (bar t) / ((q p : ℝ) + 1) ^ 2 ≤
        ((v p : ℝ) - 1 + ((p : ℝ) ^ 2 - 1) * s p) / ((q p : ℝ) + 1) ^ 2 := by
      rw [← sub_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have e1 : (1 / ((q p : ℝ) + 1)) ^ 2 * ((v p : ℝ) + ((p : ℝ) ^ 2 - 1) * s p) =
        ((v p : ℝ) + ((p : ℝ) ^ 2 - 1) * s p) / ((q p : ℝ) + 1) ^ 2 := by
      field_simp
    have e2 : (1 / ((q p : ℝ) + 1)) ^ 2 * testF p bar extra (bar t) =
        testF p bar extra (bar t) / ((q p : ℝ) + 1) ^ 2 := by
      field_simp
    rw [e1, e2]
    linarith

omit [DecidableEq T] in
/-- `∑_t f(t) ≤ p^2 |T|`. -/
theorem sum_testF_le [Fintype T] {p : ℕ} (hp : 1 ≤ p) :
    ∑ t, testF p bar extra t ≤ (p : ℝ) ^ 2 * Fintype.card T := by
  calc ∑ t, testF p bar extra t ≤ ∑ _t : T, (p : ℝ) ^ 2 :=
        Finset.sum_le_sum fun t _ => testF_le bar extra hp t
    _ = (p : ℝ) ^ 2 * Fintype.card T := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **Squared-word bound** (Lemma 7.8): `∑_{W ∈ T^{h+1}} P(W)^2 ≤ p^2 |T| ρ^h`. -/
theorem squared_word_bound [Fintype T] {p : ℕ} (hp : 3 ≤ p) (hbar : Function.Involutive bar)
    (hbarE : ∀ t, extra t → ¬ extra (bar t))
    (hO : (univ.filter (fun u => ¬ extra u)).card = v p)
    (hE : (univ.filter extra).card = s p) (h : ℕ) :
    (∑ W : Fin (h + 1) → T, wordWeight (turnW p bar extra) (h + 1) W ^ 2) ≤
      (p : ℝ) ^ 2 * Fintype.card T * rho p ^ h := by
  have hρ : 0 ≤ rho p := (rho_pos p).le
  calc (∑ W : Fin (h + 1) → T, wordWeight (turnW p bar extra) (h + 1) W ^ 2)
      ≤ rho p ^ h * ∑ t, testF p bar extra t :=
        squared_word_bound_of_perron _ _ _ hρ (testF_ge_one bar extra (by omega))
          (perron_certificate hp hbar hbarE hO hE) h
    _ ≤ rho p ^ h * ((p : ℝ) ^ 2 * Fintype.card T) := by
        gcongr
        exact sum_testF_le (by omega)
    _ = (p : ℝ) ^ 2 * Fintype.card T * rho p ^ h := by ring

end Split

end Kaplansky.OddDesign
