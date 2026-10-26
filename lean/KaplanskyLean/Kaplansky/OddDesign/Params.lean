import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# The parameters of Section 7 (`eq:oddparams`)

For a prime `p` (odd in all applications),
`q = p^5`, `v = q^2+q+1`, `s = p^2+p+1`, `λ = (q+1)/v`, `γ = (p-1)/p` and
`ρ = 1 - 1/(2(q+1))`.

The main numerical fact is the key inequality `eq:keyineq`, `2 s p^2 (q+1) < q^2` for `p ≥ 3`.
-/

namespace Kaplansky.OddDesign

/-- `q = p^5`, the order of the big plane. -/
def q (p : ℕ) : ℕ := p ^ 5

/-- `v = q^2+q+1`, the number of points (and of lines) of `PG(2,q)`. -/
def v (p : ℕ) : ℕ := q p ^ 2 + q p + 1

/-- `s = p^2+p+1`, the number of points (and of lines) of `PG(2,p)`. -/
def s (p : ℕ) : ℕ := p ^ 2 + p + 1

/-- `λ = (q+1)/v`, the proportion of lines of `PG(2,q)` through a point. -/
noncomputable def lam (p : ℕ) : ℝ := ((q p : ℝ) + 1) / (v p : ℝ)

/-- `γ = (p-1)/p`, the turn weight between two distinct extra letters. -/
noncomputable def gam (p : ℕ) : ℝ := ((p : ℝ) - 1) / p

/-- `ρ = 1 - 1/(2(q+1))`, the Perron ratio of Lemma 7.8. -/
noncomputable def rho (p : ℕ) : ℝ := 1 - 1 / (2 * ((q p : ℝ) + 1))

theorem v_eq (p : ℕ) : v p = p ^ 10 + p ^ 5 + 1 := by
  simp only [v, q]; ring

theorem q_pos {p : ℕ} (hp : 0 < p) : 0 < q p := by
  unfold q; positivity

theorem v_pos (p : ℕ) : 0 < v p := by
  unfold v; omega

theorem s_pos (p : ℕ) : 0 < s p := by
  unfold s; omega

theorem cast_q (p : ℕ) : ((q p : ℕ) : ℝ) = (p : ℝ) ^ 5 := by
  simp [q]

theorem cast_v (p : ℕ) : ((v p : ℕ) : ℝ) = (p : ℝ) ^ 10 + (p : ℝ) ^ 5 + 1 := by
  rw [v_eq]; push_cast; ring

theorem cast_s (p : ℕ) : ((s p : ℕ) : ℝ) = (p : ℝ) ^ 2 + p + 1 := by
  simp [s]

/-- The key inequality `eq:keyineq` of the paper: `2 s p^2 (q+1) < q^2` for `p ≥ 3`.
(This is where `q = p^5` is needed.) -/
theorem key_ineq {p : ℕ} (hp : 3 ≤ p) : 2 * s p * p ^ 2 * (q p + 1) < q p ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 3 := ⟨p - 3, by omega⟩
  have h : q (k + 3) ^ 2 = 2 * s (k + 3) * (k + 3) ^ 2 * (q (k + 3) + 1) +
      (k ^ 10 + 28 * k ^ 9 + 349 * k ^ 8 + 2542 * k ^ 7 + 11928 * k ^ 6 + 37422 * k ^ 5 +
        78622 * k ^ 4 + 107056 * k ^ 3 + 86623 * k ^ 2 + 33252 * k + 1953) := by
    simp only [q, s]; ring
  omega

/-- The key inequality over the reals. -/
theorem key_ineq_real {p : ℕ} (hp : 3 ≤ p) :
    2 * (s p : ℝ) * (p : ℝ) ^ 2 * ((q p : ℝ) + 1) < (q p : ℝ) ^ 2 := by
  exact_mod_cast key_ineq hp

theorem v_real (p : ℕ) : (v p : ℝ) = (q p : ℝ) ^ 2 + q p + 1 := by
  simp [v]

theorem q_real_pos {p : ℕ} (hp : 0 < p) : (0 : ℝ) < q p := by
  exact_mod_cast q_pos hp

theorem v_real_pos (p : ℕ) : (0 : ℝ) < v p := by
  exact_mod_cast v_pos p

/-- `λ < 1/q`. -/
theorem lam_lt {p : ℕ} (hp : 0 < p) : lam p < 1 / (q p : ℝ) := by
  have hq := q_real_pos hp
  have hv := v_real_pos p
  rw [lam, div_lt_div_iff₀ hv hq, v_real]
  nlinarith

theorem lam_pos (p : ℕ) : 0 < lam p := by
  have hv := v_real_pos p
  unfold lam; positivity

/-- `λ^2 ≤ 1/q^2`. -/
theorem lam_sq_le {p : ℕ} (hp : 0 < p) : lam p ^ 2 ≤ 1 / (q p : ℝ) ^ 2 := by
  have h := lam_lt hp
  have h0 := lam_pos p
  rw [one_div, ← inv_pow, ← one_div]
  gcongr

/-- `v λ^2 ≤ 1 + 1/q`. -/
theorem v_lam_sq_le {p : ℕ} (hp : 0 < p) : (v p : ℝ) * lam p ^ 2 ≤ 1 + 1 / (q p : ℝ) := by
  have hq := q_real_pos hp
  have hv := v_real_pos p
  rw [lam, div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  rw [one_add_div hq.ne', div_mul_eq_mul_div, le_div_iff₀ hq, v_real]
  nlinarith

/-- `1 ≤ ... `: the smallest positive weight `1/(q+1)` is at most `λ`. -/
theorem inv_q_succ_le_lam (p : ℕ) : 1 / ((q p : ℝ) + 1) ≤ lam p := by
  have hv := v_real_pos p
  have hq : (0 : ℝ) ≤ q p := Nat.cast_nonneg _
  rw [lam, div_le_div_iff₀ (by positivity) hv, v_real]
  nlinarith

theorem lam_le_one (p : ℕ) : lam p ≤ 1 := by
  have hv := v_real_pos p
  have hq : (0 : ℝ) ≤ q p := Nat.cast_nonneg _
  rw [lam, div_le_one hv, v_real]
  nlinarith

theorem gam_nonneg {p : ℕ} (hp : 1 ≤ p) : 0 ≤ gam p := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  unfold gam
  apply div_nonneg <;> linarith

theorem gam_le_one (p : ℕ) : gam p ≤ 1 := by
  unfold gam
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · have : (0 : ℝ) < p := by exact_mod_cast h
    rw [div_le_one this]; linarith

theorem inv_q_succ_le_gam {p : ℕ} (hp : 2 ≤ p) : 1 / ((q p : ℝ) + 1) ≤ gam p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : (p : ℝ) ^ 5 = q p := (cast_q p).symm
  have hq2 : (p : ℝ) ≤ (q p : ℝ) := by
    rw [← hq]
    have : (1 : ℝ) ≤ p := by linarith
    calc (p : ℝ) = p * 1 * 1 * 1 * 1 := by ring
      _ ≤ p * p * p * p * p := by gcongr
      _ = p ^ 5 := by ring
  unfold gam
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem rho_pos (p : ℕ) : 0 < rho p := by
  have hq : (0 : ℝ) ≤ q p := Nat.cast_nonneg _
  unfold rho
  rw [sub_pos, div_lt_one (by positivity)]
  linarith

theorem rho_lt_one (p : ℕ) : rho p < 1 := by
  have hq : (0 : ℝ) ≤ q p := Nat.cast_nonneg _
  unfold rho
  have : 0 < 1 / (2 * ((q p : ℝ) + 1)) := by positivity
  linarith

/-- `s p^2 / q^2 ≤ 1/(2(q+1))`: the key inequality in the form used twice in Lemma 7.8. -/
theorem s_psq_div_le {p : ℕ} (hp : 3 ≤ p) :
    (s p : ℝ) * (p : ℝ) ^ 2 / (q p : ℝ) ^ 2 ≤ 1 / (2 * ((q p : ℝ) + 1)) := by
  have hq := q_real_pos (by omega : 0 < p)
  have hk := key_ineq_real hp
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end Kaplansky.OddDesign
