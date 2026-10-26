import Kaplansky.Random.Alphabet

/-!
# The alphabet of OpenAI's direct-finiteness model (OAI197a §3.1–3.2)

Letters are the `v = 16513` points of `PG(2,128)` and seven extra letters (the points of the
Fano plane).  Each extra letter is paired with a distinct ordinary letter and the remaining
`16506` ordinary letters are paired among themselves.  We use the signed-generator coordinates
`(Fin 7 ⊕ Fin 8253) × Bool`: the extra letters are `(inl i, true)`, their partners
`(inl i, false)`, and the involution flips the sign.  (Ordinary letters are identified with
points of `PG(2,128)` by a fixed bijection in `OAI197a.lean`.)

Turn weights (OAI197a eq. (turn-weights)): `1/(q+1)` for two ordinary letters, `p = 129/16513`
for one ordinary and one extra letter, and `1/2` for two extra letters.

Decay (OAI197a Lemma 3.2): with `f = 4` on letters whose inverse is extra and `f = 1` otherwise,
`M f ≤ (1 - 3/600) f`, so `∑ P(W)^2 ≤ exp(-2h/600)` from `h₀ = 10·600 + 3` on.
-/

namespace Kaplansky.Random.OAI197a

open scoped BigOperators

abbrev Letter := (Fin 7 ⊕ Fin 8253) × Bool

def inverse (t : Letter) : Letter := (t.1, !t.2)

def IsExtra (t : Letter) : Prop := ∃ i : Fin 7, t = (Sum.inl i, true)

instance (t : Letter) : Decidable (IsExtra t) := inferInstanceAs (Decidable (∃ _, _))

@[simp] theorem isExtra_inl (i : Fin 7) (b : Bool) :
    IsExtra (Sum.inl i, b) ↔ b = true := by simp [IsExtra, Prod.mk.injEq]

@[simp] theorem not_isExtra_inr (i : Fin 8253) (b : Bool) :
    ¬IsExtra (Sum.inr i, b) := by simp [IsExtra]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  simp [inverse]

theorem inverse_ne (t : Letter) : inverse t ≠ t := by
  rcases t with ⟨i, b⟩
  cases b <;> simp [inverse]

theorem extra_inverse_not_extra (t : Letter) (h : IsExtra t) : ¬IsExtra (inverse t) := by
  obtain ⟨i, rfl⟩ := h
  simp [inverse]

/-- Letter density `p = (q+1)/v`. -/
noncomputable def pp : ℝ := 129 / 16513

/-- Joint weight of two outgoing letters. -/
noncomputable def J (a b : Letter) : ℝ :=
  if IsExtra a then (if IsExtra b then 1 / 2 else pp) else (if IsExtra b then pp else 1 / 129)

theorem J_nonneg (a b : Letter) : 0 ≤ J a b := by
  unfold J pp; split_ifs <;> norm_num

theorem J_le_one (a b : Letter) : J a b ≤ 1 := by
  unfold J pp; split_ifs <;> norm_num

theorem J_ge (a b : Letter) : 1 / (129 : ℝ) ≤ J a b := by
  unfold J pp; split_ifs <;> norm_num

/-- The alphabet of the OAI197a model. -/
noncomputable def alphabet : Alphabet where
  α := Letter
  inv := inverse
  inv_inv := inverse_inverse
  inv_ne := inverse_ne
  J := J
  J_nonneg := J_nonneg
  J_le_one := J_le_one
  W := 129
  W_pos := by norm_num
  J_ge := fun a b _ => by exact_mod_cast J_ge a b

/-- The Perron test vector. -/
noncomputable def f (t : Letter) : ℝ := if IsExtra (inverse t) then 4 else 1

theorem one_le_f (t : Letter) : 1 ≤ f t := by
  unfold f; split_ifs <;> norm_num

theorem f_extra (t : Letter) (h : IsExtra t) : f t = 1 := by
  simp [f, extra_inverse_not_extra t h]

theorem sum_f : (∑ t : Letter, f t) = 16541 := by
  simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type, f, inverse]
  norm_num

theorem base_row_mass (a : Letter) :
    (∑ u : Letter, J a u ^ 2 * f u) =
      if IsExtra a then 7 / 4 + 16534 * pp ^ 2
      else 7 * pp ^ 2 + 16534 / 129 ^ 2 := by
  unfold J
  split_ifs with h
  · simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type, f, inverse]
    ring
  · simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type, f, inverse]
    ring

theorem weight_eq (t u : Letter) :
    alphabet.weight t u = if u = inverse t then 0 else J (inverse t) u := rfl

theorem row_mass (t : Letter) :
    (∑ u : Letter, alphabet.weight t u ^ 2 * f u) =
      (∑ u : Letter, J (inverse t) u ^ 2 * f u) - J (inverse t) (inverse t) ^ 2 * f (inverse t) := by
  classical
  have h (u : Letter) : alphabet.weight t u ^ 2 * f u =
      J (inverse t) u ^ 2 * f u - if u = inverse t then J (inverse t) u ^ 2 * f u else 0 := by
    by_cases hu : u = inverse t <;> simp [weight_eq, hu]
  simp_rw [h, Finset.sum_sub_distrib]
  simp

/-- `M f ≤ (1 - 3/600) f`. -/
theorem matrix_contraction (t : Letter) :
    (∑ u : Letter, alphabet.weight t u ^ 2 * f u) ≤ (1 - 3 / (600 : ℝ)) * f t := by
  rw [row_mass, base_row_mass]
  by_cases h : IsExtra (inverse t)
  · have hfi : f (inverse t) = 1 := f_extra _ h
    have hft : f t = 4 := by simp [f, h]
    simp only [h, ite_true, J, hfi, hft]
    norm_num [pp]
  · have hf := one_le_f (inverse t)
    have hft : f t = 1 := by simp [f, h]
    simp only [h, ite_false, J, hft]
    norm_num [pp]
    nlinarith

theorem sum_f_le : (∑ t : Letter, f t) ≤ Real.exp 10 := by
  rw [sum_f]
  calc
    (16541 : ℝ) ≤ (27 / 10 : ℝ) ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := by
      gcongr
      exact le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
    _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num

/-- Squared-word decay with `δ = 1/600` from `h₀ = 6003` on. -/
theorem decays : alphabet.Decays 600 (10 * 600 + 3) :=
  alphabet.decays_of_perron f 600 10 (by norm_num) one_le_f
    (fun t => by
      have := matrix_contraction t
      exact_mod_cast this)
    sum_f_le

theorem log_129_le : 2 * Real.log (129 : ℕ) ≤ (10 : ℕ) := by
  have h : Real.log (129 : ℝ) < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)) 5
    rw [← Real.exp_nat_mul] at h1
    norm_num at h1 ⊢
    linarith
  push_cast
  linarith

end Kaplansky.Random.OAI197a
