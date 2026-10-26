import Mathlib

/-!
# Weighted signed alphabets and squared-word decay (generic `WordEstimate`)

This file generalizes OpenAI's `OAI.TorsionFreeZeroDivisors.WordEstimate` (vendored at
`OAI/Algebra/GroupRing/WordEstimate.lean`), which is stated for one hard-coded alphabet
`(Fin 3 ⊕ Fin 8255) × Bool`, one weight table and the constants `δ = 1/600`, `h₀ = 3002`,
`a₀ = 256`.

Here an `Alphabet` is an arbitrary finite signed alphabet with a joint-weight table `J`
whose positive values are at least `1/W`, together with a squared-word decay estimate
`∑_{W ∈ α^h} P(W)^2 ≤ exp(-2h/D)` for `h ≥ h₀`. The decay is obtained for concrete models
from a Perron certificate (`decay_of_perron`), as in OAI196 Lemma 2.1, OAI197a Lemma 3.2 and
the paper's Lemmas 6.3 and 7.8. All bin estimates of `WordEstimate` are reproved with the
symbolic constants `D` (δ = 1/D), `h₀`, `W` and `A₀` (a₀).
-/

namespace Kaplansky.Random

open scoped BigOperators

/-- The word-weight part of a random model: a signed alphabet, joint weights, and a
squared-word decay certificate.  `J a b` is the joint weight of two distinct outgoing letters
at a vertex; the turn weight is `weight t u = J (inv t) u` for `u ≠ inv t`. -/
structure Alphabet where
  α : Type
  [fα : Fintype α]
  [dα : DecidableEq α]
  [nα : Nonempty α]
  inv : α → α
  inv_inv : ∀ t, inv (inv t) = t
  inv_ne : ∀ t, inv t ≠ t
  J : α → α → ℝ
  J_nonneg : ∀ a b, 0 ≤ J a b
  J_le_one : ∀ a b, J a b ≤ 1
  /-- the smallest positive joint weight is at least `1/W` -/
  W : ℕ
  W_pos : 0 < W
  J_ge : ∀ a b, a ≠ b → 1 / (W : ℝ) ≤ J a b

attribute [instance] Alphabet.fα Alphabet.dα Alphabet.nα

namespace Alphabet

variable (A : Alphabet)

/-- Turn weight `w(t,u)`, zero on cancelling turns (OAI `WordEstimate.weight`). -/
noncomputable def weight (t u : A.α) : ℝ := if u = A.inv t then 0 else A.J (A.inv t) u

/-- Product of the turn weights from a starting letter through a tail. -/
noncomputable def continuation : (n : ℕ) → A.α → (Fin n → A.α) → ℝ
  | 0, _, _ => 1
  | n + 1, t, W => A.weight t (W 0) * continuation n (W 0) (Fin.tail W)

/-- `P(W)`, with empty products equal to one. -/
noncomputable def wordWeight : (h : ℕ) → (Fin h → A.α) → ℝ
  | 0, _ => 1
  | h + 1, W => A.continuation h (W 0) (Fin.tail W)

theorem weight_nonneg (t u : A.α) : 0 ≤ A.weight t u := by
  unfold weight
  split_ifs with h
  · exact le_rfl
  · have hne : A.inv t ≠ u := fun e => h e.symm
    exact le_trans (by have := A.W_pos; positivity) (A.J_ge _ _ hne)

theorem weight_le_one (t u : A.α) : A.weight t u ≤ 1 := by
  unfold weight
  split_ifs
  · norm_num
  · exact A.J_le_one _ _

theorem weight_pos {t u : A.α} (h : u ≠ A.inv t) : 0 < A.weight t u := by
  unfold weight
  simp only [h, ↓reduceIte]
  have hne : A.inv t ≠ u := fun e => h e.symm
  exact lt_of_lt_of_le (by have := A.W_pos; positivity) (A.J_ge _ _ hne)

theorem weight_pos_lower (t u : A.α) (h : 0 < A.weight t u) :
    1 / (A.W : ℝ) ≤ A.weight t u := by
  unfold weight at *
  split_ifs at * with hu
  · exact absurd h (lt_irrefl 0)
  · exact A.J_ge _ _ (fun e => hu e.symm)

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → A.α) → ℝ) :
    (∑ W, F W) = ∑ t, ∑ W, F (Fin.cons t W) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A.α)).sum_comp F]
  rw [Fintype.sum_prod_type]
  rfl

theorem continuation_eq_product (n : ℕ) (t : A.α) (W : Fin n → A.α) :
    A.continuation n t W =
      ∏ i : Fin n, A.weight ((Fin.cons t W : Fin (n + 1) → A.α) i.castSucc)
        ((Fin.cons t W : Fin (n + 1) → A.α) i.succ) := by
  induction n generalizing t with
  | zero => simp [continuation]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simp only [continuation, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ih]
    simp only [Fin.cons_self_tail, Fin.castSucc_succ, Fin.cons_succ, Fin.tail]

theorem wordWeight_eq_product (h : ℕ) (W : Fin (h + 1) → A.α) :
    A.wordWeight (h + 1) W = ∏ i : Fin h, A.weight (W i.castSucc) (W i.succ) := by
  rw [wordWeight, continuation_eq_product]
  simp only [Fin.cons_self_tail]

theorem continuation_nonneg (n : ℕ) (t : A.α) (W : Fin n → A.α) :
    0 ≤ A.continuation n t W := by
  rw [continuation_eq_product]
  exact Finset.prod_nonneg fun _ _ => A.weight_nonneg _ _

theorem wordWeight_nonneg (h : ℕ) (W : Fin h → A.α) : 0 ≤ A.wordWeight h W := by
  cases h with
  | zero => norm_num [wordWeight]
  | succ h => exact A.continuation_nonneg _ _ _

/-! ### Perron certificates -/

/-- A Perron certificate: a test vector `f ≥ 1` with `M f ≤ ρ f`, where `M_{tu} = w(t,u)^2`. -/
theorem continuation_mass (f : A.α → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hf : ∀ t, 1 ≤ f t)
    (hrow : ∀ t, (∑ u, A.weight t u ^ 2 * f u) ≤ ρ * f t) (n : ℕ) (t : A.α) :
    (∑ W : Fin n → A.α, A.continuation n t W ^ 2) ≤ ρ ^ n * f t := by
  induction n generalizing t with
  | zero => simpa [continuation] using hf t
  | succ n ih =>
    rw [A.sum_cons]
    simp only [continuation, Fin.cons_zero, Fin.tail_cons, mul_pow]
    simp_rw [← Finset.mul_sum]
    calc
      ∑ u, A.weight t u ^ 2 * ∑ W : Fin n → A.α, A.continuation n u W ^ 2
          ≤ ∑ u, A.weight t u ^ 2 * (ρ ^ n * f u) := by
            apply Finset.sum_le_sum
            intro u _
            exact mul_le_mul_of_nonneg_left (ih u) (sq_nonneg _)
      _ = ρ ^ n * ∑ u, A.weight t u ^ 2 * f u := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
      _ ≤ ρ ^ n * (ρ * f t) := by
            apply mul_le_mul_of_nonneg_left (hrow t)
            positivity
      _ = ρ ^ (n + 1) * f t := by ring

/-- The matrix form of the squared-word estimate (OAI `squared_word_geometric_bound`). -/
theorem squared_word_geometric_bound (f : A.α → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hf : ∀ t, 1 ≤ f t)
    (hrow : ∀ t, (∑ u, A.weight t u ^ 2 * f u) ≤ ρ * f t) (h : ℕ) :
    (∑ W : Fin (h + 1) → A.α, A.wordWeight (h + 1) W ^ 2) ≤ (∑ t, f t) * ρ ^ h := by
  rw [A.sum_cons]
  simp only [wordWeight, Fin.cons_zero, Fin.tail_cons]
  calc
    ∑ t, ∑ W : Fin h → A.α, A.continuation h t W ^ 2
        ≤ ∑ t, ρ ^ h * f t := Finset.sum_le_sum fun t _ ↦ A.continuation_mass f ρ hρ hf hrow h t
    _ = (∑ t, f t) * ρ ^ h := by rw [← Finset.mul_sum]; ring

/-- The squared-word decay estimate with `δ = 1/D`, valid for `h ≥ h₀`. -/
def Decays (D h₀ : ℕ) : Prop :=
  ∀ h, h₀ ≤ h → (∑ W : Fin h → A.α, A.wordWeight h W ^ 2) ≤ Real.exp (-2 * (1 / (D : ℝ)) * h)

/-- A Perron certificate with contraction `ρ = 1 - 3/D` and mass `∑ f ≤ exp E` gives decay
with `δ = 1/D` from `h₀ = E*D + 3` on. -/
theorem decays_of_perron (f : A.α → ℝ) (D E : ℕ) (hD : 3 ≤ D) (hf : ∀ t, 1 ≤ f t)
    (hrow : ∀ t, (∑ u, A.weight t u ^ 2 * f u) ≤ (1 - 3 / (D : ℝ)) * f t)
    (hmass : (∑ t, f t) ≤ Real.exp E) :
    A.Decays D (E * D + 3) := by
  intro h hh
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hρ : (0 : ℝ) ≤ 1 - 3 / (D : ℝ) := by
    rw [sub_nonneg, div_le_one hD0]; exact_mod_cast hD
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show h ≠ 0 by omega)
  have hb := A.squared_word_geometric_bound f _ hρ hf hrow k
  refine hb.trans ?_
  have hexp : (1 - 3 / (D : ℝ)) ≤ Real.exp (-(3 / (D : ℝ))) := by
    have := Real.add_one_le_exp (-(3 / (D : ℝ)))
    linarith
  have hpow : (1 - 3 / (D : ℝ)) ^ k ≤ Real.exp (-(3 / (D : ℝ))) ^ k :=
    pow_le_pow_left₀ hρ hexp k
  have hsum0 : 0 ≤ ∑ t, f t := Finset.sum_nonneg fun t _ => le_trans zero_le_one (hf t)
  calc
    (∑ t, f t) * (1 - 3 / (D : ℝ)) ^ k
        ≤ Real.exp E * Real.exp (-(3 / (D : ℝ))) ^ k :=
          mul_le_mul hmass hpow (by positivity) (by positivity)
    _ = Real.exp (E + k * (-(3 / (D : ℝ)))) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (-2 * (1 / (D : ℝ)) * ((k.succ : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hk : ((E * D + 3 : ℕ) : ℝ) ≤ (k.succ : ℝ) := by exact_mod_cast hh
          push_cast at hk ⊢
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hinv : (D : ℝ) * (D : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hD0.ne'
          have hEk : (E : ℝ) * D ≤ k - 2 := by linarith
          have hmul := mul_le_mul_of_nonneg_right hEk (inv_nonneg.mpr hD0.le)
          rw [mul_assoc, hinv, mul_one] at hmul
          nlinarith [inv_nonneg.mpr hD0.le]

/-! ### Weight bins (OAI `entropy-bins`), with symbolic constants -/

/-- Exact logarithmic bins, excluding zero weights. -/
noncomputable def binWords (h : ℕ) (d : ℤ) : Finset (Fin h → A.α) := by
  classical
  exact Finset.univ.filter fun W => 0 < A.wordWeight h W ∧ ⌊-Real.log (A.wordWeight h W)⌋ = d

theorem mem_binWords {h : ℕ} {d : ℤ} {W : Fin h → A.α} :
    W ∈ A.binWords h d ↔ 0 < A.wordWeight h W ∧ ⌊-Real.log (A.wordWeight h W)⌋ = d := by
  classical
  simp [binWords]

theorem bin_sq_lower {h : ℕ} {d : ℤ} {W : Fin h → A.α} (hW : W ∈ A.binWords h d) :
    Real.exp (-2 * (d : ℝ) - 2) ≤ A.wordWeight h W ^ 2 := by
  obtain ⟨hp, hd⟩ := A.mem_binWords.mp hW
  have hfloor := Int.lt_floor_add_one (-Real.log (A.wordWeight h W))
  rw [hd] at hfloor
  have hlog : -2 * (d : ℝ) - 2 ≤ 2 * Real.log (A.wordWeight h W) := by linarith
  have he := Real.exp_le_exp.mpr hlog
  have hpow : Real.exp (2 * Real.log (A.wordWeight h W)) = A.wordWeight h W ^ 2 := by
    rw [show (2 : ℝ) * Real.log (A.wordWeight h W) =
      (2 : ℕ) * Real.log (A.wordWeight h W) by norm_num, Real.exp_nat_mul, Real.exp_log hp]
  rwa [hpow] at he

variable {A}

theorem wordWeight_upper {D h₀ : ℕ} (hdec : A.Decays D h₀) (h : ℕ) (hh : h₀ ≤ h)
    (W : Fin h → A.α) : A.wordWeight h W ≤ Real.exp (-(1 / (D : ℝ)) * h) := by
  have hsingle : A.wordWeight h W ^ 2 ≤ ∑ V : Fin h → A.α, A.wordWeight h V ^ 2 :=
    Finset.single_le_sum (fun V _ => sq_nonneg (A.wordWeight h V)) (Finset.mem_univ W)
  have he := hsingle.trans (hdec h hh)
  have hexp : Real.exp (-2 * (1 / (D : ℝ)) * h) = Real.exp (-(1 / (D : ℝ)) * h) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at he
  nlinarith [Real.exp_pos (-(1 / (D : ℝ)) * h), A.wordWeight_nonneg h W]

/-- The finite bin-count bound (OAI `bin_card_bound`). -/
theorem bin_card_bound {D h₀ : ℕ} (hdec : A.Decays D h₀) (h : ℕ) (hh : h₀ ≤ h) (d : ℤ) :
    ((A.binWords h d).card : ℝ) ≤ Real.exp (2 * (d : ℝ) + 2 - 2 * (1 / (D : ℝ)) * h) := by
  have hlo : ((A.binWords h d).card : ℝ) * Real.exp (-2 * (d : ℝ) - 2) ≤
      ∑ W ∈ A.binWords h d, A.wordWeight h W ^ 2 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun W hW => A.bin_sq_lower hW)
  have hsum : (∑ W ∈ A.binWords h d, A.wordWeight h W ^ 2) ≤
      ∑ W : Fin h → A.α, A.wordWeight h W ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun W _ _ => sq_nonneg _)
  have he := hlo.trans (hsum.trans (hdec h hh))
  apply (le_div_iff₀ (Real.exp_pos _)).mpr at he
  apply he.trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Lower bin cutoff and counting bound at block scale `s` (OAI `bin_scale_bounds`;
there `2D = 1200`). -/
theorem bin_scale_bounds {D h₀ : ℕ} (hD : 0 < D) (hdec : A.Decays D h₀) (h : ℕ) (hh : h₀ ≤ h)
    (s : ℝ) (hscale : s + 2 * D ≤ 2 * h) (d : ℤ) (W : Fin h → A.α) (hW : W ∈ A.binWords h d) :
    (1 / (D : ℝ)) * s / 2 ≤ (d : ℝ) ∧
      ((A.binWords h d).card : ℝ) ≤ Real.exp (2 * d - (1 / (D : ℝ)) * s) := by
  obtain ⟨hp, hd⟩ := A.mem_binWords.mp hW
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hw := wordWeight_upper hdec h hh W
  have hlog : Real.log (A.wordWeight h W) ≤ -(1 / (D : ℝ)) * h := by
    have he := Real.log_le_log hp hw
    simpa only [Real.log_exp] using he
  have hfloor := Int.lt_floor_add_one (-Real.log (A.wordWeight h W))
  rw [hd] at hfloor
  have hsc : (1 / (D : ℝ)) * s + 2 ≤ 2 * (1 / (D : ℝ)) * h := by
    have := mul_le_mul_of_nonneg_left hscale (le_of_lt (one_div_pos.mpr hD0))
    have h2 : (1 / (D : ℝ)) * (2 * D) = 2 := by field_simp
    nlinarith
  constructor
  · nlinarith
  · apply (bin_card_bound hdec h hh d).trans
    apply Real.exp_le_exp.mpr
    linarith

theorem continuation_lower (n : ℕ) (t : A.α) (W : Fin n → A.α)
    (hp : 0 < A.continuation n t W) : (1 / (A.W : ℝ)) ^ n ≤ A.continuation n t W := by
  induction n generalizing t with
  | zero => simp [continuation]
  | succ n ih =>
    dsimp [continuation] at hp ⊢
    have ht : 0 < A.weight t (W 0) := (mul_pos_iff.mp hp).elim (fun h => h.1)
      (fun h => False.elim (not_lt_of_ge (A.weight_nonneg _ _) h.1))
    have hu : 0 < A.continuation n (W 0) (fun i => W i.succ) :=
      (mul_pos_iff.mp hp).elim (fun h => h.2)
        (fun h => False.elim (not_lt_of_ge (A.weight_nonneg _ _) h.1))
    rw [pow_succ]
    exact mul_le_mul (ih _ _ hu) (A.weight_pos_lower _ _ ht) (by have := A.W_pos; positivity)
      (A.continuation_nonneg _ _ _) |>.trans_eq (mul_comm _ _)

theorem wordWeight_lower (h : ℕ) (W : Fin h → A.α) (hp : 0 < A.wordWeight h W) :
    (1 / (A.W : ℝ)) ^ h ≤ A.wordWeight h W := by
  have hW1 : (1 : ℝ) ≤ A.W := by exact_mod_cast A.W_pos
  cases h with
  | zero => simp [wordWeight]
  | succ n =>
    have ht := continuation_lower n (W 0) (fun i => W i.succ) hp
    have hb : (1 / (A.W : ℝ)) ^ (n + 1) ≤ (1 / (A.W : ℝ)) ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) (by rw [div_le_one (by linarith)]; exact hW1)
    exact hb.trans ht

/-- Upper bin cutoff (OAI `bin_upper_bound`, there `a₀ = 256`): `d ≤ a₀ s` whenever
`2 log W ≤ a₀` and `h ≤ 2s`. -/
theorem bin_upper_bound (a₀ : ℝ) (ha : 2 * Real.log A.W ≤ a₀) (h : ℕ) (s : ℝ)
    (hscale : (h : ℝ) ≤ 2 * s) (d : ℤ) (W : Fin h → A.α) (hW : W ∈ A.binWords h d) :
    (d : ℝ) ≤ a₀ * s := by
  obtain ⟨hp, hd⟩ := A.mem_binWords.mp hW
  have hW0 : (0 : ℝ) < A.W := by exact_mod_cast A.W_pos
  have hW1 : (1 : ℝ) ≤ A.W := by exact_mod_cast A.W_pos
  have ht := wordWeight_lower h W hp
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (1 / (A.W : ℝ)) ^ h) ht
  rw [Real.log_pow, one_div, Real.log_inv] at hl
  have hb := Int.floor_le (-Real.log (A.wordWeight h W))
  rw [hd] at hb
  have hlogW : 0 ≤ Real.log A.W := Real.log_nonneg hW1
  have hs : 0 ≤ s := by
    have := Nat.cast_nonneg (α := ℝ) h
    linarith
  have hm := mul_le_mul_of_nonneg_left hscale hlogW
  nlinarith

/-- Both bin cutoffs and the squared-word count (OAI `bin_full_bounds`). -/
theorem bin_full_bounds {D h₀ : ℕ} (hD : 0 < D) (hdec : A.Decays D h₀) (a₀ : ℝ)
    (ha : 2 * Real.log A.W ≤ a₀) (h : ℕ) (hh : h₀ ≤ h) (s : ℝ)
    (hscale : s + 2 * D ≤ 2 * h) (hscale' : (h : ℝ) ≤ 2 * s)
    (d : ℤ) (W : Fin h → A.α) (hW : W ∈ A.binWords h d) :
    (1 / (D : ℝ)) * s / 2 ≤ d ∧ (d : ℝ) ≤ a₀ * s ∧
      ((A.binWords h d).card : ℝ) ≤ Real.exp (2 * d - (1 / (D : ℝ)) * s) := by
  obtain ⟨hl, hc⟩ := bin_scale_bounds hD hdec h hh s hscale d W hW
  exact ⟨hl, bin_upper_bound a₀ ha h s hscale' d W hW, hc⟩

end Alphabet

end Kaplansky.Random
