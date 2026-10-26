import Kaplansky.OddDesign.Balance
import Kaplansky.OddDesign.Perron

/-!
# Turn counts (Lemma 7.7)

`pairU a b` is the number of vertices of the uniform family carrying both letters `a ≠ b`:

* two ordinary letters: `p^2 v` (their common line class);
* an ordinary and an extra letter: `p^2 (q+1)^2`;
* two extra letters: `v (p^2-p) (q+1)`.

In every case `m · pairU a b = n λ w` with `n = p^2 v^2 m` and `w = baseW` the joint weight of
`eq:oddw` (`pairU_real`). The exact counts on `A₊`, `A₋`, `B` (with the corrections of
Proposition 7.6, bounded independently of `m`) are in `Kaplansky/OddDesign/Data.lean`.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

variable {p : ℕ} [Fact p.Prime] [Fact (3 ≤ p)]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = q p)]

@[simp] theorem inl_mem_typeSet (x : Pt K) (τ : Ty K p) :
    (Sum.inl x : Letter K p) ∈ typeSet K p τ ↔ Inc x τ.1 := by
  simp [typeSet]

@[simp] theorem inr_mem_typeSet (e : Pt (ZMod p)) (τ : Ty K p) :
    (Sum.inr e : Letter K p) ∈ typeSet K p τ ↔ e ∈ extraPart p τ.2 := by
  simp [typeSet]

@[simp] theorem inl_mem_rootSet (x : Pt K) :
    (Sum.inl x : Letter K p) ∈ rootSet K p ↔ Inc x (lineR K) := by
  simp [rootSet]

@[simp] theorem inr_mem_rootSet (e : Pt (ZMod p)) : (Sum.inr e : Letter K p) ∈ rootSet K p := by
  simp [rootSet]

variable (p) in
/-- The number of vertices of the uniform family carrying both `a` and `b`. -/
def pairU (a b : Letter K p) : ℕ :=
  ∑ τ : Ty K p, if a ∈ typeSet K p τ ∧ b ∈ typeSet K p τ then kU p K τ else 0

theorem pairU_oo {x y : Pt K} (h : x ≠ y) :
    pairU p K (Sum.inl x) (Sum.inl y) = p ^ 2 * v p := by
  unfold pairU
  rw [Fintype.sum_prod_type]
  simp only [inl_mem_typeSet]
  have : ∀ ℓ : Ln K, ∑ o : Option (Ln (ZMod p)), (if Inc x ℓ ∧ Inc y ℓ then kU p K (ℓ, o) else 0) =
      if Inc x ℓ ∧ Inc y ℓ then p ^ 2 * v p else 0 := by
    intro ℓ
    split_ifs
    · exact sum_kU_line K ℓ
    · simp
  rw [Finset.sum_congr rfl fun ℓ _ => this ℓ, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul]
  have hf : univ.filter (fun ℓ : Ln K => Inc x ℓ ∧ Inc y ℓ) = lines x ∩ lines y := by
    ext ℓ; simp
  rw [hf, card_lines_inter h, one_mul]

theorem pairU_oe (x : Pt K) (e : Pt (ZMod p)) :
    pairU p K (Sum.inl x) (Sum.inr e) = p ^ 2 * (q p + 1) ^ 2 := by
  unfold pairU
  rw [Fintype.sum_prod_type]
  simp only [inl_mem_typeSet, inr_mem_typeSet]
  have : ∀ ℓ : Ln K, ∑ o : Option (Ln (ZMod p)),
      (if Inc x ℓ ∧ e ∈ extraPart p o then kU p K (ℓ, o) else 0) =
      if Inc x ℓ then p ^ 2 * (q p + 1) else 0 := by
    intro ℓ
    rw [Fintype.sum_option]
    simp only [extraPart, Finset.notMem_empty, and_false, ite_false, zero_add, kU_some]
    split_ifs with hx
    · simp only [hx, true_and]
      rw [← Finset.sum_filter, Finset.sum_const, card_blocks_containing, smul_eq_mul]
    · simp [hx]
  rw [Finset.sum_congr rfl fun ℓ _ => this ℓ, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul]
  have hc := card_lines (F := K) x
  rw [card_K K p] at hc
  simp only [lines] at hc
  rw [hc]; ring

theorem pairU_comm (a b : Letter K p) : pairU p K a b = pairU p K b a := by
  unfold pairU
  exact Finset.sum_congr rfl fun τ _ => by simp only [and_comm]

theorem pairU_ee {e e' : Pt (ZMod p)} (h : e ≠ e') :
    pairU p K (Sum.inr e) (Sum.inr e') = v p * (p * (p - 1)) * (q p + 1) := by
  unfold pairU
  rw [Fintype.sum_prod_type]
  simp only [inr_mem_typeSet]
  have : ∀ ℓ : Ln K, ∑ o : Option (Ln (ZMod p)),
      (if e ∈ extraPart p o ∧ e' ∈ extraPart p o then kU p K (ℓ, o) else 0) =
      p * (p - 1) * (q p + 1) := by
    intro ℓ
    rw [Fintype.sum_option]
    simp only [extraPart, Finset.notMem_empty, false_and, ite_false, zero_add, kU_some]
    rw [← Finset.sum_filter, Finset.sum_const, card_blocks_containing_two h, smul_eq_mul]
  rw [Finset.sum_congr rfl fun ℓ _ => this ℓ, Finset.sum_const, Finset.card_univ,
    card_ln_K (p := p) K, smul_eq_mul]
  ring

/-- **Lemma 7.7** for the uniform family: `pairU a b · m = n λ w(a,b)` with `n = p^2 v^2 m`;
here `a = t̄`, `b = u`. -/
theorem pairU_real {a b : Letter K p} (hab : a ≠ b) :
    (pairU p K a b : ℝ) = ((p : ℝ) ^ 2 * (v p : ℝ) ^ 2) * lam p * baseW p (IsExtra K p) a b := by
  have hv : (v p : ℝ) ≠ 0 := (v_real_pos p).ne'
  have hq : (q p : ℝ) + 1 ≠ 0 := by positivity
  have hp0 : (p : ℝ) ≠ 0 := by have := three_le (p := p); positivity
  rcases a with x | e <;> rcases b with y | e'
  · rw [pairU_oo K (fun h' => hab (congrArg Sum.inl h'))]
    simp only [baseW, isExtra_inl, ite_false, lam]
    push_cast
    field_simp
  · rw [pairU_oe]
    simp only [baseW, isExtra_inl, isExtra_inr, ite_true, ite_false, lam]
    push_cast
    field_simp
  · rw [pairU_comm, pairU_oe]
    simp only [baseW, isExtra_inl, isExtra_inr, ite_true, ite_false, lam]
    push_cast
    field_simp
  · rw [pairU_ee K (fun h' => hab (congrArg Sum.inr h'))]
    simp only [baseW, isExtra_inr, ite_true, gam, lam]
    have h1 : 1 ≤ p := by have := three_le (p := p); omega
    push_cast [Nat.cast_sub h1]
    field_simp

end Kaplansky.OddDesign
