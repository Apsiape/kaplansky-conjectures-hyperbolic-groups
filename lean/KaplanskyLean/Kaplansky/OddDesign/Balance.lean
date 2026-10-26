import Kaplansky.OddDesign.Involution

/-!
# Colour balance (Proposition 7.6)

With the involution `barL` of Lemma 7.5:

* `inLL_rootVec`: `1_{S_r} ∈ 𝓛 + 𝓛̄`;
* `expansion_spec`: fixed integer expansions `U = ∑ u_τ 1_τ`, `V = ∑ v_τ 1_τ` with
  `1_{S_r} = U + V̄` (`uC`, `vC`);
* the uniform family `kU` (`q+1` vertices of each type `ℓ ∪ D`, `p^2 v - s(q+1)` of type `ℓ`)
  carries every letter `p^2 v (q+1)` times (`comb_kU`);
* the multiplicities `m k_τ - u_τ` (on `A₊`, plus the root), `m k_τ + v_τ` (on `A₋`) and `m k_τ`
  (on `B`) are positive for `m ≥ m0` (`mAp_pos`, `mAm_pos`), and the letter counts satisfy the
  balance `μ₊(t) = μ₋(t̄)` (`balance`) and `μ_B(t) = μ_B(t̄) = p^2 v (q+1) m`.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

variable {p : ℕ} [Fact p.Prime] [Fact (3 ≤ p)]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = q p)]

/-! ### `1_{S_r} ∈ 𝓛 + 𝓛̄` -/

variable (p) in
/-- `1_{S_r}`. -/
def rootVec : Vec K p := ind K p (rootSet K p)

theorem rootVec_eq :
    rootVec p K = lineVec K p (lineR K) + allVec K p - ordVec K p := by
  ext t
  rcases t with x | e
  · simp [rootVec, ind, rootSet, lineVec, allVec, ordVec]
  · simp [rootVec, ind, rootSet, lineVec, allVec, ordVec]

theorem dvd_xi_barL (t : Letter K p) : (q p : ℤ) ∣ xi p K t + xi p K (barL p K t) - 1 := by
  have h := xi_barL K t
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ (q p)).mp (by rw [Int.cast_one]; exact h.symm)

variable (p) in
/-- `d` with `1_T = ξ + ξ̄ - q d`. -/
noncomputable def dVec : Vec K p := fun t => (xi p K t + xi p K (barL p K t) - 1) / q p

theorem allVec_eq : allVec K p = xi p K + barV K p (barL p K) (xi p K) - (q p : ℤ) • dVec p K := by
  ext t
  simp only [allVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, barV, dVec]
  rw [Int.mul_ediv_cancel' (dvd_xi_barL K t)]
  ring

theorem inLL_allVec : InLL K p (barL p K) (allVec K p) := by
  rw [allVec_eq]
  exact ((InLL.of_InL (inL_xi K)).add (InLL.of_bar (inL_xi K))).sub
    (lattice_c_q (barL p K) (barL_involutive K) .top _ (barL_inr K .top) _)

theorem inLL_ordVec : InLL K p (barL p K) (ordVec K p) :=
  lattice_c_ord (barL p K) (barL_involutive K) .top _ (barL_inr K .top)

/-- **Proposition 7.6**: `1_{S_r} ∈ 𝓛 + 𝓛̄`. -/
theorem inLL_rootVec : InLL K p (barL p K) (rootVec p K) := by
  rw [rootVec_eq]
  exact ((InLL.of_InL (InL.line _)).add (inLL_allVec K)).sub (inLL_ordVec K)

/-- **Proposition 7.6**: integer expansions `U, V ∈ 𝓛` with `1_{S_r} = U + V̄`. -/
theorem exists_expansion : ∃ u v : Ty K p → ℤ,
    rootVec p K = comb K p u + barV K p (barL p K) (comb K p v) := by
  obtain ⟨U, V, ⟨u, rfl⟩, ⟨v, rfl⟩, h⟩ := inLL_rootVec (p := p) K
  exact ⟨u, v, h⟩

variable (p) in
/-- The fixed coefficients `u_τ` of `U`. -/
noncomputable def uC : Ty K p → ℤ := (exists_expansion (p := p) K).choose

variable (p) in
/-- The fixed coefficients `v_τ` of `V`. -/
noncomputable def vC : Ty K p → ℤ := (exists_expansion (p := p) K).choose_spec.choose

theorem expansion_spec :
    rootVec p K = comb K p (uC p K) + barV K p (barL p K) (comb K p (vC p K)) :=
  (exists_expansion (p := p) K).choose_spec.choose_spec

/-! ### The uniform family -/

variable (p) in
/-- The multiplicities `k_τ` of the uniform family: `q+1` for `ℓ ∪ D`, `p^2 v - s(q+1)` for `ℓ`. -/
def kU (τ : Ty K p) : ℕ := if τ.2.isSome then q p + 1 else p ^ 2 * v p - s p * (q p + 1)

theorem s_mul_le : s p * (q p + 1) < p ^ 2 * v p := by
  have h3 := three_le (p := p)
  have e1 : s p * (q p + 1) = p ^ 7 + p ^ 6 + p ^ 5 + p ^ 2 + p + 1 := by simp only [s, q]; ring
  have e2 : p ^ 2 * v p = p ^ 12 + p ^ 7 + p ^ 2 := by simp only [v, q]; ring
  rw [e1, e2]
  have a1 : p ≤ p ^ 5 := Nat.le_self_pow (by norm_num) p
  have a2 : p ^ 5 ≤ p ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have a3 : 9 * p ^ 6 ≤ p ^ 8 := by
    have : 9 ≤ p ^ 2 := by nlinarith
    calc 9 * p ^ 6 ≤ p ^ 2 * p ^ 6 := Nat.mul_le_mul_right _ this
      _ = p ^ 8 := by ring
  have a4 : p ^ 8 ≤ p ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- `p^2 v - s(q+1) = p^2 q^2 - (p+1)(q+1)` (Proposition 7.6). -/
theorem uniform_none_eq : p ^ 2 * v p - s p * (q p + 1) = p ^ 2 * q p ^ 2 - (p + 1) * (q p + 1) := by
  have e1 : p ^ 2 * v p = p ^ 2 * q p ^ 2 + (p ^ 2 * q p + p ^ 2) := by simp only [v]; ring
  have e2 : s p * (q p + 1) = (p + 1) * (q p + 1) + (p ^ 2 * q p + p ^ 2) := by simp only [s]; ring
  rw [e1, e2]; omega

theorem kU_pos (τ : Ty K p) : 0 < kU p K τ := by
  unfold kU
  split_ifs
  · omega
  · have := s_mul_le (p := p); omega

theorem kU_none (ℓ : Ln K) : kU p K (ℓ, none) + s p * (q p + 1) = p ^ 2 * v p := by
  have := s_mul_le (p := p)
  simp only [kU, Option.isSome_none, Bool.false_eq_true, ite_false]
  omega

theorem kU_some (ℓ : Ln K) (ℓ₀ : Ln (ZMod p)) : kU p K (ℓ, some ℓ₀) = q p + 1 := by
  simp [kU]

/-- Each line class of the uniform family has `p^2 v` vertices. -/
theorem sum_kU_line (ℓ : Ln K) : ∑ o : Option (Ln (ZMod p)), kU p K (ℓ, o) = p ^ 2 * v p := by
  rw [Fintype.sum_option]
  simp only [kU_some, Finset.sum_const, Finset.card_univ, card_ln_zmod, smul_eq_mul]
  rw [mul_comm (s p)]
  have := kU_none (p := p) K ℓ
  rw [mul_comm (s p)] at this
  omega

theorem card_ln_K : Fintype.card (Ln K) = v p := by
  rw [card_ln, card_K K p]; rfl

theorem card_pt_K : Fintype.card (Pt K) = v p := by
  rw [card_pt, card_K K p]; rfl

/-- The uniform family has `p^2 v^2` vertices. -/
theorem sum_kU : ∑ τ : Ty K p, kU p K τ = p ^ 2 * v p ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_kU_line, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [card_ln_K (p := p) K]
  ring

/-- The uniform family carries every letter `p^2 v (q+1)` times. -/
theorem sum_kU_ind (t : Letter K p) :
    ∑ τ : Ty K p, (kU p K τ : ℤ) * ind K p (typeSet K p τ) t = (p ^ 2 * v p * (q p + 1) : ℕ) := by
  rw [Fintype.sum_prod_type]
  rcases t with x | e
  · simp only [ind_typeSet_inl, mul_ite, mul_one, mul_zero]
    have : ∀ ℓ : Ln K, ∑ o : Option (Ln (ZMod p)),
        (if Inc x (ℓ, o).1 then (kU p K (ℓ, o) : ℤ) else 0) =
        if Inc x ℓ then ((p ^ 2 * v p : ℕ) : ℤ) else 0 := by
      intro ℓ
      split_ifs with h
      · rw [← sum_kU_line K ℓ]; push_cast; rfl
      · simp
    rw [Finset.sum_congr rfl fun ℓ _ => this ℓ, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    have hc := card_lines (F := K) x
    rw [card_K K p] at hc
    simp only [lines] at hc
    rw [hc]; push_cast; ring
  · simp only [ind_typeSet_inr, mul_ite, mul_one, mul_zero]
    have : ∀ ℓ : Ln K, ∑ o : Option (Ln (ZMod p)),
        (if e ∈ extraPart p (ℓ, o).2 then (kU p K (ℓ, o) : ℤ) else 0) =
        ((p ^ 2 * (q p + 1) : ℕ) : ℤ) := by
      intro ℓ
      rw [Fintype.sum_option]
      simp only [extraPart, Finset.notMem_empty, ite_false, zero_add, kU_some]
      rw [← Finset.sum_filter, Finset.sum_const, card_blocks_containing, nsmul_eq_mul]
      push_cast; ring
    rw [Finset.sum_congr rfl fun ℓ _ => this ℓ, Finset.sum_const, Finset.card_univ, card_ln_K (p := p) K,
      nsmul_eq_mul]
    push_cast; ring

theorem comb_kU :
    comb K p (fun τ => (kU p K τ : ℤ)) = ((p ^ 2 * v p * (q p + 1) : ℕ) : ℤ) • allVec K p := by
  ext t
  simp only [comb, sum_kU_ind, Pi.smul_apply, allVec, smul_eq_mul, mul_one]

/-! ### The multiplicities and the balance -/

variable (p) in
/-- Multiplicity of a non-root type on `A₊`: `m k_τ - u_τ`. -/
noncomputable def mAp (m : ℕ) (τ : Ty K p) : ℤ := m * kU p K τ - uC p K τ

variable (p) in
/-- Multiplicity of a type on `A₋`: `m k_τ + v_τ`. -/
noncomputable def mAm (m : ℕ) (τ : Ty K p) : ℤ := m * kU p K τ + vC p K τ

variable (p) in
/-- The threshold `m₀` beyond which all multiplicities are positive. -/
noncomputable def m0 : ℕ := (∑ τ : Ty K p, (|uC p K τ| + |vC p K τ|)).toNat + 1

theorem abs_le_m0 (τ : Ty K p) : |uC p K τ| + |vC p K τ| < m0 p K := by
  have h1 : |uC p K τ| + |vC p K τ| ≤ ∑ τ' : Ty K p, (|uC p K τ'| + |vC p K τ'|) :=
    Finset.single_le_sum (f := fun τ' => |uC p K τ'| + |vC p K τ'|)
      (fun τ' _ => by positivity) (mem_univ τ)
  unfold m0
  push_cast
  have := Int.self_le_toNat (∑ τ' : Ty K p, (|uC p K τ'| + |vC p K τ'|))
  omega

theorem mAp_pos {m : ℕ} (hm : m0 p K ≤ m) (τ : Ty K p) : 0 < mAp p K m τ := by
  have h1 := abs_le_m0 K τ
  have h2 : (1 : ℤ) ≤ kU p K τ := by exact_mod_cast kU_pos K τ
  have h3 : (m0 p K : ℤ) ≤ m := by exact_mod_cast hm
  have h4 := le_abs_self (uC p K τ)
  have h5 := abs_nonneg (vC p K τ)
  unfold mAp
  nlinarith

theorem mAm_pos {m : ℕ} (hm : m0 p K ≤ m) (τ : Ty K p) : 0 < mAm p K m τ := by
  have h1 := abs_le_m0 K τ
  have h2 : (1 : ℤ) ≤ kU p K τ := by exact_mod_cast kU_pos K τ
  have h3 : (m0 p K : ℤ) ≤ m := by exact_mod_cast hm
  have h4 := neg_abs_le (vC p K τ)
  have h5 := abs_nonneg (uC p K τ)
  unfold mAm
  nlinarith

variable (p) in
/-- `μ₊(t)`: the number of `A₊`-vertices carrying `t` (root included). -/
noncomputable def muAp (m : ℕ) (t : Letter K p) : ℤ :=
  rootVec p K t + ∑ τ, mAp p K m τ * ind K p (typeSet K p τ) t

variable (p) in
/-- `μ₋(t)`: the number of `A₋`-vertices carrying `t`. -/
noncomputable def muAm (m : ℕ) (t : Letter K p) : ℤ :=
  ∑ τ, mAm p K m τ * ind K p (typeSet K p τ) t

variable (p) in
/-- `μ_B(t)`: the number of `B`-vertices carrying `t`. -/
noncomputable def muB (m : ℕ) (t : Letter K p) : ℤ :=
  ∑ τ, ((m * kU p K τ : ℕ) : ℤ) * ind K p (typeSet K p τ) t

/-- `n λ = p^2 v (q+1) m`, the common pool size. -/
def poolN (p m : ℕ) : ℕ := p ^ 2 * v p * (q p + 1) * m

theorem muAp_eq (m : ℕ) (t : Letter K p) :
    muAp p K m t = poolN p m - comb K p (uC p K) t + rootVec p K t := by
  unfold muAp mAp poolN
  have h := sum_kU_ind K t
  simp only [comb, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, h]
  push_cast; ring

theorem muAm_eq (m : ℕ) (t : Letter K p) :
    muAm p K m t = poolN p m + comb K p (vC p K) t := by
  unfold muAm mAm poolN
  have h := sum_kU_ind K t
  simp only [comb, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, h]
  push_cast; ring

theorem muB_eq (m : ℕ) (t : Letter K p) : muB p K m t = poolN p m := by
  unfold muB poolN
  have h := sum_kU_ind K t
  push_cast
  simp only [mul_assoc, ← Finset.mul_sum, h]
  push_cast; ring

/-- **Proposition 7.6**, the balance `eq:balance`: `μ₊(t) = μ₋(t̄)`. -/
theorem balance (m : ℕ) (t : Letter K p) : muAp p K m t = muAm p K m (barL p K t) := by
  rw [muAp_eq, muAm_eq]
  have h := congrFun (expansion_spec (p := p) K) t
  simp only [Pi.add_apply, barV] at h
  rw [h]; ring

end Kaplansky.OddDesign
