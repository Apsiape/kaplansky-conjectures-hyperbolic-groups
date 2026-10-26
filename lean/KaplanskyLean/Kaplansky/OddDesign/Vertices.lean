import Kaplansky.OddDesign.Turns

/-!
# The vertex sets `A₊`, `A₋`, `B` and their exact counts

For `m : ℕ` (the paper's `n = p^2 v^2 m`):

* `VB m := Σ τ, Fin (m k_τ)`, with outgoing set `S_y = τ`;
* `VAp m := Option (Σ τ, Fin (m k_τ - u_τ))`, with `none` the root `r` of type `S_r`;
* `VAm m := Σ τ, Fin (m k_τ + v_τ)`.

(The `A`-multiplicities are truncated at `0`; they are the stated integers for `m ≥ m0`.)

Main results:
* sizes `card_VB`, `card_VAp`, `card_VAm`;
* pools `pool_B`, `pool_Ap`, `pool_Am` and the balance `balance_card` (Proposition 7.6);
* turn counts `pair_B`, `pair_Ap`, `pair_Am` (Lemma 7.7) with errors bounded independently of `m`;
* congruences and degrees for all vertex types (Lemma 7.2).
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

/-! ### Counting in sigma types -/

theorem card_sigma_fin_filter {ι : Type*} [Fintype ι] (k : ι → ℕ) (P : ι → Prop)
    [DecidablePred P] :
    Fintype.card {x : Σ i, Fin (k i) // P x.1} = ∑ i, if P i then k i else 0 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [*]

theorem card_option_filter {X : Type*} [Fintype X] (Q : Option X → Prop) [DecidablePred Q] :
    Fintype.card {x : Option X // Q x} =
      (if Q none then 1 else 0) + Fintype.card {x : X // Q (some x)} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter,
    Fintype.sum_option]

variable {p : ℕ} [Fact p.Prime] [Fact (3 ≤ p)]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = q p)]

/-! ### The vertex sets -/

variable (p) in
/-- Number of `A₊`-vertices of type `τ`. -/
noncomputable def nAp (m : ℕ) (τ : Ty K p) : ℕ := (mAp p K m τ).toNat

variable (p) in
/-- Number of `A₋`-vertices of type `τ`. -/
noncomputable def nAm (m : ℕ) (τ : Ty K p) : ℕ := (mAm p K m τ).toNat

variable (p) in
/-- Number of `B`-vertices of type `τ`. -/
def nB (m : ℕ) (τ : Ty K p) : ℕ := m * kU p K τ

variable (p) in
/-- The colour class `A₊`; `none` is the root. -/
abbrev VAp (m : ℕ) := Option (Σ τ : Ty K p, Fin (nAp p K m τ))

variable (p) in
/-- The colour class `A₋`. -/
abbrev VAm (m : ℕ) := Σ τ : Ty K p, Fin (nAm p K m τ)

variable (p) in
/-- The side `B`. -/
abbrev VB (m : ℕ) := Σ τ : Ty K p, Fin (nB p K m τ)

variable (p) in
/-- Outgoing letters on `A₊`. -/
def outAp {m : ℕ} : VAp p K m → Finset (Letter K p)
  | none => rootSet K p
  | some x => typeSet K p x.1

variable (p) in
/-- Outgoing letters on `A₋`. -/
def outAm {m : ℕ} (x : VAm p K m) : Finset (Letter K p) := typeSet K p x.1

variable (p) in
/-- Outgoing letters on `B`. -/
def outB {m : ℕ} (y : VB p K m) : Finset (Letter K p) := typeSet K p y.1

theorem nAp_eq {m : ℕ} (hm : m0 p K ≤ m) (τ : Ty K p) : (nAp p K m τ : ℤ) = mAp p K m τ :=
  Int.toNat_of_nonneg (mAp_pos K hm τ).le

theorem nAm_eq {m : ℕ} (hm : m0 p K ≤ m) (τ : Ty K p) : (nAm p K m τ : ℤ) = mAm p K m τ :=
  Int.toNat_of_nonneg (mAm_pos K hm τ).le

theorem card_VB_filter (m : ℕ) (P : Finset (Letter K p) → Prop) [DecidablePred P] :
    Fintype.card {y : VB p K m // P (outB p K y)} =
      ∑ τ : Ty K p, if P (typeSet K p τ) then nB p K m τ else 0 :=
  card_sigma_fin_filter _ (fun τ => P (typeSet K p τ))

theorem card_VAm_filter (m : ℕ) (P : Finset (Letter K p) → Prop) [DecidablePred P] :
    Fintype.card {x : VAm p K m // P (outAm p K x)} =
      ∑ τ : Ty K p, if P (typeSet K p τ) then nAm p K m τ else 0 :=
  card_sigma_fin_filter _ (fun τ => P (typeSet K p τ))

theorem card_VAp_filter (m : ℕ) (P : Finset (Letter K p) → Prop) [DecidablePred P] :
    Fintype.card {x : VAp p K m // P (outAp p K x)} =
      (if P (rootSet K p) then 1 else 0) +
        ∑ τ : Ty K p, if P (typeSet K p τ) then nAp p K m τ else 0 := by
  rw [card_option_filter]
  congr 1
  exact card_sigma_fin_filter _ (fun τ => P (typeSet K p τ))

/-! ### Sizes -/

/-- `|B| = n = p^2 v^2 m`. -/
theorem card_VB (m : ℕ) : Fintype.card (VB p K m) = p ^ 2 * v p ^ 2 * m := by
  rw [Fintype.card_sigma]
  have : ∀ τ : Ty K p, Fintype.card (Fin (nB p K m τ)) = m * kU p K τ := fun τ => by
    exact Fintype.card_fin _
  rw [Finset.sum_congr rfl fun τ _ => this τ, ← Finset.mul_sum, sum_kU]
  ring

/-- `|A₊| = n + 1 - ∑ u_τ`. -/
theorem card_VAp {m : ℕ} (hm : m0 p K ≤ m) :
    (Fintype.card (VAp p K m) : ℤ) = p ^ 2 * v p ^ 2 * m + (1 - ∑ τ, uC p K τ) := by
  rw [Fintype.card_option, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  push_cast
  simp only [nAp_eq K hm, mAp, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have := sum_kU (p := p) K
  have h : (∑ τ : Ty K p, (kU p K τ : ℤ)) = (p ^ 2 * v p ^ 2 : ℕ) := by
    rw [← this]; push_cast; rfl
  rw [h]; push_cast; ring

/-- `|A₋| = n + ∑ v_τ`. -/
theorem card_VAm {m : ℕ} (hm : m0 p K ≤ m) :
    (Fintype.card (VAm p K m) : ℤ) = p ^ 2 * v p ^ 2 * m + ∑ τ, vC p K τ := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  push_cast
  simp only [nAm_eq K hm, mAm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have := sum_kU (p := p) K
  have h : (∑ τ : Ty K p, (kU p K τ : ℤ)) = (p ^ 2 * v p ^ 2 : ℕ) := by
    rw [← this]; push_cast; rfl
  rw [h]; push_cast; ring

/-! ### Pools and balance (Proposition 7.6) -/

theorem ind_eq_ite (S : Finset (Letter K p)) (t : Letter K p) :
    ind K p S t = if t ∈ S then 1 else 0 := rfl

theorem pool_B (m : ℕ) (t : Letter K p) :
    Fintype.card {y : VB p K m // t ∈ outB p K y} = poolN p m := by
  have h := muB_eq (p := p) K m t
  rw [card_VB_filter K m (fun S => t ∈ S)]
  unfold muB at h
  have : ((∑ τ : Ty K p, (if t ∈ typeSet K p τ then nB p K m τ else 0) : ℕ) : ℤ) =
      (poolN p m : ℤ) := by
    rw [← h]; push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [ind_eq_ite]; split_ifs <;> simp [nB]
  exact_mod_cast this

theorem pool_Ap {m : ℕ} (hm : m0 p K ≤ m) (t : Letter K p) :
    (Fintype.card {x : VAp p K m // t ∈ outAp p K x} : ℤ) = muAp p K m t := by
  rw [card_VAp_filter K m (fun S => t ∈ S)]
  unfold muAp
  have h1 : ((if t ∈ rootSet K p then 1 else 0 : ℕ) : ℤ) = rootVec p K t := by
    simp only [rootVec, ind]; split_ifs <;> simp
  have h2 : ((∑ τ : Ty K p, (if t ∈ typeSet K p τ then nAp p K m τ else 0) : ℕ) : ℤ) =
      ∑ τ, mAp p K m τ * ind K p (typeSet K p τ) t := by
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [ind_eq_ite]; split_ifs <;> simp [nAp_eq K hm]
  rw [Nat.cast_add, h1, h2]

theorem pool_Am {m : ℕ} (hm : m0 p K ≤ m) (t : Letter K p) :
    (Fintype.card {x : VAm p K m // t ∈ outAm p K x} : ℤ) = muAm p K m t := by
  rw [card_VAm_filter K m (fun S => t ∈ S)]
  unfold muAm
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [ind_eq_ite]; split_ifs <;> simp [nAm_eq K hm]

/-- **Proposition 7.6** for the vertex sets: `|A₊,t| = |A₋,t̄|`. -/
theorem balance_card {m : ℕ} (hm : m0 p K ≤ m) (t : Letter K p) :
    Fintype.card {x : VAp p K m // t ∈ outAp p K x} =
      Fintype.card {x : VAm p K m // barL p K t ∈ outAm p K x} := by
  have h1 := pool_Ap K hm t
  have h2 := pool_Am K hm (barL p K t)
  rw [balance K m t] at h1
  exact_mod_cast h1.trans h2.symm

theorem balance_B (m : ℕ) (t : Letter K p) :
    Fintype.card {y : VB p K m // t ∈ outB p K y} =
      Fintype.card {y : VB p K m // barL p K t ∈ outB p K y} := by
  rw [pool_B, pool_B]

/-! ### Turn counts (Lemma 7.7) -/

theorem pair_B (m : ℕ) (a b : Letter K p) :
    Fintype.card {y : VB p K m // a ∈ outB p K y ∧ b ∈ outB p K y} = m * pairU p K a b := by
  rw [card_VB_filter K m (fun S => a ∈ S ∧ b ∈ S), pairU, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  split_ifs <;> simp [nB]

variable (p) in
/-- The error of the `A₊` turn count. -/
noncomputable def errAp (a b : Letter K p) : ℤ :=
  (if a ∈ rootSet K p ∧ b ∈ rootSet K p then 1 else 0) -
    ∑ τ : Ty K p, if a ∈ typeSet K p τ ∧ b ∈ typeSet K p τ then uC p K τ else 0

variable (p) in
/-- The error of the `A₋` turn count. -/
noncomputable def errAm (a b : Letter K p) : ℤ :=
  ∑ τ : Ty K p, if a ∈ typeSet K p τ ∧ b ∈ typeSet K p τ then vC p K τ else 0

theorem pair_Ap {m : ℕ} (hm : m0 p K ≤ m) (a b : Letter K p) :
    (Fintype.card {x : VAp p K m // a ∈ outAp p K x ∧ b ∈ outAp p K x} : ℤ) =
      m * pairU p K a b + errAp p K a b := by
  rw [card_VAp_filter K m (fun S => a ∈ S ∧ b ∈ S)]
  have h2 : ((∑ τ : Ty K p,
      (if a ∈ typeSet K p τ ∧ b ∈ typeSet K p τ then nAp p K m τ else 0) : ℕ) : ℤ) =
      (m : ℤ) * (pairU p K a b : ℤ) -
        ∑ τ : Ty K p, (if a ∈ typeSet K p τ ∧ b ∈ typeSet K p τ then uC p K τ else 0) := by
    rw [pairU]; push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp [nAp_eq K hm, mAp]
  rw [Nat.cast_add, h2, errAp]
  push_cast
  ring

theorem pair_Am {m : ℕ} (hm : m0 p K ≤ m) (a b : Letter K p) :
    (Fintype.card {x : VAm p K m // a ∈ outAm p K x ∧ b ∈ outAm p K x} : ℤ) =
      m * pairU p K a b + errAm p K a b := by
  rw [card_VAm_filter K m (fun S => a ∈ S ∧ b ∈ S), errAm, pairU]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  split_ifs <;> simp [nAm_eq K hm, mAm]

variable (p) in
/-- The bound `1 + ∑ |u_τ| + ∑ |v_τ|` on the turn-count errors. -/
noncomputable def errBound : ℤ := 1 + ∑ τ : Ty K p, (|uC p K τ| + |vC p K τ|)

theorem abs_errAp_le (a b : Letter K p) : |errAp p K a b| ≤ errBound p K := by
  unfold errAp errBound
  have h1 : |∑ τ : Ty K p, (if a ∈ typeSet K p τ ∧ b ∈ typeSet K p τ then uC p K τ else 0)| ≤
      ∑ τ : Ty K p, (|uC p K τ| + |vC p K τ|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    split_ifs
    · have := abs_nonneg (vC p K τ); linarith
    · simp; positivity
  have h2 : |(if a ∈ rootSet K p ∧ b ∈ rootSet K p then (1 : ℤ) else 0)| ≤ 1 := by
    split_ifs <;> simp
  calc _ ≤ |(if a ∈ rootSet K p ∧ b ∈ rootSet K p then (1 : ℤ) else 0)| +
        |∑ τ : Ty K p, (if a ∈ typeSet K p τ ∧ b ∈ typeSet K p τ then uC p K τ else 0)| :=
        abs_sub _ _
    _ ≤ _ := by linarith

theorem abs_errAm_le (a b : Letter K p) : |errAm p K a b| ≤ errBound p K := by
  unfold errAm errBound
  have h1 : |∑ τ : Ty K p, (if a ∈ typeSet K p τ ∧ b ∈ typeSet K p τ then vC p K τ else 0)| ≤
      ∑ τ : Ty K p, (|uC p K τ| + |vC p K τ|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    split_ifs
    · have := abs_nonneg (uC p K τ); linarith
    · simp; positivity
  linarith

/-! ### Congruences and degrees of all vertex types (Lemma 7.2) -/

variable (p) in
/-- All letter sets that occur: the non-root types and the root type. -/
noncomputable def allTypes : Finset (Finset (Letter K p)) :=
  insert (rootSet K p) (univ.image (typeSet K p))

theorem outAp_mem {m : ℕ} (x : VAp p K m) : outAp p K x ∈ allTypes p K := by
  rcases x with _ | x
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_image_of_mem _ (mem_univ _))

theorem outAm_mem {m : ℕ} (x : VAm p K m) : outAm p K x ∈ allTypes p K :=
  mem_insert_of_mem (mem_image_of_mem _ (mem_univ _))

theorem outB_mem {m : ℕ} (y : VB p K m) : outB p K y ∈ allTypes p K :=
  mem_insert_of_mem (mem_image_of_mem _ (mem_univ _))

/-- **Lemma 7.2** for all types: `|S ∩ S'| ≡ 1 (mod p)` unless `S = S' = S_r`, and
`|S_r| ≡ 2 (mod p)`. -/
theorem cong_allTypes {S S' : Finset (Letter K p)} (hS : S ∈ allTypes p K)
    (hS' : S' ∈ allTypes p K) :
    (S ∩ S').card % p = if S = rootSet K p ∧ S' = rootSet K p then 2 % p else 1 := by
  simp only [allTypes, mem_insert, mem_image, mem_univ, true_and] at hS hS'
  rcases hS with rfl | ⟨τ, rfl⟩ <;> rcases hS' with rfl | ⟨τ', rfl⟩
  · simp [rootSet_card_mod]
  · rw [ite_eq_right (fun h => typeSet_ne_rootSet τ' h.2)]; exact cong_root_type τ'
  · rw [ite_eq_right (fun h => typeSet_ne_rootSet τ h.1)]; exact cong_type_root τ
  · rw [ite_eq_right (fun h => typeSet_ne_rootSet τ h.1)]; exact cong_types τ τ'

/-- Degrees: `q+1 ≤ |S| ≤ q+1+s`. -/
theorem card_allTypes {S : Finset (Letter K p)} (hS : S ∈ allTypes p K) :
    q p + 1 ≤ S.card ∧ S.card ≤ q p + 1 + s p := by
  simp only [allTypes, mem_insert, mem_image, mem_univ, true_and] at hS
  rcases hS with rfl | ⟨τ, rfl⟩
  · rw [card_rootSet]; omega
  · exact card_typeSet_bounds τ

theorem outAp_eq_root {m : ℕ} {x : VAp p K m} (h : outAp p K x = rootSet K p) : x = none := by
  rcases x with _ | x
  · rfl
  · exact absurd h (typeSet_ne_rootSet _)

theorem outAm_ne_root {m : ℕ} (x : VAm p K m) : outAm p K x ≠ rootSet K p :=
  typeSet_ne_rootSet _

theorem outB_ne_root {m : ℕ} (y : VB p K m) : outB p K y ≠ rootSet K p :=
  typeSet_ne_rootSet _

end Kaplansky.OddDesign
