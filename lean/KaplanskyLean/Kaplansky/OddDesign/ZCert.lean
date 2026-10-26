import Kaplansky.OddDesign.Lattice
import Mathlib.Data.ZMod.ValMinAbs

/-!
# The certificate `z` (Lemma 7.4)

For an odd prime `p` put `u = (p-1)/2`, `h = (p+1)/2` and `κ = p u`. On the points of `PG(2,p)`,
```
z([i:j:1]) = ⟨i - h[j=0]⟩,   z([k:1:0]) = h,   z([1:0:0]) = κ,
```
where `⟨·⟩` is the centred representative (`ZMod.valMinAbs`).

* (a) `dvd_sum_line`: every line sum is divisible by `p`; `sum_z`: `∑_E z = p^2`;
* (b) `zVec_eq_sum`: `z = ∑_{ℓ₀} β(ℓ₀) 1_{E∖ℓ₀}` with `β(ℓ₀) = 1 - (∑_{e∈ℓ₀} z(e))/p`;
  `inL_zVec`: `z ∈ 𝓛`;
* (c) `card_z_eq_of_mem`, `card_z_eq_kappa`, `z_mem`: the values are `p` copies of each integer
  in `[-u, h]` and one `κ`; `zpair_*`: together with `1-κ` they split into pairs summing to `1`.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

variable (p : ℕ) [Fact p.Prime]

/-- `u = (p-1)/2`. -/
def uN : ℕ := p / 2

/-- `h = (p+1)/2`. -/
def hN : ℕ := p / 2 + 1

/-- `κ = p(p-1)/2`. -/
def kappa : ℤ := (p : ℤ) * (uN p : ℤ)

/-- `h` in `ZMod p`. -/
def hZ : ZMod p := (hN p : ZMod p)

/-- The indicator `[j = 0]` in `ZMod p`. -/
def jz (j : ZMod p) : ZMod p := if j = 0 then 1 else 0

/-- The shifted row coordinate `i - h[j=0]`. -/
def zrow (i j : ZMod p) : ZMod p := i - hZ p * jz p j

/-- The certificate `z` of Lemma 7.4. -/
def z : Pt (ZMod p) → ℤ
  | .aff i j => (zrow p i j).valMinAbs
  | .inf _ => (hN p : ℤ)
  | .top => kappa p

variable {p}
variable [hp3 : Fact (3 ≤ p)]

theorem three_le : 3 ≤ p := hp3.out

theorem p_odd : p % 2 = 1 := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
  · have := three_le (p := p); omega
  · exact h

theorem p_eq : p = 2 * uN p + 1 := by
  have := p_odd (p := p); unfold uN; omega

theorem hN_eq : hN p = uN p + 1 := rfl

theorem uN_pos : 1 ≤ uN p := by
  have := p_eq (p := p); have := three_le (p := p); omega

theorem two_hZ : 2 * hZ p = 1 := by
  have h1 : 2 * hN p = p + 1 := by have := p_eq (p := p); rw [hN_eq]; omega
  unfold hZ
  have : ((2 * hN p : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by rw [h1]
  rw [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_ofNat, Nat.cast_one]
    at this
  exact this

theorem one_sub_hZ : 1 - hZ p = hZ p := by
  have := two_hZ (p := p)
  linear_combination -this

theorem two_ne_zero_zmod : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  have := three_le (p := p)
  omega

theorem natCast_p_zmod : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p

/-! ### Centred representatives -/

theorem two_mul_val_ne (a : ZMod p) : 2 * a.val ≠ p := by
  have := p_odd (p := p); omega

theorem valMinAbs_bounds (a : ZMod p) :
    -(uN p : ℤ) ≤ a.valMinAbs ∧ a.valMinAbs ≤ (uN p : ℤ) := by
  have h := ZMod.valMinAbs_mem_Ioc a
  have hpe := p_eq (p := p)
  have hne : a.valMinAbs * 2 ≠ (p : ℤ) := by
    intro h'
    have : ((p : ℕ) : ℤ) % 2 = 1 := by exact_mod_cast p_odd (p := p)
    omega
  rw [Set.mem_Ioc] at h
  have hp' : (p : ℤ) = 2 * (uN p : ℤ) + 1 := by exact_mod_cast hpe
  constructor <;> omega

theorem valMinAbs_hZ : (hZ p).valMinAbs = -(uN p : ℤ) := by
  rw [ZMod.valMinAbs_spec]
  have hpe := p_eq (p := p)
  constructor
  · have h1 : hN p + uN p = p := by rw [hN_eq]; omega
    have h2 : ((hN p + uN p : ℕ) : ZMod p) = 0 := by rw [h1]; exact ZMod.natCast_self p
    push_cast at h2
    unfold hZ
    push_cast
    linear_combination h2
  · rw [Set.mem_Ioc]
    have hp' : (p : ℤ) = 2 * (uN p : ℤ) + 1 := by exact_mod_cast hpe
    constructor <;> omega

theorem valMinAbs_one_sub {b : ZMod p} (hb : b ≠ hZ p) :
    (1 - b).valMinAbs = 1 - b.valMinAbs := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨by simp [ZMod.coe_valMinAbs], ?_⟩
  have hbd := valMinAbs_bounds b
  have hpe := p_eq (p := p)
  have hp' : (p : ℤ) = 2 * (uN p : ℤ) + 1 := by exact_mod_cast hpe
  have hne : b.valMinAbs ≠ -(uN p : ℤ) := by
    intro h
    apply hb
    rw [← ZMod.valMinAbs_inj, h, valMinAbs_hZ]
  rw [Set.mem_Ioc]
  constructor <;> omega

/-- `∑_{i ∈ ZMod p} ⟨i - d⟩ = 0`. -/
theorem sum_valMinAbs_sub (d : ZMod p) : ∑ i : ZMod p, (i - d).valMinAbs = 0 := by
  have h1 : ∑ i : ZMod p, (i - d).valMinAbs = ∑ i : ZMod p, i.valMinAbs :=
    Fintype.sum_equiv (Equiv.subRight d) _ _ (fun _ => rfl)
  have h2 : ∑ i : ZMod p, i.valMinAbs = ∑ i : ZMod p, (-i).valMinAbs :=
    (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun _ => by simp))
  have h3 : ∑ i : ZMod p, (-i).valMinAbs = -∑ i : ZMod p, i.valMinAbs := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => ZMod.valMinAbs_neg_of_ne_half (two_mul_val_ne i)
  rw [h1]; linarith

/-- `∑_{j ∈ ZMod p} j = 0` for odd `p`. -/
theorem sum_zmod_id : ∑ j : ZMod p, j = 0 := by
  have h2 : ∑ j : ZMod p, j = ∑ j : ZMod p, -j :=
    Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun _ => by simp)
  rw [Finset.sum_neg_distrib] at h2
  have : (2 : ZMod p) * ∑ j : ZMod p, j = 0 := by linear_combination h2
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero_zmod

theorem sum_const_zmod (c : ZMod p) : ∑ _j : ZMod p, c = 0 := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, natCast_p_zmod, zero_mul]

/-! ### Lemma 7.4 (a) -/

/-- The sum of `z` over a line of `PG(2,p)`. -/
def lineSum (ℓ₀ : Ln (ZMod p)) : ℤ := ∑ e ∈ points ℓ₀, z p e

theorem kappa_eq : kappa p = (p : ℤ) * uN p := rfl

theorem lineSum_gen (a c : ZMod p) :
    lineSum (.gen a c) = ∑ j, (zrow p (a * j + c) j).valMinAbs + hN p := by
  rw [lineSum, sum_points_gen]; rfl

theorem lineSum_hor (c : ZMod p) : lineSum (.hor c) = kappa p := by
  rw [lineSum, sum_points_hor]
  simp only [z, zrow]
  rw [sum_valMinAbs_sub, zero_add]

theorem lineSum_infty : lineSum (.infty : Ln (ZMod p)) = (p : ℤ) * p := by
  rw [lineSum, sum_points_infty]
  simp only [z, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, kappa]
  have hpe := p_eq (p := p)
  have hp' : (p : ℤ) = 2 * (uN p : ℤ) + 1 := by exact_mod_cast hpe
  rw [hN_eq]; push_cast
  linear_combination (p : ℤ) * (-hp')

/-- **Lemma 7.4(a)**: every line sum of `z` is divisible by `p`. -/
theorem dvd_lineSum (ℓ₀ : Ln (ZMod p)) : (p : ℤ) ∣ lineSum ℓ₀ := by
  rcases ℓ₀ with ⟨a, c⟩ | c | _
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, lineSum_gen]
    push_cast
    simp only [zrow, jz]
    have : ∑ j : ZMod p, (a * j + c - hZ p * (if j = 0 then 1 else 0)) =
        a * ∑ j : ZMod p, j + ∑ _j : ZMod p, c - hZ p := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      simp
    rw [this, sum_zmod_id, sum_const_zmod]
    simp [hZ]
  · rw [lineSum_hor]; exact ⟨uN p, rfl⟩
  · rw [lineSum_infty]; exact ⟨p, rfl⟩

/-- **Lemma 7.4(a)**: `∑_{e ∈ E} z(e) = p^2`. -/
theorem sum_z : ∑ e, z p e = (p : ℤ) ^ 2 := by
  rw [sum_pt]
  simp only [z]
  have h1 : ∑ i : ZMod p, ∑ j : ZMod p, (zrow p i j).valMinAbs = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun j _ => by simp only [zrow]; exact sum_valMinAbs_sub _
  rw [h1, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, kappa, hN_eq]
  have hpe := p_eq (p := p)
  have hp' : (p : ℤ) = 2 * (uN p : ℤ) + 1 := by exact_mod_cast hpe
  push_cast
  linear_combination (p : ℤ) * (-hp')

/-! ### Lemma 7.4 (b) -/

/-- `β(ℓ₀) = 1 - (∑_{e ∈ ℓ₀} z(e))/p`, an integer by (a). -/
def beta (ℓ₀ : Ln (ZMod p)) : ℤ := 1 - lineSum ℓ₀ / p

theorem p_mul_beta (ℓ₀ : Ln (ZMod p)) : (p : ℤ) * beta ℓ₀ = p - lineSum ℓ₀ := by
  rw [beta, mul_sub, mul_one, Int.mul_ediv_cancel' (dvd_lineSum ℓ₀)]

theorem card_lines_not_mem_mem (e e' : Pt (ZMod p)) :
    (univ.filter (fun ℓ₀ : Ln (ZMod p) => ¬ Inc e ℓ₀ ∧ Inc e' ℓ₀)).card =
      if e' = e then 0 else p := by
  have hf : univ.filter (fun ℓ₀ : Ln (ZMod p) => ¬ Inc e ℓ₀ ∧ Inc e' ℓ₀) = lines e' \ lines e := by
    ext ℓ; simp [and_comm]
  rw [hf]
  split_ifs with h
  · subst h; simp
  · rw [card_lines_sdiff h, card_zmod]

/-- The pointwise identity behind Lemma 7.4(b): `∑_{ℓ₀ ∌ e} β(ℓ₀) = z(e)`. -/
theorem sum_beta (e : Pt (ZMod p)) :
    ∑ ℓ₀ : Ln (ZMod p), (if Inc e ℓ₀ then 0 else beta ℓ₀) = z p e := by
  have hp0 : (p : ℤ) ≠ 0 := by have := three_le (p := p); omega
  apply mul_left_cancel₀ hp0
  rw [Finset.mul_sum]
  have h1 : ∀ ℓ₀ : Ln (ZMod p), (p : ℤ) * (if Inc e ℓ₀ then 0 else beta ℓ₀) =
      (if Inc e ℓ₀ then 0 else (p : ℤ)) - (if Inc e ℓ₀ then 0 else lineSum ℓ₀) := by
    intro ℓ₀; split_ifs
    · simp
    · rw [p_mul_beta]
  rw [Finset.sum_congr rfl fun ℓ₀ _ => h1 ℓ₀, Finset.sum_sub_distrib]
  have h2 : ∑ ℓ₀ : Ln (ZMod p), (if Inc e ℓ₀ then (0 : ℤ) else p) = (p : ℤ) * p ^ 2 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    have := card_lines_compl e
    rw [card_zmod] at this
    rw [this]; push_cast; ring
  have h3 : ∑ ℓ₀ : Ln (ZMod p), (if Inc e ℓ₀ then (0 : ℤ) else lineSum ℓ₀) =
      (p : ℤ) * ((p : ℤ) ^ 2 - z p e) := by
    have : ∀ ℓ₀ : Ln (ZMod p), (if Inc e ℓ₀ then (0 : ℤ) else lineSum ℓ₀) =
        ∑ e', (if ¬ Inc e ℓ₀ ∧ Inc e' ℓ₀ then z p e' else 0) := by
      intro ℓ₀
      rw [lineSum, points, Finset.sum_filter]
      split_ifs with h <;> simp [h]
    rw [Finset.sum_congr rfl fun ℓ₀ _ => this ℓ₀, Finset.sum_comm]
    have : ∀ e' : Pt (ZMod p), ∑ ℓ₀ : Ln (ZMod p),
        (if ¬ Inc e ℓ₀ ∧ Inc e' ℓ₀ then z p e' else 0) =
        z p e' * (if e' = e then 0 else (p : ℤ)) := by
      intro e'
      rw [← Finset.sum_filter, Finset.sum_const, card_lines_not_mem_mem, nsmul_eq_mul]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl fun e' _ => this e']
    have : ∑ e' : Pt (ZMod p), z p e' * (if e' = e then 0 else (p : ℤ)) =
        (p : ℤ) * (∑ e', z p e' - z p e) := by
      have hpt : ∀ e', z p e' * (if e' = e then 0 else (p : ℤ)) =
          (p : ℤ) * z p e' - (if e' = e then (p : ℤ) * z p e else 0) := by
        intro e'; split_ifs with h
        · subst h; ring
        · ring
      rw [Finset.sum_congr rfl fun e' _ => hpt e', Finset.sum_sub_distrib, Finset.sum_ite_eq',
        ite_eq_left (mem_univ e), ← Finset.mul_sum]
      ring
    rw [this, sum_z]
  rw [h2, h3]; ring

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- `z` as a vector on the alphabet (zero on ordinary letters). -/
def zVec : Vec K p := Sum.elim 0 (z p)

/-- **Lemma 7.4(b)**: `z = ∑_{ℓ₀} β(ℓ₀) 1_{E ∖ ℓ₀}`. -/
theorem zVec_eq_sum : zVec K = ∑ ℓ₀, beta ℓ₀ • blockVec K p ℓ₀ := by
  ext t
  rcases t with x | e
  · simp [zVec, blockVec]
  · simp only [zVec, Sum.elim_inr, Finset.sum_apply, Pi.smul_apply, blockVec, smul_eq_mul,
      mul_ite, mul_zero, mul_one]
    exact (sum_beta e).symm

/-- `z ∈ 𝓛`. -/
theorem inL_zVec : InL K p (zVec K) := by
  rw [zVec_eq_sum]
  exact InL.sum _ _ fun ℓ₀ _ => (InL.block ℓ₀).smul _

/-! ### Lemma 7.4 (c) -/

theorem uN_lt_hN : (uN p : ℤ) < hN p := by rw [hN_eq]; push_cast; omega

theorem hN_lt_kappa : (hN p : ℤ) < kappa p := by
  rw [hN_eq, kappa]
  have h3' := three_le (p := p)
  have h3 : (3 : ℤ) ≤ p := by exact_mod_cast h3'
  have h1 : (1 : ℤ) ≤ uN p := by exact_mod_cast uN_pos (p := p)
  push_cast; nlinarith

theorem z_aff_bounds (i j : ZMod p) :
    -(uN p : ℤ) ≤ z p (.aff i j) ∧ z p (.aff i j) ≤ uN p := valMinAbs_bounds _

/-- The values of `z` lie in `[-u, h] ∪ {κ}`. -/
theorem z_mem (e : Pt (ZMod p)) :
    (-(uN p : ℤ) ≤ z p e ∧ z p e ≤ hN p) ∨ z p e = kappa p := by
  rcases e with ⟨i, j⟩ | k | _
  · have := z_aff_bounds (p := p) i j
    have := uN_lt_hN (p := p)
    left; constructor <;> omega
  · left; simp only [z]; have := uN_lt_hN (p := p); constructor <;> omega
  · right; rfl

/-- `|z| ≤ κ`. -/
theorem abs_z_le (e : Pt (ZMod p)) : |z p e| ≤ kappa p := by
  have h1 := uN_lt_hN (p := p)
  have h2 := hN_lt_kappa (p := p)
  rcases z_mem e with ⟨a, b⟩ | h
  · rw [abs_le]; constructor <;> omega
  · rw [h, abs_of_pos (by omega)]

theorem card_z_aff (y : ℤ) (hy1 : -(uN p : ℤ) ≤ y) (hy2 : y ≤ uN p) (j : ZMod p) :
    (univ.filter (fun i : ZMod p => z p (.aff i j) = y)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨(y : ZMod p) + hZ p * jz p j, ?_⟩
  ext i
  rw [mem_filter, mem_singleton]
  simp only [mem_univ, true_and]
  change (zrow p i j).valMinAbs = y ↔ _
  rw [ZMod.valMinAbs_spec]
  have hpe := p_eq (p := p)
  have hp' : (p : ℤ) = 2 * (uN p : ℤ) + 1 := by exact_mod_cast hpe
  have hr : y * 2 ∈ Set.Ioc (-(p : ℤ)) p := by rw [Set.mem_Ioc]; constructor <;> omega
  simp only [hr, and_true]
  unfold zrow
  constructor
  · intro h; rw [← h]; ring
  · intro h; rw [h]; ring

@[simp] theorem z_inf (k : ZMod p) : z p (.inf k) = hN p := rfl
@[simp] theorem z_top : z p .top = kappa p := rfl

theorem hN_cast : (hN p : ℤ) = uN p + 1 := by rw [hN_eq]; push_cast; ring

/-- **Lemma 7.4(c)**: each value `y ∈ [-u, h]` is taken exactly `p` times. -/
theorem card_z_eq_of_mem (y : ℤ) (hy1 : -(uN p : ℤ) ≤ y) (hy2 : y ≤ hN p) :
    (univ.filter (fun e => z p e = y)).card = p := by
  rw [Finset.card_filter, sum_pt]
  have hk := hN_lt_kappa (p := p)
  have hhu := hN_cast (p := p)
  by_cases hyu : y ≤ uN p
  · have hu := uN_lt_hN (p := p)
    have : ∀ j : ZMod p, ∑ i : ZMod p, (if z p (.aff i j) = y then 1 else 0) = 1 := by
      intro j
      rw [← Finset.card_filter]; exact card_z_aff y hy1 hyu j
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => this j]
    have e1 : ¬ ((hN p : ℤ) = y) := by omega
    have e2 : ¬ (kappa p = y) := by omega
    simp only [z_inf, z_top, e1, e2, ite_false, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]
  · have hyh : y = hN p := by omega
    subst hyh
    have : ∀ i j : ZMod p, (if z p (.aff i j) = (hN p : ℤ) then 1 else 0) = 0 := by
      intro i j
      have := z_aff_bounds (p := p) i j
      have := uN_lt_hN (p := p)
      exact ite_eq_right_iff.mpr (fun h => by omega)
    have e2 : ¬ (kappa p = (hN p : ℤ)) := by omega
    simp only [this, Finset.sum_const_zero, zero_add, z_inf, z_top, ite_true, e2, ite_false,
      add_zero, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]

/-- **Lemma 7.4(c)**: the value `κ` is taken exactly once. -/
theorem card_z_eq_kappa : (univ.filter (fun e => z p e = kappa p)).card = 1 := by
  rw [Finset.card_filter, sum_pt]
  have hk := hN_lt_kappa (p := p)
  have hu := uN_lt_hN (p := p)
  have : ∀ i j : ZMod p, (if z p (.aff i j) = kappa p then 1 else 0) = 0 := by
    intro i j
    have := z_aff_bounds (p := p) i j
    exact ite_eq_right_iff.mpr (fun h => by omega)
  have e2 : ¬ ((hN p : ℤ) = kappa p) := by omega
  simp only [this, Finset.sum_const_zero, zero_add, z_inf, z_top, ite_true, e2, ite_false]

/-- The values of `z` together with the further value `1 - κ`. -/
def zz : Option (Pt (ZMod p)) → ℤ
  | none => 1 - kappa p
  | some e => z p e

/-- The pairing of Lemma 7.4(c), `y ↔ 1 - y`. -/
def zpair : Option (Pt (ZMod p)) → Option (Pt (ZMod p))
  | none => some .top
  | some .top => none
  | some (.inf k) => some (.aff (hZ p + hZ p * jz p k) k)
  | some (.aff i j) =>
      if zrow p i j = hZ p then some (.inf j)
      else some (.aff (1 - zrow p i j + hZ p * jz p j) j)

theorem zrow_shift (b j : ZMod p) : zrow p (b + hZ p * jz p j) j = b := by
  simp [zrow]

theorem zrow_eq (i j : ZMod p) : i = zrow p i j + hZ p * jz p j := by
  simp [zrow]

theorem zpair_aff_of_eq {i j : ZMod p} (h : zrow p i j = hZ p) :
    zpair (some (.aff i j)) = some (.inf j) := by
  simp only [zpair, h, ite_true]

theorem zpair_aff_of_ne {i j : ZMod p} (h : zrow p i j ≠ hZ p) :
    zpair (some (.aff i j)) = some (.aff (1 - zrow p i j + hZ p * jz p j) j) := by
  simp only [zpair, h, ite_false]

theorem zpair_inf (k : ZMod p) : zpair (some (.inf k)) = some (.aff (hZ p + hZ p * jz p k) k) :=
  rfl

theorem one_sub_ne_hZ {b : ZMod p} (h : b ≠ hZ p) : 1 - b ≠ hZ p := by
  intro h'; apply h
  have := one_sub_hZ (p := p)
  linear_combination -h' + this

theorem zpair_involutive : Function.Involutive (zpair (p := p)) := by
  intro x
  rcases x with _ | ⟨i, j⟩ | k | _
  · rfl
  · by_cases h : zrow p i j = hZ p
    · have e := zrow_eq (p := p) i j
      rw [h] at e
      rw [zpair_aff_of_eq h, zpair_inf, ← e]
    · rw [zpair_aff_of_ne h, zpair_aff_of_ne (by rw [zrow_shift]; exact one_sub_ne_hZ h),
        zrow_shift]
      congr 2
      rw [sub_sub_cancel, ← zrow_eq]
  · rw [zpair_inf, zpair_aff_of_eq (zrow_shift _ _)]
  · rfl

theorem zpair_ne (x : Option (Pt (ZMod p))) : zpair x ≠ x := by
  rcases x with _ | ⟨i, j⟩ | k | _
  · simp [zpair]
  · by_cases h : zrow p i j = hZ p
    · rw [zpair_aff_of_eq h]; simp
    · rw [zpair_aff_of_ne h]
      intro he
      simp only [Option.some.injEq, Pt.aff.injEq, and_true] at he
      apply h
      have h2 : 2 * zrow p i j = 1 := by
        have e := zrow_eq (p := p) i j
        linear_combination -e - he
      have h3 : 2 * (zrow p i j - hZ p) = 0 := by
        have := two_hZ (p := p)
        linear_combination h2 - this
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left two_ne_zero_zmod)
  · simp [zpair]
  · simp [zpair]

/-- **Lemma 7.4(c)**: paired values sum to `1`. -/
theorem zz_zpair (x : Option (Pt (ZMod p))) : zz (zpair x) + zz x = 1 := by
  rcases x with _ | ⟨i, j⟩ | k | _
  · simp [zz, zpair, z]
  · by_cases h : zrow p i j = hZ p
    · rw [zpair_aff_of_eq h]
      simp only [zz, z]
      rw [h, valMinAbs_hZ, hN_eq]; push_cast; ring
    · rw [zpair_aff_of_ne h]
      simp only [zz, z]
      rw [zrow_shift, valMinAbs_one_sub h]; ring
  · rw [zpair_inf]
    simp only [zz, z]
    rw [zrow_shift, valMinAbs_hZ, hN_eq]; push_cast; ring
  · simp [zz, zpair, z]

end Kaplansky.OddDesign
