import Kaplansky.OddDesign.ZCert
import Kaplansky.OddDesign.Pairing
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The involution (Lemma 7.5)

Put `h_q = (q+1)/2` and fix a bijection `θ : K → ZMod q` (with integer values
`θ(k) ∈ {0,…,q-1}`). Let `ξ_O` be the combination of line indicators with coefficient `θ(k)` on
`X = kZ`, `1-κ-h_q` on `Y = 0` and `h_q` on `Z = 0`, and `ξ = ξ_O + z ∈ 𝓛` (`xi`, `inL_xi`).

**Lemma 7.5** (`exists_bar`): there is a fixed-point-free involution `t ↦ t̄` of `T` with
`Ē ⊆ O` such that `ξ(t) + ξ(t̄) ≡ 1 (mod q)` for every `t` (`eq:residue`).

Proof as in the paper: each extra letter `e` is paired with an affine point `[i : ι(e) : 1]` of
residue `1 - z(e)` in its own row `ι(e) ≠ 0`; the remaining ordinary letters have a residue
multiset invariant under `y ↦ 1 - y`, with the fixed residue `h_q` occurring `2q` times, and are
paired by the general pairing lemma (`exists_pairing`).
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

variable {p : ℕ} [Fact p.Prime]

instance qNeZero : NeZero (q p) := ⟨(q_pos (Fact.out : p.Prime).pos).ne'⟩

/-! ### Arithmetic in `ZMod n` for odd `n` -/

theorem isUnit_two_of_odd {n : ℕ} (hn : n % 2 = 1) : IsUnit (2 : ZMod n) := by
  have : IsUnit ((2 : ℕ) : ZMod n) := by
    rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  exact_mod_cast this

theorem eq_of_two_mul_eq {n : ℕ} (hn : n % 2 = 1) {a b : ZMod n} (h : 2 * a = 2 * b) : a = b :=
  (isUnit_two_of_odd hn).mul_left_cancel h

theorem sum_zmod_id_of_odd {n : ℕ} [NeZero n] (hn : n % 2 = 1) : ∑ x : ZMod n, x = 0 := by
  have h2 : ∑ x : ZMod n, x = ∑ x : ZMod n, -x :=
    Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun _ => by simp)
  rw [Finset.sum_neg_distrib] at h2
  apply eq_of_two_mul_eq hn
  linear_combination h2

variable [Fact (3 ≤ p)]

theorem q_odd : q p % 2 = 1 := by
  unfold q
  rw [Nat.pow_mod, p_odd (p := p)]

/-- `h_q = (q+1)/2`. -/
def hqN (p : ℕ) : ℕ := q p / 2 + 1

theorem two_hqN : 2 * hqN p = q p + 1 := by
  have := q_odd (p := p); unfold hqN; omega

/-- `h_q` in `ZMod q`. -/
def hqZ (p : ℕ) : ZMod (q p) := (hqN p : ZMod (q p))

theorem two_hqZ : 2 * hqZ p = 1 := by
  unfold hqZ
  have : ((2 * hqN p : ℕ) : ZMod (q p)) = ((q p + 1 : ℕ) : ZMod (q p)) := by rw [two_hqN]
  push_cast at this
  rw [this, ZMod.natCast_self, zero_add]

theorem one_sub_eq_self_iff (y : ZMod (q p)) : 1 - y = y ↔ y = hqZ p := by
  constructor
  · intro h
    apply eq_of_two_mul_eq (q_odd (p := p))
    rw [two_hqZ]; linear_combination -h
  · rintro rfl
    have := two_hqZ (p := p)
    linear_combination -this

/-- An integer `y` with `|2y - 1| < q` is not `≡ h_q (mod q)`. -/
theorem intCast_ne_hqZ (y : ℤ) (hy : |2 * y - 1| < (q p : ℤ)) : ((y : ℤ) : ZMod (q p)) ≠ hqZ p := by
  intro h
  have h2 : ((2 * y - 1 : ℤ) : ZMod (q p)) = 0 := by
    push_cast; rw [h, two_hqZ]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  obtain ⟨c, hc⟩ := h2
  rw [abs_lt] at hy
  have hq : (0 : ℤ) < q p := by exact_mod_cast (q_pos (Fact.out : p.Prime).pos)
  have hc0 : c = 0 := by
    rcases lt_trichotomy c 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst hc0
  omega

theorem two_kappa_lt_q : 2 * kappa p + 1 < (q p : ℤ) := by
  rw [kappa, q]
  have hpe := p_eq (p := p)
  have h3 : (3 : ℤ) ≤ p := by exact_mod_cast three_le (p := p)
  have hp' : (p : ℤ) = 2 * (uN p : ℤ) + 1 := by exact_mod_cast hpe
  have hu : (2 : ℤ) * uN p = p - 1 := by linarith
  push_cast
  have : (2 : ℤ) * (↑p * ↑(uN p)) = p * (p - 1) := by rw [← hu]; ring
  rw [this]
  nlinarith [pow_pos (by linarith : (0 : ℤ) < p) 3]

theorem z_ne_hqZ (e : Pt (ZMod p)) : ((z p e : ℤ) : ZMod (q p)) ≠ hqZ p := by
  apply intCast_ne_hqZ
  have h1 := abs_z_le e
  have h2 := two_kappa_lt_q (p := p)
  rw [abs_le] at h1
  rw [abs_lt]; constructor <;> linarith

theorem one_sub_kappa_ne_hqZ : ((1 - kappa p : ℤ) : ZMod (q p)) ≠ hqZ p := by
  apply intCast_ne_hqZ
  have h2 := two_kappa_lt_q (p := p)
  have h3 := hN_lt_kappa (p := p)
  rw [abs_lt]; constructor <;> linarith

/-! ### The vector `ξ` -/

variable (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = q p)]

variable (p) in
/-- A fixed bijection `θ : K → ZMod q`. -/
noncomputable def theta : K ≃ ZMod (q p) :=
  Fintype.equivOfCardEq (by rw [card_K K p, ZMod.card])

variable (p) in
/-- `θ(k) ∈ {0, …, q-1}` as an integer. -/
noncomputable def thetaZ (k : K) : ℤ := ((theta p K k).val : ℤ)

theorem thetaZ_cast (k : K) : ((thetaZ p K k : ℤ) : ZMod (q p)) = theta p K k := by
  simp [thetaZ]

variable (p) in
/-- `ξ_O`: coefficient `θ(k)` on `X = kZ`, `1-κ-h_q` on `Y = 0` and `h_q` on `Z = 0`. -/
noncomputable def xiO : Vec K p :=
  ∑ k, thetaZ p K k • lineVec K p (.gen 0 k) + (1 - kappa p - hqN p) • lineVec K p (.hor 0) +
    (hqN p : ℤ) • lineVec K p .infty

variable (p) in
/-- `ξ = ξ_O + z`. -/
noncomputable def xi : Vec K p := xiO p K + zVec K

/-- `ξ ∈ 𝓛`. -/
theorem inL_xi : InL K p (xi p K) := by
  refine InL.add (InL.add (InL.add (InL.sum _ _ fun k _ => (InL.line _).smul _)
    ((InL.line _).smul _)) ((InL.line _).smul _)) (inL_zVec K)

theorem xi_aff (i j : K) :
    xi p K (Sum.inl (.aff i j)) = thetaZ p K i + (1 - kappa p - hqN p) * (if j = 0 then 1 else 0) := by
  simp only [xi, xiO, zVec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, lineVec,
    Sum.elim_inl, smul_eq_mul, Sum.elim_inl, Pi.zero_apply, add_zero]
  simp only [inc_aff_gen, zero_mul, zero_add, inc_aff_hor, inc_aff_infty, ite_false, mul_zero,
    add_zero, mul_ite, mul_one]
  simp [Finset.sum_ite_eq]

theorem xi_inf (k : K) :
    xi p K (Sum.inl (.inf k)) = (if k = 0 then ∑ k', thetaZ p K k' else 0) + hqN p := by
  simp only [xi, xiO, zVec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, lineVec,
    Sum.elim_inl, smul_eq_mul, Pi.zero_apply, add_zero]
  simp only [inc_inf_gen, inc_inf_hor, inc_inf_infty, ite_false, ite_true, mul_zero, add_zero,
    mul_one, mul_ite]
  split_ifs <;> simp

theorem xi_top : xi p K (Sum.inl .top) = 1 - kappa p := by
  simp [xi, xiO, zVec, lineVec]

theorem xi_extra (e : Pt (ZMod p)) : xi p K (Sum.inr e) = z p e := by
  simp [xi, xiO, zVec, lineVec]

/-! ### Residues of ordinary letters -/

variable (p) in
/-- The residue of `ξ` at an ordinary letter. -/
noncomputable def res (x : Pt K) : ZMod (q p) := ((xi p K (Sum.inl x) : ℤ) : ZMod (q p))

variable (p) in
/-- `c₀ = 1 - κ - h_q` in `ZMod q`. -/
def c0 : ZMod (q p) := ((1 - kappa p - hqN p : ℤ) : ZMod (q p))

theorem res_aff (i j : K) :
    res p K (.aff i j) = theta p K i + c0 p * (if j = 0 then 1 else 0) := by
  rw [res, xi_aff]
  push_cast
  rw [thetaZ_cast]
  simp [c0]

theorem res_inf (k : K) : res p K (.inf k) = hqZ p := by
  rw [res, xi_inf]
  split_ifs
  · push_cast
    have : ∑ k', ((thetaZ p K k' : ℤ) : ZMod (q p)) = 0 := by
      simp_rw [thetaZ_cast]
      rw [Equiv.sum_comp (theta p K) (fun x => x)]
      exact sum_zmod_id_of_odd q_odd
    rw [this, zero_add]; rfl
  · push_cast; rw [zero_add]; rfl

theorem res_top : res p K .top = ((1 - kappa p : ℤ) : ZMod (q p)) := by
  rw [res, xi_top]

/-- The residue count on `O`: `q + q [y = h_q] + [y = 1 - κ]`. -/
theorem card_res_eq (y : ZMod (q p)) :
    (univ.filter (fun x => res p K x = y)).card =
      q p + (if hqZ p = y then q p else 0) +
        (if ((1 - kappa p : ℤ) : ZMod (q p)) = y then 1 else 0) := by
  rw [Finset.card_filter, sum_pt]
  simp only [res_aff, res_inf, res_top]
  have hrow : ∀ j : K, ∑ i : K, (if theta p K i + c0 p * (if j = 0 then 1 else 0) = y
      then 1 else 0) = 1 := by
    intro j
    rw [← Finset.card_filter, Finset.card_eq_one]
    refine ⟨(theta p K).symm (y - c0 p * (if j = 0 then 1 else 0)), ?_⟩
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    rw [Equiv.eq_symm_apply]
    constructor
    · intro h; rw [← h]; ring
    · intro h; rw [h]; ring
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hrow j]
  simp only [Finset.sum_const, Finset.card_univ, card_K K p, smul_eq_mul, mul_one]
  split_ifs <;> simp

/-! ### Step 1: pairing each extra letter with an ordinary letter -/

variable (p) in
/-- An injection of the extra letters into the nonzero rows. -/
noncomputable def rowOf : Pt (ZMod p) ↪ Kˣ :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [card_pt_zmod, Fintype.card_units, card_K K p]
    unfold s q
    have h3 := three_le (p := p)
    have : p ^ 2 + p + 2 ≤ p ^ 5 := by nlinarith [pow_pos (by omega : 0 < p) 3]
    omega))

variable (p) in
/-- The ordinary partner `[θ⁻¹(1 - z(e)) : ι(e) : 1]` of an extra letter `e`. -/
noncomputable def piE (e : Pt (ZMod p)) : Pt K :=
  .aff ((theta p K).symm (1 - ((z p e : ℤ) : ZMod (q p)))) ((rowOf p K e : Kˣ) : K)

theorem piE_injective : Function.Injective (piE p K) := by
  intro e e' h
  simp only [piE, Pt.aff.injEq] at h
  exact (rowOf p K).injective (Units.ext h.2)

theorem res_piE (e : Pt (ZMod p)) : res p K (piE p K e) = 1 - ((z p e : ℤ) : ZMod (q p)) := by
  rw [piE, res_aff, ite_eq_right (Units.ne_zero _)]
  simp

/-! ### Step 2: the remaining ordinary letters -/

variable (p) in
/-- The ordinary letters not used in step 1. -/
noncomputable def restO : Finset (Pt K) := univ \ univ.image (piE p K)

theorem card_filter_image_piE (P : Pt K → Prop) [DecidablePred P] :
    ((univ.image (piE p K)).filter P).card = (univ.filter (fun e => P (piE p K e))).card := by
  rw [filter_image, card_image_of_injective _ (piE_injective K)]

theorem card_restO_filter (y : ZMod (q p)) :
    ((restO p K).filter (fun x => res p K x = y)).card +
      (univ.filter (fun e : Pt (ZMod p) => ((z p e : ℤ) : ZMod (q p)) = 1 - y)).card =
      (univ.filter (fun x => res p K x = y)).card := by
  have h1 : (restO p K).filter (fun x => res p K x = y) =
      univ.filter (fun x => res p K x = y) \ (univ.image (piE p K)).filter (fun x => res p K x = y) := by
    ext x; simp [restO]; tauto
  have h2 : (univ.image (piE p K)).filter (fun x => res p K x = y) ⊆
      univ.filter (fun x => res p K x = y) := by
    intro x; simp only [mem_filter, mem_univ, true_and]; exact fun h => h.2
  rw [h1, card_sdiff_of_subset h2, card_filter_image_piE]
  have h3 : (univ.filter (fun e : Pt (ZMod p) => res p K (piE p K e) = y)) =
      univ.filter (fun e : Pt (ZMod p) => ((z p e : ℤ) : ZMod (q p)) = 1 - y) := by
    ext e; simp only [mem_filter, mem_univ, true_and, res_piE]
    constructor <;> intro h <;> linear_combination -h
  rw [h3]
  have h4 := card_le_card h2
  rw [card_filter_image_piE, h3] at h4
  omega

/-- Lemma 7.4(c) modulo `q`: `#{e : z(e) ≡ y} + [1-κ ≡ y] = #{e : z(e) ≡ 1-y} + [κ ≡ y]`. -/
theorem card_z_res_symm (y : ZMod (q p)) :
    (univ.filter (fun e : Pt (ZMod p) => ((z p e : ℤ) : ZMod (q p)) = y)).card +
      (if ((1 - kappa p : ℤ) : ZMod (q p)) = y then 1 else 0) =
    (univ.filter (fun e : Pt (ZMod p) => ((z p e : ℤ) : ZMod (q p)) = 1 - y)).card +
      (if ((1 - kappa p : ℤ) : ZMod (q p)) = 1 - y then 1 else 0) := by
  -- both sides count the fibres of `zz` over `Option E`, exchanged by `zpair`
  have hopt : ∀ y' : ZMod (q p),
      (univ.filter (fun x : Option (Pt (ZMod p)) => ((zz x : ℤ) : ZMod (q p)) = y')).card =
      (univ.filter (fun e : Pt (ZMod p) => ((z p e : ℤ) : ZMod (q p)) = y')).card +
        (if ((1 - kappa p : ℤ) : ZMod (q p)) = y' then 1 else 0) := by
    intro y'
    rw [Finset.card_filter, Finset.card_filter, Fintype.sum_option]
    simp only [zz]
    exact add_comm _ _
  rw [← hopt, ← hopt]
  apply Finset.card_nbij' zpair zpair
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := zz_zpair x
    rw [← hx]
    have h' : zz (zpair x) = 1 - zz x := by linarith
    rw [h']; push_cast; ring
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := zz_zpair x
    have h' : zz (zpair x) = 1 - zz x := by linarith
    rw [h']; push_cast; rw [hx]; ring
  · intro x _; exact zpair_involutive x
  · intro x _; exact zpair_involutive x

theorem restO_count_symm (y : ZMod (q p)) :
    ((restO p K).filter (fun x => res p K x = y)).card =
      ((restO p K).filter (fun x => res p K x = 1 - y)).card := by
  have a1 := card_restO_filter K y
  have a2 := card_restO_filter K (1 - y)
  rw [card_res_eq] at a1 a2
  have a3 := card_z_res_symm y
  simp only [sub_sub_cancel] at a2
  have hh : 1 - hqZ p = hqZ p := (one_sub_eq_self_iff _).mpr rfl
  have e1 : (hqZ p = 1 - y) ↔ (hqZ p = y) := by
    constructor <;> intro h <;> linear_combination -h - hh
  simp only [e1] at a2
  split_ifs at a1 a2 a3 <;> omega

theorem restO_count_even :
    Even ((restO p K).filter (fun x => res p K x = hqZ p)).card := by
  have a1 := card_restO_filter K (hqZ p)
  rw [card_res_eq] at a1
  have h0 : (univ.filter (fun e : Pt (ZMod p) => ((z p e : ℤ) : ZMod (q p)) = 1 - hqZ p)) = ∅ := by
    rw [(one_sub_eq_self_iff _).mpr rfl]
    ext e; simp [z_ne_hqZ e]
  rw [h0, ite_eq_left rfl, ite_eq_right (Ne.symm one_sub_kappa_ne_hqZ |>.symm)] at a1
  simp only [card_empty, add_zero] at a1
  exact ⟨q p, by omega⟩

/-! ### Assembling the involution -/

theorem exists_sigma : ∃ σ : Pt K → Pt K, ∀ x ∈ restO p K,
    σ x ∈ restO p K ∧ σ x ≠ x ∧ σ (σ x) = x ∧ res p K (σ x) = 1 - res p K x := by
  have hφ : Function.Involutive (fun y : ZMod (q p) => 1 - y) := fun y => by ring
  refine exists_pairing (res p K) (fun y => 1 - y) hφ (restO p K)
    (fun y => restO_count_symm K y) ?_
  intro y hy
  rw [(one_sub_eq_self_iff y).mp hy]
  exact restO_count_even K

variable (p) in
/-- The pairing of the remaining ordinary letters. -/
noncomputable def sigmaO : Pt K → Pt K := Classical.choose (exists_sigma (p := p) K)

theorem sigmaO_spec (x : Pt K) (hx : x ∈ restO p K) :
    sigmaO p K x ∈ restO p K ∧ sigmaO p K x ≠ x ∧ sigmaO p K (sigmaO p K x) = x ∧
      res p K (sigmaO p K x) = 1 - res p K x :=
  Classical.choose_spec (exists_sigma (p := p) K) x hx

theorem mem_restO {x : Pt K} : x ∈ restO p K ↔ ∀ e, piE p K e ≠ x := by
  simp [restO]

variable (p) in
/-- The involution `t ↦ t̄` of Lemma 7.5. -/
noncomputable def barL : Letter K p → Letter K p
  | Sum.inr e => Sum.inl (piE p K e)
  | Sum.inl x =>
      if h : ∃ e, piE p K e = x then Sum.inr (Classical.choose h) else Sum.inl (sigmaO p K x)

theorem barL_inr (e : Pt (ZMod p)) : barL p K (Sum.inr e) = Sum.inl (piE p K e) := rfl

theorem barL_piE (e : Pt (ZMod p)) : barL p K (Sum.inl (piE p K e)) = Sum.inr e := by
  have h : ∃ e', piE p K e' = piE p K e := ⟨e, rfl⟩
  simp only [barL, dite_eq_left h]
  exact congrArg Sum.inr (piE_injective K (Classical.choose_spec h))

theorem barL_rest {x : Pt K} (hx : x ∈ restO p K) : barL p K (Sum.inl x) = Sum.inl (sigmaO p K x) := by
  have h : ¬ ∃ e, piE p K e = x := by
    rintro ⟨e, he⟩; exact (mem_restO K).mp hx e he
  simp only [barL, dite_eq_right h]

theorem barL_involutive : Function.Involutive (barL p K) := by
  intro t
  rcases t with x | e
  · by_cases hx : x ∈ restO p K
    · rw [barL_rest K hx, barL_rest K (sigmaO_spec K x hx).1, (sigmaO_spec K x hx).2.2.1]
    · obtain ⟨e, rfl⟩ : ∃ e, piE p K e = x := by
        by_contra h
        exact hx ((mem_restO K).mpr fun e he => h ⟨e, he⟩)
      rw [barL_piE, barL_inr]
  · rw [barL_inr, barL_piE]

theorem barL_ne (t : Letter K p) : barL p K t ≠ t := by
  rcases t with x | e
  · by_cases hx : x ∈ restO p K
    · rw [barL_rest K hx]
      exact fun h => (sigmaO_spec K x hx).2.1 (Sum.inl_injective h)
    · obtain ⟨e, rfl⟩ : ∃ e, piE p K e = x := by
        by_contra h
        exact hx ((mem_restO K).mpr fun e he => h ⟨e, he⟩)
      rw [barL_piE]; exact Sum.inr_ne_inl
  · rw [barL_inr]; exact Sum.inl_ne_inr

theorem barL_extra (t : Letter K p) (ht : IsExtra K p t) : ¬ IsExtra K p (barL p K t) := by
  rcases t with x | e
  · simp at ht
  · rw [barL_inr]; simp

/-- **Lemma 7.5** (`eq:residue`): `ξ(t) + ξ(t̄) ≡ 1 (mod q)`. -/
theorem xi_barL (t : Letter K p) :
    ((xi p K t + xi p K (barL p K t) : ℤ) : ZMod (q p)) = 1 := by
  rcases t with x | e
  · by_cases hx : x ∈ restO p K
    · rw [barL_rest K hx]
      push_cast
      have := (sigmaO_spec K x hx).2.2.2
      simp only [res] at this
      rw [this]; ring
    · obtain ⟨e, rfl⟩ : ∃ e, piE p K e = x := by
        by_contra h
        exact hx ((mem_restO K).mpr fun e he => h ⟨e, he⟩)
      rw [barL_piE, xi_extra]
      push_cast
      have := res_piE K e
      simp only [res] at this
      rw [this]; ring
  · rw [barL_inr, xi_extra]
    push_cast
    have := res_piE K e
    simp only [res] at this
    rw [this]; ring

/-- **Lemma 7.5**: there is a fixed-point-free involution `t ↦ t̄` of `T` with `Ē ⊆ O`
satisfying the residue condition `eq:residue` for the vector `ξ ∈ 𝓛`. -/
theorem exists_bar : ∃ bar : Letter K p → Letter K p,
    Function.Involutive bar ∧ (∀ t, bar t ≠ t) ∧
      (∀ t, IsExtra K p t → ¬ IsExtra K p (bar t)) ∧
      ∀ t, ((xi p K t + xi p K (bar t) : ℤ) : ZMod (q p)) = 1 :=
  ⟨barL p K, barL_involutive K, barL_ne K, barL_extra K, xi_barL K⟩

end Kaplansky.OddDesign
