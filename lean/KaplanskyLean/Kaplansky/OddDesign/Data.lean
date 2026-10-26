import Kaplansky.OddDesign.Vertices
import Kaplansky.OddDesign.Decay
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The interface `OddDesign.Data p` for the random-graph chain (agent D)

`Data p` bundles everything Section 7 provides to the random model, for an odd prime `p`:
the alphabet with its involution, the vertex sets `A₊`, `A₋`, `B` (for every size parameter
`m`, with `n = p^2 v^2 m`), the congruences and degrees of the types, the exact sizes, letter
frequencies and colour balance, the turn counts, and the squared-word decay.

`data p hp : Data p` constructs it for every odd prime `p`, with `q = p^5` realized by
`GaloisField p 5`.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

/-- The design data of Section 7 for the prime `p` (see `docs/C_INTERFACE.md`). -/
structure Data (p : ℕ) where
  /-- `p` is an odd prime, so `p ≥ 3` (needed by the random model: `q + 1 ≥ 244 ≥ 129`). -/
  three_le_p : 3 ≤ p
  /-- The alphabet `T = O ⊔ E`. -/
  T : Type
  [instFintypeT : Fintype T]
  [instDecEqT : DecidableEq T]
  /-- The extra letters `E` (points of `PG(2,p)`); the others are ordinary (points of
  `PG(2,q)`). -/
  extra : T → Prop
  [instDecExtra : DecidablePred extra]
  card_ord : (univ.filter fun t => ¬ extra t).card = v p
  card_extra : (univ.filter extra).card = s p
  /-- The fixed-point-free involution `t ↦ t̄` of Lemma 7.5. -/
  inv : T → T
  inv_inv : ∀ t, inv (inv t) = t
  inv_ne : ∀ t, inv t ≠ t
  /-- `Ē ⊆ O`. -/
  inv_extra : ∀ t, extra t → ¬ extra (inv t)
  /-- The colour class `A₊` (containing the root), for each `m`. -/
  VAp : ℕ → Type
  /-- The colour class `A₋`, for each `m`. -/
  VAm : ℕ → Type
  /-- The side `B`, for each `m`. -/
  VB : ℕ → Type
  [instFintypeVAp : ∀ m, Fintype (VAp m)]
  [instFintypeVAm : ∀ m, Fintype (VAm m)]
  [instFintypeVB : ∀ m, Fintype (VB m)]
  [instDecEqVAp : ∀ m, DecidableEq (VAp m)]
  [instDecEqVAm : ∀ m, DecidableEq (VAm m)]
  [instDecEqVB : ∀ m, DecidableEq (VB m)]
  /-- Outgoing letter sets `S_x`. -/
  outAp : ∀ m, VAp m → Finset T
  outAm : ∀ m, VAm m → Finset T
  outB : ∀ m, VB m → Finset T
  /-- All types (non-root types and the root type `S_r`). -/
  types : Finset (Finset T)
  /-- The root type `S_r = ℓ_r ∪ E`. -/
  rootSet : Finset T
  rootSet_mem : rootSet ∈ types
  outAp_mem : ∀ m x, outAp m x ∈ types
  outAm_mem : ∀ m x, outAm m x ∈ types
  outB_mem : ∀ m y, outB m y ∈ types
  /-- The root `r ∈ A₊`, the only vertex of type `S_r`. -/
  root : ∀ m, VAp m
  out_root : ∀ m, outAp m (root m) = rootSet
  root_unique : ∀ m x, outAp m x = rootSet → x = root m
  outAm_ne_root : ∀ m x, outAm m x ≠ rootSet
  outB_ne_root : ∀ m y, outB m y ≠ rootSet
  /-- **Lemma 7.2**: `|S ∩ S'| ≡ 1 (mod p)` unless `S = S' = S_r`; `|S_r| ≡ 2 (mod p)`. -/
  cong : ∀ S ∈ types, ∀ S' ∈ types,
    (S ∩ S').card % p = if S = rootSet ∧ S' = rootSet then 2 % p else 1
  /-- Degrees `q+1 ≤ |S| ≤ q+1+s`. -/
  deg : ∀ S ∈ types, q p + 1 ≤ S.card ∧ S.card ≤ q p + 1 + s p
  /-- The threshold beyond which the multiplicities of Proposition 7.6 are positive. -/
  m₀ : ℕ
  /-- Size corrections. -/
  cAp : ℤ
  cAm : ℤ
  /-- Sizes, `n = p^2 v^2 m`. -/
  card_VB : ∀ m, Fintype.card (VB m) = p ^ 2 * v p ^ 2 * m
  card_VAp : ∀ m, m₀ ≤ m → (Fintype.card (VAp m) : ℤ) = p ^ 2 * v p ^ 2 * m + cAp
  card_VAm : ∀ m, m₀ ≤ m → (Fintype.card (VAm m) : ℤ) = p ^ 2 * v p ^ 2 * m + cAm
  /-- Pool corrections. -/
  eAp : T → ℤ
  eAm : T → ℤ
  /-- Letter frequencies: pools of size `n λ = p^2 v (q+1) m` (up to fixed corrections). -/
  pool_B : ∀ m t, Fintype.card {y : VB m // t ∈ outB m y} = p ^ 2 * v p * (q p + 1) * m
  pool_Ap : ∀ m, m₀ ≤ m → ∀ t,
    (Fintype.card {x : VAp m // t ∈ outAp m x} : ℤ) = p ^ 2 * v p * (q p + 1) * m + eAp t
  pool_Am : ∀ m, m₀ ≤ m → ∀ t,
    (Fintype.card {x : VAm m // t ∈ outAm m x} : ℤ) = p ^ 2 * v p * (q p + 1) * m + eAm t
  /-- **Proposition 7.6**, colour balance `eq:balance`: `μ₊(t) = μ₋(t̄)`. -/
  balance : ∀ m, m₀ ≤ m → ∀ t,
    Fintype.card {x : VAp m // t ∈ outAp m x} = Fintype.card {x : VAm m // inv t ∈ outAm m x}
  balance_B : ∀ m t,
    Fintype.card {y : VB m // t ∈ outB m y} = Fintype.card {y : VB m // inv t ∈ outB m y}
  /-- The bound on the turn-count corrections. -/
  Cturn : ℕ
  /-- **Lemma 7.7** (with `a = t̄`, `b = u`): exact on `B`. -/
  pair_B : ∀ m a b, a ≠ b →
    (Fintype.card {y : VB m // a ∈ outB m y ∧ b ∈ outB m y} : ℝ) =
      ((p ^ 2 * v p ^ 2 * m : ℕ) : ℝ) * lam p * baseW p extra a b
  /-- **Lemma 7.7** on `A₊`, with an error bounded independently of `m`. -/
  pair_Ap : ∀ m, m₀ ≤ m → ∀ a b, a ≠ b →
    |(Fintype.card {x : VAp m // a ∈ outAp m x ∧ b ∈ outAp m x} : ℝ) -
      ((p ^ 2 * v p ^ 2 * m : ℕ) : ℝ) * lam p * baseW p extra a b| ≤ Cturn
  /-- **Lemma 7.7** on `A₋`. -/
  pair_Am : ∀ m, m₀ ≤ m → ∀ a b, a ≠ b →
    |(Fintype.card {x : VAm m // a ∈ outAm m x ∧ b ∈ outAm m x} : ℝ) -
      ((p ^ 2 * v p ^ 2 * m : ℕ) : ℝ) * lam p * baseW p extra a b| ≤ Cturn
  /-- **Lemma 7.8**, Perron certificate `M f ≤ ρ f`. -/
  perron : ∀ t, ∑ u, turnW p inv extra t u ^ 2 * testF p inv extra u ≤
    rho p * testF p inv extra t
  /-- **Lemma 7.8**, squared-word bound `∑_{W ∈ T^{h+1}} P(W)^2 ≤ p^2 |T| ρ^h`. -/
  decay : ∀ h, ∑ W : Fin (h + 1) → T, wordWeight (turnW p inv extra) (h + 1) W ^ 2 ≤
    (p : ℝ) ^ 2 * Fintype.card T * rho p ^ h
  /-- `δ = 1/Dδ`. -/
  Dδ : ℕ
  /-- The decay threshold. -/
  h₀ : ℕ
  /-- The bin constant `a₀`. -/
  A₀ : ℕ
  Dδ_pos : 0 < Dδ
  /-- **Lemma 7.8**, exponential form. -/
  decay_exp : ∀ h, h₀ ≤ h →
    ∑ W : Fin h → T, wordWeight (turnW p inv extra) h W ^ 2 ≤ Real.exp (-2 * (1 / (Dδ : ℝ)) * h)
  A₀_ge : 2 * Real.log ((q p : ℝ) + 1) ≤ A₀

attribute [instance] Data.instFintypeT Data.instDecEqT Data.instDecExtra Data.instFintypeVAp
  Data.instFintypeVAm Data.instFintypeVB Data.instDecEqVAp Data.instDecEqVAm Data.instDecEqVB

/-! ### Construction for a general field of order `q` -/

section Construction

variable {p : ℕ} [Fact p.Prime] [Fact (3 ≤ p)]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = q p)]

theorem card_ord_letter : (univ.filter fun t : Letter K p => ¬ IsExtra K p t).card = v p := by
  have : (univ.filter fun t : Letter K p => ¬ IsExtra K p t) = univ.map Function.Embedding.inl := by
    ext t; rcases t with x | e <;> simp
  rw [this, card_map, card_univ, card_pt_K (p := p) K]

theorem card_extra_letter : (univ.filter fun t : Letter K p => IsExtra K p t).card = s p := by
  have : (univ.filter fun t : Letter K p => IsExtra K p t) = univ.map Function.Embedding.inr := by
    ext t; rcases t with x | e <;> simp
  rw [this, card_map, card_univ, card_pt_zmod]

theorem pair_real_bound {m : ℕ} {a b : Letter K p} (hab : a ≠ b) (c : ℤ) (err : ℤ)
    (hc : c = m * pairU p K a b + err) (herr : |err| ≤ errBound p K) :
    |(c : ℝ) - ((p ^ 2 * v p ^ 2 * m : ℕ) : ℝ) * lam p * baseW p (IsExtra K p) a b| ≤
      (errBound p K).toNat := by
  have h1 : ((p ^ 2 * v p ^ 2 * m : ℕ) : ℝ) * lam p * baseW p (IsExtra K p) a b =
      m * (pairU p K a b : ℝ) := by
    rw [pairU_real K hab]; push_cast; ring
  rw [h1, hc]
  push_cast
  have h2 : ((errBound p K).toNat : ℝ) = (errBound p K : ℝ) := by
    have : 0 ≤ errBound p K := le_trans (abs_nonneg _) herr
    exact_mod_cast Int.toNat_of_nonneg this
  rw [h2]
  have : |(err : ℝ)| ≤ (errBound p K : ℝ) := by exact_mod_cast herr
  simpa using this

variable (p) in
/-- The design data, for a finite field `K` of order `q = p^5`. -/
noncomputable def dataOf : Data p where
  three_le_p := three_le
  T := Letter K p
  extra := IsExtra K p
  card_ord := card_ord_letter K
  card_extra := card_extra_letter K
  inv := barL p K
  inv_inv := barL_involutive K
  inv_ne := barL_ne K
  inv_extra := barL_extra K
  VAp := VAp p K
  VAm := VAm p K
  VB := VB p K
  outAp _ := outAp p K
  outAm _ := outAm p K
  outB _ := outB p K
  types := allTypes p K
  rootSet := rootSet K p
  rootSet_mem := mem_insert_self _ _
  outAp_mem _ := outAp_mem K
  outAm_mem _ := outAm_mem K
  outB_mem _ := outB_mem K
  root _ := none
  out_root _ := rfl
  root_unique _ _ h := outAp_eq_root K h
  outAm_ne_root _ := outAm_ne_root K
  outB_ne_root _ := outB_ne_root K
  cong _ hS _ hS' := cong_allTypes K hS hS'
  deg _ hS := card_allTypes K hS
  m₀ := m0 p K
  cAp := 1 - ∑ τ, uC p K τ
  cAm := ∑ τ, vC p K τ
  card_VB m := card_VB K m
  card_VAp _ hm := card_VAp K hm
  card_VAm _ hm := card_VAm K hm
  eAp t := rootVec p K t - comb K p (uC p K) t
  eAm t := comb K p (vC p K) t
  pool_B m t := by rw [pool_B]; rfl
  pool_Ap m hm t := by
    rw [pool_Ap K hm, muAp_eq, poolN]; push_cast; ring
  pool_Am m hm t := by
    rw [pool_Am K hm, muAm_eq, poolN]; push_cast; ring
  balance _ hm t := balance_card K hm t
  balance_B m t := balance_B K m t
  Cturn := (errBound p K).toNat
  pair_B m a b hab := by
    rw [pair_B K m a b]
    push_cast
    rw [pairU_real K hab]; ring
  pair_Ap m hm a b hab :=
    pair_real_bound K hab _ _ (pair_Ap K hm a b) (abs_errAp_le K a b)
  pair_Am m hm a b hab :=
    pair_real_bound K hab _ _ (pair_Am K hm a b) (abs_errAm_le K a b)
  perron t := perron_certificate (three_le (p := p)) (barL_involutive K) (barL_extra K)
    (card_ord_letter K) (card_extra_letter K) t
  decay h := squared_word_bound (three_le (p := p)) (barL_involutive K) (barL_extra K)
    (card_ord_letter K) (card_extra_letter K) h
  Dδ := 8 * (q p + 1)
  h₀ := 8 * (q p + 1) * (p ^ 2 * Fintype.card (Letter K p))
  A₀ := 2 * (q p + 1)
  Dδ_pos := by positivity
  decay_exp h hh := decay_exp (three_le (p := p)) (barL_involutive K) (barL_extra K)
    (card_ord_letter K) (card_extra_letter K) h hh
  A₀_ge := log_le_A₀ p

end Construction

/-! ### The construction for every odd prime -/

/-- `GaloisField p 5` has `q = p^5` elements. -/
theorem card_galoisField (p : ℕ) [Fact p.Prime] [Fintype (GaloisField p 5)] :
    Fintype.card (GaloisField p 5) = q p := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p 5 (by norm_num)]; rfl

theorem three_le_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le; omega

/-- **The design data of Section 7, for every odd prime `p`.** -/
noncomputable def data (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : Data p :=
  letI : Fintype (GaloisField p 5) := Fintype.ofFinite _
  letI : DecidableEq (GaloisField p 5) := Classical.decEq _
  haveI : Fact (Fintype.card (GaloisField p 5) = q p) := ⟨card_galoisField p⟩
  haveI : Fact (3 ≤ p) := ⟨three_le_of_prime Fact.out hp⟩
  dataOf p (GaloisField p 5)

/-- **Existence of the design data for every odd prime.** -/
theorem nonempty_data (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : Nonempty (Data p) :=
  haveI : Fact p.Prime := ⟨hp⟩
  ⟨data p h2⟩

/-! ### Derived facts for the random-graph chain -/

namespace Data

variable {p : ℕ} (D : Data p)

/-- `v λ J ≥ 1` for every pair: the turn-count errors are absorbed into the size. -/
theorem one_le_v_lam_baseW (a b : D.T) (hp : 2 ≤ p) :
    1 ≤ (v p : ℝ) * lam p * baseW p D.extra a b := by
  have hv := v_real_pos p
  have hq : (0 : ℝ) ≤ q p := Nat.cast_nonneg _
  have h1 : (v p : ℝ) * lam p = (q p : ℝ) + 1 := by
    rw [lam]; field_simp
  rw [h1]
  have h2 := baseW_ge D.extra hp a b
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

/-- Upper bound in the form `card ≤ n' λ J` with `n' = n + Cturn · v` (side `A₊`). -/
theorem pair_Ap_le (hp : 2 ≤ p) {m : ℕ} (hm : D.m₀ ≤ m) {a b : D.T} (hab : a ≠ b) :
    (Fintype.card {x : D.VAp m // a ∈ D.outAp m x ∧ b ∈ D.outAp m x} : ℝ) ≤
      (((p ^ 2 * v p ^ 2 * m : ℕ) : ℝ) + D.Cturn * v p) * lam p * baseW p D.extra a b := by
  have h1 := (abs_le.mp (D.pair_Ap m hm a b hab)).2
  have h2 := D.one_le_v_lam_baseW a b hp
  have hC : (0 : ℝ) ≤ D.Cturn := Nat.cast_nonneg _
  nlinarith

/-- Upper bound in the form `card ≤ n' λ J` with `n' = n + Cturn · v` (side `A₋`). -/
theorem pair_Am_le (hp : 2 ≤ p) {m : ℕ} (hm : D.m₀ ≤ m) {a b : D.T} (hab : a ≠ b) :
    (Fintype.card {x : D.VAm m // a ∈ D.outAm m x ∧ b ∈ D.outAm m x} : ℝ) ≤
      (((p ^ 2 * v p ^ 2 * m : ℕ) : ℝ) + D.Cturn * v p) * lam p * baseW p D.extra a b := by
  have h1 := (abs_le.mp (D.pair_Am m hm a b hab)).2
  have h2 := D.one_le_v_lam_baseW a b hp
  have hC : (0 : ℝ) ≤ D.Cturn := Nat.cast_nonneg _
  nlinarith

/-- Upper bound in the form `card ≤ n' λ J` (side `B`). -/
theorem pair_B_le (hp : 2 ≤ p) (m : ℕ) {a b : D.T} (hab : a ≠ b) :
    (Fintype.card {y : D.VB m // a ∈ D.outB m y ∧ b ∈ D.outB m y} : ℝ) ≤
      (((p ^ 2 * v p ^ 2 * m : ℕ) : ℝ) + D.Cturn * v p) * lam p * baseW p D.extra a b := by
  rw [D.pair_B m a b hab]
  have h2 := D.one_le_v_lam_baseW a b hp
  have hC : (0 : ℝ) ≤ D.Cturn := Nat.cast_nonneg _
  nlinarith

/-- Every degree is at least `q+1 ≥ 244 ≥ 129` (OpenAI's chain needs `129`). -/
theorem deg_ge (hp : 3 ≤ p) {S : Finset D.T} (hS : S ∈ D.types) : 244 ≤ S.card := by
  have h := (D.deg S hS).1
  have : 243 ≤ q p := by
    unfold q
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ p ^ 5 := Nat.pow_le_pow_left hp 5
  omega

instance nonempty_T : Nonempty D.T := by
  have : 0 < (univ.filter D.extra).card := by rw [D.card_extra]; exact s_pos p
  obtain ⟨t, _⟩ := card_pos.mp this
  exact ⟨t⟩

include D in
theorem one_le_p : 1 ≤ p := by have := D.three_le_p; omega

include D in
theorem two_le_p : 2 ≤ p := by have := D.three_le_p; omega

include D in
/-- `q = p^5 ≥ 243`. -/
theorem q_ge : 243 ≤ q p := by
  have h := D.three_le_p
  unfold q
  calc 243 = 3 ^ 5 := by norm_num
    _ ≤ p ^ 5 := Nat.pow_le_pow_left h 5

/-- Every degree is at least `q+1 ≥ 244` (no side hypothesis). -/
theorem deg_ge' {S : Finset D.T} (hS : S ∈ D.types) : 244 ≤ S.card :=
  D.deg_ge D.three_le_p hS

end Data

end Kaplansky.OddDesign
