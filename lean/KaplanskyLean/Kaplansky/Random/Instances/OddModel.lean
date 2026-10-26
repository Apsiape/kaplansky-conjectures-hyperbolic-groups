import Kaplansky.Random.Instances.TwoColour
import Kaplansky.OddDesign.Data

/-!
# The two-colour random model of the odd-`p` design (paper §7.4, Prop 7.9 / Cor 7.10)

Agent AC's design data `Kaplansky.OddDesign.Data p` (Section 7: types, involution, vertex sets
`A₊ ∋ r`, `A₋`, `B`, colour balance, turn counts, Perron decay) is turned into a `TwoColourData`,
hence into a random `Model`.  The alphabet is `T = O ⊔ E` with joint weights `baseW` (so the turn
weights are `turnW`), `W = q + 1`, `δ = 1/Dδ`; the first-moment data are `n₀ = p²v²`,
`λ = (q+1)/v`, `P₀ = p² v (q+1)`.

Besides the model, this file exports the witness-level facts used by Proposition 7.11, in terms of
the sides of the model (no probability involved):

* `cong_AA`, `cong_root`, `cong_AB`: `|S_x ∩ S_x'| ≡ 1 (mod p)` on `A × A` off `(r, r)`,
  `|S_r ∩ S_r| ≡ 2`, and `|S_x ∩ S_y| ≡ 1` on `A × B` (Lemma 7.2 and uniqueness of the root type);
* `col_root`: the root `r` lies in the colour class `A₊` (colour `true`); the colouring of side `A`
  is `Model.SA.col`, with `flip = not`, so every edge of `Γ_A` reverses the colour
  (`SampleGraph.colourA_flip` of `Random/PatternFree.lean`).
-/

namespace Kaplansky.Random

open Filter
open scoped BigOperators

noncomputable section

namespace Odd

open Kaplansky.OddDesign

variable {p : ℕ} (D : Data p)

/-- The alphabet of the design: letters `T`, involution `t ↦ t̄`, joint weights `baseW`. -/
abbrev alphabet : Alphabet where
  α := D.T
  inv := D.inv
  inv_inv := D.inv_inv
  inv_ne := D.inv_ne
  J := baseW p D.extra
  J_nonneg := baseW_nonneg D.extra D.one_le_p
  J_le_one := baseW_le_one p D.extra
  W := q p + 1
  W_pos := Nat.succ_pos _
  J_ge a b _ := by
    have h := baseW_ge D.extra D.two_le_p a b
    push_cast
    exact h

theorem alphabet_J : (alphabet D).J = baseW p D.extra := rfl

theorem alphabet_weight (t u : D.T) :
    (alphabet D).weight t u = turnW p D.inv D.extra t u := rfl

theorem alphabet_continuation (n : ℕ) (t : D.T) (W : Fin n → D.T) :
    (alphabet D).continuation n t W = continuation (turnW p D.inv D.extra) n t W := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [Alphabet.continuation, OddDesign.continuation]
    rw [ih]
    rfl

theorem alphabet_wordWeight (h : ℕ) (W : Fin h → D.T) :
    (alphabet D).wordWeight h W = wordWeight (turnW p D.inv D.extra) h W := by
  cases h with
  | zero => rfl
  | succ h =>
    simp only [Alphabet.wordWeight, OddDesign.wordWeight]
    exact alphabet_continuation D h (W 0) (Fin.tail W)

theorem alphabet_decays : (alphabet D).Decays D.Dδ D.h₀ := by
  intro h hh
  have e : (∑ W : Fin h → D.T, (alphabet D).wordWeight h W ^ 2) =
      ∑ W : Fin h → D.T, wordWeight (turnW p D.inv D.extra) h W ^ 2 :=
    Finset.sum_congr rfl (fun W _ => by rw [alphabet_wordWeight])
  exact e.trans_le (D.decay_exp h hh)

/-- **The two-colour model data of the odd-`p` design** (paper §7.4). -/
def twoColour : TwoColourData where
  toAlphabet := alphabet D
  D := D.Dδ
  D_pos := D.Dδ_pos
  h₀ := D.h₀
  decays := alphabet_decays D
  A₀ := D.A₀
  A₀_ge := by
    have h := D.A₀_ge
    show 2 * Real.log ((q p + 1 : ℕ) : ℝ) ≤ (D.A₀ : ℝ)
    push_cast
    exact h
  VAp := D.VAp
  VAm := D.VAm
  VB := D.VB
  outAp := D.outAp
  outAm := D.outAm
  outB := D.outB
  m₀ := D.m₀
  dlo := q p + 1
  dhi := q p + 1 + s p
  dlo_ge := by have := D.q_ge; omega
  dlo_le := by omega
  degAp m x := D.deg _ (D.outAp_mem m x)
  degAm m x := D.deg _ (D.outAm_mem m x)
  degB m y := D.deg _ (D.outB_mem m y)
  n₀ := p ^ 2 * v p ^ 2
  n₀_pos := Nat.mul_pos (pow_pos (by have := D.one_le_p; omega) 2) (pow_pos (v_pos p) 2)
  lam := lam p
  lam_pos := lam_pos p
  lam_le := (lam_le_one p).trans (by norm_num)
  P₀ := p ^ 2 * v p * (q p + 1)
  P₀_eq := by
    have hv := v_real_pos p
    unfold lam
    rw [mul_div_assoc', eq_div_iff hv.ne']
    push_cast
    ring
  cAp := D.cAp
  cAm := D.cAm
  card_VAp m hm := by
    convert D.card_VAp m hm using 1
    push_cast
    ring
  card_VAm m hm := by
    convert D.card_VAm m hm using 1
    push_cast
    ring
  card_VB m _ := D.card_VB m
  eAp := D.eAp
  eAm := D.eAm
  poolAp m hm t := by
    convert D.pool_Ap m hm t using 1
    push_cast
    ring
  poolAm m hm t := by
    convert D.pool_Am m hm t using 1
    push_cast
    ring
  poolB m _ t := D.pool_B m t
  balance := D.balance
  Cturn := D.Cturn
  Cturn_nonneg := Nat.cast_nonneg _
  pairAp m hm a b hab := by
    have h := D.pair_Ap m hm a b hab
    push_cast at h ⊢
    exact h
  pairAm m hm a b hab := by
    have h := D.pair_Am m hm a b hab
    push_cast at h ⊢
    exact h
  pairB m _ a b hab := by
    have h := D.pair_B m a b hab
    refine Eq.trans_le ?_ (Nat.cast_nonneg D.Cturn)
    rw [abs_eq_zero, sub_eq_zero]
    push_cast at h ⊢
    exact h

/-- The random model of the odd-`p` design. -/
def model : Model := (twoColour D).model

/-! ### Witness-level facts in terms of the model -/

theorem model_SA_V (m : ℕ) : (model D).SA.V m = (D.VAp (m + D.m₀) ⊕ D.VAm (m + D.m₀)) := rfl

theorem model_SB_V (m : ℕ) : (model D).SB.V m = D.VB (m + D.m₀) := rfl

theorem model_SA_out_inl (m : ℕ) (x : D.VAp (m + D.m₀)) :
    (model D).SA.out m (Sum.inl x) = D.outAp (m + D.m₀) x := rfl

theorem model_SA_out_inr (m : ℕ) (x : D.VAm (m + D.m₀)) :
    (model D).SA.out m (Sum.inr x) = D.outAm (m + D.m₀) x := rfl

theorem model_SB_out (m : ℕ) (y : D.VB (m + D.m₀)) :
    (model D).SB.out m y = D.outB (m + D.m₀) y := rfl

theorem model_inv : (model D).inv = D.inv := rfl

/-- The root `r ∈ A₊` of the model at size parameter `m`. -/
def root (m : ℕ) : (model D).SA.V m := Sum.inl (D.root (m + D.m₀))

/-- The colour classes of side `A`: `true` on `A₊`, `false` on `A₋`. -/
theorem model_SA_col_inl (m : ℕ) (x : D.VAp (m + D.m₀)) :
    (model D).SA.col m (Sum.inl x) = true := rfl

theorem model_SA_col_inr (m : ℕ) (x : D.VAm (m + D.m₀)) :
    (model D).SA.col m (Sum.inr x) = false := rfl

/-- The root lies in `A₊`. -/
theorem col_root (m : ℕ) : (model D).SA.col m (root D m) = true := rfl

/-- Colours of side `A` are flipped by `not` (every edge joins `A₊` to `A₋`). -/
theorem model_SA_flip (c : (model D).SA.Col) : (model D).SA.flip c = !c := rfl

theorem model_SA_out_mem (m : ℕ) (x : (model D).SA.V m) : (model D).SA.out m x ∈ D.types := by
  rcases x with x | x
  · exact D.outAp_mem _ x
  · exact D.outAm_mem _ x

theorem model_SB_out_mem (m : ℕ) (y : (model D).SB.V m) : (model D).SB.out m y ∈ D.types :=
  D.outB_mem _ y

/-- The root is the only vertex of side `A` of root type. -/
theorem out_eq_rootSet_iff (m : ℕ) (x : (model D).SA.V m) :
    (model D).SA.out m x = D.rootSet ↔ x = root D m := by
  constructor
  · intro h
    rcases x with x | x
    · exact congrArg Sum.inl (D.root_unique _ x h)
    · exact absurd h (D.outAm_ne_root _ x)
  · rintro rfl
    exact D.out_root _

theorem out_root (m : ℕ) : (model D).SA.out m (root D m) = D.rootSet := D.out_root _

include D in
theorem one_mod_p : 1 % p = 1 := Nat.mod_eq_of_lt (by have := D.three_le_p; omega)

/-- **Lemma 7.2 on `A × A`**: `|S_x ∩ S_x'| ≡ 1 (mod p)` unless `x = x' = r`. -/
theorem cong_AA (m : ℕ) (x x' : (model D).SA.V m) (h : (x, x') ≠ (root D m, root D m)) :
    ((model D).SA.out m x ∩ (model D).SA.out m x').card ≡ 1 [MOD p] := by
  have hc := D.cong _ (model_SA_out_mem D m x) _ (model_SA_out_mem D m x')
  rw [ite_eq_right] at hc
  · exact hc.trans (one_mod_p D).symm
  · rintro ⟨h1, h2⟩
    exact h (by rw [(out_eq_rootSet_iff D m x).mp h1, (out_eq_rootSet_iff D m x').mp h2])

/-- **Lemma 7.2 at the root**: `|S_r ∩ S_r| = |S_r| ≡ 2 (mod p)`. -/
theorem cong_root (m : ℕ) :
    ((model D).SA.out m (root D m) ∩ (model D).SA.out m (root D m)).card ≡ 2 [MOD p] := by
  have hc := D.cong _ (model_SA_out_mem D m (root D m)) _ (model_SA_out_mem D m (root D m))
  rw [ite_eq_left ⟨out_root D m, out_root D m⟩] at hc
  exact hc

/-- **Lemma 7.2 on `A × B`**: `|S_x ∩ S_y| ≡ 1 (mod p)` (no vertex of `B` has root type). -/
theorem cong_AB (m : ℕ) (x : (model D).SA.V m) (y : (model D).SB.V m) :
    ((model D).SA.out m x ∩ (model D).SB.out m y).card ≡ 1 [MOD p] := by
  have hc := D.cong _ (model_SA_out_mem D m x) _ (model_SB_out_mem D m y)
  rw [ite_eq_right (fun h => D.outB_ne_root _ y h.2)] at hc
  exact hc.trans (one_mod_p D).symm

end Odd

end

end Kaplansky.Random
