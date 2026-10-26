import Kaplansky.Random.Model
import Kaplansky.Random.Instances.Counting

/-!
# The two-colour odd-`p` model (paper §6.3, §7.4) as a `Model`

`TwoColourData` is the input that the odd-`p` design of agent C (`Kaplansky.OddDesign.Data`,
see `docs/C_INTERFACE.md`) provides, in the exact form used here:

* an `Alphabet` (letters `T`, involution, weights `J = baseW`, `W = q+1`) with squared-word
  decay `δ = 1/D` from `h₀` on and `A₀ ≥ 2 log W`;
* three families of vertex types `A₊`, `A₋`, `B` (all statements for `m ≥ m₀`):
  degrees in `[dlo, dhi]` with `dlo ≥ 129`; sizes `n₀ m + O(1)` (`n₀ = p²v²`);
  pools `P₀ m + O(1)` with `P₀ = n₀ λ` (`B` exactly `P₀ m`); the two-colour balance
  `|A₊_t| = |A₋_{t̄}|`; turn tables `|# - n₀ m λ J(a,b)| ≤ C_turn`.

The model: side `A = A₊ ⊔ A₋` with colours `Bool` (`A₊ = true`) and `flip = not`, so matchings
join `(t,+)` to `(t̄,-)`; side `B` with one colour.  First-moment data: `n = 2(n₀ m' + C'')`,
`p = λ/2` (`m' = m + m₀`), so `n p J = (n₀ m' + C'') λ J` dominates every per-colour table.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology
open scoped BigOperators

noncomputable section

/-- The odd-`p` two-colour design data consumed by the random-graph chain. -/
structure TwoColourData extends Alphabet where
  D : ℕ
  D_pos : 0 < D
  h₀ : ℕ
  decays : toAlphabet.Decays D h₀
  A₀ : ℕ
  A₀_ge : 2 * Real.log W ≤ A₀
  VAp : ℕ → Type
  VAm : ℕ → Type
  VB : ℕ → Type
  [fAp : ∀ m, Fintype (VAp m)]
  [dAp : ∀ m, DecidableEq (VAp m)]
  [fAm : ∀ m, Fintype (VAm m)]
  [dAm : ∀ m, DecidableEq (VAm m)]
  [fB : ∀ m, Fintype (VB m)]
  [dB : ∀ m, DecidableEq (VB m)]
  outAp : ∀ m, VAp m → Finset α
  outAm : ∀ m, VAm m → Finset α
  outB : ∀ m, VB m → Finset α
  m₀ : ℕ
  dlo : ℕ
  dhi : ℕ
  dlo_ge : 129 ≤ dlo
  dlo_le : dlo ≤ dhi
  degAp : ∀ m x, dlo ≤ (outAp m x).card ∧ (outAp m x).card ≤ dhi
  degAm : ∀ m x, dlo ≤ (outAm m x).card ∧ (outAm m x).card ≤ dhi
  degB : ∀ m y, dlo ≤ (outB m y).card ∧ (outB m y).card ≤ dhi
  n₀ : ℕ
  n₀_pos : 0 < n₀
  lam : ℝ
  lam_pos : 0 < lam
  lam_le : lam ≤ 2
  P₀ : ℕ
  P₀_eq : (P₀ : ℝ) = n₀ * lam
  cAp : ℤ
  cAm : ℤ
  card_VAp : ∀ m, m₀ ≤ m → (Fintype.card (VAp m) : ℤ) = n₀ * m + cAp
  card_VAm : ∀ m, m₀ ≤ m → (Fintype.card (VAm m) : ℤ) = n₀ * m + cAm
  card_VB : ∀ m, m₀ ≤ m → Fintype.card (VB m) = n₀ * m
  eAp : α → ℤ
  eAm : α → ℤ
  poolAp : ∀ m, m₀ ≤ m → ∀ t, (Fintype.card {x : VAp m // t ∈ outAp m x} : ℤ) = P₀ * m + eAp t
  poolAm : ∀ m, m₀ ≤ m → ∀ t, (Fintype.card {x : VAm m // t ∈ outAm m x} : ℤ) = P₀ * m + eAm t
  poolB : ∀ m, m₀ ≤ m → ∀ t, Fintype.card {y : VB m // t ∈ outB m y} = P₀ * m
  balance : ∀ m, m₀ ≤ m → ∀ t,
    Fintype.card {x : VAp m // t ∈ outAp m x} = Fintype.card {x : VAm m // inv t ∈ outAm m x}
  Cturn : ℝ
  Cturn_nonneg : 0 ≤ Cturn
  pairAp : ∀ m, m₀ ≤ m → ∀ a b, a ≠ b →
    |(Fintype.card {x : VAp m // a ∈ outAp m x ∧ b ∈ outAp m x} : ℝ) - n₀ * m * lam * J a b| ≤
      Cturn
  pairAm : ∀ m, m₀ ≤ m → ∀ a b, a ≠ b →
    |(Fintype.card {x : VAm m // a ∈ outAm m x ∧ b ∈ outAm m x} : ℝ) - n₀ * m * lam * J a b| ≤
      Cturn
  pairB : ∀ m, m₀ ≤ m → ∀ a b, a ≠ b →
    |(Fintype.card {y : VB m // a ∈ outB m y ∧ b ∈ outB m y} : ℝ) - n₀ * m * lam * J a b| ≤
      Cturn

attribute [instance] TwoColourData.fAp TwoColourData.dAp TwoColourData.fAm TwoColourData.dAm
  TwoColourData.fB TwoColourData.dB

namespace TwoColourData

variable (X : TwoColourData)

/-! ### The two sides -/

/-- Side `A = A₊ ⊔ A₋`; colour `true` on `A₊`; matched ports have opposite colours. -/
abbrev sideA : Side X.toAlphabet where
  Col := Bool
  flip := not
  flip_flip := Bool.not_not
  V m := X.VAp (m + X.m₀) ⊕ X.VAm (m + X.m₀)
  col _ := Sum.elim (fun _ => true) (fun _ => false)
  out m := Sum.elim (X.outAp (m + X.m₀)) (X.outAm (m + X.m₀))

/-- Side `B`, one colour class. -/
abbrev sideB : Side X.toAlphabet where
  Col := Unit
  flip := id
  flip_flip _ := rfl
  V m := X.VB (m + X.m₀)
  col _ _ := ()
  out m := X.outB (m + X.m₀)

theorem le_shift (m : ℕ) : X.m₀ ≤ m + X.m₀ := Nat.le_add_left _ _

theorem sideA_pool_true (m : ℕ) (t : X.α) :
    X.sideA.pool m t true = Fintype.card {x : X.VAp (m + X.m₀) // t ∈ X.outAp _ x} := by
  unfold Side.pool
  rw [card_subtype_sum]
  have h0 : Fintype.card {y : X.VAm (m + X.m₀) //
      X.sideA.col m (Sum.inr y) = true ∧ t ∈ X.sideA.out m (Sum.inr y)} = 0 :=
    card_subtype_of_false _ (fun y h => Bool.false_ne_true h.1)
  rw [h0, add_zero]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩))

theorem sideA_pool_false (m : ℕ) (t : X.α) :
    X.sideA.pool m t false = Fintype.card {x : X.VAm (m + X.m₀) // t ∈ X.outAm _ x} := by
  unfold Side.pool
  rw [card_subtype_sum]
  have h0 : Fintype.card {x : X.VAp (m + X.m₀) //
      X.sideA.col m (Sum.inl x) = false ∧ t ∈ X.sideA.out m (Sum.inl x)} = 0 :=
    card_subtype_of_false _ (fun x h => Bool.false_ne_true h.1.symm)
  rw [h0, zero_add]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩))

theorem sideB_pool (m : ℕ) (t : X.α) (c : Unit) :
    X.sideB.pool m t c = Fintype.card {y : X.VB (m + X.m₀) // t ∈ X.outB _ y} := by
  unfold Side.pool
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun y => ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩))

theorem sideA_joint_true (m : ℕ) (a b : X.α) :
    X.sideA.joint m true a b =
      Fintype.card {x : X.VAp (m + X.m₀) // a ∈ X.outAp _ x ∧ b ∈ X.outAp _ x} := by
  unfold Side.joint
  rw [card_subtype_sum]
  have h0 : Fintype.card {y : X.VAm (m + X.m₀) // X.sideA.col m (Sum.inr y) = true ∧
      a ∈ X.sideA.out m (Sum.inr y) ∧ b ∈ X.sideA.out m (Sum.inr y)} = 0 :=
    card_subtype_of_false _ (fun y h => Bool.false_ne_true h.1)
  rw [h0, add_zero]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩))

theorem sideA_joint_false (m : ℕ) (a b : X.α) :
    X.sideA.joint m false a b =
      Fintype.card {x : X.VAm (m + X.m₀) // a ∈ X.outAm _ x ∧ b ∈ X.outAm _ x} := by
  unfold Side.joint
  rw [card_subtype_sum]
  have h0 : Fintype.card {x : X.VAp (m + X.m₀) // X.sideA.col m (Sum.inl x) = false ∧
      a ∈ X.sideA.out m (Sum.inl x) ∧ b ∈ X.sideA.out m (Sum.inl x)} = 0 :=
    card_subtype_of_false _ (fun x h => Bool.false_ne_true h.1.symm)
  rw [h0, zero_add]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩))

theorem sideB_joint (m : ℕ) (c : Unit) (a b : X.α) :
    X.sideB.joint m c a b =
      Fintype.card {y : X.VB (m + X.m₀) // a ∈ X.outB _ y ∧ b ∈ X.outB _ y} := by
  unfold Side.joint
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun y => ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩))

/-! ### Constants -/

/-- Uniform bound for the pool corrections. -/
def E : ℕ := ∑ t, ((X.eAp t).natAbs + (X.eAm t).natAbs)

theorem eAp_le (t : X.α) : -(X.E : ℤ) ≤ X.eAp t ∧ X.eAp t ≤ X.E := by
  have h : (X.eAp t).natAbs ≤ X.E :=
    le_trans (Nat.le_add_right _ _)
      (Finset.single_le_sum (f := fun t => (X.eAp t).natAbs + (X.eAm t).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  have h' : |X.eAp t| ≤ (X.E : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h
  exact abs_le.mp h'

theorem eAm_le (t : X.α) : -(X.E : ℤ) ≤ X.eAm t ∧ X.eAm t ≤ X.E := by
  have h : (X.eAm t).natAbs ≤ X.E :=
    le_trans (Nat.le_add_left _ _)
      (Finset.single_le_sum (f := fun t => (X.eAp t).natAbs + (X.eAm t).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  have h' : |X.eAm t| ≤ (X.E : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h
  exact abs_le.mp h'

/-- Size correction `C''`, large enough for the turn-table errors and the size corrections. -/
def C2 : ℝ := X.Cturn * X.W / X.lam + ((X.cAp.natAbs + X.cAm.natAbs : ℕ) : ℝ)

theorem C2_nonneg : 0 ≤ X.C2 := by
  unfold C2
  have := X.Cturn_nonneg
  have := X.lam_pos
  positivity

/-- `n m = 2 (n₀ m' + C'')`. -/
def nRef (m : ℕ) : ℝ := 2 * (X.n₀ * ((m + X.m₀ : ℕ) : ℝ) + X.C2)

/-- `N m = 2 n₀ m' + |c₊| + |c₋|` bounds both sides. -/
def NRef (m : ℕ) : ℕ := 2 * X.n₀ * (m + X.m₀) + (X.cAp.natAbs + X.cAm.natAbs)

/-- Common lower bound for the pools. -/
def carrier (m : ℕ) : ℕ := X.P₀ * (m + X.m₀) - X.E

theorem P₀_pos : (0 : ℝ) < X.P₀ := by
  rw [X.P₀_eq]
  exact mul_pos (by exact_mod_cast X.n₀_pos) X.lam_pos

theorem W_pos' : (0 : ℝ) < X.W := by exact_mod_cast X.W_pos

theorem card_A (m : ℕ) :
    (Fintype.card (X.sideA.V m) : ℤ) =
      2 * X.n₀ * ((m + X.m₀ : ℕ) : ℤ) + X.cAp + X.cAm := by
  show (Fintype.card (X.VAp (m + X.m₀) ⊕ X.VAm (m + X.m₀)) : ℤ) = _
  rw [Fintype.card_sum, Nat.cast_add, X.card_VAp _ (X.le_shift m), X.card_VAm _ (X.le_shift m)]
  ring

theorem cardA_le (m : ℕ) : Fintype.card (X.sideA.V m) ≤ X.NRef m := by
  have h := X.card_A m
  have h1 : X.cAp ≤ |X.cAp| := le_abs_self _
  have h2 : X.cAm ≤ |X.cAm| := le_abs_self _
  unfold NRef
  zify
  push_cast at h ⊢
  linarith

theorem cardB_le (m : ℕ) : Fintype.card (X.sideB.V m) ≤ X.NRef m := by
  show Fintype.card (X.VB (m + X.m₀)) ≤ _
  rw [X.card_VB _ (X.le_shift m)]
  unfold NRef
  rw [show 2 * X.n₀ * (m + X.m₀) = X.n₀ * (m + X.m₀) + X.n₀ * (m + X.m₀) by ring]
  omega

/-! ### Tables -/

theorem table_of_pair {k : ℕ} {m : ℕ} {a b : X.α} (hab : a ≠ b)
    (h : |(k : ℝ) - X.n₀ * ((m + X.m₀ : ℕ) : ℝ) * X.lam * X.J a b| ≤ X.Cturn) :
    (k : ℝ) ≤ X.nRef m * (X.lam / 2) * X.J a b := by
  have h1 := (abs_le.mp h).2
  have hJ : 1 / (X.W : ℝ) ≤ X.J a b := X.J_ge a b hab
  have hW := X.W_pos'
  have hlam := X.lam_pos
  have hJpos : 0 < X.J a b := lt_of_lt_of_le (by positivity) hJ
  -- `C_turn ≤ C'' λ J`
  have hslack : X.Cturn ≤ X.C2 * X.lam * X.J a b := by
    have hc : X.Cturn = X.Cturn * X.W / X.lam * X.lam * (1 / X.W) := by
      field_simp
    have hrest : (0 : ℝ) ≤ ((X.cAp.natAbs + X.cAm.natAbs : ℕ) : ℝ) * X.lam * X.J a b := by
      positivity
    have hmono : X.Cturn * X.W / X.lam * X.lam * (1 / X.W) ≤
        X.Cturn * X.W / X.lam * X.lam * X.J a b := by
      have : 0 ≤ X.Cturn * X.W / X.lam * X.lam := by
        have := X.Cturn_nonneg
        positivity
      exact mul_le_mul_of_nonneg_left hJ this
    unfold C2
    nlinarith
  unfold nRef
  nlinarith

theorem tableA (m : ℕ) (c : Bool) (a b : X.α) (hab : a ≠ b) :
    (X.sideA.joint m c a b : ℝ) ≤ X.nRef m * (X.lam / 2) * X.J a b := by
  cases c
  · rw [sideA_joint_false]
    exact X.table_of_pair hab (X.pairAm _ (X.le_shift m) a b hab)
  · rw [sideA_joint_true]
    exact X.table_of_pair hab (X.pairAp _ (X.le_shift m) a b hab)

theorem tableB (m : ℕ) (c : Unit) (a b : X.α) (hab : a ≠ b) :
    (X.sideB.joint m c a b : ℝ) ≤ X.nRef m * (X.lam / 2) * X.J a b := by
  rw [sideB_joint]
  exact X.table_of_pair hab (X.pairB _ (X.le_shift m) a b hab)

/-! ### Pools -/

theorem balanceA (m : ℕ) (t : X.α) (c : Bool) :
    X.sideA.pool m t c = X.sideA.pool m (X.inv t) (X.sideA.flip c) := by
  cases c
  · show X.sideA.pool m t false = X.sideA.pool m (X.inv t) true
    rw [sideA_pool_false, sideA_pool_true, X.balance _ (X.le_shift m) (X.inv t), X.inv_inv]
  · show X.sideA.pool m t true = X.sideA.pool m (X.inv t) false
    rw [sideA_pool_false, sideA_pool_true, X.balance _ (X.le_shift m) t]

theorem balanceB (m : ℕ) (t : X.α) (c : Unit) :
    X.sideB.pool m t c = X.sideB.pool m (X.inv t) (X.sideB.flip c) := by
  rw [sideB_pool, sideB_pool, X.poolB _ (X.le_shift m), X.poolB _ (X.le_shift m)]

theorem poolA (m : ℕ) (t : X.α) (c : Bool) : X.carrier m ≤ X.sideA.pool m t c := by
  unfold carrier
  cases c
  · rw [sideA_pool_false]
    have h := X.poolAm _ (X.le_shift m) t
    have he := X.eAm_le t
    omega
  · rw [sideA_pool_true]
    have h := X.poolAp _ (X.le_shift m) t
    have he := X.eAp_le t
    omega

theorem poolB' (m : ℕ) (t : X.α) (c : Unit) : X.carrier m ≤ X.sideB.pool m t c := by
  unfold carrier
  rw [sideB_pool, X.poolB _ (X.le_shift m)]
  exact Nat.sub_le _ _

theorem carrier_le (m : ℕ) : (X.carrier m : ℝ) ≤ X.nRef m * (X.lam / 2) := by
  have h1 : (X.carrier m : ℝ) ≤ X.P₀ * ((m + X.m₀ : ℕ) : ℝ) := by
    unfold carrier
    exact_mod_cast Nat.sub_le _ _
  have h2 : X.nRef m * (X.lam / 2) = X.P₀ * ((m + X.m₀ : ℕ) : ℝ) + X.C2 * X.lam := by
    unfold nRef
    rw [X.P₀_eq]
    ring
  have h3 : 0 ≤ X.C2 * X.lam := mul_nonneg X.C2_nonneg X.lam_pos.le
  linarith

/-- Eventually the carrier is `P₀ m' - E` without truncation. -/
theorem carrier_cast : ∀ᶠ m in atTop,
    (X.carrier m : ℝ) = X.P₀ * ((m : ℝ) + X.m₀) - X.E := by
  have hP : 0 < X.P₀ := by exact_mod_cast X.P₀_pos
  filter_upwards [eventually_ge_atTop X.E] with m hm
  have hle : X.E ≤ X.P₀ * (m + X.m₀) := by nlinarith
  unfold carrier
  rw [Nat.cast_sub hle]
  push_cast
  ring

theorem ratio : Tendsto (fun m => X.nRef m * (X.lam / 2) / X.carrier m) atTop (𝓝 1) := by
  have hP := X.P₀_pos
  have h := affine_ratio (X.P₀ : ℝ) (X.P₀ : ℝ) (X.P₀ * X.m₀ + X.C2 * X.lam)
    (X.P₀ * X.m₀ - X.E) hP.ne'
  rw [div_self hP.ne'] at h
  refine h.congr' ?_
  filter_upwards [X.carrier_cast] with m hm
  rw [hm]
  unfold nRef
  rw [X.P₀_eq]
  push_cast
  congr 1 <;> ring

theorem carrier_lin : ∀ᶠ m in atTop,
    X.P₀ / (4 * X.n₀) * (X.NRef m : ℝ) ≤ X.carrier m := by
  have hP := X.P₀_pos
  have hn : (0 : ℝ) < X.n₀ := by exact_mod_cast X.n₀_pos
  have h := affine_ratio (X.P₀ : ℝ) (2 * X.n₀ : ℝ) (X.P₀ * X.m₀ - X.E)
    (2 * X.n₀ * X.m₀ + (X.cAp.natAbs + X.cAm.natAbs : ℕ)) (by positivity)
  have hlt : (X.P₀ : ℝ) / (4 * X.n₀) < (X.P₀ : ℝ) / (2 * X.n₀) := by
    apply div_lt_div_of_pos_left hP (by linarith)
    linarith
  filter_upwards [h.eventually (lt_mem_nhds hlt), X.carrier_cast, eventually_ge_atTop 1]
    with m hm hc hm1
  have hN : (0 : ℝ) < X.NRef m := by
    unfold NRef
    have : 0 < 2 * X.n₀ * (m + X.m₀) + (X.cAp.natAbs + X.cAm.natAbs) :=
      Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos (by norm_num) X.n₀_pos) (by omega))
        (Nat.le_add_right _ _)
    exact_mod_cast this
  have hNe : (X.NRef m : ℝ) = 2 * X.n₀ * m + (2 * X.n₀ * X.m₀ +
      ((X.cAp.natAbs + X.cAm.natAbs : ℕ) : ℝ)) := by
    unfold NRef
    push_cast
    ring
  have hce : (X.carrier m : ℝ) = X.P₀ * m + (X.P₀ * X.m₀ - X.E) := by
    rw [hc]
    ring
  rw [← hNe, ← hce] at hm
  rw [lt_div_iff₀ hN] at hm
  linarith

theorem NRef_tendsto : Tendsto X.NRef atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro m
  unfold NRef
  have := X.n₀_pos
  calc m ≤ m + X.m₀ := Nat.le_add_right _ _
    _ ≤ 2 * X.n₀ * (m + X.m₀) := Nat.le_mul_of_pos_left _ (by have := X.n₀_pos; omega)
    _ ≤ _ := Nat.le_add_right _ _

theorem log_dhi : 12 * Real.log X.dhi < ((12 * X.dhi : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) < X.dhi := by
    have := X.dlo_ge
    have := X.dlo_le
    exact_mod_cast (show 0 < X.dhi by omega)
  have h := Real.log_le_sub_one_of_pos hpos
  push_cast
  linarith

/-! ### The model -/

/-- The two-colour odd-`p` model. -/
def model : Model where
  toAlphabet := X.toAlphabet
  D := X.D
  D_pos := X.D_pos
  h₀ := X.h₀
  decays := X.decays
  A₀ := X.A₀
  A₀_ge := X.A₀_ge
  SA := X.sideA
  SB := X.sideB
  c := 12 * X.dhi
  c_pos := by have := X.dlo_ge; have := X.dlo_le; omega
  N := X.NRef
  N_tendsto := X.NRef_tendsto
  dmax := X.dhi
  dmax_ge := by have := X.dlo_ge; have := X.dlo_le; omega
  log_dmax := X.log_dhi
  cardA_le := X.cardA_le
  cardB_le := X.cardB_le
  degA m x := by
    rcases x with x | x
    · have h := X.degAp (m + X.m₀) x
      exact ⟨le_trans X.dlo_ge h.1, h.2⟩
    · have h := X.degAm (m + X.m₀) x
      exact ⟨le_trans X.dlo_ge h.1, h.2⟩
  degB m y := by
    have h := X.degB (m + X.m₀) y
    exact ⟨le_trans X.dlo_ge h.1, h.2⟩
  balanceA := X.balanceA
  balanceB := X.balanceB
  p := X.lam / 2
  p_pos := by have := X.lam_pos; positivity
  p_le_one := by have := X.lam_le; linarith
  n := X.nRef
  cardA_le_n m := by
    have h := X.card_A m
    have h1 : X.cAp ≤ (X.cAp.natAbs : ℤ) := Int.le_natAbs
    have h2 : X.cAm ≤ (X.cAm.natAbs : ℤ) := Int.le_natAbs
    have h3 : ((Fintype.card (X.sideA.V m) : ℤ) : ℝ) ≤
        2 * X.n₀ * ((m + X.m₀ : ℕ) : ℝ) + ((X.cAp.natAbs + X.cAm.natAbs : ℕ) : ℝ) := by
      have h1' : (X.cAp : ℝ) ≤ (X.cAp.natAbs : ℝ) :=
        (Int.cast_le.mpr h1).trans_eq (Int.cast_natCast _)
      have h2' : (X.cAm : ℝ) ≤ (X.cAm.natAbs : ℝ) :=
        (Int.cast_le.mpr h2).trans_eq (Int.cast_natCast _)
      rw [h]
      push_cast at h1' h2' ⊢
      linarith
    have h4 : ((X.cAp.natAbs + X.cAm.natAbs : ℕ) : ℝ) ≤ 2 * X.C2 := by
      unfold C2
      have : 0 ≤ X.Cturn * X.W / X.lam := by
        have := X.Cturn_nonneg
        have := X.lam_pos
        have := X.W_pos'
        positivity
      have : (0 : ℝ) ≤ ((X.cAp.natAbs + X.cAm.natAbs : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    unfold nRef
    push_cast at h3 h4 ⊢
    linarith
  cardB_le_n m := by
    show (Fintype.card (X.VB (m + X.m₀)) : ℝ) ≤ X.nRef m
    rw [X.card_VB _ (X.le_shift m)]
    unfold nRef
    have := X.C2_nonneg
    have : (0 : ℝ) ≤ X.n₀ * ((m + X.m₀ : ℕ) : ℝ) := by positivity
    push_cast at this ⊢
    linarith
  tableA := X.tableA
  tableB := X.tableB
  carrier := X.carrier
  poolA := X.poolA
  poolB := X.poolB'
  carrier_le := X.carrier_le
  ratio := X.ratio
  κ := X.P₀ / (4 * X.n₀)
  κ_pos := by
    have := X.P₀_pos
    have : (0 : ℝ) < X.n₀ := by exact_mod_cast X.n₀_pos
    positivity
  carrier_lin := X.carrier_lin

end TwoColourData

end

end Kaplansky.Random
