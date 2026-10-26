import Kaplansky.Challenge

/-!
# The algebra of Kaplansky's conjectures (paper, Section 2)

Mghirbi–Douglas, *Kaplansky's conjectures fail for torsion-free hyperbolic groups in positive
characteristic*, Section 2.

* `Kaplansky.Algebra.onesided`: **Lemma 2.1** (one-sided inverses). For `ab = 1 ≠ ba` in a ring,
  `e = ba` and `ν = b(1 - e)` satisfy `e² = e ∉ {0, 1}`, `e(1 - e) = 0 = (1 - e)e`, `ν ≠ 0 = ν²`,
  and `1 ± ν` are mutually inverse.
* `Kaplansky.Algebra.one_add_ne_single`: **Lemma 2.2** (square-zero elements give non-trivial units),
  over a field and a torsion-free group (`Kaplansky.TorsionFree`). In characteristic `p`,
  `(1 + ν)^p = 1` (`one_add_pow_char_eq_one`) and the unit has order exactly `p`
  (`orderOf_unitOfSqZero`).
* `Kaplansky.Algebra.sqZero_of_mul_eq_zero`: the formal part of **Lemma 2.3** (zero divisors give
  square-zero elements), with Connell's primeness theorem replaced by an explicit hypothesis.
* `Kaplansky.Algebra.baseChange`: **base change** `𝔽_p[G] → K[G]` for a field `K` of
  characteristic `p`; it is an injective unital ring hom (`baseChange_injective`), so `ab = 1 ≠ ba`
  transfers (`map_mul_eq_one_and_ne`).
-/

namespace Kaplansky.Algebra

/-! ### Lemma 2.1: one-sided inverses -/

section OneSided

variable {R : Type*} [Ring R] {a b : R}

/-- `e = ba` is idempotent when `ab = 1`. -/
theorem idem_of_mul_eq_one (hab : a * b = 1) : (b * a) * (b * a) = b * a := by
  calc (b * a) * (b * a) = b * (a * b) * a := by simp only [mul_assoc]
    _ = b * a := by rw [hab, mul_one]

/-- `(1 - e) b = 0` for `e = ba` when `ab = 1`. -/
theorem one_sub_mul_mul_eq_zero (hab : a * b = 1) : (1 - b * a) * b = 0 := by
  rw [sub_mul, one_mul, mul_assoc, hab, mul_one, sub_self]

/-- `e (1 - e) = 0` for `e = ba` when `ab = 1`. -/
theorem idem_mul_one_sub (hab : a * b = 1) : (b * a) * (1 - b * a) = 0 := by
  rw [mul_sub, mul_one, idem_of_mul_eq_one hab, sub_self]

/-- `(1 - e) e = 0` for `e = ba` when `ab = 1`. -/
theorem one_sub_mul_idem (hab : a * b = 1) : (1 - b * a) * (b * a) = 0 := by
  rw [sub_mul, one_mul, idem_of_mul_eq_one hab, sub_self]

/-- `e = ba ≠ 0` when `ab = 1 ≠ ba`: indeed `a e b = (ab)² = 1`. -/
theorem idem_ne_zero (hab : a * b = 1) (hba : b * a ≠ 1) : b * a ≠ 0 := by
  intro h
  have h10 : (1 : R) = 0 :=
    calc (1 : R) = (a * b) * (a * b) := by rw [hab, one_mul]
      _ = a * (b * a) * b := by simp only [mul_assoc]
      _ = 0 := by rw [h, mul_zero, zero_mul]
  exact hba (h.trans h10.symm)

/-- `1 - e ≠ 0` when `ba ≠ 1`. -/
theorem one_sub_idem_ne_zero (hba : b * a ≠ 1) : 1 - b * a ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm hba)

/-- The square-zero element `ν = b (1 - ba)`: `ν² = 0`. -/
theorem nu_mul_nu (hab : a * b = 1) : (b * (1 - b * a)) * (b * (1 - b * a)) = 0 := by
  calc (b * (1 - b * a)) * (b * (1 - b * a)) = b * ((1 - b * a) * b) * (1 - b * a) := by
        simp only [mul_assoc]
    _ = 0 := by rw [one_sub_mul_mul_eq_zero hab, mul_zero, zero_mul]

/-- `ν = b (1 - ba) ≠ 0` when `ab = 1 ≠ ba`: indeed `a ν = 1 - ba ≠ 0`. -/
theorem nu_ne_zero (hab : a * b = 1) (hba : b * a ≠ 1) : b * (1 - b * a) ≠ 0 := by
  intro h
  have h' : a * (b * (1 - b * a)) = 1 - b * a := by rw [← mul_assoc, hab, one_mul]
  rw [h, mul_zero] at h'
  exact one_sub_idem_ne_zero hba h'.symm

/-- If `ν² = 0` then `(1 + ν)(1 - ν) = 1`. -/
theorem one_add_mul_one_sub {ν : R} (h : ν * ν = 0) : (1 + ν) * (1 - ν) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, h, sub_zero, sub_add_cancel]

/-- If `ν² = 0` then `(1 - ν)(1 + ν) = 1`. -/
theorem one_sub_mul_one_add {ν : R} (h : ν * ν = 0) : (1 - ν) * (1 + ν) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, h, add_zero, add_sub_cancel_right]

/-- **Lemma 2.1** (one-sided inverses). If `ab = 1 ≠ ba`, then `e = ba` and `ν = b(1 - e)` satisfy
`e² = e`, `e ≠ 0`, `e ≠ 1`, `e(1 - e) = 0 = (1 - e)e`, `ν ≠ 0`, `ν² = 0`, and
`(1 + ν)(1 - ν) = 1 = (1 - ν)(1 + ν)`. -/
theorem onesided (hab : a * b = 1) (hba : b * a ≠ 1) :
    (b * a) * (b * a) = b * a ∧ b * a ≠ 0 ∧ b * a ≠ 1 ∧
    (b * a) * (1 - b * a) = 0 ∧ (1 - b * a) * (b * a) = 0 ∧
    b * (1 - b * a) ≠ 0 ∧ (b * (1 - b * a)) * (b * (1 - b * a)) = 0 ∧
    (1 + b * (1 - b * a)) * (1 - b * (1 - b * a)) = 1 ∧
    (1 - b * (1 - b * a)) * (1 + b * (1 - b * a)) = 1 :=
  ⟨idem_of_mul_eq_one hab, idem_ne_zero hab hba, hba, idem_mul_one_sub hab, one_sub_mul_idem hab,
    nu_ne_zero hab hba, nu_mul_nu hab, one_add_mul_one_sub (nu_mul_nu hab),
    one_sub_mul_one_add (nu_mul_nu hab)⟩

/-- If `ac = 0` with `c ≠ 0`, then `ba ≠ 1` for every `b` (since otherwise `c = (ba)c = b(ac) = 0`).
This is how `ba ≠ 1` is certified in Prop. 5.1(c) and Prop. 7.11. -/
theorem mul_ne_one_of_mul_eq_zero {c : R} (hac : a * c = 0) (hc : c ≠ 0) : b * a ≠ 1 := by
  intro h
  apply hc
  calc c = (b * a) * c := by rw [h, one_mul]
    _ = 0 := by rw [mul_assoc, hac, mul_zero]

end OneSided

/-! ### Square-zero elements and units -/

section SqZero

variable {R : Type*} [Ring R]

/-- The unit `1 + ν`, with inverse `1 - ν`, attached to a square-zero element `ν`. -/
def unitOfSqZero (ν : R) (h : ν * ν = 0) : Rˣ where
  val := 1 + ν
  inv := 1 - ν
  val_inv := one_add_mul_one_sub h
  inv_val := one_sub_mul_one_add h

@[simp] theorem val_unitOfSqZero (ν : R) (h : ν * ν = 0) : (unitOfSqZero ν h : R) = 1 + ν := rfl

/-- If `ν² = 0` then `(1 + ν)^k = 1 + kν`. -/
theorem one_add_pow_of_sq_zero {ν : R} (h : ν * ν = 0) (k : ℕ) :
    (1 + ν) ^ k = 1 + (k : R) * ν := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    calc (1 + (k : R) * ν) * (1 + ν) = 1 + ((k : R) * ν + ν) + (k : R) * (ν * ν) := by
          simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc]; abel
      _ = 1 + ((k : R) + 1) * ν := by rw [h, mul_zero, add_zero, add_mul, one_mul]

/-- In characteristic `p` (in the weak sense `(p : R) = 0`), `(1 + ν)^p = 1` when `ν² = 0`. -/
theorem one_add_pow_char_eq_one {ν : R} (h : ν * ν = 0) {p : ℕ} (hp : (p : R) = 0) :
    (1 + ν) ^ p = 1 := by
  rw [one_add_pow_of_sq_zero h, hp, zero_mul, add_zero]

/-- The unit `1 + ν` has order exactly `p` when `ν ≠ 0 = ν²` and `(p : R) = 0`, `p` prime. -/
theorem orderOf_unitOfSqZero {ν : R} (h : ν * ν = 0) (hν : ν ≠ 0) {p : ℕ} [Fact p.Prime]
    (hp : (p : R) = 0) : orderOf (unitOfSqZero ν h) = p := by
  apply orderOf_eq_prime
  · ext
    rw [Units.val_pow_eq_pow_val, val_unitOfSqZero, Units.val_one]
    exact one_add_pow_char_eq_one h hp
  · intro h1
    apply hν
    have := congrArg Units.val h1
    rw [val_unitOfSqZero, Units.val_one] at this
    simpa using this

end SqZero

/-! ### Lemma 2.2: square-zero elements give non-trivial units -/

section Unit

open MonoidAlgebra

/-- **Lemma 2.2**, with the only consequence of torsion-freeness that is used: `g² = 1 → g = 1`.
If `ν ≠ 0 = ν²` in `K[G]`, then `1 + ν` is not of the form `λ g`. -/
theorem one_add_ne_single_of_sq {K G : Type*} [Field K] [Group G]
    (hG : ∀ g : G, g ^ 2 = 1 → g = 1) {ν : MonoidAlgebra K G} (hν : ν ≠ 0) (hν2 : ν * ν = 0)
    (g : G) (c : K) : 1 + ν ≠ single g c := by
  classical
  intro h
  have hν' : ν = single g c - 1 := by rw [← h, add_sub_cancel_left]
  by_cases hg : g = 1
  · subst hg
    have h1 : ν = single 1 (c - 1) := by rw [hν', single_sub, one_def]
    rw [h1, single_mul_single, one_mul, single_eq_zero, mul_self_eq_zero] at hν2
    exact hν (by rw [h1, hν2, single_zero])
  · have hg2 : g * g ≠ 1 := fun h2 => hg (hG g (by rw [pow_two]; exact h2))
    have hsq : ν * ν = single (g * g) (c * c) - single g c - single g c + 1 := by
      rw [hν', ← single_mul_single]; noncomm_ring
    have hcoef : (ν * ν).coeff 1 = 1 := by
      rw [hsq, coeff_add, coeff_sub, coeff_sub, Finsupp.add_apply, Finsupp.sub_apply,
        Finsupp.sub_apply, coeff_one_one, coeff_single, coeff_single, Finsupp.single_apply,
        Finsupp.single_apply, ite_eq_right hg2, ite_eq_right hg]
      simp
    rw [hν2, coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoef
    exact zero_ne_one hcoef

/-- **Lemma 2.2** (square-zero elements give non-trivial units). Let `G` be torsion-free, `K` a
field and `ν ∈ K[G]` with `ν ≠ 0 = ν²`. Then `1 + ν` is a unit (`unitOfSqZero`) that is not of the
form `λ g`. -/
theorem one_add_ne_single {K : Type*} [Field K] {G : Type} [Group G] (hG : Kaplansky.TorsionFree G)
    {ν : MonoidAlgebra K G} (hν : ν ≠ 0) (hν2 : ν * ν = 0) (g : G) (c : K) :
    1 + ν ≠ single g c :=
  one_add_ne_single_of_sq (fun g hg => hG g 2 two_pos hg) hν hν2 g c

/-- Lemma 2.2 together with the remark after it: in characteristic `p`, the unit `1 + ν` is not of
the form `λ g`, satisfies `(1 + ν)^p = 1`, and has order exactly `p`. -/
theorem exists_unit_of_sqZero (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p] {G : Type}
    [Group G] (hG : Kaplansky.TorsionFree G) {ν : MonoidAlgebra K G} (hν : ν ≠ 0)
    (hν2 : ν * ν = 0) :
    ∃ u : (MonoidAlgebra K G)ˣ, (u : MonoidAlgebra K G) = 1 + ν ∧
      (u : MonoidAlgebra K G) ^ p = 1 ∧ orderOf u = p ∧
      ∀ (c : K) (g : G), (u : MonoidAlgebra K G) ≠ single g c := by
  have hp : (p : MonoidAlgebra K G) = 0 := by
    rw [natCast_def, CharP.cast_eq_zero, single_zero]
  exact ⟨unitOfSqZero ν hν2, rfl, one_add_pow_char_eq_one hν2 hp,
    orderOf_unitOfSqZero hν2 hν hp, fun c g => one_add_ne_single hG hν hν2 g c⟩

end Unit

/-! ### Lemma 2.3, formal part -/

section ZeroDivisor

variable {R : Type*} [Ring R]

/-- The formal part of **Lemma 2.3**: if `αβ = 0` and `β x α ≠ 0` for some `x`, then
`ν = β x α` satisfies `ν ≠ 0 = ν²`. (In the paper, the existence of `x = g ∈ G` with `β g α ≠ 0`
comes from Connell's theorem that `K[G]` is prime, which is not in Mathlib.) -/
theorem sqZero_of_mul_eq_zero {α β x : R} (hαβ : α * β = 0) (hx : β * x * α ≠ 0) :
    ∃ ν : R, ν ≠ 0 ∧ ν * ν = 0 :=
  ⟨β * x * α, hx, by
    calc β * x * α * (β * x * α) = β * x * (α * β) * x * α := by simp only [mul_assoc]
      _ = 0 := by rw [hαβ, mul_zero, zero_mul, zero_mul]⟩

/-- Lemma 2.3 in a prime ring (`x R y = 0 → x = 0 ∨ y = 0`): zero divisors give square-zero
elements. -/
theorem sqZero_of_zeroDivisor_of_prime
    (hprime : ∀ x y : R, (∀ z : R, x * z * y = 0) → x = 0 ∨ y = 0)
    {α β : R} (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α * β = 0) :
    ∃ ν : R, ν ≠ 0 ∧ ν * ν = 0 := by
  by_contra hcon
  have hz : ∀ z : R, β * z * α = 0 := by
    intro z
    by_contra hz
    exact hcon (sqZero_of_mul_eq_zero hαβ hz)
  rcases hprime β α hz with h | h
  · exact hβ h
  · exact hα h

end ZeroDivisor

/-! ### Base change `𝔽_p[G] → K[G]` -/

section BaseChange

/-- An injective ring hom transports `ab = 1 ≠ ba`. -/
theorem map_mul_eq_one_and_ne {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (hφ : Function.Injective φ) {a b : R} (hab : a * b = 1) (hba : b * a ≠ 1) :
    φ a * φ b = 1 ∧ φ b * φ a ≠ 1 :=
  ⟨by rw [← map_mul, hab, map_one], fun h => hba (hφ (by rw [map_mul, h, map_one]))⟩

/-- The base-change map `𝔽_p[G] → K[G]` for a ring `K` of characteristic `p`: apply the canonical
map `ZMod p → K` to the coefficients. It is a unital ring hom. -/
noncomputable def baseChange (p : ℕ) (K : Type*) [Ring K] [CharP K p] (G : Type*) [Monoid G] :
    MonoidAlgebra (ZMod p) G →+* MonoidAlgebra K G :=
  MonoidAlgebra.mapRingHom G (ZMod.castHom (dvd_refl p) K)

@[simp] theorem baseChange_single (p : ℕ) (K : Type*) [Ring K] [CharP K p] (G : Type*) [Monoid G]
    (g : G) (c : ZMod p) :
    baseChange p K G (MonoidAlgebra.single g c) = MonoidAlgebra.single g (ZMod.castHom (dvd_refl p) K c) :=
  MonoidAlgebra.mapRingHom_single _ _ _

/-- Base change `𝔽_p[G] → K[G]` is injective for a field (more generally a nontrivial ring) `K` of
characteristic `p`, `p` prime. -/
theorem baseChange_injective (p : ℕ) [Fact p.Prime] (K : Type*) [Ring K] [Nontrivial K] [CharP K p]
    (G : Type*) [Monoid G] : Function.Injective (baseChange p K G) :=
  MonoidAlgebra.map_injective _ (ZMod.castHom (dvd_refl p) K).injective

/-- **Base change**: if `ab = 1 ≠ ba` in `𝔽_p[G]`, the same holds for the images in `K[G]`, for every
field `K` of characteristic `p`. -/
theorem baseChange_not_directlyFinite (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    {G : Type*} [Monoid G] {a b : MonoidAlgebra (ZMod p) G} (hab : a * b = 1) (hba : b * a ≠ 1) :
    baseChange p K G a * baseChange p K G b = 1 ∧ baseChange p K G b * baseChange p K G a ≠ 1 :=
  map_mul_eq_one_and_ne _ (baseChange_injective p K G) hab hba

end BaseChange

end Kaplansky.Algebra
