import Mathlib

/-!
# Small counting and limit lemmas shared by the model instances
-/

namespace Kaplansky.Random

open Filter Topology

theorem card_subtype_sum {X Y : Type} [Fintype X] [Fintype Y] (P : X ⊕ Y → Prop)
    [DecidablePred P] :
    Fintype.card {z // P z} = Fintype.card {x // P (.inl x)} + Fintype.card {y // P (.inr y)} := by
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_sum_type]

theorem card_subtype_of_false {X : Type} [Fintype X] (P : X → Prop) [DecidablePred P]
    (h : ∀ x, ¬P x) : Fintype.card {x // P x} = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun x => h x.1 x.2⟩

/-- `(P m + a) / (Q m + b) → P / Q`. -/
theorem affine_ratio (P Q a b : ℝ) (hQ : Q ≠ 0) :
    Tendsto (fun m : ℕ => (P * m + a) / (Q * m + b)) atTop (𝓝 (P / Q)) := by
  have ha := tendsto_const_div_atTop_nhds_zero_nat a
  have hb := tendsto_const_div_atTop_nhds_zero_nat b
  have h := ((tendsto_const_nhds (x := P)).add ha).div ((tendsto_const_nhds (x := Q)).add hb)
    (by simpa using hQ)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  simp only [Pi.div_apply]
  rw [← mul_div_mul_left (P * m + a) (Q * m + b) (inv_ne_zero hm')]
  congr 1 <;> field_simp

/-- Shifting the index does not change a limit along `atTop`. -/
theorem tendsto_shift {f : ℕ → ℝ} {l : ℝ} (k : ℕ) (h : Tendsto f atTop (𝓝 l)) :
    Tendsto (fun m => f (m + k)) atTop (𝓝 l) :=
  h.comp (tendsto_add_atTop_nat k)

end Kaplansky.Random
