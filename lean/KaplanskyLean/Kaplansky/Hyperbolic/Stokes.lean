import Kaplansky.Hyperbolic.WordIntegral
import Kaplansky.Hyperbolic.WordHyperbolic

/-!
# Cone decompositions give a linear cochain bound

A *cone decomposition* of a null word `w` is the metric-free output of the free-outer-disk
exclusion: finitely many occurrences `o`, a permutation `σ` of them, positions `pos o` with
`pos (σ o) = pos o · (signed generator)`, cone points `cone o` constant along `σ`, each position
within word length `ℓ` of its cone point, such that for every antisymmetric `F` the integral of `F`
along `w` equals `-Σ_o F (pos o) (pos (σ o))`.

Telescoping through the cone points (discrete Stokes) bounds such a sum by `2ℓ · #occurrences`,
using `|F x y + F y c + F c x| ≤ 2 d(y,c)` for `F = form o a T` and `d(x,y) ≤ 1`.
If every cyclically reduced null word has a cone decomposition with `#occurrences ≤ K·|w|`,
the Cayley graph satisfies `CochainBound ⌈2ℓK⌉`, hence the group is word-hyperbolic.
-/

namespace Kaplansky.Hyperbolic

open OAI.Release075

section TriangleBound
variable {V : Type} (M : Discrete.Metric V)

/-- The generalized triangle bound: one short side, the third vertex arbitrary. -/
theorem form_cone_bound (o a x y c : V) (T : ℕ) (hxy : M.dist x y ≤ 1) :
    |M.form o a T x y + M.form o a T y c + M.form o a T c x| ≤ 2 * (M.dist y c : ℤ) := by
  have hτ₁ : |M.tent o T x - M.tent o T y| ≤ 1 :=
    (M.tent_lipschitz o T x y).trans (by exact_mod_cast hxy)
  have hδ₁ : |(M.dist a y : ℤ) - M.dist a c| ≤ M.dist y c := M.int_dist_sub_le a y c
  have hτ₂ : |M.tent o T c - M.tent o T y| ≤ M.dist y c := by
    have h := M.tent_lipschitz o T c y
    rwa [M.symm c y] at h
  have hδ₂ : |(M.dist a x : ℤ) - M.dist a y| ≤ 1 :=
    (M.int_dist_sub_le a x y).trans (by exact_mod_cast hxy)
  have he : M.form o a T x y + M.form o a T y c + M.form o a T c x =
      (M.tent o T x - M.tent o T y) * ((M.dist a y : ℤ) - M.dist a c) +
      (M.tent o T c - M.tent o T y) * ((M.dist a x : ℤ) - M.dist a y) := by
    unfold Discrete.Metric.form
    ring
  rw [he]
  have hd : (0 : ℤ) ≤ M.dist y c := Nat.cast_nonneg _
  calc
    _ ≤ |(M.tent o T x - M.tent o T y) * ((M.dist a y : ℤ) - M.dist a c)| +
        |(M.tent o T c - M.tent o T y) * ((M.dist a x : ℤ) - M.dist a y)| := abs_add_le _ _
    _ ≤ 1 * (M.dist y c : ℤ) + (M.dist y c : ℤ) * 1 := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hτ₁ hδ₁ (abs_nonneg _) (by norm_num))
        (mul_le_mul hτ₂ hδ₂ (abs_nonneg _) hd)
    _ = 2 * (M.dist y c : ℤ) := by ring

end TriangleBound

section Cones
variable {G : Type} [Group G] {S₀ : Type} (gen : S₀ → G)

/-- A metric-free cone decomposition of the word `w`, with cone radius `ℓ`. -/
structure ConeDecomposition (ℓ : ℕ) (w : List (S₀ × Bool)) where
  O : Type
  [fO : Fintype O]
  σ : Equiv.Perm O
  pos : O → G
  cone : O → G
  step : ∀ o, ∃ a : S₀ × Bool, pos (σ o) = pos o * eval gen a
  cone_next : ∀ o, cone (σ o) = cone o
  near : ∀ o, ∃ u : List (S₀ × Bool), u.length ≤ ℓ ∧ pos o = cone o * value gen u
  integral : ∀ F : G → G → ℤ, (∀ x y, F y x = -F x y) →
    wint gen F 1 w = -∑ o, F (pos o) (pos (σ o))

attribute [instance] ConeDecomposition.fO

/-- Discrete Stokes through the cone points. -/
theorem cone_sum_bound (hX : (SimpleGraph.mulCayley (Set.range gen)).Connected) {ℓ : ℕ} {w : List (S₀ × Bool)} (cd : ConeDecomposition gen ℓ w)
    (g o a : G) (T : ℕ) :
    |∑ x, (Discrete.graphMetric (SimpleGraph.mulCayley (Set.range gen)) hX).form o a T (g * cd.pos x) (g * cd.pos (cd.σ x))| ≤
      2 * ℓ * Fintype.card cd.O := by
  set M := Discrete.graphMetric (SimpleGraph.mulCayley (Set.range gen)) hX
  set F := M.form o a T
  let P : cd.O → G := fun x => g * cd.pos x
  let Q : cd.O → G := fun x => g * cd.cone x
  have htel : ∑ x, F (P x) (P (cd.σ x)) =
      ∑ x, (F (P x) (P (cd.σ x)) + F (P (cd.σ x)) (Q x) + F (Q x) (P x)) := by
    have h1 : ∑ x, F (P (cd.σ x)) (Q x) = ∑ x, F (P x) (Q x) := by
      have := Equiv.sum_comp cd.σ (fun x => F (P x) (Q x))
      simpa only [Q, cd.cone_next] using this
    have h2 : ∑ x, F (Q x) (P x) = -∑ x, F (P x) (Q x) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => M.form_flip o a T (P x) (Q x)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2]
    ring
  have hterm : ∀ x, |F (P x) (P (cd.σ x)) + F (P (cd.σ x)) (Q x) + F (Q x) (P x)| ≤ 2 * ℓ := by
    intro x
    have hstep : M.dist (P x) (P (cd.σ x)) ≤ 1 := by
      obtain ⟨b, hb⟩ := cd.step x
      change (SimpleGraph.mulCayley (Set.range gen)).dist _ _ ≤ 1
      simp only [P, hb, ← mul_assoc]
      exact dist_eval_le gen _ b
    have hnear : M.dist (P (cd.σ x)) (Q x) ≤ ℓ := by
      obtain ⟨u, hu, hpos⟩ := cd.near (cd.σ x)
      change (SimpleGraph.mulCayley (Set.range gen)).dist _ _ ≤ ℓ
      rw [SimpleGraph.dist_comm]
      have hQ : Q x = g * cd.cone (cd.σ x) := by simp [Q, cd.cone_next]
      rw [hQ]
      simp only [P, hpos, ← mul_assoc]
      exact (dist_value_le gen hX _ u).trans hu
    have hb : |F (P x) (P (cd.σ x)) + F (P (cd.σ x)) (Q x) + F (Q x) (P x)| ≤
        2 * (M.dist (P (cd.σ x)) (Q x) : ℤ) :=
      form_cone_bound M o a (P x) (P (cd.σ x)) (Q x) T hstep
    have hn : (M.dist (P (cd.σ x)) (Q x) : ℤ) ≤ ℓ := by exact_mod_cast hnear
    linarith
  rw [htel]
  calc
    _ ≤ ∑ x, |F (P x) (P (cd.σ x)) + F (P (cd.σ x)) (Q x) + F (Q x) (P x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : cd.O, (2 * ℓ : ℤ) := Finset.sum_le_sum fun x _ => hterm x
    _ = 2 * ℓ * Fintype.card cd.O := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

variable [DecidableEq S₀]

/-- Cone decompositions of linear size for all cyclically reduced null words give a linear
cochain bound for the Cayley graph. -/
theorem cochainBound_of_cones (hX : (SimpleGraph.mulCayley (Set.range gen)).Connected) (ℓ : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hcd : ∀ w : List (S₀ × Bool), w ≠ [] → FreeGroup.IsCyclicallyReduced w →
      value gen w = 1 →
      ∃ cd : ConeDecomposition gen ℓ w, (Fintype.card cd.O : ℝ) ≤ K * w.length) :
    Discrete.CochainBound (Discrete.graphMetric (SimpleGraph.mulCayley (Set.range gen)) hX) ⌈2 * ℓ * K⌉₊ := by
  intro o a x T p
  let M := Discrete.graphMetric (SimpleGraph.mulCayley (Set.range gen)) hX
  let F := M.form o a T
  have hanti : ∀ y z, F z y = -F y z := fun y z => M.form_flip o a T y z
  obtain ⟨w, hwl, hwx, hwF⟩ := exists_path_word gen hX p
  have hw1 : value gen w = 1 := by
    have : x * value gen w = x * 1 := by rw [hwx, mul_one]
    exact mul_left_cancel this
  rw [← hwF F (fun z => M.form_self o a z T)]
  obtain ⟨h, r, hcr, hr1, hrl, hint⟩ := exists_cyclically_reduced hanti x w hw1
  rw [hint]
  by_cases hrn : r = []
  · subst hrn
    simp only [wint_nil, abs_zero]
    positivity
  obtain ⟨cd, hcard⟩ := hcd r hrn hcr hr1
  -- move the base point to 1
  have htr : wint gen F h r = wint gen (fun y z => F (h * y) (h * z)) 1 r := by
    rw [← wint_translate F h 1 r, mul_one]
  rw [htr, cd.integral (fun y z => F (h * y) (h * z)) (fun y z => hanti (h * y) (h * z)),
    abs_neg]
  have hb := cone_sum_bound gen hX cd h o a T
  have hcardr : (Fintype.card cd.O : ℝ) ≤ K * p.length := by
    have : (r.length : ℝ) ≤ p.length := by exact_mod_cast hrl.trans hwl
    nlinarith [mul_le_mul_of_nonneg_left this hK]
  have hfinal : (2 * ℓ * Fintype.card cd.O : ℝ) ≤ (⌈2 * ℓ * K⌉₊ : ℝ) * p.length := by
    have hc := Nat.le_ceil (2 * ℓ * K)
    have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    have hp : (0 : ℝ) ≤ p.length := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hcardr (by positivity : (0:ℝ) ≤ 2 * ℓ),
      mul_le_mul_of_nonneg_right hc hp]
  have hfinalZ : (2 * ℓ * Fintype.card cd.O : ℤ) ≤ (⌈2 * ℓ * K⌉₊ : ℤ) * p.length := by
    exact_mod_cast hfinal
  exact hb.trans hfinalZ

/-- Word-hyperbolicity from linear cone decompositions. -/
theorem wordHyperbolic_of_cones [Finite S₀] (hsurj : ∀ g : G, ∃ u, value gen u = g) (ℓ : ℕ)
    (K : ℝ) (hK : 0 ≤ K)
    (hcd : ∀ w : List (S₀ × Bool), w ≠ [] → FreeGroup.IsCyclicallyReduced w →
      value gen w = 1 →
      ∃ cd : ConeDecomposition gen ℓ w, (Fintype.card cd.O : ℝ) ≤ K * w.length) :
    Kaplansky.WordHyperbolic G := by
  have hX : (SimpleGraph.mulCayley (Set.range gen)).Connected := connected_of_surjective gen hsurj
  exact wordHyperbolic_of_cochainBound (Set.range gen) (Set.finite_range gen) hX
    (cochainBound_of_cones gen hX ℓ K hK hcd)

end Cones

end Kaplansky.Hyperbolic
