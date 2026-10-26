import Kaplansky.Exclusion.Basic
import OAI.Algebra.GroupRing.Main

/-!
# OpenAI's sampled graph is pattern-free

For OpenAI's sample `graph rep r` (Result 196), with signed labels and roots `x, y`, the facts
proved by OpenAI (`SampleGraph.degree`, `girth`, `diameter`, and the avoidance of bounded systems
from `SampleGraph.exists_avoiding`) give `Exclusion.PatternFree` with
`ε = PathSystem.ε = 1/2467200`, `d = TypedDiameter.D₀`, `λ = 400` (so `D₀ + 4λ + 8` is OpenAI's
closure constant `ClosedWords.D`), at scale `L = GirthAsymptotics.L (size rep) ≥ 3`.
-/

namespace Kaplansky.Main

open OAI.TorsionFreeZeroDivisors
open SampleGraph GirthAsymptotics TypedGraphs ActualPatternEvent

variable {rep : ℕ} (r : Match rep) (x : VA rep) (y : VB rep)

/-- The two roots of the model. -/
def isRoot (v : VA rep ⊕ VB rep) : Prop := v = Sum.inl x ∨ v = Sum.inr y

lemma signed_immersed (d e : DA rep ⊕ DB rep)
    (ho : (graph rep r).origin d = (graph rep r).origin e)
    (hl : ConcreteTorsion.signedLabels rep d = ConcreteTorsion.signedLabels rep e) : d = e := by
  apply SampleGraph.immersed rep r d e ho
  have := congrArg Types.signedLetter hl
  simpa [ConcreteTorsion.signedLabels] using this

lemma signed_inverse (t : Types.Signed) :
    Types.signedLetter (WordPairing.inverseLetter t) = Types.inverse (Types.signedLetter t) := by
  simp [Types.inverse, WordPairing.inverseLetter]

/-- A generic bounded system for the sample is one of OpenAI's bounded systems. -/
def toOAI {Bnd K I : ℕ}
    (s : Exclusion.GBoundedSystem (graph rep r) (ConcreteTorsion.signedLabels rep)
      WordPairing.inverseLetter (isRoot x y) Bnd K I (L (size rep)) PathSystem.ε) :
    BoundedSystem Bnd K I rep r x y where
  P := s.P
  E := s.E
  fP := s.fP
  fE := s.fE
  paths := s.paths
  nonempty := s.nonempty
  root := s.root
  path_bound := s.path_bound
  comparison_bound := s.comparison_bound
  path_chain := s.path_chain
  cyclic_chain := s.cyclic_chain
  length_le := s.length_le
  length_ge := s.length_ge
  comparisons := s.comparisons
  lower := s.lower
  upper := s.upper
  lower_eq := s.lower_eq
  upper_eq := s.upper_eq
  lower_le := s.lower_le
  upper_le := s.upper_le
  reduced := s.reduced
  unpaired_le := s.unpaired_le
  rootA := by
    intro z hz
    obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hz
    have he' : (graph rep r).origin ((s.paths p).head (s.nonempty p)) = Sum.inl z := he
    rcases s.root_start p hp with h | h
    · rw [he'] at h; exact Sum.inl.inj h
    · rw [he'] at h; cases h
  rootB := by
    intro z hz
    obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hz
    have he' : (graph rep r).origin ((s.paths p).head (s.nonempty p)) = Sum.inr z := he
    rcases s.root_start p hp with h | h
    · rw [he'] at h; cases h
    · rw [he'] at h; exact Sum.inr.inj h
  compatible := by
    intro p e he
    have h := congrArg Types.signedLetter (s.compatible p e he)
    simp only [ConcreteTorsion.signedLabels, Function.comp_apply, Equiv.apply_symm_apply] at h
    rw [h]
    split_ifs
    · rw [signed_inverse, Equiv.apply_symm_apply]
    · rw [Equiv.apply_symm_apply]

lemma closureConst_eq : Exclusion.closureConst (TypedDiameter.D₀ : ℝ) 400 = ClosedWords.D := by
  unfold Exclusion.closureConst ClosedWords.D
  rw [show (TypedDiameter.D₀ : ℝ) + 4 * 400 + 8 = ((TypedDiameter.D₀ + 1608 : ℕ) : ℝ) by
    push_cast; ring]
  exact Nat.ceil_natCast _

lemma eps_le_one : PathSystem.ε ≤ 1 :=
  (min_le_left _ _).trans (by norm_num)

lemma one_le_D₀ : 1 ≤ TypedDiameter.D₀ := by
  unfold TypedDiameter.D₀
  have := Nat.zero_le TypedDiameter.A₀
  omega

/-- `log₂ (2n) ≤ 400·L(n)` once `L(n) ≥ 1`, with `L(n) = ⌊ln n / 100⌋`. -/
lemma logb_le (n : ℕ) (hL : 1 ≤ L n) :
    Real.logb 2 ((2 * n : ℕ) : ℝ) ≤ 400 * (L n : ℝ) := by
  have hLpos : (0 : ℝ) < L n := by exact_mod_cast hL
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [L] at hL
    · exact h
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hfl : Real.log n / 100 < (L n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [Real.logb, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hnr.ne',
    div_le_iff₀ (by linarith)]
  have hln : Real.log n < 100 * ((L n : ℝ) + 1) := by linarith
  have hL1 : (1 : ℝ) ≤ L n := by exact_mod_cast hL
  have hlog2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hp := mul_pos (sub_pos.mpr hlog2) hLpos
  nlinarith

variable {r x y}

/-- **OpenAI's sample is pattern-free.** -/
theorem patternFree (hL : 3 ≤ L (size rep)) (hd : GraphSample.Diameters rep r)
    (hsample : r ∈ samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D)
      (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) :
    Exclusion.PatternFree (graph rep r) (ConcreteTorsion.signedLabels rep)
      WordPairing.inverseLetter (isRoot x y) PathSystem.ε (TypedDiameter.D₀ : ℝ) 400
      (L (size rep)) where
  inv_involutive := WordPairing.inverseLetter_involutive
  inv_ne a := by
    rcases a with ⟨g, b⟩
    cases b <;> simp [WordPairing.inverseLetter]
  label_reverse := ConcreteTorsion.signedLabels_reverse rep r
  immersed := signed_immersed r
  eps_pos := PathSystem.ε_pos
  eps_le := eps_le_one
  one_le_d := by exact_mod_cast one_le_D₀
  one_le_lam := by norm_num
  scale := hL
  degree v := by
    have h := (by norm_num : 7 ≤ 129).trans (SampleGraph.degree rep r v)
    convert h
  girth := Exclusion.girth_of_egirth (graph rep r) (L (size rep)) (SampleGraph.girth rep r hsample)
  diameter a b h := by exact_mod_cast SampleGraph.diameter rep r hd a b h
  size := by
    rw [SampleGraph.card_vertices]
    exact logb_le _ (by omega)
  avoid := by
    rw [closureConst_eq, Exclusion.two_pairs]
    exact ⟨fun s => havoid.false (toOAI r x y s)⟩

end Kaplansky.Main
