import OAI.GroupTheory.Hyperbolic.GraphMetric

/-!
# Integrals of 1-cochains along words in a Cayley graph

For a group `G` with generators `gen : S₀ → G`, a word `w : List (S₀ × Bool)` read from a base
point `g` visits `g, g·w₀, g·w₀w₁, …`. For `F : G → G → ℤ` we define the integral `wint F g w`
of `F` along this walk, and prove:

* every closed lazy path in the Cayley graph `mulCayley (range gen)` has a word with the same
  integral and at most the same length (`exists_path_word`);
* the integral is invariant under free reduction when `F` is antisymmetric;
* conjugation: `wint F g (c ++ w ++ c⁻¹) = wint F (g·c) w` when `w = 1` in `G`;
* hence every null word may be replaced by a cyclically reduced one (`exists_cyclically_reduced`).
-/

namespace Kaplansky.Hyperbolic

open OAI.Release075

section Words
variable {G : Type} [Group G] {S₀ : Type} (gen : S₀ → G)

/-- The value of a signed generator. -/
def eval (a : S₀ × Bool) : G := if a.2 then gen a.1 else (gen a.1)⁻¹

/-- The value of a word. -/
def value (w : List (S₀ × Bool)) : G := (w.map (eval gen)).prod

@[simp] lemma value_nil : value gen [] = 1 := rfl
@[simp] lemma value_cons (a : S₀ × Bool) (w : List (S₀ × Bool)) :
    value gen (a :: w) = eval gen a * value gen w := by simp [value]
@[simp] lemma value_append (u v : List (S₀ × Bool)) :
    value gen (u ++ v) = value gen u * value gen v := by simp [value]
@[simp] lemma value_singleton (a : S₀ × Bool) : value gen [a] = eval gen a := by simp [value]

lemma eval_flip (a : S₀ × Bool) : eval gen (a.1, !a.2) = (eval gen a)⁻¹ := by
  rcases a with ⟨s, b⟩
  cases b <;> simp [eval]

lemma value_invRev (w : List (S₀ × Bool)) : value gen (FreeGroup.invRev w) = (value gen w)⁻¹ := by
  induction w with
  | nil => simp [FreeGroup.invRev]
  | cons a w ih =>
    have h : FreeGroup.invRev (a :: w) = FreeGroup.invRev w ++ [(a.1, !a.2)] := by
      simp [FreeGroup.invRev]
    rw [h, value_append, ih, value_singleton, eval_flip, value_cons, mul_inv_rev]

/-- Free reduction does not change the value. -/
lemma value_red_step {L L' : List (S₀ × Bool)} (h : FreeGroup.Red.Step L L') :
    value gen L = value gen L' := by
  cases h with
  | @not L₁ L₂ x b =>
    rw [value_append, value_append, value_cons, value_cons]
    have : eval gen (x, !b) = (eval gen (x, b))⁻¹ := eval_flip gen (x, b)
    rw [this, mul_inv_cancel_left]

lemma value_red {L L' : List (S₀ × Bool)} (h : FreeGroup.Red L L') :
    value gen L = value gen L' := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (value_red_step gen hs)

/-- The integral of `F` along the walk reading `w` from `g`. -/
def wint (F : G → G → ℤ) : G → List (S₀ × Bool) → ℤ
  | _, [] => 0
  | g, a :: w => F g (g * eval gen a) + wint F (g * eval gen a) w

variable {gen}
variable (F : G → G → ℤ)

@[simp] lemma wint_nil (g : G) : wint gen F g [] = 0 := rfl
@[simp] lemma wint_cons (g : G) (a : S₀ × Bool) (w : List (S₀ × Bool)) :
    wint gen F g (a :: w) = F g (g * eval gen a) + wint gen F (g * eval gen a) w := rfl

lemma wint_append (g : G) (u v : List (S₀ × Bool)) :
    wint gen F g (u ++ v) = wint gen F g u + wint gen F (g * value gen u) v := by
  induction u generalizing g with
  | nil => simp
  | cons a u ih =>
    rw [List.cons_append, wint_cons, wint_cons, ih, value_cons, mul_assoc]
    ring

lemma wint_singleton (g : G) (a : S₀ × Bool) : wint gen F g [a] = F g (g * eval gen a) := by
  simp

/-- Left translation of the base point. -/
lemma wint_translate (g h : G) (w : List (S₀ × Bool)) :
    wint gen F (g * h) w = wint gen (fun x y => F (g * x) (g * y)) h w := by
  induction w generalizing h with
  | nil => rfl
  | cons a w ih =>
    rw [wint_cons, wint_cons, mul_assoc, ih]

/-- The integral as a sum over the steps of the walk. -/
lemma wint_eq_sum (g : G) (w : List (S₀ × Bool)) :
    wint gen F g w = ∑ i : Fin w.length,
      F (g * value gen (w.take i.val)) (g * value gen (w.take (i.val + 1))) := by
  induction w generalizing g with
  | nil => simp
  | cons a w ih =>
    rw [wint_cons, ih, List.length_cons, Fin.sum_univ_succ]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ, List.take_succ_cons, value_cons, mul_assoc]

variable {F}
variable (hF : ∀ x y, F y x = -F x y)
include hF

lemma wint_cancel (g : G) (x : S₀) (b : Bool) (w : List (S₀ × Bool)) :
    wint gen F g ((x, b) :: (x, !b) :: w) = wint gen F g w := by
  have he : eval gen (x, !b) = (eval gen (x, b))⁻¹ := eval_flip gen (x, b)
  rw [wint_cons, wint_cons, he, mul_inv_cancel_right, hF (g * eval gen (x, b)) g]
  ring

lemma wint_red_step {L L' : List (S₀ × Bool)} (h : FreeGroup.Red.Step L L') (g : G) :
    wint gen F g L = wint gen F g L' := by
  cases h with
  | @not L₁ L₂ x b =>
    rw [wint_append, wint_append, wint_cancel hF]

lemma wint_red {L L' : List (S₀ × Bool)} (h : FreeGroup.Red L L') (g : G) :
    wint gen F g L = wint gen F g L' := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (wint_red_step hF hs g)

lemma wint_append_invRev (g : G) (c : List (S₀ × Bool)) :
    wint gen F g (c ++ FreeGroup.invRev c) = 0 := by
  induction c generalizing g with
  | nil => simp [FreeGroup.invRev]
  | cons a c ih =>
    have h : a :: c ++ FreeGroup.invRev (a :: c) =
        a :: ((c ++ FreeGroup.invRev c) ++ [(a.1, !a.2)]) := by
      simp [FreeGroup.invRev]
    rw [h, wint_cons, wint_append, ih, value_append, value_invRev, mul_inv_cancel, mul_one,
      wint_singleton, eval_flip, mul_inv_cancel_right, hF (g * eval gen a) g]
    ring

/-- Conjugating a null word does not change its integral (after moving the base point). -/
lemma wint_conj (g : G) (c w : List (S₀ × Bool)) (hw : value gen w = 1) :
    wint gen F g (c ++ w ++ FreeGroup.invRev c) = wint gen F (g * value gen c) w := by
  have h1 := wint_append (gen := gen) F g (c ++ w) (FreeGroup.invRev c)
  have h2 := wint_append (gen := gen) F g c w
  have h3 := wint_append (gen := gen) F g c (FreeGroup.invRev c)
  rw [wint_append_invRev hF] at h3
  rw [value_append, hw, mul_one] at h1
  rw [h1, h2]
  linarith

omit hF in
lemma length_le_of_red {L L' : List (S₀ × Bool)} (h : FreeGroup.Red L L') :
    L'.length ≤ L.length := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih =>
    cases hs with
    | @not L₁ L₂ x b =>
      simp only [List.length_append, List.length_cons] at ih ⊢
      omega

variable [DecidableEq S₀]

/-- Every null word can be replaced by a cyclically reduced null word of at most the same
length, with the same integral from a suitable base point. -/
theorem exists_cyclically_reduced (g : G) (w : List (S₀ × Bool)) (hw : value gen w = 1) :
    ∃ (h : G) (r : List (S₀ × Bool)), FreeGroup.IsCyclicallyReduced r ∧ value gen r = 1 ∧
      r.length ≤ w.length ∧ wint gen F g w = wint gen F h r := by
  let R := FreeGroup.reduce w
  have hR : FreeGroup.Red w R := FreeGroup.reduce.red
  have hRed : FreeGroup.IsReduced R := FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem
  let c := FreeGroup.reduceCyclically.conjugator R
  let r := FreeGroup.reduceCyclically R
  have hdec : c ++ r ++ FreeGroup.invRev c = R :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically R
  have hvR : value gen R = 1 := (value_red gen hR).symm.trans hw
  have hvr : value gen r = 1 := by
    have h := congrArg (value gen) hdec
    rw [value_append, value_append, value_invRev, hvR] at h
    have h' : value gen c * value gen r = value gen c := by
      have := congrArg (· * value gen c) h
      simpa [mul_assoc] using this
    simpa using h'
  refine ⟨g * value gen c, r, FreeGroup.reduceCyclically.isCyclicallyReduced hRed, hvr, ?_, ?_⟩
  · have h1 := length_le_of_red hR
    have h2 := congrArg List.length hdec
    simp only [List.length_append] at h2
    omega
  · rw [wint_red hF hR g, ← hdec, wint_conj hF g c r hvr]

end Words

section Cayley
variable {G : Type} [Group G] {S₀ : Type} (gen : S₀ → G)

lemma adj_or_eq_eval (x : G) (a : S₀ × Bool) :
    x = x * eval gen a ∨ (SimpleGraph.mulCayley (Set.range gen)).Adj x (x * eval gen a) := by
  by_cases h : x = x * eval gen a
  · exact Or.inl h
  · right
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨h, gen a.1, ⟨a.1, rfl⟩, ?_⟩
    rcases a with ⟨s, b⟩
    cases b
    · right; simp [eval]
    · left; simp [eval]

lemma reachable_value (x : G) (u : List (S₀ × Bool)) :
    (SimpleGraph.mulCayley (Set.range gen)).Reachable x (x * value gen u) := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    rw [value_cons, ← mul_assoc]
    refine SimpleGraph.Reachable.trans ?_ (ih (x * eval gen a))
    rcases adj_or_eq_eval gen x a with h | h
    · rw [← h]
    · exact h.reachable

lemma connected_of_surjective (hsurj : ∀ g : G, ∃ u, value gen u = g) :
    (SimpleGraph.mulCayley (Set.range gen)).Connected := by
  refine SimpleGraph.Connected.mk ?_
  intro x y
  obtain ⟨u, hu⟩ := hsurj (x⁻¹ * y)
  have h := reachable_value gen x u
  rwa [hu, mul_inv_cancel_left] at h

lemma dist_eval_le (x : G) (a : S₀ × Bool) :
    (SimpleGraph.mulCayley (Set.range gen)).dist x (x * eval gen a) ≤ 1 := by
  rcases adj_or_eq_eval gen x a with h | h
  · rw [← h, SimpleGraph.dist_self]; exact zero_le_one
  · exact (SimpleGraph.dist_eq_one_iff_adj.mpr h).le

lemma dist_value_le (hX : (SimpleGraph.mulCayley (Set.range gen)).Connected)
    (x : G) (u : List (S₀ × Bool)) :
    (SimpleGraph.mulCayley (Set.range gen)).dist x (x * value gen u) ≤ u.length := by
  induction u generalizing x with
  | nil => simp
  | cons a u ih =>
    rw [value_cons, ← mul_assoc, List.length_cons]
    have h1 := dist_eval_le gen x a
    have h2 := ih (x * eval gen a)
    have h3 := hX.dist_triangle (u := x) (v := x * eval gen a) (w := x * eval gen a * value gen u)
    omega

/-- A lazy path in the Cayley graph is read by a word of at most the same length with the same
integral, for every `F` vanishing on the diagonal. -/
theorem exists_path_word (hX : (SimpleGraph.mulCayley (Set.range gen)).Connected) {x y : G}
    (p : Discrete.Path (Discrete.graphMetric (SimpleGraph.mulCayley (Set.range gen)) hX) x y) :
    ∃ w : List (S₀ × Bool), w.length ≤ p.length ∧ x * value gen w = y ∧
      ∀ F : G → G → ℤ, (∀ z, F z z = 0) → wint gen F x w = p.integral F := by
  have hprefix : ∀ n, n ≤ p.length → ∃ w : List (S₀ × Bool), w.length ≤ n ∧
      x * value gen w = p.point n ∧
      ∀ F : G → G → ℤ, (∀ z, F z z = 0) →
        wint gen F x w = ∑ i ∈ Finset.range n, F (p.point i) (p.point (i + 1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨[], by simp, by simpa using p.zero.symm, fun F _ => by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨u, hul, hux, huF⟩ := ih (by omega)
      by_cases he : p.point n = p.point (n + 1)
      · refine ⟨u, by omega, hux.trans he, fun F hF0 => ?_⟩
        rw [huF F hF0, Finset.sum_range_succ, ← he, hF0, add_zero]
      · have hstep : (SimpleGraph.mulCayley (Set.range gen)).dist (p.point n) (p.point (n + 1)) ≤ 1 :=
          p.step n (by omega)
        have hadj : (SimpleGraph.mulCayley (Set.range gen)).Adj (p.point n) (p.point (n + 1)) := by
          apply SimpleGraph.dist_eq_one_iff_adj.mp
          have hpos := hX.pos_dist_of_ne he
          omega
        obtain ⟨_, g, ⟨s, rfl⟩, hg⟩ := (SimpleGraph.mulCayley_adj' _ _ _).mp hadj
        have ha : ∃ a : S₀ × Bool, p.point n * eval gen a = p.point (n + 1) := by
          rcases hg with h1 | h2
          · exact ⟨(s, true), by simpa [eval] using h1⟩
          · refine ⟨(s, false), ?_⟩
            rw [h2]
            simp [eval]
        obtain ⟨a, ha⟩ := ha
        refine ⟨u ++ [a], by simp; omega, ?_, fun F hF0 => ?_⟩
        · rw [value_append, value_singleton, ← mul_assoc, hux, ha]
        · rw [wint_append, wint_singleton, huF F hF0, hux, ha, Finset.sum_range_succ]
  obtain ⟨w, hw, hwx, hwF⟩ := hprefix p.length le_rfl
  exact ⟨w, hw, by simpa using hwx, fun F hF0 => hwF F hF0⟩

end Cayley

end Kaplansky.Hyperbolic
