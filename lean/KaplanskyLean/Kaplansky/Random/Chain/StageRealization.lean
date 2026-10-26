import Kaplansky.Random.Chain.StageBlocks
import OAI.Algebra.GroupRing.StageRealization

/-!
# Fork of `OAI/Algebra/GroupRing/StageRealization.lean` (and the typed part of `TypeWeights`)

The chain realization count for one fixed word, now over the alphabet `M.α`, on a side whose
vertices carry colours (`col : TV → Col`) and whose ports are coloured letters (`cout col out`).

New ingredient (paper Prop 6.6 and Prop 7.9(c)): a word `w` on the chains together with a
colouring `κ` of the *marked* vertices determines a colour at every vertex of the subdivided
chain graph (`vcol`): colours flip along every edge.  The chain pattern is labelled by
coloured letters `clabel w κ`, so the allowed images of an internal vertex lie in one colour
class and the per-colour turn table `n·p·J` applies there.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors

noncomputable section

namespace ChainRealization
open scoped Classical BigOperators
open ChainSubdivision
open OAI.TorsionFreeZeroDivisors.ChainRealization (pin pin_internal edges_card)
variable (M : Model) {C V : Type*} [Fintype C] [Fintype V]
variable (len : C → ℕ) (first last : C → V)

/-- Uncoloured letters on the subdivided chains (OAI `ChainRealization.label`). -/
def label (w : C → ℤ → M.α) (d : Dart len) : M.α :=
  if d.2 then M.inv (w d.1.1 d.1.2.val) else w d.1.1 d.1.2.val

omit [Fintype C] [Fintype V] in
@[simp] theorem label_reverse (w : C → ℤ → M.α) (d : Dart len) :
    label M len w ((graph len first last).reverse d) = M.inv (label M len w d) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp [label, M.inv_inv]

omit [Fintype C] [Fintype V] in
@[simp] theorem label_back (w : C → ℤ → M.α) (v : Interior len) :
    label M len w (back len v) = M.inv (w v.1 v.2.val) := rfl

omit [Fintype C] [Fintype V] in
@[simp] theorem label_front (w : C → ℤ → M.α) (v : Interior len) :
    label M len w (front len v) = w v.1 ((v.2.val : ℤ) + 1) := by
  simp [label, front, Nat.cast_add]

variable {Col : Type} (flip : Col → Col)

/-- Colours of all vertices of the subdivided chain graph, forced by a colouring of the
marked vertices: colours flip along every edge. -/
def vcol (κ : V → Col) : Vertex len (V := V) → Col
  | .inl v => κ v
  | .inr v => flip^[v.2.val + 1] (κ (first v.1))

/-- Coloured chain letters. -/
def clabel (w : C → ℤ → M.α) (κ : V → Col) (d : Dart len) : M.α × Col :=
  (label M len w d, vcol len first flip κ ((graph len first last).origin d))

omit [Fintype C] [Fintype V] in
theorem clabel_injective (w : C → ℤ → M.α) (κ : V → Col)
    (himm : Function.Injective (fun d => ((graph len first last).origin d, label M len w d))) :
    Function.Injective (fun d => ((graph len first last).origin d,
      clabel M len first last flip w κ d)) := by
  intro d e h
  apply himm
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x => x.2.1) h
  exact Prod.ext h1 h2

omit [Fintype C] [Fintype V] in
/-- Literal internal turn weight. -/
theorem internal_weight (w : C → ℤ → M.α)
    (himm : Function.Injective (fun d => ((graph len first last).origin d, label M len w d)))
    (v : Interior len) :
    M.J (label M len w (back len v)) (label M len w (front len v)) =
      M.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ) + 1)) := by
  have hn : label M len w (back len v) ≠ label M len w (front len v) := by
    intro he
    exact back_ne_front len v (himm (Prod.ext (by simp) he))
  rw [label_back, label_front] at hn ⊢
  unfold Alphabet.weight
  rw [if_neg]
  intro he
  exact hn (by rw [he])

def turnProduct (w : C → ℤ → M.α) : ℝ :=
  ∏ v : Interior len, M.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ) + 1))

/-- Vertex-assignment cost (OAI `ChainRealization.cost`). -/
def cost {TV : Type*} (pp : V → Option TV) (n p : ℝ)
    (w : C → ℤ → M.α) : Vertex len (V := V) → ℝ
  | .inl v => if pp v = none then n else 1
  | .inr v => n * p * M.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ) + 1))

theorem cost_product {TV : Type*} (pp : V → Option TV) (n p : ℝ)
    (w : C → ℤ → M.α) :
    (∏ v, cost M len pp n p w v) =
      n ^ ((Finset.univ.filter fun v => pp v = none).card + ∑ c, (len c - 1)) *
        p ^ (∑ c, (len c - 1)) * turnProduct M len w := by
  rw [Fintype.prod_sum_type]
  simp only [cost, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    card_interiors, Finset.prod_ite, Finset.prod_const, one_pow, mul_one, pow_add,
    turnProduct]
  ring

omit [Fintype V] in
/-- Allowed images are bounded by the coloured type table. -/
theorem allowed_cost {TV : Type} [Fintype TV] [Fintype Col] [DecidableEq Col]
    (col : TV → Col) (out : TV → Finset M.α) (pp : V → Option TV)
    (n p : ℝ) (hp : 0 ≤ p) (w : C → ℤ → M.α) (κ : V → Col)
    (himm : Function.Injective (fun d => ((graph len first last).origin d, label M len w d)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ c a b, a ≠ b →
      (Fintype.card {x : TV // col x = c ∧ a ∈ out x ∧ b ∈ out x} : ℝ) ≤ n * p * M.J a b) :
    ∀ v, ((StageRealization.allowed (graph len first last)
      (clabel M len first last flip w κ) (cout col out) (pin len pp) v).card : ℝ) ≤
        cost M len pp n p w v := by
  have hn0 : 0 ≤ n := le_trans (Nat.cast_nonneg _) hn
  intro v
  cases v with
  | inl v =>
    dsimp [cost]
    split_ifs with hpp
    · exact (Nat.cast_le.mpr (StageRealization.allowed_card_le _ _ _ _ _)).trans hn
    · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hpp
      exact_mod_cast StageRealization.pinned_card_le (graph len first last)
        (clabel M len first last flip w κ) (cout col out) (pin len pp) (.inl v) x hx
  | inr v =>
    have hcimm := clabel_injective M len first last flip w κ himm
    have hn' : clabel M len first last flip w κ (back len v) ≠
        clabel M len first last flip w κ (front len v) := by
      intro he
      exact back_ne_front len v (hcimm (Prod.ext (by simp) he))
    have h := StageRealization.allowed_turn_table (graph len first last)
      (clabel M len first last flip w κ) (cout col out) (pin len pp) (.inr v)
      (back len v) (front len v) (back_origin len first last v) (front_origin len first last v) hn'
      (fun t u => if t.1 = u.1 then 0 else n * p * M.J t.1 u.1) (by
        intro t u htu
        by_cases h1 : t.1 = u.1
        · rw [if_pos h1]
          have h2 : t.2 ≠ u.2 := fun h2 => htu (Prod.ext h1 h2)
          have : IsEmpty {x : TV // t ∈ cout col out x ∧ u ∈ cout col out x} :=
            ⟨fun x => h2 ((mem_cout.mp x.property.1).2.trans (mem_cout.mp x.property.2).2.symm)⟩
          have hz : Fintype.card {x : TV // t ∈ cout col out x ∧ u ∈ cout col out x} = 0 :=
            Fintype.card_eq_zero
          have h0 : (Fintype.card {x : TV // t ∈ cout col out x ∧ u ∈ cout col out x} : ℝ) ≤ 0 := by
            rw [hz]; simp
          convert h0
        · rw [if_neg h1]
          have hle : Fintype.card {x : TV // t ∈ cout col out x ∧ u ∈ cout col out x} ≤
              Fintype.card {x : TV // col x = t.2 ∧ t.1 ∈ out x ∧ u.1 ∈ out x} := by
            apply Fintype.card_le_of_injective
              (fun x => ⟨x.val, by
                have ht := mem_cout.mp x.property.1
                have hu := mem_cout.mp x.property.2
                exact ⟨ht.2.symm, ht.1, hu.1⟩⟩)
            intro x y hxy
            exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
          have hfin := (Nat.cast_le.mpr hle).trans (htable _ _ _ h1)
          convert hfin)
    have hne : (clabel M len first last flip w κ (back len v)).1 ≠
        (clabel M len first last flip w κ (front len v)).1 := by
      intro he
      have himm' := himm (a₁ := back len v) (a₂ := front len v)
      exact back_ne_front len v (himm' (Prod.ext (by simp) he))
    rw [if_neg hne] at h
    have hw := internal_weight M len first last w himm v
    simp only [clabel] at h
    rw [hw] at h
    exact h

/-- Exact finite first moment for one coloured chain pattern. -/
theorem fixed_label_bound {TV : Type} [Fintype TV] [Fintype Col] [DecidableEq Col]
    (col : TV → Col) (out : TV → Finset M.α) (pp : V → Option TV)
    (n p : ℝ) (hp : 0 ≤ p) (w : C → ℤ → M.α) (κ : V → Col)
    (himm : Function.Injective (fun d => ((graph len first last).origin d, label M len w d)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ c a b, a ≠ b →
      (Fintype.card {x : TV // col x = c ∧ a ∈ out x ∧ b ∈ out x} : ℝ) ≤ n * p * M.J a b)
    (N d R : ℕ) (h2 : 2 ≤ d) (hR : 0 < R)
    (hd : ∀ v, Nat.card {e : PatternEmbeddings.Dart (cout col out) //
      PatternEmbeddings.origin (cout col out) e = v} ≤ d)
    (hsize : ∀ x : PatternEmbeddings.Dart (cout col out),
      R + (∑ c, len c) + 4 * d ^ (2 * N + 1) ≤
        Nat.card {e : PatternEmbeddings.Dart (cout col out) //
          PatternEmbeddings.label (cout col out) e = PatternEmbeddings.label (cout col out) x})
    (hΩ : (ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label (cout col out)) (bar := cbar M.inv flip)
      (PatternEmbeddings.origin (cout col out)) N ∅).Nonempty) :
    ((∑ r ∈ ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label (cout col out)) (bar := cbar M.inv flip)
      (PatternEmbeddings.origin (cout col out)) N ∅,
        StageRealization.realizations (graph len first last)
          (clabel M len first last flip w κ) (cout col out)
          (pin len pp) (cbar M.inv flip) r : ℕ) : ℝ) /
        (ConditionedMatchings.Matching.conditioned
          (label := PatternEmbeddings.label (cout col out)) (bar := cbar M.inv flip)
          (PatternEmbeddings.origin (cout col out)) N ∅).card ≤
      (n ^ ((Finset.univ.filter fun v => pp v = none).card + ∑ c, (len c - 1)) *
        p ^ (∑ c, (len c - 1)) * turnProduct M len w) / (R : ℝ) ^ (∑ c, len c) := by
  have hbar : ∀ t, cbar M.inv flip t ≠ t := fun t h => M.inv_ne t.1 (congrArg Prod.fst h)
  have h := StageRealization.fixed_label_bound (graph len first last)
    (clabel M len first last flip w κ) (cout col out) (pin len pp) (cbar M.inv flip) hbar
    (clabel_injective M len first last flip w κ himm) N d R h2 hR hd
    (by intro x; rw [edges_card]; exact hsize x) ?_ (cost M len pp n p w)
    (allowed_cost M len first last flip col out pp n p hp w κ himm hn htable)
  · rw [cost_product, edges_card] at h
    convert h
  · convert hΩ using 2

end ChainRealization

namespace ChainWeights
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
open OAI.TorsionFreeZeroDivisors.ChainWeights
variable (M : Model) {C : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len : C → ℕ)

def atTurn (w : C → ℤ → M.α) (x : Position len) : ℝ :=
  M.weight (w x.1 x.2.val) (w x.1 (x.2.val + 1))
def chainProduct (w : C → ℤ → M.α) : ℝ := ∏ x ∈ turns len, atTurn M len w x

omit [Fintype C] in
theorem wordWeight_pred (h : ℕ) (W : Fin h → M.α) :
    M.wordWeight h W = ∏ k : Fin (h - 1), M.weight (W ⟨k.val, by omega⟩) (W ⟨k.val + 1, by omega⟩) := by
  cases h with
  | zero => simp [Alphabet.wordWeight]
  | succ h => exact M.wordWeight_eq_product h W

theorem turn_product (w : C → ℤ → M.α) :
    (∏ x : BlockTurn s len, atTurn M len w (turnPoint s hs len x)) =
      ∏ i : Underlying s len, M.wordWeight (height s len i) (word s len w i) := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [wordWeight_pred]
  apply Finset.prod_congr rfl
  intro k _
  change M.weight (w i.1 (firstCoordinate s len i k).val)
    (w i.1 ((firstCoordinate s len i k).val + 1)) =
    M.weight (w i.1 ((k.val : ℤ) + lower s len i))
      (w i.1 (((k.val + 1 : ℕ) : ℤ) + lower s len i))
  rw [firstCoordinate_val]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 2; ring

include hs in
theorem chain_le_blocks (w : C → ℤ → M.α) :
    chainProduct M len w ≤
      ∏ i : Underlying s len, M.wordWeight (height s len i) (word s len w i) := by
  let S := Finset.univ.image (turnPoint s hs len)
  have hS : S ⊆ turns len := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact turnPoint_mem s hs len y
  calc
    chainProduct M len w ≤ ∏ x ∈ S, atTurn M len w x :=
      Finset.prod_le_prod_of_subset_of_le_one₀ hS (fun x _ => M.weight_nonneg _ _)
        (fun x _ _ => M.weight_le_one _ _)
    _ = ∏ x : BlockTurn s len, atTurn M len w (turnPoint s hs len x) := by
      exact Finset.prod_image (fun _ _ _ _ he => turnPoint_injective s hs len he)
    _ = _ := turn_product M s hs len w

omit [Fintype C] in
theorem bin_weight_upper {h : ℕ} {d : ℤ} {W : Fin h → M.α}
    (hW : W ∈ M.binWords h d) : M.wordWeight h W ≤ Real.exp (-(d : ℝ)) := by
  obtain ⟨hp, he⟩ := M.mem_binWords.mp hW
  have hf := Int.floor_le (-Real.log (M.wordWeight h W))
  rw [he] at hf
  calc
    M.wordWeight h W = Real.exp (Real.log (M.wordWeight h W)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

include hs in
theorem chain_bin_bound (w : C → ℤ → M.α) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ M.binWords (height s len i) (d i)) :
    chainProduct M len w ≤ Real.exp (-∑ i, (d i : ℝ)) := by
  refine (chain_le_blocks M s hs len w).trans ?_
  calc
    (∏ i, M.wordWeight (height s len i) (word s len w i)) ≤ ∏ i, Real.exp (-(d i : ℝ)) :=
      Finset.prod_le_prod₀ (fun i _ => M.wordWeight_nonneg _ _)
        (fun i _ => bin_weight_upper M (hbin i))
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem chainProduct_eq (w : C → ℤ → M.α) :
    chainProduct M len w = ∏ v : ((c : C) × Fin (len c - 1)),
      M.weight (w v.1 v.2.val) (w v.1 ((v.2.val : ℤ) + 1)) := by
  rw [chainProduct, ← Finset.prod_coe_sort]
  symm
  exact Fintype.prod_equiv (turnEquiv len) _ _ (fun _ => rfl)

end ChainWeights

end

end Kaplansky.Random
