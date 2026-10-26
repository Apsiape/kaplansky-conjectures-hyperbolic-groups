import Kaplansky.Random.Chain.StageRealization
import OAI.Algebra.GroupRing.StageExpectation

/-!
# Fork of `OAI/Algebra/GroupRing/StageExpectation.lean`

Model-dependent parts of `StageExpectation` and `TwoSideStage`.  A `TwoSideStage.Side`
now carries the colour data of its prescribed side; the realization count of a word is
summed over the colourings `κ` of the marked vertices (`crealizations`), and the first
moment acquires the factor `|Col| ^ |V|` (`Side.colours`).  For a one-colour side this
factor is `1` and everything is OpenAI's argument.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors

noncomputable section

namespace StageExpectation
open scoped Classical BigOperators
open ChainSubdivision BlockAlignment ComparedBlocks RepeatedBlocks
open OAI.TorsionFreeZeroDivisors.StageExpectation (label_union_mean word_position activeLen
  activeIndex active_bin_sum)
section
variable (M : Model) {C V TV : Type} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)

include hs in
theorem turnProduct_bin (w : C → ℤ → M.α) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ M.binWords (height s len i) (d i)) :
    ChainRealization.turnProduct M len w ≤ Real.exp (-∑ i, (d i : ℝ)) := by
  rw [ChainRealization.turnProduct, ← ChainWeights.chainProduct_eq M len w]
  exact ChainWeights.chain_bin_bound M s hs len w d hbin

variable {Col : Type} [Fintype Col] [DecidableEq Col] (flip : Col → Col)

include hs in
theorem fixed_label_bin_bound (col : TV → Col) (out : TV → Finset M.α)
    (pp : V → Option TV) (n p : ℝ) (hp : 0 ≤ p)
    (w : C → ℤ → M.α) (κ : V → Col) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ M.binWords (height s len i) (d i))
    (himm : Function.Injective (fun a =>
      ((graph len first last).origin a, ChainRealization.label M len w a)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ c a b, a ≠ b →
      (Fintype.card {x : TV // col x = c ∧ a ∈ out x ∧ b ∈ out x} : ℝ) ≤ n * p * M.J a b)
    (N D R : ℕ) (hD : 2 ≤ D) (hR : 0 < R)
    (hdegree : ∀ v, Nat.card {a : PatternEmbeddings.Dart (cout col out) //
      PatternEmbeddings.origin (cout col out) a = v} ≤ D)
    (hsize : ∀ x : PatternEmbeddings.Dart (cout col out),
      R + (∑ c, len c) + 4 * D ^ (2 * N + 1) ≤
        Nat.card {a : PatternEmbeddings.Dart (cout col out) //
          PatternEmbeddings.label (cout col out) a = PatternEmbeddings.label (cout col out) x})
    (hΩ : (ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label (cout col out)) (bar := cbar M.inv flip)
      (PatternEmbeddings.origin (cout col out)) N ∅).Nonempty) :
    ((∑ r ∈ ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label (cout col out)) (bar := cbar M.inv flip)
      (PatternEmbeddings.origin (cout col out)) N ∅,
        StageRealization.realizations (graph len first last)
          (ChainRealization.clabel M len first last flip w κ) (cout col out)
          (OAI.TorsionFreeZeroDivisors.ChainRealization.pin len pp) (cbar M.inv flip) r : ℕ) : ℝ) /
      (ConditionedMatchings.Matching.conditioned
        (label := PatternEmbeddings.label (cout col out)) (bar := cbar M.inv flip)
        (PatternEmbeddings.origin (cout col out)) N ∅).card ≤
      (n ^ ((Finset.univ.filter fun v => pp v = none).card + ∑ c, (len c - 1)) *
        p ^ (∑ c, (len c - 1))) / (R : ℝ) ^ (∑ c, len c) *
        Real.exp (-∑ i, (d i : ℝ)) := by
  have hn0 : 0 ≤ n := (Nat.cast_nonneg (Fintype.card TV)).trans hn
  refine (ChainRealization.fixed_label_bound M len first last flip col out pp n p hp w κ
    himm hn htable N D R hD hR hdegree hsize hΩ).trans ?_
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (turnProduct_bin M s hs len w d hbin) (by positivity)

end

/-- Letters on a chain, extended by an arbitrary letter off the chain. -/
def readWord (M : Model) {C : Type} (len : C → ℕ) (F : ComparedBlocks.Position len → M.α)
    (c : C) (q : ℤ) : M.α :=
  if h : q ∈ positions 0 (len c) then F ⟨c, ⟨q, h⟩⟩ else Classical.arbitrary M.α

@[simp] theorem readWord_on (M : Model) {C : Type} (len : C → ℕ)
    (F : ComparedBlocks.Position len → M.α) (c : C)
    (q : positions 0 (len c)) : readWord M len F c q.val = F ⟨c, q⟩ := by
  simp [readWord, q.property]

section Active
open OAI.TorsionFreeZeroDivisors.ChainStageLabels (StagePosition activeBlocks ActiveChain)
variable (M : Model) {C E : Type} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

include hs in
theorem active_bins (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → M.α)
    (hF : F ∈ ChainStageLabels.fullWords M s len m j cmp d) :
    ∀ i, word s (activeLen len m j) (readWord M (activeLen len m j) F) i ∈
      M.binWords (height s (activeLen len m j) i) (d (activeIndex s len m j i)) := by
  obtain ⟨w, _, _, hb, rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (activeLen len m j)
      (readWord M (activeLen len m j) (fun x => w x.1.val x.2.val)) i =
      word s len w (activeIndex s len m j i) := by
    funext k
    dsimp only [word, readWord]
    rw [dite_eq_left (word_position s hs (activeLen len m j) i k)]
    rfl
  rw [he]
  exact hb (activeIndex s len m j i)

end Active

end StageExpectation

namespace TwoSideStage
open scoped Classical BigOperators
open ChainSubdivision PatternEmbeddings ConditionedMatchings BlockAlignment ComparedBlocks
  RepeatedBlocks

/-- A stage on one prescribed side, with the colour data of that side. -/
structure Side (M : Model) where
  C : Type
  V : Type
  TV : Type
  fC : Fintype C
  fV : Fintype V
  fTV : Fintype TV
  dTV : DecidableEq TV
  Col : Type
  fCol : Fintype Col
  dCol : DecidableEq Col
  flip : Col → Col
  col : TV → Col
  len : C → ℕ
  first : C → V
  last : C → V
  out : TV → Finset M.α
  pin : V → Option TV
attribute [instance] Side.fC Side.fV Side.fTV Side.dTV Side.fCol Side.dCol

variable {M : Model}

abbrev Side.Word (S : Side M) := ComparedBlocks.Position S.len → M.α
abbrev Side.outgoing (S : Side M) := cout S.col S.out
abbrev Side.Match (S : Side M) := Matching (label S.outgoing) (cbar M.inv S.flip)

def Side.samples (S : Side M) (N : ℕ) : Finset S.Match :=
  Matching.conditioned (label := label S.outgoing) (bar := cbar M.inv S.flip)
    (origin S.outgoing) N ∅

def Side.immersed (S : Side M) (F : S.Word) : Prop :=
  Function.Injective (fun a => ((graph S.len S.first S.last).origin a,
    ChainRealization.label M S.len (StageExpectation.readWord M S.len F) a))

def Side.realizations (S : Side M) (F : S.Word) (κ : S.V → S.Col) (r : S.Match) : ℕ :=
  StageRealization.realizations (graph S.len S.first S.last)
    (ChainRealization.clabel M S.len S.first S.last S.flip (StageExpectation.readWord M S.len F) κ)
    S.outgoing (OAI.TorsionFreeZeroDivisors.ChainRealization.pin S.len S.pin) (cbar M.inv S.flip) r

/-- Realizations summed over the colourings of the marked vertices. -/
def Side.crealizations (S : Side M) (F : S.Word) (r : S.Match) : ℕ :=
  ∑ κ : S.V → S.Col, S.realizations F κ r

def Side.internal (S : Side M) : ℕ := ∑ c, (S.len c - 1)
def Side.edges (S : Side M) : ℕ := ∑ c, S.len c
def Side.freeMarks (S : Side M) : ℕ := (Finset.univ.filter fun v => S.pin v = none).card

def Side.cost (S : Side M) (n p : ℝ) (R : ℕ) : ℝ :=
  (n ^ (S.freeMarks + S.internal) * p ^ S.internal) / (R : ℝ) ^ S.edges

/-- Number of colourings of the marked vertices. -/
def Side.colours (S : Side M) : ℝ := (Fintype.card S.Col : ℝ) ^ Fintype.card S.V

theorem Side.colours_eq (S : Side M) :
    (Fintype.card (S.V → S.Col) : ℝ) = S.colours := by
  simp [Side.colours, Fintype.card_fun]

theorem Side.colours_nonneg (S : Side M) : 0 ≤ S.colours := by
  unfold Side.colours; positivity

/-- The literal finite matching conditions. -/
structure Conditions (S : Side M) (n p : ℝ) (N D R : ℕ) : Prop where
  nonneg : 0 ≤ p
  vertices : (Fintype.card S.TV : ℝ) ≤ n
  table : ∀ c a b, a ≠ b →
    (Fintype.card {x : S.TV // S.col x = c ∧ a ∈ S.out x ∧ b ∈ S.out x} : ℝ) ≤ n * p * M.J a b
  degree_lower : 2 ≤ D
  denominator_pos : 0 < R
  degree : ∀ v, Nat.card {a : PatternEmbeddings.Dart S.outgoing // origin S.outgoing a = v} ≤ D
  room : ∀ x : PatternEmbeddings.Dart S.outgoing,
    R + S.edges + 4 * D ^ (2 * N + 1) ≤
      Nat.card {a : PatternEmbeddings.Dart S.outgoing // label S.outgoing a = label S.outgoing x}
  nonempty : (S.samples N).Nonempty

variable (s : ℝ) (hs : 0 < s)

def Side.bins (S : Side M) (d : Underlying s S.len → ℤ) (F : S.Word) : Prop :=
  ∀ i, RepeatedBlocks.word s S.len (StageExpectation.readWord M S.len F) i ∈
    M.binWords (RepeatedBlocks.height s S.len i) (d i)

include hs in
/-- Single-side first moment of one word, summed over the marked-vertex colourings. -/
theorem fixed_mean (S : Side M) (n p : ℝ) (N D R : ℕ) (h : Conditions S n p N D R)
    (F : S.Word) (hF : S.immersed F) (d : Underlying s S.len → ℤ)
    (hd : S.bins s d F) :
    TwoSideMean.mean (S.samples N) (S.crealizations F) ≤
      S.colours * (S.cost n p R * Real.exp (-∑ i, (d i : ℝ))) := by
  have hone (κ : S.V → S.Col) :
      TwoSideMean.mean (S.samples N) (S.realizations F κ) ≤
        S.cost n p R * Real.exp (-∑ i, (d i : ℝ)) :=
    StageExpectation.fixed_label_bin_bound M s hs S.len S.first S.last S.flip S.col S.out S.pin
      n p h.nonneg (StageExpectation.readWord M S.len F) κ d hd hF h.vertices h.table
      N D R h.degree_lower h.denominator_pos h.degree h.room h.nonempty
  have hu := TwoSideMean.label_union (S.samples N) (Finset.univ : Finset (S.V → S.Col))
    (fun κ => S.realizations F κ) (fun κ _ => hone κ)
  rw [Finset.card_univ, Side.colours_eq] at hu
  exact hu

variable {W : Type*}

def immersedLabels (A B : Side M) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word) :
    Finset W :=
  X.filter fun w => A.immersed (WA w) ∧ B.immersed (WB w)

def count (A B : Side M) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (r : A.Match × B.Match) : ℕ :=
  ∑ w ∈ immersedLabels A B X WA WB, A.crealizations (WA w) r.1 * B.crealizations (WB w) r.2

include hs in
/-- Two-side stage first moment. -/
theorem mean_bound (A B : Side M) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (n p : ℝ) (N D R : ℕ) (hA : Conditions A n p N D R) (hB : Conditions B n p N D R)
    (dA : Underlying s A.len → ℤ) (dB : Underlying s B.len → ℤ)
    (hdA : ∀ w ∈ X, A.bins s dA (WA w)) (hdB : ∀ w ∈ X, B.bins s dB (WB w)) :
    TwoSideMean.mean ((A.samples N) ×ˢ (B.samples N)) (count A B X WA WB) ≤
      (X.card : ℝ) * ((A.colours * B.colours) * (A.cost n p R * B.cost n p R) *
        Real.exp (-(∑ i, (dA i : ℝ)) - (∑ i, (dB i : ℝ)))) := by
  have hn : 0 ≤ n := (Nat.cast_nonneg (Fintype.card A.TV)).trans hA.vertices
  have hp := hA.nonneg
  have hcA := A.colours_nonneg
  have hcB := B.colours_nonneg
  have hcost : 0 ≤ (A.colours * B.colours) * (A.cost n p R * B.cost n p R) *
      Real.exp (-(∑ i, (dA i : ℝ)) - (∑ i, (dB i : ℝ))) := by
    unfold Side.cost
    positivity
  have he := TwoSideMean.global_mean_bound (A.samples N) (B.samples N)
    (immersedLabels A B X WA WB) (fun w => A.crealizations (WA w))
    (fun w => B.crealizations (WB w))
    (fun w hw => fixed_mean s hs A n p N D R hA (WA w)
      (Finset.mem_filter.mp hw).2.1 dA (hdA w (Finset.mem_filter.mp hw).1))
    (fun w hw => fixed_mean s hs B n p N D R hB (WB w)
      (Finset.mem_filter.mp hw).2.2 dB (hdB w (Finset.mem_filter.mp hw).1))
  have eq : (A.colours * (A.cost n p R * Real.exp (-∑ i, (dA i : ℝ)))) *
      (B.colours * (B.cost n p R * Real.exp (-∑ i, (dB i : ℝ)))) =
      (A.colours * B.colours) * (A.cost n p R * B.cost n p R) *
        Real.exp (-(∑ i, (dA i : ℝ)) - (∑ i, (dB i : ℝ))) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [eq] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Finset.card_filter_le ..)) hcost)

theorem cost_product (A B : Side M) (n p : ℝ) (R : ℕ) :
    A.cost n p R * B.cost n p R =
      (n ^ (A.freeMarks + A.internal + B.freeMarks + B.internal) * p ^ (A.internal + B.internal)) /
        (R : ℝ) ^ (A.edges + B.edges) := by
  simp only [Side.cost, pow_add]
  ring

end TwoSideStage

end

end Kaplansky.Random
