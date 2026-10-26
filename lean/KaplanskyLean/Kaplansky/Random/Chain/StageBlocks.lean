import Kaplansky.Random.Model
import OAI.Algebra.GroupRing.StageBlocks

/-!
# Fork of `OAI/Algebra/GroupRing/StageBlocks.lean` for an abstract `Model`

Model-dependent declarations of the namespaces `StageBlocks`, `ActualStageLabels` and
`ChainStageLabels`, re-declared over the alphabet `M.α` with the decay constants
`δ = 1/M.D`, `h₀ = M.h₀` in place of `1/600`, `3002`.  Generic declarations
(`ActualStageLabels.projection_empty`, `projection_bound`, `ChainStageLabels.stageWords_mem`,
`ActiveChain`, `StagePosition`, `StageTail`, `activeBlocks`, `tail_subset`, `blockPoint`,
`tailPoint`, `tail_count`, `count_extension_exp`) are used from OpenAI's file.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors

noncomputable section

namespace StageBlocks
open scoped BigOperators Classical
variable (M : Model)

def translationWords {n : ℕ} (D : BlockConstraints.Translation n) : Finset (Fin n → M.α) :=
  Finset.univ.filter (fun W => ∀ i : D.domain, W (D.target i) = W i.val)

theorem translation_card {n : ℕ} (D : BlockConstraints.Translation n) :
    (translationWords M D).card ≤ (Fintype.card M.α) ^ (n - D.domain.card) := by
  have he : {W : Fin n → M.α // W ∈ translationWords M D} ≃
      {W : Fin n → M.α // ∀ i : D.domain, W (D.target i) = W i.val} :=
    Equiv.subtypeEquivRight (fun W => by simp [translationWords])
  have hh := D.word_count (T := M.α)
  rw [← Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_coe] at hh
  exact hh

end StageBlocks

namespace ActualStageLabels

open scoped Classical BigOperators
open ComparedBlocks RepeatedBlocks
variable (M : Model)
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ)
variable (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def symbol (e : E) : M.α ≃ M.α :=
  if cmp.reverse e then ⟨M.inv, M.inv, M.inv_inv, M.inv_inv⟩ else Equiv.refl _

abbrev L := links s hs len m cmp err (symbol M len m cmp)
abbrev P := (data s hs len m cmp err).matching
abbrev Component := LinkComponents.Component (multiplicity s len m) (P s hs len m cmp err)

def Comparing (w : C → ℤ → M.α) : Prop :=
  ∀ x e, cmp.side x = some e →
    w x.1.1 x.2.val = if cmp.reverse e then
      M.inv (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val

def Immersed (w : C → ℤ → M.α) : Prop :=
  ∀ (i : Underlying s len) q,
    lower s len i ≤ q → q + 1 < upper s len i → w i.1 (q + 1) ≠ M.inv (w i.1 q)

variable (d : Underlying s len → ℤ)

def Feasible (W : (i : Underlying s len) → Fin (height s len i) → M.α) : Prop :=
  (∀ i, W i ∈ M.binWords (height s len i) (d i)) ∧
    ∃ w : C → ℤ → M.α, Comparing M len m cmp w ∧ Immersed M s len w ∧ W = word s len w

omit [Fintype C] in
theorem feasible_consistent {W : (i : Underlying s len) → Fin (height s len i) → M.α}
    (hW : Feasible M s len m cmp d W) : (L M s hs len m cmp err).Consistent W := by
  obtain ⟨_, w, hw, _, rfl⟩ := hW
  apply links_consistent s hs len m cmp err (symbol M len m cmp) (fun x => w x.1.1 x.2.val)
  · intro x e he
    have hh := hw x e he
    unfold symbol
    split_ifs with h
    · simpa [h] using hh
    · simpa [h] using hh
  · intro b x
    unfold word
    rw [coordinate_val, sub_add_cancel]
    have ht := ((mem_blockPositions s hs (traversalLength len m)).mp x.property).1
    exact congrArg (fun t : Traversal m => w t.1 x.val.2.val) ht.symm

/-- The component cost, with `δ = 1/M.D`. -/
def cost (c : Component s hs len m cmp err) : ℝ :=
  LinkComponents.componentLabelCost (multiplicity s len m) (P s hs len m cmp err)
    (fun i => (d i : ℝ)) (1 / (M.D : ℝ)) s c

theorem root_count
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val))
    (w₀ : C → ℤ → M.α) (hcompare₀ : Comparing M len m cmp w₀) (hred₀ : Immersed M s len w₀)
    (c : Component s hs len m cmp err) :
    ∃ (r : c) (R : Finset (Fin (height s len r.val) → M.α)),
      (R.card : ℝ) ≤ Real.exp (cost M s hs len m cmp err d c +
        (err : ℝ) * Real.log (Fintype.card M.α)) ∧
      ∀ W, Feasible M s len m cmp d W → W r.val ∈ R := by
  have halog : 0 ≤ Real.log (Fintype.card M.α) := M.log_card_α_nonneg
  by_cases hc : LinkComponents.HasSelf (multiplicity s len m) (P s hs len m cmp err) c
  · obtain ⟨r, tr, hdef, htr⟩ := self_component_translation s hs len m cmp err M.inv
      M.inv_inv M.inv_ne w₀ hcompare₀ hred₀ hreduced c hc
    refine ⟨r, StageBlocks.translationWords M tr, ?_, ?_⟩
    · have hb : ((StageBlocks.translationWords M tr).card : ℝ) ≤
          (Fintype.card M.α : ℝ) ^ (height s len r.val - tr.domain.card) := by
        exact_mod_cast StageBlocks.translation_card M tr
      have ha : 0 < (Fintype.card M.α : ℝ) := by exact_mod_cast M.card_α_pos
      calc
        _ ≤ (Fintype.card M.α : ℝ) ^ (height s len r.val - tr.domain.card) := hb
        _ ≤ (Fintype.card M.α : ℝ) ^ err :=
          pow_le_pow_right₀ (by exact_mod_cast M.card_α_pos) hdef
        _ = _ := by
          simp only [cost, LinkComponents.componentLabelCost, ite_eq_left hc, zero_add]
          rw [Real.exp_nat_mul, Real.exp_log ha]
    · intro W hW
      obtain ⟨_, w, hw, _, rfl⟩ := hW
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htr M.α M.inv w hw⟩
  · let r := LinkComponents.minimumRoot (multiplicity s len m) (P s hs len m cmp err)
      (fun i => (d i : ℝ)) c
    refine ⟨r, M.binWords (height s len r.val) (d r.val), ?_, ?_⟩
    · have hb := Alphabet.bin_card_bound M.decays (height s len r.val) (hlarge r.val) (d r.val)
      apply hb.trans
      apply Real.exp_le_exp.mpr
      have hh := M.scale_mul (hscale r.val)
      have he := mul_nonneg (Nat.cast_nonneg err : (0 : ℝ) ≤ err) halog
      simp only [cost, LinkComponents.componentLabelCost, ite_eq_right hc]
      change 2 * (d r.val : ℝ) + 2 - 2 * (1 / (M.D : ℝ)) * (height s len r.val : ℝ) ≤ _
      linarith
    · intro W hW
      exact hW.1 r.val

theorem stage_count (A : Finset (Underlying s len))
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val)) :
    ((StageLabels.stageWords (height s len) A (Feasible M s len m cmp d)).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents
          (L M s hs len m cmp err).graph.connectedComponentMk A,
        cost M s hs len m cmp err d c.val) +
        2 * (err : ℝ) * Fintype.card (Underlying s len) * Real.log (Fintype.card M.α)) := by
  by_cases hex : ∃ W, Feasible M s len m cmp d W
  · obtain ⟨W, _, w₀, hw₀, hr₀, _⟩ := hex
    have hroot := root_count M s hs len m cmp err d hlarge hscale hreduced w₀ hw₀ hr₀
    choose r R hR hmem using hroot
    exact OAI.TorsionFreeZeroDivisors.ActualStageLabels.projection_bound
      (L M s hs len m cmp err) A r R (Feasible M s len m cmp d)
      (fun _ hw => feasible_consistent M s hs len m cmp err d hw)
      (fun W hw c => hmem c W hw) err
      (links_deficit s hs len m cmp err (symbol M len m cmp))
      (cost M s hs len m cmp err d) hR
  · rw [OAI.TorsionFreeZeroDivisors.ActualStageLabels.projection_empty _ _ _ hex,
      Finset.card_empty, Nat.cast_zero]
    exact (Real.exp_pos _).le

theorem active_iff (j : ℕ) (c : Component s hs len m cmp err) :
    c ∈ StageLabels.activeComponents (L M s hs len m cmp err).graph.connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)) ↔
      j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c := by
  rw [← LinkComponents.active_iff]
  constructor
  · intro hc
    obtain ⟨i, hi, hc⟩ := Finset.mem_image.mp hc
    exact ⟨⟨i, hc⟩, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, i.property⟩

theorem cost_sum (j : ℕ) :
    (∑ c : StageLabels.activeComponents (L M s hs len m cmp err).graph.connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)), cost M s hs len m cmp err d c.val) =
    ∑ c : Component s hs len m cmp err,
      if j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c then
        cost M s hs len m cmp err d c else 0 := by
  change (∑ c : StageLabels.activeComponents
    (LinkComponents.graph (multiplicity s len m) (P s hs len m cmp err)).connectedComponentMk
    (Finset.univ.filter (fun i => j < multiplicity s len m i)), cost M s hs len m cmp err d c.val) = _
  rw [Finset.sum_coe_sort]
  have hset : StageLabels.activeComponents
      (LinkComponents.graph (multiplicity s len m) (P s hs len m cmp err)).connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)) =
      Finset.univ.filter (fun c : Component s hs len m cmp err =>
        j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c) := by
    ext c
    exact (active_iff M s hs len m cmp err j c).trans (by simp)
  rw [hset, Finset.sum_filter]

end ActualStageLabels

namespace ChainStageLabels
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
open OAI.TorsionFreeZeroDivisors.ChainStageLabels
variable (M : Model)
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

def blockRestrict (F : StagePosition len m j → M.α) :
    (i : activeBlocks s len m j) → Fin (height s len i.val) → M.α :=
  fun i k => F (blockPoint s hs len m j i k)
def tailRestrict (F : StagePosition len m j → M.α) : StageTail s len m j → M.α :=
  fun x => F (tailPoint s hs len m j x)

def encode (F : StagePosition len m j → M.α) :=
  (blockRestrict M s hs len m j F, tailRestrict M s hs len m j F)

theorem encode_injective : Function.Injective (encode M s hs len m j) := by
  intro F G he
  have hb := congrArg Prod.fst he
  have ht := congrArg Prod.snd he
  funext x
  rcases x with ⟨⟨c, hc⟩, q⟩
  obtain ⟨k, hk⟩ | htq := full_or_tail s hs (len c) q.property
  · let i : activeBlocks s len m j := ⟨⟨c, k⟩, by simp [activeBlocks, hc]⟩
    let z : Fin (height s len i.val) := wordCoordinate s len i.val ⟨q.val, hk⟩
    have h := congr_fun (congr_fun hb i) z
    simpa [encode, blockRestrict, blockPoint, z, i] using h
  · have h := congr_fun ht ⟨⟨c, hc⟩, ⟨q.val, htq⟩⟩
    exact h

theorem extension_count (X : Finset (StagePosition len m j → M.α))
    (Y : Finset ((i : activeBlocks s len m j) → Fin (height s len i.val) → M.α))
    (hX : ∀ F ∈ X, blockRestrict M s hs len m j F ∈ Y) :
    X.card ≤ Y.card * (Fintype.card M.α) ^ Fintype.card (StageTail s len m j) := by
  calc
    X.card = (X.image (encode M s hs len m j)).card :=
      (Finset.card_image_of_injective X (encode_injective M s hs len m j)).symm
    _ ≤ (Y ×ˢ Finset.univ).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_product.mpr ⟨hX F hF, Finset.mem_univ _⟩
    _ = _ := by simp

variable (cmp : Comparisons (E := E) (traversalLength len m)) (d : Underlying s len → ℤ)

def fullWords : Finset (StagePosition len m j → M.α) :=
  Finset.univ.filter (fun F => ∃ w : C → ℤ → M.α,
    ActualStageLabels.Comparing M len m cmp w ∧ ActualStageLabels.Immersed M s len w ∧
    (∀ i, word s len w i ∈ M.binWords (height s len i) (d i)) ∧
    F = fun x => w x.1.val x.2.val)

theorem blockRestrict_word (w : C → ℤ → M.α) :
    blockRestrict M s hs len m j (fun x => w x.1.val x.2.val) =
      fun i k => word s len w i.val k := by
  funext i k
  have hv := wordCoordinate_val s len i.val ((wordCoordinate s len i.val).symm k)
  rw [Equiv.apply_symm_apply] at hv
  change w i.val.1 ((wordCoordinate s len i.val).symm k).val =
    w i.val.1 ((k.val : ℤ) + lower s len i.val)
  congr 1
  omega

theorem restrict_mem (F : StagePosition len m j → M.α)
    (hF : F ∈ fullWords M s len m j cmp d) :
    blockRestrict M s hs len m j F ∈ StageLabels.stageWords (height s len)
      (activeBlocks s len m j) (ActualStageLabels.Feasible M s len m cmp d) := by
  have hF' : ∃ w : C → ℤ → M.α,
      ActualStageLabels.Comparing M len m cmp w ∧ ActualStageLabels.Immersed M s len w ∧
      (∀ i, word s len w i ∈ M.binWords (height s len i) (d i)) ∧
      F = fun x => w x.1.val x.2.val := (Finset.mem_filter.mp hF).2
  obtain ⟨w, hw, hr, hd, rfl⟩ := hF'
  rw [blockRestrict_word]
  have hW : ActualStageLabels.Feasible M s len m cmp d (word s len w) := ⟨hd, w, hw, hr, rfl⟩
  exact stageWords_mem (height s len) (activeBlocks s len m j)
    (ActualStageLabels.Feasible M s len m cmp d) (word s len w) hW

/-- Stage-label estimate including every tail (OAI `full_stage_count`). -/
theorem full_stage_count (err : ℕ)
    (hlarge : ∀ i, M.h₀ ≤ height s len i)
    (hscale : ∀ i, s + 2 * M.D ≤ 2 * (height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1, x.2.val) ≠ ((cmp.pairing.partner x).1.1, (cmp.pairing.partner x).2.val)) :
    ((fullWords M s len m j cmp d).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents
        (ActualStageLabels.L M s hs len m cmp err).graph.connectedComponentMk
          (activeBlocks s len m j),
        ActualStageLabels.cost M s hs len m cmp err d c.val) +
        (2 * (err : ℝ) * Fintype.card (Underlying s len) + (s + 1) * Fintype.card C) *
          Real.log (Fintype.card M.α)) := by
  have he := extension_count M s hs len m j (fullWords M s len m j cmp d)
    (StageLabels.stageWords (height s len) (activeBlocks s len m j)
      (ActualStageLabels.Feasible M s len m cmp d)) (restrict_mem M s hs len m j cmp d)
  have hcard := ActualStageLabels.stage_count M s hs len m cmp err d
    (activeBlocks s len m j) hlarge hscale hreduced
  exact count_extension_exp _ _ _ _ _ _ _ he hcard (tail_count s hs len m j)
    M.card_α_pos

end ChainStageLabels

end

end Kaplansky.Random
