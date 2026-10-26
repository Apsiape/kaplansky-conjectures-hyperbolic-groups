import Kaplansky.Exclusion.Segments
import OAI.Algebra.GroupRing.PlanarMap

/-!
# The prepared system and the key estimate

For a boundary map `m` of a reduced cone picture in a pattern-free graph, we

1. keep the balanced segments of the graph boundaries, with the interval comparisons among them;
2. close every split segment by a short closure (generic version of OpenAI's `ClosedWords`, using
   `ShortClosure.short_closure` with the diameter and degree hypotheses of `PatternFree`);
3. transfer the planar separator of the whole segmented map to the kept pieces
   (`PlanarMap.Model.induced`);
4. run the localisation argument with slack (`GPathSystem.excluded_of_separator'`).

The result (`MapSystem.key_estimate`) is the paper's Proposition 4.4 (`prop:key`):
`13/16 · ε · H ≤ ℓ_∞` when there is no root, where `H` is the total length of the graph boundaries
and `ℓ_∞` that of the free outer boundaries; and a rooted map cannot occur.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.Exclusion

noncomputable section

open OAI.TorsionFreeZeroDivisors
open PortSubdivision ComparedBlocks BlockAlignment PermutationCycles

namespace MapSystem
open scoped Classical BigOperators

variable {V D A : Type} [Fintype V] [Fintype D] {Γ : PortGraph V D} {label : D → A}
  {inv : A → A} {isRoot : V → Prop}
variable (m : MapSystem Γ label inv isRoot) (cap : ℕ) (hc : 0 < cap)

abbrev Kept := {p : m.Piece cap // m.keepP cap p}
abbrev kseg (q : m.Kept cap) : List D := BalancedWords.segment m.w cap hc q.val

lemma kseg_ne (q : m.Kept cap) : m.kseg cap hc q ≠ [] :=
  BalancedWords.segment_nonempty m.w cap hc m.nonempty q.val

abbrev kstart (q : m.Kept cap) : V := Γ.origin ((m.kseg cap hc q).head (m.kseg_ne cap hc q))

lemma kseg_chain (q : m.Kept cap) :
    (m.kseg cap hc q).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse) :=
  ConsecutivePieces.segment_chain _ _ _ (m.chain q.val.1 q.property) q.val.2

lemma segment_path (q : m.Kept cap) :
    ShortClosure.ReducedPath Γ (m.kstart cap hc q)
      (ShortClosure.endpoint Γ (m.kstart cap hc q) (m.kseg cap hc q)) (m.kseg cap hc q) where
  chain := m.kseg_chain cap hc q
  start := by
    intro d hd
    rw [List.head?_eq_some_head (m.kseg_ne cap hc q)] at hd
    exact congrArg Γ.origin (Option.some.inj hd.symm)
  finish := rfl

lemma kseg_length (q : m.Kept cap) :
    (m.kseg cap hc q).length = BalancedWords.old m.w cap q.val :=
  BalancedWords.segment_length m.w cap hc q.val

variable (B : ℕ)
  (hdiam : ∀ a b, (ShortClosure.simpleGraph Γ).Reachable a b → (ShortClosure.simpleGraph Γ).dist a b ≤ B)
  (hdeg : ∀ v, 7 ≤ (Finset.univ.filter (fun x : D => Γ.origin x = v)).card)

/-- A chosen short closure of a kept segment. -/
noncomputable def chosenTail (q : m.Kept cap) : List D :=
  (ShortClosure.short_closure Γ B hdiam hdeg (m.segment_path cap hc q) (m.kseg_ne cap hc q)).choose

lemma chosenTail_spec (q : m.Kept cap) :
    (m.chosenTail cap hc B hdiam hdeg q).length ≤ B + 4 * (Nat.log 2 (Fintype.card V) + 1) ∧
      ShortClosure.ReducedPath Γ (m.kstart cap hc q) (m.kstart cap hc q)
        (m.kseg cap hc q ++ m.chosenTail cap hc B hdiam hdeg q) ∧
      ∀ᵉ (a ∈ (m.kseg cap hc q ++ m.chosenTail cap hc B hdiam hdeg q).getLast?)
          (b ∈ (m.kseg cap hc q ++ m.chosenTail cap hc B hdiam hdeg q).head?),
        WeightedMoore.PortWalk.step Γ.origin Γ.reverse a b :=
  (ShortClosure.short_closure Γ B hdiam hdeg (m.segment_path cap hc q) (m.kseg_ne cap hc q)).choose_spec

/-- Only split boundaries are closed. -/
noncomputable def tail (q : m.Kept cap) : List D :=
  if (m.w q.val.1).length ≤ cap then [] else m.chosenTail cap hc B hdiam hdeg q
noncomputable def word (q : m.Kept cap) : List D :=
  m.kseg cap hc q ++ m.tail cap hc B hdiam hdeg q

lemma tail_short (q : m.Kept cap) (hq : (m.w q.val.1).length ≤ cap) :
    m.tail cap hc B hdiam hdeg q = [] := ite_eq_left hq
lemma tail_bound (q : m.Kept cap) :
    (m.tail cap hc B hdiam hdeg q).length ≤ B + 4 * (Nat.log 2 (Fintype.card V) + 1) := by
  unfold tail
  split_ifs
  · simp only [List.length_nil, Nat.zero_le]
  · exact (m.chosenTail_spec cap hc B hdiam hdeg q).1
lemma word_short (q : m.Kept cap) (hq : (m.w q.val.1).length ≤ cap) :
    m.word cap hc B hdiam hdeg q = m.w q.val.1 := by
  rw [word, m.tail_short cap hc B hdiam hdeg q hq, List.append_nil]
  exact BalancedWords.intact m.w cap hc q.val hq
lemma word_nonempty (q : m.Kept cap) : m.word cap hc B hdiam hdeg q ≠ [] := by
  intro h
  exact m.kseg_ne cap hc q (List.append_eq_nil_iff.mp h).1
lemma word_chain (q : m.Kept cap) :
    (m.word cap hc B hdiam hdeg q).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse) := by
  by_cases hq : (m.w q.val.1).length ≤ cap
  · rw [m.word_short cap hc B hdiam hdeg q hq]
    exact m.chain q.val.1 q.property
  · simpa only [word, tail, ite_eq_right hq] using (m.chosenTail_spec cap hc B hdiam hdeg q).2.1.chain
lemma cyclic_of_long (q : m.Kept cap) (hq : cap < (m.w q.val.1).length) :
    ∀ᵉ (a ∈ (m.word cap hc B hdiam hdeg q).getLast?) (b ∈ (m.word cap hc B hdiam hdeg q).head?),
      WeightedMoore.PortWalk.step Γ.origin Γ.reverse a b := by
  simpa only [word, tail, ite_eq_right (show ¬(m.w q.val.1).length ≤ cap by omega)] using
    (m.chosenTail_spec cap hc B hdiam hdeg q).2.2
lemma old_le_word (q : m.Kept cap) :
    BalancedWords.old m.w cap q.val ≤ (m.word cap hc B hdiam hdeg q).length := by
  simp only [word, List.length_append, m.kseg_length]
  omega

/-! ### The root piece -/

/-- The root piece: the intact rooted boundary, if it is not split. -/
noncomputable def rootK : Option (m.Kept cap) := m.root.bind fun t =>
  if h : (m.w t).length ≤ cap ∧ m.keep t then
    some ⟨⟨t, ⟨0, BalancedPieces.number_pos hc⟩⟩, h.2⟩ else none

lemma kept_eq (p q : m.Kept cap) (h : p.val.1 = q.val.1) (hp : (m.w p.val.1).length ≤ cap) : p = q := by
  rcases p with ⟨⟨t, i⟩, hp'⟩
  rcases q with ⟨⟨u, j⟩, hq'⟩
  dsimp only at h hp
  subst u
  have hij : i = j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    simp only [BalancedPieces.number, ite_eq_left hp] at hi hj
    omega
  subst hij
  rfl

lemma rootK_eq_some (q : m.Kept cap) :
    m.rootK cap hc = some q ↔ m.root = some q.val.1 ∧ (m.w q.val.1).length ≤ cap := by
  cases hr : m.root with
  | none => simp [rootK, hr]
  | some t =>
    by_cases ht : (m.w t).length ≤ cap ∧ m.keep t
    · simp only [rootK, hr, Option.bind_some, dite_eq_left ht, Option.some.injEq]
      constructor
      · intro h
        rw [← h]
        exact ⟨rfl, ht.1⟩
      · intro h
        apply m.kept_eq cap _ q (by simpa using h.1) ht.1
    · simp only [rootK, hr, Option.bind_some, dite_eq_right ht, Option.some.injEq]
      constructor
      · intro h; cases h
      · rintro ⟨rfl, h2⟩
        exact False.elim (ht ⟨h2, q.property⟩)

lemma cyclic_iff' {P : Type} [Fintype P] (root : Option P) (t : P) :
    StageRoot.cyclic root t = true ↔ root ≠ some t := by
  simp only [StageRoot.cyclic, decide_eq_true_eq]

lemma word_cyclic (q : m.Kept cap) (hq : StageRoot.cyclic (m.rootK cap hc) q = true) :
    ∀ᵉ (a ∈ (m.word cap hc B hdiam hdeg q).getLast?) (b ∈ (m.word cap hc B hdiam hdeg q).head?),
      WeightedMoore.PortWalk.step Γ.origin Γ.reverse a b := by
  have hq' := (cyclic_iff' (m.rootK cap hc) q).mp hq
  by_cases hs : (m.w q.val.1).length ≤ cap
  · rw [m.word_short cap hc B hdiam hdeg q hs]
    apply m.cyclic q.val.1 q.property
    intro he
    exact hq' ((m.rootK_eq_some cap hc q).mpr ⟨he, hs⟩)
  · exact m.cyclic_of_long cap hc B hdiam hdeg q (by omega)

lemma root_start' (q : m.Kept cap) (hq : m.rootK cap hc = some q) :
    isRoot (Γ.origin ((m.word cap hc B hdiam hdeg q).head (m.word_nonempty cap hc B hdiam hdeg q))) := by
  have hs := (m.rootK_eq_some cap hc q).mp hq
  have he := m.word_short cap hc B hdiam hdeg q hs.2
  have hh : (m.word cap hc B hdiam hdeg q).head (m.word_nonempty cap hc B hdiam hdeg q) =
      (m.w q.val.1).head (m.nonempty q.val.1) := by
    simp only [he]
  rw [hh]
  exact m.root_start _ hs.1

/-! ### The prepared path system -/

abbrev Ck := m.keptComparisons cap hc

lemma upper_real (e : {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e}) :
    (m.Ck cap hc).hi e ≤ ((m.kseg cap hc ((m.Ck cap hc).source e)).length : ℝ) := by
  change (m.comparisons cap hc).hi e.val ≤ ((BalancedRotation.len m.w cap hc
    ((m.comparisons cap hc).source e.val)) : ℝ)
  rw [m.upper_eq]
  exact_mod_cast m.upper_le cap hc e.val

abbrev grow := WordPositions.prefix_bound (m.kseg cap hc) (m.tail cap hc B hdiam hdeg)

lemma kdart (x : Position (RestrictComparisons.Length (m.keepP cap)
    (len := BalancedRotation.len m.w cap hc))) :
    RawDecomposition.dart (m.kseg cap hc) x =
      RawDecomposition.dart m.w (BalancedRotation.e m.w cap hc (RestrictComparisons.embed _ x)) := by
  rw [← m.dart cap hc]
  rfl

/-- The key pairing facts for a kept side. -/
lemma kept_side {x : Position (RestrictComparisons.Length (m.keepP cap)
    (len := BalancedRotation.len m.w cap hc))}
    {e : {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e}}
    (he : (m.Ck cap hc).side x = some e) :
    m.keep (BalancedRotation.e m.w cap hc (RestrictComparisons.embed _ x)).1 ∧
    m.keep (m.α (BalancedRotation.e m.w cap hc (RestrictComparisons.embed _ x))).1 ∧
    BalancedRotation.e m.w cap hc (RestrictComparisons.embed _ ((m.Ck cap hc).pairing.partner x)) =
      m.α (BalancedRotation.e m.w cap hc (RestrictComparisons.embed _ x)) := by
  have hpart := RestrictComparisons.partner_image_of_side (m.comparisons cap hc) (m.keepP cap) he
  have hpartner : BalancedRotation.e m.w cap hc (RestrictComparisons.embed _ ((m.Ck cap hc).pairing.partner x)) =
      m.α (BalancedRotation.e m.w cap hc (RestrictComparisons.embed _ x)) := by
    change BalancedRotation.e m.w cap hc (RestrictComparisons.embed _
      (RestrictComparisons.partner (m.comparisons cap hc) (m.keepP cap) x)) = _
    rw [hpart, m.comparisons_partner, m.transport]
  refine ⟨?_, ?_, hpartner⟩
  · rw [BalancedRotation.source]; exact x.1.property
  · rw [← hpartner, BalancedRotation.source]
    exact ((m.Ck cap hc).pairing.partner x).1.property


/-- The comparisons of the prepared system: the kept comparisons, on the closed words. -/
noncomputable def ccomp :
    Comparisons (E := {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e})
      (fun q => (m.word cap hc B hdiam hdeg q).length) :=
  ExtendComparisons.comparisons (m.Ck cap hc) (m.grow cap hc B hdiam hdeg) (m.upper_real cap hc)

lemma ccomp_upper_le (e : {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e}) :
    m.upper cap hc e.val ≤
      (m.word cap hc B hdiam hdeg ((m.ccomp cap hc B hdiam hdeg).source e)).length := by
  have h1 : m.upper cap hc e.val ≤ (m.kseg cap hc ((m.Ck cap hc).source e)).length :=
    m.upper_le cap hc e.val
  exact h1.trans (m.grow cap hc B hdiam hdeg ((m.Ck cap hc).source e))

lemma ccomp_side {p : Position (fun q => (m.kseg cap hc q ++ m.tail cap hc B hdiam hdeg q).length)}
    {e : {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e}}
    (he : (m.ccomp cap hc B hdiam hdeg).side p = some e) :
    ∃ hp : ExtendComparisons.Old (len := fun q => (m.kseg cap hc q).length) p,
      (m.Ck cap hc).side (ExtendComparisons.project p hp) = some e := by
  change ExtendComparisons.side (m.Ck cap hc) p = some e at he
  have hp := ExtendComparisons.side_some_old (m.Ck cap hc) he
  refine ⟨hp, ?_⟩
  simpa only [ExtendComparisons.side, dite_eq_left hp] using he

lemma ccomp_reduced (p : Position (fun q => (m.word cap hc B hdiam hdeg q).length))
    (e : {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e})
    (he : (m.ccomp cap hc B hdiam hdeg).side p = some e) :
    RawDecomposition.dart (m.word cap hc B hdiam hdeg) p ≠
        RawDecomposition.dart (m.word cap hc B hdiam hdeg)
          ((m.ccomp cap hc B hdiam hdeg).pairing.partner p) ∧
      RawDecomposition.dart (m.word cap hc B hdiam hdeg) p ≠
        Γ.reverse (RawDecomposition.dart (m.word cap hc B hdiam hdeg)
          ((m.ccomp cap hc B hdiam hdeg).pairing.partner p)) := by
  obtain ⟨hp, he'⟩ := m.ccomp_side cap hc B hdiam hdeg he
  obtain ⟨h1, h2, h3⟩ := m.kept_side cap hc he'
  have hg := m.reduced _ h1 h2
  rw [← ExtendComparisons.embed_project (m.grow cap hc B hdiam hdeg) p hp]
  change RawDecomposition.dart (fun q => m.kseg cap hc q ++ m.tail cap hc B hdiam hdeg q) _ ≠
    RawDecomposition.dart _ (ExtendComparisons.partner (m.Ck cap hc) (m.grow cap hc B hdiam hdeg) _) ∧
    RawDecomposition.dart (fun q => m.kseg cap hc q ++ m.tail cap hc B hdiam hdeg q) _ ≠
      Γ.reverse (RawDecomposition.dart _
        (ExtendComparisons.partner (m.Ck cap hc) (m.grow cap hc B hdiam hdeg) _))
  rw [ExtendComparisons.partner_embed, WordPositions.dart_prefix, WordPositions.dart_prefix,
    m.kdart, m.kdart, h3]
  exact hg

lemma ccomp_compatible (hinv : Function.Involutive inv)
    (p : Position (fun q => (m.word cap hc B hdiam hdeg q).length))
    (e : {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e})
    (he : (m.ccomp cap hc B hdiam hdeg).side p = some e) :
    label (RawDecomposition.dart (m.word cap hc B hdiam hdeg) p) =
      if (m.ccomp cap hc B hdiam hdeg).reverse e then
        inv (label (RawDecomposition.dart (m.word cap hc B hdiam hdeg)
          ((m.ccomp cap hc B hdiam hdeg).pairing.partner p)))
      else label (RawDecomposition.dart (m.word cap hc B hdiam hdeg)
        ((m.ccomp cap hc B hdiam hdeg).pairing.partner p)) := by
  obtain ⟨hp, he'⟩ := m.ccomp_side cap hc B hdiam hdeg he
  obtain ⟨h1, h2, h3⟩ := m.kept_side cap hc he'
  have hg := m.compatible _ h1 h2
  rw [← ExtendComparisons.embed_project (m.grow cap hc B hdiam hdeg) p hp]
  change label (RawDecomposition.dart (fun q => m.kseg cap hc q ++ m.tail cap hc B hdiam hdeg q) _) =
    if true then
      inv (label (RawDecomposition.dart _
        (ExtendComparisons.partner (m.Ck cap hc) (m.grow cap hc B hdiam hdeg) _)))
    else label (RawDecomposition.dart _
      (ExtendComparisons.partner (m.Ck cap hc) (m.grow cap hc B hdiam hdeg) _))
  rw [ExtendComparisons.partner_embed, WordPositions.dart_prefix, WordPositions.dart_prefix,
    m.kdart, m.kdart, h3, ite_eq_left rfl, hg, hinv]

variable (hinv : Function.Involutive inv)

/-- The prepared system: kept segments, closed by short closures, with the kept comparisons. -/
noncomputable def closed : GPathSystem Γ label inv isRoot where
  P := m.Kept cap
  E := {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e}
  fP := inferInstance
  fE := inferInstance
  paths := m.word cap hc B hdiam hdeg
  nonempty := m.word_nonempty cap hc B hdiam hdeg
  root := m.rootK cap hc
  path_chain := m.word_chain cap hc B hdiam hdeg
  cyclic_chain := m.word_cyclic cap hc B hdiam hdeg
  comparisons := m.ccomp cap hc B hdiam hdeg
  lower e := m.lower cap hc e.val
  upper e := m.upper cap hc e.val
  lower_eq e := m.lower_eq cap hc e.val
  upper_eq e := m.upper_eq cap hc e.val
  lower_le e := m.lower_le cap hc e.val
  upper_le := m.ccomp_upper_le cap hc B hdiam hdeg
  reduced := m.ccomp_reduced cap hc B hdiam hdeg
  root_start := m.root_start' cap hc B hdiam hdeg
  compatible := m.ccomp_compatible cap hc B hdiam hdeg hinv

/-! ### Counting for the prepared system -/

lemma closed_fixed :
    (Finset.univ.filter (fun p => (m.closed cap hc B hdiam hdeg hinv).comparisons.pairing.partner p = p)).card ≤
      m.outerLength + ∑ q, (m.tail cap hc B hdiam hdeg q).length := by
  have h := ExtendComparisons.fixed_card (m.Ck cap hc) (m.grow cap hc B hdiam hdeg)
  have hn := WordPositions.new_card (m.kseg cap hc) (m.tail cap hc B hdiam hdeg)
  have hk := m.kept_fixed_le cap hc
  have key := h.le.trans (Nat.add_le_add (by convert hk using 3) hn.le)
  convert key using 3
  all_goals first | exact Iff.rfl | rfl

lemma closed_old (p : Position (fun t => ((m.closed cap hc B hdiam hdeg hinv).paths t).length))
    (hp : (m.closed cap hc B hdiam hdeg hinv).comparisons.pairing.partner p ≠ p) :
    p.2.val ∈ positions 0 (BalancedWords.old m.w cap p.1.val) := by
  have hh := WordPositions.nonfixed_old (m.kseg cap hc) (m.tail cap hc B hdiam hdeg) (m.Ck cap hc) p hp
  convert hh using 2
  exact_mod_cast (m.kseg_length cap hc p.1).symm

include hc in
lemma kept_old_sum : (∑ q : m.Kept cap, BalancedWords.old m.w cap q.val) = m.keptLength := by
  have hs : ∑ p ∈ Finset.univ.filter (m.keepP cap), BalancedWords.old m.w cap p =
      ∑ q : m.Kept cap, BalancedWords.old m.w cap q.val :=
    Finset.sum_subtype _ (fun p => by simp) _
  rw [← hs, Finset.sum_filter, Fintype.sum_sigma, keptLength, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : m.keep t
  · simp only [keepP, ht, ite_true]
    exact BalancedPieces.sizes_sum (h := (m.w t).length) hc
  · simp [keepP, ht]

lemma tail_charge (hcap : 6 ≤ cap) (tailCap : ℕ)
    (htail : ∀ q, (m.tail cap hc B hdiam hdeg q).length ≤ tailCap) :
    cap * (∑ q, (m.tail cap hc B hdiam hdeg q).length) ≤ 3 * tailCap * m.keptLength := by
  let f : m.Piece cap → ℕ := fun p =>
    if h : m.keepP cap p then (m.tail cap hc B hdiam hdeg ⟨p, h⟩).length else 0
  have hsum : (∑ q, (m.tail cap hc B hdiam hdeg q).length) = ∑ p, f p := by
    have h1 : (∑ q : m.Kept cap, (m.tail cap hc B hdiam hdeg q).length) = ∑ q : m.Kept cap, f q.val := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [f, dite_eq_left q.property]
    have hs : ∑ p ∈ Finset.univ.filter (m.keepP cap), f p = ∑ q : m.Kept cap, f q.val :=
      Finset.sum_subtype _ (fun p => by simp) f
    rw [h1, ← hs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : m.keepP cap p
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      simp only [f, dite_eq_right h]
  rw [hsum, Fintype.sum_sigma, Finset.mul_sum, keptLength, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases hk : m.keep t
  · rw [ite_eq_left hk]
    by_cases hs : (m.w t).length ≤ cap
    · have he : ∀ i : Fin (BalancedPieces.number (m.w t).length cap), f ⟨t, i⟩ = 0 := by
        intro i
        show (if h : m.keepP cap ⟨t, i⟩ then (m.tail cap hc B hdiam hdeg ⟨⟨t, i⟩, h⟩).length else 0) = 0
        rw [dite_eq_left (show m.keepP cap ⟨t, i⟩ from hk),
          m.tail_short cap hc B hdiam hdeg ⟨⟨t, i⟩, hk⟩ hs]
        rfl
      simp only [he, Finset.sum_const_zero, Nat.mul_zero, Nat.zero_le]
    · have hsum' : (∑ i : Fin (BalancedPieces.number (m.w t).length cap), f ⟨t, i⟩) ≤
          BalancedPieces.number (m.w t).length cap * tailCap := by
        calc
          _ ≤ ∑ _i : Fin (BalancedPieces.number (m.w t).length cap), tailCap := by
            apply Finset.sum_le_sum
            intro i _
            show (if h : m.keepP cap ⟨t, i⟩ then (m.tail cap hc B hdiam hdeg ⟨⟨t, i⟩, h⟩).length
              else 0) ≤ tailCap
            rw [dite_eq_left (show m.keepP cap ⟨t, i⟩ from hk)]
            exact htail _
          _ = _ := by simp
      have hcount := BalancedPieces.number_charge (h := (m.w t).length) hcap
      rw [ite_eq_left (show cap < (m.w t).length by omega)] at hcount
      have ha := Nat.mul_le_mul_left cap hsum'
      have hb := Nat.mul_le_mul_right tailCap hcount
      nlinarith
  · have he : ∀ i : Fin (BalancedPieces.number (m.w t).length cap), f ⟨t, i⟩ = 0 := by
      intro i
      show (if h : m.keepP cap ⟨t, i⟩ then (m.tail cap hc B hdiam hdeg ⟨⟨t, i⟩, h⟩).length
        else 0) = 0
      rw [dite_eq_right (show ¬m.keepP cap ⟨t, i⟩ from hk)]
    simp only [he, Finset.sum_const_zero, Nat.mul_zero, ite_eq_right hk, le_refl]

/-! ### The separator on kept pieces -/

def split_mono {W : Type} [DecidableEq W] {R Q : W → W → Prop} {S : Finset W}
    (h : ∀ p q, p ≠ q → Q p q → R p q) (P : RecursiveSeparator.Split R S) :
    RecursiveSeparator.Split Q S where
  remove := P.remove
  parts := P.parts
  remove_subset := P.remove_subset
  cover := P.cover
  disjoint := P.disjoint
  closed := by
    intro b hb x hx y hy hq
    by_cases he : x = y
    · simpa only [← he] using hx
    · exact P.closed b hb x hx y hy (h x y he hq)
  size := P.size
  cost := P.cost

lemma closed_rel {p q : m.Kept cap} (hpq : p ≠ q)
    (h : PairingClusters.Rel (fun z : Position (fun t => ((m.closed cap hc B hdiam hdeg hinv).paths t).length) => z.1)
      (m.closed cap hc B hdiam hdeg hinv).comparisons.pairing.partner p q) :
    PairingClusters.Rel (fun z : Position (BalancedRotation.len m.w cap hc) => z.1)
      (m.α' cap hc) p.val q.val := by
  have h' := (ExtendComparisons.rel_iff (m.Ck cap hc) (m.grow cap hc B hdiam hdeg) hpq).mp h
  obtain ⟨x, hx, hy⟩ := h'
  have hne : (m.Ck cap hc).pairing.partner x ≠ x := by
    intro he
    rw [he, hx] at hy
    exact hpq hy
  have hk : m.keepP cap ((m.comparisons cap hc).pairing.partner (RestrictComparisons.embed _ x)).1 := by
    by_contra hk
    exact hne (RestrictComparisons.partner_no (m.comparisons cap hc) (m.keepP cap) x hk)
  have himg := RestrictComparisons.partner_image_yes (m.comparisons cap hc) (m.keepP cap) x hk
  refine ⟨RestrictComparisons.embed _ x, by simp [RestrictComparisons.embed, hx], ?_⟩
  rw [← m.comparisons_partner, ← himg]
  change (RestrictComparisons.partner (m.comparisons cap hc) (m.keepP cap) x).1.val = q.val
  exact congrArg Subtype.val hy

lemma segment_pos (p : m.Piece cap) : 0 < BalancedRotation.len m.w cap hc p :=
  List.length_pos_iff.mpr (BalancedWords.segment_nonempty m.w cap hc m.nonempty p)

lemma segmented_genusZero :
    MapEuler.GenusZero (BoundaryRotation.perm (BalancedRotation.len m.w cap hc)) (m.α' cap hc) :=
  BalancedGenus.genusZero m.w cap hc m.α m.involutive m.genusZero

/-- The sharp one-step separator for every set of kept pieces of the prepared system.
The decidable-equality instance is left implicit so that it unifies with the one expected by
the caller. -/
theorem oneStep {inst : DecidableEq (m.Kept cap)} (S' : Finset (m.Kept cap)) :
    Nonempty (@RecursiveSeparator.Split (m.Kept cap) inst
      (PairingClusters.Rel (fun z : Position (fun t => ((m.closed cap hc B hdiam hdeg hinv).paths t).length) => z.1)
        (m.closed cap hc B hdiam hdeg hinv).comparisons.pairing.partner) S') := by
  let M := BoundaryRotation.model (BalancedRotation.len m.w cap hc) (m.segment_pos cap hc)
    (m.α' cap hc) (m.α'_involutive cap hc) (m.segmented_genusZero cap hc)
  let s : Set (m.Piece cap) := {p | m.keepP cap p}
  let M' := M.induced s
  let f : m.Kept cap ≃ s := Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  obtain ⟨P⟩ := M'.split (S'.map f.toEmbedding)
  have P' : @RecursiveSeparator.Split (m.Kept cap) inst
      (fun a b => a ≠ b ∧
        PairingClusters.Rel (fun z : Position (fun t => ((m.closed cap hc B hdiam hdeg hinv).paths t).length) => z.1)
          (m.closed cap hc B hdiam hdeg hinv).comparisons.pairing.partner a b)
      ((S'.map f.toEmbedding).map f.symm.toEmbedding) :=
    (RecursiveSeparator.Split.changeDecidableEq P).map f.symm.toEmbedding (by
    intro v w hvw
    obtain ⟨hne, hrel⟩ := hvw
    change v.val ≠ w.val ∧ PairingClusters.Rel (fun x => x.1) (m.α' cap hc) v.val w.val
    refine ⟨fun h => hne (congrArg f.symm (Subtype.ext h)), ?_⟩
    exact m.closed_rel cap hc B hdiam hdeg hinv hne hrel)
  have hS : (S'.map f.toEmbedding).map f.symm.toEmbedding = S' := by
    rw [Finset.map_map]
    ext x
    simp
  rw [hS] at P'
  exact ⟨split_mono (fun p q hpq hq => ⟨hpq, hq⟩) P'⟩

end MapSystem

end

end Kaplansky.Exclusion
