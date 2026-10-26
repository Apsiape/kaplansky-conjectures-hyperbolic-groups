import Kaplansky.Exclusion.Prepared
import OAI.Algebra.GroupRing.ConePicture

/-!
# The key estimate (paper Proposition 4.4, `prop:key`)

Let `Γ` be `(ε,d,λ)`-pattern-free at scale `L`, and let `m` be the boundary map of a reduced cone
picture (`MapSystem`), with at least one cyclic graph boundary. Then

* if `m` has no root: `13/16 · ε · H ≤ ℓ_∞`, i.e. `H ≤ 16/(13ε) · ℓ_∞` (`key_free`);
* `m` cannot be rooted (`key_rooted`) — rooted maps have no outer boundary.

Here `H = keptLength` is the cone length (plus the rooted path) and `ℓ_∞ = outerLength`.
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
variable {ε d lam : ℝ} {L : ℕ}

/-- The closure constant absorbs the diameter and the logarithmic loop length. -/
lemma closure_le (pf : PatternFree Γ label inv isRoot ε d lam L) :
    ⌊d * L⌋₊ + 4 * (Nat.log 2 (Fintype.card V) + 1) ≤ closureConst d lam * L := by
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast pf.scale
  have hd : (1 : ℝ) ≤ d := pf.one_le_d
  have hlam : (1 : ℝ) ≤ lam := pf.one_le_lam
  have hlog : (Nat.log 2 (Fintype.card V) : ℝ) ≤ lam * L := by
    by_cases hV : Fintype.card V = 0
    · rw [hV, Nat.log_zero_right, Nat.cast_zero]
      exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
    · have h1 : (Nat.log 2 (Fintype.card V) : ℝ) ≤ Real.logb 2 (Fintype.card V) := by
        have := Real.natLog_le_logb (Fintype.card V) 2
        exact_mod_cast this
      exact h1.trans pf.size
  have hfl : (⌊d * L⌋₊ : ℝ) ≤ d * L := Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have hceil : d + 4 * lam + 8 ≤ (closureConst d lam : ℝ) := Nat.le_ceil _
  have hgoal : ((⌊d * L⌋₊ + 4 * (Nat.log 2 (Fintype.card V) + 1) : ℕ) : ℝ) ≤
      ((closureConst d lam * L : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hceil (by linarith : (0 : ℝ) ≤ L)]
  exact_mod_cast hgoal

variable (m : MapSystem Γ label inv isRoot) (pf : PatternFree Γ label inv isRoot ε d lam L)
include pf

/-- **Key estimate** for a boundary map in a pattern-free graph (paper Proposition 4.4).
`S` is the budget for one short exceptional cluster: `0` without a root, `H/2` with a root. -/
theorem key_estimate (hord : ∃ t, m.keep t ∧ m.root ≠ some t) (S : ℝ) (hS : 0 ≤ S)
    (hSroot : m.root ≠ none → (m.keptLength : ℝ) / 2 ≤ S)
    (hgap : (m.outerLength : ℝ) / ε + S < 13 / 16 * m.keptLength) : False := by
  set D₀ := closureConst d lam
  set U := PlanarParameters.U ε D₀
  set cap := U * L with hcapU
  have hU : 3 ≤ U := PlanarParameters.U_ge ε D₀
  have hL3 : 3 ≤ L := pf.scale
  have hcap6 : 6 ≤ cap := by
    show 6 ≤ U * L
    nlinarith
  have hc : 0 < cap := by omega
  set B := ⌊d * L⌋₊
  have hdiam : ∀ a b, (ShortClosure.simpleGraph Γ).Reachable a b →
      (ShortClosure.simpleGraph Γ).dist a b ≤ B := fun a b h =>
    Nat.le_floor (pf.diameter a b h)
  have hdeg := pf.degree
  have hinv := pf.inv_involutive
  have hε := pf.eps_pos
  have hε1 := pf.eps_le
  let s := m.closed cap hc B hdiam hdeg hinv
  set H := m.keptLength
  set n := m.outerLength
  -- an ordinary graph boundary
  obtain ⟨t₀, hk₀, hr₀⟩ := hord
  have hLt : L ≤ (m.w t₀).length :=
    pf.girth _ (m.nonempty t₀) (m.chain t₀ hk₀) (m.cyclic t₀ hk₀ hr₀)
  have hHt : (m.w t₀).length ≤ H :=
    Finset.single_le_sum (f := fun t => (m.w t).length) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₀⟩)
  have hHL : L ≤ H := hLt.trans hHt
  have hH₀ : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hL0 : 0 < L := by omega
  have hnH : (n : ℝ) ≤ H := by
    have h1 : (n : ℝ) / ε < 13 / 16 * H := by linarith
    have h2 : (n : ℝ) ≤ (n : ℝ) / ε := by
      rw [le_div_iff₀ hε]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith
    linarith
  -- lower bound for the old length of a non-root kept piece
  have old_lower : ∀ q : m.Kept cap, m.rootK cap hc ≠ some q → L ≤ BalancedWords.old m.w cap q.val := by
    intro q hq
    by_cases hs : (m.w q.val.1).length ≤ cap
    · have hold : BalancedWords.old m.w cap q.val = (m.w q.val.1).length := by
        simp only [BalancedWords.old, BalancedPieces.sizes, ite_eq_left hs]
      rw [hold]
      have hnr : m.root ≠ some q.val.1 := fun he => hq ((m.rootK_eq_some cap hc q).mpr ⟨he, hs⟩)
      exact pf.girth _ (m.nonempty _) (m.chain _ q.property) (m.cyclic _ q.property hnr)
    · have hh := BalancedPieces.sizes_lower_long hcap6 (by omega : cap < (m.w q.val.1).length) q.val.2
      change L ≤ BalancedPieces.sizes (m.w q.val.1).length cap q.val.2
      have : U * L ≤ 3 * BalancedPieces.sizes (m.w q.val.1).length cap q.val.2 := hh
      have h3 := Nat.mul_le_mul_right L hU
      linarith
  have hsumold : (∑ q : m.Kept cap, BalancedWords.old m.w cap q.val) = H := m.kept_old_sum cap hc
  -- pieces
  have hpiecesN : Fintype.card (m.Kept cap) * L ≤ H + L := by
    have hh := SingleException.cardinal_charge (m.rootK cap hc)
      (fun q => BalancedWords.old m.w cap q.val) L old_lower
    rw [hsumold] at hh
    exact hh
  have hpieces : (Fintype.card s.P : ℝ) * L ≤ 2 * (H : ℝ) := by
    have : Fintype.card (m.Kept cap) * L ≤ 2 * H := by omega
    exact_mod_cast this
  -- comparisons
  have hcount := m.sides_count cap hc hcap6
  have hcompare : (Fintype.card s.E : ℝ) / 2 ≤ (192 : ℝ) / (16 * L) * H := by
    change (Fintype.card {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e} : ℝ) / 2 ≤ _
    have hb := m.outer_le
    have key : Fintype.card {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e} * L
        ≤ 24 * H := by
      set E := Fintype.card {e // RestrictComparisons.Active (m.comparisons cap hc) (m.keepP cap) e}
      set K := Fintype.card (m.Kept cap)
      set b := (Finset.univ.filter (fun t => ¬m.keep t)).card
      by_cases hroot : m.root = none
      · have hall : ∀ q : m.Kept cap, L ≤ BalancedWords.old m.w cap q.val := by
          intro q
          apply old_lower
          simp [rootK, hroot]
        have hKL : K * L ≤ H := by
          rw [← hsumold]
          calc
            K * L = ∑ _q : m.Kept cap, L := by simp [K]
            _ ≤ _ := Finset.sum_le_sum fun q _ => hall q
        have hn' : n ≤ H := by exact_mod_cast hnH
        have e1 : E * L * U ≤ 10 * K * L * U + 10 * b * L * U + 6 * n := by
          have : E * cap ≤ 10 * K * cap + 10 * b * cap + 6 * n := hcount
          change E * (U * L) ≤ 10 * K * (U * L) + 10 * b * (U * L) + 6 * n at this
          nlinarith
        have e2 := Nat.mul_le_mul_right U hKL
        have e3 := Nat.mul_le_mul_right (L * U) hb
        have e4 := Nat.mul_le_mul_right U hHL
        have e5 := Nat.mul_le_mul_left H hU
        have e6 : E * L * U ≤ 24 * H * U := by nlinarith
        exact Nat.le_of_mul_le_mul_right e6 (by omega)
      · have hallk := m.root_only hroot
        have hb0 : b = 0 := by
          simp only [b]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro t _ h; exact h (hallk t)
        have hn0 : n = 0 := by
          change m.outerLength = 0
          unfold outerLength
          rw [Finset.sum_eq_zero]
          intro t ht
          exact absurd (hallk t) (Finset.mem_filter.mp ht).2
        have h0 : E * cap ≤ 10 * K * cap := by
          have := hcount
          rw [hb0, show m.outerLength = 0 from hn0] at this
          linarith
        have h1 : E ≤ 10 * K := by
          have : E * cap ≤ (10 * K) * cap := by linarith
          exact Nat.le_of_mul_le_mul_right this hc
        have h2 := Nat.mul_le_mul_right L h1
        nlinarith
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
    have hkey : ((Fintype.card {e // RestrictComparisons.Active (m.comparisons cap hc)
        (m.keepP cap) e} : ℕ) : ℝ) * L ≤ 24 * H := by exact_mod_cast key
    rw [show (192 : ℝ) / (16 * L) * H = 12 * H / L by ring, le_div_iff₀ hLr]
    linarith
  -- unpaired
  have htail : ∀ q, (m.tail cap hc B hdiam hdeg q).length ≤ D₀ * L := fun q =>
    (m.tail_bound cap hc B hdiam hdeg q).trans (closure_le pf)
  have hadded : ((Finset.univ.filter (fun p => s.comparisons.pairing.partner p = p)).card : ℝ) ≤
      3 * (D₀ : ℝ) / U * H + n := by
    have hf := m.closed_fixed cap hc B hdiam hdeg hinv
    have hcharge := m.tail_charge cap hc B hdiam hdeg hcap6 (D₀ * L) htail
    have hdiv := SingleException.divide_cast (U := U) (L := L) (D := D₀)
      (A := ∑ q, (m.tail cap hc B hdiam hdeg q).length) (H := H) (by omega) hL0
      hcharge
    have hf' : ((Finset.univ.filter (fun p => s.comparisons.pairing.partner p = p)).card : ℝ) ≤
        n + ∑ q, ((m.tail cap hc B hdiam hdeg q).length : ℝ) := by
      exact_mod_cast hf
    push_cast at hdiv
    linarith
  -- the short cluster
  have hroot' : ∀ q, s.root = some q → (s.paths q).length < L → ((s.paths q).length : ℝ) ≤ S := by
    intro q hq hlt
    have hs := (m.rootK_eq_some cap hc q).mp hq
    have hw : s.paths q = m.w q.val.1 := m.word_short cap hc B hdiam hdeg q hs.2
    rw [hw] at hlt ⊢
    have hS2 := hSroot (by rw [hs.1]; exact Option.some_ne_none _)
    have hne : q.val.1 ≠ t₀ := by
      intro he; rw [he] at hs; exact hr₀ hs.1
    have h2 := SingleException.two_mass (T := {t // m.keep t}) (fun t => (m.w t.val).length)
      ⟨q.val.1, q.property⟩ ⟨t₀, hk₀⟩ (fun h => hne (congrArg Subtype.val h))
    have hsub : (∑ t : {t // m.keep t}, (m.w t.val).length) = H := by
      have hs : ∑ t ∈ Finset.univ.filter m.keep, (m.w t).length =
          ∑ t : {t // m.keep t}, (m.w t.val).length :=
        Finset.sum_subtype _ (fun t => by simp) (fun t => (m.w t).length)
      rw [← hs]
      rfl
    have h2' : (m.w q.val.1).length + (m.w t₀).length ≤
        ∑ t : {t // m.keep t}, (m.w t.val).length := h2
    rw [hsub] at h2'
    have : 2 * (m.w q.val.1).length ≤ H := by omega
    have : (2 * (m.w q.val.1).length : ℝ) ≤ H := by exact_mod_cast this
    linarith
  have hlong : ∀ q, s.root ≠ some q → L ≤ (s.paths q).length := fun q hq =>
    (old_lower q hq).trans (m.old_le_word cap hc B hdiam hdeg q)
  have havoid : IsEmpty (GBoundedSystem Γ label inv isRoot (PlanarParameters.C ε D₀)
      (PlanarParameters.K ε D₀) (PlanarParameters.sides ε D₀) L ε) := by
    rw [← two_pairs]
    exact pf.avoid
  exact s.excluded_of_separator' L ε D₀ (H : ℝ) (n : ℝ) S (fun q => BalancedWords.old m.w cap q.val)
    hε hH₀ hL0
    (fun (q : m.Kept cap) => m.old_le_word cap hc B hdiam hdeg q)
    (fun (q : m.Kept cap) => BalancedWords.old_le m.w cap hcap6 q.val)
    (fun (q : m.Kept cap) => by
      change (m.kseg cap hc q ++ m.tail cap hc B hdiam hdeg q).length ≤ (U + D₀) * L
      rw [List.length_append, m.kseg_length]
      have h1 : BalancedWords.old m.w cap q.val ≤ U * L := BalancedWords.old_le m.w cap hcap6 q.val
      have h2 := htail q
      nlinarith)
    (by
      show (H : ℝ) ≤ ∑ t : m.Kept cap, ((BalancedWords.old m.w cap t.val : ℕ) : ℝ)
      rw [← Nat.cast_sum, hsumold])
    hpieces hadded (m.closed_old cap hc B hdiam hdeg hinv) hcompare hlong hS hroot' hgap
    (fun S' _ => m.oneStep cap hc B hdiam hdeg hinv S') havoid

/-- **Proposition 4.4, free case**: the cone length of a reduced capped picture is at most
`16/(13ε)` times the length of its outer word. -/
theorem key_free (hroot : m.root = none) (hord : ∃ t, m.keep t) :
    (13 / 16 : ℝ) * ε * m.keptLength ≤ m.outerLength := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t, ht⟩ := hord
  refine m.key_estimate pf ⟨t, ht, by simp [hroot]⟩ 0 le_rfl (fun h => absurd hroot h) ?_
  have hε := pf.eps_pos
  rw [add_zero, div_lt_iff₀ hε]
  linarith

/-- **Proposition 4.4, spherical and rooted cases**: no reduced spherical or rooted picture. -/
theorem key_closed (hord : ∃ t, m.keep t ∧ m.root ≠ some t) (hall : ∀ t, m.keep t) : False := by
  have hn : m.outerLength = 0 := by
    unfold outerLength
    rw [Finset.sum_eq_zero]
    intro t ht
    exact absurd (hall t) (Finset.mem_filter.mp ht).2
  obtain ⟨t, ht, hr⟩ := hord
  have hpos : 0 < m.keptLength :=
    lt_of_lt_of_le (List.length_pos_iff.mpr (m.nonempty t))
      (Finset.single_le_sum (f := fun t => (m.w t).length) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
  have hposR : (0 : ℝ) < m.keptLength := by exact_mod_cast hpos
  refine m.key_estimate pf ⟨t, ht, hr⟩ ((m.keptLength : ℝ) / 2) (by positivity) (fun _ => le_rfl) ?_
  rw [hn, Nat.cast_zero, zero_div, zero_add]
  linarith

end MapSystem

end

end Kaplansky.Exclusion
