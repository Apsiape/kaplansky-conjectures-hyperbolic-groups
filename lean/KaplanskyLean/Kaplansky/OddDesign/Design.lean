import Kaplansky.OddDesign.Plane
import Kaplansky.OddDesign.Params
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Common
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# The types of Section 7 (Def 7.1) and their congruences (Lemma 7.2)

Fix a prime `p` and a finite field `K` with `|K| = q = p^5` (later `K = GaloisField p 5`).

* The ordinary letters are the points of `PG(2,K)`, the extra letters the points of
  `PG(2,ZMod p)`; `Letter K p := Pt K ⊕ Pt (ZMod p)`.
* A block is the complement `E ∖ ℓ₀` of a line `ℓ₀` of `PG(2,p)` (`block ℓ₀`).
* Non-root types are indexed by `Ty K p := Ln K × Option (Ln (ZMod p))`:
  `(ℓ, none) ↦ ℓ` and `(ℓ, some ℓ₀) ↦ ℓ ∪ (E ∖ ℓ₀)` (`typeSet`).
* The root type is `S_r = ℓ_r ∪ E` with `ℓ_r` the line `Z = 0` (`rootSet`).

Lemma 7.2 (`cong_types`, `cong_root_type`, `rootSet_card_mod`): `|τ ∩ τ'| ≡ 1 (mod p)` unless
`τ = τ' = S_r`, and `|S_r| = q+1+s ≡ 2 (mod p)`; a non-root type has `q+1` or `q+1+p^2` letters.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable (p : ℕ) [Fact p.Prime]

/-- The alphabet `T = O ⊔ E`: ordinary letters (points of `PG(2,q)`) and extra letters
(points of `PG(2,p)`). -/
abbrev Letter := Pt K ⊕ Pt (ZMod p)

/-- Extra letters. -/
def IsExtra (t : Letter K p) : Prop := t.isRight = true

instance : DecidablePred (IsExtra K p) := fun t => inferInstanceAs (Decidable (t.isRight = true))

@[simp] theorem isExtra_inl (x : Pt K) : ¬ IsExtra K p (Sum.inl x) := by simp [IsExtra]
@[simp] theorem isExtra_inr (e : Pt (ZMod p)) : IsExtra K p (Sum.inr e) := by simp [IsExtra]

/-- A block: the complement `E ∖ ℓ₀` of a line of `PG(2,p)`. -/
def block (ℓ₀ : Ln (ZMod p)) : Finset (Pt (ZMod p)) := univ.filter (fun e => ¬ Inc e ℓ₀)

@[simp] theorem mem_block {e : Pt (ZMod p)} {ℓ₀ : Ln (ZMod p)} : e ∈ block p ℓ₀ ↔ ¬ Inc e ℓ₀ := by
  simp [block]

/-- The extra part of a non-root type. -/
def extraPart : Option (Ln (ZMod p)) → Finset (Pt (ZMod p))
  | none => ∅
  | some ℓ₀ => block p ℓ₀

/-- Non-root type indices: a line `ℓ` of `PG(2,q)` and an optional block. -/
abbrev Ty := Ln K × Option (Ln (ZMod p))

/-- The letter set of a non-root type: `ℓ` or `ℓ ∪ D`. -/
def typeSet (τ : Ty K p) : Finset (Letter K p) := (points τ.1).disjSum (extraPart p τ.2)

/-- The line `ℓ_r` of the root type (the line `Z = 0`). -/
def lineR : Ln K := .infty

/-- The root type `S_r = ℓ_r ∪ E`. -/
def rootSet : Finset (Letter K p) := (points (lineR K)).disjSum univ

/-! ### Counting in `PG(2,p)` -/

variable {p}

theorem card_zmod : Fintype.card (ZMod p) = p := ZMod.card p

theorem prime_two_le : 2 ≤ p := (Fact.out : p.Prime).two_le

/-- `PG(2,p)` has `s = p^2+p+1` points. -/
theorem card_pt_zmod : Fintype.card (Pt (ZMod p)) = s p := by
  rw [card_pt, card_zmod]; rfl

theorem card_ln_zmod : Fintype.card (Ln (ZMod p)) = s p := by
  rw [card_ln, card_zmod]; rfl

/-- A block has `p^2` points. -/
theorem card_block (ℓ₀ : Ln (ZMod p)) : (block p ℓ₀).card = p ^ 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Pt (ZMod p))))
    (fun e => Inc e ℓ₀)
  rw [card_univ, card_pt_zmod] at h
  have h2 : (univ.filter (fun e => Inc e ℓ₀)).card = p + 1 := by
    have := card_points ℓ₀
    rw [card_zmod] at this
    exact this
  unfold block
  unfold s at h
  omega

/-- Two distinct blocks meet in `p^2 - p = p(p-1)` points. -/
theorem card_block_inter {ℓ₀ ℓ₁ : Ln (ZMod p)} (h : ℓ₀ ≠ ℓ₁) :
    (block p ℓ₀ ∩ block p ℓ₁).card = p * (p - 1) := by
  have e1 : block p ℓ₀ ∩ block p ℓ₁ = univ \ (points ℓ₀ ∪ points ℓ₁) := by
    ext e; simp [block, not_or]
  have hu := Finset.card_union_add_card_inter (points ℓ₀) (points ℓ₁)
  rw [card_points, card_points, card_points_inter h, card_zmod] at hu
  rw [e1, card_sdiff_of_subset (subset_univ _), card_univ, card_pt_zmod]
  have hp := prime_two_le (p := p)
  unfold s
  have : (points ℓ₀ ∪ points ℓ₁).card = 2 * p + 1 := by omega
  rw [this]
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

/-- Every extra letter lies in `p^2` blocks. -/
theorem card_blocks_containing (e : Pt (ZMod p)) :
    (univ.filter (fun ℓ₀ : Ln (ZMod p) => e ∈ block p ℓ₀)).card = p ^ 2 := by
  simp only [mem_block]
  rw [card_lines_compl, card_zmod]

/-- Two distinct extra letters lie together in `p^2 - p = p(p-1)` blocks. -/
theorem card_blocks_containing_two {e e' : Pt (ZMod p)} (h : e ≠ e') :
    (univ.filter (fun ℓ₀ : Ln (ZMod p) => e ∈ block p ℓ₀ ∧ e' ∈ block p ℓ₀)).card =
      p * (p - 1) := by
  have e1 : univ.filter (fun ℓ₀ : Ln (ZMod p) => e ∈ block p ℓ₀ ∧ e' ∈ block p ℓ₀) =
      univ \ (lines e ∪ lines e') := by
    ext ℓ; simp [block, not_or]
  have hu := Finset.card_union_add_card_inter (lines e) (lines e')
  rw [card_lines, card_lines, card_lines_inter h, card_zmod] at hu
  rw [e1, card_sdiff_of_subset (subset_univ _), card_univ, card_ln_zmod]
  have hp := prime_two_le (p := p)
  unfold s
  have : (lines e ∪ lines e').card = 2 * p + 1 := by omega
  rw [this]
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

/-! ### Lemma 7.2 -/

theorem card_K (K : Type) [Fintype K] (p : ℕ) [hK : Fact (Fintype.card K = q p)] :
    Fintype.card K = q p := hK.out

variable {K}
variable [hK : Fact (Fintype.card K = q p)]

theorem disjSum_inter {α β : Type*} [DecidableEq α] [DecidableEq β] (a b : Finset α)
    (c d : Finset β) : a.disjSum c ∩ b.disjSum d = (a ∩ b).disjSum (c ∩ d) := by
  ext x; cases x <;> simp

/-- `|T| = v + s` is even (Def 7.1), since `v` and `s` are odd. -/
theorem card_letter : Fintype.card (Letter K p) = v p + s p := by
  rw [Fintype.card_sum, card_pt, card_K K p, card_pt_zmod]; rfl

theorem even_card_letter : Even (Fintype.card (Letter K p)) := by
  rw [card_letter]
  have h1 : v p % 2 = 1 := by
    unfold v; have := Nat.even_mul_succ_self (q p)
    rw [Nat.even_iff] at this
    have : q p ^ 2 + q p = q p * (q p + 1) := by ring
    omega
  have h2 : s p % 2 = 1 := by
    unfold s; have := Nat.even_mul_succ_self p
    rw [Nat.even_iff] at this
    have : p ^ 2 + p = p * (p + 1) := by ring
    omega
  rw [Nat.even_iff]; omega

/-- Lines of `PG(2,q)` meet in `1` or `q+1` points. -/
theorem card_line_inter (ℓ ℓ' : Ln K) :
    (points ℓ ∩ points ℓ').card = if ℓ = ℓ' then q p + 1 else 1 := by
  rw [card_points_inter_eq, card_K K p]

/-- `n % p = 1` whenever `n = 1 + p k`. -/
theorem mod_eq_one_of (n k : ℕ) (h : n = 1 + p * k) : n % p = 1 := by
  subst h
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (prime_two_le (p := p))

/-- The ordinary parts meet in `1 + p k` letters. -/
theorem exists_line_inter (ℓ ℓ' : Ln K) : ∃ k, (points ℓ ∩ points ℓ').card = 1 + p * k := by
  rw [card_line_inter (p := p)]
  split_ifs
  · exact ⟨p ^ 4, by simp only [q]; ring⟩
  · exact ⟨0, by ring⟩

/-- Two extra parts of non-root types meet in a multiple of `p` letters. -/
theorem exists_extra_inter (o o' : Option (Ln (ZMod p))) :
    ∃ k, (extraPart p o ∩ extraPart p o').card = p * k := by
  rcases o with _ | ℓ₀ <;> rcases o' with _ | ℓ₁
  · exact ⟨0, by simp [extraPart]⟩
  · exact ⟨0, by simp [extraPart]⟩
  · exact ⟨0, by simp [extraPart]⟩
  · simp only [extraPart]
    by_cases h : ℓ₀ = ℓ₁
    · subst h; rw [inter_self, card_block]; exact ⟨p, by ring⟩
    · rw [card_block_inter h]; exact ⟨p - 1, rfl⟩

theorem card_typeSet_inter (τ τ' : Ty K p) :
    (typeSet K p τ ∩ typeSet K p τ').card =
      (points τ.1 ∩ points τ'.1).card + (extraPart p τ.2 ∩ extraPart p τ'.2).card := by
  rw [typeSet, typeSet, disjSum_inter, card_disjSum]

/-- **Lemma 7.2**, non-root pairs: `|τ ∩ τ'| ≡ 1 (mod p)`. -/
theorem cong_types (τ τ' : Ty K p) : (typeSet K p τ ∩ typeSet K p τ').card % p = 1 := by
  obtain ⟨k, hk⟩ := exists_line_inter (p := p) τ.1 τ'.1
  obtain ⟨k', hk'⟩ := exists_extra_inter τ.2 τ'.2
  exact mod_eq_one_of _ (k + k') (by rw [card_typeSet_inter, hk, hk']; ring)

/-- **Lemma 7.2**, root against a non-root type: `|S_r ∩ τ| ≡ 1 (mod p)`. -/
theorem cong_root_type (τ : Ty K p) : (rootSet K p ∩ typeSet K p τ).card % p = 1 := by
  obtain ⟨k, hk⟩ := exists_line_inter (p := p) (lineR K) τ.1
  have hk' : ∃ k', ((univ : Finset (Pt (ZMod p))) ∩ extraPart p τ.2).card = p * k' := by
    rcases τ.2 with _ | ℓ₀
    · exact ⟨0, by simp [extraPart]⟩
    · exact ⟨p, by simp only [extraPart, univ_inter, card_block]; ring⟩
  obtain ⟨k', hk'⟩ := hk'
  refine mod_eq_one_of _ (k + k') ?_
  rw [rootSet, typeSet, disjSum_inter, card_disjSum, hk, hk']
  ring

/-- `|τ ∩ S_r| ≡ 1 (mod p)`. -/
theorem cong_type_root (τ : Ty K p) : (typeSet K p τ ∩ rootSet K p).card % p = 1 := by
  rw [inter_comm]; exact cong_root_type τ

/-- The root type has `q+1+s` letters. -/
theorem card_rootSet : (rootSet K p).card = q p + 1 + s p := by
  rw [rootSet, card_disjSum, card_points, card_univ, card_pt_zmod, card_K K p]

/-- **Lemma 7.2**, the root against itself: `|S_r| ≡ 2 (mod p)`. -/
theorem rootSet_card_mod : (rootSet K p).card % p = 2 % p := by
  rw [card_rootSet, q, s]
  have : p ^ 5 + 1 + (p ^ 2 + p + 1) = 2 + p * (p ^ 4 + p + 1) := by ring
  rw [this, Nat.add_mul_mod_self_left]

/-- A non-root type has `q+1` or `q+1+p^2` letters. -/
theorem card_typeSet (τ : Ty K p) :
    (typeSet K p τ).card = q p + 1 + (if τ.2.isSome then p ^ 2 else 0) := by
  rw [typeSet, card_disjSum, card_points, card_K K p]
  rcases τ with ⟨ℓ, _ | ℓ₀⟩
  · simp [extraPart]
  · simp [extraPart, card_block]

theorem card_typeSet_bounds (τ : Ty K p) :
    q p + 1 ≤ (typeSet K p τ).card ∧ (typeSet K p τ).card ≤ q p + 1 + s p := by
  rw [card_typeSet]
  constructor
  · omega
  · split_ifs <;> simp only [s] <;> omega

/-- No non-root type equals the root type (they differ on the extra letters). -/
theorem typeSet_ne_rootSet (τ : Ty K p) : typeSet K p τ ≠ rootSet K p := by
  intro h
  have h1 := card_typeSet τ
  rw [h, card_rootSet] at h1
  have hp := prime_two_le (p := p)
  split_ifs at h1 <;> simp only [s] at h1 <;> nlinarith

end Kaplansky.OddDesign
