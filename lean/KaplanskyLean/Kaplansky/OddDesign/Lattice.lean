import Kaplansky.OddDesign.Design

/-!
# The lattice `𝓛` and Lemma 7.3

Vectors are functions `Letter K p → ℤ`. The lattice `𝓛 ⊆ ℤ^T` is spanned by the indicators of
the non-root types; we record membership with explicit integer coefficients:
`InL w ↔ ∃ c : Ty K p → ℤ, comb c = w` where `comb c = ∑_τ c_τ 1_τ`.
For an involution `bar` of `T`, `InLL bar w` means `w ∈ 𝓛 + bar(𝓛)`, i.e. `w = U + V̄` with
`U, V ∈ 𝓛` and `V̄(t) = V(t̄)`.

Lemma 7.3:
* (a) `lattice_a`: `p^2 1_e = ∑_D 1_D - p ∑_{D ∌ e} 1_D`; `inL_q_single_extra`: `q 1_e ∈ 𝓛`;
* (b) `lattice_b`: `q (1_t - 1_{t'}) = ∑_{ℓ ∋ t} 1_ℓ - ∑_{ℓ ∋ t'} 1_ℓ ∈ 𝓛`;
* (c) `lattice_c_q`, `lattice_c_ord`: if `ē ∈ O` for some `e ∈ E`, then `q ℤ^T ⊆ 𝓛 + 𝓛̄`
  and `1_O ∈ 𝓛 + 𝓛̄`.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable (p : ℕ) [Fact p.Prime]

/-- Integer vectors on the alphabet. -/
abbrev Vec := Letter K p → ℤ

/-- The indicator vector of a set of letters. -/
def ind (S : Finset (Letter K p)) : Vec K p := fun t => if t ∈ S then 1 else 0

/-- `1_ℓ` for a line `ℓ` of `PG(2,q)`. -/
def lineVec (ℓ : Ln K) : Vec K p := Sum.elim (fun x => if Inc x ℓ then 1 else 0) 0

/-- `1_D` for the block `D = E ∖ ℓ₀`. -/
def blockVec (ℓ₀ : Ln (ZMod p)) : Vec K p := Sum.elim 0 (fun e => if Inc e ℓ₀ then 0 else 1)

/-- `1_t`. -/
def single (t : Letter K p) : Vec K p := fun t' => if t' = t then 1 else 0

/-- `1_O`. -/
def ordVec : Vec K p := Sum.elim 1 0

/-- `1_T`. -/
def allVec : Vec K p := fun _ => 1

/-- `∑_τ c_τ 1_τ`. -/
def comb (c : Ty K p → ℤ) : Vec K p := fun t => ∑ τ, c τ * ind K p (typeSet K p τ) t

/-- Membership in the lattice `𝓛` spanned by the non-root types. -/
def InL (w : Vec K p) : Prop := ∃ c : Ty K p → ℤ, comb K p c = w

/-- `w̄(t) = w(t̄)`. -/
def barV (bar : Letter K p → Letter K p) (w : Vec K p) : Vec K p := fun t => w (bar t)

/-- Membership in `𝓛 + 𝓛̄`. -/
def InLL (bar : Letter K p → Letter K p) (w : Vec K p) : Prop :=
  ∃ U V, InL K p U ∧ InL K p V ∧ w = U + barV K p bar V

variable {K p}

/-! ### Closure properties -/

theorem comb_add (c c' : Ty K p → ℤ) : comb K p (c + c') = comb K p c + comb K p c' := by
  ext t; simp [comb, add_mul, Finset.sum_add_distrib]

theorem comb_smul (n : ℤ) (c : Ty K p → ℤ) : comb K p (n • c) = n • comb K p c := by
  ext t; simp [comb, Finset.mul_sum, mul_assoc]

theorem InL.zero : InL K p 0 := ⟨0, by ext t; simp [comb]⟩

theorem InL.add {w w' : Vec K p} (h : InL K p w) (h' : InL K p w') : InL K p (w + w') := by
  obtain ⟨c, rfl⟩ := h; obtain ⟨c', rfl⟩ := h'
  exact ⟨c + c', comb_add c c'⟩

theorem InL.smul {w : Vec K p} (n : ℤ) (h : InL K p w) : InL K p (n • w) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨n • c, comb_smul n c⟩

theorem InL.neg {w : Vec K p} (h : InL K p w) : InL K p (-w) := by
  simpa using h.smul (-1)

theorem InL.sub {w w' : Vec K p} (h : InL K p w) (h' : InL K p w') : InL K p (w - w') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem InL.sum {ι : Type*} (s : Finset ι) (f : ι → Vec K p) (h : ∀ i ∈ s, InL K p (f i)) :
    InL K p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InL.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem InL.typeSet (τ : Ty K p) : InL K p (ind K p (typeSet K p τ)) := by
  refine ⟨fun τ' => if τ' = τ then 1 else 0, ?_⟩
  ext t
  simp [comb]

theorem ind_typeSet_inl (τ : Ty K p) (x : Pt K) :
    ind K p (typeSet K p τ) (Sum.inl x) = if Inc x τ.1 then 1 else 0 := by
  simp [ind, typeSet]

theorem ind_typeSet_inr (τ : Ty K p) (e : Pt (ZMod p)) :
    ind K p (typeSet K p τ) (Sum.inr e) = if e ∈ extraPart p τ.2 then 1 else 0 := by
  simp [ind, typeSet]

theorem lineVec_eq (ℓ : Ln K) : lineVec K p ℓ = ind K p (typeSet K p (ℓ, none)) := by
  ext t; cases t <;> simp [lineVec, ind, typeSet, extraPart]

theorem blockVec_eq (ℓ : Ln K) (ℓ₀ : Ln (ZMod p)) :
    blockVec K p ℓ₀ = ind K p (typeSet K p (ℓ, some ℓ₀)) - ind K p (typeSet K p (ℓ, none)) := by
  ext t; cases t <;> simp [blockVec, ind, typeSet, extraPart, block]

theorem InL.line (ℓ : Ln K) : InL K p (lineVec K p ℓ) := by
  rw [lineVec_eq]; exact InL.typeSet _

theorem InL.block (ℓ₀ : Ln (ZMod p)) : InL K p (blockVec K p ℓ₀) := by
  rw [blockVec_eq .infty]; exact (InL.typeSet _).sub (InL.typeSet _)

theorem InLL.of_InL {bar : Letter K p → Letter K p} {w : Vec K p} (h : InL K p w) :
    InLL K p bar w :=
  ⟨w, 0, h, InL.zero, by ext t; simp [barV]⟩

theorem InLL.of_bar {bar : Letter K p → Letter K p} {w : Vec K p} (h : InL K p w) :
    InLL K p bar (barV K p bar w) :=
  ⟨0, w, InL.zero, h, by ext t; simp⟩

theorem InLL.add {bar : Letter K p → Letter K p} {w w' : Vec K p} (h : InLL K p bar w)
    (h' : InLL K p bar w') : InLL K p bar (w + w') := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h
  obtain ⟨U', V', hU', hV', rfl⟩ := h'
  refine ⟨U + U', V + V', hU.add hU', hV.add hV', ?_⟩
  ext t; simp [barV]; ring

theorem InLL.smul {bar : Letter K p → Letter K p} {w : Vec K p} (n : ℤ) (h : InLL K p bar w) :
    InLL K p bar (n • w) := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h
  refine ⟨n • U, n • V, hU.smul n, hV.smul n, ?_⟩
  ext t; simp [barV]; ring

theorem InLL.neg {bar : Letter K p → Letter K p} {w : Vec K p} (h : InLL K p bar w) :
    InLL K p bar (-w) := by
  simpa using h.smul (-1)

theorem InLL.sub {bar : Letter K p → Letter K p} {w w' : Vec K p} (h : InLL K p bar w)
    (h' : InLL K p bar w') : InLL K p bar (w - w') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem InLL.sum {bar : Letter K p → Letter K p} {ι : Type*} (s : Finset ι) (f : ι → Vec K p)
    (h : ∀ i ∈ s, InLL K p bar (f i)) : InLL K p bar (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (InLL.of_InL (bar := bar) (InL.zero (K := K) (p := p)))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-! ### Lemma 7.3 (a) -/

/-- **Lemma 7.3(a)**: `p^2 1_e = ∑_D 1_D - p ∑_{D ∌ e} 1_D`; the blocks not containing `e` are
the complements of the lines through `e`. -/
theorem lattice_a (e : Pt (ZMod p)) :
    (p ^ 2 : ℤ) • single K p (Sum.inr e) =
      ∑ ℓ₀, blockVec K p ℓ₀ - (p : ℤ) • ∑ ℓ₀ ∈ lines e, blockVec K p ℓ₀ := by
  ext t
  rcases t with x | e'
  · simp [single, blockVec]
  · simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, single, blockVec,
      Sum.elim_inr, Sum.inr.injEq]
    have h1 : ∑ ℓ₀ : Ln (ZMod p), (if Inc e' ℓ₀ then (0 : ℤ) else 1) = (p : ℤ) ^ 2 := by
      have := card_lines_compl e'
      rw [card_zmod] at this
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
        mul_one, this]
      push_cast; ring
    have h2 : ∑ ℓ₀ ∈ lines e, (if Inc e' ℓ₀ then (0 : ℤ) else 1) =
        if e' = e then 0 else (p : ℤ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      have hf : (lines e).filter (fun ℓ₀ => ¬ Inc e' ℓ₀) = lines e \ lines e' := by
        ext ℓ; simp
      rw [hf]
      split_ifs with h
      · subst h; simp
      · rw [card_lines_sdiff (Ne.symm h), card_zmod]
    rw [h1, h2]
    split_ifs <;> ring

/-- **Lemma 7.3(a)**, literally: `p^2 1_e = ∑_{D ∈ 𝓓} 1_D - p ∑_{D ∌ e} 1_D`, the blocks being
indexed by their complementary lines. -/
theorem lattice_a' (e : Pt (ZMod p)) :
    (p ^ 2 : ℤ) • single K p (Sum.inr e) =
      ∑ ℓ₀, blockVec K p ℓ₀ -
        (p : ℤ) • ∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => e ∉ block p ℓ₀), blockVec K p ℓ₀ := by
  have : univ.filter (fun ℓ₀ => e ∉ block p ℓ₀) = lines e := by ext ℓ; simp
  rw [this, lattice_a]

/-- `q 1_e ∈ 𝓛` for an extra letter `e`. -/
theorem inL_q_single_extra (e : Pt (ZMod p)) :
    InL K p ((q p : ℤ) • single K p (Sum.inr e)) := by
  have h : (q p : ℤ) • single K p (Sum.inr e) =
      (p ^ 3 : ℤ) • ((p ^ 2 : ℤ) • single K p (Sum.inr e)) := by
    rw [smul_smul]; congr 1; simp [q]; ring
  rw [h, lattice_a]
  refine InL.smul _ (InL.sub (InL.sum _ _ fun ℓ₀ _ => InL.block ℓ₀) (InL.smul _ ?_))
  exact InL.sum _ _ fun ℓ₀ _ => InL.block ℓ₀

/-! ### Lemma 7.3 (b) -/

variable [Fact (Fintype.card K = q p)]

/-- The `q+1` lines through `t` cover `t` exactly `q+1` times and every other ordinary letter
once: `∑_{ℓ ∋ t} 1_ℓ = q 1_t + 1_O`. -/
theorem sum_lineVec_lines (t : Pt K) :
    ∑ ℓ ∈ lines t, lineVec K p ℓ = (q p : ℤ) • single K p (Sum.inl t) + ordVec K p := by
  ext t'
  rcases t' with x | e
  · simp only [Finset.sum_apply, lineVec, Sum.elim_inl, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, single, Sum.inl.injEq, ordVec, Pi.one_apply]
    rw [Finset.sum_boole]
    have hf : (lines t).filter (fun ℓ => Inc x ℓ) = lines t ∩ lines x := by
      ext ℓ; simp
    rw [hf]
    by_cases h : x = t
    · subst h; rw [inter_self, card_lines, card_K K p]; simp
    · rw [card_lines_inter (Ne.symm h)]; simp [h]
  · simp [lineVec, single, ordVec]

/-- **Lemma 7.3(b)**: `q (1_t - 1_{t'}) = ∑_{ℓ ∋ t} 1_ℓ - ∑_{ℓ ∋ t'} 1_ℓ`. -/
theorem lattice_b (t t' : Pt K) :
    (q p : ℤ) • (single K p (Sum.inl t) - single K p (Sum.inl t')) =
      ∑ ℓ ∈ lines t, lineVec K p ℓ - ∑ ℓ ∈ lines t', lineVec K p ℓ := by
  rw [sum_lineVec_lines, sum_lineVec_lines, smul_sub]
  abel

theorem inL_q_single_sub (t t' : Pt K) :
    InL K p ((q p : ℤ) • (single K p (Sum.inl t) - single K p (Sum.inl t'))) := by
  rw [lattice_b]
  exact (InL.sum _ _ fun ℓ _ => InL.line ℓ).sub (InL.sum _ _ fun ℓ _ => InL.line ℓ)

/-- Every ordinary letter lies on `q+1` lines: `∑_ℓ 1_ℓ = (q+1) 1_O`. -/
theorem sum_lineVec_all : ∑ ℓ, lineVec K p ℓ = ((q p : ℤ) + 1) • ordVec K p := by
  ext t
  rcases t with x | e
  · simp only [Finset.sum_apply, lineVec, Sum.elim_inl, Pi.smul_apply, smul_eq_mul, ordVec,
      Pi.one_apply, mul_one]
    rw [Finset.sum_boole]
    have := card_lines (F := K) x
    rw [card_K K p] at this
    simp only [lines] at this
    rw [this]; push_cast; ring
  · simp [lineVec, ordVec]

/-! ### Lemma 7.3 (c) -/

theorem barV_single (bar : Letter K p → Letter K p) (hbar : Function.Involutive bar)
    (t : Letter K p) : barV K p bar (single K p t) = single K p (bar t) := by
  ext t'
  simp only [barV, single]
  have : bar t' = t ↔ t' = bar t := by
    constructor
    · intro h; rw [← h, hbar]
    · intro h; rw [h, hbar]
  simp only [this]

theorem vec_eq_sum_single (d : Vec K p) : d = ∑ t, d t • single K p t := by
  ext t'
  simp [single, Finset.sum_apply]

/-- **Lemma 7.3(c)**, first part: if `ē ∈ O` for some `e ∈ E`, then `q ℤ^T ⊆ 𝓛 + 𝓛̄`. -/
theorem lattice_c_q (bar : Letter K p → Letter K p) (hbar : Function.Involutive bar)
    (e₀ : Pt (ZMod p)) (x₀ : Pt K) (h₀ : bar (Sum.inr e₀) = Sum.inl x₀) (d : Vec K p) :
    InLL K p bar ((q p : ℤ) • d) := by
  have hsingle : ∀ t, InLL K p bar ((q p : ℤ) • single K p t) := by
    intro t
    rcases t with x | e
    · have h1 : (q p : ℤ) • single K p (Sum.inl x) =
          (q p : ℤ) • (single K p (Sum.inl x) - single K p (Sum.inl x₀)) +
            barV K p bar ((q p : ℤ) • single K p (Sum.inr e₀)) := by
        have : barV K p bar ((q p : ℤ) • single K p (Sum.inr e₀)) =
            (q p : ℤ) • single K p (Sum.inl x₀) := by
          rw [← h₀, ← barV_single bar hbar]; rfl
        rw [this, smul_sub]; abel
      rw [h1]
      exact (InLL.of_InL (inL_q_single_sub x x₀)).add (InLL.of_bar (inL_q_single_extra e₀))
    · exact InLL.of_InL (inL_q_single_extra e)
  rw [vec_eq_sum_single d, Finset.smul_sum]
  refine InLL.sum _ _ fun t _ => ?_
  rw [smul_comm]
  exact (hsingle t).smul _

/-- **Lemma 7.3(c)**, second part: `1_O ∈ 𝓛 + 𝓛̄`. -/
theorem lattice_c_ord (bar : Letter K p → Letter K p) (hbar : Function.Involutive bar)
    (e₀ : Pt (ZMod p)) (x₀ : Pt K) (h₀ : bar (Sum.inr e₀) = Sum.inl x₀) :
    InLL K p bar (ordVec K p) := by
  have h : ordVec K p = ∑ ℓ, lineVec K p ℓ - (q p : ℤ) • ordVec K p := by
    rw [sum_lineVec_all, add_smul, one_smul]; abel
  rw [h]
  exact (InLL.of_InL (InL.sum _ _ fun ℓ _ => InL.line ℓ)).sub
    (lattice_c_q bar hbar e₀ x₀ h₀ _)

end Kaplansky.OddDesign
