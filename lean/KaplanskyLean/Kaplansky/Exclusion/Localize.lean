import Kaplansky.Exclusion.Basic

/-!
# Cluster localisation with an outer-disk slack

Generic versions of OpenAI's `PlanarLocalization.exists_good_cluster`,
`ClusterLocalization.exists_selected`, `PathSystem.excluded_of_local_totals` and
`PathSystem.excluded_of_separator`, for an arbitrary graph and an arbitrary `ε`, with one change:
the number of unpaired occurrences may exceed the budget `ε/16·H₀` by a slack `ℓ`, the number of
occurrences joined to a free outer disk (paper, proof of Proposition 4.4, equation (4.2)), and the
short clusters may have mass `S` (`S = H₀/2` for a rooted picture, `S = 0` otherwise).
The conclusion survives as long as `ℓ/ε + S < 13/16·H₀`.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.Exclusion

noncomputable section

open OAI.TorsionFreeZeroDivisors
open PortSubdivision ComparedBlocks BlockAlignment ClusterLocalization

section Analytic
open scoped BigOperators

/-- `exists_good_cluster` with slack: unpaired budget `ε/16·H₀ + ℓ`, short mass `≤ S`. -/
theorem exists_good_cluster' {Z : Type} [Fintype Z]
    (h b i : Z → ℝ) (H₀ L ε C C₂ ℓ S : ℝ)
    (hL : 0 < L) (hε : 0 < ε) (hC₂ : 0 < C₂)
    (hh : ∀ z, 0 ≤ h z) (hb : ∀ z, 0 ≤ b z) (hi : ∀ z, 0 ≤ i z)
    (hupper : ∀ z, h z ≤ C * L)
    (hretained : 15 / 16 * H₀ ≤ ∑ z, h z)
    (hunpaired : ∑ z, b z ≤ ε / 16 * H₀ + ℓ)
    (hcomparisons : ∑ z, i z ≤ C₂ / (16 * L) * H₀)
    (hshort : ∑ z ∈ Finset.univ.filter (fun z => h z < L), h z ≤ S)
    (hgap : ℓ / ε + S < 13 / 16 * H₀) :
    ∃ z, L ≤ h z ∧ h z ≤ C * L ∧ b z ≤ ε * h z ∧ i z ≤ C₂ * h z / L := by
  classical
  let badB := Finset.univ.filter (fun z => ε * h z < b z)
  let badI := Finset.univ.filter (fun z => (C₂ / L) * h z < i z)
  let short := Finset.univ.filter (fun z => h z < L)
  have hB : ∑ z ∈ badB, h z ≤ H₀ / 16 + ℓ / ε := by
    have ht := (PlanarLocalization.bad_mass h b ε hb).trans hunpaired
    change ε * (∑ z ∈ badB, h z) ≤ ε / 16 * H₀ + ℓ at ht
    rw [div_add_div _ _ (by norm_num : (16:ℝ) ≠ 0) hε.ne',
      le_div_iff₀ (mul_pos (by norm_num) hε)]
    nlinarith
  have hI : ∑ z ∈ badI, h z ≤ H₀ / 16 := by
    have ht := (PlanarLocalization.bad_mass h i (C₂ / L) hi).trans hcomparisons
    change (C₂ / L) * (∑ z ∈ badI, h z) ≤ C₂ / (16 * L) * H₀ at ht
    have he : C₂ / (16 * L) * H₀ = (C₂ / L) * (H₀ / 16) := by ring
    rw [he] at ht
    have hp := div_pos hC₂ hL
    exact le_of_mul_le_mul_left ht hp
  by_contra hn
  have hc : ∀ z, z ∈ badB ∨ z ∈ badI ∨ z ∈ short := by
    intro z
    by_cases hB' : b z ≤ ε * h z
    · by_cases hI' : i z ≤ C₂ * h z / L
      · have hs : h z < L := by
          by_contra hl
          exact hn ⟨z, le_of_not_gt hl, hupper z, hB', hI'⟩
        exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩))
      · right; left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa only [div_mul_eq_mul_div] using lt_of_not_ge hI'
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hB'⟩)
  have hsum : (∑ z, h z) ≤ (∑ z ∈ badB, h z) + (∑ z ∈ badI, h z) + (∑ z ∈ short, h z) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    have hc := hc z
    simp only [badB, badI, short, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have h0 := hh z
    split_ifs <;> first | linarith | (exfalso; tauto)
  change (∑ z ∈ short, h z) ≤ S at hshort
  linarith

end Analytic

section Selected
open scoped Classical BigOperators
variable {T E : Type} [Fintype T] [Fintype E] {len : T → ℕ}
    (C : Comparisons (E := E) len) (keep : T → Prop)
local instance selectedClusterFintype' : Fintype (Cluster C keep) := Fintype.ofFinite _

/-- `ClusterLocalization.exists_selected` with slack `ℓ` and short budget `S`. -/
theorem exists_selected' (old : T → ℕ) (ho : ∀ t, old t ≤ len t)
    (_root : Option T) (L K cap : ℕ) (H₀ ε C₂ ℓ S : ℝ)
    (hL : 0 < L) (hε : 0 < ε) (hC₂ : 0 < C₂)
    (hsize : ∀ c : Cluster C keep, (paths C keep c).card ≤ K)
    (hcap : ∀ t, len t ≤ cap * L)
    (hbase : H₀ ≤ ∑ t, (old t : ℝ))
    (hdelete : (∑ t ∈ Finset.univ.filter (fun t => ¬keep t), (old t : ℝ)) ≤ H₀ / 16)
    (hbad : ((Finset.univ.filter (fun x : Position len => C.pairing.partner x = x)).card : ℝ) +
      ((Finset.univ.filter (fun x : Position len => ¬keep x.1 ∧ C.pairing.partner x ≠ x)).card : ℝ)
        ≤ ε / 16 * H₀ + ℓ)
    (hcompare : (Fintype.card E : ℝ) / 2 ≤ C₂ / (16 * L) * H₀)
    (hshort : ((∑ c ∈ Finset.univ.filter (fun c => mass C keep c < L), mass C keep c : ℕ) : ℝ) ≤ S)
    (hgap : ℓ / ε + S < 13 / 16 * H₀) :
    ∃ c : Cluster C keep, L ≤ mass C keep c ∧ mass C keep c ≤ K * cap * L ∧
      (bad C keep c : ℝ) ≤ ε * mass C keep c ∧
      (comparisons C keep c : ℝ) / 2 ≤ C₂ * mass C keep c / L := by
  have hret : 15 / 16 * H₀ ≤ ∑ c, (mass C keep c : ℝ) := by
    have hh : (∑ t, (old t : ℝ)) ≤ (∑ c, (mass C keep c : ℝ)) +
        ∑ t ∈ Finset.univ.filter (fun t => ¬keep t), (old t : ℝ) := by
      exact_mod_cast retained_original C keep old ho
    linarith
  have hb : (∑ c, (bad C keep c : ℝ)) ≤ ε / 16 * H₀ + ℓ := by
    have hh : (∑ c, (bad C keep c : ℝ)) ≤
        ((Finset.univ.filter (fun x : Position len => C.pairing.partner x = x)).card : ℝ) +
        ((Finset.univ.filter (fun x : Position len => ¬keep x.1 ∧ C.pairing.partner x ≠ x)).card : ℝ) := by
      exact_mod_cast bad_sum C keep
    exact hh.trans hbad
  have hi : (∑ c, (comparisons C keep c : ℝ) / 2) ≤ C₂ / (16 * L) * H₀ := by
    rw [← Finset.sum_div]
    apply le_trans _ hcompare
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast comparisons_sum C keep
  have hu : ∀ c : Cluster C keep, (mass C keep c : ℝ) ≤ (K * cap : ℝ) * L := by
    intro c
    have h := mass_upper C keep hsize hcap c
    rw [← Nat.mul_assoc] at h
    exact_mod_cast h
  have hs : (∑ c ∈ Finset.univ.filter (fun c => (mass C keep c : ℝ) < L), (mass C keep c : ℝ)) ≤ S := by
    simpa only [Nat.cast_sum, Nat.cast_lt] using hshort
  obtain ⟨c, hcl, hcu, hcb, hci⟩ := exists_good_cluster'
    (fun c => (mass C keep c : ℝ)) (fun c => (bad C keep c : ℝ))
    (fun c => (comparisons C keep c : ℝ) / 2) H₀ L ε (K * cap) C₂ ℓ S
    (by exact_mod_cast hL) hε hC₂ (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (fun _ => by positivity) hu hret hb hi hs hgap
  refine ⟨c, ?_, ?_, hcb, hci⟩
  · exact_mod_cast hcl
  · exact_mod_cast hcu

end Selected

section Localization
open scoped Classical BigOperators
variable {V D A : Type} [Fintype D] {Γ : PortGraph V D} {label : D → A} {inv : A → A}
  {isRoot : V → Prop}

namespace GPathSystem
variable (s : GPathSystem Γ label inv isRoot) (keep : s.P → Prop) (L : ℕ) (ε : ℝ)
local instance : Fintype (Cluster s.comparisons keep) := Fintype.ofFinite _

/-- Realize a selected cluster as a bounded system (generic `selected_bounded`). -/
def selected_bounded {Bnd K I : ℕ} (c : Cluster s.comparisons keep)
    (hP : (ClusterLocalization.paths s.comparisons keep c).card ≤ K)
    (hE : ClusterLocalization.comparisons s.comparisons keep c ≤ I)
    (hlo : L ≤ mass s.comparisons keep c)
    (hhi : mass s.comparisons keep c ≤ Bnd * L)
    (hbad : (bad s.comparisons keep c : ℝ) ≤ ε * mass s.comparisons keep c) :
    GBoundedSystem Γ label inv isRoot Bnd K I L ε := by
  let sc := s.restrict (belongs s.comparisons keep c)
  refine {
    P := {p // belongs s.comparisons keep c p}
    E := {e // RestrictComparisons.Active s.comparisons (belongs s.comparisons keep c) e}
    fP := inferInstance
    fE := inferInstance
    paths := fun p => s.paths p.val
    nonempty := fun p => s.nonempty p.val
    root := sc.root
    path_bound := ?_
    comparison_bound := hE
    path_chain := sc.path_chain
    cyclic_chain := sc.cyclic_chain
    length_le := ?_
    length_ge := ?_
    comparisons := localC s.comparisons keep c
    lower := sc.lower
    upper := sc.upper
    lower_eq := sc.lower_eq
    upper_eq := sc.upper_eq
    lower_le := sc.lower_le
    upper_le := sc.upper_le
    reduced := sc.reduced
    unpaired_le := ?_
    root_start := sc.root_start
    compatible := sc.compatible }
  · simpa only [Fintype.card_subtype, ClusterLocalization.paths] using hP
  · rw [local_mass]; exact hhi
  · rw [local_mass]; exact hlo
  · rw [← fixed_card s.comparisons keep c, ← local_mass s.comparisons keep c] at hbad
    convert hbad using 2
    congr 1
    ext p
    simp

/-- At most one short cluster, of mass at most `S`. -/
lemma short_bound (S : ℝ) (hlong : ∀ t, s.root ≠ some t → L ≤ (s.paths t).length)
    (hS : 0 ≤ S)
    (hroot : ∀ t, s.root = some t → (s.paths t).length < L → ((s.paths t).length : ℝ) ≤ S) :
    ((∑ c ∈ Finset.univ.filter (fun c => mass s.comparisons keep c < L),
      mass s.comparisons keep c : ℕ) : ℝ) ≤ S := by
  have hh : ((∑ c ∈ Finset.univ.filter (fun c => mass s.comparisons keep c < L),
      mass s.comparisons keep c : ℕ) : ℝ) ≤
      ((∑ t ∈ Finset.univ.filter (fun t => s.root = some t ∧ (s.paths t).length < L),
        (s.paths t).length : ℕ) : ℝ) := by
    exact_mod_cast short_mass_refined s.comparisons keep s.root hlong
  apply hh.trans
  cases hr : s.root with
  | none => simpa using hS
  | some r =>
    by_cases h : (s.paths r).length < L
    · have he : (Finset.univ.filter (fun t => some r = some t ∧ (s.paths t).length < L)) = {r} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.some.injEq,
          Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, _⟩; rfl
        · rintro rfl; exact ⟨rfl, h⟩
      rw [he, Finset.sum_singleton]
      exact hroot r hr h
    · have he : (Finset.univ.filter (fun t => some r = some t ∧ (s.paths t).length < L)) = ∅ := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.some.injEq,
          Finset.notMem_empty, iff_false, not_and]
        rintro rfl; exact h
      rw [he, Finset.sum_empty]
      simpa using hS

/-- Generic `excluded_of_local_totals`, with slack. -/
theorem excluded_of_local_totals' (K cap : ℕ) (C₂ H₀ ℓ S : ℝ) (old : s.P → ℕ)
    (ho : ∀ t, old t ≤ (s.paths t).length)
    (hL : 0 < L) (hε : 0 < ε) (hC₂ : 0 < C₂)
    (hsize : ∀ c : Cluster s.comparisons keep, (ClusterLocalization.paths s.comparisons keep c).card ≤ K)
    (hcap : ∀ t, (s.paths t).length ≤ cap * L)
    (hbase : H₀ ≤ ∑ t, (old t : ℝ))
    (hdelete : (∑ t ∈ Finset.univ.filter (fun t => ¬keep t), (old t : ℝ)) ≤ H₀ / 16)
    (hbad : ((Finset.univ.filter (fun p => s.comparisons.pairing.partner p = p)).card : ℝ) +
      ((Finset.univ.filter (fun p => ¬keep p.1 ∧ s.comparisons.pairing.partner p ≠ p)).card : ℝ) ≤
        ε / 16 * H₀ + ℓ)
    (hcompare : (Fintype.card s.E : ℝ) / 2 ≤ C₂ / (16 * L) * H₀)
    (hshort : ((∑ c ∈ Finset.univ.filter (fun c => mass s.comparisons keep c < L),
      mass s.comparisons keep c : ℕ) : ℝ) ≤ S)
    (hgap : ℓ / ε + S < 13 / 16 * H₀)
    (havoid : IsEmpty (GBoundedSystem Γ label inv isRoot (K * cap) K ⌈2 * C₂ * (K * cap : ℝ)⌉₊ L ε)) :
    False := by
  obtain ⟨c, hlo, hhi, hb, hi⟩ := exists_selected' s.comparisons keep old ho s.root
    L K cap H₀ ε C₂ ℓ S hL hε hC₂ hsize hcap hbase hdelete hbad hcompare hshort hgap
  have he : ClusterLocalization.comparisons s.comparisons keep c ≤ ⌈2 * C₂ * (K * cap : ℝ)⌉₊ := by
    suffices (ClusterLocalization.comparisons s.comparisons keep c : ℝ) ≤
        (⌈2 * C₂ * (K * cap : ℝ)⌉₊ : ℝ) by exact_mod_cast this
    apply le_trans _ (Nat.le_ceil _)
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have hi' := (le_div_iff₀ hLr).mp hi
    have hh : (mass s.comparisons keep c : ℝ) ≤ (K * cap : ℝ) * L := by exact_mod_cast hhi
    have hm := mul_le_mul_of_nonneg_left hh hC₂.le
    nlinarith
  exact havoid.false (s.selected_bounded keep L ε c (hsize c) he hlo hhi hb)

/-- Generic `excluded_of_separator`, for parameters `(ε, D)` and with slack `ℓ`. -/
theorem excluded_of_separator' (D : ℕ) (H₀ ℓ S : ℝ) (old : s.P → ℕ)
    (hε : 0 < ε) (hH₀ : 0 < H₀) (hL : 0 < L)
    (ho : ∀ t, old t ≤ (s.paths t).length)
    (hcapOld : ∀ t, old t ≤ PlanarParameters.U ε D * L)
    (hcap : ∀ t, (s.paths t).length ≤ (PlanarParameters.U ε D + D) * L)
    (hbase : H₀ ≤ ∑ t, (old t : ℝ))
    (hpieces : (Fintype.card s.P : ℝ) * L ≤ 2 * H₀)
    (hadded : ((Finset.univ.filter (fun p => s.comparisons.pairing.partner p = p)).card : ℝ) ≤
      3 * (D : ℝ) / PlanarParameters.U ε D * H₀ + ℓ)
    (hprefix : ∀ p : Position (fun t => (s.paths t).length), s.comparisons.pairing.partner p ≠ p →
      p.2.val ∈ BlockAlignment.positions 0 (old p.1))
    (hcompare : (Fintype.card s.E : ℝ) / 2 ≤ (192 : ℝ) / (16 * L) * H₀)
    (hlong : ∀ t, s.root ≠ some t → L ≤ (s.paths t).length)
    (hS : 0 ≤ S)
    (hroot : ∀ t, s.root = some t → (s.paths t).length < L → ((s.paths t).length : ℝ) ≤ S)
    (hgap : ℓ / ε + S < 13 / 16 * H₀)
    (oneStep : ∀ S' : Finset s.P, PlanarParameters.K ε D < S'.card →
      Nonempty (RecursiveSeparator.Split
        (PairingClusters.Rel (fun p : Position (fun t => (s.paths t).length) => p.1)
          s.comparisons.pairing.partner) S'))
    (havoid : IsEmpty (GBoundedSystem Γ label inv isRoot (PlanarParameters.C ε D)
      (PlanarParameters.K ε D) (PlanarParameters.sides ε D) L ε)) : False := by
  classical
  let R := PairingClusters.Rel (fun p : Position (fun t => (s.paths t).length) => p.1)
    s.comparisons.pairing.partner
  obtain ⟨A', hsmall, hA⟩ := PlanarParameters.delete ε D R hε oneStep
  let keep : s.P → Prop := fun t => t ∉ A'
  have hcount : ((Finset.univ.filter (fun t => ¬keep t)).card : ℝ) ≤
      PlanarParameters.η ε D * Fintype.card s.P := by
    simpa only [keep, not_not, Finset.filter_mem_eq_inter, Finset.univ_inter] using hA
  have hsize : ∀ c : Cluster s.comparisons keep,
      (ClusterLocalization.paths s.comparisons keep c).card ≤ PlanarParameters.K ε D := by
    apply ClusterLocalization.paths_card_le
    intro t ht
    obtain ⟨B, _hB, htB, hBK, hcl⟩ := hsmall t (by
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using ht)
    refine ⟨B, htB, hBK, ?_⟩
    intro a ha b hb hab
    exact hcl a ha b (by simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using hb) hab
  have hη := (PlanarParameters.η_pos ε D hε).le
  have hd : (∑ t ∈ Finset.univ.filter (fun t => ¬keep t), (old t : ℝ)) ≤
      2 * PlanarParameters.η ε D * PlanarParameters.U ε D * H₀ := by
    convert LocalizationCounts.deleted_mass keep old hcapOld hη (by
      convert hcount using 1
      congr 2
      ext t
      simp) hpieces using 1
    congr 1
    ext t
    simp
  have hdshort : (∑ t ∈ Finset.univ.filter (fun t => ¬keep t), (old t : ℝ)) ≤ H₀ / 16 := by
    apply hd.trans
    have hh := mul_le_mul_of_nonneg_right (PlanarParameters.deletion_loss ε D) hH₀.le
    nlinarith
  have hb : ((Finset.univ.filter (fun p => s.comparisons.pairing.partner p = p)).card : ℝ) +
      ((Finset.univ.filter (fun p => ¬keep p.1 ∧ s.comparisons.pairing.partner p ≠ p)).card : ℝ) ≤
        ε / 16 * H₀ + ℓ := by
    have hnew : ((Finset.univ.filter (fun p => ¬keep p.1 ∧ s.comparisons.pairing.partner p ≠ p)).card : ℝ) ≤
        ∑ t ∈ Finset.univ.filter (fun t => ¬keep t), (old t : ℝ) := by
      have hn := LocalizationCounts.deleted_nonfixed_le s.comparisons keep old hprefix
      have hn' : (Finset.univ.filter (fun p => ¬keep p.1 ∧ s.comparisons.pairing.partner p ≠ p)).card ≤
          ∑ t ∈ Finset.univ.filter (fun t => ¬keep t), old t := by
        convert hn using 1 <;> congr 1 <;> ext t <;> simp
      exact_mod_cast hn'
    have hdε : (∑ t ∈ Finset.univ.filter (fun t => ¬keep t), (old t : ℝ)) ≤ ε / 32 * H₀ :=
      hd.trans (mul_le_mul_of_nonneg_right (PlanarParameters.unpaired_loss ε D) hH₀.le)
    have ha := mul_le_mul_of_nonneg_right (PlanarParameters.closure_loss ε D hε) hH₀.le
    linarith
  have hi : ⌈2 * (192 : ℝ) * (PlanarParameters.K ε D * (PlanarParameters.U ε D + D) : ℝ)⌉₊ =
      PlanarParameters.sides ε D := by
    rw [show 2 * (192 : ℝ) * (PlanarParameters.K ε D * (PlanarParameters.U ε D + D) : ℝ) =
      (2 * 192 * (PlanarParameters.K ε D * (PlanarParameters.U ε D + D)) : ℕ) by push_cast; ring]
    rw [Nat.ceil_natCast]
    rfl
  have havoid' : IsEmpty (GBoundedSystem Γ label inv isRoot
      (PlanarParameters.K ε D * (PlanarParameters.U ε D + D)) (PlanarParameters.K ε D)
      ⌈2 * (192 : ℝ) * (PlanarParameters.K ε D * (PlanarParameters.U ε D + D) : ℝ)⌉₊ L ε) := by
    rw [hi]
    exact havoid
  exact s.excluded_of_local_totals' keep L ε (PlanarParameters.K ε D) (PlanarParameters.U ε D + D)
    192 H₀ ℓ S old ho hL hε (by norm_num) hsize hcap hbase (by
      convert hdshort using 1
      congr 1
      ext t
      simp) (by
      convert hb using 1
      congr 3
      ext t
      simp) hcompare (s.short_bound keep L S hlong hS hroot) hgap (by
      convert havoid' using 1
      push_cast
      rfl)

end GPathSystem
end Localization

end

end Kaplansky.Exclusion
