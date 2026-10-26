import Kaplansky.Random.Chain.Sample
import Kaplansky.Exclusion.Basic

/-!
# Random models give pattern-free graphs (paper Definition 3.3, Theorem 3.4 (b)–(d))

For every `Model` and all large size parameters, for every choice of the two roots, some
girth-conditioned sample is `Exclusion.PatternFree` (agent B's Definition 3.3) with

* `ε = M.ε = StageFusion.epsilon (1/D) A₀` (fixed by the alphabet),
* `d = TypedDiameter.D₀ M` (component diameters `≤ d·L`),
* `λ = 1 + 2c / log 2` (`log₂ |V| ≤ λ L`),
* scale `L = M.L mm = ⌊log N / c⌋₊ ≥ 3`, degrees `≥ 129 ≥ 7`.

This is the packaging of `SampleGraph.exists_avoiding` in the form consumed by Theorem B; it
mirrors `Kaplansky.Main.patternFree` (OpenAI's sample).
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology PortSubdivision

noncomputable section

namespace SampleGraph
open ActualPatternEvent
variable (M : Model) (mm : ℕ) (r : Match M mm)

/-- The two roots of a sample. -/
def isRoot (x : VA M mm) (y : VB M mm) (v : VA M mm ⊕ VB M mm) : Prop :=
  v = Sum.inl x ∨ v = Sum.inr y

lemma simple_eq : ShortClosure.simpleGraph (graph M mm r) =
    ShortClosure.simpleGraph (A M mm r) ⊕g ShortClosure.simpleGraph (B M mm r) :=
  SumPort.simple_eq (A M mm r) (B M mm r)

/-- Degree of a coloured typed side: the size of the outgoing type. -/
lemma side_degree {α TV Col : Type} [Fintype TV] [DecidableEq TV] [Fintype α] [DecidableEq α]
    [Fintype Col] [DecidableEq Col] (col : TV → Col) (out : TV → Finset α) (v : TV) :
    Fintype.card {d : PatternEmbeddings.Dart (cout col out) //
      PatternEmbeddings.origin (cout col out) d = v} = (out v).card := by
  rw [← Nat.card_eq_fintype_card]
  exact origin_card col out v

lemma degree_card (v : VA M mm ⊕ VB M mm) :
    129 ≤ Fintype.card {d : DA M mm ⊕ DB M mm // (graph M mm r).origin d = v} := by
  classical
  cases v with
  | inl v =>
    have e : {d : DA M mm ⊕ DB M mm // (graph M mm r).origin d = Sum.inl v} ≃
        {d : DA M mm // PatternEmbeddings.origin (M.SA.out' mm) d = v} :=
      { toFun := fun d => match d with
          | ⟨Sum.inl d, h⟩ => ⟨d, Sum.inl.inj h⟩
          | ⟨Sum.inr _, h⟩ => absurd h (by simp [graph, SumPort.graph])
        invFun := fun d => ⟨Sum.inl d.val, congrArg Sum.inl d.property⟩
        left_inv := by
          rintro ⟨d | d, h⟩
          · rfl
          · exact absurd h (by simp [graph, SumPort.graph])
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e]
    have h := side_degree (M.SA.col mm) (M.SA.out mm) v
    exact (M.degA mm v).1.trans_eq h.symm
  | inr v =>
    have e : {d : DA M mm ⊕ DB M mm // (graph M mm r).origin d = Sum.inr v} ≃
        {d : DB M mm // PatternEmbeddings.origin (M.SB.out' mm) d = v} :=
      { toFun := fun d => match d with
          | ⟨Sum.inr d, h⟩ => ⟨d, Sum.inr.inj h⟩
          | ⟨Sum.inl _, h⟩ => absurd h (by simp [graph, SumPort.graph])
        invFun := fun d => ⟨Sum.inr d.val, congrArg Sum.inr d.property⟩
        left_inv := by
          rintro ⟨d | d, h⟩
          · exact absurd h (by simp [graph, SumPort.graph])
          · rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e]
    have h := side_degree (M.SB.col mm) (M.SB.out mm) v
    exact (M.degB mm v).1.trans_eq h.symm

/-- Every vertex of the sample has degree at least `129`. -/
lemma degree (v : VA M mm ⊕ VB M mm)
    {inst : DecidablePred fun d : DA M mm ⊕ DB M mm => (graph M mm r).origin d = v} :
    129 ≤ (@Finset.filter _ (fun d : DA M mm ⊕ DB M mm => (graph M mm r).origin d = v) inst
      Finset.univ).card := by
  have h := degree_card M mm r v
  rw [Fintype.card_subtype] at h
  convert h

lemma diameter (hd : GraphSample.Diameters M mm r) :
    ∀ a b, (ShortClosure.simpleGraph (graph M mm r)).Reachable a b →
      (ShortClosure.simpleGraph (graph M mm r)).dist a b ≤ TypedDiameter.D₀ M * M.L mm := by
  rw [simple_eq]
  exact SumGirth.diameter _ _ _ hd.1 hd.2

/-- The letters of the darts at a vertex are its outgoing type `S_v` (used with
`Parity.simultaneousSteps_eq_card_inter`). -/
lemma labels_at (v : VA M mm ⊕ VB M mm) :
    (Finset.univ.filter (fun d => (graph M mm r).origin d = v)).image (label M mm) =
      Sum.elim (M.SA.out mm) (M.SB.out mm) v := by
  ext t
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases d with d | d
    · have hv : v = Sum.inl d.val.1 := hd.symm
      subst hv
      exact ((Side.mem_out' M.SA).mp d.property).1
    · have hv : v = Sum.inr d.val.1 := hd.symm
      subst hv
      exact ((Side.mem_out' M.SB).mp d.property).1
  · intro ht
    rcases v with x | y
    · exact ⟨Sum.inl ⟨(x, (t, M.SA.col mm x)), (Side.mem_out' M.SA).mpr ⟨ht, rfl⟩⟩, rfl, rfl⟩
    · exact ⟨Sum.inr ⟨(y, (t, M.SB.col mm y)), (Side.mem_out' M.SB).mpr ⟨ht, rfl⟩⟩, rfl, rfl⟩

/-- Colours flip along the edges of side `A`: matched ports `(t, c)`, `(t̄, flip c)`.  In the
two-colour model every edge of `Γ_A` joins `A₊` to `A₋`. -/
lemma colourA_flip (d : DA M mm) :
    M.SA.col mm ((A M mm r).origin ((A M mm r).reverse d)) =
      M.SA.flip (M.SA.col mm ((A M mm r).origin d)) := by
  have h := congrArg Prod.snd (r.1.label_reverse d)
  have h1 := ((Side.mem_out' M.SA).mp (r.1 d).property).2
  have h2 := ((Side.mem_out' M.SA).mp d.property).2
  calc M.SA.col mm ((A M mm r).origin ((A M mm r).reverse d)) = ((r.1 d).val.2).2 := h1.symm
    _ = (M.SA.bar d.val.2).2 := h
    _ = M.SA.flip d.val.2.2 := rfl
    _ = M.SA.flip (M.SA.col mm ((A M mm r).origin d)) := congrArg M.SA.flip h2

/-- Colours flip along the edges of side `B`. -/
lemma colourB_flip (d : DB M mm) :
    M.SB.col mm ((B M mm r).origin ((B M mm r).reverse d)) =
      M.SB.flip (M.SB.col mm ((B M mm r).origin d)) := by
  have h := congrArg Prod.snd (r.2.label_reverse d)
  have h1 := ((Side.mem_out' M.SB).mp (r.2 d).property).2
  have h2 := ((Side.mem_out' M.SB).mp d.property).2
  calc M.SB.col mm ((B M mm r).origin ((B M mm r).reverse d)) = ((r.2 d).val.2).2 := h1.symm
    _ = (M.SB.bar d.val.2).2 := h
    _ = M.SB.flip d.val.2.2 := rfl
    _ = M.SB.flip (M.SB.col mm ((B M mm r).origin d)) := congrArg M.SB.flip h2

lemma card_vertices : Fintype.card (VA M mm ⊕ VB M mm) ≤ 2 * M.N mm := by
  rw [Fintype.card_sum]
  have h1 : Fintype.card (VA M mm) ≤ M.N mm := M.cardA_le mm
  have h2 : Fintype.card (VB M mm) ≤ M.N mm := M.cardB_le mm
  omega

end SampleGraph

namespace Model
variable (M : Model)

/-- The size constant `λ = 1 + 2c / log 2`. -/
def lam : ℝ := 1 + 2 * M.c / Real.log 2

theorem one_le_lam : 1 ≤ M.lam := by
  unfold lam
  have hc : (0 : ℝ) < M.c := by exact_mod_cast M.c_pos
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have : 0 ≤ 2 * (M.c : ℝ) / Real.log 2 := by positivity
  linarith

/-- `log₂ k ≤ λ L(n)` for `k ≤ 2n` once `L(n) = ⌊log n / c⌋₊ ≥ 1`. -/
theorem logb_le (n k : ℕ) (hk : k ≤ 2 * n) (hL : 1 ≤ scaleL M.c n) :
    Real.logb 2 k ≤ M.lam * scaleL M.c n := by
  have hc : (0 : ℝ) < M.c := by exact_mod_cast M.c_pos
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hLr : (1 : ℝ) ≤ scaleL M.c n := by exact_mod_cast hL
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [scaleL] at hL
    · exact h
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hfl : Real.log n / M.c < (scaleL M.c n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hln : Real.log n < M.c * ((scaleL M.c n : ℝ) + 1) := by
    rwa [div_lt_iff₀ hc, mul_comm] at hfl
  -- `log₂ k ≤ log₂ (2n) = 1 + log n / log 2`
  have hk2 : Real.logb 2 k ≤ 1 + Real.log n / Real.log 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp only [Nat.cast_zero, Real.logb_zero]
      have : 0 ≤ Real.log n / Real.log 2 := div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) hlog2.le
      linarith
    · have hkr : (0 : ℝ) < k := by exact_mod_cast h
      have hk' : (k : ℝ) ≤ 2 * n := by exact_mod_cast hk
      calc Real.logb 2 k ≤ Real.logb 2 (2 * n) :=
            Real.logb_le_logb_of_le (by norm_num) hkr hk'
        _ = 1 + Real.log n / Real.log 2 := by
            rw [Real.logb, Real.log_mul (by norm_num) hnr.ne', add_div, div_self hlog2.ne']
  have hmain : Real.log n / Real.log 2 ≤ 2 * M.c / Real.log 2 * scaleL M.c n := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog2]
    nlinarith
  unfold lam
  nlinarith

theorem eps_le_one : M.ε ≤ 1 :=
  (min_le_left _ _).trans (by norm_num)

theorem one_le_D₀ : (1 : ℝ) ≤ TypedDiameter.D₀ M := by
  unfold TypedDiameter.D₀
  have : 1 ≤ (TypedDiameter.A₀' M + 1) * (8 * M.c + 3) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _) (by omega))
  exact_mod_cast this

/-- The closure constant `D₀ = ⌈d + 4λ + 8⌉` of the model. -/
def closure : ℕ := Exclusion.closureConst (TypedDiameter.D₀ M : ℝ) M.lam

end Model

namespace SampleGraph
open ActualPatternEvent
variable {M : Model} {mm : ℕ} {r : Match M mm} {x : VA M mm} {y : VB M mm}

/-- A generic bounded system of the sample (agent B's `GBoundedSystem`) is a bounded system of
the model. -/
def ofGeneric {Bnd K I : ℕ}
    (s : Exclusion.GBoundedSystem (graph M mm r) (label M mm) M.inv (isRoot M mm x y)
      Bnd K I (M.L mm) M.ε) :
    BoundedSystem M Bnd K I mm r x y where
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
    rcases s.root_start p hp with h | h
    · rw [he] at h; exact Sum.inl.inj h
    · rw [he] at h; cases h
  rootB := by
    intro z hz
    obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hz
    rcases s.root_start p hp with h | h
    · rw [he] at h; cases h
    · rw [he] at h; exact Sum.inr.inj h
  compatible := s.compatible

end SampleGraph

namespace Model
open SampleGraph ActualPatternEvent
variable (M : Model)

/-- **Theorem 3.4 (b)–(d) for an abstract model, in the form of Definition 3.3.**  For all
large size parameters and every choice of roots `x ∈ A`, `y ∈ B`, some girth-conditioned
sample is pattern-free with `ε = M.ε`, `d = D₀`, `λ = 1 + 2c/log 2` at scale `L = M.L mm`. -/
theorem exists_patternFree :
    ∀ᶠ mm in atTop, ∀ (x : VA M mm) (y : VB M mm), ∃ r ∈ samples M mm,
      Exclusion.PatternFree (graph M mm r) (label M mm) M.inv (isRoot M mm x y)
        M.ε (TypedDiameter.D₀ M : ℝ) M.lam (M.L mm) := by
  have hK := PlanarParameters.K_pos M.ε M.closure
  have hI : 0 < 2 * Exclusion.pairs M.ε M.closure := by
    rw [Exclusion.two_pairs]
    exact PlanarParameters.sides_pos M.ε M.closure
  filter_upwards [SampleGraph.exists_avoiding M (PlanarParameters.C M.ε M.closure)
      (PlanarParameters.K M.ε M.closure) (2 * Exclusion.pairs M.ε M.closure) hK hI,
    M.L_tendsto.eventually_ge_atTop 3] with mm havoid hL
  intro x y
  obtain ⟨r, hr, hd, ha⟩ := havoid x y
  refine ⟨r, hr, ?_⟩
  exact {
    inv_involutive := M.inv_inv
    inv_ne := M.inv_ne
    label_reverse := SampleGraph.label_reverse M mm r
    immersed := SampleGraph.immersed M mm r
    eps_pos := M.ε_pos
    eps_le := M.eps_le_one
    one_le_d := M.one_le_D₀
    one_le_lam := M.one_le_lam
    scale := hL
    degree := fun v => (by norm_num : 7 ≤ 129).trans (SampleGraph.degree M mm r v)
    girth := Exclusion.girth_of_egirth _ _ (SampleGraph.girth M mm r hr)
    diameter := fun a b h => by exact_mod_cast SampleGraph.diameter M mm r hd a b h
    size := by
      have hc := SampleGraph.card_vertices M mm
      exact M.logb_le (M.N mm) _ hc (le_trans (by norm_num) hL)
    avoid := ⟨fun s => ha.false (SampleGraph.ofGeneric s)⟩ }

end Model

end

end Kaplansky.Random
