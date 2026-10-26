import Kaplansky.Random.Alphabet
import OAI.Algebra.GroupRing.IntervalSelfLinks
import OAI.Algebra.GroupRing.MatchingGraphs
import OAI.Algebra.GroupRing.PatternCount

/-!
# Abstract random models (the `ModelData` of `docs/D_DESIGN.md` §1)

OpenAI's probability chain (`OAI/Algebra/GroupRing`, closure of `BoundedSystem`) is written
for one model.  A `Model` bundles everything that chain uses about the model:

* an `Alphabet` with a squared-word decay estimate (`δ = 1/D` from `h₀` on) and the bin
  constant `A₀ ≥ 2 log W`;
* two `Side`s `A` and `B`, each a family (indexed by the size parameter `m`) of finite vertex
  types with outgoing letter sets and a colour function.  A side with `Col = Unit` is OpenAI's
  single-bijection-per-inverse-pair model; `Col = Bool` with `flip = not` is the two-colour
  model of the paper (§6.3): matchings join `(t,+)` to `(t̄,-)`;
* the scale `L m = ⌊log (N m) / c⌋₊`, the maximum degree, and the first-moment data `n, p`,
  the per-colour turn tables `≤ n·p·J` and the common pool lower bound `carrier`.

The matching space of a side is OpenAI's generic `ConditionedMatchings.Matching` over the
*port alphabet* `α × Col`.
-/

namespace Kaplansky.Random

open OAI.TorsionFreeZeroDivisors
open Filter Topology

/-- Coloured outgoing ports: each outgoing letter of `x` tagged with the colour of `x`. -/
def cout {α TV Col : Type} (col : TV → Col) (out : TV → Finset α) (x : TV) : Finset (α × Col) :=
  (out x).map ⟨fun t => (t, col x), fun _ _ h => (Prod.mk.inj h).1⟩

@[simp] theorem mem_cout {α TV Col : Type} {col : TV → Col} {out : TV → Finset α} {x : TV}
    {y : α × Col} : y ∈ cout col out x ↔ y.1 ∈ out x ∧ y.2 = col x := by
  rcases y with ⟨t, c⟩
  unfold cout
  rw [Finset.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    have h' : (u, col x) = (t, c) := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    exact ⟨hu, rfl⟩
  · rintro ⟨ht, hc⟩
    have hc' : c = col x := hc
    exact ⟨t, ht, show (t, col x) = (t, c) by rw [hc']⟩

theorem card_cout {α TV Col : Type} (col : TV → Col) (out : TV → Finset α) (x : TV) :
    (cout col out x).card = (out x).card := by
  simp [cout]

/-- The inverse of a coloured port. -/
def cbar {α Col : Type} (inv : α → α) (flip : Col → Col) (x : α × Col) : α × Col :=
  (inv x.1, flip x.2)

/-- One side of a random model, at every size parameter `m`. -/
structure Side (Ab : Alphabet) where
  Col : Type
  [fCol : Fintype Col]
  [dCol : DecidableEq Col]
  [nCol : Nonempty Col]
  flip : Col → Col
  flip_flip : ∀ c, flip (flip c) = c
  V : ℕ → Type
  [fV : ∀ m, Fintype (V m)]
  [dV : ∀ m, DecidableEq (V m)]
  col : ∀ m, V m → Col
  out : ∀ m, V m → Finset Ab.α

attribute [instance] Side.fCol Side.dCol Side.nCol Side.fV Side.dV

namespace Side

variable {Ab : Alphabet} (S : Side Ab)

/-- The port alphabet: a letter together with the colour class of the port's vertex. -/
abbrev Port := Ab.α × S.Col

/-- Inverse port label: matched ports carry inverse letters and opposite colours. -/
def bar (x : S.Port) : S.Port := cbar Ab.inv S.flip x

theorem bar_ne (x : S.Port) : S.bar x ≠ x := by
  intro h
  exact Ab.inv_ne x.1 (congrArg Prod.fst h)

theorem bar_bar (x : S.Port) : S.bar (S.bar x) = x := by
  simp [bar, cbar, Ab.inv_inv, S.flip_flip]

/-- Coloured outgoing ports of a vertex. -/
def out' (m : ℕ) (x : S.V m) : Finset S.Port := cout (S.col m) (S.out m) x

@[simp] theorem mem_out' {m : ℕ} {x : S.V m} {y : S.Port} :
    y ∈ S.out' m x ↔ y.1 ∈ S.out m x ∧ y.2 = S.col m x := mem_cout

theorem card_out' (m : ℕ) (x : S.V m) : (S.out' m x).card = (S.out m x).card :=
  card_cout _ _ _

/-- Darts of the sampled graph on this side (OpenAI's generic dart type). -/
abbrev Dart (m : ℕ) := PatternEmbeddings.Dart (S.out' m)

/-- The matching space of this side. -/
abbrev Match (m : ℕ) := ConditionedMatchings.Matching (PatternEmbeddings.label (S.out' m)) S.bar

/-- The uniform space conditioned on girth (subdivision girth `N`). -/
noncomputable def samples (m N : ℕ) : Finset (S.Match m) :=
  ConditionedMatchings.Matching.conditioned (label := PatternEmbeddings.label (S.out' m))
    (bar := S.bar) (PatternEmbeddings.origin (S.out' m)) N ∅

/-- Size of the pool of ports with letter `t` in colour class `c`. -/
noncomputable def pool (m : ℕ) (t : Ab.α) (c : S.Col) : ℕ :=
  Fintype.card {x : S.V m // S.col m x = c ∧ t ∈ S.out m x}

/-- Joint count of two letters inside one colour class. -/
noncomputable def joint (m : ℕ) (c : S.Col) (a b : Ab.α) : ℕ :=
  Fintype.card {x : S.V m // S.col m x = c ∧ a ∈ S.out m x ∧ b ∈ S.out m x}

end Side

/-- Logarithmic scale with divisor `c` (OpenAI: `c = 100`). -/
noncomputable def scaleL (c n : ℕ) : ℕ := ⌊Real.log n / c⌋₊

/-- Everything OpenAI's probability chain uses about a random model. -/
structure Model extends Alphabet where
  /-- squared-word decay with `δ = 1/D` -/
  D : ℕ
  D_pos : 0 < D
  h₀ : ℕ
  decays : toAlphabet.Decays D h₀
  /-- the bin constant `a₀` -/
  A₀ : ℕ
  A₀_ge : 2 * Real.log W ≤ A₀
  SA : Side toAlphabet
  SB : Side toAlphabet
  /-- scale: `L m = ⌊log (N m) / c⌋₊` -/
  c : ℕ
  c_pos : 0 < c
  N : ℕ → ℕ
  N_tendsto : Tendsto N atTop atTop
  dmax : ℕ
  dmax_ge : 129 ≤ dmax
  log_dmax : 12 * Real.log dmax < c
  cardA_le : ∀ m, Fintype.card (SA.V m) ≤ N m
  cardB_le : ∀ m, Fintype.card (SB.V m) ≤ N m
  degA : ∀ m x, 129 ≤ (SA.out m x).card ∧ (SA.out m x).card ≤ dmax
  degB : ∀ m x, 129 ≤ (SB.out m x).card ∧ (SB.out m x).card ≤ dmax
  /-- matchings exist: every pool has the size of its inverse pool -/
  balanceA : ∀ m t col, SA.pool m t col = SA.pool m (inv t) (SA.flip col)
  balanceB : ∀ m t col, SB.pool m t col = SB.pool m (inv t) (SB.flip col)
  /-- first-moment data: `n` vertices available, letter density `p` -/
  p : ℝ
  p_pos : 0 < p
  p_le_one : p ≤ 1
  n : ℕ → ℝ
  cardA_le_n : ∀ m, (Fintype.card (SA.V m) : ℝ) ≤ n m
  cardB_le_n : ∀ m, (Fintype.card (SB.V m) : ℝ) ≤ n m
  tableA : ∀ m col a b, a ≠ b → (SA.joint m col a b : ℝ) ≤ n m * p * J a b
  tableB : ∀ m col a b, a ≠ b → (SB.joint m col a b : ℝ) ≤ n m * p * J a b
  /-- common lower bound for all pools -/
  carrier : ℕ → ℕ
  poolA : ∀ m t col, carrier m ≤ SA.pool m t col
  poolB : ∀ m t col, carrier m ≤ SB.pool m t col
  carrier_le : ∀ m, (carrier m : ℝ) ≤ n m * p
  ratio : Tendsto (fun m => n m * p / carrier m) atTop (𝓝 1)
  /-- pools are a fixed proportion of the reference size -/
  κ : ℝ
  κ_pos : 0 < κ
  carrier_lin : ∀ᶠ m in atTop, κ * N m ≤ carrier m

namespace Model

variable (M : Model)

/-- The scale `L`. -/
noncomputable def L (m : ℕ) : ℕ := scaleL M.c (M.N m)

/-- The error threshold, fixed by the alphabet before any pattern parameter
(OpenAI: `epsilon (1/600) 256 = 1/2467200`). -/
noncomputable def ε : ℝ := StageFusion.epsilon (1 / (M.D : ℝ)) M.A₀

theorem ε_pos : 0 < M.ε :=
  StageFusion.epsilon_pos (one_div_pos.mpr (by exact_mod_cast M.D_pos)) (Nat.cast_nonneg _)

theorem D_pos' : (0 : ℝ) < M.D := by exact_mod_cast M.D_pos

theorem δ_pos : (0 : ℝ) < 1 / (M.D : ℝ) := one_div_pos.mpr M.D_pos'

/-- The scale condition `s + 2D ≤ 2x` (OpenAI: `s + 1200 ≤ 2x`) in multiplied form. -/
theorem scale_mul {s x : ℝ} (h : s + 2 * M.D ≤ 2 * x) :
    (1 / (M.D : ℝ)) * s + 2 ≤ 2 * (1 / (M.D : ℝ)) * x := by
  have hD := M.D_pos'
  have hm := mul_le_mul_of_nonneg_left h (le_of_lt M.δ_pos)
  have h2 : (1 / (M.D : ℝ)) * (2 * M.D) = 2 := by field_simp
  nlinarith

theorem A₀_nonneg : (0 : ℝ) ≤ M.A₀ := Nat.cast_nonneg _

theorem card_α_pos : 0 < Fintype.card M.α := Fintype.card_pos

theorem log_card_α_nonneg : 0 ≤ Real.log (Fintype.card M.α) :=
  Real.log_nonneg (by exact_mod_cast M.card_α_pos)

end Model

end Kaplansky.Random
