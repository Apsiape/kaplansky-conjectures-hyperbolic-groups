import Mathlib.Combinatorics.Configuration
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The projective plane `PG(2,F)` in normalized coordinates

For a field `F` we use the normalized homogeneous coordinates of the paper's proof of
Lemma 7.4:

* points `[i:j:1]` (`Pt.aff i j`), `[k:1:0]` (`Pt.inf k`) and `[1:0:0]` (`Pt.top`);
* lines `X = aY + cZ` (`Ln.gen a c`), `Y = cZ` (`Ln.hor c`) and `Z = 0` (`Ln.infty`).

Incidence `Inc x l` is given by an explicit table. We identify both types with Mathlib's
projectivization `ℙ F (Fin 3 → F)` (points and lines via orthogonality), and transport the
`Configuration.ProjectivePlane` structure to obtain, for a finite field of order `q`:

* `card_pt`, `card_ln`: there are `q^2+q+1` points and lines;
* `card_points`: every line has `q+1` points;
* `card_lines`: `q+1` lines pass through every point;
* `card_points_inter`: two distinct lines meet in exactly one point;
* `card_lines_inter`: two distinct points lie on exactly one line.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Configuration Matrix
open scoped LinearAlgebra.Projectivization

/-- A point of `PG(2,F)`: `[i:j:1]`, `[k:1:0]` or `[1:0:0]`. -/
inductive Pt (F : Type*) where
  | aff (i j : F)
  | inf (k : F)
  | top
  deriving DecidableEq

/-- A line of `PG(2,F)`: `X = aY + cZ`, `Y = cZ` or `Z = 0`. -/
inductive Ln (F : Type*) where
  | gen (a c : F)
  | hor (c : F)
  | infty
  deriving DecidableEq

variable {F : Type*}

/-- Points as a sum type. -/
def Pt.equivSum : Pt F ≃ (F × F) ⊕ (F ⊕ Unit) where
  toFun
    | .aff i j => .inl (i, j)
    | .inf k => .inr (.inl k)
    | .top => .inr (.inr ())
  invFun
    | .inl (i, j) => .aff i j
    | .inr (.inl k) => .inf k
    | .inr (.inr _) => .top
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, j⟩ | k | ⟨⟩ <;> rfl

/-- Lines as a sum type. -/
def Ln.equivSum : Ln F ≃ (F × F) ⊕ (F ⊕ Unit) where
  toFun
    | .gen a c => .inl (a, c)
    | .hor c => .inr (.inl c)
    | .infty => .inr (.inr ())
  invFun
    | .inl (a, c) => .gen a c
    | .inr (.inl c) => .hor c
    | .inr (.inr _) => .infty
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, j⟩ | k | ⟨⟩ <;> rfl

instance [Fintype F] : Fintype (Pt F) := Fintype.ofEquiv _ Pt.equivSum.symm
instance [Fintype F] : Fintype (Ln F) := Fintype.ofEquiv _ Ln.equivSum.symm

/-- `PG(2,F)` has `q^2+q+1` points. -/
theorem card_pt [Fintype F] :
    Fintype.card (Pt F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  rw [Fintype.card_congr Pt.equivSum]
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

/-- `PG(2,F)` has `q^2+q+1` lines. -/
theorem card_ln [Fintype F] :
    Fintype.card (Ln F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  rw [Fintype.card_congr Ln.equivSum]
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

section Incidence

variable [Field F]

/-- Incidence of points and lines. -/
def Inc : Pt F → Ln F → Prop
  | .aff i j, .gen a c => i = a * j + c
  | .inf k, .gen a _ => k = a
  | .top, .gen _ _ => False
  | .aff _ j, .hor c => j = c
  | .inf _, .hor _ => False
  | .top, .hor _ => True
  | .aff _ _, .infty => False
  | .inf _, .infty => True
  | .top, .infty => True

instance [DecidableEq F] (x : Pt F) (l : Ln F) : Decidable (Inc x l) := by
  cases x <;> cases l <;> (unfold Inc; infer_instance)

@[simp] theorem inc_aff_gen (i j a c : F) : Inc (.aff i j) (.gen a c) ↔ i = a * j + c := Iff.rfl
@[simp] theorem inc_inf_gen (k a c : F) : Inc (.inf k) (.gen a c) ↔ k = a := Iff.rfl
@[simp] theorem inc_top_gen (a c : F) : ¬ Inc (.top : Pt F) (.gen a c) := id
@[simp] theorem inc_aff_hor (i j c : F) : Inc (.aff i j) (.hor c) ↔ j = c := Iff.rfl
@[simp] theorem inc_inf_hor (k c : F) : ¬ Inc (.inf k) (.hor c) := id
@[simp] theorem inc_top_hor (c : F) : Inc (.top : Pt F) (.hor c) := trivial
@[simp] theorem inc_aff_infty (i j : F) : ¬ Inc (.aff i j) (.infty : Ln F) := id
@[simp] theorem inc_inf_infty (k : F) : Inc (.inf k) (.infty : Ln F) := trivial
@[simp] theorem inc_top_infty : Inc (.top : Pt F) (.infty : Ln F) := trivial

/-- Homogeneous coordinates of a point. -/
def Pt.vec : Pt F → Fin 3 → F
  | .aff i j => ![i, j, 1]
  | .inf k => ![k, 1, 0]
  | .top => ![1, 0, 0]

/-- Homogeneous coordinates of a line. -/
def Ln.vec : Ln F → Fin 3 → F
  | .gen a c => ![1, -a, -c]
  | .hor c => ![0, 1, -c]
  | .infty => ![0, 0, 1]

theorem Pt.vec_ne_zero (x : Pt F) : x.vec ≠ 0 := by
  intro h
  cases x with
  | aff i j => simpa [Pt.vec] using congrFun h 2
  | inf k => simpa [Pt.vec] using congrFun h 1
  | top => simpa [Pt.vec] using congrFun h 0

theorem Ln.vec_ne_zero (l : Ln F) : l.vec ≠ 0 := by
  intro h
  cases l with
  | gen a c => simpa [Ln.vec] using congrFun h 0
  | hor c => simpa [Ln.vec] using congrFun h 1
  | infty => simpa [Ln.vec] using congrFun h 2

theorem inc_iff_dotProduct (x : Pt F) (l : Ln F) : Inc x l ↔ x.vec ⬝ᵥ l.vec = 0 := by
  cases x <;> cases l <;>
    simp [Inc, Pt.vec, Ln.vec, dotProduct, Fin.sum_univ_three] <;>
    constructor <;> intro h <;> linear_combination h

/-- The point of `ℙ F (Fin 3 → F)` represented by `x`. -/
noncomputable def Pt.toProj (x : Pt F) : ℙ F (Fin 3 → F) :=
  Projectivization.mk F x.vec x.vec_ne_zero

/-- The line of `ℙ F (Fin 3 → F)` (via orthogonality) represented by `l`. -/
noncomputable def Ln.toProj (l : Ln F) : ℙ F (Fin 3 → F) :=
  Projectivization.mk F l.vec l.vec_ne_zero

theorem inc_iff_mem (x : Pt F) (l : Ln F) : Inc x l ↔ x.toProj ∈ l.toProj := by
  rw [inc_iff_dotProduct, ofField.mem_iff, Pt.toProj, Ln.toProj,
    Projectivization.orthogonal_mk]

theorem Pt.toProj_injective : Function.Injective (Pt.toProj (F := F)) := by
  intro x y h
  rw [Pt.toProj, Pt.toProj, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  rcases x with ⟨i, j⟩ | k | _ <;> rcases y with ⟨i', j'⟩ | k' | _ <;>
    simp [Pt.vec] at h0 h1 h2 ⊢
  case aff.aff => subst h2; simp only [one_mul] at h0 h1; exact ⟨h0.symm, h1.symm⟩
  case inf.aff => subst h2; simp at h1
  case inf.inf => subst h1; simp only [one_mul] at h0; exact h0.symm
  case top.aff => subst h2; simp at h0
  case top.inf => subst h1; simp at h0

theorem Pt.toProj_surjective : Function.Surjective (Pt.toProj (F := F)) := by
  intro w
  induction w using Projectivization.ind with
  | h v hv =>
    rcases eq_or_ne (v 2) 0 with h2 | h2
    · rcases eq_or_ne (v 1) 0 with h1 | h1
      · have h0 : v 0 ≠ 0 := by
          intro h0; apply hv; ext m; fin_cases m <;> simp [h0, h1, h2]
        refine ⟨.top, ?_⟩
        rw [Pt.toProj, Projectivization.mk_eq_mk_iff']
        refine ⟨(v 0)⁻¹, ?_⟩
        ext m; fin_cases m <;> simp [Pt.vec, h1, h2, h0]
      · refine ⟨.inf (v 0 / v 1), ?_⟩
        rw [Pt.toProj, Projectivization.mk_eq_mk_iff']
        refine ⟨(v 1)⁻¹, ?_⟩
        ext m; fin_cases m <;> simp [Pt.vec, h2] <;> field_simp
    · refine ⟨.aff (v 0 / v 2) (v 1 / v 2), ?_⟩
      rw [Pt.toProj, Projectivization.mk_eq_mk_iff']
      refine ⟨(v 2)⁻¹, ?_⟩
      ext m; fin_cases m <;> simp [Pt.vec] <;> field_simp

theorem Ln.toProj_injective : Function.Injective (Ln.toProj (F := F)) := by
  intro x y h
  rw [Ln.toProj, Ln.toProj, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  rcases x with ⟨b, c⟩ | c | _ <;> rcases y with ⟨b', c'⟩ | c' | _ <;>
    simp [Ln.vec] at h0 h1 h2 ⊢
  case gen.gen => subst h0; simp only [one_mul] at h1 h2; exact ⟨h1.symm, h2.symm⟩
  case hor.gen => subst h0; simp at h1
  case hor.hor => subst h1; simp only [one_mul] at h2; exact h2.symm
  case infty.gen => subst h0; simp at h2
  case infty.hor => subst h1; simp at h2

theorem Ln.toProj_surjective : Function.Surjective (Ln.toProj (F := F)) := by
  intro w
  induction w using Projectivization.ind with
  | h v hv =>
    rcases eq_or_ne (v 0) 0 with h0 | h0
    · rcases eq_or_ne (v 1) 0 with h1 | h1
      · have h2 : v 2 ≠ 0 := by
          intro h2; apply hv; ext m; fin_cases m <;> simp [h0, h1, h2]
        refine ⟨.infty, ?_⟩
        rw [Ln.toProj, Projectivization.mk_eq_mk_iff']
        refine ⟨(v 2)⁻¹, ?_⟩
        ext m; fin_cases m <;> simp [Ln.vec, h1, h0, h2]
      · refine ⟨.hor (-(v 2 / v 1)), ?_⟩
        rw [Ln.toProj, Projectivization.mk_eq_mk_iff']
        refine ⟨(v 1)⁻¹, ?_⟩
        ext m; fin_cases m <;> simp [Ln.vec, h0] <;> field_simp
    · refine ⟨.gen (-(v 1 / v 0)) (-(v 2 / v 0)), ?_⟩
      rw [Ln.toProj, Projectivization.mk_eq_mk_iff']
      refine ⟨(v 0)⁻¹, ?_⟩
      ext m; fin_cases m <;> simp [Ln.vec] <;> field_simp

/-- Points of `PG(2,F)` are the points of the projectivization. -/
noncomputable def Pt.equivProj : Pt F ≃ ℙ F (Fin 3 → F) :=
  Equiv.ofBijective _ ⟨Pt.toProj_injective, Pt.toProj_surjective⟩

/-- Lines of `PG(2,F)` are the points of the (dual) projectivization. -/
noncomputable def Ln.equivProj : Ln F ≃ ℙ F (Fin 3 → F) :=
  Equiv.ofBijective _ ⟨Ln.toProj_injective, Ln.toProj_surjective⟩

end Incidence

section Counting

variable [Field F] [Fintype F] [DecidableEq F]

/-- The points on a line. -/
def points (l : Ln F) : Finset (Pt F) := Finset.univ.filter (fun x => Inc x l)

/-- The lines through a point. -/
def lines (x : Pt F) : Finset (Ln F) := Finset.univ.filter (fun l => Inc x l)

@[simp] theorem mem_points {x : Pt F} {l : Ln F} : x ∈ points l ↔ Inc x l := by
  simp [points]

@[simp] theorem mem_lines {x : Pt F} {l : Ln F} : l ∈ lines x ↔ Inc x l := by
  simp [lines]

local notation "PP" => ℙ F (Fin 3 → F)

noncomputable local instance : Fintype PP := Fintype.ofFinite _

noncomputable local instance (x y : PP) : Decidable (x ∈ y) := Classical.propDecidable _

/-- The order of Mathlib's projective plane over `F` is `|F|`. -/
theorem order_eq : ProjectivePlane.order PP PP = Fintype.card F := by
  have h := ProjectivePlane.card_points PP PP
  rw [← Fintype.card_congr (Pt.equivProj (F := F)), card_pt] at h
  set n := ProjectivePlane.order PP PP
  set k := Fintype.card F
  rcases lt_trichotomy n k with hlt | heq | hgt
  · have : n ^ 2 < k ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
    omega
  · exact heq
  · have : k ^ 2 < n ^ 2 := Nat.pow_lt_pow_left hgt (by norm_num)
    omega

/-- Every line of `PG(2,F)` has `q+1` points. -/
theorem card_points (l : Ln F) : (points l).card = Fintype.card F + 1 := by
  have h := ProjectivePlane.pointCount_eq PP l.toProj
  rw [order_eq, pointCount, Nat.card_eq_fintype_card] at h
  rw [← h, points, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (Equiv.subtypeEquiv Pt.equivProj (fun x => inc_iff_mem x l))

/-- `q+1` lines of `PG(2,F)` pass through every point. -/
theorem card_lines (x : Pt F) : (lines x).card = Fintype.card F + 1 := by
  have h := ProjectivePlane.lineCount_eq PP x.toProj
  rw [order_eq, lineCount, Nat.card_eq_fintype_card] at h
  rw [← h, lines, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (Equiv.subtypeEquiv Ln.equivProj (fun l => inc_iff_mem x l))

/-- Two distinct lines of `PG(2,F)` meet in exactly one point. -/
theorem existsUnique_inter {l m : Ln F} (hlm : l ≠ m) : ∃! x, Inc x l ∧ Inc x m := by
  obtain ⟨y, hy, hu⟩ := HasPoints.existsUnique_point PP PP l.toProj m.toProj
    (fun h => hlm (Ln.toProj_injective h))
  obtain ⟨x, rfl⟩ := Pt.toProj_surjective y
  refine ⟨x, ?_, fun z hz => ?_⟩
  · show Inc x l ∧ Inc x m
    rwa [inc_iff_mem, inc_iff_mem]
  · have hz' : Inc z l ∧ Inc z m := hz
    rw [inc_iff_mem, inc_iff_mem] at hz'
    exact Pt.toProj_injective (hu _ hz')

/-- Two distinct points of `PG(2,F)` lie on exactly one line. -/
theorem existsUnique_join {x y : Pt F} (hxy : x ≠ y) : ∃! l, Inc x l ∧ Inc y l := by
  obtain ⟨m, hm, hu⟩ := HasLines.existsUnique_line PP PP x.toProj y.toProj
    (fun h => hxy (Pt.toProj_injective h))
  obtain ⟨l, rfl⟩ := Ln.toProj_surjective m
  refine ⟨l, ?_, fun z hz => ?_⟩
  · show Inc x l ∧ Inc y l
    rwa [inc_iff_mem, inc_iff_mem]
  · have hz' : Inc x z ∧ Inc y z := hz
    rw [inc_iff_mem, inc_iff_mem] at hz'
    exact Ln.toProj_injective (hu _ hz')

theorem card_filter_eq_one_of_existsUnique {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] (h : ∃! a, P a) : (Finset.univ.filter P).card = 1 := by
  obtain ⟨a, ha, hu⟩ := h
  rw [Finset.card_eq_one]
  exact ⟨a, by ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]; exact ⟨hu b, fun h => h ▸ ha⟩⟩

/-- Two distinct lines of `PG(2,F)` meet in exactly one point. -/
theorem card_points_inter {l m : Ln F} (hlm : l ≠ m) : (points l ∩ points m).card = 1 := by
  rw [points, points, ← Finset.filter_and]
  exact card_filter_eq_one_of_existsUnique _ (existsUnique_inter hlm)

/-- Two distinct points of `PG(2,F)` lie on exactly one line. -/
theorem card_lines_inter {x y : Pt F} (hxy : x ≠ y) : (lines x ∩ lines y).card = 1 := by
  rw [lines, lines, ← Finset.filter_and]
  exact card_filter_eq_one_of_existsUnique _ (existsUnique_join hxy)

/-- `|ℓ ∩ ℓ'|` is `q+1` or `1`. -/
theorem card_points_inter_eq (l m : Ln F) :
    (points l ∩ points m).card = if l = m then Fintype.card F + 1 else 1 := by
  split_ifs with h
  · subst h; rw [Finset.inter_self, card_points]
  · exact card_points_inter h

/-- The number of lines through `x` avoiding `y ≠ x` is `q`. -/
theorem card_lines_sdiff {x y : Pt F} (hxy : x ≠ y) :
    (lines x \ lines y).card = Fintype.card F := by
  have h1 := Finset.card_sdiff_add_card_inter (lines x) (lines y)
  rw [card_lines_inter hxy, card_lines] at h1
  omega

/-- The number of lines avoiding a point is `q^2`. -/
theorem card_lines_compl (x : Pt F) :
    (Finset.univ.filter (fun l => ¬ Inc x l)).card = Fintype.card F ^ 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun l => Inc x l)
  rw [Finset.card_univ, card_ln] at h
  have h2 : (Finset.univ.filter (fun l => Inc x l)).card = Fintype.card F + 1 := card_lines x
  omega

end Counting

/-! ### Sums over points -/

section Sums

variable [Fintype F] {M : Type*} [AddCommMonoid M]

theorem sum_pt (g : Pt F → M) :
    ∑ x, g x = ∑ i, ∑ j, g (.aff i j) + ∑ k, g (.inf k) + g .top := by
  rw [← (Pt.equivSum (F := F)).symm.sum_comp g, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Finset.sum_singleton, add_assoc]
  rfl

variable [Field F] [DecidableEq F]

theorem sum_points_gen (g : Pt F → M) (a c : F) :
    ∑ x ∈ points (.gen a c), g x = ∑ j, g (.aff (a * j + c) j) + g (.inf a) := by
  rw [points, Finset.sum_filter, sum_pt]
  simp only [inc_aff_gen, inc_inf_gen, inc_top_gen, ite_false, add_zero]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq']

theorem sum_points_hor (g : Pt F → M) (c : F) :
    ∑ x ∈ points (.hor c), g x = ∑ i, g (.aff i c) + g .top := by
  rw [points, Finset.sum_filter, sum_pt]
  simp [Finset.sum_ite_eq']

theorem sum_points_infty (g : Pt F → M) :
    ∑ x ∈ points (.infty : Ln F), g x = ∑ k, g (.inf k) + g .top := by
  rw [points, Finset.sum_filter, sum_pt]
  simp

end Sums

end Kaplansky.OddDesign
