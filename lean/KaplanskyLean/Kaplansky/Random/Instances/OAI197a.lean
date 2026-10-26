import Kaplansky.Random.Model
import Kaplansky.Random.Instances.Fano
import Kaplansky.Random.Instances.OAI197aAlphabet
import Kaplansky.Random.Instances.Counting

/-!
# OpenAI's direct-finiteness model (OAI197a §3.1) as a `Model`

Letters: the `v = 16513` points of `PG(2,128)` (OpenAI's `Types.Point`) and seven extra letters
(the Fano points).  Types: a line `ℓ` (its `129` points) together with an extra part, which is
empty, a complement `D_i` of a Fano line (four extras), or all seven extras (only the root).

**Vertex sets.**  OAI197a lets `m → ∞` through `m ≡ 1 (mod 4)`, puts `m` vertices in every line
class of `A`, `m - 1` in every class of `B`, and distributes `a_m = ((q+1)m-1)/4` (resp.
`b_m = (q+1)(m-1)/4`) copies of each block as evenly as possible.  We use an equivalent layout
in which every count is exact up to one fixed finite configuration:

* the *bulk* `Bulk N = Line × Slot × Fin N`, with `4v = 66052` slots per line, of which `129`
  carry each block `D_i` (so each block occurs `129 v N` times, evenly in every line class);
* the *core*: one vertex per line, `32` of them carrying each block, one root carrying all seven
  extras (OAI197a's configuration at `m = 1`).

`A = Bulk (m+1) ⊔ Core`, `B = Bulk (m+1)`.  Every letter has `8520708 (m+1) + 129` carriers in
`A` and `8520708 (m+1)` in `B`; the turn tables of the bulk are exactly `n p J` with
`n = 4 v² (m+1)`, and the core adds at most `129`.  The parity conditions of OAI197a
Proposition `prop:types` hold (`parity_AA`, `parity_root`, `parity_AB`).
-/

/- The vertex types `Bulk N ⊕ Core` are nested sums/products; their synthesized `DecidableEq` and
`Fintype` instances exceed the default instance size bound. -/
set_option synthInstance.maxSize 1024

namespace Kaplansky.Random.OAI197a

open OAI.TorsionFreeZeroDivisors
open Filter Topology
open scoped BigOperators

noncomputable section

/-! ### Letters as points and extras -/

/-- Codes of the ordinary letters. -/
abbrev OrdCode := Fin 7 ⊕ (Fin 8253 × Bool)

/-- Ordinary codes and extra indices are the letters. -/
def codeEquiv : OrdCode ⊕ Fin 7 ≃ Letter where
  toFun
    | .inl (.inl i) => (.inl i, false)
    | .inl (.inr (j, b)) => (.inr j, b)
    | .inr i => (.inl i, true)
  invFun
    | (.inl i, false) => .inl (.inl i)
    | (.inl i, true) => .inr i
    | (.inr j, b) => .inl (.inr (j, b))
  left_inv := by
    rintro ((i | ⟨j, b⟩) | i) <;> rfl
  right_inv := by
    rintro ⟨i | j, b⟩
    · cases b <;> rfl
    · rfl

/-- A fixed identification of the points with the ordinary codes; the points coded `inl i`
are the partners of the extras. -/
def pointCode : Types.Point ≃ OrdCode := Fintype.equivOfCardEq (by
  rw [Types.point_card]
  simp [OrdCode])

/-- Letters are points or extras. -/
def letterEquiv : Types.Point ⊕ Fin 7 ≃ Letter :=
  (Equiv.sumCongr pointCode (Equiv.refl _)).trans codeEquiv

theorem letterEquiv_inr (i : Fin 7) : letterEquiv (.inr i) = (.inl i, true) := rfl

theorem isExtra_inr (i : Fin 7) : IsExtra (letterEquiv (.inr i)) := ⟨i, rfl⟩

theorem not_isExtra_inl (P : Types.Point) : ¬IsExtra (letterEquiv (.inl P)) := by
  rintro ⟨i, hi⟩
  have h : letterEquiv (.inl P) = letterEquiv (.inr i) := hi
  exact Sum.inl_ne_inr (letterEquiv.injective h)

theorem J_inl_inl (P Q : Types.Point) : J (letterEquiv (.inl P)) (letterEquiv (.inl Q)) = 1 / 129 := by
  simp [J, not_isExtra_inl]

theorem J_inl_inr (P : Types.Point) (i : Fin 7) :
    J (letterEquiv (.inl P)) (letterEquiv (.inr i)) = pp := by
  simp [J, not_isExtra_inl, isExtra_inr]

theorem J_inr_inl (i : Fin 7) (P : Types.Point) :
    J (letterEquiv (.inr i)) (letterEquiv (.inl P)) = pp := by
  simp [J, not_isExtra_inl, isExtra_inr]

theorem J_inr_inr (i k : Fin 7) : J (letterEquiv (.inr i)) (letterEquiv (.inr k)) = 1 / 2 := by
  simp [J, isExtra_inr]

/-! ### Types -/

/-- The type with ordinary part the points of `ℓ` and extra part `X`. -/
def typeSet (ℓ : Types.Line) (X : Finset (Fin 7)) : Finset Letter :=
  ((Types.pointsOn ℓ).disjSum X).map letterEquiv.toEmbedding

theorem mem_inl {ℓ : Types.Line} {X : Finset (Fin 7)} {P : Types.Point} :
    letterEquiv (.inl P) ∈ typeSet ℓ X ↔ P ∈ ℓ := by
  rw [typeSet, Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.inl_mem_disjSum,
    Types.mem_pointsOn]

theorem mem_inr {ℓ : Types.Line} {X : Finset (Fin 7)} {i : Fin 7} :
    letterEquiv (.inr i) ∈ typeSet ℓ X ↔ i ∈ X := by
  rw [typeSet, Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.inr_mem_disjSum]

theorem card_typeSet (ℓ : Types.Line) (X : Finset (Fin 7)) :
    (typeSet ℓ X).card = 129 + X.card := by
  rw [typeSet, Finset.card_map, Finset.card_disjSum, Types.pointsOn_card]

theorem card_inter_typeSet (ℓ ℓ' : Types.Line) (X X' : Finset (Fin 7)) :
    (typeSet ℓ X ∩ typeSet ℓ' X').card =
      (Types.pointsOn ℓ ∩ Types.pointsOn ℓ').card + (X ∩ X').card := by
  rw [typeSet, typeSet, ← Finset.map_inter, Finset.card_map, Types.disjSum_inter,
    Finset.card_disjSum]

theorem degree_bounds (ℓ : Types.Line) (X : Finset (Fin 7)) :
    129 ≤ (typeSet ℓ X).card ∧ (typeSet ℓ X).card ≤ 136 := by
  rw [card_typeSet]
  have h := Finset.card_le_univ X
  simp only [Fintype.card_fin] at h
  omega

/-- Admissible extra parts. -/
def Adm (X : Finset (Fin 7)) : Prop := X = ∅ ∨ (∃ i, X = Fano.block i) ∨ X = Finset.univ

theorem block_ne_univ (i : Fin 7) : Fano.block i ≠ Finset.univ := by
  intro h
  have h1 := Fano.block_card i
  rw [h, Fano.univ_card] at h1
  omega

theorem even_inter {X Y : Finset (Fin 7)} (hX : Adm X) (hY : Adm Y)
    (h : ¬(X = Finset.univ ∧ Y = Finset.univ)) : Even (X ∩ Y).card := by
  rcases hX with rfl | ⟨i, rfl⟩ | rfl <;> rcases hY with rfl | ⟨j, rfl⟩ | rfl
  · simp
  · simp
  · simp
  · simp
  · exact Fano.block_inter_even i j
  · exact Fano.block_univ_even i
  · simp
  · rw [Finset.univ_inter, Fano.block_card]; decide
  · exact absurd ⟨rfl, rfl⟩ h

theorem odd_inter {ℓ ℓ' : Types.Line} {X Y : Finset (Fin 7)} (hX : Adm X) (hY : Adm Y)
    (h : ¬(X = Finset.univ ∧ Y = Finset.univ)) : Odd (typeSet ℓ X ∩ typeSet ℓ' Y).card := by
  rw [card_inter_typeSet]
  exact (Types.ordinary_inter_odd ℓ ℓ').add_even (even_inter hX hY h)

/-! ### Slots, bulk and core -/

/-- Bulk slots of one line class: `129` for each block, `65149` empty. -/
abbrev Slot := (Fin 7 × Fin 129) ⊕ Fin 65149

def slotExtra : Slot → Finset (Fin 7)
  | .inl (i, _) => Fano.block i
  | .inr _ => ∅

theorem slotExtra_adm (s : Slot) : Adm (slotExtra s) := by
  rcases s with ⟨i, _⟩ | _
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inl rfl

theorem slotExtra_ne_univ (s : Slot) : slotExtra s ≠ Finset.univ := by
  rcases s with ⟨i, _⟩ | _
  · exact block_ne_univ i
  · intro h
    have h1 := congrArg Finset.card h
    simp [slotExtra] at h1

theorem card_slot : Fintype.card Slot = 66052 := by simp [Slot]

theorem slot_extra_frequency (e : Fin 7) :
    Fintype.card {s : Slot // e ∈ slotExtra s} = 516 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  have hz : (∑ s : Fin 65149, if e ∈ slotExtra (.inr s) then 1 else 0) = 0 := by
    simp [slotExtra]
  rw [hz, add_zero, Fintype.sum_prod_type]
  have hi (i : Fin 7) :
      (∑ j : Fin 129, if e ∈ slotExtra (.inl (i, j)) then 1 else 0) =
        129 * (if e ∈ Fano.block i then 1 else 0) := by
    by_cases h : e ∈ Fano.block i <;> simp [slotExtra, h]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have h4 := Fano.blocks_through e
  simp only [Nat.cast_id] at h4 ⊢
  omega

theorem slot_extra_joint (e f : Fin 7) (hef : e ≠ f) :
    Fintype.card {s : Slot // e ∈ slotExtra s ∧ f ∈ slotExtra s} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  have hz : (∑ s : Fin 65149, if e ∈ slotExtra (.inr s) ∧ f ∈ slotExtra (.inr s)
      then 1 else 0) = 0 := by
    simp [slotExtra]
  rw [hz, add_zero, Fintype.sum_prod_type]
  have hi (i : Fin 7) :
      (∑ j : Fin 129, if e ∈ slotExtra (.inl (i, j)) ∧ f ∈ slotExtra (.inl (i, j))
        then 1 else 0) = 129 * (if e ∈ Fano.block i ∧ f ∈ Fano.block i then 1 else 0) := by
    by_cases h : e ∈ Fano.block i ∧ f ∈ Fano.block i <;> simp [slotExtra, h]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have h2 := Fano.blocks_through_two e f hef
  simp only [Nat.cast_id] at h2 ⊢
  omega

/-- The core: `32` vertices for each block, the root, and `16288` plain vertices. -/
abbrev Core := (Fin 7 × Fin 32) ⊕ (Unit ⊕ Fin 16288)

def coreExtra : Core → Finset (Fin 7)
  | .inl (i, _) => Fano.block i
  | .inr (.inl _) => Finset.univ
  | .inr (.inr _) => ∅

/-- The root of side `A`: the only vertex with all seven extras. -/
def coreRoot : Core := .inr (.inl ())

theorem coreExtra_adm (c : Core) : Adm (coreExtra c) := by
  rcases c with ⟨i, _⟩ | _ | _
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl

theorem coreExtra_eq_univ {c : Core} : coreExtra c = Finset.univ ↔ c = coreRoot := by
  rcases c with ⟨i, _⟩ | ⟨⟩ | _
  · simp only [coreExtra, coreRoot, reduceCtorEq, iff_false]
    exact block_ne_univ i
  · simp [coreExtra, coreRoot]
  · simp only [coreExtra, coreRoot, Sum.inr.injEq, reduceCtorEq, iff_false]
    intro h
    have h1 := congrArg Finset.card h
    simp at h1

theorem card_core : Fintype.card Core = 16513 := by simp [Core]

/-- The core has one vertex on every line. -/
def coreLine : Core ≃ Types.Line := Fintype.equivOfCardEq (by
  rw [card_core, Types.point_card])

theorem core_extra_frequency (e : Fin 7) :
    Fintype.card {c : Core // e ∈ coreExtra c} = 129 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hz : (∑ s : Fin 16288, if e ∈ coreExtra (.inr (.inr s)) then 1 else 0) = 0 := by
    simp [coreExtra]
  have hr : (∑ s : Unit, if e ∈ coreExtra (.inr (.inl s)) then 1 else 0) = 1 := by
    simp [coreExtra]
  rw [hz, hr, add_zero, Fintype.sum_prod_type]
  have hi (i : Fin 7) :
      (∑ j : Fin 32, if e ∈ coreExtra (.inl (i, j)) then 1 else 0) =
        32 * (if e ∈ Fano.block i then 1 else 0) := by
    by_cases h : e ∈ Fano.block i <;> simp [coreExtra, h]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have h4 := Fano.blocks_through e
  simp only [Nat.cast_id] at h4 ⊢
  omega

/-- Bulk vertices: line, slot, replica. -/
abbrev Bulk (N : ℕ) := Types.Line × Slot × Fin N

theorem card_bulk (N : ℕ) : Fintype.card (Bulk N) = 1090716676 * N := by
  simp only [Fintype.card_prod, card_slot, Fintype.card_fin, Types.point_card]
  ring

/-! ### Carrier counts -/

theorem bulk_inl (N : ℕ) (P : Types.Point) :
    Fintype.card {x : Bulk N // letterEquiv (.inl P) ∈ typeSet x.1 (slotExtra x.2.1)} =
      8520708 * N := by
  have he : ∀ x : Bulk N,
      letterEquiv (.inl P) ∈ typeSet x.1 (slotExtra x.2.1) ↔ P ∈ x.1 := fun x => mem_inl
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    Types.card_prod_fst (V := Slot × Fin N) (fun l : Types.Line => P ∈ l), Fintype.card_prod,
    card_slot, Fintype.card_fin, Types.line_single_card]
  ring

theorem bulk_inr (N : ℕ) (e : Fin 7) :
    Fintype.card {x : Bulk N // letterEquiv (.inr e) ∈ typeSet x.1 (slotExtra x.2.1)} =
      8520708 * N := by
  have he : ∀ x : Bulk N,
      letterEquiv (.inr e) ∈ typeSet x.1 (slotExtra x.2.1) ↔ e ∈ slotExtra x.2.1 :=
    fun x => mem_inr
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    Types.card_prod_snd (U := Types.Line) (fun x : Slot × Fin N => e ∈ slotExtra x.1),
    Types.card_prod_fst (V := Fin N) (fun s : Slot => e ∈ slotExtra s),
    Types.point_card, slot_extra_frequency, Fintype.card_fin]
  ring

theorem bulk_pool (N : ℕ) (t : Letter) :
    Fintype.card {x : Bulk N // t ∈ typeSet x.1 (slotExtra x.2.1)} = 8520708 * N := by
  obtain ⟨s, rfl⟩ := letterEquiv.surjective t
  rcases s with P | e
  · exact bulk_inl N P
  · exact bulk_inr N e

theorem core_pool (t : Letter) :
    Fintype.card {c : Core // t ∈ typeSet (coreLine c) (coreExtra c)} = 129 := by
  obtain ⟨s, rfl⟩ := letterEquiv.surjective t
  rcases s with P | e
  · have he : ∀ c : Core,
        letterEquiv (.inl P) ∈ typeSet (coreLine c) (coreExtra c) ↔ P ∈ coreLine c :=
      fun c => mem_inl
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
      Fintype.card_congr (coreLine.subtypeEquiv (p := fun c => P ∈ coreLine c)
        (q := fun l : Types.Line => P ∈ l) (fun c => Iff.rfl)),
      Types.line_single_card]
  · have he : ∀ c : Core,
        letterEquiv (.inr e) ∈ typeSet (coreLine c) (coreExtra c) ↔ e ∈ coreExtra c :=
      fun c => mem_inr
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he), core_extra_frequency]

/-! ### Joint counts -/

theorem bulk_joint_inl_inl (N : ℕ) (P Q : Types.Point) (hPQ : P ≠ Q) :
    Fintype.card {x : Bulk N // letterEquiv (.inl P) ∈ typeSet x.1 (slotExtra x.2.1) ∧
      letterEquiv (.inl Q) ∈ typeSet x.1 (slotExtra x.2.1)} = 66052 * N := by
  have he : ∀ x : Bulk N, (letterEquiv (.inl P) ∈ typeSet x.1 (slotExtra x.2.1) ∧
      letterEquiv (.inl Q) ∈ typeSet x.1 (slotExtra x.2.1)) ↔ (P ∈ x.1 ∧ Q ∈ x.1) :=
    fun x => and_congr mem_inl mem_inl
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    Types.card_prod_fst (V := Slot × Fin N) (fun l : Types.Line => P ∈ l ∧ Q ∈ l),
    Types.line_joint_card P Q hPQ, Fintype.card_prod, card_slot, Fintype.card_fin, one_mul]

theorem bulk_joint_inl_inr (N : ℕ) (P : Types.Point) (e : Fin 7) :
    Fintype.card {x : Bulk N // letterEquiv (.inl P) ∈ typeSet x.1 (slotExtra x.2.1) ∧
      letterEquiv (.inr e) ∈ typeSet x.1 (slotExtra x.2.1)} = 66564 * N := by
  have he : ∀ x : Bulk N, (letterEquiv (.inl P) ∈ typeSet x.1 (slotExtra x.2.1) ∧
      letterEquiv (.inr e) ∈ typeSet x.1 (slotExtra x.2.1)) ↔ (P ∈ x.1 ∧ e ∈ slotExtra x.2.1) :=
    fun x => and_congr mem_inl mem_inr
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    Types.card_prod_both (fun l : Types.Line => P ∈ l) (fun x : Slot × Fin N => e ∈ slotExtra x.1),
    Types.card_prod_fst (V := Fin N) (fun s : Slot => e ∈ slotExtra s),
    Types.line_single_card P, slot_extra_frequency, Fintype.card_fin]
  ring

theorem bulk_joint_inr_inr (N : ℕ) (e f : Fin 7) (hef : e ≠ f) :
    Fintype.card {x : Bulk N // letterEquiv (.inr e) ∈ typeSet x.1 (slotExtra x.2.1) ∧
      letterEquiv (.inr f) ∈ typeSet x.1 (slotExtra x.2.1)} = 4260354 * N := by
  have he : ∀ x : Bulk N, (letterEquiv (.inr e) ∈ typeSet x.1 (slotExtra x.2.1) ∧
      letterEquiv (.inr f) ∈ typeSet x.1 (slotExtra x.2.1)) ↔
      (e ∈ slotExtra x.2.1 ∧ f ∈ slotExtra x.2.1) :=
    fun x => and_congr mem_inr mem_inr
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    Types.card_prod_snd (U := Types.Line)
      (fun x : Slot × Fin N => e ∈ slotExtra x.1 ∧ f ∈ slotExtra x.1),
    Types.card_prod_fst (V := Fin N) (fun s : Slot => e ∈ slotExtra s ∧ f ∈ slotExtra s),
    Types.point_card, slot_extra_joint e f hef, Fintype.card_fin]
  ring

theorem core_joint_le (a b : Letter) :
    Fintype.card {c : Core // a ∈ typeSet (coreLine c) (coreExtra c) ∧
      b ∈ typeSet (coreLine c) (coreExtra c)} ≤ 129 := by
  rw [← core_pool a]
  exact Fintype.card_subtype_mono _ _ (fun c h => h.1)

/-! ### The two sides -/

abbrev VA (m : ℕ) := Bulk (m + 1) ⊕ Core
abbrev VB (m : ℕ) := Bulk (m + 1)

def lineA (m : ℕ) : VA m → Types.Line := Sum.elim (fun x => x.1) coreLine
def extraA (m : ℕ) : VA m → Finset (Fin 7) := Sum.elim (fun x => slotExtra x.2.1) coreExtra
def outA (m : ℕ) (x : VA m) : Finset Letter := typeSet (lineA m x) (extraA m x)

def outB (m : ℕ) (y : VB m) : Finset Letter := typeSet y.1 (slotExtra y.2.1)

/-- The root `x_A` of side `A`. -/
def rootA (m : ℕ) : VA m := .inr coreRoot

theorem extraA_adm (m : ℕ) (x : VA m) : Adm (extraA m x) := by
  rcases x with x | c
  · exact slotExtra_adm _
  · exact coreExtra_adm c

theorem extraA_eq_univ {m : ℕ} {x : VA m} : extraA m x = Finset.univ ↔ x = rootA m := by
  rcases x with x | c
  · simp only [extraA, Sum.elim_inl, rootA, reduceCtorEq, iff_false]
    exact slotExtra_ne_univ _
  · simp only [extraA, Sum.elim_inr, rootA, Sum.inr.injEq]
    exact coreExtra_eq_univ

theorem card_VA (m : ℕ) : Fintype.card (VA m) = 1090716676 * (m + 1) + 16513 := by
  rw [Fintype.card_sum, card_bulk, card_core]

theorem card_VB (m : ℕ) : Fintype.card (VB m) = 1090716676 * (m + 1) := card_bulk _

theorem poolA_card (m : ℕ) (t : Letter) :
    Fintype.card {x : VA m // t ∈ outA m x} = 8520708 * (m + 1) + 129 := by
  rw [card_subtype_sum]
  exact congrArg₂ (· + ·) (bulk_pool (m + 1) t) (core_pool t)

theorem poolB_card (m : ℕ) (t : Letter) :
    Fintype.card {y : VB m // t ∈ outB m y} = 8520708 * (m + 1) :=
  bulk_pool (m + 1) t

theorem jointA_le (m : ℕ) (a b : Letter) :
    Fintype.card {x : VA m // a ∈ outA m x ∧ b ∈ outA m x} ≤
      Fintype.card {x : Bulk (m + 1) // a ∈ typeSet x.1 (slotExtra x.2.1) ∧
        b ∈ typeSet x.1 (slotExtra x.2.1)} + 129 := by
  rw [card_subtype_sum]
  exact Nat.add_le_add_left (core_joint_le a b) _

/-- The bulk turn table is exactly `n p J` with `n = 4 v² N`. -/
theorem bulk_joint_eq (N : ℕ) (a b : Letter) (hab : a ≠ b) :
    (Fintype.card {x : Bulk N // a ∈ typeSet x.1 (slotExtra x.2.1) ∧
        b ∈ typeSet x.1 (slotExtra x.2.1)} : ℝ) =
      1090716676 * N * pp * J a b := by
  obtain ⟨sa, rfl⟩ := letterEquiv.surjective a
  obtain ⟨sb, rfl⟩ := letterEquiv.surjective b
  rcases sa with P | e <;> rcases sb with Q | f
  · have hPQ : P ≠ Q := fun h => hab (by rw [h])
    rw [bulk_joint_inl_inl N P Q hPQ, J_inl_inl, pp]
    push_cast
    ring
  · rw [bulk_joint_inl_inr N P f, J_inl_inr, pp]
    push_cast
    ring
  · have he : ∀ x : Bulk N, (letterEquiv (.inr e) ∈ typeSet x.1 (slotExtra x.2.1) ∧
        letterEquiv (.inl Q) ∈ typeSet x.1 (slotExtra x.2.1)) ↔
        (letterEquiv (.inl Q) ∈ typeSet x.1 (slotExtra x.2.1) ∧
          letterEquiv (.inr e) ∈ typeSet x.1 (slotExtra x.2.1)) := fun x => and_comm
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he), bulk_joint_inl_inr N Q e, J_inr_inl, pp]
    push_cast
    ring
  · have hef : e ≠ f := fun h => hab (by rw [h])
    rw [bulk_joint_inr_inr N e f hef, J_inr_inr, pp]
    push_cast
    ring

/-- `v²` -/
theorem v_sq : (1090716676 : ℝ) = 4 * 16513 ^ 2 := by norm_num

/-- The reference count `n m = v² (4m+5)`. -/
def nRef (m : ℕ) : ℝ := 272679169 * (4 * (m : ℝ) + 5)

theorem nRef_pos (m : ℕ) : 0 < nRef m := by unfold nRef; positivity

theorem core_slack (m : ℕ) (a b : Letter) :
    (129 : ℝ) ≤ (nRef m - 1090716676 * (m + 1 : ℕ)) * pp * J a b := by
  have h : nRef m - 1090716676 * ((m + 1 : ℕ) : ℝ) = 272679169 := by
    unfold nRef; push_cast; ring
  rw [h]
  have hJ := J_ge a b
  unfold pp
  nlinarith

theorem tableA_bound (m : ℕ) (a b : Letter) (hab : a ≠ b) :
    (Fintype.card {x : VA m // a ∈ outA m x ∧ b ∈ outA m x} : ℝ) ≤ nRef m * pp * J a b := by
  have h1 : (Fintype.card {x : VA m // a ∈ outA m x ∧ b ∈ outA m x} : ℝ) ≤
      (Fintype.card {x : Bulk (m + 1) // a ∈ typeSet x.1 (slotExtra x.2.1) ∧
        b ∈ typeSet x.1 (slotExtra x.2.1)} : ℝ) + 129 := by
    exact_mod_cast jointA_le m a b
  rw [bulk_joint_eq (m + 1) a b hab] at h1
  have h2 := core_slack m a b
  nlinarith

theorem tableB_bound (m : ℕ) (a b : Letter) (hab : a ≠ b) :
    (Fintype.card {y : VB m // a ∈ outB m y ∧ b ∈ outB m y} : ℝ) ≤ nRef m * pp * J a b := by
  have h1 := bulk_joint_eq (m + 1) a b hab
  have h2 := core_slack m a b
  have h3 : (Fintype.card {y : VB m // a ∈ outB m y ∧ b ∈ outB m y} : ℝ) =
      (Fintype.card {x : Bulk (m + 1) // a ∈ typeSet x.1 (slotExtra x.2.1) ∧
        b ∈ typeSet x.1 (slotExtra x.2.1)} : ℝ) := rfl
  rw [h3, h1]
  nlinarith

/-! ### Parity (OAI197a Proposition `prop:types`) -/

theorem parity_AA (m : ℕ) (x x' : VA m) (h : ¬(x = rootA m ∧ x' = rootA m)) :
    Odd (outA m x ∩ outA m x').card := by
  apply odd_inter (extraA_adm m x) (extraA_adm m x')
  rwa [extraA_eq_univ, extraA_eq_univ]

theorem parity_root (m : ℕ) : Even (outA m (rootA m)).card := by
  rw [outA, card_typeSet]
  have h : extraA m (rootA m) = Finset.univ := extraA_eq_univ.mpr rfl
  rw [h, Fano.univ_card]
  decide

theorem parity_AB (m : ℕ) (x : VA m) (y : VB m) : Odd (outA m x ∩ outB m y).card := by
  apply odd_inter (extraA_adm m x) (slotExtra_adm _)
  rintro ⟨-, h⟩
  exact slotExtra_ne_univ _ h

theorem parity_BB (m : ℕ) (y y' : VB m) : Odd (outB m y ∩ outB m y').card := by
  apply odd_inter (slotExtra_adm _) (slotExtra_adm _)
  rintro ⟨h, -⟩
  exact slotExtra_ne_univ _ h

theorem degreeA (m : ℕ) (x : VA m) : 129 ≤ (outA m x).card ∧ (outA m x).card ≤ 136 :=
  degree_bounds _ _

theorem degreeB (m : ℕ) (y : VB m) : 129 ≤ (outB m y).card ∧ (outB m y).card ≤ 136 :=
  degree_bounds _ _

/-! ### The model -/

/-- Side `A` (one colour class). -/
def sideA : Side alphabet where
  Col := Unit
  flip := id
  flip_flip _ := rfl
  V := VA
  col _ _ := ()
  out := outA

/-- Side `B` (one colour class). -/
def sideB : Side alphabet where
  Col := Unit
  flip := id
  flip_flip _ := rfl
  V := VB
  col _ _ := ()
  out := outB

/-- For a side with one colour class, a pool is the number of carriers. -/
theorem pool_eq_card {Ab : Alphabet} (S : Side Ab) (m : ℕ) (t : Ab.α) (c : S.Col)
    (hc : ∀ x, S.col m x = c) :
    S.pool m t c = Fintype.card {x : S.V m // t ∈ S.out m x} := by
  unfold Side.pool
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => ⟨fun h => h.2, fun h => ⟨hc x, h⟩⟩))

/-- For a side with one colour class, a joint count is the number of joint carriers. -/
theorem joint_eq_card {Ab : Alphabet} (S : Side Ab) (m : ℕ) (c : S.Col) (a b : Ab.α)
    (hc : ∀ x, S.col m x = c) :
    S.joint m c a b = Fintype.card {x : S.V m // a ∈ S.out m x ∧ b ∈ S.out m x} := by
  unfold Side.joint
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => ⟨fun h => h.2, fun h => ⟨hc x, h⟩⟩))

theorem sideA_pool (m : ℕ) (t : Letter) (c : sideA.Col) :
    sideA.pool m t c = 8520708 * (m + 1) + 129 :=
  (pool_eq_card sideA m t c (fun _ => rfl)).trans (poolA_card m t)

theorem sideB_pool (m : ℕ) (t : Letter) (c : sideB.Col) :
    sideB.pool m t c = 8520708 * (m + 1) :=
  (pool_eq_card sideB m t c (fun _ => rfl)).trans (poolB_card m t)

theorem sideA_joint (m : ℕ) (c : sideA.Col) (a b : Letter) :
    sideA.joint m c a b = Fintype.card {x : VA m // a ∈ outA m x ∧ b ∈ outA m x} :=
  joint_eq_card sideA m c a b (fun _ => rfl)

theorem sideB_joint (m : ℕ) (c : sideB.Col) (a b : Letter) :
    sideB.joint m c a b = Fintype.card {y : VB m // a ∈ outB m y ∧ b ∈ outB m y} :=
  joint_eq_card sideB m c a b (fun _ => rfl)

theorem log_136 : 12 * Real.log (136 : ℕ) < (100 : ℕ) := by
  have h : Real.log (136 : ℝ) < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)) 5
    rw [← Real.exp_nat_mul] at h1
    norm_num at h1 ⊢
    linarith
  push_cast
  linarith

theorem ratio_tendsto :
    Tendsto (fun m : ℕ => nRef m * pp / ((8520708 * (m + 1) : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h : (fun m : ℕ => nRef m * pp / ((8520708 * (m + 1) : ℕ) : ℝ)) =
      fun m : ℕ => 1 + (1 / 4) * (1 / ((m : ℝ) + 1)) := by
    funext m
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    unfold nRef pp
    push_cast
    field_simp
    ring
  rw [h]
  have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 4 : ℝ)
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).add h0
  simpa using h1

/-- **OpenAI's direct-finiteness model** (OAI197a §3) as a `Model`: alphabet with `δ = 1/600`,
`h₀ = 6003`, `a₀ = 10`; scale `L = ⌊log N / 100⌋`; degrees in `[129, 136]`. -/
def model : Model where
  toAlphabet := alphabet
  D := 600
  D_pos := by norm_num
  h₀ := 10 * 600 + 3
  decays := decays
  A₀ := 10
  A₀_ge := log_129_le
  SA := sideA
  SB := sideB
  c := 100
  c_pos := by norm_num
  N m := 272679169 * (4 * m + 5)
  N_tendsto := by
    apply tendsto_atTop_mono _ tendsto_id
    intro m
    show m ≤ 272679169 * (4 * m + 5)
    omega
  dmax := 136
  dmax_ge := by norm_num
  log_dmax := log_136
  cardA_le m := by
    show Fintype.card (VA m) ≤ 272679169 * (4 * m + 5)
    rw [card_VA]
    omega
  cardB_le m := by
    show Fintype.card (VB m) ≤ 272679169 * (4 * m + 5)
    rw [card_VB]
    omega
  degA m x := degreeA m x
  degB m y := degreeB m y
  balanceA m t c := (sideA_pool m t c).trans (sideA_pool m _ _).symm
  balanceB m t c := (sideB_pool m t c).trans (sideB_pool m _ _).symm
  p := pp
  p_pos := by unfold pp; norm_num
  p_le_one := by unfold pp; norm_num
  n := nRef
  cardA_le_n m := by
    show (Fintype.card (VA m) : ℝ) ≤ nRef m
    rw [card_VA]
    unfold nRef
    push_cast
    nlinarith
  cardB_le_n m := by
    show (Fintype.card (VB m) : ℝ) ≤ nRef m
    rw [card_VB]
    unfold nRef
    push_cast
    nlinarith
  tableA m c a b hab :=
    (congrArg (Nat.cast : ℕ → ℝ) (sideA_joint m c a b)).trans_le (tableA_bound m a b hab)
  tableB m c a b hab :=
    (congrArg (Nat.cast : ℕ → ℝ) (sideB_joint m c a b)).trans_le (tableB_bound m a b hab)
  carrier m := 8520708 * (m + 1)
  poolA m t c := le_of_le_of_eq (Nat.le_add_right _ 129) (sideA_pool m t c).symm
  poolB m t c := le_of_eq (sideB_pool m t c).symm
  carrier_le m := by
    show ((8520708 * (m + 1) : ℕ) : ℝ) ≤ nRef m * pp
    unfold nRef pp
    push_cast
    nlinarith
  ratio := ratio_tendsto
  κ := 1 / 272679169
  κ_pos := by norm_num
  carrier_lin := Eventually.of_forall (fun m => by
    show 1 / (272679169 : ℝ) * ((272679169 * (4 * m + 5) : ℕ) : ℝ) ≤ ((8520708 * (m + 1) : ℕ) : ℝ)
    push_cast
    nlinarith)

/-! ### Exports for the parity certificate (paper Prop 5.1(b), OAI197a Prop 2.1)

The types of the vertices of the model are `model.SA.out m = outA m` and
`model.SB.out m = outB m`; the root of side `A` is `rootA m`, the only vertex whose type contains
all seven extra letters. -/

theorem model_SA_V (m : ℕ) : model.SA.V m = VA m := rfl

theorem model_SB_V (m : ℕ) : model.SB.V m = VB m := rfl

theorem model_SA_out (m : ℕ) : model.SA.out m = outA m := rfl

theorem model_SB_out (m : ℕ) : model.SB.out m = outB m := rfl

theorem model_inv : model.inv = inverse := rfl

/-- `|S_x ∩ S_x'|` is odd on `A × A` except at `(x_A, x_A)`. -/
theorem odd_AA (m : ℕ) (x x' : model.SA.V m) (h : (x, x') ≠ (rootA m, rootA m)) :
    Odd (model.SA.out m x ∩ model.SA.out m x').card :=
  parity_AA m x x' (fun hx => h (Prod.ext hx.1 hx.2))

/-- `|S_{x_A} ∩ S_{x_A}| = |S_{x_A}|` is even. -/
theorem even_root (m : ℕ) : Even (model.SA.out m (rootA m) ∩ model.SA.out m (rootA m)).card := by
  rw [Finset.inter_self]
  exact parity_root m

/-- `|S_x ∩ S_y|` is odd on `A × B`. -/
theorem odd_AB (m : ℕ) (x : model.SA.V m) (y : model.SB.V m) :
    Odd (model.SA.out m x ∩ model.SB.out m y).card :=
  parity_AB m x y

/-- The root is the only vertex of side `A` whose type contains every extra letter. -/
theorem root_unique (m : ℕ) (x : model.SA.V m) :
    model.SA.out m x = model.SA.out m (rootA m) ↔ x = rootA m := by
  constructor
  · intro h
    have hx : extraA m x = Finset.univ := by
      have h1 : outA m x = outA m (rootA m) := h
      have h2 : extraA m (rootA m) = Finset.univ := extraA_eq_univ.mpr rfl
      ext i
      simp only [Finset.mem_univ, iff_true]
      have hi : letterEquiv (.inr i) ∈ outA m (rootA m) :=
        mem_inr.mpr (by rw [h2]; exact Finset.mem_univ i)
      rw [← h1] at hi
      exact mem_inr.mp hi
    exact extraA_eq_univ.mp hx
  · rintro rfl
    rfl

end

end Kaplansky.Random.OAI197a
