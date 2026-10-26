import Mathlib

/-!
# The Fano plane and its line complements (OAI197a §3.1, paper Prop 5.1(b))

Points `Fin 7`, the seven lines of `PG(2,2)` listed explicitly, and the blocks
`D_i = complement of line i`.  All facts are finite and proved by `decide`.
-/

namespace Kaplansky.Random.Fano

/-- The seven lines of the Fano plane. -/
def line : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

/-- Blocks: complements of the Fano lines. -/
def block (i : Fin 7) : Finset (Fin 7) := Finset.univ \ line i

theorem line_card : ∀ i, (line i).card = 3 := by decide

theorem line_inter : ∀ i j, i ≠ j → (line i ∩ line j).card = 1 := by decide

theorem block_card : ∀ i, (block i).card = 4 := by decide

/-- Distinct blocks meet in two points. -/
theorem block_inter : ∀ i j, i ≠ j → (block i ∩ block j).card = 2 := by decide

/-- Every point lies in four blocks. -/
theorem blocks_through : ∀ e : Fin 7,
    (Finset.univ.filter (fun i => e ∈ block i)).card = 4 := by decide

/-- Two distinct points lie together in two blocks. -/
theorem blocks_through_two : ∀ e f : Fin 7, e ≠ f →
    (Finset.univ.filter (fun i => e ∈ block i ∧ f ∈ block i)).card = 2 := by decide

/-- Intersections of extra parts used for the parity conditions: every intersection of two
extra parts (empty, a block, or all seven) is even, except `E ∩ E`. -/
theorem block_inter_even : ∀ i j, Even (block i ∩ block j).card := by decide

theorem block_univ_even : ∀ i, Even (block i ∩ Finset.univ).card := by decide

theorem univ_card : (Finset.univ : Finset (Fin 7)).card = 7 := by decide

end Kaplansky.Random.Fano
