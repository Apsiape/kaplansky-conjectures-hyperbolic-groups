import Mathlib

/-!
# Challenge statements: Mghirbi–Douglas, "Kaplansky's conjectures fail for torsion-free
hyperbolic groups in positive characteristic". This formalization accompanies version 1.0.2 (26 October 2026); the
statements were written against version 1.0.1 (doi:10.5281/zenodo.23374592) and are unchanged; the paper's
all-versions DOI is 10.5281/zenodo.23374263.

This file contains ONLY definitions and statements (proved by `sorry`). It is the trusted
interface: the solution modules must prove these exact statements, checked by `#print axioms`
(allowed: `propext`, `Quot.sound`, `Classical.choice`) and by a Comparator-style comparison.

Definitions are copied verbatim from OpenAI's public Comparator challenges (openai/math, commit
1581d4c, Apache-2.0), so that our notions agree with the ones OpenAI's formalizations use:
* `TorsionFree`, `HasFiniteTwoDimensionalClassifyingSpace`: ComparatorChallenges/TorsionFreeZeroDivisors.lean
* `Geodesic`, `SideThin`, `WordHyperbolic`: ComparatorChallenges/TorsionFreeHyperbolic.lean
(universe-polymorphic versions specialised to `Type`).
-/

namespace Kaplansky

/-- Ordinary group torsion-freeness, without requiring uniqueness of all roots. -/
def TorsionFree (G : Type) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- A connected finite Hausdorff 2-dimensional CW K(G,1). -/
def HasFiniteTwoDimensionalClassifyingSpace (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (topX : TopologicalSpace X),
    letI : TopologicalSpace X := topX
    ∃ (_hausdorff : T2Space X) (_connected : PathConnectedSpace X)
      (cw : Topology.CWComplex (Set.univ : Set X)),
      letI : Topology.CWComplex (Set.univ : Set X) := cw
      Topology.CWComplex.Finite (Set.univ : Set X) ∧
      (∀ n : ℕ, 2 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) ∧
      Nonempty (Topology.CWComplex.cell (Set.univ : Set X) 2) ∧
      ∃ (x : X), Nonempty (G ≃* FundamentalGroup X x) ∧
        ∃ (E : Type) (topE : TopologicalSpace E),
          letI : TopologicalSpace E := topE
          ContractibleSpace E ∧
          ∃ p : E → X, IsCoveringMap p ∧ Function.Surjective p

/-- A shortest edge path in the unit-edge graph. -/
def Geodesic {V : Type} (X : SimpleGraph V) {x y : V} (p : X.Walk x y) : Prop :=
  p.length = X.dist x y

/-- Each vertex of `p` is within `δ` of a vertex of `q` or `r`. -/
def SideThin {V : Type} (X : SimpleGraph V) (δ : ℕ) {x y z : V}
    (p : X.Walk x y) (q : X.Walk y z) (r : X.Walk z x) : Prop :=
  ∀ a ∈ p.support, ∃ b, (b ∈ q.support ∨ b ∈ r.support) ∧ X.dist a b ≤ δ

/-- A finitely generated group with a unit-edge Cayley graph whose geodesic triangles
are uniformly thin. Connectedness of this Cayley graph asserts that `S` generates. -/
def WordHyperbolic (G : Type) [Group G] : Prop :=
  ∃ S : Set G, S.Finite ∧ (SimpleGraph.mulCayley S).Connected ∧
    ∃ δ : ℕ, ∀ (x y z : G)
      (p : (SimpleGraph.mulCayley S).Walk x y)
      (q : (SimpleGraph.mulCayley S).Walk y z)
      (r : (SimpleGraph.mulCayley S).Walk z x),
      Geodesic (SimpleGraph.mulCayley S) p →
      Geodesic (SimpleGraph.mulCayley S) q →
      Geodesic (SimpleGraph.mulCayley S) r →
      SideThin (SimpleGraph.mulCayley S) δ p q r ∧
      SideThin (SimpleGraph.mulCayley S) δ q r p ∧
      SideThin (SimpleGraph.mulCayley S) δ r p q

/-- The geometric hypotheses on the group in the paper's Main Theorem. -/
def GoodHyperbolic (G : Type) [Group G] : Prop :=
  Group.IsFinitelyPresented G ∧ TorsionFree G ∧ WordHyperbolic G ∧
    HasFiniteTwoDimensionalClassifyingSpace G

/-- **Main Theorem** (paper, boxed statement). For every prime `p` there are a finitely presented,
torsion-free, word-hyperbolic group `G` with a finite two-dimensional classifying space and
`a, b ∈ 𝔽_p[G]` with `ab = 1 ≠ ba`. (`p = 2`: Corollary 5.2; odd `p`: Theorem C.) -/
def MainTheorem : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ (G : Type) (_ : Group G), GoodHyperbolic G ∧
      ∃ a b : MonoidAlgebra (ZMod p) G, a * b = 1 ∧ b * a ≠ 1

/-- **Main Theorem, consequences.** For the same groups, over every field `K` of characteristic `p`:
`K[G]` is not directly finite, and contains an idempotent other than `0, 1`, a zero divisor, and a
unit of order `p` that is not of the form `λ g`. -/
def MainTheoremConsequences : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ (G : Type) (_ : Group G), GoodHyperbolic G ∧
      ∀ (K : Type) (_ : Field K) (_ : CharP K p),
        (∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1) ∧
        (∃ e : MonoidAlgebra K G, e * e = e ∧ e ≠ 0 ∧ e ≠ 1) ∧
        (∃ x y : MonoidAlgebra K G, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) ∧
        (∃ u : (MonoidAlgebra K G)ˣ, (u : MonoidAlgebra K G) ^ p = 1 ∧
          ∀ (c : K) (g : G), (u : MonoidAlgebra K G) ≠ MonoidAlgebra.single g c)

/-- **Corollary 5.4** (milestone 1: every OpenAI input is already formalized). A finitely presented,
torsion-free, word-hyperbolic group with a finite two-dimensional classifying space whose group
algebra over `𝔽₂` has zero divisors. -/
def HyperbolicZeroDivisors : Prop :=
  ∃ (G : Type) (_ : Group G), GoodHyperbolic G ∧
    ∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0

theorem hyperbolicZeroDivisors : HyperbolicZeroDivisors := by
  sorry

theorem mainTheorem : MainTheorem := by
  sorry

theorem mainTheoremConsequences : MainTheoremConsequences := by
  sorry

end Kaplansky
