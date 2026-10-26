import Kaplansky.Final.Model
import Kaplansky.Random.Instances.OAI197aFinal

/-!
# The Main Theorem for `p = 2` (paper Corollary 5.2)

OpenAI's direct-finiteness model (OAI197a, `Random.OAI197a.model`) has, for large `m`, a
pattern-free sample rooted at `rootA m` (the vertex carrying all seven extras) and any `y ∈ B`
(`Random.OAI197a.exists_patternFree`). Its letters are already signed. Theorem B and
Prop. 5.1(b),(c) apply with `σ = 1` (in `𝔽₂`, `-1 = 1`) and the parity conditions of OAI197a
Proposition `prop:types` (`parity_AA`, `parity_root`, `parity_AB`): `a = ∑_{x ∈ A} g_x`,
`b = a* = ∑ g_x⁻¹` satisfy `ab = 1 ≠ ba` in `𝔽₂[G]`.

Main result: `Final.two_counterexample`.
-/

namespace Kaplansky.Final

open OAI.TorsionFreeZeroDivisors
open Kaplansky.Random Kaplansky.Random.SampleGraph Kaplansky.Random.ActualPatternEvent
open Filter

/-- **Main Theorem, `p = 2`** (paper Corollary 5.2). -/
theorem two_counterexample :
    ∃ (G : Type) (_ : Group G), Kaplansky.GoodHyperbolic G ∧
      ∃ a b : MonoidAlgebra (ZMod 2) G, a * b = 1 ∧ b * a ≠ 1 := by
  classical
  obtain ⟨m, hm⟩ := OAI197a.exists_patternFree.exists
  have hcardB : 0 < Fintype.card (OAI197a.VB m) := by
    rw [OAI197a.card_VB]
    positivity
  obtain ⟨y⟩ := Fintype.card_pos_iff.mp hcardB
  obtain ⟨r, -, pf⟩ := hm y
  exact model_counterexample (M := OAI197a.model) (x := OAI197a.rootA m)
    (S₀ := Fin 7 ⊕ Fin 8253) id pf (p := 2) (fun _ => 1) (fun _ => by decide) rfl
    (fun x₁ x₂ hx => by
      have h := OAI197a.parity_AA m x₁ x₂ (fun h => hx (Prod.ext h.1 h.2))
      exact (Nat.odd_iff.mp h).trans rfl)
    (by
      have h := OAI197a.parity_root m
      exact (Nat.even_iff.mp h).trans rfl)
    (fun x₁ y₁ => by
      have h := OAI197a.parity_AB m x₁ y₁
      exact (Nat.odd_iff.mp h).trans rfl)

end Kaplansky.Final
