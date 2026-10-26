import Kaplansky.Random.PatternFree
import Kaplansky.Random.Instances.OAI197a

/-!
# OAI197a: the `p = 2` direct-finiteness model is pattern-free

Theorem 3.4 (b)–(d) for OpenAI's model of OAI197a (types: lines of `PG(2,128)` plus
complements of Fano lines).  The letters are already signed (`Letter = (Fin 7 ⊕ Fin 8253) × Bool`
with `inverse = WordPairing.inverseLetter`), so the result is in the form of Theorem B.
The root of side `A` is the vertex `rootA m` carrying all seven extras; the parity facts of
OAI197a Proposition `prop:types` are `parity_AA`, `parity_root`, `parity_AB` (in `OAI197a.lean`).
-/

namespace Kaplansky.Random.OAI197a

open OAI.TorsionFreeZeroDivisors
open Filter

/-- **Theorem 3.4 (b)–(d), `p = 2` model (OAI197a).**  For all large `m` and every root `y` of
side `B`, some girth-conditioned sample of `model` at size `m`, rooted at `rootA m` and `y`, is
pattern-free in the sense of Definition 3.3. -/
theorem exists_patternFree :
    ∀ᶠ m in atTop, ∀ y : VB m, ∃ r ∈ ActualPatternEvent.samples model m,
      Exclusion.PatternFree (SampleGraph.graph model m r) (SampleGraph.label model m)
        WordPairing.inverseLetter (SampleGraph.isRoot model m (rootA m) y)
        model.ε (TypedDiameter.D₀ model : ℝ) model.lam (model.L m) := by
  filter_upwards [model.exists_patternFree] with m h
  intro y
  exact h (rootA m) y

end Kaplansky.Random.OAI197a
