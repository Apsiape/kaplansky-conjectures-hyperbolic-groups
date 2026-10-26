import Kaplansky.Algebra.Lemmas

/-!
# The consequences of the Main Theorem

`Kaplansky.Algebra.mainTheoremConsequences_of_mainTheorem : Kaplansky.MainTheorem →
Kaplansky.MainTheoremConsequences` (definitions verbatim from `Kaplansky/Challenge.lean`).

Given `a, b ∈ 𝔽_p[G]` with `ab = 1 ≠ ba` and a field `K` of characteristic `p`:
* base change gives `a', b' ∈ K[G]` with `a'b' = 1 ≠ b'a'`;
* `e = b'a'` is an idempotent other than `0, 1` (Lemma 2.1);
* `e (1 - e) = 0` with `e ≠ 0 ≠ 1 - e` is a zero divisor (Lemma 2.1);
* `ν = b'(1 - e)` has `ν ≠ 0 = ν²`, so `1 + ν` is a unit with `(1 + ν)^p = 1`, and it is not of the
  form `λ g` because `G` is torsion-free (Lemma 2.2; torsion-freeness is part of `GoodHyperbolic`).

We also record the corresponding reduction from zero divisors to non-trivial units, conditional on
primeness of `K[G]` (Lemma 2.3; Connell's theorem is not in Mathlib).
-/

namespace Kaplansky.Algebra

open MonoidAlgebra

/-- All four consequences over a single field `K` of characteristic `p`, from `ab = 1 ≠ ba` in
`𝔽_p[G]`. -/
theorem consequences_of_not_directlyFinite (p : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (hG : Kaplansky.TorsionFree G) {a b : MonoidAlgebra (ZMod p) G} (hab : a * b = 1)
    (hba : b * a ≠ 1) (K : Type) [Field K] [CharP K p] :
    (∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1) ∧
    (∃ e : MonoidAlgebra K G, e * e = e ∧ e ≠ 0 ∧ e ≠ 1) ∧
    (∃ x y : MonoidAlgebra K G, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) ∧
    (∃ u : (MonoidAlgebra K G)ˣ, (u : MonoidAlgebra K G) ^ p = 1 ∧
      ∀ (c : K) (g : G), (u : MonoidAlgebra K G) ≠ MonoidAlgebra.single g c) := by
  obtain ⟨hab', hba'⟩ := baseChange_not_directlyFinite p K hab hba
  set a' := baseChange p K G a
  set b' := baseChange p K G b
  obtain ⟨he, he0, he1, hz, -, hν0, hν2, -, -⟩ := onesided hab' hba'
  obtain ⟨u, -, hup, -, hus⟩ := exists_unit_of_sqZero p hG hν0 hν2
  exact ⟨⟨a', b', hab', hba'⟩, ⟨b' * a', he, he0, he1⟩,
    ⟨b' * a', 1 - b' * a', he0, one_sub_idem_ne_zero hba', hz⟩, ⟨u, hup, hus⟩⟩

/-- **Main Theorem ⇒ its consequences.** The statement uses the Challenge definitions verbatim. -/
theorem mainTheoremConsequences_of_mainTheorem :
    Kaplansky.MainTheorem → Kaplansky.MainTheoremConsequences := by
  intro hmain p hp
  obtain ⟨G, instG, hG, a, b, hab, hba⟩ := hmain p hp
  refine ⟨G, instG, hG, fun K instK instC => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  exact consequences_of_not_directlyFinite p hG.2.1 hab hba K

/-- Lemma 2.3 ⇒ Lemma 2.2, conditional on primeness of `K[G]` (which for torsion-free `G` is
Connell's theorem, not available in Mathlib): zero divisors in `K[G]` give a unit that is not of the
form `λ g`, of order `p` in characteristic `p`. -/
theorem exists_unit_of_zeroDivisor_of_prime (p : ℕ) [Fact p.Prime] {K : Type*} [Field K]
    [CharP K p] {G : Type} [Group G] (hG : Kaplansky.TorsionFree G)
    (hprime : ∀ x y : MonoidAlgebra K G, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0)
    {α β : MonoidAlgebra K G} (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α * β = 0) :
    ∃ u : (MonoidAlgebra K G)ˣ, (u : MonoidAlgebra K G) ^ p = 1 ∧ orderOf u = p ∧
      ∀ (c : K) (g : G), (u : MonoidAlgebra K G) ≠ MonoidAlgebra.single g c := by
  obtain ⟨ν, hν, hν2⟩ := sqZero_of_zeroDivisor_of_prime hprime hα hβ hαβ
  obtain ⟨u, -, hup, hord, hus⟩ := exists_unit_of_sqZero p hG hν hν2
  exact ⟨u, hup, hord, hus⟩

end Kaplansky.Algebra
