import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group

/-!
# Parity and signed-handshake certificates (paper, Sections 5.1, 6.1 and 7.5)

All statements are about abstract finite labelled graphs, in OpenAI's conventions
(`OAI.TorsionFreeZeroDivisors.Factors`, `OAI/Algebra/GroupRing/PlanarMap.lean`):

* a vertex type `A` (`Fintype`; in applications, the vertex set `A'` of the root component);
* outgoing label sets `outA : A → Finset T` (the types `S_x`);
* darts `Dart outA = {p : A × T // p.2 ∈ outA p.1}` (identical to OpenAI's `Factors.DartA`);
* a dart reversal `rA : Dart outA → Dart outA`, involutive, with `(rA d).val.2 = bar d.val.2` for a
  fixed-point-free `bar : T → T`; the end of `d` is `(rA d).val.1`;
* a labelling `letter : T → G` into a group and path labels `g : A → G` with
  `g (rA d).val.1 = g d.val.1 * letter d.val.2` (i.e. `g_{x·t} = g_x t`).

The same data with `B`, `outB`, `rB`, `h` describe the second component. The argument order of
the theorems below follows OpenAI's `Factors.product_zero`.

## Main results

* `signed_handshake` — **Lemma 6.1(a)** (paper `lem:handshake`): if `σ : A → R` reverses sign
  along every edge, then `∑_{x,y} |S_x ∩ S_y| σ(x) g_x h_y⁻¹ = 0` in `R[G]`, any commutative ring.
* `signed_product_zero` — **Lemma 6.1(b)**: if every `|S_x ∩ S_y| = 1` in `R`, then
  `(∑ σ(x) g_x)(∑ h_y⁻¹) = 0`; `signed_product_zero_zmod` is the `ZMod p` version with
  `|S_x ∩ S_y| ≡ 1 [MOD p]`; `signed_handshake_self`/`signed_product_zero_self` are the
  self-pairing variants `B' = A'`.
* `coeff_one_sum_single`, `sum_single_ne_zero`, `sum_single_inv_ne_zero` — **Lemma 6.1(c)** and
  Prop. 5.1(c): under root protection the coefficient of `1` is `σ(root)`.
* `parity_product_zero` — **Prop. 5.1(a)** (= OpenAI's `Factors.product_zero`).
* `parity_mul_star_eq_one` — **Prop. 5.1(b)**: `a a* = 1` in `𝔽₂[G]`.
* `parity_star_mul_ne_one` — **Prop. 5.1(c)**: `a* a ≠ 1`, via `ac = 0` and `c ≠ 0`.
* `parity_not_directlyFinite` — Prop. 5.1(b)+(c): `a a* = 1 ≠ a* a`.
* `self_pairing_root` — the self-pairing identity with one exception at the root.
* `signed_zero_divisor` — odd `p`: `α, β ≠ 0`, `αβ = 0` (algebraic part of `thm:D`).
* `oddWitness` — **Prop. 7.11** (paper `prop:oddwitness`): `ab = 1`, `ac = 0`, `c ≠ 0`, `ba ≠ 1`.

## Dart-level (`PortGraph`-style) versions

For graphs given by darts `D` with `origin : D → V`, involutive `rev : D → D` and letters
`label : D → T` with `label (rev d) = bar (label d)` (OpenAI's `PortSubdivision.PortGraph`; also
port alphabets `α × Col` composed with the first projection), the multiplicity of `(x, y)` is
`simultaneousSteps` (pairs of darts at `x`, `y` with equal letters), which equals `|S_x ∩ S_y|`
for immersed graphs (`simultaneousSteps_eq_card_inter`). Results: `dart_signed_handshake`,
`dart_signed_product_zero`, `dart_self_pairing_root`, `dart_parity_product_zero`,
`dart_parity_mul_star_eq_one`, `dart_signed_zero_divisor`, `dart_oddWitness`.
`sign_of_colouring` turns a proper two-colouring into the sign `σ`.
-/

namespace Kaplansky.Parity

open MonoidAlgebra

/-! ### Darts -/

/-- Darts of a graph in which the vertex `x` has outgoing label set `out x`: pairs `(x, t)` with
`t ∈ out x`. Identical to OpenAI's `Factors.DartA` / `Factors.DartB`. -/
abbrev Dart {V T : Type*} (out : V → Finset T) := {p : V × T // p.2 ∈ out p.1}

section Reversal

variable {V T : Type*} {out : V → Finset T} {bar : T → T} {r : Dart out → Dart out}

/-- Reversing the dart `(x·t, t̄)` returns `(x, t)`. -/
lemma rev_mk_end (hl : ∀ d, (r d).val.2 = bar d.val.2) (hr : Function.Involutive r) (d : Dart out)
    (h : bar d.val.2 ∈ out (r d).val.1) : r ⟨((r d).val.1, bar d.val.2), h⟩ = d := by
  have : (⟨((r d).val.1, bar d.val.2), h⟩ : Dart out) = r d :=
    Subtype.ext (Prod.ext rfl (hl d).symm)
  rw [this, hr d]

/-- The label map is involutive on the labels of darts. -/
lemma bar_bar (hl : ∀ d, (r d).val.2 = bar d.val.2) (hr : Function.Involutive r) (d : Dart out) :
    bar (bar d.val.2) = d.val.2 := by
  have h1 := hl (r d)
  rw [hr d, hl d] at h1
  exact h1.symm

/-- The reversed label lies in the end's outgoing set. -/
lemma bar_mem_end (hl : ∀ d, (r d).val.2 = bar d.val.2) (d : Dart out) :
    bar d.val.2 ∈ out (r d).val.1 := by
  rw [← hl d]; exact (r d).property

end Reversal

/-! ### The cancellation core -/

section Core

variable {A B T : Type*} [Fintype A] [Fintype B] [DecidableEq T]

/-- **Signed cancellation core.** Let `f : A → B → M` be anti-invariant under simultaneous steps:
`f (x·t) (y·t) = -f x y` whenever `t ∈ S_x ∩ S_y`. Then `∑_{x,y} |S_x ∩ S_y| • f x y = 0`.
The proof is the fixed-point-free involution `(x, y, t) ↦ (x·t, y·t, t̄)` on simultaneous steps. -/
theorem sum_card_inter_nsmul_eq_zero {M : Type*} [AddCommGroup M]
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (f : A → B → M)
    (hf : ∀ (dA : Dart outA) (dB : Dart outB), dA.val.2 = dB.val.2 →
      f (rA dA).val.1 (rB dB).val.1 = -f dA.val.1 dB.val.1) :
    ∑ x, ∑ y, (outA x ∩ outB y).card • f x y = 0 := by
  classical
  -- the simultaneous steps `(x, y, t)` with `t ∈ S_x ∩ S_y`
  set s : Finset (Σ _ : A × B, T) :=
    (Finset.univ : Finset (A × B)).sigma (fun p => outA p.1 ∩ outB p.2) with hs
  have hsum : ∑ q ∈ s, f q.1.1 q.1.2 = ∑ x, ∑ y, (outA x ∩ outB y).card • f x y := by
    rw [hs, Finset.sum_sigma]
    simp only [Finset.sum_const]
    exact Fintype.sum_prod_type' (fun x y => (outA x ∩ outB y).card • f x y)
  rw [← hsum]
  have memA : ∀ q ∈ s, q.2 ∈ outA q.1.1 := fun q hq =>
    (Finset.mem_inter.mp (Finset.mem_sigma.mp hq).2).1
  have memB : ∀ q ∈ s, q.2 ∈ outB q.1.2 := fun q hq =>
    (Finset.mem_inter.mp (Finset.mem_sigma.mp hq).2).2
  -- the involution
  let ι : ∀ q ∈ s, Σ _ : A × B, T := fun q hq =>
    ⟨((rA ⟨(q.1.1, q.2), memA q hq⟩).val.1, (rB ⟨(q.1.2, q.2), memB q hq⟩).val.1), bar q.2⟩
  have ι_mem : ∀ q hq, ι q hq ∈ s := by
    intro q hq
    refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact bar_mem_end hA ⟨(q.1.1, q.2), memA q hq⟩
    · exact bar_mem_end hB ⟨(q.1.2, q.2), memB q hq⟩
  refine Finset.sum_involution ι ?_ ?_ ι_mem ?_
  · intro q hq
    rw [hf ⟨(q.1.1, q.2), memA q hq⟩ ⟨(q.1.2, q.2), memB q hq⟩ rfl, add_neg_cancel]
  · intro q hq _ heq
    have h2 := congrArg Sigma.snd heq
    exact hbar q.2 h2
  · intro q hq
    obtain ⟨⟨x, y⟩, t⟩ := q
    have hx : t ∈ outA x := memA _ hq
    have hy : t ∈ outB y := memB _ hq
    have e1 := rev_mk_end hA hrA ⟨(x, t), hx⟩ (bar_mem_end hA ⟨(x, t), hx⟩)
    have e2 := rev_mk_end hB hrB ⟨(y, t), hy⟩ (bar_mem_end hB ⟨(y, t), hy⟩)
    have e3 := bar_bar hA hrA ⟨(x, t), hx⟩
    simp only [ι] at e1 e2 e3 ⊢
    rw [Sigma.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [Prod.mk.injEq]
      exact ⟨congrArg (fun d => d.val.1) e1, congrArg (fun d => d.val.1) e2⟩
    · exact heq_of_eq e3

end Core

/-! ### Products of sums of group elements -/

section Products

variable {A B G R : Type*} [Fintype A] [Fintype B] [Group G]

lemma sum_single_mul_sum_single [Semiring R] (u : A → G) (v : B → G) (a : A → R) (b : B → R) :
    (∑ x, single (u x) (a x)) * (∑ y, single (v y) (b y)) =
      ∑ x, ∑ y, single (u x * v y) (a x * b y) := by
  rw [Finset.sum_mul_sum]
  simp only [single_mul_single]

/-- **Lemma 6.1(c)** / Prop. 5.1(c), coefficient form: if `root` is the only vertex with label `1`,
the coefficient of `1` in `∑ σ(x) g_x` is `σ(root)`. -/
theorem coeff_one_sum_single [Semiring R] (root : A) (g : A → G) (σ : A → R)
    (hroot : g root = 1) (hunique : ∀ x, g x = 1 → x = root) :
    (∑ x, single (g x) (σ x)).coeff 1 = σ root := by
  classical
  rw [coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single root]
  · rw [coeff_single, hroot, Finsupp.single_eq_same]
  · intro x _ hx
    rw [coeff_single, Finsupp.single_apply, ite_eq_right (fun h => hx (hunique x h))]
  · intro h; exact absurd (Finset.mem_univ root) h

/-- **Lemma 6.1(c)**: under root protection, `∑ σ(x) g_x ≠ 0` when `σ(root) ≠ 0`. -/
theorem sum_single_ne_zero [Semiring R] (root : A) (g : A → G) (σ : A → R)
    (hroot : g root = 1) (hunique : ∀ x, g x = 1 → x = root) (hσ : σ root ≠ 0) :
    (∑ x, single (g x) (σ x)) ≠ 0 := by
  intro h
  have := coeff_one_sum_single root g σ hroot hunique
  rw [h, coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact hσ this.symm

/-- Root protection for the second factor: `c = ∑ h_y⁻¹ ≠ 0`. -/
theorem sum_single_inv_ne_zero [Semiring R] [Nontrivial R] (root : B) (h : B → G)
    (hroot : h root = 1) (hunique : ∀ y, h y = 1 → y = root) :
    (∑ y, single (h y)⁻¹ (1 : R)) ≠ 0 :=
  sum_single_ne_zero root (fun y => (h y)⁻¹) (fun _ => (1 : R)) (by simp [hroot])
    (fun y hy => hunique y (inv_eq_one.mp hy)) one_ne_zero

/-- From a handshake identity with multiplicities `N x y` that are all `1` in `R`, the product
`(∑ σ(x) g_x)(∑ h_y⁻¹)` vanishes. -/
theorem mul_eq_zero_of_handshake [CommRing R] (g : A → G) (h : B → G) (σ : A → R)
    (N : A → B → R) (hz : ∑ x, ∑ y, single (g x * (h y)⁻¹) (N x y * σ x) = 0)
    (hone : ∀ x y, N x y = 1) :
    (∑ x, single (g x) (σ x)) * (∑ y, single (h y)⁻¹ (1 : R)) = 0 := by
  simp only [hone, one_mul] at hz
  rw [sum_single_mul_sum_single]
  simpa only [mul_one] using hz

/-- From a self-pairing handshake identity whose multiplicities are `1 + [x = x' = root]` in `R`:
`(∑ σ(x) g_x)(∑ g_x⁻¹) = -σ(root)·1`. -/
theorem mul_eq_neg_of_handshake_root [CommRing R] (g : A → G) (σ : A → R) (N : A → A → R)
    (root : A) (hz : ∑ x, ∑ x', single (g x * (g x')⁻¹) (N x x' * σ x) = 0)
    (hone : ∀ x x', (x, x') ≠ (root, root) → N x x' = 1) (htwo : N root root = 2) :
    (∑ x, single (g x) (σ x)) * (∑ x, single (g x)⁻¹ (1 : R)) = -single 1 (σ root) := by
  classical
  have key : ∀ x x', single (g x * (g x')⁻¹) (N x x' * σ x) =
      single (g x * (g x')⁻¹) (σ x) + if x = root ∧ x' = root then single 1 (σ root) else 0 := by
    intro x x'
    by_cases hx : x = root ∧ x' = root
    · obtain ⟨rfl, rfl⟩ := hx
      rw [htwo, ite_eq_left ⟨rfl, rfl⟩, mul_inv_cancel, two_mul, single_add]
    · rw [hone x x' (fun he => hx (Prod.mk.inj he)), one_mul, ite_eq_right hx, add_zero]
  simp only [key, Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Fintype.sum_ite_eq'] at hz
  rw [sum_single_mul_sum_single]
  simp only [mul_one]
  exact eq_neg_of_add_eq_zero_left hz

end Products

/-! ### Lemma 6.1: signed handshake -/

section Handshake

variable {A B T G : Type*} [Fintype A] [Fintype B] [DecidableEq T] [Group G]

/-- **Lemma 6.1(a)** (signed handshake, paper `lem:handshake`). If `σ : A → R` reverses sign along
every edge of the `A`-side graph, then in `R[G]`
`∑_{x ∈ A, y ∈ B} |S_x ∩ S_y| σ(x) g_x h_y⁻¹ = 0`.
Over `R = ℤ` this is identity (6.1) of the paper. -/
theorem signed_handshake {R : Type*} [CommRing R]
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G) (h : B → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (hh : ∀ d : Dart outB, h (rB d).val.1 = h d.val.1 * letter d.val.2)
    (σ : A → R) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1) :
    ∑ x, ∑ y, single (g x * (h y)⁻¹) (((outA x ∩ outB y).card : R) * σ x) = 0 := by
  have hz := sum_card_inter_nsmul_eq_zero outA outB bar rA rB hA hB hrA hrB hbar
    (fun x y => single (g x * (h y)⁻¹) (σ x)) (by
      intro dA dB hl
      rw [hg, hh, hσ, hl, single_neg]
      congr 2
      group)
  simpa only [smul_single, nsmul_eq_mul] using hz

/-- **Lemma 6.1(b)** (signed cancellation). If `|S_x ∩ S_y| = 1` in `R` for all `x, y`, then
`(∑_x σ(x) g_x)(∑_y h_y⁻¹) = 0` in `R[G]`. -/
theorem signed_product_zero {R : Type*} [CommRing R]
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G) (h : B → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (hh : ∀ d : Dart outB, h (rB d).val.1 = h d.val.1 * letter d.val.2)
    (σ : A → R) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1)
    (hone : ∀ x y, ((outA x ∩ outB y).card : R) = 1) :
    (∑ x, single (g x) (σ x)) * (∑ y, single (h y)⁻¹ (1 : R)) = 0 :=
  mul_eq_zero_of_handshake g h σ (fun x y => ((outA x ∩ outB y).card : R))
    (signed_handshake outA outB bar rA rB hA hB hrA hrB hbar letter g h hg hh σ hσ) hone

/-- **Lemma 6.1(b) over `𝔽_p`**: if `|S_x ∩ S_y| ≡ 1 (mod p)` for all `x, y`, then
`(∑_x σ(x) g_x)(∑_y h_y⁻¹) = 0` in `(ZMod p)[G]`. -/
theorem signed_product_zero_zmod {p : ℕ}
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G) (h : B → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (hh : ∀ d : Dart outB, h (rB d).val.1 = h d.val.1 * letter d.val.2)
    (σ : A → ZMod p) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1)
    (hmod : ∀ x y, (outA x ∩ outB y).card ≡ 1 [MOD p]) :
    (∑ x, single (g x) (σ x)) * (∑ y, single (h y)⁻¹ (1 : ZMod p)) = 0 :=
  signed_product_zero outA outB bar rA rB hA hB hrA hrB hbar letter g h hg hh σ hσ
    (fun x y => by rw [(ZMod.natCast_eq_natCast_iff _ 1 p).mpr (hmod x y), Nat.cast_one])

/-- **Lemma 6.1(a), self-pairing variant `B' = A'`**:
`∑_{x, x' ∈ A} |S_x ∩ S_{x'}| σ(x) g_x g_{x'}⁻¹ = 0`. -/
theorem signed_handshake_self {R : Type*} [CommRing R]
    (outA : A → Finset T) (bar : T → T) (rA : Dart outA → Dart outA)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hrA : Function.Involutive rA) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (σ : A → R) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1) :
    ∑ x, ∑ x', single (g x * (g x')⁻¹) (((outA x ∩ outA x').card : R) * σ x) = 0 :=
  signed_handshake outA outA bar rA rA hA hA hrA hrA hbar letter g g hg hg σ hσ

/-- **Lemma 6.1(b), self-pairing variant `B' = A'`**. -/
theorem signed_product_zero_self {R : Type*} [CommRing R]
    (outA : A → Finset T) (bar : T → T) (rA : Dart outA → Dart outA)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hrA : Function.Involutive rA) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (σ : A → R) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1)
    (hone : ∀ x x', ((outA x ∩ outA x').card : R) = 1) :
    (∑ x, single (g x) (σ x)) * (∑ x, single (g x)⁻¹ (1 : R)) = 0 :=
  signed_product_zero outA outA bar rA rA hA hA hrA hrA hbar letter g g hg hg σ hσ hone

/-- **Self-pairing with one exception at the root.** If `|S_x ∩ S_{x'}| = 1` in `R` for
`(x, x') ≠ (root, root)` and `|S_root| = 2` in `R`, then
`(∑_x σ(x) g_x)(∑_x g_x⁻¹) = -σ(root)·1`. -/
theorem self_pairing_root {R : Type*} [CommRing R]
    (outA : A → Finset T) (bar : T → T) (rA : Dart outA → Dart outA)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hrA : Function.Involutive rA) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (σ : A → R) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1) (root : A)
    (hone : ∀ x x', (x, x') ≠ (root, root) → ((outA x ∩ outA x').card : R) = 1)
    (htwo : ((outA root).card : R) = 2) :
    (∑ x, single (g x) (σ x)) * (∑ x, single (g x)⁻¹ (1 : R)) = -single 1 (σ root) :=
  mul_eq_neg_of_handshake_root g σ (fun x x' => ((outA x ∩ outA x').card : R)) root
    (signed_handshake_self outA bar rA hA hrA hbar letter g hg σ hσ) hone
    (by simp only [Finset.inter_self]; exact htwo)

end Handshake

/-! ### Prop. 5.1: OpenAI's parity certificates in characteristic two -/

section CharTwo

variable {A B T G : Type*} [Fintype A] [Fintype B] [DecidableEq T] [Group G]

/-- In `ZMod 2`, the constant sign `1` reverses sign along every edge. -/
lemma one_eq_neg_one_zmod_two : (1 : ZMod 2) = -1 := by decide

lemma natCast_zmod_two_of_odd {n : ℕ} (h : Odd n) : (n : ZMod 2) = 1 :=
  (ZMod.natCast_eq_one_iff_odd).mpr h

/-- **Prop. 5.1(a)** (OpenAI's `Factors.product_zero`, same hypotheses): if every `|S_x ∩ S_y|` is
odd, then `a c = 0` in `𝔽₂[G]`, where `a = ∑ g_x`, `c = ∑ h_y⁻¹`. -/
theorem parity_product_zero
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (hodd : ∀ x y, Odd (outA x ∩ outB y).card)
    (letter : T → G) (g : A → G) (h : B → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (hh : ∀ d : Dart outB, h (rB d).val.1 = h d.val.1 * letter d.val.2) :
    (∑ x, single (g x) (1 : ZMod 2)) * (∑ y, single (h y)⁻¹ (1 : ZMod 2)) = 0 :=
  signed_product_zero outA outB bar rA rB hA hB hrA hrB hbar letter g h hg hh (fun _ => 1)
    (fun _ => one_eq_neg_one_zmod_two) (fun x y => natCast_zmod_two_of_odd (hodd x y))

/-- **Prop. 5.1(b)**: if `|S_x ∩ S_{x'}|` is odd for all `(x, x') ≠ (root, root)` and `|S_root|` is
even, then `a a* = 1` in `𝔽₂[G]`, where `a = ∑ g_x` and `a* = ∑ g_x⁻¹`. -/
theorem parity_mul_star_eq_one
    (outA : A → Finset T) (bar : T → T) (rA : Dart outA → Dart outA)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hrA : Function.Involutive rA) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2) (root : A)
    (hodd : ∀ x x', (x, x') ≠ (root, root) → Odd (outA x ∩ outA x').card)
    (heven : Even (outA root).card) :
    (∑ x, single (g x) (1 : ZMod 2)) * (∑ x, single (g x)⁻¹ (1 : ZMod 2)) = 1 := by
  rw [self_pairing_root outA bar rA hA hrA hbar letter g hg (fun _ => (1 : ZMod 2))
    (fun _ => one_eq_neg_one_zmod_two) root
    (fun x x' hx => natCast_zmod_two_of_odd (hodd x x' hx))
    (by rw [(ZMod.natCast_eq_zero_iff_even).mpr heven]; decide)]
  rw [← single_neg, ← one_eq_neg_one_zmod_two, one_def]

/-- **Prop. 5.1(c)**, nonvanishing (OpenAI's `Factors.sum_nonzero`): if `root` is the only vertex
with label `1`, then `∑ g_x ≠ 0` in `𝔽₂[G]`. -/
theorem parity_sum_ne_zero (root : A) (g : A → G) (hroot : g root = 1)
    (hunique : ∀ x, g x = 1 → x = root) : (∑ x, single (g x) (1 : ZMod 2)) ≠ 0 :=
  sum_single_ne_zero root g (fun _ => (1 : ZMod 2)) hroot hunique one_ne_zero

/-- **Prop. 5.1(c)**, direct finiteness fails: in the situation of (a), if the root `rootB` of the
`B`-side is protected (it is the only vertex with label `1`), then `a* a ≠ 1`, because `a c = 0` and
`c ≠ 0`. Together with `parity_mul_star_eq_one` this gives `a a* = 1 ≠ a* a`. -/
theorem parity_star_mul_ne_one
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (hodd : ∀ x y, Odd (outA x ∩ outB y).card)
    (letter : T → G) (g : A → G) (h : B → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (hh : ∀ d : Dart outB, h (rB d).val.1 = h d.val.1 * letter d.val.2)
    (rootB : B) (hrootB : h rootB = 1) (huniqueB : ∀ y, h y = 1 → y = rootB) :
    (∑ x, single (g x)⁻¹ (1 : ZMod 2)) * (∑ x, single (g x) (1 : ZMod 2)) ≠ 1 := by
  intro h1
  apply sum_single_inv_ne_zero (R := ZMod 2) rootB h hrootB huniqueB
  have hac := parity_product_zero outA outB bar rA rB hA hB hrA hrB hbar hodd letter g h hg hh
  calc (∑ y, single (h y)⁻¹ (1 : ZMod 2))
      = ((∑ x, single (g x)⁻¹ (1 : ZMod 2)) * (∑ x, single (g x) (1 : ZMod 2))) *
          (∑ y, single (h y)⁻¹ (1 : ZMod 2)) := by rw [h1, one_mul]
    _ = 0 := by rw [mul_assoc, hac, mul_zero]

/-- **Prop. 5.1(b)+(c)** combined: under the hypotheses of (a) and (b) and root protection of the
`B`-side, `a = ∑ g_x` and `a* = ∑ g_x⁻¹` satisfy `a a* = 1 ≠ a* a` in `𝔽₂[G]`. -/
theorem parity_not_directlyFinite
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G) (h : B → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (hh : ∀ d : Dart outB, h (rB d).val.1 = h d.val.1 * letter d.val.2)
    (root : A) (hodd : ∀ x x', (x, x') ≠ (root, root) → Odd (outA x ∩ outA x').card)
    (heven : Even (outA root).card) (hcross : ∀ x y, Odd (outA x ∩ outB y).card)
    (rootB : B) (hrootB : h rootB = 1) (huniqueB : ∀ y, h y = 1 → y = rootB) :
    (∑ x, single (g x) (1 : ZMod 2)) * (∑ x, single (g x)⁻¹ (1 : ZMod 2)) = 1 ∧
    (∑ x, single (g x)⁻¹ (1 : ZMod 2)) * (∑ x, single (g x) (1 : ZMod 2)) ≠ 1 :=
  ⟨parity_mul_star_eq_one outA bar rA hA hrA hbar letter g hg root hodd heven,
    parity_star_mul_ne_one outA outB bar rA rB hA hB hrA hrB hbar hcross letter g h hg hh rootB
      hrootB huniqueB⟩

end CharTwo

/-! ### Zero divisors in odd characteristic (paper, Prop. 6.x / `thm:D`, algebraic part) -/

section SignedZeroDivisor

variable {A B T G : Type*} [Fintype A] [Fintype B] [DecidableEq T] [Group G]

/-- **Signed zero divisors** (Lemma 6.1(b),(c)): if `|S_x ∩ S_y| ≡ 1 (mod p)` for all `x, y`, the
`A`-side is bipartite with sign `σ` and `σ(x_A) ≠ 0`, and both roots are protected, then
`α = ∑ σ(x) g_x` and `β = ∑ h_y⁻¹` are non-zero elements of `𝔽_p[G]` with `αβ = 0`. -/
theorem signed_zero_divisor {p : ℕ} [Fact p.Prime]
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G) (h : B → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (hh : ∀ d : Dart outB, h (rB d).val.1 = h d.val.1 * letter d.val.2)
    (σ : A → ZMod p) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1)
    (hcross : ∀ x y, (outA x ∩ outB y).card ≡ 1 [MOD p])
    (rootA : A) (hrootA : g rootA = 1) (huniqueA : ∀ x, g x = 1 → x = rootA)
    (hσroot : σ rootA ≠ 0)
    (rootB : B) (hrootB : h rootB = 1) (huniqueB : ∀ y, h y = 1 → y = rootB) :
    (∑ x, single (g x) (σ x)) ≠ 0 ∧ (∑ y, single (h y)⁻¹ (1 : ZMod p)) ≠ 0 ∧
    (∑ x, single (g x) (σ x)) * (∑ y, single (h y)⁻¹ (1 : ZMod p)) = 0 :=
  ⟨sum_single_ne_zero rootA g σ hrootA huniqueA hσroot,
    sum_single_inv_ne_zero rootB h hrootB huniqueB,
    signed_product_zero_zmod outA outB bar rA rB hA hB hrA hrB hbar letter g h hg hh σ hσ hcross⟩

end SignedZeroDivisor

/-! ### Prop. 7.11: the odd-characteristic witnesses -/

section OddWitness

variable {A B T G : Type*} [Fintype A] [Fintype B] [DecidableEq T] [Group G]

/-- **Prop. 7.11, `ab = 1`** (over any commutative ring). With `|S_x ∩ S_{x'}| = 1 + [x = x' = r]`
in `R` on the root component and `σ(r) = 1`, put `a = ∑ σ(x) g_x` and `b = -∑ g_x⁻¹`. Then
`ab = 1`. -/
theorem oddWitness_mul_eq_one {R : Type*} [CommRing R]
    (outA : A → Finset T) (bar : T → T) (rA : Dart outA → Dart outA)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hrA : Function.Involutive rA) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (σ : A → R) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1) (root : A)
    (hσroot : σ root = 1)
    (hone : ∀ x x', (x, x') ≠ (root, root) → ((outA x ∩ outA x').card : R) = 1)
    (htwo : ((outA root).card : R) = 2) :
    (∑ x, single (g x) (σ x)) * (-∑ x, single (g x)⁻¹ (1 : R)) = 1 := by
  rw [mul_neg, self_pairing_root outA bar rA hA hrA hbar letter g hg σ hσ root hone htwo, hσroot,
    neg_neg, one_def]

/-- **Prop. 7.11** (paper `prop:oddwitness`). Let `A` be the root component (with root `r`) and `B`
the component of `x_B`, over a common alphabet. Assume
* the `A`-side is bipartite with sign `σ`, i.e. `σ(x·t) = -σ(x)`, and `σ(r) = 1`;
* `|S_x ∩ S_{x'}| ≡ 1 + [x = x' = r] (mod p)` for `x, x' ∈ A`
  (stated as `≡ 1` off `(r, r)` and `|S_r| ≡ 2`);
* `|S_x ∩ S_y| ≡ 1 (mod p)` for `x ∈ A`, `y ∈ B`;
* root protection of `x_B`: `h_{x_B} = 1` and `h_y = 1 → y = x_B`.

Put `a = ∑ σ(x) g_x`, `b = -∑ g_x⁻¹` and `c = ∑ h_y⁻¹` in `𝔽_p[G]`. Then `ab = 1`, `ac = 0`,
`c ≠ 0`, and hence `ba ≠ 1`. -/
theorem oddWitness {p : ℕ} [Fact p.Prime]
    (outA : A → Finset T) (outB : B → Finset T) (bar : T → T)
    (rA : Dart outA → Dart outA) (rB : Dart outB → Dart outB)
    (hA : ∀ d, (rA d).val.2 = bar d.val.2) (hB : ∀ d, (rB d).val.2 = bar d.val.2)
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) (hbar : ∀ t, bar t ≠ t)
    (letter : T → G) (g : A → G) (h : B → G)
    (hg : ∀ d : Dart outA, g (rA d).val.1 = g d.val.1 * letter d.val.2)
    (hh : ∀ d : Dart outB, h (rB d).val.1 = h d.val.1 * letter d.val.2)
    (σ : A → ZMod p) (hσ : ∀ d : Dart outA, σ (rA d).val.1 = -σ d.val.1)
    (root : A) (hσroot : σ root = 1)
    (hself : ∀ x x', (x, x') ≠ (root, root) → (outA x ∩ outA x').card ≡ 1 [MOD p])
    (hroot : (outA root).card ≡ 2 [MOD p])
    (hcross : ∀ x y, (outA x ∩ outB y).card ≡ 1 [MOD p])
    (rootB : B) (hrootB : h rootB = 1) (huniqueB : ∀ y, h y = 1 → y = rootB) :
    (∑ x, single (g x) (σ x)) * (-∑ x, single (g x)⁻¹ (1 : ZMod p)) = 1 ∧
    (∑ x, single (g x) (σ x)) * (∑ y, single (h y)⁻¹ (1 : ZMod p)) = 0 ∧
    (∑ y, single (h y)⁻¹ (1 : ZMod p)) ≠ 0 ∧
    (-∑ x, single (g x)⁻¹ (1 : ZMod p)) * (∑ x, single (g x) (σ x)) ≠ 1 := by
  have hab := oddWitness_mul_eq_one outA bar rA hA hrA hbar letter g hg σ hσ root hσroot
    (fun x x' hx => by rw [(ZMod.natCast_eq_natCast_iff _ 1 p).mpr (hself x x' hx), Nat.cast_one])
    (by rw [(ZMod.natCast_eq_natCast_iff _ 2 p).mpr hroot]; norm_num)
  have hac := signed_product_zero_zmod outA outB bar rA rB hA hB hrA hrB hbar letter g h hg hh σ hσ
    hcross
  have hc := sum_single_inv_ne_zero (R := ZMod p) rootB h hrootB huniqueB
  refine ⟨hab, hac, hc, ?_⟩
  intro hba
  apply hc
  calc (∑ y, single (h y)⁻¹ (1 : ZMod p))
      = ((-∑ x, single (g x)⁻¹ (1 : ZMod p)) * (∑ x, single (g x) (σ x))) *
          (∑ y, single (h y)⁻¹ (1 : ZMod p)) := by rw [hba, one_mul]
    _ = 0 := by rw [mul_assoc, hac, mul_zero]

end OddWitness

/-! ### Dart-level (`PortGraph`-style) handshake

The same identities for graphs given by darts `D` with `origin : D → V`, an involutive reversal
`rev : D → D` and labels `label : D → T` (`label (rev d) = bar (label d)`), as in OpenAI's
`PortSubdivision.PortGraph`. The multiplicity of `(x, y)` is the number `simultaneousSteps` of pairs
of darts at `x` and `y` with equal labels; for immersed graphs it is `|S_x ∩ S_y|`
(`simultaneousSteps_eq_card_inter`). -/

section DartLevel

variable {V W D E T G : Type*} [Fintype V] [Fintype W] [Fintype D] [Fintype E]
  [DecidableEq V] [DecidableEq W] [DecidableEq T] [Group G]

/-- The number of simultaneous steps at `(x, y)`: pairs of darts `(d, e)` with `d` leaving `x`,
`e` leaving `y`, and equal labels. -/
def simultaneousSteps (originA : D → V) (labelA : D → T) (originB : E → W) (labelB : E → T)
    (x : V) (y : W) : ℕ :=
  (Finset.univ.filter fun q : D × E =>
    originA q.1 = x ∧ originB q.2 = y ∧ labelA q.1 = labelB q.2).card

omit [Fintype V] [Fintype W] in
/-- For immersed graphs (distinct darts at a vertex have distinct labels), the number of
simultaneous steps at `(x, y)` is `|S_x ∩ S_y|`, where `S_x` is the set of labels at `x`. -/
theorem simultaneousSteps_eq_card_inter (originA : D → V) (labelA : D → T) (originB : E → W)
    (labelB : E → T)
    (himmA : ∀ d d', originA d = originA d' → labelA d = labelA d' → d = d')
    (himmB : ∀ e e', originB e = originB e' → labelB e = labelB e' → e = e') (x : V) (y : W) :
    simultaneousSteps originA labelA originB labelB x y =
      ((Finset.univ.filter fun d => originA d = x).image labelA ∩
        (Finset.univ.filter fun e => originB e = y).image labelB).card := by
  unfold simultaneousSteps
  refine Finset.card_bij (fun q _ => labelA q.1) ?_ ?_ ?_
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hq).2
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨q.1, ?_, rfl⟩,
      Finset.mem_image.mpr ⟨q.2, ?_, h3.symm⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
  · intro q hq q' hq' he
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hq).2
    obtain ⟨h1', h2', h3'⟩ := (Finset.mem_filter.mp hq').2
    have e1 : q.1 = q'.1 := himmA _ _ (h1.trans h1'.symm) he
    have e2 : q.2 = q'.2 := himmB _ _ (h2.trans h2'.symm) (h3.symm.trans (he.trans h3'))
    exact Prod.ext e1 e2
  · intro t ht
    obtain ⟨htA, htB⟩ := Finset.mem_inter.mp ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp htA
    obtain ⟨e, he, het⟩ := Finset.mem_image.mp htB
    exact ⟨(d, e), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hd).2, (Finset.mem_filter.mp he).2, het.symm⟩, rfl⟩

/-- **Dart-level cancellation core**: for `f` anti-invariant under simultaneous steps,
`∑_{x,y} N(x, y) • f x y = 0`, where `N = simultaneousSteps`. -/
theorem dart_sum_nsmul_eq_zero {M : Type*} [AddCommGroup M]
    (originA : D → V) (revA : D → D) (labelA : D → T)
    (originB : E → W) (revB : E → E) (labelB : E → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hrB : Function.Involutive revB)
    (hlA : ∀ d, labelA (revA d) = bar (labelA d)) (hlB : ∀ e, labelB (revB e) = bar (labelB e))
    (hbar : ∀ t, bar t ≠ t) (f : V → W → M)
    (hf : ∀ d e, labelA d = labelB e →
      f (originA (revA d)) (originB (revB e)) = -f (originA d) (originB e)) :
    ∑ x, ∑ y, simultaneousSteps originA labelA originB labelB x y • f x y = 0 := by
  classical
  set s := Finset.univ.filter fun q : D × E => labelA q.1 = labelB q.2 with hs
  have hsum : ∑ q ∈ s, f (originA q.1) (originB q.2) =
      ∑ x, ∑ y, simultaneousSteps originA labelA originB labelB x y • f x y := by
    rw [← Finset.sum_fiberwise_of_maps_to' (s := s) (t := Finset.univ)
      (g := fun q : D × E => (originA q.1, originB q.2)) (fun _ _ => Finset.mem_univ _)
      (fun j : V × W => f j.1 j.2)]
    rw [← Fintype.sum_prod_type' (fun x y => simultaneousSteps originA labelA originB labelB x y •
      f x y)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const]
    congr 1
    unfold simultaneousSteps
    rw [hs, Finset.filter_filter]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
    tauto
  rw [← hsum]
  refine Finset.sum_involution (fun q _ => (revA q.1, revB q.2)) ?_ ?_ ?_ ?_
  · intro q hq
    rw [hf q.1 q.2 (Finset.mem_filter.mp hq).2, add_neg_cancel]
  · intro q hq _ heq
    have h1 := congrArg (fun q : D × E => labelA q.1) heq
    simp only [hlA] at h1
    exact hbar _ h1
  · intro q hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [hlA, hlB, (Finset.mem_filter.mp hq).2]
  · intro q _
    simp only [hrA q.1, hrB q.2]

/-- **Lemma 6.1(a), dart level.** If `σ` reverses sign along every edge of the `A`-side, then
`∑_{x,y} N(x, y) σ(x) g_x h_y⁻¹ = 0` in `R[G]`, `N = simultaneousSteps`. -/
theorem dart_signed_handshake {R : Type*} [CommRing R]
    (originA : D → V) (revA : D → D) (labelA : D → T)
    (originB : E → W) (revB : E → E) (labelB : E → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hrB : Function.Involutive revB)
    (hlA : ∀ d, labelA (revA d) = bar (labelA d)) (hlB : ∀ e, labelB (revB e) = bar (labelB e))
    (hbar : ∀ t, bar t ≠ t) (letter : T → G) (g : V → G) (h : W → G)
    (hg : ∀ d, g (originA (revA d)) = g (originA d) * letter (labelA d))
    (hh : ∀ e, h (originB (revB e)) = h (originB e) * letter (labelB e))
    (σ : V → R) (hσ : ∀ d, σ (originA (revA d)) = -σ (originA d)) :
    ∑ x, ∑ y, single (g x * (h y)⁻¹)
      ((simultaneousSteps originA labelA originB labelB x y : R) * σ x) = 0 := by
  have hz := dart_sum_nsmul_eq_zero originA revA labelA originB revB labelB bar hrA hrB hlA hlB hbar
    (fun x y => single (g x * (h y)⁻¹) (σ x)) (by
      intro d e hl
      rw [hg, hh, hσ, hl, single_neg]
      congr 2
      group)
  simpa only [smul_single, nsmul_eq_mul] using hz

/-- **Lemma 6.1(b), dart level**: if every `N(x, y) = 1` in `R`, then
`(∑ σ(x) g_x)(∑ h_y⁻¹) = 0`. -/
theorem dart_signed_product_zero {R : Type*} [CommRing R]
    (originA : D → V) (revA : D → D) (labelA : D → T)
    (originB : E → W) (revB : E → E) (labelB : E → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hrB : Function.Involutive revB)
    (hlA : ∀ d, labelA (revA d) = bar (labelA d)) (hlB : ∀ e, labelB (revB e) = bar (labelB e))
    (hbar : ∀ t, bar t ≠ t) (letter : T → G) (g : V → G) (h : W → G)
    (hg : ∀ d, g (originA (revA d)) = g (originA d) * letter (labelA d))
    (hh : ∀ e, h (originB (revB e)) = h (originB e) * letter (labelB e))
    (σ : V → R) (hσ : ∀ d, σ (originA (revA d)) = -σ (originA d))
    (hone : ∀ x y, (simultaneousSteps originA labelA originB labelB x y : R) = 1) :
    (∑ x, single (g x) (σ x)) * (∑ y, single (h y)⁻¹ (1 : R)) = 0 :=
  mul_eq_zero_of_handshake g h σ
    (fun x y => (simultaneousSteps originA labelA originB labelB x y : R))
    (dart_signed_handshake originA revA labelA originB revB labelB bar hrA hrB hlA hlB hbar letter
      g h hg hh σ hσ) hone

/-- **Self-pairing with a root exception, dart level** (Prop. 5.1(b) and Prop. 7.11): if
`N(x, x') = 1` for `(x, x') ≠ (root, root)` and `N(root, root) = 2` in `R`, then
`(∑ σ(x) g_x)(∑ g_x⁻¹) = -σ(root)·1`. -/
theorem dart_self_pairing_root {R : Type*} [CommRing R]
    (originA : D → V) (revA : D → D) (labelA : D → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hlA : ∀ d, labelA (revA d) = bar (labelA d))
    (hbar : ∀ t, bar t ≠ t) (letter : T → G) (g : V → G)
    (hg : ∀ d, g (originA (revA d)) = g (originA d) * letter (labelA d))
    (σ : V → R) (hσ : ∀ d, σ (originA (revA d)) = -σ (originA d)) (root : V)
    (hone : ∀ x x', (x, x') ≠ (root, root) →
      (simultaneousSteps originA labelA originA labelA x x' : R) = 1)
    (htwo : (simultaneousSteps originA labelA originA labelA root root : R) = 2) :
    (∑ x, single (g x) (σ x)) * (∑ x, single (g x)⁻¹ (1 : R)) = -single 1 (σ root) :=
  mul_eq_neg_of_handshake_root g σ
    (fun x x' => (simultaneousSteps originA labelA originA labelA x x' : R)) root
    (dart_signed_handshake originA revA labelA originA revA labelA bar hrA hrA hlA hlA hbar letter
      g g hg hg σ hσ) hone htwo

/-- **Prop. 5.1(b), dart level**: if `N(x, x')` is odd for `(x, x') ≠ (root, root)` and
`N(root, root)` is even, then `a a* = 1` in `𝔽₂[G]`. -/
theorem dart_parity_mul_star_eq_one
    (originA : D → V) (revA : D → D) (labelA : D → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hlA : ∀ d, labelA (revA d) = bar (labelA d))
    (hbar : ∀ t, bar t ≠ t) (letter : T → G) (g : V → G)
    (hg : ∀ d, g (originA (revA d)) = g (originA d) * letter (labelA d)) (root : V)
    (hodd : ∀ x x', (x, x') ≠ (root, root) →
      Odd (simultaneousSteps originA labelA originA labelA x x'))
    (heven : Even (simultaneousSteps originA labelA originA labelA root root)) :
    (∑ x, single (g x) (1 : ZMod 2)) * (∑ x, single (g x)⁻¹ (1 : ZMod 2)) = 1 := by
  rw [dart_self_pairing_root originA revA labelA bar hrA hlA hbar letter g hg
    (fun _ => (1 : ZMod 2)) (fun _ => one_eq_neg_one_zmod_two) root
    (fun x x' hx => natCast_zmod_two_of_odd (hodd x x' hx))
    (by rw [(ZMod.natCast_eq_zero_iff_even).mpr heven]; decide)]
  rw [← single_neg, ← one_eq_neg_one_zmod_two, one_def]

/-- **Prop. 5.1(a), dart level** (OpenAI's `Factors.product_zero` for port graphs): if every
`N(x, y)` is odd, then `(∑ g_x)(∑ h_y⁻¹) = 0` in `𝔽₂[G]`. -/
theorem dart_parity_product_zero
    (originA : D → V) (revA : D → D) (labelA : D → T)
    (originB : E → W) (revB : E → E) (labelB : E → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hrB : Function.Involutive revB)
    (hlA : ∀ d, labelA (revA d) = bar (labelA d)) (hlB : ∀ e, labelB (revB e) = bar (labelB e))
    (hbar : ∀ t, bar t ≠ t) (letter : T → G) (g : V → G) (h : W → G)
    (hg : ∀ d, g (originA (revA d)) = g (originA d) * letter (labelA d))
    (hh : ∀ e, h (originB (revB e)) = h (originB e) * letter (labelB e))
    (hodd : ∀ x y, Odd (simultaneousSteps originA labelA originB labelB x y)) :
    (∑ x, single (g x) (1 : ZMod 2)) * (∑ y, single (h y)⁻¹ (1 : ZMod 2)) = 0 :=
  dart_signed_product_zero originA revA labelA originB revB labelB bar hrA hrB hlA hlB hbar letter
    g h hg hh (fun _ => 1) (fun _ => one_eq_neg_one_zmod_two)
    (fun x y => natCast_zmod_two_of_odd (hodd x y))

/-- **Prop. 7.11, dart level** (paper `prop:oddwitness`): with `N` the number of simultaneous steps,
assume `N(x, x') ≡ 1 (mod p)` on `A × A` off `(root, root)`, `N(root, root) ≡ 2`, `N(x, y) ≡ 1` on
`A × B`, `σ` reverses along edges with `σ(root) = 1`, and `x_B` is protected. Then
`a = ∑ σ(x) g_x`, `b = -∑ g_x⁻¹`, `c = ∑ h_y⁻¹` satisfy `ab = 1`, `ac = 0`, `c ≠ 0`, `ba ≠ 1`. -/
theorem dart_oddWitness {p : ℕ} [Fact p.Prime]
    (originA : D → V) (revA : D → D) (labelA : D → T)
    (originB : E → W) (revB : E → E) (labelB : E → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hrB : Function.Involutive revB)
    (hlA : ∀ d, labelA (revA d) = bar (labelA d)) (hlB : ∀ e, labelB (revB e) = bar (labelB e))
    (hbar : ∀ t, bar t ≠ t) (letter : T → G) (g : V → G) (h : W → G)
    (hg : ∀ d, g (originA (revA d)) = g (originA d) * letter (labelA d))
    (hh : ∀ e, h (originB (revB e)) = h (originB e) * letter (labelB e))
    (σ : V → ZMod p) (hσ : ∀ d, σ (originA (revA d)) = -σ (originA d))
    (root : V) (hσroot : σ root = 1)
    (hself : ∀ x x', (x, x') ≠ (root, root) →
      simultaneousSteps originA labelA originA labelA x x' ≡ 1 [MOD p])
    (hroot : simultaneousSteps originA labelA originA labelA root root ≡ 2 [MOD p])
    (hcross : ∀ x y, simultaneousSteps originA labelA originB labelB x y ≡ 1 [MOD p])
    (rootB : W) (hrootB : h rootB = 1) (huniqueB : ∀ y, h y = 1 → y = rootB) :
    (∑ x, single (g x) (σ x)) * (-∑ x, single (g x)⁻¹ (1 : ZMod p)) = 1 ∧
    (∑ x, single (g x) (σ x)) * (∑ y, single (h y)⁻¹ (1 : ZMod p)) = 0 ∧
    (∑ y, single (h y)⁻¹ (1 : ZMod p)) ≠ 0 ∧
    (-∑ x, single (g x)⁻¹ (1 : ZMod p)) * (∑ x, single (g x) (σ x)) ≠ 1 := by
  have hab : (∑ x, single (g x) (σ x)) * (-∑ x, single (g x)⁻¹ (1 : ZMod p)) = 1 := by
    rw [mul_neg, dart_self_pairing_root originA revA labelA bar hrA hlA hbar letter g hg σ hσ root
      (fun x x' hx => by
        rw [(ZMod.natCast_eq_natCast_iff _ 1 p).mpr (hself x x' hx), Nat.cast_one])
      (by rw [(ZMod.natCast_eq_natCast_iff _ 2 p).mpr hroot]; norm_num), hσroot, neg_neg, one_def]
  have hac := dart_signed_product_zero originA revA labelA originB revB labelB bar hrA hrB hlA hlB
    hbar letter g h hg hh σ hσ
    (fun x y => by rw [(ZMod.natCast_eq_natCast_iff _ 1 p).mpr (hcross x y), Nat.cast_one])
  have hc := sum_single_inv_ne_zero (R := ZMod p) rootB h hrootB huniqueB
  refine ⟨hab, hac, hc, ?_⟩
  intro hba
  apply hc
  calc (∑ y, single (h y)⁻¹ (1 : ZMod p))
      = ((-∑ x, single (g x)⁻¹ (1 : ZMod p)) * (∑ x, single (g x) (σ x))) *
          (∑ y, single (h y)⁻¹ (1 : ZMod p)) := by rw [hba, one_mul]
    _ = 0 := by rw [mul_assoc, hac, mul_zero]

/-- **Signed zero divisors, dart level** (Lemma 6.1(b),(c)): if `N(x, y) ≡ 1 (mod p)` for all
`x, y`, `σ` reverses along edges with `σ(x_A) ≠ 0`, and both roots are protected, then
`α = ∑ σ(x) g_x` and `β = ∑ h_y⁻¹` are non-zero with `αβ = 0` in `𝔽_p[G]`. -/
theorem dart_signed_zero_divisor {p : ℕ} [Fact p.Prime]
    (originA : D → V) (revA : D → D) (labelA : D → T)
    (originB : E → W) (revB : E → E) (labelB : E → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hrB : Function.Involutive revB)
    (hlA : ∀ d, labelA (revA d) = bar (labelA d)) (hlB : ∀ e, labelB (revB e) = bar (labelB e))
    (hbar : ∀ t, bar t ≠ t) (letter : T → G) (g : V → G) (h : W → G)
    (hg : ∀ d, g (originA (revA d)) = g (originA d) * letter (labelA d))
    (hh : ∀ e, h (originB (revB e)) = h (originB e) * letter (labelB e))
    (σ : V → ZMod p) (hσ : ∀ d, σ (originA (revA d)) = -σ (originA d))
    (hcross : ∀ x y, simultaneousSteps originA labelA originB labelB x y ≡ 1 [MOD p])
    (rootA : V) (hrootA : g rootA = 1) (huniqueA : ∀ x, g x = 1 → x = rootA)
    (hσroot : σ rootA ≠ 0)
    (rootB : W) (hrootB : h rootB = 1) (huniqueB : ∀ y, h y = 1 → y = rootB) :
    (∑ x, single (g x) (σ x)) ≠ 0 ∧ (∑ y, single (h y)⁻¹ (1 : ZMod p)) ≠ 0 ∧
    (∑ x, single (g x) (σ x)) * (∑ y, single (h y)⁻¹ (1 : ZMod p)) = 0 :=
  ⟨sum_single_ne_zero rootA g σ hrootA huniqueA hσroot,
    sum_single_inv_ne_zero rootB h hrootB huniqueB,
    dart_signed_product_zero originA revA labelA originB revB labelB bar hrA hrB hlA hlB hbar letter
      g h hg hh σ hσ
      (fun x y => by rw [(ZMod.natCast_eq_natCast_iff _ 1 p).mpr (hcross x y), Nat.cast_one])⟩

end DartLevel

/-! ### Signs from two-colourings -/

/-- A proper two-colouring `colour` of the `A`-side (every edge changes the colour) gives the sign
`σ = ±1` that reverses along edges, as required by the signed handshake. Stated for arbitrary darts
with `origin` and `rev`; for `Dart outA` take `origin := fun d => d.val.1`. -/
theorem sign_of_colouring {V D R : Type*} [Ring R] (origin : D → V) (rev : D → D)
    (colour : V → Bool) (hcol : ∀ d, colour (origin (rev d)) = !colour (origin d)) (d : D) :
    (if colour (origin (rev d)) then (1 : R) else -1) =
      -(if colour (origin d) then (1 : R) else -1) := by
  rw [hcol]
  cases colour (origin d) <;> simp

end Kaplansky.Parity
