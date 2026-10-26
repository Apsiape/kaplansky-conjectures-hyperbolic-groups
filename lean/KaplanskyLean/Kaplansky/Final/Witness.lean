import Kaplansky.Parity.Certificates

/-!
# The algebraic witness for a pattern-free two-sided graph (paper Prop. 5.1, Prop. 7.11)

A purely algebraic bridge between the certificates of `Kaplansky.Parity` and the concrete
random models. The data are those of a sampled graph `Γ = Γ_A ⊔ Γ_B`:

* darts `DA`, `DB` with origins, involutive reversals and letters in an alphabet `T` with a
  fixed-point-free involution `bar` (`label (rev d) = bar (label d)`), immersed on both sides;
* the types `outA x`, `outB y` (the letters of the darts at a vertex);
* path labels `gA : VA → G`, `gB : VB → G` into a group with `g (x·t) = g x · letter t` (in the
  cone group: the route values `GraphPresentation.value`);
* a sign `σ` on `A` reversing along edges, `σ(root) = 1`;
* the type congruences `|S_x ∩ S_x'| ≡ 1 + [x = x' = r] (mod p)` on `A` and
  `|S_x ∩ S_y| ≡ 1 (mod p)` across;
* root protection of `rootB` on its component `reach` (Theorem B (ii)).

Then `𝔽_p[G]` is not directly finite (`exists_not_directlyFinite`). For `p = 2` one takes `σ = 1`
(`-1 = 1`), and the congruences are the parity conditions of Prop. 5.1.

The `B` side is restricted to the component of `rootB` (a subtype), so that root protection gives
uniqueness of the vertex with trivial label; the `A` side is used in full.
-/

namespace Kaplansky.Final

open MonoidAlgebra Finset Kaplansky.Parity

section Witness

variable {VA VB DA DB T G : Type*} [Fintype VA] [Fintype VB] [Fintype DA] [Fintype DB]
  [DecidableEq VA] [DecidableEq VB] [DecidableEq T] [Group G]

/-- **Prop. 7.11 / Prop. 5.1(b),(c) for a sampled graph.** Under the hypotheses above,
`a = ∑_x σ(x) g_x` and `b = -∑_x g_x⁻¹` (with `g_x = g_r⁻¹ gA x`) satisfy `ab = 1 ≠ ba` in
`𝔽_p[G]`. -/
theorem exists_not_directlyFinite {p : ℕ} [Fact p.Prime]
    (originA : DA → VA) (revA : DA → DA) (labA : DA → T)
    (originB : DB → VB) (revB : DB → DB) (labB : DB → T) (bar : T → T)
    (hrA : Function.Involutive revA) (hrB : Function.Involutive revB)
    (hlA : ∀ d, labA (revA d) = bar (labA d)) (hlB : ∀ e, labB (revB e) = bar (labB e))
    (hbar : ∀ t, bar t ≠ t)
    (himmA : ∀ d d', originA d = originA d' → labA d = labA d' → d = d')
    (himmB : ∀ e e', originB e = originB e' → labB e = labB e' → e = e')
    (outA : VA → Finset T) (outB : VB → Finset T)
    (houtA : ∀ x, (univ.filter fun d => originA d = x).image labA = outA x)
    (houtB : ∀ y, (univ.filter fun e => originB e = y).image labB = outB y)
    (letter : T → G) (gA : VA → G) (gB : VB → G)
    (hgA : ∀ d, gA (originA (revA d)) = gA (originA d) * letter (labA d))
    (hgB : ∀ e, gB (originB (revB e)) = gB (originB e) * letter (labB e))
    (σ : VA → ZMod p) (hσ : ∀ d, σ (originA (revA d)) = -σ (originA d))
    (rootA : VA) (hσroot : σ rootA = 1)
    (hself : ∀ x x', (x, x') ≠ (rootA, rootA) → (outA x ∩ outA x').card ≡ 1 [MOD p])
    (hroot : (outA rootA).card ≡ 2 [MOD p])
    (hcross : ∀ x y, (outA x ∩ outB y).card ≡ 1 [MOD p])
    (reach : VB → Prop) (rootB : VB) (hreach : reach rootB)
    (hreachrev : ∀ e, reach (originB e) → reach (originB (revB e)))
    (hprot : ∀ y, reach y → gB y = gB rootB → y = rootB) :
    ∃ a b : MonoidAlgebra (ZMod p) G, a * b = 1 ∧ b * a ≠ 1 := by
  classical
  let originB' : {e : DB // reach (originB e)} → {y : VB // reach y} :=
    fun e => ⟨originB e.1, e.2⟩
  let revB' : {e : DB // reach (originB e)} → {e : DB // reach (originB e)} :=
    fun e => ⟨revB e.1, hreachrev e.1 e.2⟩
  let labB' : {e : DB // reach (originB e)} → T := fun e => labB e.1
  let g : VA → G := fun x => (gA rootA)⁻¹ * gA x
  let h : {y : VB // reach y} → G := fun y => (gB rootB)⁻¹ * gB y.1
  have hg : ∀ d, g (originA (revA d)) = g (originA d) * letter (labA d) := by
    intro d
    simp only [g, hgA, mul_assoc]
  have hh : ∀ e, h (originB' (revB' e)) = h (originB' e) * letter (labB' e) := by
    intro e
    simp only [h, originB', revB', labB', hgB, mul_assoc]
  have hrB' : Function.Involutive revB' := fun e => Subtype.ext (hrB e.1)
  have hlB' : ∀ e, labB' (revB' e) = bar (labB' e) := fun e => hlB e.1
  have himmB' : ∀ e e', originB' e = originB' e' → labB' e = labB' e' → e = e' :=
    fun e e' ho hl => Subtype.ext (himmB _ _ (congrArg Subtype.val ho) hl)
  have houtB' : ∀ y : {y : VB // reach y},
      (univ.filter fun e => originB' e = y).image labB' = outB y.1 := by
    intro y
    rw [← houtB y.1]
    ext t
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.1, congrArg Subtype.val he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he ▸ y.2⟩, Subtype.ext he, rfl⟩
  have hNA : ∀ x x', simultaneousSteps originA labA originA labA x x' =
      (outA x ∩ outA x').card := by
    intro x x'
    rw [simultaneousSteps_eq_card_inter originA labA originA labA himmA himmA, houtA, houtA]
  have hNB : ∀ x (y : {y : VB // reach y}), simultaneousSteps originA labA originB' labB' x y =
      (outA x ∩ outB y.1).card := by
    intro x y
    rw [simultaneousSteps_eq_card_inter originA labA originB' labB' himmA himmB', houtA, houtB']
  obtain ⟨hab, -, -, hba⟩ := dart_oddWitness originA revA labA originB' revB' labB' bar hrA hrB'
    hlA hlB' hbar letter g h hg hh σ hσ rootA hσroot
    (fun x x' hx => by rw [hNA]; exact hself x x' hx)
    (by rw [hNA, Finset.inter_self]; exact hroot)
    (fun x y => by rw [hNB]; exact hcross x y.1)
    ⟨rootB, hreach⟩ (by simp only [h, inv_mul_cancel])
    (fun y hy => Subtype.ext (hprot y.1 y.2 (inv_mul_eq_one.mp hy).symm))
  exact ⟨_, _, hab, hba⟩

end Witness

end Kaplansky.Final
