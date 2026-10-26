import Kaplansky.OddDesign.Perron
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Squared-word decay in exponential form (Lemma 7.8)

From `∑_{W ∈ T^{h+1}} P(W)^2 ≤ p^2 |T| ρ^h` with `ρ = 1 - 1/(2(q+1))`:

* `decay_exp`: for `h ≥ h₀ = 8 (q+1) p^2 |T|`, `∑_{W ∈ T^h} P(W)^2 ≤ exp(-2 δ h)` with
  `δ = 1/(8(q+1))` (all constants natural numbers, as agent D's chain wants);
* `decay_paper`: the paper's form, `δ = -¼ log ρ > 0` and `∑_{W ∈ T^h} P(W)^2 ≤ e^{-2δh}` for all
  sufficiently large `h`;
* `log_le_A₀`: `2 log (q+1) ≤ 2(q+1)`, the bin constant `a₀`.
-/

set_option linter.unusedSectionVars false

namespace Kaplansky.OddDesign

open Finset

/-- A geometric squared-word bound `C (1 - 1/(2Q))^h` gives exponential decay with
`δ = 1/(8Q)` from `h ≥ 8 Q C` on. -/
theorem decay_exp_of_geometric {T : Type*} [Fintype T] (w : T → T → ℝ) (C Q : ℝ)
    (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (hbound : ∀ h : ℕ, ∑ W : Fin (h + 1) → T, wordWeight w (h + 1) W ^ 2 ≤
      C * (1 - 1 / (2 * Q)) ^ h)
    (h : ℕ) (hh : 8 * Q * C ≤ h) :
    ∑ W : Fin h → T, wordWeight w h W ^ 2 ≤ Real.exp (-2 * (1 / (8 * Q)) * h) := by
  have hQ0 : 0 < Q := by linarith
  have hQC : 1 ≤ Q * C := by nlinarith
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by
    have : (1 : ℝ) ≤ h := by nlinarith
    have : 1 ≤ h := by exact_mod_cast this
    omega⟩
  push_cast at hh ⊢
  have hρ0 : 0 ≤ 1 - 1 / (2 * Q) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hρ : 1 - 1 / (2 * Q) ≤ Real.exp (-(1 / (2 * Q))) := by
    have := Real.add_one_le_exp (-(1 / (2 * Q))); linarith
  have hkey : C ≤ Real.exp ((k - 1) / (4 * Q)) := by
    have h1 : C ≤ (k - 1) / (4 * Q) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have h2 := Real.add_one_le_exp ((k - 1) / (4 * Q))
    linarith
  calc ∑ W : Fin (k + 1) → T, wordWeight w (k + 1) W ^ 2 ≤ C * (1 - 1 / (2 * Q)) ^ k :=
        hbound k
    _ ≤ C * Real.exp (-(1 / (2 * Q))) ^ k := by gcongr
    _ = C * Real.exp (k * (-(1 / (2 * Q)))) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp ((k - 1) / (4 * Q)) * Real.exp (k * (-(1 / (2 * Q)))) := by
        gcongr
    _ = Real.exp (-2 * (1 / (8 * Q)) * (k + 1)) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring

/-- `2 log (q+1) ≤ 2 (q+1)`. -/
theorem log_le_A₀ (p : ℕ) : 2 * Real.log ((q p : ℝ) + 1) ≤ ((2 * (q p + 1) : ℕ) : ℝ) := by
  have hq : (0 : ℝ) ≤ q p := Nat.cast_nonneg _
  have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (q p : ℝ) + 1)
  push_cast
  linarith

section Split

variable {T : Type*} [Fintype T] [DecidableEq T]
variable {bar : T → T} {extra : T → Prop} [DecidablePred extra]

/-- **Lemma 7.8**, exponential form with natural constants: `δ = 1/D`, `D = 8(q+1)`, and
`h₀ = 8 (q+1) p^2 |T|`. -/
theorem decay_exp {p : ℕ} (hp : 3 ≤ p) (hbar : Function.Involutive bar)
    (hbarE : ∀ t, extra t → ¬ extra (bar t))
    (hO : (univ.filter (fun u => ¬ extra u)).card = v p)
    (hE : (univ.filter extra).card = s p) (h : ℕ)
    (hh : 8 * (q p + 1) * (p ^ 2 * Fintype.card T) ≤ h) :
    ∑ W : Fin h → T, wordWeight (turnW p bar extra) h W ^ 2 ≤
      Real.exp (-2 * (1 / ((8 * (q p + 1) : ℕ) : ℝ)) * h) := by
  have hT : 1 ≤ Fintype.card T := by
    have : 0 < (univ.filter extra).card := by rw [hE]; exact s_pos p
    exact Fintype.card_pos_iff.mpr (by obtain ⟨t, _⟩ := card_pos.mp this; exact ⟨t⟩)
  have hC : (1 : ℝ) ≤ (p : ℝ) ^ 2 * Fintype.card T := by
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    have h2 : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
    nlinarith
  have hQ : (1 : ℝ) ≤ (q p : ℝ) + 1 := by have : (0 : ℝ) ≤ q p := Nat.cast_nonneg _; linarith
  have := decay_exp_of_geometric (turnW p bar extra) ((p : ℝ) ^ 2 * Fintype.card T)
    ((q p : ℝ) + 1) hC hQ
    (fun h => by
      have := squared_word_bound hp hbar hbarE hO hE h
      simpa [rho] using this) h (by exact_mod_cast hh)
  simpa using this

/-- **Lemma 7.8**, the paper's form: `δ = -¼ log ρ` is positive and
`∑_{W ∈ T^h} P(W)^2 ≤ e^{-2δh}` for all sufficiently large `h`. -/
theorem decay_paper {p : ℕ} (hp : 3 ≤ p) (hbar : Function.Involutive bar)
    (hbarE : ∀ t, extra t → ¬ extra (bar t))
    (hO : (univ.filter (fun u => ¬ extra u)).card = v p)
    (hE : (univ.filter extra).card = s p) :
    0 < -(1 / 4) * Real.log (rho p) ∧ ∃ h₀ : ℕ, ∀ h, h₀ ≤ h →
      ∑ W : Fin h → T, wordWeight (turnW p bar extra) h W ^ 2 ≤
        Real.exp (-2 * (-(1 / 4) * Real.log (rho p)) * h) := by
  have hρ0 := rho_pos p
  have hρ1 := rho_lt_one p
  have hL : Real.log (rho p) < 0 := Real.log_neg hρ0 hρ1
  refine ⟨by linarith, ?_⟩
  set L := -Real.log (rho p) with hLdef
  have hL0 : 0 < L := by linarith
  set C : ℝ := (p : ℝ) ^ 2 * Fintype.card T
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * C / L + 2)
  refine ⟨N, fun h hh => ?_⟩
  have hh' : (2 * C / L + 2 : ℝ) ≤ h := le_trans hN (by exact_mod_cast hh)
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by
    have : (2 : ℝ) ≤ h := by
      have : 0 ≤ 2 * C / L := by
        apply div_nonneg _ hL0.le
        have : (0 : ℝ) ≤ (p : ℝ) ^ 2 * Fintype.card T := by positivity
        linarith
      linarith
    have : 2 ≤ h := by exact_mod_cast this
    omega⟩
  push_cast at hh' ⊢
  have hb := squared_word_bound hp hbar hbarE hO hE k
  have hpow : rho p ^ k = Real.exp (k * Real.log (rho p)) := by
    rw [Real.exp_nat_mul, Real.exp_log hρ0]
  have hkey : C ≤ Real.exp ((k - 1) * L / 2) := by
    have h1 : C ≤ (k - 1) * L / 2 := by
      have : 2 * C / L ≤ k - 1 := by linarith
      rw [div_le_iff₀ hL0] at this
      linarith
    have h2 := Real.add_one_le_exp ((k - 1) * L / 2)
    linarith
  calc ∑ W : Fin (k + 1) → T, wordWeight (turnW p bar extra) (k + 1) W ^ 2
      ≤ C * rho p ^ k := hb
    _ = C * Real.exp (k * Real.log (rho p)) := by rw [hpow]
    _ ≤ Real.exp ((k - 1) * L / 2) * Real.exp (k * Real.log (rho p)) := by gcongr
    _ = Real.exp (-2 * (-(1 / 4) * Real.log (rho p)) * (k + 1)) := by
        rw [← Real.exp_add]; congr 1; rw [hLdef]; ring

end Split

end Kaplansky.OddDesign
