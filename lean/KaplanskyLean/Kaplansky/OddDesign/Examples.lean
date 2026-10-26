import Kaplansky.OddDesign.Balance

/-!
# Numerical checks for `p = 3` (paper, remarks after Lemmas 7.4, 7.5, Prop 7.6 and Lemma 7.8)

All by `decide`/`norm_num`; no `native_decide`.
-/

namespace Kaplansky.OddDesign

/-- `q = 3^5 = 243`. -/
example : q 3 = 243 := by norm_num [q]

/-- `v = 243^2 + 243 + 1 = 59293`. -/
example : v 3 = 59293 := by norm_num [v, q]

/-- `s = 13`. -/
example : s 3 = 13 := by norm_num [s]

/-- The key inequality at `p = 3`: `2 s p^2 (q+1) = 57096 < 59049 = q^2`; this is the value
`6344/6561` of `eq:keyineq`. -/
example : 2 * s 3 * 3 ^ 2 * (q 3 + 1) = 57096 ∧ q 3 ^ 2 = 59049 := by norm_num [s, q]

example : (2 * s 3 * 3 ^ 2 * (q 3 + 1) : ℚ) / (q 3 : ℚ) ^ 2 = 6344 / 6561 := by
  norm_num [s, q]

/-- `ρ = 487/488` for `p = 3`. -/
example : rho 3 = 487 / 488 := by norm_num [rho, q]

/-- For `p = 3` the uniform family has `244` vertices of each block type and `530465` vertices
with no extra letters in each line class. -/
example : q 3 + 1 = 244 ∧ 3 ^ 2 * v 3 - s 3 * (q 3 + 1) = 530465 := by norm_num [v, s, q]

/-- `u = 1`, `h = 2`, `κ = 3` and `1 - κ = -2` for `p = 3`. -/
example : uN 3 = 1 ∧ hN 3 = 2 ∧ kappa 3 = 3 := by norm_num [uN, hN, kappa]

/-- `h_q = 122` and the coefficient `1 - κ - h_q = -124` of `ξ_O` on `Y = 0` for `p = 3`. -/
example : hqN 3 = 122 ∧ (1 - kappa 3 - hqN 3 : ℤ) = -124 := by
  norm_num [hqN, q, kappa, uN]

/-- The centred representatives in `ZMod 3`. -/
example : (0 : ZMod 3).valMinAbs = 0 ∧ (1 : ZMod 3).valMinAbs = 1 ∧
    (2 : ZMod 3).valMinAbs = -1 := by decide

/-- Lemma 7.2 at `p = 3`: the cross-intersection sizes `1, 1+9 = 10 (≡ 1)`, `1 + 6 = 7 (≡ 1)`,
`q+1 = 244 (≡ 1)`, `244 + 9`, `244 + 6`, and `|S_r| = q+1+s = 257 ≡ 2 (mod 3)`. -/
example : (244 : ℕ) % 3 = 1 ∧ (244 + 9) % 3 = 1 ∧ (244 + 6) % 3 = 1 ∧ (1 + 6) % 3 = 1 ∧
    (q 3 + 1 + s 3) % 3 = 2 := by norm_num [q, s]

end Kaplansky.OddDesign
