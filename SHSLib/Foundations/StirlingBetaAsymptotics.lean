/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stirling's approximation for the Beta function

Applying the Stirling bracket `½log(2π) < S(t) < ½log(2π) + 1/(12t)` for the
defect `S(t) = log Γ(t) − (t − ½)log t + t` (batches 155/156) to each of the
three Gamma factors in `B(x,y) = Γ(x)Γ(y)/Γ(x+y)` gives, for `x, y > 0`,

  `log B(x,y) = ½log(2π) + (x−½)log x + (y−½)log y − (x+y−½)log(x+y) + ε`,
  `−1/(12(x+y)) < ε < 1/(12x) + 1/(12y)`,

so in particular `|ε| ≤ 1/(12x) + 1/(12y)`. Note that the linear terms `−x`,
`−y`, `+(x+y)` cancel exactly, which is why the Beta function has no
exponential factor in its Stirling expansion.

The symmetric case reads `B(x,x) ≈ √(4π/x)·4^{−x}`, i.e.

  `|log B(x,x) − (½log(4π/x) − 2x log 2)| ≤ 1/(6x)`.
-/
import SHSLib.Foundations.StirlingBeta

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-- The Stirling main term for `log B(x,y)`. -/
noncomputable def betaStirlingMain (x y : ℝ) : ℝ :=
  1 / 2 * Real.log (2 * π) + (x - 1 / 2) * Real.log x + (y - 1 / 2) * Real.log y
    - (x + y - 1 / 2) * Real.log (x + y)

/-- `log B(x,y) = log Γ(x) + log Γ(y) − log Γ(x+y)` for positive arguments. -/
theorem log_betaFn_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (betaFn x y) = logGamma x + logGamma y - logGamma (x + y) := by
  have h1 := Real.Gamma_pos_of_pos hx
  have h2 := Real.Gamma_pos_of_pos hy
  have h3 := Real.Gamma_pos_of_pos (add_pos hx hy)
  unfold betaFn
  rw [Real.log_div (by positivity) h3.ne', Real.log_mul h1.ne' h2.ne', logGamma, logGamma,
    logGamma]

/-- The exact decomposition of `log B(x,y)` into its Stirling main term and the
combination `S(x) + S(y) − S(x+y)` of Stirling defects. -/
theorem log_betaFn_sub_main {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (betaFn x y) - betaStirlingMain x y
      = (stirlingDefect x - 1 / 2 * Real.log (2 * π))
        + (stirlingDefect y - 1 / 2 * Real.log (2 * π))
        - (stirlingDefect (x + y) - 1 / 2 * Real.log (2 * π)) := by
  rw [log_betaFn_eq hx hy, betaStirlingMain, stirlingDefect, stirlingDefect, stirlingDefect]
  ring

/-- **Stirling's approximation for the Beta function, two-sided**: for
`x, y > 0`,
`−1/(12(x+y)) < log B(x,y) − betaStirlingMain x y < 1/(12x) + 1/(12y)`. -/
theorem log_betaFn_bracket {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    -(1 / (12 * (x + y))) < Real.log (betaFn x y) - betaStirlingMain x y
      ∧ Real.log (betaFn x y) - betaStirlingMain x y < 1 / (12 * x) + 1 / (12 * y) := by
  have hxy : (0 : ℝ) < x + y := add_pos hx hy
  have h1 := stirlingConstant_lt_stirlingDefect hx
  have h2 := stirlingDefect_lt_stirlingConstant_add_binet hx
  have h3 := stirlingConstant_lt_stirlingDefect hy
  have h4 := stirlingDefect_lt_stirlingConstant_add_binet hy
  have h5 := stirlingConstant_lt_stirlingDefect hxy
  have h6 := stirlingDefect_lt_stirlingConstant_add_binet hxy
  rw [log_betaFn_sub_main hx hy]
  constructor <;> linarith

/-- **Stirling's approximation for the Beta function**: for `x, y > 0`,
`|log B(x,y) − betaStirlingMain x y| ≤ 1/(12x) + 1/(12y)`. -/
theorem log_betaFn_stirling_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log (betaFn x y) - betaStirlingMain x y| ≤ 1 / (12 * x) + 1 / (12 * y) := by
  obtain ⟨hlo, hup⟩ := log_betaFn_bracket hx hy
  have hxy : (0 : ℝ) < x + y := add_pos hx hy
  have hcmp : 1 / (12 * (x + y)) ≤ 1 / (12 * x) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hpos : (0 : ℝ) < 1 / (12 * y) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **The symmetric case**: `B(x,x) ≈ √(4π/x)·4^{−x}`, quantitatively
`|log B(x,x) − (½log(4π/x) − 2x log 2)| ≤ 1/(6x)`. -/
theorem log_betaFn_self_bound {x : ℝ} (hx : 0 < x) :
    |Real.log (betaFn x x) - (1 / 2 * Real.log (4 * π / x) - 2 * x * Real.log 2)|
      ≤ 1 / (6 * x) := by
  have hmain : betaStirlingMain x x
      = 1 / 2 * Real.log (4 * π / x) - 2 * x * Real.log 2 := by
    have hlog2x : Real.log (x + x) = Real.log 2 + Real.log x := by
      rw [show x + x = 2 * x by ring, Real.log_mul (by norm_num) hx.ne']
    have hlog2pi : Real.log (2 * π) = Real.log 2 + Real.log π :=
      Real.log_mul (by norm_num) Real.pi_pos.ne'
    have hlog4pi : Real.log (4 * π / x)
        = 2 * Real.log 2 + Real.log π - Real.log x := by
      rw [Real.log_div (by positivity) hx.ne', Real.log_mul (by norm_num) Real.pi_pos.ne',
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [betaStirlingMain, hlog2x, hlog2pi, hlog4pi]
    ring
  have h := log_betaFn_stirling_bound hx hx
  rw [hmain] at h
  have hsimp : 1 / (12 * x) + 1 / (12 * x) = 1 / (6 * x) := by
    field_simp
    ring
  rwa [hsimp] at h

end SHSLib.Trigamma
