/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Beta function and its asymptotics `B(x,y) ∼ Γ(y)·x^{−y}`

Mathlib carries the Beta *integral* only in its complex form, so we introduce
the real Beta function directly through the Gamma quotient,

  `B(x,y) = Γ(x)Γ(y)/Γ(x+y)`,

record its symmetry, positivity, the values `B(x,1) = 1/x`, and the
recurrence `B(x, y+1) = B(x,y)·y/(x+y)`.

The point of the batch is the asymptotic behaviour in the first argument. The
identity

  `B(x,y)·x^y/Γ(y) = (Γ(x+y)/(Γ(x)·x^y))⁻¹`

turns the shifted-ratio bracket of batch 166 into

  `exp(−(y²+y+1)/x) ≤ B(x,y)·x^y/Γ(y) ≤ exp((y²+y+1)/x)`   (`x ≥ ½`, `y ≥ 0`)

and hence `B(x,y)·x^y/Γ(y) → 1` as `x → ∞`: the classical
`B(x,y) ∼ Γ(y)·x^{−y}`, here with an explicit `O(1/x)` error.
-/
import SHSLib.Foundations.StirlingShiftRatio

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-- The real Beta function `B(x,y) = Γ(x)Γ(y)/Γ(x+y)`. -/
noncomputable def betaFn (x y : ℝ) : ℝ := Real.Gamma x * Real.Gamma y / Real.Gamma (x + y)

/-- `B` is symmetric. -/
theorem betaFn_symm (x y : ℝ) : betaFn x y = betaFn y x := by
  unfold betaFn
  rw [add_comm x y, mul_comm (Real.Gamma x)]

/-- `B(x,y) > 0` for positive arguments. -/
theorem betaFn_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < betaFn x y := by
  have h1 := Real.Gamma_pos_of_pos hx
  have h2 := Real.Gamma_pos_of_pos hy
  have h3 := Real.Gamma_pos_of_pos (add_pos hx hy)
  unfold betaFn
  positivity

/-- `B(x,1) = 1/x`. -/
theorem betaFn_one_right {x : ℝ} (hx : 0 < x) : betaFn x 1 = 1 / x := by
  have hG : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx.ne'
  have hx0 : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  unfold betaFn
  rw [hG, Real.Gamma_one, mul_one]
  field_simp

/-- The recurrence `B(x, y+1) = B(x,y) · y/(x+y)`. -/
theorem betaFn_add_one_right {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    betaFn x (y + 1) = betaFn x y * (y / (x + y)) := by
  have hGy : Real.Gamma (y + 1) = y * Real.Gamma y := Real.Gamma_add_one hy.ne'
  have hGxy : Real.Gamma (x + y + 1) = (x + y) * Real.Gamma (x + y) :=
    Real.Gamma_add_one (add_pos hx hy).ne'
  have hne : Real.Gamma (x + y) ≠ 0 := (Real.Gamma_pos_of_pos (add_pos hx hy)).ne'
  have hxy : x + y ≠ 0 := (add_pos hx hy).ne'
  have hassoc : x + (y + 1) = x + y + 1 := by ring
  unfold betaFn
  rw [hassoc, hGy, hGxy]
  field_simp

/-- The normalised Beta function is exactly the reciprocal of the shifted
Gamma ratio of batch 166. -/
theorem betaFn_normalised_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    betaFn x y * x ^ y / Real.Gamma y
      = (Real.Gamma (x + y) / (Real.Gamma x * x ^ y))⁻¹ := by
  have hGx := Real.Gamma_pos_of_pos hx
  have hGy := Real.Gamma_pos_of_pos hy
  have hGxy := Real.Gamma_pos_of_pos (add_pos hx hy)
  have hp : (0 : ℝ) < x ^ y := Real.rpow_pos_of_pos hx y
  unfold betaFn
  rw [inv_div]
  field_simp

/-- **The Beta function, quantitatively**: for `x ≥ ½` and `y > 0`,
`exp(−(y²+y+1)/x) ≤ B(x,y)·x^y/Γ(y) ≤ exp((y²+y+1)/x)`. -/
theorem betaFn_bracket {x y : ℝ} (hx : 1 / 2 ≤ x) (hy : 0 < y) :
    Real.exp (-((y ^ 2 + y + 1) / x)) ≤ betaFn x y * x ^ y / Real.Gamma y
      ∧ betaFn x y * x ^ y / Real.Gamma y ≤ Real.exp ((y ^ 2 + y + 1) / x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxy : (0 : ℝ) < x + y := by linarith
  have hpos := gamma_shift_ratio_pos hx0 hxy
  obtain ⟨h1, h2⟩ := gamma_shift_ratio_bracket hx hy.le
  rw [betaFn_normalised_eq hx0 hy]
  constructor
  · rw [Real.exp_neg]
    exact inv_anti₀ hpos h2
  · have := inv_anti₀ (Real.exp_pos _) h1
    rwa [Real.exp_neg, inv_inv] at this

/-- **`B(x,y) ∼ Γ(y)·x^{−y}`**: for every fixed `y > 0`,
`B(x,y)·x^y/Γ(y) → 1` as `x → ∞`. -/
theorem tendsto_betaFn_normalised {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ => betaFn x y * x ^ y / Real.Gamma y) atTop (𝓝 1) := by
  have hR := tendsto_gamma_shift_ratio y hy.le
  have hinv : Tendsto (fun x : ℝ => (Real.Gamma (x + y) / (Real.Gamma x * x ^ y))⁻¹)
      atTop (𝓝 1) := by
    simpa using hR.inv₀ (by norm_num)
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (betaFn_normalised_eq hx hy).symm

end SHSLib.Trigamma
