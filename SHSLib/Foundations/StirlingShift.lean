/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The shifted Gamma ratio `Γ(x+a)/(Γ(x) x^a)`

The Stirling defect `S(y) = log Γ(y) − (y − ½) log y + y` is trapped between
`½log(2π)` and `½log(2π) + 1/(12y)` (batches 155/156), which turns the
elementary identity

  `log Γ(x+a) − log Γ(x) − a log x
     = (x + a − ½) log((x+a)/x) − a + S(x+a) − S(x)`

into an explicit `O(1/x)` bound: with the two-sided estimate
`a/(x+a) ≤ log((x+a)/x) ≤ a/x`,

  `−a/(2x) − 1/(12x) ≤ log Γ(x+a) − log Γ(x) − a log x ≤ a(a−½)/x + 1/(12x)`,

hence `|log Γ(x+a) − log Γ(x) − a log x| ≤ (a² + a + 1)/x` for `x ≥ ½` and
`a ≥ 0`, and in particular `log Γ(x+a) − log Γ(x) − a log x → 0`, the
quantitative form of `Γ(x+a) ∼ Γ(x) x^a`.
-/
import SHSLib.Foundations.StirlingBinet

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-- The exact decomposition of the shifted log-Gamma difference. -/
theorem logGamma_shift_eq (x a : ℝ) :
    logGamma (x + a) - logGamma x - a * Real.log x
      = (x + a - 1 / 2) * (Real.log (x + a) - Real.log x) - a
        + (stirlingDefect (x + a) - stirlingDefect x) := by
  rw [stirlingDefect, stirlingDefect]
  ring

/-- **The shifted Gamma ratio, quantitatively**: for `x ≥ ½` and `a ≥ 0`,
`|log Γ(x+a) − log Γ(x) − a log x| ≤ (a² + a + 1)/x`. -/
theorem logGamma_shift_bound {x a : ℝ} (hx : 1 / 2 ≤ x) (ha : 0 ≤ a) :
    |logGamma (x + a) - logGamma x - a * Real.log x| ≤ (a ^ 2 + a + 1) / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxa : (0 : ℝ) < x + a := by linarith
  have hcoef : (0 : ℝ) ≤ x + a - 1 / 2 := by linarith
  have hlogdiff : Real.log (x + a) - Real.log x = Real.log ((x + a) / x) := by
    rw [Real.log_div hxa.ne' hx0.ne']
  -- two-sided bound on the logarithm
  have hupper : Real.log (x + a) - Real.log x ≤ a / x := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (x + a) / x by positivity)
    have hsub : (x + a) / x - 1 = a / x := by
      field_simp
      ring
    rw [hlogdiff]
    linarith [hsub ▸ h]
  have hlower : a / (x + a) ≤ Real.log (x + a) - Real.log x := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < x / (x + a) by positivity)
    have hsub : x / (x + a) - 1 = -(a / (x + a)) := by
      field_simp
      ring
    have hlogsym : Real.log (x / (x + a)) = -Real.log ((x + a) / x) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hlogsym, hsub] at h
    rw [hlogdiff]
    linarith
  -- the main term
  have hA : (x + a - 1 / 2) * (Real.log (x + a) - Real.log x)
      ≤ (x + a - 1 / 2) * (a / x) := mul_le_mul_of_nonneg_left hupper hcoef
  have hAeq : (x + a - 1 / 2) * (a / x) = a + (a ^ 2 - a / 2) / x := by
    field_simp
    ring
  have hB : (x + a - 1 / 2) * (a / (x + a))
      ≤ (x + a - 1 / 2) * (Real.log (x + a) - Real.log x) :=
    mul_le_mul_of_nonneg_left hlower hcoef
  have hBeq : (x + a - 1 / 2) * (a / (x + a)) = a - a / (2 * (x + a)) := by
    field_simp
  -- the Stirling defect difference
  have hS1 := stirlingConstant_lt_stirlingDefect hx0
  have hS2 := stirlingDefect_lt_stirlingConstant_add_binet hx0
  have hS3 := stirlingConstant_lt_stirlingDefect hxa
  have hS4 := stirlingDefect_lt_stirlingConstant_add_binet hxa
  have h12 : 1 / (12 * (x + a)) ≤ 1 / (12 * x) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmono : a / (2 * (x + a)) ≤ a / (2 * x) :=
    div_le_div_of_nonneg_left ha (by positivity) (by linarith)
  -- assemble
  rw [logGamma_shift_eq x a, abs_le]
  have hup : (a ^ 2 - a / 2) / x + 1 / (12 * x) ≤ (a ^ 2 + a + 1) / x := by
    have hcollect : (a ^ 2 - a / 2) / x + 1 / (12 * x)
        = (a ^ 2 - a / 2 + 1 / 12) / x := by
      field_simp
    rw [hcollect]
    exact div_le_div_of_nonneg_right (by linarith) hx0.le
  have hlo : a / (2 * x) + 1 / (12 * x) ≤ (a ^ 2 + a + 1) / x := by
    have hcollect : a / (2 * x) + 1 / (12 * x) = (a / 2 + 1 / 12) / x := by
      field_simp
    rw [hcollect]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg a]) hx0.le
  constructor
  · linarith
  · linarith

/-- **`log Γ(x+a) − log Γ(x) − a log x → 0`** as `x → ∞`, for every fixed
`a ≥ 0`: the quantitative statement `Γ(x+a) ∼ Γ(x)·x^a`. -/
theorem tendsto_logGamma_shift (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun x : ℝ => logGamma (x + a) - logGamma x - a * Real.log x) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hbound : Tendsto (fun x : ℝ => (a ^ 2 + a + 1) / x) atTop (𝓝 0) := by
    have h := hinv.const_mul (a ^ 2 + a + 1)
    simp only [mul_zero] at h
    exact h.congr (fun x => by rw [div_eq_mul_inv])
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with x hx
  simpa [Real.norm_eq_abs] using logGamma_shift_bound hx ha

end SHSLib.Trigamma
