/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Γ(x+a)/(Γ(x)·x^a)` in multiplicative form

Batch 165 bounded the *logarithm* of the shifted Gamma ratio:
`|log Γ(x+a) − log Γ(x) − a log x| ≤ (a²+a+1)/x` for `x ≥ ½`, `a ≥ 0`.
Exponentiating turns this into a two-sided multiplicative bracket

  `exp(−(a²+a+1)/x) ≤ Γ(x+a)/(Γ(x)·x^a) ≤ exp((a²+a+1)/x)`,

together with the limit `Γ(x+a)/(Γ(x)·x^a) → 1`, i.e. the classical
`Γ(x+a) ∼ Γ(x)·x^a`.
-/
import SHSLib.Foundations.StirlingShift

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-- The logarithm of the shifted Gamma ratio is exactly the quantity bounded in
batch 165. -/
theorem log_gamma_shift_ratio {x a : ℝ} (hx : 0 < x) (hxa : 0 < x + a) :
    Real.log (Real.Gamma (x + a) / (Real.Gamma x * x ^ a))
      = logGamma (x + a) - logGamma x - a * Real.log x := by
  have hG1 : (0 : ℝ) < Real.Gamma (x + a) := Real.Gamma_pos_of_pos hxa
  have hG2 : (0 : ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hp : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx a
  rw [Real.log_div hG1.ne' (by positivity), Real.log_mul hG2.ne' hp.ne',
    Real.log_rpow hx, logGamma, logGamma]
  ring

/-- The shifted Gamma ratio is positive. -/
theorem gamma_shift_ratio_pos {x a : ℝ} (hx : 0 < x) (hxa : 0 < x + a) :
    0 < Real.Gamma (x + a) / (Real.Gamma x * x ^ a) := by
  have hG1 : (0 : ℝ) < Real.Gamma (x + a) := Real.Gamma_pos_of_pos hxa
  have hG2 : (0 : ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hp : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx a
  positivity

/-- **The shifted Gamma ratio, multiplicative bracket**: for `x ≥ ½` and
`a ≥ 0`,
`exp(−(a²+a+1)/x) ≤ Γ(x+a)/(Γ(x)·x^a) ≤ exp((a²+a+1)/x)`. -/
theorem gamma_shift_ratio_bracket {x a : ℝ} (hx : 1 / 2 ≤ x) (ha : 0 ≤ a) :
    Real.exp (-((a ^ 2 + a + 1) / x)) ≤ Real.Gamma (x + a) / (Real.Gamma x * x ^ a)
      ∧ Real.Gamma (x + a) / (Real.Gamma x * x ^ a) ≤ Real.exp ((a ^ 2 + a + 1) / x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxa : (0 : ℝ) < x + a := by linarith
  have hpos := gamma_shift_ratio_pos hx0 hxa
  have hlog := log_gamma_shift_ratio hx0 hxa
  have hb := logGamma_shift_bound hx ha
  rw [← hlog, abs_le] at hb
  constructor
  · calc Real.exp (-((a ^ 2 + a + 1) / x))
        ≤ Real.exp (Real.log (Real.Gamma (x + a) / (Real.Gamma x * x ^ a))) :=
          Real.exp_le_exp.mpr hb.1
      _ = _ := Real.exp_log hpos
  · calc Real.Gamma (x + a) / (Real.Gamma x * x ^ a)
        = Real.exp (Real.log (Real.Gamma (x + a) / (Real.Gamma x * x ^ a))) :=
          (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hb.2

/-- **`Γ(x+a)/(Γ(x)·x^a) → 1`** as `x → ∞`, for every fixed `a ≥ 0`: the
classical asymptotic `Γ(x+a) ∼ Γ(x)·x^a`. -/
theorem tendsto_gamma_shift_ratio (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun x : ℝ => Real.Gamma (x + a) / (Real.Gamma x * x ^ a)) atTop (𝓝 1) := by
  have hL := tendsto_logGamma_shift a ha
  have hexp : Tendsto (fun x : ℝ =>
      Real.exp (logGamma (x + a) - logGamma x - a * Real.log x)) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp hL
    simpa using this
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-a)] with x hx hxa
  have hxa' : (0 : ℝ) < x + a := by linarith
  rw [← log_gamma_shift_ratio hx hxa', Real.exp_log (gamma_shift_ratio_pos hx hxa')]

end SHSLib.Trigamma
