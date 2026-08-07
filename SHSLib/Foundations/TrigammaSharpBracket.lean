/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sharp trigamma bracket `1/x + 1/(2x²) < ψ'(x) < 1/x + 1/x²`

Batch 152 bracketed the trigamma function between `1/x` and `1/(x−1)`, which is
sharp only to first order.  The classical two-sided estimate

  `1/x + 1/(2x²) < ψ'(x) < 1/x + 1/x²`

is proved here by the telescoping criterion `pos_of_step_of_tendsto_atTop` of
batch 151: for each of the two defects the unit-step decrement is an explicit
positive rational function,

  `(1/x + 1/x² − ψ'(x)) − (same at x+1) = 1/(x(x+1)²)`,
  `(ψ'(x) − 1/x − 1/(2x²)) − (same at x+1) = 1/(2x²(x+1)²)`,

using the trigamma recurrence `ψ'(x+1) = ψ'(x) − 1/x²`, and both defects tend
to `0` at infinity because `ψ'` does.
-/
import SHSLib.Foundations.DigammaSharpBound
import SHSLib.Foundations.PolygammaAsymptotics

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The two limits -/

private theorem tendsto_one_div_atTop' : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
  simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))

private theorem tendsto_one_div_sq_atTop : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (𝓝 0) := by
  have h := tendsto_one_div_atTop'.mul tendsto_one_div_atTop'
  simpa [div_mul_div_comm, sq] using h

/-! ### The upper bound -/

/-- The unit-step decrement of `1/x + 1/x² − ψ'(x)`. -/
theorem trigamma_upper_step {x : ℝ} (hx : 0 < x) :
    (1 / (x + 1) + 1 / (x + 1) ^ 2 - trigamma (x + 1))
      < 1 / x + 1 / x ^ 2 - trigamma x := by
  have hrec : trigamma (x + 1) = trigamma x - 1 / x ^ 2 := trigamma_step hx
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hid : (1 / x + 1 / x ^ 2) - (1 / (x + 1) + 1 / (x + 1) ^ 2) - 1 / x ^ 2
      = 1 / (x * (x + 1) ^ 2) := by
    field_simp
    ring
  have hpos : 0 < 1 / (x * (x + 1) ^ 2) := by positivity
  rw [hrec]
  linarith [hid, hpos]

/-- **`ψ'(x) < 1/x + 1/x²`** for every `x > 0`. -/
theorem trigamma_lt_inv_add_inv_sq {x : ℝ} (hx : 0 < x) :
    trigamma x < 1 / x + 1 / x ^ 2 := by
  set f : ℝ → ℝ := fun y => 1 / y + 1 / y ^ 2 - trigamma y with hf_def
  have hstep : ∀ y : ℝ, 0 < y → f (y + 1) < f y := fun y hy => trigamma_upper_step hy
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop'.add tendsto_one_div_sq_atTop).sub tendsto_trigamma_atTop
    simpa [hf_def] using h
  have hpos := pos_of_step_of_tendsto_atTop hstep hlim hx
  simp only [hf_def] at hpos
  linarith

/-! ### The lower bound -/

/-- The unit-step decrement of `ψ'(x) − 1/x − 1/(2x²)`. -/
theorem trigamma_lower_step {x : ℝ} (hx : 0 < x) :
    (trigamma (x + 1) - 1 / (x + 1) - 1 / (2 * (x + 1) ^ 2))
      < trigamma x - 1 / x - 1 / (2 * x ^ 2) := by
  have hrec : trigamma (x + 1) = trigamma x - 1 / x ^ 2 := trigamma_step hx
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hid : (1 / (x + 1) + 1 / (2 * (x + 1) ^ 2)) - (1 / x + 1 / (2 * x ^ 2)) + 1 / x ^ 2
      = 1 / (2 * x ^ 2 * (x + 1) ^ 2) := by
    field_simp
    ring
  have hpos : 0 < 1 / (2 * x ^ 2 * (x + 1) ^ 2) := by positivity
  rw [hrec]
  linarith [hid, hpos]

/-- **`1/x + 1/(2x²) < ψ'(x)`** for every `x > 0`. -/
theorem inv_add_half_inv_sq_lt_trigamma {x : ℝ} (hx : 0 < x) :
    1 / x + 1 / (2 * x ^ 2) < trigamma x := by
  set f : ℝ → ℝ := fun y => trigamma y - 1 / y - 1 / (2 * y ^ 2) with hf_def
  have hstep : ∀ y : ℝ, 0 < y → f (y + 1) < f y := fun y hy => trigamma_lower_step hy
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hhalf : Tendsto (fun y : ℝ => 1 / (2 * y ^ 2)) atTop (𝓝 0) := by
      have h := tendsto_one_div_sq_atTop.const_mul (1 / 2 : ℝ)
      simp only [mul_zero] at h
      exact h.congr (fun y => by rw [one_div, one_div, one_div, mul_inv])
    have h := (tendsto_trigamma_atTop.sub tendsto_one_div_atTop').sub hhalf
    simpa [hf_def] using h
  have hpos := pos_of_step_of_tendsto_atTop hstep hlim hx
  simp only [hf_def] at hpos
  linarith

/-- The sharp bracket, in one statement. -/
theorem trigamma_bracket {x : ℝ} (hx : 0 < x) :
    1 / x + 1 / (2 * x ^ 2) < trigamma x ∧ trigamma x < 1 / x + 1 / x ^ 2 :=
  ⟨inv_add_half_inv_sq_lt_trigamma hx, trigamma_lt_inv_add_inv_sq hx⟩

end SHSLib.Trigamma
