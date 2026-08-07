/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection formulas for `ψ` and `ψ'`, and the quarter-integer values

`SHSLib/Foundations/Trigamma.lean` records the first derivative of Euler's
reflection formula, `ψ(x) − ψ(1−x) = −π cot(π x)` on `(0, 1)`.  This file
states it in terms of `digamma` (`digamma_reflection`) and differentiates it
once more:

  `ψ'(x) + ψ'(1−x) = π² / sin(π x)²`  (`trigamma_reflection`).

Combined with the trigamma series of `SHSLib/Foundations/TrigammaSeries.lean`
this is the Mittag-Leffler expansion of `π²/sin²`:

  `∑_{k ≥ 0} 1/(x+k)² + ∑_{k ≥ 0} 1/(1−x+k)² = π² / sin(π x)²`
  (`tsum_inv_sq_reflection`).

Together with Legendre duplication (`duplication_deriv`, used through
`digamma_half`) the reflection formula also pins down the digamma values at the
quarter integers:

  `ψ(1/4) = −γ − 3 log 2 − π/2`,  `ψ(3/4) = −γ − 3 log 2 + π/2`.
-/
import SHSLib.Foundations.DigammaEuler

open Real Set Filter

namespace SHSLib.Trigamma

/-! ### The reflection formula for `ψ` -/

/-- **Reflection formula for the digamma function**: for `x ∈ (0,1)`,
`ψ(1−x) − ψ(x) = π cot(π x)`. -/
theorem digamma_reflection {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    digamma (1 - x) - digamma x = π * Real.cos (π * x) / Real.sin (π * x) := by
  have h := reflection_deriv hx
  rw [digamma_def, digamma_def]
  linarith

/-! ### The reflection formula for `ψ'` -/

/-- **Reflection formula for the trigamma function**: for `x ∈ (0,1)`,
`ψ'(x) + ψ'(1−x) = π² / sin(π x)²`. -/
theorem trigamma_reflection {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    trigamma x + trigamma (1 - x) = π ^ 2 / Real.sin (π * x) ^ 2 := by
  obtain ⟨h0, h1⟩ := hx
  have hs : 0 < Real.sin (π * x) := sin_pi_mul_pos ⟨h0, h1⟩
  have hEq : (fun y : ℝ => deriv logGamma y - deriv logGamma (1 - y))
      =ᶠ[nhds x] fun y : ℝ => -(π * (Real.cos (π * y) / Real.sin (π * y))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo (0 : ℝ) 1 from ⟨h0, h1⟩)] with y hy
    rw [reflection_deriv hy]
    ring
  have hA : HasDerivAt (deriv logGamma) (trigamma x) x :=
    (differentiableAt_deriv_logGamma h0).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => deriv logGamma (1 - y)) (trigamma (1 - x) * (-1)) x := by
    have h2 : HasDerivAt (deriv logGamma) (trigamma (1 - x)) (1 - x) :=
      (differentiableAt_deriv_logGamma (by linarith)).hasDerivAt
    exact h2.comp x ((hasDerivAt_id x).const_sub 1)
  have hAB : HasDerivAt (fun y : ℝ => deriv logGamma y - deriv logGamma (1 - y))
      (trigamma x - trigamma (1 - x) * (-1)) x := hA.sub hB
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (π * y)) (Real.cos (π * x) * π) x := by
    simpa using (Real.hasDerivAt_sin (π * x)).comp x ((hasDerivAt_id x).const_mul π)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (π * y)) (-Real.sin (π * x) * π) x := by
    simpa using (Real.hasDerivAt_cos (π * x)).comp x ((hasDerivAt_id x).const_mul π)
  have hdiv := hcos.div hsin hs.ne'
  have hG : HasDerivAt (fun y : ℝ => -(π * (Real.cos (π * y) / Real.sin (π * y))))
      (π ^ 2 / Real.sin (π * x) ^ 2) x := by
    have h := (hdiv.const_mul π).neg
    convert h using 1
    have hpyth : Real.sin (π * x) ^ 2 + Real.cos (π * x) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq (π * x)
    field_simp
    nlinarith [hpyth]
  have hd := hEq.deriv_eq
  rw [hAB.deriv, hG.deriv] at hd
  linarith

/-- The Mittag-Leffler expansion of `π²/sin²` in the form given by the trigamma
series: for `x ∈ (0,1)`,
`∑_{k ≥ 0} 1/(x+k)² + ∑_{k ≥ 0} 1/(1−x+k)² = π²/sin(π x)²`. -/
theorem tsum_inv_sq_reflection {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∑' k : ℕ, 1 / (x + k) ^ 2) + ∑' k : ℕ, 1 / ((1 - x) + k) ^ 2
      = π ^ 2 / Real.sin (π * x) ^ 2 := by
  obtain ⟨h0, h1⟩ := hx
  have h := trigamma_reflection (x := x) ⟨h0, h1⟩
  rw [trigamma_eq_tsum h0, trigamma_eq_tsum (by linarith : (0 : ℝ) < 1 - x)] at h
  exact h

/-! ### The quarter-integer values -/

/-- `ψ(3/4) − ψ(1/4) = π`, the reflection formula at `x = 1/4`. -/
theorem digamma_three_quarters_sub_quarter :
    digamma (3 / 4) - digamma (1 / 4) = π := by
  have hx : (1 : ℝ) / 4 ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h := digamma_reflection hx
  have hval : π * (1 / 4 : ℝ) = π / 4 := by ring
  rw [hval, Real.cos_pi_div_four, Real.sin_pi_div_four] at h
  have h34 : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  rw [h34] at h
  rw [h]
  have h2 : Real.sqrt 2 ≠ 0 := by
    positivity
  field_simp

/-- `ψ(1/4) + ψ(3/4) = −2γ − 6 log 2`, Legendre duplication at `x = 1/4`. -/
theorem digamma_quarter_add_three_quarters :
    digamma (1 / 4) + digamma (3 / 4)
      = -2 * Real.eulerMascheroniConstant - 6 * Real.log 2 := by
  have h := duplication_deriv (x := 1 / 4) (by norm_num)
  have h1 : (1 : ℝ) / 4 + 1 / 2 = 3 / 4 := by norm_num
  have h2 : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  rw [h1, h2] at h
  have hhalf : deriv logGamma (1 / 2) = -Real.eulerMascheroniConstant - 2 * Real.log 2 := by
    rw [← digamma_def]; exact digamma_half
  rw [hhalf] at h
  rw [digamma_def, digamma_def]
  linarith

/-- `ψ(1/4) = −γ − 3 log 2 − π/2`. -/
theorem digamma_quarter :
    digamma (1 / 4) = -Real.eulerMascheroniConstant - 3 * Real.log 2 - π / 2 := by
  have h1 := digamma_three_quarters_sub_quarter
  have h2 := digamma_quarter_add_three_quarters
  linarith

/-- `ψ(3/4) = −γ − 3 log 2 + π/2`. -/
theorem digamma_three_quarters :
    digamma (3 / 4) = -Real.eulerMascheroniConstant - 3 * Real.log 2 + π / 2 := by
  have h1 := digamma_three_quarters_sub_quarter
  have h2 := digamma_quarter_add_three_quarters
  linarith

/-- The trigamma reflection formula at `x = 1/2` recovers `ψ'(1/2) = π²/2`. -/
theorem trigamma_half_of_reflection : trigamma (1 / 2) = π ^ 2 / 2 := by
  have hx : (1 : ℝ) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h := trigamma_reflection hx
  have hval : π * (1 / 2 : ℝ) = π / 2 := by ring
  rw [hval, Real.sin_pi_div_two] at h
  norm_num at h
  linarith

end SHSLib.Trigamma
