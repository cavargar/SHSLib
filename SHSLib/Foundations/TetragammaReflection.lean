/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection at third order, and the cubic Mittag-Leffler expansion

Differentiating the trigamma reflection formula
`ψ'(x) + ψ'(1−x) = π²/sin(π x)²` of
`SHSLib/Foundations/DigammaReflection.lean` once more gives

  `ψ''(x) − ψ''(1−x) = −2π³ cos(π x)/sin(π x)³`  (`tetragamma_reflection`),

and substituting the tetragamma series `ψ''(x) = −2 ∑_{k ≥ 0} 1/(x+k)³` turns
this into the cubic Mittag-Leffler expansion

  `∑_{k ≥ 0} 1/(x+k)³ − ∑_{k ≥ 0} 1/(1−x+k)³ = π³ cos(π x)/sin(π x)³`
  (`tsum_inv_cube_reflection`),

valid for `x ∈ (0,1)`.  At the fixed point `x = 1/2` both sides vanish, which
is recorded as `tsum_inv_cube_half_cancel`.
-/
import SHSLib.Foundations.DigammaReflection

open Real Set Filter

namespace SHSLib.Trigamma

/-- **Reflection formula at third order**: for `x ∈ (0,1)`,
`ψ''(x) − ψ''(1−x) = −2π³ cos(π x)/sin(π x)³`. -/
theorem tetragamma_reflection {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    tetragamma x - tetragamma (1 - x)
      = -(2 * π ^ 3 * Real.cos (π * x) / Real.sin (π * x) ^ 3) := by
  obtain ⟨h0, h1⟩ := hx
  have hs : 0 < Real.sin (π * x) := sin_pi_mul_pos ⟨h0, h1⟩
  have hEq : (fun y : ℝ => trigamma y + trigamma (1 - y))
      =ᶠ[nhds x] fun y : ℝ => π ^ 2 * (Real.sin (π * y) ^ 2)⁻¹ := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo (0 : ℝ) 1 from ⟨h0, h1⟩)] with y hy
    rw [trigamma_reflection hy]
    field_simp
  have hA : HasDerivAt trigamma (tetragamma x) x :=
    (differentiableAt_trigamma h0).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => trigamma (1 - y)) (tetragamma (1 - x) * (-1)) x := by
    have h2 : HasDerivAt trigamma (tetragamma (1 - x)) (1 - x) :=
      (differentiableAt_trigamma (by linarith)).hasDerivAt
    exact h2.comp x ((hasDerivAt_id x).const_sub 1)
  have hAB : HasDerivAt (fun y : ℝ => trigamma y + trigamma (1 - y))
      (tetragamma x + tetragamma (1 - x) * (-1)) x := hA.add hB
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (π * y)) (Real.cos (π * x) * π) x := by
    simpa using (Real.hasDerivAt_sin (π * x)).comp x ((hasDerivAt_id x).const_mul π)
  have hsq : HasDerivAt (fun y : ℝ => Real.sin (π * y) ^ 2)
      (2 * Real.sin (π * x) ^ 1 * (Real.cos (π * x) * π)) x := hsin.pow 2
  have hne : Real.sin (π * x) ^ 2 ≠ 0 := by positivity
  have hinv := hsq.inv hne
  have hG : HasDerivAt (fun y : ℝ => π ^ 2 * (Real.sin (π * y) ^ 2)⁻¹)
      (-(2 * π ^ 3 * Real.cos (π * x) / Real.sin (π * x) ^ 3)) x := by
    have h := hinv.const_mul (π ^ 2)
    convert h using 1
    field_simp
  have hd := hEq.deriv_eq
  rw [hAB.deriv, hG.deriv] at hd
  linarith

/-- The cubic Mittag-Leffler expansion: for `x ∈ (0,1)`,
`∑_{k ≥ 0} 1/(x+k)³ − ∑_{k ≥ 0} 1/(1−x+k)³ = π³ cos(π x)/sin(π x)³`. -/
theorem tsum_inv_cube_reflection {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∑' k : ℕ, 1 / (x + k) ^ 3) - ∑' k : ℕ, 1 / ((1 - x) + k) ^ 3
      = π ^ 3 * Real.cos (π * x) / Real.sin (π * x) ^ 3 := by
  obtain ⟨h0, h1⟩ := hx
  have h := tetragamma_reflection (x := x) ⟨h0, h1⟩
  rw [tetragamma_eq_tsum h0, tetragamma_eq_tsum (by linarith : (0 : ℝ) < 1 - x)] at h
  have hs : 0 < Real.sin (π * x) := sin_pi_mul_pos ⟨h0, h1⟩
  have hne : Real.sin (π * x) ^ 3 ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

/-- At the fixed point of the reflection the two cubic series agree. -/
theorem tsum_inv_cube_half_cancel :
    (∑' k : ℕ, 1 / ((1 / 2 : ℝ) + k) ^ 3) - ∑' k : ℕ, 1 / ((1 - (1 / 2 : ℝ)) + k) ^ 3 = 0 := by
  have hx : (1 : ℝ) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h := tsum_inv_cube_reflection hx
  rw [h, show π * (1 / 2 : ℝ) = π / 2 by ring, Real.cos_pi_div_two]
  ring

end SHSLib.Trigamma
