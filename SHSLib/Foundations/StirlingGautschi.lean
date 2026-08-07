/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gautschi's inequality for the Gamma ratio

For `x > 0` and `s ∈ (0,1)`,

  `x^{1−s} ≤ Γ(x+1)/Γ(x+s) ≤ (x+s)^{1−s}`.

Both directions are one application of the logarithmic convexity of `Γ`
(Mathlib's `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`) combined with
the functional equation `Γ(y+1) = yΓ(y)`:

* at the points `x` and `x+1` with weights `1−s` and `s`, the interpolation
  point is `x+s`, giving `Γ(x+s) ≤ Γ(x)^{1−s} Γ(x+1)^{s} = Γ(x+1) x^{s−1}`;
* at the points `x+s` and `x+1+s` with weights `s` and `1−s`, the
  interpolation point is `x+1`, giving
  `Γ(x+1) ≤ Γ(x+s)^{s} Γ(x+1+s)^{1−s} = Γ(x+s)(x+s)^{1−s}`.

The special case `s = ½` bounds `Γ(x+1)/Γ(x+½)` between `√x` and `√(x+½)`,
complementing the sharp bracket for integer arguments proved in
`SHSLib/Foundations/StirlingHalfInteger.lean`.
-/
import SHSLib.Foundations.StirlingHalfInteger

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-- **Gautschi's inequality**: `x^{1−s} ≤ Γ(x+1)/Γ(x+s) ≤ (x+s)^{1−s}` for
`x > 0` and `0 < s < 1`. -/
theorem gautschi_bracket {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    x ^ (1 - s) ≤ Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) ≤ (x + s) ^ (1 - s) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hxs : (0 : ℝ) < x + s := by linarith
  have hxs1 : (0 : ℝ) < x + 1 + s := by linarith
  have hG : (0 : ℝ) < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hG1 : (0 : ℝ) < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos hx1
  have hGs : (0 : ℝ) < Real.Gamma (x + s) := Real.Gamma_pos_of_pos hxs
  have hGs1 : (0 : ℝ) < Real.Gamma (x + 1 + s) := Real.Gamma_pos_of_pos hxs1
  have hrec : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx.ne'
  have hrecs : Real.Gamma (x + s + 1) = (x + s) * Real.Gamma (x + s) :=
    Real.Gamma_add_one hxs.ne'
  constructor
  · -- convexity at `x` and `x+1`, weights `1−s` and `s`
    have hconv := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
      hx hx1 (by linarith : (0:ℝ) < 1 - s) hs0 (by ring)
    have hpt : (1 - s) * x + s * (x + 1) = x + s := by ring
    rw [hpt] at hconv
    have hGx : Real.Gamma x = Real.Gamma (x + 1) / x := by
      rw [hrec]; field_simp
    rw [hGx, Real.div_rpow hG1.le hx.le] at hconv
    have hcomb : Real.Gamma (x + 1) ^ (1 - s) * Real.Gamma (x + 1) ^ s
        = Real.Gamma (x + 1) := by
      rw [← Real.rpow_add hG1]
      simp
    have hconv' : Real.Gamma (x + s) ≤ Real.Gamma (x + 1) / x ^ (1 - s) := by
      calc Real.Gamma (x + s)
          ≤ Real.Gamma (x + 1) ^ (1 - s) / x ^ (1 - s) * Real.Gamma (x + 1) ^ s := hconv
        _ = (Real.Gamma (x + 1) ^ (1 - s) * Real.Gamma (x + 1) ^ s) / x ^ (1 - s) := by ring
        _ = Real.Gamma (x + 1) / x ^ (1 - s) := by rw [hcomb]
    have hxpow : (0 : ℝ) < x ^ (1 - s) := Real.rpow_pos_of_pos hx _
    rw [le_div_iff₀ hGs]
    rw [le_div_iff₀ hxpow] at hconv'
    linarith
  · -- convexity at `x+s` and `x+1+s`, weights `s` and `1−s`
    have hconv := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
      hxs hxs1 hs0 (by linarith : (0:ℝ) < 1 - s) (by ring)
    have hpt : s * (x + s) + (1 - s) * (x + 1 + s) = x + 1 := by ring
    rw [hpt] at hconv
    have hGs1' : Real.Gamma (x + 1 + s) = (x + s) * Real.Gamma (x + s) := by
      rw [show x + 1 + s = x + s + 1 by ring, hrecs]
    rw [hGs1', Real.mul_rpow hxs.le hGs.le] at hconv
    have hcomb : Real.Gamma (x + s) ^ s * Real.Gamma (x + s) ^ (1 - s)
        = Real.Gamma (x + s) := by
      rw [← Real.rpow_add hGs]
      simp
    have hconv' : Real.Gamma (x + 1) ≤ (x + s) ^ (1 - s) * Real.Gamma (x + s) := by
      calc Real.Gamma (x + 1)
          ≤ Real.Gamma (x + s) ^ s * ((x + s) ^ (1 - s) * Real.Gamma (x + s) ^ (1 - s)) := hconv
        _ = (x + s) ^ (1 - s) * (Real.Gamma (x + s) ^ s * Real.Gamma (x + s) ^ (1 - s)) := by
              ring
        _ = (x + s) ^ (1 - s) * Real.Gamma (x + s) := by rw [hcomb]
    rw [div_le_iff₀ hGs]
    linarith

/-- **Gautschi at `s = ½`**: `√x ≤ Γ(x+1)/Γ(x+½) ≤ √(x+½)` for `x > 0`. -/
theorem gamma_ratio_half_sqrt_bracket {x : ℝ} (hx : 0 < x) :
    Real.sqrt x ≤ Real.Gamma (x + 1) / Real.Gamma (x + 1 / 2) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + 1 / 2) ≤ Real.sqrt (x + 1 / 2) := by
  obtain ⟨h1, h2⟩ := gautschi_bracket hx (by norm_num : (0:ℝ) < 1 / 2)
    (by norm_num : (1:ℝ) / 2 < 1)
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf] at h1 h2
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact ⟨h1, h2⟩

end SHSLib.Trigamma
