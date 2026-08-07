/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Beta laws with a unit parameter, and extremes of a uniform sample

Two families of Beta laws have elementary distribution functions:

  `I_x(a,1) = x^a`  and  `I_x(1,b) = 1 − (1−x)^b`,

with quantile functions `p ↦ p^{1/a}` and `p ↦ 1 − (1−p)^{1/b}`.  This module
proves both, starting from the definition of the incomplete Beta function as an
integral, and then applies them to the order-statistic theory of batches
187–190:

* the maximum of `n` independent uniforms on `[0,1]` has distribution function
  `x^n` — it is `Beta(n,1)`;
* the minimum has distribution function `1 − (1−x)^n` — it is `Beta(1,n)`;
* an order statistic of a sample from a `Beta(1,b)` law has distribution
  function `I_{1−(1−x)^b}(j+1, m+1)`.
-/
import SHSLib.Foundations.OrderStatisticTransform

open MeasureTheory Set

namespace SHSLib.Trigamma

/-! ### The distribution function of `Beta(a,1)` and `Beta(1,b)` -/

/-- `B(x; a, 1) = x^a / a`. -/
theorem incompleteBetaFn_one_right {a : ℝ} (ha : 0 < a) (x : ℝ) :
    incompleteBetaFn a 1 x = x ^ a / a := by
  have hcongr : incompleteBetaFn a 1 x = ∫ t in (0:ℝ)..x, t ^ (a - 1) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp [betaIntegrand]
  rw [hcongr, integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
  ring_nf

/-- **The `Beta(a,1)` distribution function is the power `x^a`.** -/
theorem regBetaFn_one_right {a : ℝ} (ha : 0 < a) (x : ℝ) :
    regBetaFn a 1 x = x ^ a := by
  rw [regBetaFn, incompleteBetaFn_one_right ha, betaFn_one_right ha]
  field_simp

/-- **The `Beta(1,b)` distribution function is `1 − (1−x)^b`.** -/
theorem regBetaFn_one_left {b : ℝ} (hb : 0 < b) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regBetaFn 1 b x = 1 - (1 - x) ^ b := by
  rw [regBetaFn_symm one_pos hb hx0 hx1, regBetaFn_one_right hb]

/-! ### The corresponding quantile functions -/

/-- The `Beta(a,1)` quantile function is `p ↦ p^{1/a}`. -/
theorem betaQuantile_one_right {a : ℝ} (ha : 0 < a) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    betaQuantile a 1 p = p ^ (1 / a) := by
  have hx0 : 0 ≤ p ^ (1 / a) := Real.rpow_nonneg hp0 _
  have hx1 : p ^ (1 / a) ≤ 1 := Real.rpow_le_one hp0 hp1 (by positivity)
  have hval : regBetaFn a 1 (p ^ (1 / a)) = p := by
    rw [regBetaFn_one_right ha, ← Real.rpow_mul hp0, one_div, inv_mul_cancel₀ ha.ne',
      Real.rpow_one]
  have := betaQuantile_regBetaFn ha one_pos hx0 hx1
  rwa [hval] at this

/-- The `Beta(1,b)` quantile function is `p ↦ 1 − (1−p)^{1/b}`. -/
theorem betaQuantile_one_left {b : ℝ} (hb : 0 < b) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    betaQuantile 1 b p = 1 - (1 - p) ^ (1 / b) := by
  have h1p0 : 0 ≤ 1 - p := by linarith
  have hx0 : 0 ≤ (1 - p) ^ (1 / b) := Real.rpow_nonneg h1p0 _
  have hx1 : (1 - p) ^ (1 / b) ≤ 1 := Real.rpow_le_one h1p0 (by linarith) (by positivity)
  have hval : regBetaFn 1 b (1 - (1 - p) ^ (1 / b)) = p := by
    rw [regBetaFn_one_left hb (by linarith) (by linarith)]
    have : (1:ℝ) - (1 - (1 - p) ^ (1 / b)) = (1 - p) ^ (1 / b) := by ring
    rw [this, ← Real.rpow_mul h1p0, one_div, inv_mul_cancel₀ hb.ne', Real.rpow_one]
    ring
  have := betaQuantile_regBetaFn (a := 1) (b := b) (x := 1 - (1 - p) ^ (1 / b))
    one_pos hb (by linarith) (by linarith)
  rwa [hval] at this

/-! ### Extremes of a uniform sample -/

/-- The distribution function of the `(j+1)`-st order statistic of `n`
independent uniforms, in a form free of the decomposition `n = j+m+1`. -/
theorem measure_orderStat_le' {n j : ℕ} (hj : j < n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    unifPi n {w : Fin n → ℝ | orderStat n w ⟨j, hj⟩ ≤ x}
      = ENNReal.ofReal (regBetaFn ((j : ℝ) + 1) ((n : ℝ) - (j : ℝ)) x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + m + 1 := ⟨n - j - 1, by omega⟩
  have h := measure_orderStat_le j m hx0 hx1 (⟨j, hj⟩ : Fin (j + m + 1)) rfl
  rw [h]
  congr 2
  push_cast
  ring

/-- **The maximum of `n+1` independent uniforms on `[0,1]`** has distribution
function `x^{n+1}`. -/
theorem measure_max_unif (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    unifPi (n + 1) {w : Fin (n + 1) → ℝ | orderStat (n + 1) w (Fin.last n) ≤ x}
      = ENNReal.ofReal (x ^ ((n : ℝ) + 1)) := by
  have h := measure_orderStat_le' (n := n + 1) (j := n) (by omega) hx0 hx1
  have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hlast] at h
  rw [h, show ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 by push_cast; ring,
    regBetaFn_one_right (by positivity)]

/-- **The minimum of `m+1` independent uniforms on `[0,1]`** has distribution
function `1 − (1−x)^{m+1}`. -/
theorem measure_min_unif (m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    unifPi (m + 1) {w : Fin (m + 1) → ℝ | orderStat (m + 1) w ⟨0, by omega⟩ ≤ x}
      = ENNReal.ofReal (1 - (1 - x) ^ ((m : ℝ) + 1)) := by
  have h := measure_orderStat_le' (n := m + 1) (j := 0) (by omega) hx0 hx1
  rw [h, Nat.cast_zero, zero_add, sub_zero,
    show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring,
    regBetaFn_one_left (by positivity) hx0 hx1]

/-- **An order statistic of a `Beta(1,b)` sample.**  Its distribution function
is `I_{1−(1−x)^b}(j+1, m+1)`. -/
theorem measure_orderStat_betaOneSample_le {b : ℝ} (hb : 0 < b) (j m : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 b))
        {w : Fin (j + m + 1) → ℝ | orderStat (j + m + 1) w ⟨j, by omega⟩ ≤ x}
      = ENNReal.ofReal
          (regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1) (1 - (1 - x) ^ b)) := by
  rw [measure_orderStat_betaSample_le one_pos hb j m hx0 hx1,
    regBetaFn_one_left hb hx0 hx1]

end SHSLib.Trigamma
