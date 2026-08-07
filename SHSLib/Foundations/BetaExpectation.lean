/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expectations under the Beta law

Batch 171 computed the moments of the Beta distribution as interval integrals
against the density `betaPDF`; batch 177 packaged the law as a measure
`betaMeasure`.  This module connects the two: for every `g : ℝ → ℝ`,

  `∫ t, g t ∂(betaMeasure a b) = ∫ t in 0..1, g t · betaPDF a b t`,

so the moment formulas of batch 171 become genuine expectations.  The mean,
the second moment, the general integer moment and the variance are restated in
that form.
-/
import SHSLib.Foundations.BetaMeasure

open Real Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SHSLib.Trigamma

theorem betaDensity_lt_top (a b : ℝ) (t : ℝ) : betaDensity a b t < ⊤ := by
  unfold betaDensity
  by_cases ht : t ∈ Set.Ioo (0:ℝ) 1
  · rw [Set.indicator_of_mem ht]
    exact ENNReal.ofReal_lt_top
  · rw [Set.indicator_of_notMem ht]
    exact ENNReal.zero_lt_top

/-- The real-valued form of the Beta density: the truncation of `betaPDF` to
`(0,1)`. -/
theorem betaDensity_toReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    (betaDensity a b t).toReal = Set.indicator (Set.Ioo (0:ℝ) 1) (betaPDF a b) t := by
  unfold betaDensity
  by_cases ht : t ∈ Set.Ioo (0:ℝ) 1
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
      ENNReal.toReal_ofReal (betaPDF_nonneg ha hb ht.1.le ht.2.le)]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, ENNReal.toReal_zero]

/-- **Expectation under the Beta law** is the interval integral against the
Beta density. -/
theorem integral_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (g : ℝ → ℝ) :
    ∫ t, g t ∂(betaMeasure a b) = ∫ t in (0:ℝ)..1, g t * betaPDF a b t := by
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_betaDensity a b)
    (Filter.Eventually.of_forall (fun t => betaDensity_lt_top a b t))]
  have hfun : (fun t => (betaDensity a b t).toReal • g t)
      = Set.indicator (Set.Ioo (0:ℝ) 1) (fun t => g t * betaPDF a b t) := by
    funext t
    rw [smul_eq_mul, betaDensity_toReal ha hb t]
    by_cases ht : t ∈ Set.Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_comm]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioo,
    intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The Beta law is normalised: the expectation of the constant `1` is `1`. -/
theorem integral_one_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ _t, (1:ℝ) ∂(betaMeasure a b) = 1 := by
  rw [integral_betaMeasure ha hb]
  simpa using integral_betaPDF ha hb

/-- **The mean of the Beta law**: `E[X] = a/(a+b)`. -/
theorem integral_id_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t, t ∂(betaMeasure a b) = a / (a + b) := by
  rw [integral_betaMeasure ha hb, betaPDF_mean ha hb]

/-- **The integer moments of the Beta law**: `E[X^k] = ∏_{i<k} (a+i)/(a+b+i)`. -/
theorem integral_pow_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    ∫ t, t ^ k ∂(betaMeasure a b) = ∏ i ∈ Finset.range k, (a + i) / (a + b + i) := by
  rw [integral_betaMeasure ha hb, betaPDF_moment_nat ha hb k]

/-- **The second moment of the Beta law**: `E[X²] = a(a+1)/((a+b)(a+b+1))`. -/
theorem integral_sq_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t, t ^ (2:ℕ) ∂(betaMeasure a b) = a * (a + 1) / ((a + b) * (a + b + 1)) := by
  rw [integral_betaMeasure ha hb, betaPDF_second_moment ha hb]

/-- **The variance of the Beta law**: `E[X²] − E[X]² = ab/((a+b)²(a+b+1))`. -/
theorem variance_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t, t ^ (2:ℕ) ∂(betaMeasure a b)) - (∫ t, t ∂(betaMeasure a b)) ^ 2
      = a * b / ((a + b) ^ 2 * (a + b + 1)) := by
  rw [integral_sq_betaMeasure ha hb, integral_id_betaMeasure ha hb]
  have hab : (0:ℝ) < a + b := by linarith
  have hab1 : (0:ℝ) < a + b + 1 := by linarith
  field_simp
  ring

end SHSLib.Trigamma
