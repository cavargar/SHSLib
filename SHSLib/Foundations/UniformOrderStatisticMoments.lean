/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Moments and concentration of a uniform order statistic

Since the `(j+1)`-st order statistic of `n = j+m+1` independent uniforms has the
`Beta(j+1, m+1)` law (batch 188), all the Beta computations of the library
transfer to it:

  `E[X] = (j+1)/(n+1)`,
  `Var[X] = (j+1)(m+1)/((n+1)²(n+2))`,
  `P(|X − (j+1)/(n+1)| < c) ≥ 1 − Var[X]/c²`.

The transfers are the change-of-variables formula for a pushforward
(`integral_map`, `variance_map`) and, for the concentration statement, the
definition of the pushforward on a measurable set.
-/
import SHSLib.Foundations.UniformOrderStatisticLaw
import SHSLib.Foundations.BetaConcentration

open MeasureTheory ProbabilityTheory Set ENNReal

namespace SHSLib.Trigamma

/-- The `(j+1)`-st order statistic of a sample of `n = j+m+1` uniforms, as a
random variable on the sample space. -/
noncomputable def unifOrderStat (j m : ℕ) (w : Fin (j + m + 1) → ℝ) : ℝ :=
  orderStat (j + m + 1) w ⟨j, by omega⟩

theorem measurable_unifOrderStat (j m : ℕ) : Measurable (unifOrderStat j m) :=
  measurable_orderStat _ _

theorem map_unifOrderStat (j m : ℕ) :
    (unifPi (j + m + 1)).map (unifOrderStat j m) = betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1) :=
  map_orderStat j m

/-- **The mean of the `(j+1)`-st order statistic** of `n = j+m+1` uniforms is
`(j+1)/(n+1)`. -/
theorem integral_unifOrderStat (j m : ℕ) :
    ∫ w, unifOrderStat j m w ∂(unifPi (j + m + 1))
      = ((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) := by
  have hmap := integral_map (φ := unifOrderStat j m) (f := fun y : ℝ => y)
    (measurable_unifOrderStat j m).aemeasurable
    (by
      rw [map_unifOrderStat]
      exact measurable_id.aestronglyMeasurable)
  rw [map_unifOrderStat, integral_id_betaMeasure (by positivity) (by positivity)] at hmap
  rw [← hmap]
  ring_nf

/-- **The variance of the `(j+1)`-st order statistic** of `n = j+m+1` uniforms
is `(j+1)(m+1)/((n+1)²(n+2))`. -/
theorem variance_unifOrderStat (j m : ℕ) :
    variance (unifOrderStat j m) (unifPi (j + m + 1))
      = ((j : ℝ) + 1) * ((m : ℝ) + 1)
          / (((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3)) := by
  have hvar := variance_map (X := (id : ℝ → ℝ)) (Y := unifOrderStat j m)
    (μ := unifPi (j + m + 1))
    (by rw [map_unifOrderStat]; exact measurable_id.aemeasurable)
    (measurable_unifOrderStat j m).aemeasurable
  rw [map_unifOrderStat, variance_id_betaMeasure (by positivity) (by positivity)] at hvar
  have hcomp : (id : ℝ → ℝ) ∘ unifOrderStat j m = unifOrderStat j m := rfl
  rw [hcomp] at hvar
  rw [← hvar]
  ring_nf

/-- **Concentration of the order statistic**: it lies within `c` of its mean
`(j+1)/(n+1)` with probability at least `1 − Var/c²`. -/
theorem unifOrderStat_concentration (j m : ℕ) {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal
        (((j : ℝ) + 1) * ((m : ℝ) + 1)
          / (((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3)) / c ^ 2)
      ≤ unifPi (j + m + 1)
          {w | unifOrderStat j m w ∈
            Set.Ioo (((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) - c)
              (((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) + c)} := by
  have hmean : ((j : ℝ) + 1) / (((j : ℝ) + 1) + ((m : ℝ) + 1))
      = ((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) := by ring_nf
  have hvar : ((j : ℝ) + 1) * ((m : ℝ) + 1)
      / ((((j : ℝ) + 1) + ((m : ℝ) + 1)) ^ 2 * (((j : ℝ) + 1) + ((m : ℝ) + 1) + 1))
      = ((j : ℝ) + 1) * ((m : ℝ) + 1)
          / (((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3)) := by ring_nf
  have hconc := betaMeasure_concentration (a := (j : ℝ) + 1) (b := (m : ℝ) + 1)
    (by positivity) (by positivity) hc
  rw [hmean, hvar] at hconc
  have hset : unifPi (j + m + 1)
      {w | unifOrderStat j m w ∈
        Set.Ioo (((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) - c)
          (((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) + c)}
      = betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)
          (Set.Ioo (((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) - c)
            (((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) + c)) := by
    rw [← map_unifOrderStat j m,
      Measure.map_apply (measurable_unifOrderStat j m) measurableSet_Ioo]
    rfl
  rw [hset]
  exact hconc

end SHSLib.Trigamma
