/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Moments of an order statistic of a power-law (`Beta(a,1)`) sample

Batch 193 computed the moments of an order statistic of a `Beta(1,b)` sample,
whose quantile function is `p ↦ 1 − (1−p)^{1/b}`.  This module treats the other
elementary family, `Beta(a,1)`, the *power law* with distribution function
`x^a` and quantile function

  `Q_{a,1}(p) = p^{1/a}`.

Here the reflection of batch 193 is not needed: the moments of the order
statistic are the *direct* fractional moments of the rank law, so with

  `R'(c) = B(j+1+c, m+1) / B(j+1, m+1)`

the `(j+1)`-st order statistic of `n = j+m+1` independent `Beta(a,1)` variables
has mean `R'(1/a)`, second moment `R'(2/a)` and variance `R'(2/a) − R'(1/a)²`.

Two checks: at `a = 1` (the uniform parent) this module's ratio and batch 193's
agree and both give the classical mean `(j+1)/(n+1)`; and at `m = 0` (the sample
maximum) the mean is `na/(na+1)`, the mean of a `Beta(na, 1)` variable.
-/
import SHSLib.Foundations.BetaOrderStatisticMoments

open MeasureTheory ProbabilityTheory Set

namespace SHSLib.Trigamma

/-- `t ↦ t^s` is integrable for the Beta law when `s ≥ 0`. -/
theorem integrable_rpow_betaMeasure {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) :
    Integrable (fun t : ℝ => t ^ s) (betaMeasure a b) := by
  refine integrable_of_ae_bounded_betaMeasure ha hb
    ((measurable_id.pow_const s).aestronglyMeasurable) (C := 1) ?_
  filter_upwards [ae_mem_Ioo_betaMeasure a b] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.1.le s)]
  exact Real.rpow_le_one ht.1.le ht.2.le hs

/-- The clamped `Beta(a,1)` quantile is `p ↦ p^{1/a}` on `[0,1]`. -/
theorem betaQuantileClamp_one_right {a : ℝ} (ha : 0 < a) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    betaQuantileClamp a 1 p = p ^ (1 / a) := by
  rw [betaQuantileClamp_eq_of_mem hp, betaQuantile_one_right ha hp.1 hp.2]

/-- The Beta-function ratio `R'(c) = B(j+1+c, m+1)/B(j+1, m+1)`, the `c`-th
direct moment of `Beta(j+1, m+1)`. -/
noncomputable def betaOrderRatioLeft (j m : ℕ) (c : ℝ) : ℝ :=
  betaFn ((j : ℝ) + 1 + c) ((m : ℝ) + 1) / betaFn ((j : ℝ) + 1) ((m : ℝ) + 1)

/-- The mean of the clamped `Beta(a,1)` quantile under `Beta(j, m)`. -/
theorem integral_betaQuantileClamp_one_right {a : ℝ} (ha : 0 < a) (j m : ℝ)
    (hj : 0 < j) (hm : 0 < m) :
    ∫ p, betaQuantileClamp a 1 p ∂(betaMeasure j m)
      = betaFn (j + 1 / a) m / betaFn j m := by
  have hs : (0:ℝ) ≤ 1 / a := by positivity
  have hae : ∀ᵐ p ∂(betaMeasure j m), betaQuantileClamp a 1 p = p ^ (1 / a) := by
    filter_upwards [ae_mem_Ioo_betaMeasure j m] with p hp
    exact betaQuantileClamp_one_right ha ⟨hp.1.le, hp.2.le⟩
  rw [integral_congr_ae hae, integral_rpow_betaMeasure hj hm hs]

/-- The second moment of the clamped `Beta(a,1)` quantile under `Beta(j, m)`. -/
theorem integral_sq_betaQuantileClamp_one_right {a : ℝ} (ha : 0 < a) (j m : ℝ)
    (hj : 0 < j) (hm : 0 < m) :
    ∫ p, (betaQuantileClamp a 1 p) ^ 2 ∂(betaMeasure j m)
      = betaFn (j + 2 / a) m / betaFn j m := by
  have hs : (0:ℝ) ≤ 2 / a := by positivity
  have hae : ∀ᵐ p ∂(betaMeasure j m), (betaQuantileClamp a 1 p) ^ 2 = p ^ (2 / a) := by
    filter_upwards [ae_mem_Ioo_betaMeasure j m] with p hp
    rw [betaQuantileClamp_one_right ha ⟨hp.1.le, hp.2.le⟩,
      ← Real.rpow_natCast (p ^ (1 / a)) 2, ← Real.rpow_mul hp.1.le]
    norm_num
    ring_nf
  rw [integral_congr_ae hae, integral_rpow_betaMeasure hj hm hs]

/-- **The mean of the `(j+1)`-st order statistic of a `Beta(a,1)` sample** of
size `n = j+m+1`: `B(j+1+1/a, m+1)/B(j+1, m+1)`. -/
theorem integral_orderStat_betaOneRightSample {a : ℝ} (ha : 0 < a) (j m : ℕ) :
    ∫ w, unifOrderStat j m w
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a 1))
      = betaOrderRatioLeft j m (1 / a) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have h := integral_orderStat_betaSample ha one_pos j m (fun y => y) continuous_id
  rw [h, integral_betaQuantileClamp_one_right ha _ _ hj hm, betaOrderRatioLeft]

/-- **The second moment of the `(j+1)`-st order statistic of a `Beta(a,1)`
sample**. -/
theorem integral_sq_orderStat_betaOneRightSample {a : ℝ} (ha : 0 < a) (j m : ℕ) :
    ∫ w, (unifOrderStat j m w) ^ 2
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a 1))
      = betaOrderRatioLeft j m (2 / a) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have h := integral_orderStat_betaSample ha one_pos j m (fun y => y ^ 2) (continuous_pow 2)
  rw [h, integral_sq_betaQuantileClamp_one_right ha _ _ hj hm, betaOrderRatioLeft]

/-- **The variance of the `(j+1)`-st order statistic of a `Beta(a,1)` sample**:
`R'(2/a) − R'(1/a)²`. -/
theorem variance_orderStat_betaOneRightSample {a : ℝ} (ha : 0 < a) (j m : ℕ) :
    variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a 1))
      = betaOrderRatioLeft j m (2 / a) - betaOrderRatioLeft j m (1 / a) ^ 2 := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  haveI : IsProbabilityMeasure (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    isProbabilityMeasure_betaMeasure hj hm
  have hmap : (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a 1)).map
      (unifOrderStat j m)
      = (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp a 1) :=
    map_orderStat_betaSample ha one_pos j m
  have h1 : variance (id : ℝ → ℝ)
      ((Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a 1)).map (unifOrderStat j m))
      = variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a 1)) :=
    variance_map measurable_id.aemeasurable (measurable_unifOrderStat j m).aemeasurable
  have h2 : variance (id : ℝ → ℝ)
      ((betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp a 1))
      = variance (betaQuantileClamp a 1) (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    variance_map measurable_id.aemeasurable
      (continuous_betaQuantileClamp ha one_pos).measurable.aemeasurable
  have hQ2 : MemLp (betaQuantileClamp a 1) 2
      (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) := by
    refine memLp_of_ae_bounded_betaMeasure hj hm
      (continuous_betaQuantileClamp ha one_pos).measurable.aestronglyMeasurable (C := 1) ?_ 2
    filter_upwards [ae_mem_Ioo_betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)] with p hp
    rw [betaQuantileClamp_one_right ha ⟨hp.1.le, hp.2.le⟩, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hp.1.le _)]
    exact Real.rpow_le_one hp.1.le hp.2.le (by positivity)
  rw [← h1, hmap, h2, variance_eq_sub hQ2]
  have hsq : ∫ p, ((betaQuantileClamp a 1) ^ 2) p
      ∂(betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1))
      = ∫ p, (betaQuantileClamp a 1 p) ^ 2
        ∂(betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) := by
    simp
  rw [hsq, integral_sq_betaQuantileClamp_one_right ha _ _ hj hm,
    integral_betaQuantileClamp_one_right ha _ _ hj hm, betaOrderRatioLeft,
    betaOrderRatioLeft]

/-! ### Two checks -/

/-- The rank-law ratio of batch 193 at `c = 1`: `B(j+1, m+2)/B(j+1, m+1) = (m+1)/(n+1)`. -/
theorem betaOrderRatio_one (j m : ℕ) :
    betaOrderRatio j m 1 = ((m : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  rw [betaOrderRatio, betaFn_add_one_right hj hm, mul_comm, mul_div_assoc,
    div_self (betaFn_pos hj hm).ne']
  field_simp
  ring

/-- The rank-law ratio of this module at `c = 1`:
`B(j+2, m+1)/B(j+1, m+1) = (j+1)/(n+1)`. -/
theorem betaOrderRatioLeft_one (j m : ℕ) :
    betaOrderRatioLeft j m 1 = ((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  rw [betaOrderRatioLeft, betaFn_symm ((j : ℝ) + 1 + 1) ((m : ℝ) + 1),
    betaFn_add_one_right hm hj, betaFn_symm ((m : ℝ) + 1) ((j : ℝ) + 1), mul_comm,
    mul_div_assoc, div_self (betaFn_pos hj hm).ne']
  field_simp
  ring

/-- **Consistency of the two parent families at the uniform law.**  For `a = 1`
both `Beta(a,1)` and `Beta(1,b)` are the uniform law, and the mean formulas of
this module and of batch 193 agree, both giving `(j+1)/(n+1)`. -/
theorem betaOrderRatioLeft_one_eq (j m : ℕ) :
    betaOrderRatioLeft j m 1 = 1 - betaOrderRatio j m 1 := by
  rw [betaOrderRatioLeft_one, betaOrderRatio_one]
  have hn : (0:ℝ) < (j : ℝ) + (m : ℝ) + 2 := by positivity
  field_simp
  ring

/-- **The mean of the maximum of `n = j+1` independent `Beta(a,1)` variables**
is `na/(na+1)` — the maximum is `Beta(na, 1)`. -/
theorem integral_max_betaOneRightSample {a : ℝ} (ha : 0 < a) (j : ℕ) :
    ∫ w, unifOrderStat j 0 w
        ∂(Measure.pi (fun _ : Fin (j + 0 + 1) => betaMeasure a 1))
      = ((j : ℝ) + 1) * a / (((j : ℝ) + 1) * a + 1) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hja : (0:ℝ) < (j : ℝ) + 1 + 1 / a := by positivity
  rw [integral_orderStat_betaOneRightSample ha j 0, betaOrderRatioLeft]
  rw [Nat.cast_zero, zero_add, betaFn_one_right hja, betaFn_one_right hj]
  have ha' : a ≠ 0 := ha.ne'
  field_simp

end SHSLib.Trigamma
