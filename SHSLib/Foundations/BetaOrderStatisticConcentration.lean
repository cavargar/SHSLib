/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concentration of an order statistic of a Beta sample

Batches 193–194 computed the mean and the variance of the `(j+1)`-st order
statistic of a sample of `n = j+m+1` independent `Beta(1,b)` (resp. `Beta(a,1)`)
variables as ratios of Beta functions.  This module turns those two numbers into
a concentration statement, by Chebyshev's inequality.

The one structural input is square-integrability of the order statistic for the
product measure.  It holds for *every* Beta parent: the order statistic is the
image of the rank variable under the clamped quantile function, which takes its
values in `[0,1]`, so the order statistic is bounded by one almost surely and
the product measure is a probability measure.

The general statements are `orderStat_betaSample_chebyshev` and
`orderStat_betaSample_concentration`; specialising the mean and the variance
gives the explicit forms for the two elementary parent families.
-/
import SHSLib.Foundations.BetaOrderStatisticMomentsPower

open MeasureTheory ProbabilityTheory Set ENNReal

namespace SHSLib.Trigamma

/-! ### The order statistic is bounded -/

/-- The clamped Beta quantile takes its values in `[0,1]`. -/
theorem betaQuantileClamp_mem_Icc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℝ) :
    betaQuantileClamp a b p ∈ Set.Icc (0:ℝ) 1 := by
  have hmem : max 0 (min 1 p) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  rw [betaQuantileClamp]
  exact betaQuantile_mem_Icc ha hb hmem.1 hmem.2

/-- The product of Beta laws is a probability measure. -/
theorem isProbabilityMeasure_betaPi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    IsProbabilityMeasure (Measure.pi (fun _ : Fin n => betaMeasure a b)) := by
  haveI := isProbabilityMeasure_betaMeasure ha hb
  infer_instance

/-- **The order statistic of a Beta sample is bounded by one** almost surely. -/
theorem ae_norm_le_one_orderStat_betaSample {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (j m : ℕ) :
    ∀ᵐ w ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)),
      ‖unifOrderStat j m w‖ ≤ 1 := by
  have hmap : (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)).map
      (unifOrderStat j m)
      = (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp a b) :=
    map_orderStat_betaSample ha hb j m
  have hT : MeasurableSet {y : ℝ | 1 < ‖y‖} := by
    have : {y : ℝ | 1 < ‖y‖} = (fun y : ℝ => ‖y‖) ⁻¹' Set.Ioi 1 := rfl
    rw [this]
    exact measurable_norm measurableSet_Ioi
  have hpre : betaQuantileClamp a b ⁻¹' {y : ℝ | 1 < ‖y‖} = (∅ : Set ℝ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    have h := betaQuantileClamp_mem_Icc ha hb p
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have hzero : (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
      (unifOrderStat j m ⁻¹' {y : ℝ | 1 < ‖y‖}) = 0 := by
    rw [← Measure.map_apply (measurable_unifOrderStat j m) hT, hmap,
      Measure.map_apply (continuous_betaQuantileClamp ha hb).measurable hT, hpre,
      measure_empty]
  rw [Filter.eventually_iff, mem_ae_iff]
  convert hzero using 2
  ext w
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage, not_le]

/-- The order statistic of a Beta sample is square-integrable. -/
theorem memLp_orderStat_betaSample {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j m : ℕ) :
    MemLp (unifOrderStat j m) 2
      (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)) := by
  haveI := isProbabilityMeasure_betaPi ha hb (j + m + 1)
  exact MemLp.of_bound (measurable_unifOrderStat j m).aestronglyMeasurable 1
    (ae_norm_le_one_orderStat_betaSample ha hb j m)

/-! ### Chebyshev's inequality for the order statistic -/

/-- **Chebyshev's inequality for an order statistic of a Beta sample**: the
probability of deviating from the mean by at least `c` is at most
`Var/c²`. -/
theorem orderStat_betaSample_chebyshev {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j m : ℕ)
    {c : ℝ} (hc : 0 < c) :
    (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
        {w | c ≤ |unifOrderStat j m w
          - ∫ w', unifOrderStat j m w'
              ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))|}
      ≤ ENNReal.ofReal
          (variance (unifOrderStat j m)
            (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)) / c ^ 2) := by
  haveI := isProbabilityMeasure_betaPi ha hb (j + m + 1)
  exact ProbabilityTheory.meas_ge_le_variance_div_sq (memLp_orderStat_betaSample ha hb j m) hc

/-- The complementary form: at least `1 − Var/c²` of the mass of the order
statistic lies within `c` of its mean. -/
theorem orderStat_betaSample_concentration {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j m : ℕ)
    {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal
        (variance (unifOrderStat j m)
          (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)) / c ^ 2)
      ≤ (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
          {w | unifOrderStat j m w ∈
            Set.Ioo ((∫ w', unifOrderStat j m w'
                ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))) - c)
              ((∫ w', unifOrderStat j m w'
                ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))) + c)} := by
  haveI := isProbabilityMeasure_betaPi ha hb (j + m + 1)
  set μ := Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b) with hμ
  set e : ℝ := ∫ w', unifOrderStat j m w' ∂μ with he
  have hmeas : MeasurableSet {w | c ≤ |unifOrderStat j m w - e|} :=
    (((measurable_unifOrderStat j m).sub_const e).abs) measurableSet_Ici
  have hcompl : {w | c ≤ |unifOrderStat j m w - e|}ᶜ
      = {w | unifOrderStat j m w ∈ Set.Ioo (e - c) (e + c)} := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_Ioo, abs_lt]
    constructor
    · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hprob : μ {w | unifOrderStat j m w ∈ Set.Ioo (e - c) (e + c)}
      = 1 - μ {w | c ≤ |unifOrderStat j m w - e|} := by
    rw [← hcompl, prob_compl_eq_one_sub hmeas]
  rw [hprob]
  exact tsub_le_tsub_left (orderStat_betaSample_chebyshev ha hb j m hc) 1

/-! ### The two elementary parent families -/

/-- **Concentration for a `Beta(1,b)` sample**: with `R(c) = B(j+1, m+1+c)/B(j+1, m+1)`,
the order statistic lies within `c` of `1 − R(1/b)` with probability at least
`1 − (R(2/b) − R(1/b)²)/c²`. -/
theorem orderStat_betaOneSample_concentration {b : ℝ} (hb : 0 < b) (j m : ℕ)
    {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal
        ((betaOrderRatio j m (2 / b) - betaOrderRatio j m (1 / b) ^ 2) / c ^ 2)
      ≤ (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 b))
          {w | unifOrderStat j m w ∈
            Set.Ioo (1 - betaOrderRatio j m (1 / b) - c)
              (1 - betaOrderRatio j m (1 / b) + c)} := by
  have h := orderStat_betaSample_concentration one_pos hb j m hc
  rwa [integral_orderStat_betaOneSample hb j m, variance_orderStat_betaOneSample hb j m] at h

/-- **Concentration for a `Beta(a,1)` sample**: with
`R'(c) = B(j+1+c, m+1)/B(j+1, m+1)`, the order statistic lies within `c` of
`R'(1/a)` with probability at least `1 − (R'(2/a) − R'(1/a)²)/c²`. -/
theorem orderStat_betaOneRightSample_concentration {a : ℝ} (ha : 0 < a) (j m : ℕ)
    {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal
        ((betaOrderRatioLeft j m (2 / a) - betaOrderRatioLeft j m (1 / a) ^ 2) / c ^ 2)
      ≤ (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a 1))
          {w | unifOrderStat j m w ∈
            Set.Ioo (betaOrderRatioLeft j m (1 / a) - c)
              (betaOrderRatioLeft j m (1 / a) + c)} := by
  have h := orderStat_betaSample_concentration ha one_pos j m hc
  rwa [integral_orderStat_betaOneRightSample ha j m,
    variance_orderStat_betaOneRightSample ha j m] at h

end SHSLib.Trigamma
