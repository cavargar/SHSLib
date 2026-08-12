/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Moments of an order statistic of a Beta sample

Batch 190 identified the law of the `(j+1)`-st order statistic of a sample of
`n = j+m+1` independent `Beta(a,b)` variables as the pushforward of
`Beta(j+1, m+1)` under the `Beta(a,b)` quantile function.  This module turns
that law identity into closed-form *moments*, for the parent family with a unit
first parameter, where the quantile function is elementary:

  `Q_{1,b}(p) = 1 − (1−p)^{1/b}`.

The two ingredients are

* the **fractional moments of the Beta law**,
  `E[X^s] = B(a+s, b)/B(a,b)` and `E[(1−X)^s] = B(a, b+s)/B(a,b)` for `s ≥ 0`
  (the second by the reflection `t ↦ 1−t`, which exchanges the parameters), and
* the law identity `map_orderStat_betaSample` of batch 190.

Together they give the mean, the second moment and the variance of the
`(j+1)`-st order statistic of a `Beta(1,b)` sample as ratios of Beta functions,
and, as a check, the classical uniform values `(j+1)/(n+1)` when `b = 1` and the
mean `1/(nb+1)` of the minimum of `n` such variables.
-/
import SHSLib.Foundations.BetaPowerLaw
import SHSLib.Foundations.UniformOrderStatisticMoments

open MeasureTheory ProbabilityTheory Set

namespace SHSLib.Trigamma

/-! ### Fractional moments of the Beta law -/

/-- **The fractional moments of the Beta law**: `E[X^s] = B(a+s, b)/B(a,b)` for
every `s ≥ 0`. -/
theorem integral_rpow_betaMeasure {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) :
    ∫ t, t ^ s ∂(betaMeasure a b) = betaFn (a + s) b / betaFn a b := by
  rw [integral_betaMeasure ha hb, integral_rpow_mul_betaPDF ha hb hs]

/-- The Beta density is reflected by `t ↦ 1 − t`, with the parameters
exchanged. -/
theorem betaPDF_one_sub (a b t : ℝ) : betaPDF b a (1 - t) = betaPDF a b t := by
  unfold betaPDF
  rw [show (1:ℝ) - (1 - t) = t by ring, betaFn_symm b a, mul_comm]

/-- A bounded measurable function is integrable for the Beta law. -/
theorem integrable_of_ae_bounded_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (betaMeasure a b)) {C : ℝ}
    (hC : ∀ᵐ t ∂(betaMeasure a b), ‖g t‖ ≤ C) :
    Integrable g (betaMeasure a b) :=
  (memLp_one_iff_integrable).1 (memLp_of_ae_bounded_betaMeasure ha hb hg hC 1)

/-- `t ↦ (1−t)^s` is integrable for the Beta law when `s ≥ 0`. -/
theorem integrable_one_sub_rpow_betaMeasure {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 ≤ s) :
    Integrable (fun t : ℝ => (1 - t) ^ s) (betaMeasure a b) := by
  refine integrable_of_ae_bounded_betaMeasure ha hb
    (((measurable_const.sub measurable_id).pow_const s).aestronglyMeasurable) (C := 1) ?_
  filter_upwards [ae_mem_Ioo_betaMeasure a b] with t ht
  have h0 : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 s)]
  exact Real.rpow_le_one h0 (by linarith [ht.1]) hs

/-- **The reflected fractional moments of the Beta law**:
`E[(1−X)^s] = B(a, b+s)/B(a,b)` for every `s ≥ 0`. -/
theorem integral_one_sub_rpow_betaMeasure {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 ≤ s) :
    ∫ t, (1 - t) ^ s ∂(betaMeasure a b) = betaFn a (b + s) / betaFn a b := by
  rw [integral_betaMeasure ha hb]
  have hsub : (∫ t in (0:ℝ)..1, (1 - t) ^ s * betaPDF a b t)
      = ∫ t in (0:ℝ)..1, t ^ s * betaPDF b a t := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := (0:ℝ)) (b := (1:ℝ)) (fun x : ℝ => x ^ s * betaPDF b a x) 1
    simpa [betaPDF_one_sub] using h
  rw [hsub, integral_rpow_mul_betaPDF hb ha hs, betaFn_symm (b + s) a, betaFn_symm b a]

/-! ### The order statistic of a Beta sample -/

/-- The expectation of the `(j+1)`-st order statistic of a `Beta(a,b)` sample is
the expectation of the `Beta(a,b)` quantile function under `Beta(j+1, m+1)`. -/
theorem integral_orderStat_betaSample {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j m : ℕ)
    (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ w, g (unifOrderStat j m w)
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
      = ∫ p, g (betaQuantileClamp a b p) ∂(betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) := by
  have hmap := map_orderStat_betaSample ha hb j m
  have hX : (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w ⟨j, by omega⟩)
      = unifOrderStat j m := rfl
  rw [hX] at hmap
  have h1 : ∫ y, g y ∂((Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)).map
        (unifOrderStat j m))
      = ∫ w, g (unifOrderStat j m w)
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)) :=
    integral_map (measurable_unifOrderStat j m).aemeasurable hg.aestronglyMeasurable
  have h2 : ∫ y, g y ∂((betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp a b))
      = ∫ p, g (betaQuantileClamp a b p) ∂(betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    integral_map (continuous_betaQuantileClamp ha hb).measurable.aemeasurable
      hg.aestronglyMeasurable
  rw [← h1, hmap, h2]

/-- The clamped `Beta(1,b)` quantile is `p ↦ 1 − (1−p)^{1/b}` on `[0,1]`. -/
theorem betaQuantileClamp_one_left {b : ℝ} (hb : 0 < b) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    betaQuantileClamp 1 b p = 1 - (1 - p) ^ (1 / b) := by
  rw [betaQuantileClamp_eq_of_mem hp, betaQuantile_one_left hb hp.1 hp.2]

/-- The Beta-function ratio `R(c) = B(j+1, m+1+c)/B(j+1, m+1)`, the `c`-th
reflected moment of `Beta(j+1, m+1)`. -/
noncomputable def betaOrderRatio (j m : ℕ) (c : ℝ) : ℝ :=
  betaFn ((j : ℝ) + 1) ((m : ℝ) + 1 + c) / betaFn ((j : ℝ) + 1) ((m : ℝ) + 1)

/-- The mean of the clamped `Beta(1,b)` quantile under `Beta(j+1, m+1)`. -/
theorem integral_betaQuantileClamp_one_left {b : ℝ} (hb : 0 < b) (j m : ℝ)
    (hj : 0 < j) (hm : 0 < m) :
    ∫ p, betaQuantileClamp 1 b p ∂(betaMeasure j m)
      = 1 - betaFn j (m + 1 / b) / betaFn j m := by
  haveI : IsProbabilityMeasure (betaMeasure j m) := isProbabilityMeasure_betaMeasure hj hm
  have hs : (0:ℝ) ≤ 1 / b := by positivity
  have hae : ∀ᵐ p ∂(betaMeasure j m),
      betaQuantileClamp 1 b p = 1 - (1 - p) ^ (1 / b) := by
    filter_upwards [ae_mem_Ioo_betaMeasure j m] with p hp
    exact betaQuantileClamp_one_left hb ⟨hp.1.le, hp.2.le⟩
  rw [integral_congr_ae hae,
    integral_sub (integrable_const 1) (integrable_one_sub_rpow_betaMeasure hj hm hs),
    integral_one_sub_rpow_betaMeasure hj hm hs, integral_const]
  simp

/-- The second moment of the clamped `Beta(1,b)` quantile under
`Beta(j+1, m+1)`. -/
theorem integral_sq_betaQuantileClamp_one_left {b : ℝ} (hb : 0 < b) (j m : ℝ)
    (hj : 0 < j) (hm : 0 < m) :
    ∫ p, (betaQuantileClamp 1 b p) ^ 2 ∂(betaMeasure j m)
      = 1 - 2 * (betaFn j (m + 1 / b) / betaFn j m)
          + betaFn j (m + 2 / b) / betaFn j m := by
  haveI : IsProbabilityMeasure (betaMeasure j m) := isProbabilityMeasure_betaMeasure hj hm
  have hs1 : (0:ℝ) ≤ 1 / b := by positivity
  have hs2 : (0:ℝ) ≤ 2 / b := by positivity
  have hae : ∀ᵐ p ∂(betaMeasure j m),
      (betaQuantileClamp 1 b p) ^ 2
        = 1 - 2 * (1 - p) ^ (1 / b) + (1 - p) ^ (2 / b) := by
    filter_upwards [ae_mem_Ioo_betaMeasure j m] with p hp
    have h0 : (0:ℝ) ≤ 1 - p := by linarith [hp.2]
    have hsq : ((1 - p) ^ (1 / b)) ^ 2 = (1 - p) ^ (2 / b) := by
      rw [← Real.rpow_natCast ((1 - p) ^ (1 / b)) 2, ← Real.rpow_mul h0]
      norm_num
      ring_nf
    rw [betaQuantileClamp_one_left hb ⟨hp.1.le, hp.2.le⟩]
    rw [← hsq]; ring
  have hint1 : Integrable (fun p : ℝ => 1 - 2 * (1 - p) ^ (1 / b)) (betaMeasure j m) :=
    (integrable_const (1:ℝ)).sub ((integrable_one_sub_rpow_betaMeasure hj hm hs1).const_mul 2)
  have hint2 : Integrable (fun p : ℝ => (1 - p) ^ (2 / b)) (betaMeasure j m) :=
    integrable_one_sub_rpow_betaMeasure hj hm hs2
  rw [integral_congr_ae hae,
    integral_add (f := fun p : ℝ => 1 - 2 * (1 - p) ^ (1 / b))
      (g := fun p : ℝ => (1 - p) ^ (2 / b)) hint1 hint2,
    integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun p : ℝ => 2 * (1 - p) ^ (1 / b))
      (integrable_const 1)
      ((integrable_one_sub_rpow_betaMeasure hj hm hs1).const_mul 2),
    integral_const_mul, integral_one_sub_rpow_betaMeasure hj hm hs1,
    integral_one_sub_rpow_betaMeasure hj hm hs2, integral_const]
  simp

/-- **The mean of the `(j+1)`-st order statistic of a `Beta(1,b)` sample** of
size `n = j+m+1`: `1 − B(j+1, m+1+1/b)/B(j+1, m+1)`. -/
theorem integral_orderStat_betaOneSample {b : ℝ} (hb : 0 < b) (j m : ℕ) :
    ∫ w, unifOrderStat j m w
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 b))
      = 1 - betaOrderRatio j m (1 / b) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have h := integral_orderStat_betaSample one_pos hb j m (fun y => y) continuous_id
  rw [h, integral_betaQuantileClamp_one_left hb _ _ hj hm, betaOrderRatio]

/-- **The second moment of the `(j+1)`-st order statistic of a `Beta(1,b)`
sample**. -/
theorem integral_sq_orderStat_betaOneSample {b : ℝ} (hb : 0 < b) (j m : ℕ) :
    ∫ w, (unifOrderStat j m w) ^ 2
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 b))
      = 1 - 2 * betaOrderRatio j m (1 / b) + betaOrderRatio j m (2 / b) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have h := integral_orderStat_betaSample one_pos hb j m (fun y => y ^ 2)
    (continuous_pow 2)
  rw [h, integral_sq_betaQuantileClamp_one_left hb _ _ hj hm, betaOrderRatio,
    betaOrderRatio]

/-- **The variance of the `(j+1)`-st order statistic of a `Beta(1,b)` sample**:
`R(2/b) − R(1/b)²`. -/
theorem variance_orderStat_betaOneSample {b : ℝ} (hb : 0 < b) (j m : ℕ) :
    variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 b))
      = betaOrderRatio j m (2 / b) - betaOrderRatio j m (1 / b) ^ 2 := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  haveI : IsProbabilityMeasure (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    isProbabilityMeasure_betaMeasure hj hm
  have hmap : (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 b)).map
      (unifOrderStat j m)
      = (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp 1 b) :=
    map_orderStat_betaSample one_pos hb j m
  have h1 : variance (id : ℝ → ℝ)
      ((Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 b)).map (unifOrderStat j m))
      = variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 b)) :=
    variance_map measurable_id.aemeasurable (measurable_unifOrderStat j m).aemeasurable
  have h2 : variance (id : ℝ → ℝ)
      ((betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp 1 b))
      = variance (betaQuantileClamp 1 b) (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    variance_map measurable_id.aemeasurable
      (continuous_betaQuantileClamp one_pos hb).measurable.aemeasurable
  have hQ2 : MemLp (betaQuantileClamp 1 b) 2
      (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) := by
    refine memLp_of_ae_bounded_betaMeasure hj hm
      (continuous_betaQuantileClamp one_pos hb).measurable.aestronglyMeasurable (C := 1) ?_ 2
    filter_upwards [ae_mem_Ioo_betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)] with p hp
    have h0 : (0:ℝ) ≤ 1 - p := by linarith [hp.2]
    have hle : (1 - p) ^ (1 / b) ≤ 1 :=
      Real.rpow_le_one h0 (by linarith [hp.1]) (by positivity)
    have hge : (0:ℝ) ≤ (1 - p) ^ (1 / b) := Real.rpow_nonneg h0 _
    rw [betaQuantileClamp_one_left hb ⟨hp.1.le, hp.2.le⟩, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  rw [← h1, hmap, h2, variance_eq_sub hQ2]
  have hsq : ∫ p, ((betaQuantileClamp 1 b) ^ 2) p
      ∂(betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1))
      = ∫ p, (betaQuantileClamp 1 b p) ^ 2
        ∂(betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) := by
    simp
  rw [hsq, integral_sq_betaQuantileClamp_one_left hb _ _ hj hm,
    integral_betaQuantileClamp_one_left hb _ _ hj hm, betaOrderRatio, betaOrderRatio]
  ring

/-! ### Two checks -/

/-- For `b = 1` the parent law is uniform and the mean is the classical
`(j+1)/(n+1)`. -/
theorem integral_orderStat_betaOneSample_uniform (j m : ℕ) :
    ∫ w, unifOrderStat j m w
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 1))
      = ((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  rw [integral_orderStat_betaOneSample one_pos j m, betaOrderRatio,
    show ((m : ℝ) + 1 + 1 / 1) = ((m : ℝ) + 1) + 1 by norm_num,
    betaFn_add_one_right hj hm, mul_comm, mul_div_assoc,
    div_self (betaFn_pos hj hm).ne']
  field_simp
  ring

/-- **The mean of the minimum of `n = m+1` independent `Beta(1,b)` variables**
is `1/(nb+1)` — the minimum is `Beta(1, nb)`. -/
theorem integral_min_betaOneSample {b : ℝ} (hb : 0 < b) (m : ℕ) :
    ∫ w, unifOrderStat 0 m w
        ∂(Measure.pi (fun _ : Fin (0 + m + 1) => betaMeasure 1 b))
      = 1 / (((m : ℝ) + 1) * b + 1) := by
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hmb : (0:ℝ) < (m : ℝ) + 1 + 1 / b := by positivity
  rw [integral_orderStat_betaOneSample hb 0 m, betaOrderRatio]
  rw [Nat.cast_zero, zero_add, betaFn_symm 1 ((m : ℝ) + 1 + 1 / b), betaFn_symm 1 ((m : ℝ) + 1),
    betaFn_one_right hmb, betaFn_one_right hm]
  have hb' : b ≠ 0 := hb.ne'
  field_simp
  ring

end SHSLib.Trigamma
