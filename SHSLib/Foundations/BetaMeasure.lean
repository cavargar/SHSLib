/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Beta law as a measure

Batches 171–176 built the Beta density `betaPDF`, the regularised incomplete
Beta function `regBetaFn` (its cumulative distribution function), the quantile
function `betaQuantile`, and the Beta–Binomial identity.  All of those live at
the level of Riemann/interval integrals.  This module packages the Beta law as
an honest Mathlib measure on `ℝ`:

  `betaMeasure a b = volume.withDensity (𝟙_{(0,1)} · betaPDF a b)`,

and proves

* `betaMeasure_univ` — total mass `1`, hence `IsProbabilityMeasure`;
* `betaMeasure_Iic` — the measure of `(-∞, x]` is `I_x(a,b)` for `x ∈ [0,1]`,
  together with the degenerate cases `x ≤ 0` and `1 ≤ x`;
* `betaMeasure_Ioc` — the measure of an interval `(x, y] ⊆ [0,1]`;
* `betaMeasure_singleton` — the law has no atoms.

This is the bridge that lets the Beta law be used wherever this library speaks
about probability measures, in particular for the division ratio of the
cell-size models.
-/
import SHSLib.Foundations.BetaQuantileContinuity

open Real Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SHSLib.Trigamma

/-- The Beta density as an `ℝ≥0∞`-valued function, supported on `(0,1)`. -/
noncomputable def betaDensity (a b : ℝ) : ℝ → ℝ≥0∞ :=
  Set.indicator (Set.Ioo (0:ℝ) 1) (fun t => ENNReal.ofReal (betaPDF a b t))

/-- The **Beta law** with shape parameters `a, b`, as a measure on `ℝ`. -/
noncomputable def betaMeasure (a b : ℝ) : Measure ℝ :=
  volume.withDensity (betaDensity a b)

theorem measurable_betaPDF (a b : ℝ) : Measurable (betaPDF a b) := by
  unfold betaPDF
  fun_prop

theorem measurable_betaDensity (a b : ℝ) : Measurable (betaDensity a b) :=
  (ENNReal.measurable_ofReal.comp (measurable_betaPDF a b)).indicator measurableSet_Ioo

/-- The Beta law of a measurable set is the Lebesgue integral of the density
over its intersection with `(0,1)`. -/
theorem betaMeasure_apply (a b : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    betaMeasure a b s = ∫⁻ t in Set.Ioo (0:ℝ) 1 ∩ s, ENNReal.ofReal (betaPDF a b t) := by
  rw [betaMeasure, withDensity_apply _ hs]
  unfold betaDensity
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]

/-- The Lebesgue integral of the Beta density over `(0, x]` is `I_x(a,b)`. -/
theorem lintegral_betaPDF_Ioc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫⁻ t in Set.Ioc 0 x, ENNReal.ofReal (betaPDF a b t)
      = ENNReal.ofReal (regBetaFn a b x) := by
  have hint : IntervalIntegrable (betaPDF a b) volume 0 x := by
    have h := betaIntegrand_intervalIntegrable_of_mem ha hb le_rfl (by norm_num) hx0 hx1
    have := h.div_const (betaFn a b)
    simpa [betaPDF, betaIntegrand] using this
  have hIoc : IntegrableOn (betaPDF a b) (Set.Ioc 0 x) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx0).mp hint
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 x)] betaPDF a b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact betaPDF_nonneg ha hb ht.1.le (ht.2.trans hx1)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIoc hnn]
  congr 1
  rw [regBetaFn, incompleteBetaFn, intervalIntegral.integral_of_le hx0]
  simp only [betaPDF, betaIntegrand]
  rw [MeasureTheory.integral_div]

/-- On `[0,1]` the intersection `(0,1) ∩ (-∞, x]` agrees with `(0, x]` up to a
null set. -/
theorem Ioo_inter_Iic_ae_eq_Ioc {x : ℝ} (hx1 : x ≤ 1) :
    ((Set.Ioo (0:ℝ) 1 ∩ Set.Iic x : Set ℝ)) =ᵐ[volume] (Set.Ioc (0:ℝ) x : Set ℝ) := by
  have hnull : volume ({(1:ℝ)} : Set ℝ) = 0 := by simp
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull] with t ht
  simp only [Set.mem_singleton_iff] at ht
  apply propext
  constructor
  · rintro ⟨⟨h0, _⟩, hx⟩
    exact ⟨h0, hx⟩
  · rintro ⟨h0, hx⟩
    exact ⟨⟨h0, lt_of_le_of_ne (hx.trans hx1) ht⟩, hx⟩

/-- **The Beta CDF**: for `x ∈ [0,1]` the Beta law of `(-∞, x]` is `I_x(a,b)`. -/
theorem betaMeasure_Iic {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    betaMeasure a b (Set.Iic x) = ENNReal.ofReal (regBetaFn a b x) := by
  rw [betaMeasure_apply a b measurableSet_Iic,
    MeasureTheory.setLIntegral_congr (Ioo_inter_Iic_ae_eq_Ioc hx1),
    lintegral_betaPDF_Ioc ha hb hx0 hx1]

/-- The Beta law is a probability measure: its total mass is `1`. -/
theorem betaMeasure_univ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaMeasure a b Set.univ = 1 := by
  rw [betaMeasure_apply a b MeasurableSet.univ, Set.inter_univ,
    MeasureTheory.setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := 1)),
    lintegral_betaPDF_Ioc ha hb zero_le_one le_rfl, regBetaFn_one ha hb, ENNReal.ofReal_one]

theorem isProbabilityMeasure_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (betaMeasure a b) :=
  ⟨betaMeasure_univ ha hb⟩

/-- Below `0` the Beta law puts no mass. -/
theorem betaMeasure_Iic_of_nonpos (a b : ℝ) {x : ℝ} (hx : x ≤ 0) :
    betaMeasure a b (Set.Iic x) = 0 := by
  rw [betaMeasure_apply a b measurableSet_Iic]
  have hempty : Set.Ioo (0:ℝ) 1 ∩ Set.Iic x = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro ⟨h0, _⟩ hxt
    linarith
  rw [hempty]
  simp

/-- Above `1` the Beta law has already accumulated all its mass. -/
theorem betaMeasure_Iic_of_one_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : 1 ≤ x) : betaMeasure a b (Set.Iic x) = 1 := by
  have h1 : betaMeasure a b (Set.Iic (1:ℝ)) = 1 := by
    rw [betaMeasure_Iic ha hb zero_le_one le_rfl, regBetaFn_one ha hb, ENNReal.ofReal_one]
  refine le_antisymm ?_ ?_
  · rw [← betaMeasure_univ ha hb]
    exact measure_mono (Set.subset_univ _)
  · rw [← h1]
    exact measure_mono (Set.Iic_subset_Iic.mpr hx)

/-- The Beta law of an interval `(x, y] ⊆ [0,1]`. -/
theorem betaMeasure_Ioc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x y : ℝ}
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    betaMeasure a b (Set.Ioc x y)
      = ENNReal.ofReal (regBetaFn a b y - regBetaFn a b x) := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hsplit : Set.Iic y = Set.Iic x ∪ Set.Ioc x y := (Set.Iic_union_Ioc_eq_Iic hxy).symm
  have hdisj : Disjoint (Set.Iic x) (Set.Ioc x y) := by
    rw [Set.disjoint_left]
    rintro t ht ⟨h1, _⟩
    exact absurd ht (by simpa using h1)
  have hadd : betaMeasure a b (Set.Iic y)
      = betaMeasure a b (Set.Iic x) + betaMeasure a b (Set.Ioc x y) := by
    rw [hsplit, measure_union hdisj measurableSet_Ioc]
  rw [betaMeasure_Iic ha hb hy0 hy1, betaMeasure_Iic ha hb hx0 hx1] at hadd
  have hmono : regBetaFn a b x ≤ regBetaFn a b y := regBetaFn_mono ha hb hx0 hxy hy1
  have hxnn : 0 ≤ regBetaFn a b x := (regBetaFn_mem_Icc ha hb hx0 hx1).1
  rw [show regBetaFn a b y = regBetaFn a b x + (regBetaFn a b y - regBetaFn a b x) by ring,
    ENNReal.ofReal_add hxnn (by linarith)] at hadd
  exact ((ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp hadd).symm

/-- The Beta law has no atoms. -/
theorem betaMeasure_singleton (a b : ℝ) (x : ℝ) : betaMeasure a b {x} = 0 := by
  rw [betaMeasure_apply a b (measurableSet_singleton x)]
  refine MeasureTheory.setLIntegral_measure_zero _ _ ?_
  exact measure_mono_null Set.inter_subset_right (by simp)

end SHSLib.Trigamma
