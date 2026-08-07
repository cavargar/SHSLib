import SHSLib.Core.DavisResetOccupationRegular
import SHSLib.Core.DavisFiniteCompensatorMeasurable
import SHSLib.Core.DavisOneSegmentTruncatedCompensation

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # A criterion for the regularity of the reset occupation

`DavisResetOccupationRegular` bundles four measurability/integrability
conditions on a model and a test function: joint measurability of the reset
occupation density, its integrability on every elapsed window, and joint
measurability of the occupation compensator and of the survivor factor.  Every
concrete instance built so far discharged them by hand, by computing the
compensator and the survivor factor in closed form.

That work is unnecessary.  All four conditions follow from data that any
reasonable model has anyway:

* the augmented flow is jointly measurable (`DavisFlowRegular`), the resets are
  measurable (`DavisResetRegular`) and the intensities are measurable;
* the test function is measurable;
* the occupation density is continuous along the flow — the hypothesis
  `DavisResetOccupationContinuousAlongFlow`, which the model-level martingale
  statements ask for in any case.

The two integrals — the occupation compensator and the accumulated hazard — are
handled by one general fact: an integral over `[0, u]` of a jointly measurable
integrand is jointly measurable in the parameter and in `u`, because it is the
integral of the indicator of a measurable set.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}

/-! ## Measurability of a parametric integral over an initial segment -/

/-- **An integral over `[0, u]` is jointly measurable** in the parameter and in
the upper endpoint, as soon as the integrand is jointly measurable. -/
theorem measurable_setIntegral_Icc_zero {α : Type*} [MeasurableSpace α]
    {F : α × ℝ → ℝ} (hF : Measurable F) :
    Measurable fun p : α × ℝ≥0 => ∫ s in Set.Icc (0 : ℝ) (p.2 : ℝ), F (p.1, s) := by
  classical
  set f : (α × ℝ≥0) × ℝ → ℝ := fun p =>
    if 0 ≤ p.2 ∧ p.2 ≤ ((p.1.2 : ℝ)) then F (p.1.1, p.2) else 0 with hfdef
  have hsetm : MeasurableSet {p : (α × ℝ≥0) × ℝ |
      0 ≤ p.2 ∧ p.2 ≤ ((p.1.2 : ℝ))} := by
    have hm2 : Measurable fun p : (α × ℝ≥0) × ℝ => ((p.1.2 : ℝ)) :=
      measurable_coe_nnreal_real.comp (measurable_snd.comp measurable_fst)
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd hm2)
  have hfm : Measurable f := by
    refine Measurable.ite hsetm ?_ measurable_const
    exact hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hint : ∀ p : α × ℝ≥0,
      (∫ s in Set.Icc (0 : ℝ) (p.2 : ℝ), F (p.1, s)) = ∫ s : ℝ, f (p, s) := by
    intro p
    rw [← MeasureTheory.integral_indicator
      (measurableSet_Icc (a := (0 : ℝ)) (b := ((p.2 : ℝ))))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    by_cases hs : 0 ≤ s ∧ s ≤ ((p.2 : ℝ))
    · rw [Set.indicator_of_mem (Set.mem_Icc.mpr hs)]
      simp only [hfdef, if_pos hs]
    · rw [Set.indicator_of_notMem (fun hmem => hs (Set.mem_Icc.mp hmem))]
      simp only [hfdef, if_neg hs]
  simp only [hint]
  exact (hfm.stronglyMeasurable.integral_prod_right').measurable

/-! ## Measurability of the model data -/

variable (S : SHS Q n m)

omit [MeasurableSingletonClass Q] in
/-- The total intensity of a model with measurable intensities is measurable. -/
theorem measurable_totalIntensity [S.IntensitiesMeasurable] :
    Measurable fun z : DavisState Q n => S.totalIntensity z :=
  Finset.measurable_sum _ fun i _ => IntensitiesMeasurable.measurable i

omit [MeasurableSingletonClass Q] in
/-- The augmented flow, as a jointly measurable function of the state and a
real elapsed time. -/
theorem measurable_davisFlow_toNNReal {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) :
    Measurable fun p : DavisState Q n × ℝ => davisFlow S hflow p.2.toNNReal p.1 :=
  hf.measurable_joint.comp ((measurable_snd.real_toNNReal).prodMk measurable_fst)

omit [MeasurableSingletonClass Q] in
/-- The total intensity along the flow is jointly measurable. -/
theorem measurable_totalIntensity_davisFlow [S.IntensitiesMeasurable]
    {hflow : S.HasGlobalFlow} (hf : DavisFlowRegular S hflow) :
    Measurable fun p : DavisState Q n × ℝ =>
      S.totalIntensity (davisFlow S hflow p.2.toNNReal p.1) :=
  (measurable_totalIntensity S).comp (measurable_davisFlow_toNNReal S hf)

/-- **The reset occupation density is jointly measurable** for a measurable test
function. -/
theorem measurable_davisSegmentResetOccupationDensity [S.IntensitiesMeasurable]
    {hflow : S.HasGlobalFlow} (hf : DavisFlowRegular S hflow)
    (hr : DavisResetRegular S) {g : DavisState Q n → ℝ} (hg : Measurable g) :
    Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentResetOccupationDensity S hflow g p.1 p.2 := by
  unfold davisSegmentResetOccupationDensity
  exact (measurable_totalIntensity_davisFlow S hf).mul
    ((measurable_davisExpectedResetIncrement S hr g hg).comp
      (measurable_davisFlow_toNNReal S hf))

omit [MeasurableSingletonClass Q] in
/-- **The survivor factor is jointly measurable** in the state and the elapsed
duration. -/
theorem measurable_davisSegmentSurvivor [S.IntensitiesMeasurable]
    {hflow : S.HasGlobalFlow} (hf : DavisFlowRegular S hflow) :
    Measurable fun p : DavisState Q n × ℝ≥0 => davisSegmentSurvivor S hflow p.1 p.2 := by
  have : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisIntegratedHazard S hflow p.1 p.2 :=
    measurable_setIntegral_Icc_zero (measurable_totalIntensity_davisFlow S hf)
  exact Real.measurable_exp.comp this.neg

/-- **The reset occupation compensator is jointly measurable.** -/
theorem measurable_davisSegmentResetOccupationCompensator [S.IntensitiesMeasurable]
    {hflow : S.HasGlobalFlow} (hf : DavisFlowRegular S hflow)
    (hr : DavisResetRegular S) {g : DavisState Q n → ℝ} (hg : Measurable g) :
    Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentResetOccupationCompensator S hflow g p.1 p.2 :=
  measurable_setIntegral_Icc_zero
    (measurable_davisSegmentResetOccupationDensity S hf hr hg)

/-! ## The criterion -/

/-- **Regularity of the reset occupation, from measurability alone.**  For a
model with a measurable flow, measurable resets and measurable intensities, and
a measurable test function whose occupation density is continuous along the
flow, all four conditions of `DavisResetOccupationRegular` hold. -/
theorem davisResetOccupationRegular_of_measurable [S.IntensitiesMeasurable]
    {hflow : S.HasGlobalFlow} (hf : DavisFlowRegular S hflow)
    (hr : DavisResetRegular S) {g : DavisState Q n → ℝ} (hg : Measurable g)
    (hcont : DavisResetOccupationContinuousAlongFlow S hflow g) :
    DavisResetOccupationRegular S hflow g where
  density_measurable := measurable_davisSegmentResetOccupationDensity S hf hr hg
  density_integrableOn := fun z _ => (hcont z).integrableOn_Icc
  stoppedCompensator_measurable :=
    measurable_davisSegmentResetOccupationCompensator S hf hr hg
  survivor_measurable := measurable_davisSegmentSurvivor S hf

end SHS
