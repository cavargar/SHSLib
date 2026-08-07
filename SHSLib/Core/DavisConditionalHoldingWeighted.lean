import SHSLib.Core.DavisConditionalHoldingRandomThreshold

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The weighted survivor identity

The conditional holding-time law at a history-measurable threshold, proved in
the previous module, is an identity between the measure of an event and an
integral of the survivor factor.  The conditional step of the one-segment
martingale needs its *weighted* form: the same identity with a history
measurable weight inserted on both sides,

`∫⁻ (A ∩ {u < h_k}) w = ∫⁻ A w · Sur_k(u)`.

The passage from sets to weights is a general measure-theoretic fact: two
measures that agree on a sub-σ-algebra integrate every function measurable for
that sub-σ-algebra identically.  Applying it to the restriction of `P` to the
survival event and to `P` weighted by the survivor factor gives the weighted
identity; a signed version for a bounded weight follows by splitting the weight
into positive and negative parts.

The intended application is the conditional law of the *active part* of the
one-segment contribution: on the event that segment `k` is still running at
the observation time, the partial occupation compensator carried at a later
time is a history-measurable weight, and the weighted identity computes its
conditional mean as the survivor-weighted compensator.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Measures agreeing on a sub-σ-algebra -/

/-- Two measures agreeing on a sub-σ-algebra give the same lower integral to
every function measurable for that sub-σ-algebra. -/
theorem lintegral_eq_of_measure_eq_of_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {mS : MeasurableSpace Ω}
    (hm : mS ≤ mΩ) (μ ν : @Measure Ω mΩ)
    (hagree : ∀ A, MeasurableSet[mS] A → μ A = ν A)
    (w : Ω → ℝ≥0∞) (hw : Measurable[mS] w) :
    ∫⁻ ω, w ω ∂μ = ∫⁻ ω, w ω ∂ν := by
  have h1 : μ.trim hm = ν.trim hm := by
    refine Measure.ext fun A hA => ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
    exact hagree A hA
  rw [← lintegral_trim hm hw, ← lintegral_trim hm hw, h1]

/-! ## The weighted survivor identity -/

/-- **The weighted survivor identity.**  For a history-measurable threshold
and a history-measurable nonnegative weight, integrating the weight over the
part of a history event on which the segment survives the threshold is the
same as integrating the survivor-weighted weight over the whole event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_lt_holdingTime_weighted
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (k : ℕ) (u : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (w : Ω → ℝ≥0∞)
    (hw : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] w) :
    ∫⁻ ω in A ∩ {ω | u ω < ξ.holdingTime k ω}, w ω ∂P =
      ∫⁻ ω in A, w ω * ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
          (u ω)) ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  set ρ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u ω))
    with hρ
  have hm : (F k : MeasurableSpace Ω) ≤ mΩ := F.le k
  have hHmeas : Measurable fun ω =>
      (davisPreJumpHistory S hflow ξ initial k ω).currentState :=
    (DavisPreJumpHistory.measurable_currentState k).comp
      (hξ.preJumpHistory S hflow hf hr initial k)
  have hρmeas : Measurable ρ :=
    (hsurv.comp (hHmeas.prodMk (hu.mono hm le_rfl))).ennreal_ofReal
  have hAm : MeasurableSet A := hm _ hA
  have hSm : MeasurableSet {ω | u ω < ξ.holdingTime k ω} :=
    measurableSet_lt (hu.mono hm le_rfl) (hξ.holdingTime k)
  -- the two measures that agree on the history σ-algebra
  have hagree : ∀ B, MeasurableSet[F k] B →
      (P.restrict {ω | u ω < ξ.holdingTime k ω}) B = (P.withDensity ρ) B := by
    intro B hB
    rw [Measure.restrict_apply (hm _ hB), withDensity_apply ρ (hm _ hB)]
    exact hlaw.measure_lt_holdingTime_of_historyMeasurable hcont hsurv k u hu B hB
  have hind : Measurable[F k] (A.indicator w) :=
    hw.indicator (s := A) hA
  have hkey := lintegral_eq_of_measure_eq_of_le hm
    (P.restrict {ω | u ω < ξ.holdingTime k ω}) (P.withDensity ρ) hagree
    (A.indicator w) hind
  -- rewrite both sides as set integrals
  rw [lintegral_indicator hAm, Measure.restrict_restrict hAm] at hkey
  rw [lintegral_withDensity_eq_lintegral_mul _ hρmeas
    (hind.mono hm le_rfl)] at hkey
  rw [hkey]
  rw [← lintegral_indicator hAm]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ A
  · simp [Set.indicator_of_mem hω, hρ, mul_comm]
  · simp [Set.indicator_of_notMem hω]

/-! ## The signed weighted identity -/

/-- **The signed weighted survivor identity.**  For a history-measurable
threshold and a bounded history-measurable real weight, the mean of the weight
over the part of a history event on which the segment survives the threshold is
the mean of the survivor-weighted weight over the whole event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_lt_holdingTime_weighted
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (k : ℕ) (u : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (w : Ω → ℝ)
    (hw : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] w)
    (C : ℝ) (hwC : ∀ ω, |w ω| ≤ C) :
    ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω}, w ω ∂P =
      ∫ ω in A, w ω *
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
          (u ω)) ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  set Sset : Set Ω := {ω | u ω < ξ.holdingTime k ω} with hSset
  set sur : Ω → ℝ := fun ω =>
    (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u ω)
    with hsur
  have hm : (F k : MeasurableSpace Ω) ≤ mΩ := F.le k
  have hAm : MeasurableSet A := hm _ hA
  have hSm : MeasurableSet Sset :=
    measurableSet_lt (hu.mono hm le_rfl) (hξ.holdingTime k)
  have hHmeas : Measurable fun ω =>
      (davisPreJumpHistory S hflow ξ initial k ω).currentState :=
    (DavisPreJumpHistory.measurable_currentState k).comp
      (hξ.preJumpHistory S hflow hf hr initial k)
  have hsurmeas : Measurable sur :=
    hsurv.comp (hHmeas.prodMk (hu.mono hm le_rfl))
  have hsurIoc : ∀ ω, sur ω ∈ Set.Ioc (0 : ℝ) 1 := fun ω =>
    DavisPreJumpHistory.nextSurvivor_mem_Ioc S hflow _ _
  have hwm : Measurable w := hw.mono hm le_rfl
  -- reduce to a common domain of integration
  have hleft : ∫ ω in A ∩ Sset, w ω ∂P = ∫ ω in A, Sset.indicator w ω ∂P :=
    (MeasureTheory.setIntegral_indicator hSm).symm
  rw [hleft]
  -- the pointwise identities for the positive and the negative parts
  have hpt : ∀ (f : Ω → ℝ), (∀ ω, ENNReal.ofReal (Sset.indicator f ω) =
      Sset.indicator (fun ω => ENNReal.ofReal (f ω)) ω) := by
    intro f ω
    by_cases hω : ω ∈ Sset
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hmul : ∀ (f : Ω → ℝ) (ω : Ω),
      ENNReal.ofReal (f ω * sur ω) =
        ENNReal.ofReal (f ω) * ENNReal.ofReal (sur ω) := by
    intro f ω
    rcases le_or_gt 0 (f ω) with hpos | hneg
    · exact ENNReal.ofReal_mul hpos
    · have h1 : f ω * sur ω ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (hsurIoc ω).1.le
      rw [ENNReal.ofReal_eq_zero.2 h1, ENNReal.ofReal_eq_zero.2 hneg.le, zero_mul]
  have hpart : ∀ (f : Ω → ℝ), Measurable[F k] f →
      ∫⁻ ω in A, ENNReal.ofReal (Sset.indicator f ω) ∂P =
        ∫⁻ ω in A, ENNReal.ofReal (f ω * sur ω) ∂P := by
    intro f hfF
    have h1 : ∫⁻ ω in A, ENNReal.ofReal (Sset.indicator f ω) ∂P =
        ∫⁻ ω in A ∩ Sset, ENNReal.ofReal (f ω) ∂P := by
      rw [show (fun ω => ENNReal.ofReal (Sset.indicator f ω)) =
        Sset.indicator (fun ω => ENNReal.ofReal (f ω)) from funext (hpt f)]
      rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]
    rw [h1, hlaw.lintegral_lt_holdingTime_weighted hcont hsurv k u hu A hA
      (fun ω => ENNReal.ofReal (f ω)) hfF.ennreal_ofReal]
    exact lintegral_congr fun ω => (hmul f ω).symm
  -- integrability of both sides
  have hbound : ∀ ω, |Sset.indicator w ω| ≤ C := by
    intro ω
    by_cases hω : ω ∈ Sset
    · rw [Set.indicator_of_mem hω]; exact hwC ω
    · rw [Set.indicator_of_notMem hω, abs_zero]
      exact le_trans (abs_nonneg (w ω)) (hwC ω)
  have hintL : IntegrableOn (fun ω => Sset.indicator w ω) A P := by
    refine Integrable.integrableOn ?_
    refine Integrable.mono' (integrable_const C) (hwm.indicator hSm).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hbound ω
  have hintR : IntegrableOn (fun ω => w ω * sur ω) A P := by
    refine Integrable.integrableOn ?_
    refine Integrable.mono' (integrable_const C) (hwm.mul hsurmeas).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hsurIoc ω).1]
    calc |w ω| * sur ω ≤ |w ω| * 1 := by
          exact mul_le_mul_of_nonneg_left (hsurIoc ω).2 (abs_nonneg _)
      _ = |w ω| := mul_one _
      _ ≤ C := hwC ω
  refine integral_eq_of_lintegral_pos_neg_eq _ _ A hintL hintR ?_ ?_
  · exact hpart w hw
  · have hneg := hpart (fun ω => -w ω) hw.neg
    have h1 : (fun ω => -(Sset.indicator w ω)) = Sset.indicator (fun ω => -w ω) := by
      funext ω
      by_cases hω : ω ∈ Sset
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    calc ∫⁻ ω in A, ENNReal.ofReal (-(Sset.indicator w ω)) ∂P
        = ∫⁻ ω in A, ENNReal.ofReal (Sset.indicator (fun ω => -w ω) ω) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [show -(Sset.indicator w ω) = Sset.indicator (fun ω => -w ω) ω from
            congrFun h1 ω]
      _ = ∫⁻ ω in A, ENNReal.ofReal (-w ω * sur ω) ∂P := hneg
      _ = ∫⁻ ω in A, ENNReal.ofReal (-(w ω * sur ω)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [neg_mul]

/-! ## Monotonicity of the survivor factor -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The integrated hazard is nondecreasing in the elapsed duration. -/
theorem davisIntegratedHazard_mono
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow) (z : DavisState Q n)
    {u v : ℝ≥0} (huv : u ≤ v) :
    davisIntegratedHazard S hflow z u ≤ davisIntegratedHazard S hflow z v := by
  unfold davisIntegratedHazard
  refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
  · exact (hcont z).integrableOn_Icc
  · filter_upwards with s using totalIntensity_nonneg _ _
  · exact Filter.Eventually.of_forall
      (Set.Icc_subset_Icc le_rfl (by exact_mod_cast huv))

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The survivor factor is nonincreasing in the elapsed duration. -/
theorem davisSegmentSurvivor_antitone
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow) (z : DavisState Q n)
    {u v : ℝ≥0} (huv : u ≤ v) :
    davisSegmentSurvivor S hflow z v ≤ davisSegmentSurvivor S hflow z u := by
  unfold davisSegmentSurvivor
  exact Real.exp_le_exp.2 (by linarith [davisIntegratedHazard_mono S hflow hcont z huv])

end SHS
