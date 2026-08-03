import SHSLib.Core.DavisConditionalHoldingApproximation

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Signed threshold-step integration for Davis holding times

The nonnegative threshold-step interface is convenient for monotone convergence.
For a real-valued compensator one ultimately subtracts positive and negative
parts.  This module provides the corresponding finite signed-step identity,
which is the algebraic endpoint needed after the two nonnegative limits have
been established.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A finite real-valued threshold-step test of the `k`-th holding time. -/
def davisHoldingSignedThresholdStep {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (k : ℕ) {ι : Type*} (s : Finset ι) (u : ι → ℝ≥0)
    (w : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ s, w i * ({ω' | u i < ξ.holdingTime k ω'}.indicator (fun _ => (1 : ℝ))) ω

/-- The survivor-side partner of a finite signed threshold-step test. -/
def davisHoldingSignedThresholdSurvivorStep
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) {ι : Type*} (s : Finset ι) (u : ι → ℝ≥0)
    (w : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ s, w i *
    (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u i)

/-- A single real weighted survival indicator has the corresponding
survivor-weighted integral on every pre-jump-history event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_weighted_survival_indicator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (u : ℝ≥0) (w : ℝ) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hsurv : Measurable (fun ω =>
      (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u)) :
    ∫ ω in A, w * ({ω' | u < ξ.holdingTime k ω'}.indicator
        (fun _ => (1 : ℝ))) ω ∂P =
      ∫ ω in A, w *
        (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u ∂P := by
  -- Factor out the real weight from both sides.
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  congr 1
  -- The real integral of the indicator is the real-valued event measure.
  have hsurvSet : MeasurableSet {ω : Ω | u < ξ.holdingTime k ω} :=
    measurableSet_lt measurable_const (hξ.holdingTime k)
  have lhs_eq : ∫ a in A, ({ω' | u < ξ.holdingTime k ω'}.indicator fun _ => (1 : ℝ)) a ∂P =
      (P (A ∩ {ω | u < ξ.holdingTime k ω})).toReal := by
    have h1 : ∫ a in A, ({ω' | u < ξ.holdingTime k ω'}.indicator fun _ => (1 : ℝ)) a ∂P =
        ∫ a in A ∩ {ω | u < ξ.holdingTime k ω}, (1 : ℝ) ∂P := by
      rw [MeasureTheory.setIntegral_indicator hsurvSet]
    simp [h1, Measure.real]
  -- Replace the event measure using the conditional survivor identity.
  have surv_id := hlaw.survivor_identity k u A hA
  rw [surv_id] at lhs_eq
  rw [lhs_eq]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · filter_upwards with x
    exact (DavisPreJumpHistory.nextSurvivor_mem_Ioc S hflow (S.davisPreJumpHistory hflow ξ initial k x) u).1.le
  · exact hsurv.aestronglyMeasurable.restrict

/-- Finite signed threshold-step tests integrate by replacing every holding-time
survival indicator with the history-dependent survivor factor. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_signedThresholdStep
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) {ι : Type*} (s : Finset ι) (u : ι → ℝ≥0)
    (w : ι → ℝ) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hP : IsFiniteMeasure P)
    (hsurv : ∀ i ∈ s, Measurable (fun ω =>
      (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u i))) :
    ∫ ω in A, davisHoldingSignedThresholdStep ξ k s u w ω ∂P =
      ∫ ω in A,
        davisHoldingSignedThresholdSurvivorStep S hflow ξ initial k s u w ω ∂P := by
  unfold davisHoldingSignedThresholdStep davisHoldingSignedThresholdSurvivorStep
  rw [MeasureTheory.integral_finset_sum, MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact hlaw.integral_weighted_survival_indicator k (u i) (w i) A hA (hsurv i hi)
  · intro i hi
    apply MeasureTheory.Integrable.const_mul
    have hbdd : ∀ ω, ‖(davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u i)‖ ≤ 1 := by
      intro ω
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(DavisPreJumpHistory.nextSurvivor_mem_Ioc S hflow (davisPreJumpHistory S hflow ξ initial k ω) (u i)).1.le],
        (DavisPreJumpHistory.nextSurvivor_mem_Ioc S hflow (davisPreJumpHistory S hflow ξ initial k ω) (u i)).2⟩
    exact MeasureTheory.Integrable.of_bound (hsurv i hi).aestronglyMeasurable 1 (Filter.Eventually.of_forall hbdd)
  · intro i hi
    apply MeasureTheory.Integrable.const_mul
    have hmeas : Measurable ({ω' | u i < ξ.holdingTime k ω'}.indicator fun x => (1 : ℝ)) := by
      apply Measurable.indicator
      · exact measurable_const
      · exact measurableSet_lt measurable_const (hξ.holdingTime k)
    have hbdd : ∀ ω, ‖({ω' | u i < ξ.holdingTime k ω'}.indicator fun x => (1 : ℝ)) ω‖ ≤ 1 := by
      intro ω
      simp [Set.indicator, Real.norm_eq_abs]
      split_ifs <;> simp
    exact MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbdd)

end SHS
