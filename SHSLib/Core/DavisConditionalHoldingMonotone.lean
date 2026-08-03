import SHSLib.Core.DavisConditionalHoldingIntegral

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Monotone limits of conditional holding-time threshold tests

This module extends the finite threshold-step integration rule to monotone
limits.  The approximation is kept explicit: a sequence of finite nonnegative
threshold-step tests is paired with the sequence obtained by replacing every
holding-time survival indicator by its history-dependent survivor factor.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The history-side partner of a finite holding-time threshold-step test. -/
def davisHoldingThresholdSurvivorStep
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) {ι : Type*} (s : Finset ι) (u : ι → ℝ≥0)
    (w : ι → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∑ i ∈ s, w i * ENNReal.ofReal
    ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u i))

/-- A finite threshold-step test and its survivor-side partner have the same
conditional nonnegative integral on every pre-jump-history event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_thresholdStep_survivorStep
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) {ι : Type*} (s : Finset ι) (u : ι → ℝ≥0)
    (w : ι → ℝ≥0∞) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hmeas : ∀ i ∈ s, Measurable (fun ω => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u i)))) :
    ∫⁻ ω in A, davisHoldingThresholdStep ξ k s u w ω ∂P =
      ∫⁻ ω in A,
        davisHoldingThresholdSurvivorStep S hflow ξ initial k s u w ω ∂P := by
  rw [hlaw.lintegral_thresholdStep k s u w A hA]
  simp only [davisHoldingThresholdSurvivorStep]
  rw [MeasureTheory.lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.lintegral_const_mul _ (hmeas i hi)]
  · intro i hi
    exact Measurable.const_mul (hmeas i hi) (w i)

/-- Conditional threshold-step integration is stable under monotone limits.
The hypotheses explicitly record measurability and monotonicity of the two
approximating sequences; this avoids claiming an unrestricted monotone-class
theorem without the required history-side regularity. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_iSup_thresholdStep
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) {ι : Type*} (s : ℕ → Finset ι)
    (u : ℕ → ι → ℝ≥0) (w : ℕ → ι → ℝ≥0∞) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hrightTermMeas : ∀ j i, i ∈ s j → Measurable (fun ω => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u j i))))
    (hleftMono : Monotone (fun j => davisHoldingThresholdStep ξ k (s j) (u j) (w j)))
    (hrightMono : Monotone (fun j => davisHoldingThresholdSurvivorStep
      S hflow ξ initial k (s j) (u j) (w j))) :
    ∫⁻ ω in A, ⨆ j, davisHoldingThresholdStep ξ k (s j) (u j) (w j) ω ∂P =
      ∫⁻ ω in A, ⨆ j, davisHoldingThresholdSurvivorStep
        S hflow ξ initial k (s j) (u j) (w j) ω ∂P := by
  have heq : ∀ j, ∫⁻ ω in A, davisHoldingThresholdStep ξ k (s j) (u j) (w j) ω ∂P =
      ∫⁻ ω in A, davisHoldingThresholdSurvivorStep S hflow ξ initial k (s j) (u j) (w j) ω ∂P := by
    intro j
    apply hlaw.lintegral_thresholdStep_survivorStep k (s j) (u j) (w j) A
    · exact hA
    · exact fun i hi => hrightTermMeas j i hi
  have hleftMeas : ∀ j, Measurable (fun ω => davisHoldingThresholdStep ξ k (s j) (u j) (w j) ω) := by
    intro j
    unfold davisHoldingThresholdStep
    apply Finset.measurable_sum
    intro i _
    apply Measurable.const_mul
    apply Measurable.indicator
    · exact measurable_const
    · exact measurableSet_lt measurable_const (hξ.holdingTime k)
  have hrightMeas : ∀ j, Measurable (fun ω => davisHoldingThresholdSurvivorStep S hflow ξ initial k (s j) (u j) (w j) ω) := by
    intro j
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.const_mul
    exact hrightTermMeas j i hi
  rw [MeasureTheory.lintegral_iSup hleftMeas hleftMono, MeasureTheory.lintegral_iSup hrightMeas hrightMono]
  simp_rw [heq]

end SHS
