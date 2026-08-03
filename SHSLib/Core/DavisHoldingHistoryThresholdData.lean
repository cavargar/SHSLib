import SHSLib.Core.DavisConditionalHoldingHistoryStep

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Packaged history-localized holding-time approximations

Occupation densities depend on both elapsed time and the finite pre-jump
history.  Consequently their simple approximations require history events as
well as deterministic time thresholds.  This module packages increasing
approximations of that form and passes their finite conditional identities to
the limit.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Matching increasing representations by nonnegative threshold steps whose
coefficients are localized to pre-jump-history events. -/
structure DavisHoldingHistoryThresholdApproximationData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (k : ℕ) (f g : Ω → ℝ≥0∞) where
  support : ℕ → Finset ℕ
  event : ℕ → ℕ → Set Ω
  threshold : ℕ → ℕ → ℝ≥0
  weight : ℕ → ℕ → ℝ≥0∞
  event_measurable : ∀ j i, i ∈ support j →
    MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] (event j i)
  survivorTerm_measurable : ∀ j i, i ∈ support j → Measurable (fun ω =>
    ENNReal.ofReal ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor
      S hflow (threshold j i)))
  sampled_monotone : Monotone (fun j =>
    davisHoldingHistoryThresholdStep ξ k (support j) (event j)
      (threshold j) (weight j))
  survivor_monotone : Monotone (fun j =>
    davisHoldingHistoryThresholdSurvivorStep S hflow ξ initial k
      (support j) (event j) (threshold j) (weight j))
  sampled_representation : ∀ ω, f ω = ⨆ j,
    davisHoldingHistoryThresholdStep ξ k (support j) (event j)
      (threshold j) (weight j) ω
  survivor_representation : ∀ ω, g ω = ⨆ j,
    davisHoldingHistoryThresholdSurvivorStep S hflow ξ initial k
      (support j) (event j) (threshold j) (weight j) ω

/-- Packaged history-localized approximation data yields the corresponding
conditional `lintegral` identity on every pre-jump-history event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_of_historyThresholdData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (f g : Ω → ℝ≥0∞)
    (hdata : DavisHoldingHistoryThresholdApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr)
      hξ initial k f g)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    ∫⁻ ω in A, f ω ∂P = ∫⁻ ω in A, g ω ∂P := by
  simp only [hdata.sampled_representation, hdata.survivor_representation]
  have h_event_meas : ∀ j i, i ∈ hdata.support j → MeasurableSet (hdata.event j i) := by
    intro j i hi
    obtain ⟨s', hs'_meas, hs'_eq⟩ := hdata.event_measurable j i hi
    rw [← hs'_eq]
    exact hξ.preJumpHistory S hflow hf hr initial k hs'_meas
  have hleftMeas : ∀ j, Measurable (fun ω => davisHoldingHistoryThresholdStep ξ k (hdata.support j) (hdata.event j) (hdata.threshold j) (hdata.weight j) ω) := by
    intro j
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.const_mul
    apply Measurable.indicator
    · exact measurable_const
    · exact MeasurableSet.inter (h_event_meas j i hi) (hξ.holdingTime k measurableSet_Ioi)
  have hrightMeas : ∀ j, Measurable (fun ω => davisHoldingHistoryThresholdSurvivorStep S hflow ξ initial k (hdata.support j) (hdata.event j) (hdata.threshold j) (hdata.weight j) ω) := by
    intro j
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.const_mul
    exact Measurable.indicator (hdata.survivorTerm_measurable j i hi) (h_event_meas j i hi)
  have heq : ∀ j, ∫⁻ ω in A, davisHoldingHistoryThresholdStep ξ k (hdata.support j) (hdata.event j) (hdata.threshold j) (hdata.weight j) ω ∂P =
      ∫⁻ ω in A, davisHoldingHistoryThresholdSurvivorStep S hflow ξ initial k (hdata.support j) (hdata.event j) (hdata.threshold j) (hdata.weight j) ω ∂P := by
    intro j
    apply hlaw.lintegral_historyThresholdStep k (hdata.support j) (hdata.event j) (hdata.threshold j) (hdata.weight j) A hA
    · exact fun i hi => hdata.event_measurable j i hi
    · exact fun i hi => hdata.survivorTerm_measurable j i hi
  rw [MeasureTheory.lintegral_iSup hleftMeas hdata.sampled_monotone,
      MeasureTheory.lintegral_iSup hrightMeas hdata.survivor_monotone]
  simp_rw [heq]

end SHS
