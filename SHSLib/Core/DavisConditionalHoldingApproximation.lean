import SHSLib.Core.DavisConditionalHoldingMonotone

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Reusable threshold-approximation interface for holding times

This module packages the monotone threshold-step result as an interface for a
pair of nonnegative functions.  A caller supplies pointwise increasing
threshold-step representations of a holding-time functional and its
history-side survivor transform; the conditional integral identity then
follows without repeating the monotone-convergence argument.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Conditional holding-time integration for any pair represented pointwise by
matching monotone threshold-step approximations. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_of_thresholdApproximation
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) {ι : Type*} (s : ℕ → Finset ι)
    (u : ℕ → ι → ℝ≥0) (w : ℕ → ι → ℝ≥0∞)
    (f g : Ω → ℝ≥0∞) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hrightTermMeas : ∀ j i, i ∈ s j → Measurable (fun ω => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u j i))))
    (hleftMono : Monotone (fun j => davisHoldingThresholdStep ξ k (s j) (u j) (w j)))
    (hrightMono : Monotone (fun j => davisHoldingThresholdSurvivorStep
      S hflow ξ initial k (s j) (u j) (w j)))
    (hf_repr : ∀ ω, f ω = ⨆ j, davisHoldingThresholdStep ξ k (s j) (u j) (w j) ω)
    (hg_repr : ∀ ω, g ω = ⨆ j, davisHoldingThresholdSurvivorStep
      S hflow ξ initial k (s j) (u j) (w j) ω) :
    ∫⁻ ω in A, f ω ∂P = ∫⁻ ω in A, g ω ∂P := by
  simp_rw [hf_repr, hg_repr]
  exact hlaw.lintegral_iSup_thresholdStep k s u w A hA hrightTermMeas hleftMono hrightMono

end SHS
