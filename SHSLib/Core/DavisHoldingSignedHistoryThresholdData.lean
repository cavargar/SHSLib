import SHSLib.Core.DavisHoldingHistoryThresholdData

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Signed history-localized holding-time approximation data

This is the signed assembly layer for history-dependent occupation
functionals.  Positive and negative variation are represented separately by
increasing history-localized threshold steps and then recombined as a real
integral identity.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Matching history-localized threshold approximations for the positive and
negative parts of two real-valued functionals. -/
structure DavisHoldingSignedHistoryThresholdApproximationData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (k : ℕ) (f g : Ω → ℝ) where
  positive : DavisHoldingHistoryThresholdApproximationData
    (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
    (fun ω => ENNReal.ofReal (f ω)) (fun ω => ENNReal.ofReal (g ω))
  negative : DavisHoldingHistoryThresholdApproximationData
    (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
    (fun ω => ENNReal.ofReal (-f ω)) (fun ω => ENNReal.ofReal (-g ω))

/-- Signed history-localized threshold data implies equality of real integrals
on every pre-jump-history event, under the necessary integrability hypotheses. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_of_signedHistoryThresholdData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (f g : Ω → ℝ)
    (hdata : DavisHoldingSignedHistoryThresholdApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr)
      hξ initial k f g)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hf_int : IntegrableOn f A P) (hg_int : IntegrableOn g A P) :
    ∫ ω in A, f ω ∂P = ∫ ω in A, g ω ∂P := by
  have hpos := hlaw.lintegral_of_historyThresholdData k
    (fun ω => ENNReal.ofReal (f ω)) (fun ω => ENNReal.ofReal (g ω)) hdata.positive A hA
  have hneg := hlaw.lintegral_of_historyThresholdData k
    (fun ω => ENNReal.ofReal (-f ω)) (fun ω => ENNReal.ofReal (-g ω)) hdata.negative A hA
  rw [MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf_int,
    MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg_int,
    hpos, hneg]

end SHS
