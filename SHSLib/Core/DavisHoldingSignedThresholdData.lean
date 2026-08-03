import SHSLib.Core.DavisHoldingThresholdData

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Packaged signed holding-time threshold approximation data

Positive and negative variation approximations are bundled here and converted
into a real conditional integral identity.  This is the assembly layer needed
before specializing to reset occupation compensators.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Matching threshold representations for the positive and negative parts of
real-valued sampled and survivor-side functionals. -/
structure DavisHoldingSignedThresholdApproximationData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (k : ℕ) (f g : Ω → ℝ) where
  positive : DavisHoldingThresholdApproximationData
    (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
    (fun ω => ENNReal.ofReal (f ω)) (fun ω => ENNReal.ofReal (g ω))
  negative : DavisHoldingThresholdApproximationData
    (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
    (fun ω => ENNReal.ofReal (-f ω)) (fun ω => ENNReal.ofReal (-g ω))

/-- Packaged signed threshold data implies equality of the corresponding real
integrals on every pre-jump-history event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_of_signedThresholdData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (f g : Ω → ℝ)
    (hdata : DavisHoldingSignedThresholdApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr)
      hξ initial k f g)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hf_int : IntegrableOn f A P) (hg_int : IntegrableOn g A P) :
    ∫ ω in A, f ω ∂P = ∫ ω in A, g ω ∂P := by
  have hpos := hlaw.lintegral_of_thresholdData k
    (fun ω => ENNReal.ofReal (f ω)) (fun ω => ENNReal.ofReal (g ω)) hdata.positive A hA
  have hneg := hlaw.lintegral_of_thresholdData k
    (fun ω => ENNReal.ofReal (-f ω)) (fun ω => ENNReal.ofReal (-g ω)) hdata.negative A hA
  rw [MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf_int,
    MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg_int,
    hpos, hneg]

end SHS
