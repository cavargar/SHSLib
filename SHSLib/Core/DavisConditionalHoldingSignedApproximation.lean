import SHSLib.Core.DavisConditionalHoldingSignedStep

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Signed approximation limits for Davis holding times

This module passes from the nonnegative threshold-approximation interface to
real-valued conditional integral identities.  Positive and negative parts are
approximated separately; their two `lintegral` identities are then subtracted.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Two matching identities for the positive and negative parts of integrable
real functions imply equality of their real integrals. -/
theorem integral_eq_of_lintegral_pos_neg_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f g : Ω → ℝ) (A : Set Ω)
    (hf : IntegrableOn f A P) (hg : IntegrableOn g A P)
    (hpos : ∫⁻ ω in A, ENNReal.ofReal (f ω) ∂P =
      ∫⁻ ω in A, ENNReal.ofReal (g ω) ∂P)
    (hneg : ∫⁻ ω in A, ENNReal.ofReal (-f ω) ∂P =
      ∫⁻ ω in A, ENNReal.ofReal (-g ω) ∂P) :
    ∫ ω in A, f ω ∂P = ∫ ω in A, g ω ∂P := by
  rw [MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg,
    hpos, hneg]

/-- Conditional real integration from separate matching monotone threshold-step
representations of the positive and negative parts.

All measurability, monotonicity, representation, and integrability assumptions
are explicit.  Thus this theorem can be applied to an occupation functional as
soon as concrete simple approximations and an integrable envelope have been
constructed, without adding hidden regularity assumptions to the basic SHS
structure. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_of_signedThresholdApproximation
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) {ιp ιn : Type*}
    (sp : ℕ → Finset ιp) (up : ℕ → ιp → ℝ≥0)
    (wp : ℕ → ιp → ℝ≥0∞)
    (sn : ℕ → Finset ιn) (un : ℕ → ιn → ℝ≥0)
    (wn : ℕ → ιn → ℝ≥0∞)
    (f g : Ω → ℝ) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hfpTermMeas : ∀ j i, i ∈ sp j → Measurable (fun ω => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (up j i))))
    (hfnTermMeas : ∀ j i, i ∈ sn j → Measurable (fun ω => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (un j i))))
    (hfpMono : Monotone (fun j => davisHoldingThresholdStep ξ k (sp j) (up j) (wp j)))
    (hgpMono : Monotone (fun j => davisHoldingThresholdSurvivorStep
      S hflow ξ initial k (sp j) (up j) (wp j)))
    (hfnMono : Monotone (fun j => davisHoldingThresholdStep ξ k (sn j) (un j) (wn j)))
    (hgnMono : Monotone (fun j => davisHoldingThresholdSurvivorStep
      S hflow ξ initial k (sn j) (un j) (wn j)))
    (hfp_repr : ∀ ω, ENNReal.ofReal (f ω) =
      ⨆ j, davisHoldingThresholdStep ξ k (sp j) (up j) (wp j) ω)
    (hgp_repr : ∀ ω, ENNReal.ofReal (g ω) =
      ⨆ j, davisHoldingThresholdSurvivorStep S hflow ξ initial k
        (sp j) (up j) (wp j) ω)
    (hfn_repr : ∀ ω, ENNReal.ofReal (-f ω) =
      ⨆ j, davisHoldingThresholdStep ξ k (sn j) (un j) (wn j) ω)
    (hgn_repr : ∀ ω, ENNReal.ofReal (-g ω) =
      ⨆ j, davisHoldingThresholdSurvivorStep S hflow ξ initial k
        (sn j) (un j) (wn j) ω)
    (hf_int : IntegrableOn f A P) (hg_int : IntegrableOn g A P) :
    ∫ ω in A, f ω ∂P = ∫ ω in A, g ω ∂P := by
  apply integral_eq_of_lintegral_pos_neg_eq f g A hf_int hg_int
  · exact hlaw.lintegral_of_thresholdApproximation k sp up wp
      (fun ω => ENNReal.ofReal (f ω)) (fun ω => ENNReal.ofReal (g ω)) A hA
      hfpTermMeas hfpMono hgpMono hfp_repr hgp_repr
  · exact hlaw.lintegral_of_thresholdApproximation k sn un wn
      (fun ω => ENNReal.ofReal (-f ω)) (fun ω => ENNReal.ofReal (-g ω)) A hA
      hfnTermMeas hfnMono hgnMono hfn_repr hgn_repr

end SHS
