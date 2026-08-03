import SHSLib.Core.DavisResetOccupationConditionalHistory
import SHSLib.Core.DavisResetOccupationRegular

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Integrability of capped reset occupation

This file separates the two estimates needed by the conditional occupation
identity.  The sampled raw occupation is dominated by accumulated total hazard
on the occupied interval.  The survivor-weighted expected compensator is
uniformly bounded for bounded test functions.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Joint regularity of the stopped compensator makes its history-dependent,
capped sampled version measurable. -/
theorem DavisResetOccupationRegular.measurable_cappedSampledCompensator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k : ℕ) (u : ℝ≥0) :
    Measurable (davisCappedSampledResetOccupationCompensator
      S hflow g ξ initial k u) := by
  unfold davisCappedSampledResetOccupationCompensator
  have hp : Measurable (fun ω =>
      ((davisPreJumpHistory S hflow ξ initial k ω).currentState,
        min (ξ.holdingTime k ω) u)) :=
    ((DavisPreJumpHistory.measurable_currentState k).comp
      (hξ.preJumpHistory S hflow hf hr initial k)).prodMk
        ((hξ.holdingTime k).min measurable_const)
  simpa only [Function.comp_apply] using
    hreg.stoppedCompensator_measurable.comp hp

/-- The capped sampled raw occupation is bounded by accumulated total
intensity along the actually occupied part of the segment. -/
theorem abs_davisCappedSampledResetOccupationCompensator_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) (u : ℝ≥0) (ω : Ω) :
    |davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k u ω| ≤
      2 * C * ∫ s in Set.Icc (0 : ℝ)
          ((min (ξ.holdingTime k ω) u : ℝ≥0) : ℝ),
        S.totalIntensity (davisFlow S hflow s.toNNReal
          (davisPreJumpHistory S hflow ξ initial k ω).currentState) := by
  unfold davisCappedSampledResetOccupationCompensator
  exact abs_davisSegmentResetOccupationCompensator_le_integral_intensity
    S hflow g C hg
    (davisPreJumpHistory S hflow ξ initial k ω).currentState
    (min (ξ.holdingTime k ω) u)
    (hreg.density_integrableOn _ _)
    ((hcont _).integrableOn_Icc)

/-- An integrable accumulated-hazard envelope yields integrability of the
capped sampled raw occupation. -/
theorem integrable_cappedSampledResetOccupationCompensator
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (k : ℕ) (u : ℝ≥0)
    (henvelope : Integrable (fun ω =>
      2 * C * ∫ s in Set.Icc (0 : ℝ)
          ((min (ξ.holdingTime k ω) u : ℝ≥0) : ℝ),
        S.totalIntensity (davisFlow S hflow s.toNNReal
          (davisPreJumpHistory S hflow ξ initial k ω).currentState)) P) :
    Integrable (davisCappedSampledResetOccupationCompensator
      S hflow g ξ initial k u) P := by
  apply MeasureTheory.Integrable.mono' henvelope
    (hreg.measurable_cappedSampledCompensator (hf := hf) (hr := hr)
      hξ initial k u).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_davisCappedSampledResetOccupationCompensator_le
    S hflow hcont g C hg hreg ξ initial k u ω

/-- For a bounded test function, the survivor-weighted expected one-segment
compensator is integrable on a finite measure space once its measurability and
the deterministic density integrability needed by the bound are available. -/
theorem integrable_history_expectedResetCompensator
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ y, |g y| ≤ C)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (state : Ω → DavisState Q n) (u : ℝ≥0)
    (hmeas : AEStronglyMeasurable (fun ω =>
      davisSegmentExpectedResetCompensator S hflow g (state ω) u) P)
    (hreset : ∀ ω, IntegrableOn
      (davisSegmentExpectedResetDensity S hflow g (state ω))
      (Set.Icc (0 : ℝ) (u : ℝ))) :
    Integrable (fun ω =>
      davisSegmentExpectedResetCompensator S hflow g (state ω) u) P := by
  -- First establish integrability of hazard density from continuity
  have hhazard : ∀ ω, IntegrableOn
      (davisSegmentHazardDensity S hflow (state ω))
      (Set.Icc (0 : ℝ) (u : ℝ)) := by
    intro ω
    -- Hazard density is continuous on [0, u], hence integrable
    have hcont_lam : Continuous (fun s : ℝ => S.totalIntensity (davisFlow S hflow s.toNNReal (state ω))) := hcont (state ω)
    have hcont_survivor : ContinuousOn (fun s => davisSegmentSurvivor S hflow (state ω) s.toNNReal) (Set.Icc 0 (u : ℝ)) := by
      unfold davisSegmentSurvivor
      apply ContinuousOn.rexp
      apply ContinuousOn.neg
      unfold davisIntegratedHazard
      -- On [0, u], s.toNNReal = s, so we can simplify
      have h_eq : ∀ s ∈ Set.Icc 0 (u : ℝ), davisIntegratedHazard S hflow (state ω) s.toNNReal =
                           ∫ x in (0 : ℝ)..s, S.totalIntensity (davisFlow S hflow x.toNNReal (state ω)) := by
        intro s hs
        simp_rw [davisIntegratedHazard, integral_Icc_eq_integral_Ioc]
        rw [intervalIntegral.integral_of_le hs.1]
        have h : (0 : ℝ) ≤ s.toNNReal := NNReal.coe_nonneg s.toNNReal
        rw [Real.toNNReal_of_nonneg hs.1] at h ⊢
        rfl
      apply ContinuousOn.congr _ h_eq
      have hint : IntegrableOn (fun s => S.totalIntensity (davisFlow S hflow s.toNNReal (state ω))) (Set.Icc 0 (u : ℝ)) :=
        hcont_lam.integrableOn_Icc
      refine intervalIntegral.continuousOn_primitive (f := fun s => S.totalIntensity (davisFlow S hflow s.toNNReal (state ω))) hint |> fun h => h.congr ?_
      intro x hx
      simp only [intervalIntegral.integral_of_le hx.1]
    have hcont_on : ContinuousOn (fun s => davisSegmentHazardDensity S hflow (state ω) s) (Set.Icc 0 (u : ℝ)) := by
      unfold davisSegmentHazardDensity
      apply ContinuousOn.mul hcont_lam.continuousOn hcont_survivor
    exact hcont_on.integrableOn_Icc
  -- Use the bound |compensator| ≤ 2C and finite measure to get integrability
  refine MeasureTheory.Integrable.mono' (μ := P) (MeasureTheory.integrable_const (2 * C)) hmeas ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_davisSegmentExpectedResetCompensator_le_two_mul S hflow hcont g C hC hg (state ω) u (hreset ω) (hhazard ω)

end SHS
