import SHSLib.Core.DavisChannelLaw

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-! # One-step holding-time and reset-channel machinery

This module combines the conditional holding-time and channel interfaces for a
single jump.  It also records the finite-channel algebra that turns normalized
channel probabilities into the reset part of the Davis compensator.  The
state-valued reset kernel is treated carefully: if two channels have the same
reset image, the mass of that image is the sum of both channel weights.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The finite-history information is contained in the information available
just before sampling the next channel. -/
theorem DavisJumpNoise.preJumpHistorySpace_le_preChannel
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n) (k : ℕ) :
    ξ.preJumpHistorySpace S hflow initial k ≤
      ξ.preChannelSpace S hflow initial k := by
  rw [DavisJumpNoise.preJumpHistorySpace, DavisJumpNoise.preChannelSpace]
  set f : Ω → DavisPreJumpHistory Q n m k × ℝ≥0 := fun ω =>
    (davisPreJumpHistory S hflow ξ initial k ω, ξ.holdingTime k ω)
  show MeasurableSpace.comap (fun x => (f x).1) inferInstance ≤
    MeasurableSpace.comap f inferInstance
  simp only [← Function.comp_def]
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le

/-- The event that the next holding time exceeds `u` is measurable once that
holding time has been revealed. -/
theorem DavisJumpNoise.holdingTime_gt_measurable_preChannel
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) (u : ℝ≥0) :
    MeasurableSet[ξ.preChannelSpace S hflow initial k]
      {ω | u < ξ.holdingTime k ω} := by
  have hmeas := DavisJumpNoise.holdingTime_measurable_preChannel S hflow ξ initial k
  exact hmeas measurableSet_Ioi

/-- Joint one-step sampling assumptions: the holding time has the integrated
hazard law given the finite history, and after revealing that holding time the
channel has the normalized intensity law. -/
structure DavisJumpNoise.ConditionalOneStepLaw
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) : Prop where
  holding : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial
  channel : ξ.ConditionalChannelLaw S hflow P initial

/-- A conditional channel law gives the joint event identity for survival past
`u` and selection of channel `ℓ`, tested against every finite-history event. -/
theorem DavisJumpNoise.ConditionalChannelLaw.channel_after_survival_identity
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (u : ℝ≥0) (ℓ : Fin m) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    P (A ∩ {ω | u < ξ.holdingTime k ω} ∩ {ω | ξ.channel k ω = ℓ}) =
      ∫⁻ ω in A ∩ {ω | u < ξ.holdingTime k ω}, ENNReal.ofReal
        (davisChannelProbability S
          ((davisPreJumpHistory S hflow ξ initial k ω).stateBeforeNextJump
            S hflow (ξ.holdingTime k ω)) ℓ) ∂P := by
  have hA' : MeasurableSet[ξ.preChannelSpace S hflow initial k] A :=
    (ξ.preJumpHistorySpace_le_preChannel S hflow initial k) A hA
  exact hlaw.channel_identity k ℓ (A ∩ {ω | u < ξ.holdingTime k ω})
    (hA'.inter
      (ξ.holdingTime_gt_measurable_preChannel S hflow initial k u))

/-- The normalized expected increment of a test function across one reset. -/
def davisExpectedResetIncrement (S : SHS Q n m)
    (g : DavisState Q n → ℝ) (z : DavisState Q n) : ℝ :=
  ∑ ℓ : Fin m, davisChannelProbability S z ℓ *
    (g (S.resetDavisState ℓ z) - g z)

/-- Multiplying the normalized one-reset expectation by total intensity gives
exactly the finite reset compensator, including at states of zero intensity. -/
theorem totalIntensity_mul_davisExpectedResetIncrement
    (S : SHS Q n m) (g : DavisState Q n → ℝ) (z : DavisState Q n) :
    S.totalIntensity z * davisExpectedResetIncrement S g z =
      ∑ ℓ : Fin m, (g (S.resetDavisState ℓ z) - g z) *
        S.intensity ℓ z.1 z.2.1 z.2.2 := by
  unfold davisExpectedResetIncrement
  by_cases hz : S.totalIntensity z = 0
  · rw [totalIntensity] at hz
    have hzero : ∀ ℓ, S.intensity ℓ z.1 z.2.1 z.2.2 = 0 := fun ℓ =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun ℓ _ => S.intensity_nonneg ℓ z.1 z.2.1 z.2.2)).mp hz ℓ (Finset.mem_univ _)
    simp [hzero]; left; rw [totalIntensity]; exact hz
  · unfold davisChannelProbability
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.mul_sum, Finset.sum_congr rfl]
    intro ℓ _
    field_simp

/-- Away from zero total intensity, the marked reset kernel evaluates a
measurable event by summing the weights of all channels whose reset image lies
in that event. -/
theorem markedResetKernel_apply_of_totalIntensity_ne_zero
    (S : SHS Q n m) (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (z : DavisState Q n) (A : Set (DavisState Q n))
    (hz : S.totalIntensity z ≠ 0) :
    markedResetKernel S hr z A =
      ∑ ℓ ∈ Finset.univ.filter (fun j : Fin m => S.resetDavisState j z ∈ A),
        ENNReal.ofReal (davisChannelProbability S z ℓ) := by
  show markedResetMeasure S z A = _
  rw [markedResetMeasure]
  rw [if_neg hz]
  simp only [davisChannelProbability]
  simp
  rw [Finset.sum_filter]
  congr 1 with x
  by_cases hx : S.resetDavisState x z ∈ A <;> simp [hx]

/-- Consequently, the mass of one reset image is the sum of the probabilities
of every channel with that same image; no injectivity of reset channels is
silently assumed. -/
theorem markedResetKernel_singleton_reset
    (S : SHS Q n m) (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (z : DavisState Q n) (ℓ : Fin m) (hz : S.totalIntensity z ≠ 0) :
    markedResetKernel S hr z {S.resetDavisState ℓ z} =
      ∑ j ∈ Finset.univ.filter
          (fun j : Fin m => S.resetDavisState j z = S.resetDavisState ℓ z),
        ENNReal.ofReal (davisChannelProbability S z j) := by
  simpa only [Set.mem_singleton_iff] using
    markedResetKernel_apply_of_totalIntensity_ne_zero S hr z
      {S.resetDavisState ℓ z} hz

end SHS
