import SHSLib.Core.DavisElapsedOccupationEnvelopeCriterion

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The bounded regime: uniform envelopes with no extra probabilistic input

Two elementary path-level bounds remove the remaining integrability
hypotheses of the concrete martingale and generator statements.

If the total jump intensity is bounded by a constant, then the hazard
accumulated by any elapsed time is at most that constant times the elapsed
time, because the completed holding times and the active partial segment
together make up exactly the elapsed time.  If moreover the holding times are
bounded below by a strictly positive constant, then the number of completed
jumps by any elapsed time is at most the elapsed time divided by that
constant.

For a bounded test function these two bounds make the elapsed occupation
envelope bounded by a deterministic constant at every fixed time.  Over a
finite measure the envelope is therefore automatically integrable, and the
martingale, generator, and Dynkin statements hold with the deterministic-cap
increment law as their only remaining structural input.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Under a uniform bound on the total intensity, the accumulated hazard at
elapsed time `t` is at most that bound times `t`. -/
theorem davisElapsedAccumulatedHazard_le_of_totalIntensity_bounded
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (L : ℝ) (hL : ∀ z, S.totalIntensity z ≤ L)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    davisElapsedAccumulatedHazard S hflow ξ hne initial t ω ≤ L * t := by
  unfold davisElapsedAccumulatedHazard
  let k := ξ.activeSegmentIndex hne t ω
  -- Bound each integral by L times the interval length
  have hintegral_bound : ∀ (T : ℝ), 0 ≤ T →
      ∀ z : DavisState Q n, ∫ s in Set.Icc (0 : ℝ) T, S.totalIntensity (S.davisFlow hflow s.toNNReal z) ≤ L * T := by
    intro T hT z
    have hintegrable : MeasureTheory.IntegrableOn (fun s => S.totalIntensity (S.davisFlow hflow s.toNNReal z)) (Set.Icc (0 : ℝ) T) := by
      exact (hcont z).integrableOn_Icc
    calc ∫ s in Set.Icc (0 : ℝ) T, S.totalIntensity (S.davisFlow hflow s.toNNReal z)
        ≤ ∫ _ in Set.Icc (0 : ℝ) T, L := by
          apply MeasureTheory.setIntegral_mono_on hintegrable (MeasureTheory.integrable_const L) measurableSet_Icc
          intro s _
          exact hL _
      _ = L * T := by
          rw [MeasureTheory.integral_const, smul_eq_mul]
          simp [hT]
          ring
  -- Apply bound to sum of completed segments
  have hsum_bound : ∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω), S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω)) ≤
      L * ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) := by
    calc ∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω), S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))
        ≤ ∑ i ∈ Finset.range k, L * (ξ.holdingTime i ω : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact hintegral_bound _ (by positivity) _
      _ = L * ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) := by rw [Finset.mul_sum]
  -- Bound for the active segment
  have hactive_bound : ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0), S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω)) ≤
      L * (t - ξ.jumpTime k ω : ℝ) := by
    have hle := ξ.jumpTime_activeSegmentIndex_le hne t ω
    have heq : ((t - ξ.jumpTime k ω : ℝ≥0) : ℝ) = t - ξ.jumpTime k ω := by
      rw [NNReal.coe_sub hle]
    rw [heq]
    apply hintegral_bound
    exact sub_nonneg_of_le hle
  -- Use jumpTime k = ∑_{i < k} holdingTime i
  have hjumpTime_eq : (ξ.jumpTime k ω : ℝ) = ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) := by
    induction k with
    | zero => simp [DavisJumpNoise.jumpTime_zero]
    | succ n ih =>
        simp [DavisJumpNoise.jumpTime_succ, Finset.sum_range_succ, ih]
  -- Combine bounds
  calc (∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω), S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))) +
        ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0), S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω))
      ≤ L * ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) + L * (t - ξ.jumpTime k ω : ℝ) := by
        apply add_le_add hsum_bound hactive_bound
    _ = L * (∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) + (t - ξ.jumpTime k ω : ℝ)) := by ring
    _ = L * (ξ.jumpTime k ω + (t - ξ.jumpTime k ω : ℝ)) := by rw [← hjumpTime_eq]
    _ = L * t := by ring

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Holding times bounded below by `d` limit the number of completed jumps by
elapsed time `t`. -/
theorem DavisJumpNoise.activeSegmentIndex_mul_le_of_holdingTime_ge
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (d : ℝ≥0) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω) (t : ℝ≥0) (ω : Ω) :
    ((ξ.activeSegmentIndex hne t ω : ℝ)) * (d : ℝ) ≤ (t : ℝ) := by
  set k := ξ.activeSegmentIndex hne t ω with hk
  -- First, jumpTime k ≤ t
  have hjump_le : ξ.jumpTime k ω ≤ t := ξ.jumpTime_activeSegmentIndex_le hne t ω
  -- Express jumpTime k as a sum of holding times
  have hjump_eq : ξ.jumpTime k ω = ∑ i ∈ Finset.range k, ξ.holdingTime i ω := by
    induction k with
    | zero => simp [DavisJumpNoise.jumpTime_zero]
    | succ n ih => simp [DavisJumpNoise.jumpTime_succ, Finset.sum_range_succ, ih]
  -- Each holding time is at least d, so the sum is at least k * d
  have hsum_ge : ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ≥0) ≥ k * d := by
    calc ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ≥0)
        ≥ ∑ _i ∈ Finset.range k, d := Finset.sum_le_sum fun i _ => hd i ω
      _ = k * d := by simp [Finset.sum_const]
  -- Combine: k * d ≤ jumpTime k ≤ t
  have h_final : (k : ℝ≥0) * d ≤ ξ.jumpTime k ω := by
    rw [hjump_eq]
    exact hsum_ge
  exact h_final.trans hjump_le

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A strictly positive lower bound on holding times gives positive holding
times. -/
theorem DavisJumpNoise.positiveHoldingTimes_of_holdingTime_ge
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (d : ℝ≥0) (hdpos : 0 < d)
    (hd : ∀ i ω, d ≤ ξ.holdingTime i ω) :
    ξ.PositiveHoldingTimes :=
  fun k ω => lt_of_lt_of_le hdpos (hd k ω)

/-- In the bounded regime the elapsed occupation envelope is bounded by a
deterministic constant at every fixed time. -/
theorem davisElapsedOccupationEnvelope_le_of_bounded_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hC : 0 ≤ C) (hgC : ∀ z, |g z| ≤ C)
    (L : ℝ) (hL : ∀ z, S.totalIntensity z ≤ L)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω ≤
      (2 * C) * ((t : ℝ) / (d : ℝ)) + 2 * C * (L * t) := by
  -- Use the bound from davisElapsedOccupationEnvelope_le_count_add_magnitude
  have h1 := davisElapsedOccupationEnvelope_le_count_add_magnitude S hflow ξ hne initial g C hgC t ω
  -- Use the bound on the magnitude by accumulated hazard
  have h2 := davisElapsedResetOccupationMagnitude_le_accumulatedHazard S hflow hcont g C hgC hreg ξ hne initial t ω
  -- Use the bound on accumulated hazard by total intensity
  have h3 := davisElapsedAccumulatedHazard_le_of_totalIntensity_bounded S hflow hcont L hL ξ hne initial t ω
  -- Use the bound on active segment index
  have h4 := ξ.activeSegmentIndex_mul_le_of_holdingTime_ge hne d hd t ω
  -- Derive activeSegmentIndex ≤ t / d
  have h5 : (ξ.activeSegmentIndex hne t ω : ℝ) ≤ (t : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ (by positivity : (d : ℝ) > 0)]
    exact h4
  -- Chain the inequalities
  calc davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω
      ≤ (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * C) + davisElapsedResetOccupationMagnitude S hflow ξ hne initial g t ω := h1
    _ ≤ (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * C) + 2 * C * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by linarith [h2]
    _ ≤ (t / d) * (2 * C) + 2 * C * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by
        apply add_le_add
        · have hC' : 0 ≤ 2 * C := by linarith
          nlinarith [h5]
        · exact le_refl _
    _ ≤ (t / d) * (2 * C) + 2 * C * (L * t) := by
        apply add_le_add
        · exact le_refl _
        · have hC' : 0 ≤ 2 * C := by linarith
          nlinarith [h3]
    _ = 2 * C * (t / d) + 2 * C * (L * t) := by ring

/-- In the bounded regime every fixed-time envelope is integrable over a
finite measure, with no further probabilistic hypotheses. -/
theorem integrable_davisElapsedOccupationEnvelope_of_bounded_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hC : 0 ≤ C) (hgC : ∀ z, |g z| ≤ C)
    (L : ℝ) (hL : ∀ z, S.totalIntensity z ≤ L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (initial : DavisState Q n) (hg : Measurable g) (t : ℝ≥0) :
    Integrable (davisElapsedOccupationEnvelope
      S hflow ξ hne initial g t) P := by
  -- The envelope is bounded by a constant
  have hbound : ∀ ω, davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω ≤
      (2 * C) * ((t : ℝ) / (d : ℝ)) + 2 * C * (L * t) := by
    intro ω
    exact davisElapsedOccupationEnvelope_le_of_bounded_regime hreg hcont C hC hgC L hL ξ hne d hdpos hd initial t ω
  -- The envelope is non-negative
  have hnonneg : ∀ ω, 0 ≤ davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω := by
    intro ω
    unfold davisElapsedOccupationEnvelope
    apply add_nonneg
    apply add_nonneg
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact abs_nonneg _
  -- The envelope is measurable
  have hmeas : Measurable (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) :=
    @DavisResetOccupationRegular.measurable_elapsedOccupationEnvelope Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial hg t
  -- Bound for the norm (as ae bound)
  have hbound_norm : ∀ᵐ ω ∂P, ‖davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω‖ ≤
      (2 * C) * ((t : ℝ) / (d : ℝ)) + 2 * C * (L * t) :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]; exact hbound ω)
  exact MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable _ hbound_norm

/-- Martingale property in the bounded regime: the deterministic-cap increment
law is the only remaining structural input. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_bounded_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hC : 0 ≤ C) (hgC : ∀ z, |g z| ≤ C)
    (L : ℝ) (hL : ∀ z, S.totalIntensity z ≤ L)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive}
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (initial : DavisState Q n) (hg : Measurable g)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P := by
  have henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P := fun t =>
    @integrable_davisElapsedOccupationEnvelope_of_bounded_regime Q _ _ n m S hflow hf hr g hreg hcont C hC hgC L hL Ω _ P _ ξ hξ hne d hdpos hd initial hg t
  exact @DavisStoppedElapsedOccupationIncrementLaw.martingale_full
    Q _ _ n m S hflow hf hr g hreg Ω _ P _ ξ hξ hne initial hg hlaw henv

/-- Dynkin-type identity in the bounded regime: the occupation-compensated
test-function increment has zero mean at every elapsed time. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_of_bounded_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {a g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hC : 0 ≤ C) (hgC : ∀ z, |g z| ≤ C)
    (L : ℝ) (hL : ∀ z, S.totalIntensity z ≤ L)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive}
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (initial : DavisState Q n) (hg : Measurable g)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g)
    (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 := by
  have hpos : ξ.PositiveHoldingTimes := DavisJumpNoise.positiveHoldingTimes_of_holdingTime_ge ξ d hdpos hd
  have hmart : Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
    @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_bounded_regime
      Q _ _ n m S hflow hf hr g hreg hcont C hC hgC L hL Ω _ P _ ξ hξ hne d hdpos hd initial hg hlaw
  exact integral_davisElapsedCompensatedGeneratorProcess_eq_zero
    S hflow P ξ.fullFiltration ξ hne hpos initial a g hga hmart t

end SHS
