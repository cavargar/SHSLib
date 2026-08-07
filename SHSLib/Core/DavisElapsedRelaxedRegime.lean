import SHSLib.Core.DavisElapsedOccupationMinimalFiltration

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The relaxed regime: random path-level envelopes

The bounded regime asks for a uniform bound on the total jump intensity over
the whole state space and for a deterministic strictly positive lower bound on
the holding times.  Both requirements can be weakened substantially.

For the accumulated hazard it suffices to bound the intensity along the states
actually visited by the trajectory, and the bound may itself be a random
variable, required only to be integrable.  For the completed-jump count it
suffices to bound the holding times from below by a random strictly positive
variable whose reciprocal is integrable.

Under these two relaxed hypotheses the elapsed occupation envelope is
integrable at every time for a bounded test function, so the martingale,
generator, and Dynkin-type statements hold with the deterministic-cap
increment law as their only remaining structural input.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Under a random bound on the total intensity along the visited flow
segments, the accumulated hazard at elapsed time `t` is at most that bound
times `t`. -/
theorem davisElapsedAccumulatedHazard_le_of_pathwise_intensity_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (t : ℝ≥0) (ω : Ω) :
    davisElapsedAccumulatedHazard S hflow ξ hne initial t ω ≤ L ω * t := by
  unfold davisElapsedAccumulatedHazard
  let k := ξ.activeSegmentIndex hne t ω
  -- Bound each integral by L(ω) times the interval length
  have hintegral_bound : ∀ i, ∀ (T : ℝ), 0 ≤ T →
      ∫ s in Set.Icc (0 : ℝ) T, S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω)) ≤ L ω * T := by
    intro i T hT
    have hintegrable : MeasureTheory.IntegrableOn (fun s => S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))) (Set.Icc (0 : ℝ) T) := by
      exact (hcont _).integrableOn_Icc
    calc ∫ s in Set.Icc (0 : ℝ) T, S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))
        ≤ ∫ _ in Set.Icc (0 : ℝ) T, L ω := by
          apply MeasureTheory.setIntegral_mono_on hintegrable (MeasureTheory.integrable_const (L ω)) measurableSet_Icc
          intro s _
          exact hL i ω s
      _ = L ω * T := by
          rw [MeasureTheory.integral_const, smul_eq_mul]
          simp [hT]
          ring
  -- Apply bound to sum of completed segments
  have hsum_bound : ∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω), S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω)) ≤
      L ω * ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) := by
    calc ∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω), S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))
        ≤ ∑ i ∈ Finset.range k, L ω * (ξ.holdingTime i ω : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact hintegral_bound i _ (by positivity)
      _ = L ω * ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) := by rw [Finset.mul_sum]
  -- Bound for the active segment
  have hactive_bound : ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0), S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω)) ≤
      L ω * (t - ξ.jumpTime k ω : ℝ) := by
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
      ≤ L ω * ∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) + L ω * (t - ξ.jumpTime k ω : ℝ) := by
        apply add_le_add hsum_bound hactive_bound
    _ = L ω * (∑ i ∈ Finset.range k, (ξ.holdingTime i ω : ℝ) + (t - ξ.jumpTime k ω : ℝ)) := by ring
    _ = L ω * (ξ.jumpTime k ω + (t - ξ.jumpTime k ω : ℝ)) := by rw [← hjumpTime_eq]
    _ = L ω * t := by ring

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The accumulated hazard is nonnegative. -/
theorem davisElapsedAccumulatedHazard_nonneg
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    0 ≤ davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by
  unfold davisElapsedAccumulatedHazard
  refine add_nonneg ?_ ?_
  · apply Finset.sum_nonneg
    intro i _
    apply MeasureTheory.setIntegral_nonneg measurableSet_Icc
    exact fun s _ => totalIntensity_nonneg _ _
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Icc
    exact fun s _ => totalIntensity_nonneg _ _

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- An integrable random intensity bound along the visited flow segments makes
the accumulated hazard integrable at every time. -/
theorem integrable_davisElapsedAccumulatedHazard_of_pathwise_intensity_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (hLint : Integrable L P) (t : ℝ≥0)
    (hmeas : AEStronglyMeasurable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P) :
    Integrable (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P := by
  -- The bound L * t is integrable since L is integrable
  have hLint_t : Integrable (fun ω => L ω * t) P := hLint.mul_const t
  -- The hazard is bounded by L * t
  have hbound : ∀ ω, davisElapsedAccumulatedHazard S hflow ξ hne initial t ω ≤ L ω * t := by
    intro ω
    exact davisElapsedAccumulatedHazard_le_of_pathwise_intensity_bound S hflow hcont ξ hne initial L hL t ω
  -- The hazard is nonnegative
  have hnonneg : ∀ ω, 0 ≤ davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by
    intro ω
    exact davisElapsedAccumulatedHazard_nonneg S hflow ξ hne initial t ω
  -- A nonnegative function bounded by an integrable function is integrable
  refine Integrable.mono' hLint_t ?_ ?_
  · exact hmeas
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]
    exact hbound ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A random strictly positive lower bound on the holding times limits the
completed-jump count by the elapsed time divided by that bound. -/
theorem DavisJumpNoise.activeSegmentIndex_le_of_holdingTime_ge_random
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω) (t : ℝ≥0) (ω : Ω) :
    ((ξ.activeSegmentIndex hne t ω : ℝ)) ≤ (t : ℝ) / (d ω : ℝ) := by
  have hjump_le : ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω ≤ t :=
    ξ.jumpTime_activeSegmentIndex_le hne t ω
  -- Prove by induction that jumpTime n ω ≥ n * d ω
  have hprod_le : ∀ n : ℕ, (n : ℝ) * d ω ≤ ξ.jumpTime n ω := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, jumpTime_succ]
      exact add_le_add ih (hd k ω)
  have hprod_le' : (ξ.activeSegmentIndex hne t ω : ℝ) * d ω ≤ ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω :=
    hprod_le _
  have hprod_le_t : (ξ.activeSegmentIndex hne t ω : ℝ) * d ω ≤ t := le_trans hprod_le' hjump_le
  have hdpos' : (0 : ℝ) < d ω := NNReal.coe_pos.mpr (hdpos ω)
  rw [le_div_iff₀' hdpos']
  rwa [mul_comm]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- If in addition the reciprocal bound is integrable, the completed-jump
count is integrable at every time. -/
theorem integrable_activeSegmentIndex_of_holdingTime_ge_random
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω) (t : ℝ≥0)
    (hdint : Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P) :
    Integrable (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P := by
  have hbound : ∀ ω, |(ξ.activeSegmentIndex hne t ω : ℝ)| ≤ (t : ℝ) / (d ω : ℝ) := by
    intro ω
    have hle := DavisJumpNoise.activeSegmentIndex_le_of_holdingTime_ge_random ξ hne d hdpos hd t ω
    have hnonneg : 0 ≤ (ξ.activeSegmentIndex hne t ω : ℝ) := by positivity
    rw [abs_of_nonneg hnonneg]
    exact hle
  have hmeas : AEStronglyMeasurable (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P := by
    let k : Ω → ℕ := fun ω => ξ.activeSegmentIndex hne t ω
    have hk : Measurable k := hξ.activeSegmentIndex hne t
    have hk2 : Measurable (fun ω => (k ω : ℝ)) := by measurability
    exact hk2.aestronglyMeasurable
  exact hdint.mono' hmeas (.of_forall hbound)

/-- Envelope integrability in the relaxed regime. -/
theorem integrable_davisElapsedOccupationEnvelope_of_relaxed_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hgC : ∀ z, |g z| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g)
    (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (hLint : Integrable L P)
    (hhazmeas : ∀ t, AEStronglyMeasurable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P)
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hdint : ∀ t : ℝ≥0, Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P)
    (t : ℝ≥0) :
    Integrable (davisElapsedOccupationEnvelope
      S hflow ξ hne initial g t) P :=
  @DavisResetOccupationRegular.integrable_elapsedOccupationEnvelope_of_bounded
    Q _ _ n m S hflow hf hr g hreg hcont C hgC Ω _ P ξ hξ hne initial hg
    (fun t => integrable_activeSegmentIndex_of_holdingTime_ge_random
      P hξ hne d hdpos hd t (hdint t))
    (fun t => integrable_davisElapsedAccumulatedHazard_of_pathwise_intensity_bound
      S hflow hcont P ξ hne initial L hL hLint t (hhazmeas t)) t

/-- Martingale property in the relaxed regime: the deterministic-cap increment
law is the only remaining structural input. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_relaxed_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hgC : ∀ z, |g z| ≤ C)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (hLint : Integrable L P)
    (hhazmeas : ∀ t, AEStronglyMeasurable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P)
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hdint : ∀ t : ℝ≥0, Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale_full
    Q _ _ n m S hflow hf hr g hreg Ω _ P _ ξ hξ hne initial hg hlaw
    (fun t => @integrable_davisElapsedOccupationEnvelope_of_relaxed_regime
      Q _ _ n m S hflow hf hr g hreg hcont C hgC Ω _ P ξ hξ hne initial hg
      L hL hLint hhazmeas d hdpos hd hdint t)

/-- Dynkin-type identity in the relaxed regime: the occupation-compensated
test-function increment has zero mean at every elapsed time. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_of_relaxed_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {a g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hgC : ∀ z, |g z| ≤ C)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (hLint : Integrable L P)
    (hhazmeas : ∀ t, AEStronglyMeasurable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P)
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hdint : ∀ t : ℝ≥0, Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g)
    (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 := by
  have hpos : ξ.PositiveHoldingTimes := fun k ω =>
    lt_of_lt_of_le (hdpos ω) (hd k ω)
  have hmart : Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
    @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_relaxed_regime
      Q _ _ n m S hflow hf hr g hreg hcont C hgC Ω _ P _ ξ hξ hne initial hg
      L hL hLint hhazmeas d hdpos hd hdint hlaw
  exact integral_davisElapsedCompensatedGeneratorProcess_eq_zero
    S hflow P ξ.fullFiltration ξ hne hpos initial a g hga hmart t

end SHS
