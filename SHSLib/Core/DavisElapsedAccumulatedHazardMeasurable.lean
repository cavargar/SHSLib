import SHSLib.Core.DavisElapsedRelaxedRegime

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Measurability of the accumulated hazard

The relaxed-regime statements retain one hypothesis that the bounded regime
did not need: measurability of the accumulated hazard at each elapsed time.
This module discharges it.

The segment hazard is the negative logarithm of the segment survivor factor,
which is jointly measurable in the segment initial state and the segment
duration by the standing occupation regularity assumption.  The accumulated
hazard is obtained from it by summing over a random number of completed
segments and adding the active partial segment; both operations preserve
measurability because the segment index is measurable and ranges over a
countable set.  Consequently the envelope integrability, martingale, and
Dynkin-type statements of the relaxed regime hold with no measurability side
condition.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Two measurability helpers for randomly indexed families -/

/-- Selecting a member of a countably indexed family of measurable functions
by a measurable index preserves measurability. -/
theorem measurable_apply_measurable_index {α : Type*} [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β] (k : α → ℕ) (hk : Measurable k)
    (f : ℕ → α → β) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun a => f (k a) a) := by
  intro s hs
  have h1 : (fun a => f (k a) a) ⁻¹' s = ⋃ i : ℕ, {a | k a = i} ∩ {a | f i a ∈ s} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨k a, rfl, h⟩, fun ⟨i, hi, hi'⟩ => hi ▸ hi'⟩
  rw [h1]
  exact MeasurableSet.iUnion fun i => (hk (MeasurableSet.singleton i)).inter (hf i hs)

/-- Summing a countably indexed family of measurable functions over a
measurable number of terms preserves measurability. -/
theorem measurable_sum_range_measurable_index {α : Type*} [MeasurableSpace α]
    (k : α → ℕ) (hk : Measurable k) (f : ℕ → α → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun a => ∑ i ∈ Finset.range (k a), f i a) :=
  measurable_apply_measurable_index k hk
    (fun j a => ∑ i ∈ Finset.range j, f i a)
    (fun _ => Finset.measurable_sum _ fun i _ => hf i)

/-! ## Joint measurability of the segment hazard -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The integrated hazard of a segment is the negative logarithm of its
survivor factor. -/
theorem davisIntegratedHazard_eq_neg_log_segmentSurvivor
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (z : DavisState Q n) (u : ℝ≥0) :
    davisIntegratedHazard S hflow z u =
      -Real.log (davisSegmentSurvivor S hflow z u) := by
  unfold davisSegmentSurvivor
  rw [Real.log_exp]
  ring

omit [MeasurableSingletonClass Q] in
/-- The integrated hazard is jointly measurable in the segment initial state
and the segment duration. -/
theorem DavisResetOccupationRegular.measurable_integratedHazard
    {S : SHS Q n m} {hflow : S.HasGlobalFlow} {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g) :
    Measurable (fun p : DavisState Q n × ℝ≥0 =>
      davisIntegratedHazard S hflow p.1 p.2) := by
  have h : (fun p : DavisState Q n × ℝ≥0 =>
        davisIntegratedHazard S hflow p.1 p.2) =
      fun p : DavisState Q n × ℝ≥0 =>
        -Real.log (davisSegmentSurvivor S hflow p.1 p.2) := by
    funext p
    exact davisIntegratedHazard_eq_neg_log_segmentSurvivor S hflow p.1 p.2
  rw [h]
  exact (Real.measurable_log.comp hreg.survivor_measurable).neg

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The accumulated hazard is a sum of segment hazards along the visited
segments. -/
theorem davisElapsedAccumulatedHazard_eq_sum_integratedHazard
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    davisElapsedAccumulatedHazard S hflow ξ hne initial t ω =
      (∑ i ∈ Finset.range (ξ.activeSegmentIndex hne t ω),
          davisIntegratedHazard S hflow
            (davisStateAfterJump S hflow ξ initial i ω)
            (ξ.holdingTime i ω)) +
        davisIntegratedHazard S hflow
          (davisStateAfterJump S hflow ξ initial
            (ξ.activeSegmentIndex hne t ω) ω)
          (t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω) := by
  unfold davisElapsedAccumulatedHazard davisIntegratedHazard
  rfl

/-! ## Measurability of the accumulated hazard -/

/-- The accumulated hazard at a fixed elapsed time is measurable. -/
theorem DavisResetOccupationRegular.measurable_elapsedAccumulatedHazard
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) :
    Measurable (davisElapsedAccumulatedHazard S hflow ξ hne initial t) := by
  have heq : davisElapsedAccumulatedHazard S hflow ξ hne initial t =
      fun ω => (∑ i ∈ Finset.range (ξ.activeSegmentIndex hne t ω),
          davisIntegratedHazard S hflow
            (davisStateAfterJump S hflow ξ initial i ω)
            (ξ.holdingTime i ω)) +
        davisIntegratedHazard S hflow
          (davisStateAfterJump S hflow ξ initial
            (ξ.activeSegmentIndex hne t ω) ω)
          (t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω) := by
    funext ω
    exact davisElapsedAccumulatedHazard_eq_sum_integratedHazard
      S hflow ξ hne initial t ω
  rw [heq]
  have hk_meas : Measurable (fun ω => ξ.activeSegmentIndex hne t ω) :=
    hξ.activeSegmentIndex hne t
  have hjoint : Measurable (fun p : DavisState Q n × ℝ≥0 =>
      davisIntegratedHazard S hflow p.1 p.2) := hreg.measurable_integratedHazard
  have hf_meas : ∀ i : ℕ, Measurable (fun ω =>
      davisIntegratedHazard S hflow
        (davisStateAfterJump S hflow ξ initial i ω)
        (ξ.holdingTime i ω)) := fun i =>
    hjoint.comp ((hξ.stateAfterJump S hflow hf hr initial i).prodMk
      (hξ.holdingTime i))
  have hsum_meas := measurable_sum_range_measurable_index
    (fun ω => ξ.activeSegmentIndex hne t ω) hk_meas
    (fun i ω => davisIntegratedHazard S hflow
      (davisStateAfterJump S hflow ξ initial i ω)
      (ξ.holdingTime i ω)) hf_meas
  have hf_last_meas : ∀ i : ℕ, Measurable (fun ω =>
      davisIntegratedHazard S hflow
        (davisStateAfterJump S hflow ξ initial i ω)
        (t - ξ.jumpTime i ω)) := fun i =>
    hjoint.comp ((hξ.stateAfterJump S hflow hf hr initial i).prodMk
      (measurable_const.sub (hξ.jumpTime i)))
  have hlast_meas := measurable_apply_measurable_index
    (fun ω => ξ.activeSegmentIndex hne t ω) hk_meas
    (fun i ω => davisIntegratedHazard S hflow
      (davisStateAfterJump S hflow ξ initial i ω)
      (t - ξ.jumpTime i ω)) hf_last_meas
  exact hsum_meas.add hlast_meas

/-- Integrability of the accumulated hazard from an integrable pathwise
intensity envelope, with no measurability side condition. -/
theorem integrable_davisElapsedAccumulatedHazard_of_pathwise_bound
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (hLint : Integrable L P) (t : ℝ≥0) :
    Integrable (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P :=
  integrable_davisElapsedAccumulatedHazard_of_pathwise_intensity_bound
    S hflow hcont P ξ hne initial L hL hLint t
    (@DavisResetOccupationRegular.measurable_elapsedAccumulatedHazard
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial
      t).aestronglyMeasurable

/-! ## The relaxed regime without a measurability hypothesis -/

/-- Envelope integrability in the relaxed regime, with the measurability
hypothesis discharged. -/
theorem integrable_davisElapsedOccupationEnvelope_of_relaxed_regime'
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
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hdint : ∀ t : ℝ≥0, Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P)
    (t : ℝ≥0) :
    Integrable (davisElapsedOccupationEnvelope
      S hflow ξ hne initial g t) P :=
  @integrable_davisElapsedOccupationEnvelope_of_relaxed_regime
    Q _ _ n m S hflow hf hr g hreg hcont C hgC Ω _ P ξ hξ hne initial hg
    L hL hLint
    (fun t => (@DavisResetOccupationRegular.measurable_elapsedAccumulatedHazard
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial
      t).aestronglyMeasurable)
    d hdpos hd hdint t

/-- Martingale property in the relaxed regime, with the measurability
hypothesis discharged: the deterministic-cap increment law is the only
remaining structural input. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_relaxed_regime'
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
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hdint : ∀ t : ℝ≥0, Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_relaxed_regime
    Q _ _ n m S hflow hf hr g hreg hcont C hgC Ω _ P _ ξ hξ hne initial hg
    L hL hLint
    (fun t => (@DavisResetOccupationRegular.measurable_elapsedAccumulatedHazard
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial
      t).aestronglyMeasurable)
    d hdpos hd hdint hlaw

/-- Dynkin-type identity in the relaxed regime, with the measurability
hypothesis discharged. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_of_relaxed_regime'
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
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hdint : ∀ t : ℝ≥0, Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g)
    (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 :=
  @integral_davisElapsedCompensatedGeneratorProcess_eq_zero_of_relaxed_regime
    Q _ _ n m S hflow hf hr a g hreg hcont C hgC Ω _ P _ ξ hξ hne initial hg
    hga L hL hLint
    (fun t => (@DavisResetOccupationRegular.measurable_elapsedAccumulatedHazard
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial
      t).aestronglyMeasurable)
    d hdpos hd hdint hlaw t

end SHS
