import SHSLib.Core.DavisElapsedOccupationCentering
import SHSLib.Core.DavisResetOccupationIntegrable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Concrete integrability criteria for the elapsed occupation envelope

The occupation part of the fixed-time envelope is bounded by accumulated total
hazard along the completed segments and the active partial segment.  Together
with an integrable active jump count, this turns boundedness of the test
function into an integrability criterion for the common envelope.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Total accumulated hazard along all completed segments and the active
partial segment at a fixed elapsed time. -/
def davisElapsedAccumulatedHazard (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) : ℝ :=
  let k := ξ.activeSegmentIndex hne t ω
  (∑ i ∈ Finset.range k,
      ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (davisFlow S hflow s.toNNReal
          (davisStateAfterJump S hflow ξ initial i ω))) +
    ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial k ω))

/-- Absolute completed and active reset occupations at fixed elapsed time. -/
def davisElapsedResetOccupationMagnitude (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  let k := ξ.activeSegmentIndex hne t ω
  (∑ i ∈ Finset.range k,
      |davisSampledResetOccupationCompensator S hflow g ξ initial i ω|) +
    |davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial k ω)
      (t - ξ.jumpTime k ω)|

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The common envelope is bounded by the completed-jump contribution plus the
occupation magnitude. -/
theorem davisElapsedOccupationEnvelope_le_count_add_magnitude
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C) (t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω ≤
      (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * C) +
        davisElapsedResetOccupationMagnitude
          S hflow ξ hne initial g t ω := by
  calc davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω
      = (∑ i ∈ Finset.range (ξ.activeSegmentIndex hne t ω),
          |davisRealizedResetIncrement S hflow ξ initial g i ω|) +
        (∑ i ∈ Finset.range (ξ.activeSegmentIndex hne t ω),
          |davisSampledResetOccupationCompensator S hflow g ξ initial i ω|) +
        |davisSegmentResetOccupationCompensator S hflow g
          (davisStateAfterJump S hflow ξ initial (ξ.activeSegmentIndex hne t ω) ω)
          (t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω)| := by rfl
    _ = (∑ i ∈ Finset.range (ξ.activeSegmentIndex hne t ω),
          |davisRealizedResetIncrement S hflow ξ initial g i ω|) +
        davisElapsedResetOccupationMagnitude
          S hflow ξ hne initial g t ω := by
        simp [davisElapsedResetOccupationMagnitude]
        ring
    _ ≤ (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * C) +
        davisElapsedResetOccupationMagnitude
          S hflow ξ hne initial g t ω := by
        gcongr
        have hbound : ∀ i ω, |davisRealizedResetIncrement S hflow ξ initial g i ω| ≤ 2 * C := by
          intro i ω
          unfold davisRealizedResetIncrement
          calc |g (S.resetDavisState (ξ.channel i ω) (davisStateBeforeJump S hflow ξ initial i ω)) -
                g (davisStateBeforeJump S hflow ξ initial i ω)|
              ≤ |g (S.resetDavisState (ξ.channel i ω) (davisStateBeforeJump S hflow ξ initial i ω))| +
                |g (davisStateBeforeJump S hflow ξ initial i ω)| := abs_sub _ _
            _ ≤ C + C := by linarith [hg (S.resetDavisState (ξ.channel i ω) (davisStateBeforeJump S hflow ξ initial i ω)),
                                      hg (davisStateBeforeJump S hflow ξ initial i ω)]
            _ = 2 * C := by ring
        exact le_trans (Finset.sum_le_sum fun i _ => hbound i ω) (by simp)

/-- Bounded tests control all completed and active reset occupations by twice
the bound times the total accumulated hazard. -/
theorem davisElapsedResetOccupationMagnitude_le_accumulatedHazard
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    davisElapsedResetOccupationMagnitude S hflow ξ hne initial g t ω ≤
      2 * C * davisElapsedAccumulatedHazard
        S hflow ξ hne initial t ω := by
  let k := ξ.activeSegmentIndex hne t ω
  -- For each completed segment i < k, bound the sampled compensator
  have hsampled : ∀ i ∈ Finset.range k,
      |S.davisSampledResetOccupationCompensator hflow g ξ initial i ω| ≤
      2 * C * ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω)) := by
    intro i _
    rw [davisSampledResetOccupationCompensator]
    apply abs_davisSegmentResetOccupationCompensator_le_integral_intensity
      S hflow g C hg _ _ (hreg.density_integrableOn _ _)
      ((hcont _).integrableOn_Icc)
  -- For the active segment, bound the segment compensator
  have hsegment :
      |S.davisSegmentResetOccupationCompensator hflow g (S.davisStateAfterJump hflow ξ initial k ω) (t - ξ.jumpTime k ω)| ≤
      2 * C * ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω)) := by
    apply abs_davisSegmentResetOccupationCompensator_le_integral_intensity
      S hflow g C hg _ _ (hreg.density_integrableOn _ _)
      ((hcont _).integrableOn_Icc)
  -- Sum the bounds
  have hle : (∑ i ∈ Finset.range k, |S.davisSampledResetOccupationCompensator hflow g ξ initial i ω| +
        |S.davisSegmentResetOccupationCompensator hflow g (S.davisStateAfterJump hflow ξ initial k ω) (t - ξ.jumpTime k ω)|) ≤
      (2 * C) * (∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))) +
      (2 * C) * ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω)) := by
    apply add_le_add
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum hsampled
    · exact hsegment
  have heq : (2 * C) * (∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))) +
      (2 * C) * ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω)) =
      (2 * C * ((∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))) +
        (∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω))))) := by
    rw [mul_add]
  rw [davisElapsedResetOccupationMagnitude, davisElapsedAccumulatedHazard]
  show (∑ i ∈ Finset.range k, |S.davisSampledResetOccupationCompensator hflow g ξ initial i ω| +
        |S.davisSegmentResetOccupationCompensator hflow g (S.davisStateAfterJump hflow ξ initial k ω) (t - ξ.jumpTime k ω)|) ≤
      2 * C * ((∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))) +
        (∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω))))
  convert hle using 1
  linarith

/-- An integrable jump count and accumulated-hazard envelope imply
integrability of the common fixed-time envelope.  Measurability of the two
random finite-sum expressions is kept explicit. -/
theorem integrable_davisElapsedOccupationEnvelope_of_count_hazard
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0)
    (henvelopeMeas : AEStronglyMeasurable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P)
    (hcount : Integrable
      (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : Integrable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P) :
    Integrable (davisElapsedOccupationEnvelope
      S hflow ξ hne initial g t) P := by
  -- The envelope is bounded by count * (2*C) + 2*C * hazard
  have hbdd : ∀ ω, |davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω| ≤
      (2 * C) * (ξ.activeSegmentIndex hne t ω) + (2 * C) * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by
    intro ω
    have h_nonneg : 0 ≤ davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω := by
      unfold davisElapsedOccupationEnvelope
      apply add_nonneg
      apply add_nonneg
      · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      · exact abs_nonneg _
    rw [abs_of_nonneg h_nonneg]
    have h1 := davisElapsedOccupationEnvelope_le_count_add_magnitude S hflow ξ hne initial g C hg t ω
    have h2 := davisElapsedResetOccupationMagnitude_le_accumulatedHazard S hflow hcont g C hg hreg ξ hne initial t ω
    calc davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω
        ≤ (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * C) + davisElapsedResetOccupationMagnitude S hflow ξ hne initial g t ω := h1
      _ ≤ (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * C) + 2 * C * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by linarith
      _ = (2 * C) * (ξ.activeSegmentIndex hne t ω) + (2 * C) * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by ring
  -- The bounding function is integrable
  have hcount' : Integrable (fun ω => (2 * C) * (ξ.activeSegmentIndex hne t ω)) P :=
    hcount.const_mul (2 * C)
  have hhazard' : Integrable (fun ω => (2 * C) * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P :=
    hhazard.const_mul (2 * C)
  have hbound_int : Integrable (fun ω => (2 * C) * (ξ.activeSegmentIndex hne t ω) + (2 * C) * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P :=
    hcount'.add hhazard'
  exact hbound_int.mono' henvelopeMeas (Filter.Eventually.of_forall hbdd)

end SHS
