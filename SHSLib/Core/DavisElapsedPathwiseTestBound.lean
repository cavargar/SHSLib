import SHSLib.Core.DavisElapsedRelaxedRegime

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Path-level bounds on the test function

The relaxed regime weakened the two deterministic hypotheses on the dynamics —
the uniform bound on the total jump intensity and the deterministic lower bound
on the holding times — but it still asked for a uniform bound on the test
function over the whole state space.

Exactly as for the intensity, that requirement only has to hold along the
states actually visited by the trajectory, and the bound may itself be a random
variable.  This module records the resulting path-level test bound, redoes the
two envelope estimates with it, and restates the envelope integrability, the
martingale property, and the Dynkin-type zero-mean identity for a test function
that is bounded only along the trajectory.

The price is that the bound now multiplies the two path-level quantities, so
the integrability hypotheses are on the products of the random test bound with
the completed-jump count and with the accumulated hazard.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A random path-level bound on the test function: at every elapsed time on
every visited flow segment, the test function and all of its reset images are
bounded by `G ω`. -/
def DavisPathwiseTestBound (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (G : Ω → ℝ) : Prop :=
  ∀ (i : ℕ) (ω : Ω) (s : ℝ),
    |g (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω))| ≤ G ω ∧
      ∀ ℓ : Fin m, |g (S.resetDavisState ℓ (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)))| ≤ G ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A path-level test bound is nonnegative. -/
theorem DavisPathwiseTestBound.nonneg
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    {g : DavisState Q n → ℝ} {G : Ω → ℝ}
    (hG : DavisPathwiseTestBound S hflow ξ initial g G) (ω : Ω) :
    0 ≤ G ω :=
  le_trans (abs_nonneg _) ((hG 0 ω 0).1)

/-! ## The two envelope estimates with a segment bound -/

/-- Segment form of the occupation-density bound: only the values of the test
function along one flow segment and at its reset images are used. -/
theorem abs_davisSegmentResetOccupationDensity_le_of_segment_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (B : ℝ) (z : DavisState Q n)
    (hgz : ∀ s : ℝ, |g (davisFlow S hflow s.toNNReal z)| ≤ B)
    (hgr : ∀ (s : ℝ) (ℓ : Fin m),
      |g (S.resetDavisState ℓ (davisFlow S hflow s.toNNReal z))| ≤ B)
    (s : ℝ) :
    |davisSegmentResetOccupationDensity S hflow g z s| ≤
      2 * B * S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
  rw [davisSegmentResetOccupationDensity_eq_sum S hflow g z s]
  set y := davisFlow S hflow s.toNNReal z with hy
  have hs : (s.toNNReal : ℝ).toNNReal = s.toNNReal := by
    by_cases h : s ≤ 0
    · simp [Real.toNNReal_of_nonpos h]
    · simp [Real.toNNReal_of_nonneg (le_of_lt (not_le.mp h))]
  calc |∑ ℓ : Fin m, (g (S.resetDavisState ℓ y) - g y) * S.intensity ℓ y.1 y.2.1 y.2.2|
      ≤ ∑ ℓ, |(g (S.resetDavisState ℓ y) - g y) * S.intensity ℓ y.1 y.2.1 y.2.2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ℓ, |g (S.resetDavisState ℓ y) - g y| * S.intensity ℓ y.1 y.2.1 y.2.2 := by
        congr 1 with ℓ
        rw [abs_mul, abs_of_nonneg (S.intensity_nonneg ℓ _ _ _)]
    _ ≤ ∑ ℓ, 2 * B * S.intensity ℓ y.1 y.2.1 y.2.2 := by
        apply Finset.sum_le_sum
        intro ℓ _
        apply mul_le_mul_of_nonneg_right
        · have hgy := hgz (↑s.toNNReal)
          have hgrℓ := hgr (↑s.toNNReal) ℓ
          simp only [hs] at hgy hgrℓ
          calc |g (S.resetDavisState ℓ y) - g y|
                ≤ |g (S.resetDavisState ℓ y)| + |g y| := abs_sub _ _
              _ ≤ B + B := add_le_add hgrℓ hgy
              _ = 2 * B := by ring
        · exact S.intensity_nonneg ℓ _ _ _
    _ = 2 * B * S.totalIntensity y := by
        rw [totalIntensity, Finset.mul_sum]

/-- Segment form of the occupation-compensator bound. -/
theorem abs_davisSegmentResetOccupationCompensator_le_of_segment_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (B : ℝ) (z : DavisState Q n) (u : ℝ≥0)
    (hgz : ∀ s : ℝ, |g (davisFlow S hflow s.toNNReal z)| ≤ B)
    (hgr : ∀ (s : ℝ) (ℓ : Fin m),
      |g (S.resetDavisState ℓ (davisFlow S hflow s.toNNReal z))| ≤ B)
    (hreset : IntegrableOn
      (davisSegmentResetOccupationDensity S hflow g z)
      (Set.Icc (0 : ℝ) (u : ℝ)))
    (hintensity : IntegrableOn
      (fun s : ℝ => S.totalIntensity (davisFlow S hflow s.toNNReal z))
      (Set.Icc (0 : ℝ) (u : ℝ))) :
    |davisSegmentResetOccupationCompensator S hflow g z u| ≤
      2 * B * ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
  unfold davisSegmentResetOccupationCompensator
  calc |∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          davisSegmentResetOccupationDensity S hflow g z s|
      ≤ ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          |davisSegmentResetOccupationDensity S hflow g z s| := by
        apply abs_integral_le_integral_abs
    _ ≤ ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          2 * B * S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact hreset.norm
        · apply MeasureTheory.Integrable.const_mul
          exact hintensity
        · exact measurableSet_Icc
        · intro s hs
          exact abs_davisSegmentResetOccupationDensity_le_of_segment_bound
            S hflow g B z hgz hgr s
    _ = 2 * B * ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
        rw [MeasureTheory.integral_const_mul]

/-- Under a path-level test bound, the reset occupation magnitude is bounded by
twice that bound times the accumulated hazard. -/
theorem davisElapsedResetOccupationMagnitude_le_accumulatedHazard_pathwise
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (G : Ω → ℝ)
    (hG : DavisPathwiseTestBound S hflow ξ initial g G)
    (t : ℝ≥0) (ω : Ω) :
    davisElapsedResetOccupationMagnitude S hflow ξ hne initial g t ω ≤
      2 * G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by
  let k := ξ.activeSegmentIndex hne t ω
  -- For each completed segment i < k, bound the sampled compensator
  have hsampled : ∀ i ∈ Finset.range k,
      |S.davisSampledResetOccupationCompensator hflow g ξ initial i ω| ≤
      2 * G ω * ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω)) := by
    intro i _
    rw [davisSampledResetOccupationCompensator]
    apply abs_davisSegmentResetOccupationCompensator_le_of_segment_bound
      S hflow g (G ω) _
    · intro s
      exact (hG i ω s).1
    · intro s ℓ
      exact (hG i ω s).2 ℓ
    · exact hreg.density_integrableOn _ _
    · exact (hcont _).integrableOn_Icc
  -- For the active segment, bound the segment compensator
  have hsegment :
      |S.davisSegmentResetOccupationCompensator hflow g (S.davisStateAfterJump hflow ξ initial k ω) (t - ξ.jumpTime k ω)| ≤
      2 * G ω * ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω)) := by
    apply abs_davisSegmentResetOccupationCompensator_le_of_segment_bound
      S hflow g (G ω) _
    · intro s
      exact (hG k ω s).1
    · intro s ℓ
      exact (hG k ω s).2 ℓ
    · exact hreg.density_integrableOn _ _
    · exact (hcont _).integrableOn_Icc
  -- Sum the bounds
  have hle : (∑ i ∈ Finset.range k, |S.davisSampledResetOccupationCompensator hflow g ξ initial i ω| +
        |S.davisSegmentResetOccupationCompensator hflow g (S.davisStateAfterJump hflow ξ initial k ω) (t - ξ.jumpTime k ω)|) ≤
      (2 * G ω) * (∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))) +
      (2 * G ω) * ∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω)) := by
    apply add_le_add
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum hsampled
    · exact hsegment
  rw [davisElapsedResetOccupationMagnitude, davisElapsedAccumulatedHazard]
  show (∑ i ∈ Finset.range k, |S.davisSampledResetOccupationCompensator hflow g ξ initial i ω| +
        |S.davisSegmentResetOccupationCompensator hflow g (S.davisStateAfterJump hflow ξ initial k ω) (t - ξ.jumpTime k ω)|) ≤
      2 * G ω * ((∑ i ∈ Finset.range k, ∫ s in Set.Icc (0 : ℝ) (ξ.holdingTime i ω : ℝ),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial i ω))) +
        (∫ s in Set.Icc (0 : ℝ) (t - ξ.jumpTime k ω : ℝ≥0),
        S.totalIntensity (S.davisFlow hflow s.toNNReal (S.davisStateAfterJump hflow ξ initial k ω))))
  convert hle using 1
  ring

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Under a path-level test bound, the common envelope is bounded by the
completed-jump contribution plus the occupation magnitude. -/
theorem davisElapsedOccupationEnvelope_le_count_add_magnitude_pathwise
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) (G : Ω → ℝ)
    (hG : DavisPathwiseTestBound S hflow ξ initial g G)
    (t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω ≤
      (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * G ω) +
        davisElapsedResetOccupationMagnitude
          S hflow ξ hne initial g t ω := by
  let k := ξ.activeSegmentIndex hne t ω
  calc davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω
      = (∑ i ∈ Finset.range k,
          |davisRealizedResetIncrement S hflow ξ initial g i ω|) +
        (∑ i ∈ Finset.range k,
          |davisSampledResetOccupationCompensator S hflow g ξ initial i ω|) +
        |davisSegmentResetOccupationCompensator S hflow g
          (davisStateAfterJump S hflow ξ initial k ω)
          (t - ξ.jumpTime k ω)| := by rfl
    _ = (∑ i ∈ Finset.range k,
          |davisRealizedResetIncrement S hflow ξ initial g i ω|) +
        davisElapsedResetOccupationMagnitude
          S hflow ξ hne initial g t ω := by
        simp [davisElapsedResetOccupationMagnitude]
        ring
    _ ≤ (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * G ω) +
        davisElapsedResetOccupationMagnitude
          S hflow ξ hne initial g t ω := by
        gcongr
        have hbound : ∀ i ω, |davisRealizedResetIncrement S hflow ξ initial g i ω| ≤ 2 * G ω := by
          intro i ω
          unfold davisRealizedResetIncrement davisStateBeforeJump
          have hpre : |g (davisFlow S hflow ((ξ.holdingTime i ω) : ℝ).toNNReal (davisStateAfterJump S hflow ξ initial i ω))| ≤ G ω := (hG i ω (↑(ξ.holdingTime i ω))).1
          have hreset : ∀ ℓ : Fin m, |g (S.resetDavisState ℓ (davisFlow S hflow ((ξ.holdingTime i ω) : ℝ).toNNReal (davisStateAfterJump S hflow ξ initial i ω)))| ≤ G ω := (hG i ω (↑(ξ.holdingTime i ω))).2
          simp only [Real.toNNReal_coe] at hpre hreset ⊢
          calc |g (S.resetDavisState (ξ.channel i ω) (davisFlow S hflow (ξ.holdingTime i ω) (davisStateAfterJump S hflow ξ initial i ω))) -
                g (davisFlow S hflow (ξ.holdingTime i ω) (davisStateAfterJump S hflow ξ initial i ω))|
              ≤ |g (S.resetDavisState (ξ.channel i ω) (davisFlow S hflow (ξ.holdingTime i ω) (davisStateAfterJump S hflow ξ initial i ω)))| +
                |g (davisFlow S hflow (ξ.holdingTime i ω) (davisStateAfterJump S hflow ξ initial i ω))| := abs_sub _ _
            _ ≤ G ω + G ω := by linarith [hreset (ξ.channel i ω), hpre]
            _ = 2 * G ω := by ring
        have hsum : ∑ _i ∈ Finset.range k, 2 * G ω = k * (2 * G ω) := by simp
        exact le_trans (Finset.sum_le_sum fun i _ => hbound i ω) hsum.le

/-! ## Envelope integrability, martingale, and Dynkin identity -/

/-- Envelope integrability from a path-level test bound: the two integrability
hypotheses are on the products of that bound with the completed-jump count and
with the accumulated hazard. -/
theorem integrable_davisElapsedOccupationEnvelope_of_pathwise_test_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (G : Ω → ℝ)
    (hG : DavisPathwiseTestBound S hflow ξ initial g G) (t : ℝ≥0)
    (henvelopeMeas : AEStronglyMeasurable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P)
    (hcount : Integrable
      (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : Integrable
      (fun ω => G ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P) :
    Integrable (davisElapsedOccupationEnvelope
      S hflow ξ hne initial g t) P := by
  -- The envelope is nonnegative
  have henv_nonneg : ∀ ω, 0 ≤ davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω := by
    intro ω
    unfold davisElapsedOccupationEnvelope
    apply add_nonneg
    apply add_nonneg
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact abs_nonneg _
  -- Bound: envelope ≤ count * (2 * G) + magnitude
  have h_bound1 : ∀ ω, davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω ≤
      (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * G ω) +
      davisElapsedResetOccupationMagnitude S hflow ξ hne initial g t ω :=
    davisElapsedOccupationEnvelope_le_count_add_magnitude_pathwise S hflow ξ hne initial g G hG t
  -- Bound: magnitude ≤ 2 * G * accumulatedHazard
  have h_bound2 : ∀ ω, davisElapsedResetOccupationMagnitude S hflow ξ hne initial g t ω ≤
      2 * G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω :=
    davisElapsedResetOccupationMagnitude_le_accumulatedHazard_pathwise S hflow hcont g hreg ξ hne initial G hG t
  -- Combine: envelope ≤ 2 * G * count + 2 * G * hazard
  have h_combined : ∀ ω, davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω ≤
      2 * G ω * (ξ.activeSegmentIndex hne t ω : ℝ) + 2 * G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by
    intro ω
    calc davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω
        ≤ (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * G ω) +
          davisElapsedResetOccupationMagnitude S hflow ξ hne initial g t ω := h_bound1 ω
      _ ≤ (ξ.activeSegmentIndex hne t ω : ℝ) * (2 * G ω) +
          2 * G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by
          gcongr; exact h_bound2 ω
      _ = 2 * G ω * (ξ.activeSegmentIndex hne t ω : ℝ) + 2 * G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω := by ring
  -- The bounding function is integrable: 2 * (G * count + G * hazard)
  have h_bound_integrable : Integrable
      (fun ω => 2 * G ω * (ξ.activeSegmentIndex hne t ω : ℝ) + 2 * G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P := by
    have h1 : Integrable (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P := hcount
    have h2 : Integrable (fun ω => G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P := hhazard
    have hsum : Integrable (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ) + G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P := h1.add h2
    convert hsum.const_mul 2 using 1
    ext ω; ring
  -- Use the bound to conclude integrability
  refine MeasureTheory.Integrable.mono' h_bound_integrable ?_ ?_
  · exact henvelopeMeas
  · exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (henv_nonneg ω)]
      exact h_combined ω)

/-- Envelope integrability for a measurable test function bounded only along
the trajectory, with the envelope measurability discharged by reset-occupation
regularity. -/
theorem DavisResetOccupationRegular.integrable_elapsedOccupationEnvelope_of_pathwise_bound
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g) (G : Ω → ℝ)
    (hG : DavisPathwiseTestBound S hflow ξ initial g G)
    (hcount : ∀ t, Integrable
      (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (fun ω => G ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P)
    (t : ℝ≥0) :
    Integrable (davisElapsedOccupationEnvelope
      S hflow ξ hne initial g t) P := by
  refine integrable_davisElapsedOccupationEnvelope_of_pathwise_test_bound
    S hflow hcont g hreg P ξ hne initial G hG t ?_ (hcount t) (hhazard t)
  exact (@DavisResetOccupationRegular.measurable_elapsedOccupationEnvelope
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial hg t).aestronglyMeasurable

/-- Martingale property for a test function bounded only along the trajectory:
the deterministic-cap increment law is the only remaining structural input. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_pathwise_bound
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (G : Ω → ℝ) (hG : DavisPathwiseTestBound S hflow ξ initial g G)
    (hcount : ∀ t, Integrable
      (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (fun ω => G ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale_full
    Q _ _ n m S hflow hf hr g hreg Ω _ P _ ξ hξ hne initial hg hlaw
    (fun t => @DavisResetOccupationRegular.integrable_elapsedOccupationEnvelope_of_pathwise_bound
      Q _ _ n m S hflow hf hr g hreg hcont Ω _ P ξ hξ hne initial hg G hG
      hcount hhazard t)

/-- Dynkin-type identity for a test function bounded only along the
trajectory. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_of_pathwise_bound
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {a g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) (hg : Measurable g)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (G : Ω → ℝ) (hG : DavisPathwiseTestBound S hflow ξ initial g G)
    (hcount : ∀ t, Integrable
      (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (fun ω => G ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g)
    (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 := by
  have hmart : Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
    @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_pathwise_bound
      Q _ _ n m S hflow hf hr g hreg hcont Ω _ P _ ξ hξ hne initial hg
      G hG hcount hhazard hlaw
  exact integral_davisElapsedCompensatedGeneratorProcess_eq_zero
    S hflow P ξ.fullFiltration ξ hne hpos initial a g hga hmart t

end SHS
