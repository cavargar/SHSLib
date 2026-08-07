import SHSLib.Core.DavisElapsedPathwiseProducts
import SHSLib.Core.DavisElapsedAccumulatedHazardMeasurable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Square integrability of the path-level quantities

The Cauchy–Schwarz criterion of the previous module reduces the two product
hypotheses of the path-level regime to square integrability of three factors:
the random test bound, the completed-jump count and the accumulated hazard.
The first is a hypothesis on the test function, but the last two are
properties of the model, and they are obtained from exactly the same pathwise
estimates that gave integrability in the relaxed regime, now applied in `L²`:

* the accumulated hazard at elapsed time `t` is squeezed between `0` and
  `L · t`, so it is square integrable as soon as the random intensity bound
  `L` is;
* the completed-jump count at elapsed time `t` is at most `t / d`, so it is
  square integrable as soon as `t / d` is, where `d` is the random strictly
  positive lower bound on the holding times.

Combining the two with the Cauchy–Schwarz criterion gives the martingale and
Dynkin statements for an unbounded test function under three `L²` conditions,
with the deterministic-cap increment law as the only remaining structural
input.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Square integrability of the accumulated hazard -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A square-integrable random intensity bound along the visited flow segments
makes the accumulated hazard square integrable at every elapsed time. -/
theorem memLp_two_davisElapsedAccumulatedHazard_of_pathwise_intensity_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (hL2 : MemLp L 2 P) (t : ℝ≥0)
    (hmeas : AEStronglyMeasurable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P) :
    MemLp (davisElapsedAccumulatedHazard S hflow ξ hne initial t) 2 P := by
  refine MemLp.of_le (hL2.mul_const (t : ℝ)) hmeas ?_
  filter_upwards with ω
  have hnonneg : 0 ≤ davisElapsedAccumulatedHazard S hflow ξ hne initial t ω :=
    davisElapsedAccumulatedHazard_nonneg S hflow ξ hne initial t ω
  have hbound : davisElapsedAccumulatedHazard S hflow ξ hne initial t ω ≤ L ω * t :=
    davisElapsedAccumulatedHazard_le_of_pathwise_intensity_bound
      S hflow hcont ξ hne initial L hL t ω
  have hLnonneg : 0 ≤ L ω :=
    le_trans (totalIntensity_nonneg _ _) (hL 0 ω 0)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ L ω * t)]
  exact hbound

/-- Square integrability of the accumulated hazard, with the measurability
side condition discharged by the reset-occupation regularity. -/
theorem DavisResetOccupationRegular.memLp_two_elapsedAccumulatedHazard
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
    (hL2 : MemLp L 2 P) (t : ℝ≥0) :
    MemLp (davisElapsedAccumulatedHazard S hflow ξ hne initial t) 2 P :=
  memLp_two_davisElapsedAccumulatedHazard_of_pathwise_intensity_bound
    S hflow hcont P ξ hne initial L hL hL2 t
    (@DavisResetOccupationRegular.measurable_elapsedAccumulatedHazard
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial t).aestronglyMeasurable

/-! ## Square integrability of the completed-jump count -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A random strictly positive lower bound on the holding times whose scaled
reciprocal is square integrable makes the completed-jump count square
integrable at every elapsed time. -/
theorem memLp_two_activeSegmentIndex_of_holdingTime_ge_random
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω) (t : ℝ≥0)
    (hd2 : MemLp (fun ω => (t : ℝ) / (d ω : ℝ)) 2 P) :
    MemLp (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) 2 P := by
  have hmeas : AEStronglyMeasurable
      (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P := by
    have hk : Measurable (fun ω => ξ.activeSegmentIndex hne t ω) :=
      hξ.activeSegmentIndex hne t
    have hk2 : Measurable (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) := by
      measurability
    exact hk2.aestronglyMeasurable
  refine MemLp.of_le hd2 hmeas ?_
  filter_upwards with ω
  have hle := DavisJumpNoise.activeSegmentIndex_le_of_holdingTime_ge_random
    ξ hne d hdpos hd t ω
  have hdpos' : (0 : ℝ) < d ω := NNReal.coe_pos.mpr (hdpos ω)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ξ.activeSegmentIndex hne t ω : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) / (d ω : ℝ))]
  exact hle

/-! ## The square-integrable relaxed regime -/

/-- Both product hypotheses of the path-level regime hold under the square
integrability of the random test bound, of the random intensity bound and of
the scaled reciprocal holding-time bound. -/
theorem integrable_mul_of_square_relaxed_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (G : Ω → ℝ) (hG2 : MemLp G 2 P)
    (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (hL2 : MemLp L 2 P)
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hd2 : ∀ t : ℝ≥0, MemLp (fun ω => (t : ℝ) / (d ω : ℝ)) 2 P) :
    (∀ t, Integrable (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P) ∧
      ∀ t, Integrable (fun ω => G ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P :=
  integrable_mul_of_memLp_two_pathwise_bound S hflow P ξ hne initial G hG2
    (fun t => memLp_two_activeSegmentIndex_of_holdingTime_ge_random
      P hξ hne d hdpos hd t (hd2 t))
    (fun t => @DavisResetOccupationRegular.memLp_two_elapsedAccumulatedHazard
      Q _ _ n m S hflow hf hr g hreg hcont Ω _ P ξ hξ hne initial L hL hL2 t)

/-- Martingale property in the square-integrable relaxed regime: an unbounded
test function bounded along the trajectory by a square-integrable random
variable, a square-integrable random intensity bound, and a random
strictly positive holding-time lower bound with square-integrable scaled
reciprocal. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_square_relaxed_regime
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (G : Ω → ℝ) (hG : DavisPathwiseTestBound S hflow ξ initial g G)
    (hG2 : MemLp G 2 P)
    (L : Ω → ℝ)
    (hL : ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ L ω)
    (hL2 : MemLp L 2 P)
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hd2 : ∀ t : ℝ≥0, MemLp (fun ω => (t : ℝ) / (d ω : ℝ)) 2 P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_pathwise_bound
    Q _ _ n m S hflow hf hr g hreg hcont Ω _ P _ ξ hξ hne initial hg G hG
    (@integrable_mul_of_square_relaxed_regime
      Q _ _ n m S hflow hf hr g hreg hcont Ω _ P ξ hξ hne initial G hG2
      L hL hL2 d hdpos hd hd2).1
    (@integrable_mul_of_square_relaxed_regime
      Q _ _ n m S hflow hf hr g hreg hcont Ω _ P ξ hξ hne initial G hG2
      L hL hL2 d hdpos hd hd2).2 hlaw

end SHS
