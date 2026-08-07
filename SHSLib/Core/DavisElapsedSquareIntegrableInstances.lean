import SHSLib.Core.DavisElapsedPathwiseSquareIntegrability

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Model classes satisfying the square-integrability conditions

The square-integrable relaxed regime asks for three `L²` conditions: on the
random test bound, on the random intensity bound along the visited flow
segments, and on the scaled reciprocal of the random lower bound for the
holding times.  This module discharges the last two for the model classes in
which they are automatic, and assembles the resulting statements.

* A **uniform intensity bound** over the state space is a constant intensity
  bound along the trajectory, and constants are square integrable over a
  finite measure.
* A **deterministic minimal holding time** is a constant lower bound, and its
  scaled reciprocal is again constant, hence square integrable.

Combining the two leaves a single genuine hypothesis, square integrability of
the path-level test bound.  The resulting statement strictly extends the
bounded regime, which needed a test function bounded uniformly over the whole
state space: here the test function only has to be bounded along the visited
trajectory by a square-integrable random variable.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The two automatic conditions -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A uniform bound on the total intensity is a constant intensity bound along
every visited flow segment. -/
theorem intensity_bound_of_uniform
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (Λ : ℝ) (hΛ : ∀ z, S.totalIntensity z ≤ Λ) :
    ∀ i (ω : Ω) (s : ℝ),
      S.totalIntensity (davisFlow S hflow s.toNNReal
        (davisStateAfterJump S hflow ξ initial i ω)) ≤ (fun _ => Λ) ω :=
  fun _ _ _ => hΛ _

/-- A constant intensity bound is square integrable over a finite measure. -/
theorem memLp_two_const_intensity_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Λ : ℝ) : MemLp (fun _ : Ω => Λ) 2 P :=
  memLp_const Λ

/-- A deterministic strictly positive minimal holding time is a constant
random lower bound whose scaled reciprocal is square integrable. -/
theorem memLp_two_const_holdingTime_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (δ t : ℝ≥0) :
    MemLp (fun _ : Ω => (t : ℝ) / (δ : ℝ)) 2 P :=
  memLp_const _

/-! ## Uniform intensity and deterministic minimal holding time -/

/-- **The two product hypotheses for a uniform model.**  With a uniform bound
on the total intensity and a deterministic strictly positive minimal holding
time, the two product hypotheses of the path-level regime follow from square
integrability of the path-level test bound alone. -/
theorem integrable_mul_of_uniform_model
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (G : Ω → ℝ) (hG2 : MemLp G 2 P)
    (Λ : ℝ) (hΛ : ∀ z, S.totalIntensity z ≤ Λ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hd : ∀ i ω, δ ≤ ξ.holdingTime i ω) :
    (∀ t, Integrable (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P) ∧
      ∀ t, Integrable (fun ω => G ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P :=
  @integrable_mul_of_square_relaxed_regime
    Q _ _ n m S hflow hf hr g hreg hcont Ω _ P ξ hξ hne initial G hG2
    (fun _ => Λ) (intensity_bound_of_uniform S hflow ξ initial Λ hΛ)
    (memLp_const Λ) (fun _ => δ) (fun _ => hδ) hd
    (fun _ => memLp_const _)

/-- **Martingale property for a uniform model with a square-integrable test
bound.**  Under a uniform intensity bound and a deterministic strictly
positive minimal holding time, the occupation-centered reset process is a
martingale for the full-information filtration as soon as the test function is
bounded along the trajectory by a square-integrable random variable, with the
deterministic-cap increment law as the only remaining structural input. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_uniform_model
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
    (Λ : ℝ) (hΛ : ∀ z, S.totalIntensity z ≤ Λ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hd : ∀ i ω, δ ≤ ξ.holdingTime i ω)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_square_relaxed_regime
    Q _ _ n m S hflow hf hr g hreg hcont Ω _ P _ ξ hξ hne initial hg G hG hG2
    (fun _ => Λ) (intensity_bound_of_uniform S hflow ξ initial Λ hΛ)
    (memLp_const Λ) (fun _ => δ) (fun _ => hδ) hd
    (fun _ => memLp_const _) hlaw

/-- **Dynkin-type identity for a uniform model with a square-integrable test
bound.** -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_of_uniform_model
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
    (hG2 : MemLp G 2 P)
    (Λ : ℝ) (hΛ : ∀ z, S.totalIntensity z ≤ Λ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hd : ∀ i ω, δ ≤ ξ.holdingTime i ω)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g)
    (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 :=
  @integral_davisElapsedCompensatedGeneratorProcess_eq_zero_of_pathwise_bound
    Q _ _ n m S hflow hf hr a g hreg hcont Ω _ P _ ξ hξ hne hpos initial hg hga
    G hG
    (@integrable_mul_of_uniform_model
      Q _ _ n m S hflow hf hr g hreg hcont Ω _ P _ ξ hξ hne initial G hG2
      Λ hΛ δ hδ hd).1
    (@integrable_mul_of_uniform_model
      Q _ _ n m S hflow hf hr g hreg hcont Ω _ P _ ξ hξ hne initial G hG2
      Λ hΛ δ hδ hd).2
    hlaw t

/-! ## A uniformly bounded test function is the degenerate case -/

/-- With a uniformly bounded test function the square-integrability hypothesis
is automatic, so the uniform model recovers the bounded regime. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_uniform_model_of_bounded_test
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (C : ℝ) (hgC : ∀ z, |g z| ≤ C)
    (Λ : ℝ) (hΛ : ∀ z, S.totalIntensity z ≤ Λ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hd : ∀ i ω, δ ≤ ξ.holdingTime i ω)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_uniform_model
    Q _ _ n m S hflow hf hr g hreg hcont Ω _ P _ ξ hξ hne initial hg
    (fun _ => C) (DavisPathwiseTestBound.of_uniform S hflow ξ initial g C hgC)
    (memLp_const C) Λ hΛ δ hδ hd hlaw

end SHS
