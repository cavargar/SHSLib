import SHSLib.Core.DavisElapsedOccupationFullObservability
import SHSLib.Core.DavisElapsedOccupationEnvelopeIntegrable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Envelope integrability from bounded tests, and fully concrete martingales

The concrete martingale theorem still takes integrability of the elapsed
occupation envelope at every time as an input.  For a bounded test function
that input follows from two purely path-level integrability statements: an
integrable active jump count and an integrable accumulated hazard.  This
module records that criterion and then feeds it, together with the
full-information observability instance, into the martingale and generator
theorems.

The final statement is a Dynkin-type identity: under boundedness of the test
function, the flow fundamental-theorem identity, path-level integrability, and
the deterministic-cap increment law, the occupation-compensated test-function
increment has zero mean at every elapsed time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Bounded test functions with integrable jump count and integrable
accumulated hazard have integrable elapsed occupation envelopes at every
time. -/
theorem DavisResetOccupationRegular.integrable_elapsedOccupationEnvelope_of_bounded
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hgC : ∀ z, |g z| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g)
    (hcount : ∀ t, Integrable
      (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P)
    (t : ℝ≥0) :
    Integrable (davisElapsedOccupationEnvelope
      S hflow ξ hne initial g t) P := by
  apply integrable_davisElapsedOccupationEnvelope_of_count_hazard
    S hflow hcont g C hgC hreg P ξ hne initial t
  · exact (@DavisResetOccupationRegular.measurable_elapsedOccupationEnvelope
        Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial hg t).aestronglyMeasurable
  · exact hcount t
  · exact hhazard t

/-- Fully concrete martingale property for the full-information filtration:
only reset-occupation regularity, measurable noise, a bounded measurable test
function, path-level integrability, and the deterministic-cap increment law
are required. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_bounded
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hgC : ∀ z, |g z| ≤ C)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (hcount : ∀ t, Integrable
      (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P := by
  have henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P := fun t =>
    @DavisResetOccupationRegular.integrable_elapsedOccupationEnvelope_of_bounded
      Q _ _ n m S hflow hf hr g hreg hcont C hgC Ω _ P ξ hξ hne initial hg hcount hhazard t
  exact @DavisStoppedElapsedOccupationIncrementLaw.martingale_full
    Q _ _ n m S hflow hf hr g hreg Ω _ P _ ξ hξ hne initial hg hlaw henv

/-- Fully concrete martingale property for the occupation-compensated
test-function process. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_compensatedGenerator_of_bounded
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
    (hcount : ∀ t, Integrable
      (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        S hflow ξ hne initial a g) ξ.fullFiltration P := by
  have henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P := fun t =>
    @DavisResetOccupationRegular.integrable_elapsedOccupationEnvelope_of_bounded
      Q _ _ n m S hflow hf hr g hreg hcont C hgC Ω _ P ξ hξ hne initial hg hcount hhazard t
  have hmart_centered : Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
    @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_bounded
      Q _ _ n m S hflow hf hr g hreg hcont C hgC Ω _ P _ ξ hξ hne initial hg hcount hhazard hlaw
  exact martingale_davisElapsedCompensatedGeneratorProcess
    S hflow P ξ.fullFiltration ξ hne initial a g hga hmart_centered

/-- Dynkin-type identity under concrete hypotheses: the occupation-compensated
test-function increment has zero mean at every elapsed time. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_of_bounded
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {a g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hgC : ∀ z, |g z| ≤ C)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) (hg : Measurable g)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (hcount : ∀ t, Integrable
      (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g)
    (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 := by
  have hmart : Martingale
      (davisElapsedCompensatedGeneratorProcess
        S hflow ξ hne initial a g) ξ.fullFiltration P :=
    @DavisStoppedElapsedOccupationIncrementLaw.martingale_compensatedGenerator_of_bounded
      Q _ _ n m S hflow hf hr a g hreg hcont C hgC Ω _ P _ ξ hξ hne initial hg hga hcount hhazard hlaw
  -- Use martingale property: ∫ M_t = ∫ M_0
  have hcond : ∀ᵐ (ω : Ω) ∂P, P[fun ω' => davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g t ω' | ξ.fullFiltration 0] ω =
                                davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g 0 ω :=
    hmart.condExp_ae_eq (zero_le t)
  have hSTART : davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g 0 = 0 := by
    rw [davisElapsedCompensatedGeneratorProcess_eq_occupationCenteredProcess
      S hflow ξ hne initial a g hga]
    exact funext fun ω => davisElapsedOccupationCenteredResetProcess_zero S hflow ξ hne hpos initial g ω
  calc ∫ ω, davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g t ω ∂P
      = ∫ ω, P[fun ω' => davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g t ω' | ξ.fullFiltration 0] ω ∂P := by
        rw [MeasureTheory.integral_condExp]
    _ = ∫ ω, davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g 0 ω ∂P := by
        exact MeasureTheory.integral_congr_ae hcond
    _ = 0 := by simp [hSTART]

end SHS
