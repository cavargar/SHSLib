import SHSLib.Core.DavisElapsedOccupationProcessMeasurable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Integrability constructors for the elapsed occupation process

The measurable stopped approximations from the reset-occupation regularity
interface discharge the analytic measurability premise in the fixed-time
envelope criterion.  Ambient integrability then passes automatically to every
restricted measure.  Subtraction gives the corresponding two-time increment
constructor.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- An integrable fixed-time envelope makes the full elapsed
occupation-centered reset value integrable. -/
theorem DavisResetOccupationRegular.integrable_elapsedOccupationCenteredResetSum
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (initial : DavisState Q n)
    (hg : Measurable g) (t : ℝ≥0)
    (henvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Integrable (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t) P := by
  refine integrable_davisElapsedOccupationCenteredResetSum_of_envelope
    S hflow P ξ hne initial g t ?_ henvelope
  intro N
  exact (hreg.measurable_stoppedElapsedOccupationCenteredResetSum
    (hf := hf) (hr := hr) hξ hne initial hg N t).aestronglyMeasurable

/-- Ambient fixed-time integrability implies integrability on every event,
without requiring the event itself to be measurable. -/
theorem DavisResetOccupationRegular.integrable_elapsedOccupationCenteredResetSum_restrict
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (initial : DavisState Q n)
    (hg : Measurable g) (t : ℝ≥0) (A : Set Ω)
    (henvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Integrable (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t) (P.restrict A) := by
  exact (@hreg.integrable_elapsedOccupationCenteredResetSum
    Q _ _ n m S hflow hf hr g Ω _ P ξ hξ hne initial hg t
    henvelope).restrict

/-- Integrable envelopes at two endpoints make the corresponding elapsed
occupation-centered increment integrable. -/
theorem DavisResetOccupationRegular.integrable_elapsedOccupationCenteredResetIncrement
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (initial : DavisState Q n)
    (hg : Measurable g) (s t : ℝ≥0)
    (hsenvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s) P)
    (htenvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Integrable (davisElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g s t) P := by
  have ht := @hreg.integrable_elapsedOccupationCenteredResetSum
    Q _ _ n m S hflow hf hr g Ω _ P ξ hξ hne initial hg t htenvelope
  have hs := @hreg.integrable_elapsedOccupationCenteredResetSum
    Q _ _ n m S hflow hf hr g Ω _ P ξ hξ hne initial hg s hsenvelope
  unfold davisElapsedOccupationCenteredResetIncrement
  simp only [davisElapsedOccupationCenteredResetProcess]
  exact ht.sub hs

/-- The same endpoint assumptions give integrability of the increment after
restriction to an arbitrary event. -/
theorem DavisResetOccupationRegular.integrable_elapsedOccupationCenteredResetIncrement_restrict
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (initial : DavisState Q n)
    (hg : Measurable g) (s t : ℝ≥0) (A : Set Ω)
    (hsenvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s) P)
    (htenvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Integrable (davisElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g s t) (P.restrict A) := by
  exact (@hreg.integrable_elapsedOccupationCenteredResetIncrement
    Q _ _ n m S hflow hf hr g Ω _ P ξ hξ hne initial hg s t
    hsenvelope htenvelope).restrict

end SHS
