import SHSLib.Core.DavisElapsedOccupationIncrement

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Event-localized centering of elapsed occupation increments

Zero event integrals at two fixed times imply a zero event integral for the
corresponding process increment.  Combining this elementary subtraction step
with fixed-time cap removal gives a reusable two-endpoint criterion stated
entirely in terms of deterministic jump-capped approximations.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Integrable, event-centered endpoint values have an event-centered
increment. -/
theorem setIntegral_davisElapsedOccupationCenteredResetIncrement_eq_zero_of_endpoints
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (s t : ℝ≥0) (A : Set Ω)
    (hsint : Integrable (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g s) (P.restrict A))
    (htint : Integrable (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t) (P.restrict A))
    (hszero : ∫ ω in A, davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g s ω ∂P = 0)
    (htzero : ∫ ω in A, davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t ω ∂P = 0) :
    ∫ ω in A, davisElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g s t ω ∂P = 0 := by
  simp only [davisElapsedOccupationCenteredResetIncrement,
             davisElapsedOccupationCenteredResetProcess]
  rw [integral_sub htint hsint, htzero, hszero, zero_sub, neg_zero]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- If all deterministic jump-capped endpoint approximations are centered on
an event and each endpoint has an integrable envelope there, then the full
elapsed process increment is centered on that event. -/
theorem setIntegral_davisElapsedOccupationCenteredResetIncrement_eq_zero_of_stopped
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (s t : ℝ≥0) (A : Set Ω)
    (hsmeas : ∀ N, AEStronglyMeasurable
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s) (P.restrict A))
    (htmeas : ∀ N, AEStronglyMeasurable
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) (P.restrict A))
    (hsenvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s)
      (P.restrict A))
    (htenvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t)
      (P.restrict A))
    (hszero : ∀ N, ∫ ω in A,
      davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s ω ∂P = 0)
    (htzero : ∀ N, ∫ ω in A,
      davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω ∂P = 0) :
    ∫ ω in A, davisElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g s t ω ∂P = 0 := by
  -- Get integrability at time s
  have hsint : Integrable (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g s) (P.restrict A) :=
    integrable_davisElapsedOccupationCenteredResetSum_of_envelope
      S hflow (P.restrict A) ξ hne initial g s (fun N => hsmeas N) hsenvelope
  -- Get integrability at time t
  have htint : Integrable (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t) (P.restrict A) :=
    integrable_davisElapsedOccupationCenteredResetSum_of_envelope
      S hflow (P.restrict A) ξ hne initial g t (fun N => htmeas N) htenvelope
  -- Get that the integral at time s is zero
  have hszero' : ∫ ω in A, davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g s ω ∂P = 0 :=
    setIntegral_davisElapsedOccupationCenteredResetSum_eq_zero_of_stopped
      S hflow P ξ hne initial g s A (fun N => hsmeas N) hsenvelope hszero
  -- Get that the integral at time t is zero
  have htzero' : ∫ ω in A, davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t ω ∂P = 0 :=
    setIntegral_davisElapsedOccupationCenteredResetSum_eq_zero_of_stopped
      S hflow P ξ hne initial g t A (fun N => htmeas N) htenvelope htzero
  -- Apply the endpoint theorem
  exact setIntegral_davisElapsedOccupationCenteredResetIncrement_eq_zero_of_endpoints
    S hflow P ξ hne initial g s t A hsint htint hszero' htzero'

end SHS
