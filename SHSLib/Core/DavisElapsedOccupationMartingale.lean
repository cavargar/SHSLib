import SHSLib.Core.DavisElapsedOccupationConditionalIncrement

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Martingale packaging for the elapsed occupation-centered reset process

The three ingredients developed so far — filtration observability
(adaptedness), fixed-time integrability, and zero conditional expectation of
every two-time increment — combine into the statement that the elapsed
occupation-centered reset process is a martingale.

The first theorem is the abstract packaging step.  The second instantiates it
from the deterministic-cap increment law together with reset-occupation
regularity and an integrable elapsed occupation envelope at every time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Adaptedness, fixed-time integrability, and vanishing conditional
increments make the elapsed occupation-centered reset process a martingale. -/
theorem martingale_davisElapsedOccupationCenteredResetProcess
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hadapted : StronglyAdapted filtration
      (davisElapsedOccupationCenteredResetProcess S hflow ξ hne initial g))
    (hint : ∀ t, Integrable
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g t) P)
    (hcond : ∀ s t, s ≤ t →
      P[davisElapsedOccupationCenteredResetIncrement
          S hflow ξ hne initial g s t | filtration s] =ᵐ[P] (0 : Ω → ℝ)) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) filtration P := by
  refine ⟨hadapted, ?_⟩
  intro s t hst
  have hsub : P[davisElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g s t | filtration s] =ᵐ[P]
      P[davisElapsedOccupationCenteredResetProcess
          S hflow ξ hne initial g t | filtration s] -
        P[davisElapsedOccupationCenteredResetProcess
          S hflow ξ hne initial g s | filtration s] := by
    have : davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g s t =
        (fun ω => davisElapsedOccupationCenteredResetProcess
            S hflow ξ hne initial g t ω -
          davisElapsedOccupationCenteredResetProcess
            S hflow ξ hne initial g s ω) := rfl
    rw [this]
    exact condExp_sub (hint t) (hint s) _
  have hself : P[davisElapsedOccupationCenteredResetProcess
      S hflow ξ hne initial g s | filtration s] =ᵐ[P]
      davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g s :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (filtration.le s) (hadapted s) (hint s))
  filter_upwards [hcond s t hst, hsub, hself] with ω h1 h2 h3
  simp only [Pi.zero_apply] at h1
  rw [h1] at h2
  simp only [Pi.sub_apply, h3] at h2
  linarith

/-- Concrete martingale property: observability, reset-occupation regularity
with integrable elapsed envelopes, and the deterministic-cap increment law
together make the elapsed occupation-centered reset process a martingale. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) filtration P := by
  refine martingale_davisElapsedOccupationCenteredResetProcess
    S hflow P filtration ξ hne initial g
    (fun t => (hobs.measurable_elapsed t).stronglyMeasurable) (fun t => ?_)
    (fun s t hst => ?_)
  · exact @hreg.integrable_elapsedOccupationCenteredResetSum
      Q _ _ n m S hflow hf hr g Ω _ P ξ hξ hne initial hg t (henv t)
  · have hint : Integrable (davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g s t) P :=
      @hreg.integrable_elapsedOccupationCenteredResetIncrement
        Q _ _ n m S hflow hf hr g Ω _ P ξ hξ hne initial hg s t
        (henv s) (henv t)
    exact hlaw.condExp_elapsed_eq_zero s t hst (filtration.le s) hint
      (fun A _ _ => ⟨(henv s).restrict, (henv t).restrict⟩)

end SHS
