import SHSLib.Core.DavisStoppedElapsedOccupationIncrement

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Conditional law interface for stopped elapsed occupation increments

This module records the precise eventwise compensation statement supplied by
segmentwise holding-time and channel laws.  It then converts that statement to
a conditional-expectation identity for every deterministic jump cap.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Eventwise conditional centering and integrability of every deterministic
jump-capped elapsed occupation increment. -/
structure DavisStoppedElapsedOccupationIncrementLaw
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) : Prop where
  integrable : ∀ N s t,
    Integrable (davisStoppedElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g N s t) P
  centered_on_earlier_events : ∀ N s t, s ≤ t → ∀ A,
    MeasurableSet[filtration s] A → P A < ⊤ →
      ∫ ω in A, davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t ω ∂P = 0

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The stopped increment law is equivalently available as a zero conditional
expectation at every deterministic cap. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.condExp_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g)
    (N : ℕ) (s t : ℝ≥0) (hst : s ≤ t)
    (hle : filtration s ≤ mΩ) [SigmaFinite (P.trim hle)] :
    P[davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t | filtration s] =ᵐ[P]
      (0 : Ω → ℝ) := by
  apply condExp_davisStoppedElapsedOccupationCenteredResetIncrement_eq_zero S hflow P filtration ξ hne initial g N s t hle
  exact hlaw.integrable N s t
  exact fun A hA hAfin => hlaw.centered_on_earlier_events N s t hst A hA hAfin

end SHS
