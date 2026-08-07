import SHSLib.Core.DavisStoppedElapsedOccupationIncrementLaw

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Conditional cap removal for elapsed occupation increments

Deterministic-cap increment laws pass to the full elapsed process by dominated
convergence.  The dominating function is the sum of the two endpoint
envelopes.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Eventwise centering of every stopped increment passes to the full
increment when the two endpoint envelopes are integrable on the event. -/
theorem setIntegral_davisElapsedOccupationCenteredResetIncrement_eq_zero_of_law
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g)
    (s t : ℝ≥0) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[filtration s] A) (hAfin : P A < ⊤)
    (hsenvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s)
      (P.restrict A))
    (htenvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t)
      (P.restrict A)) :
    ∫ ω in A, davisElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g s t ω ∂P = 0 := by
  -- The dominating function is the sum of the two endpoint envelopes
  let bound : Ω → ℝ := fun ω => davisElapsedOccupationEnvelope S hflow ξ hne initial g s ω + davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω
  -- Pointwise convergence of stopped increments to full increment
  have htendsto : ∀ ω, Filter.Tendsto (fun N => davisStoppedElapsedOccupationCenteredResetIncrement S hflow ξ hne initial g N s t ω) Filter.atTop (nhds (davisElapsedOccupationCenteredResetIncrement S hflow ξ hne initial g s t ω)) := fun ω => tendsto_davisStoppedElapsedOccupationCenteredResetIncrement S hflow ξ hne initial g s t ω
  -- The bound holds for all stopped increments
  have hbound : ∀ N ω, |davisStoppedElapsedOccupationCenteredResetIncrement S hflow ξ hne initial g N s t ω| ≤ bound ω := by
    intro N ω
    unfold davisStoppedElapsedOccupationCenteredResetIncrement
    have ht := abs_davisStoppedElapsedOccupationCenteredResetSum_le_envelope S hflow ξ hne initial g N t ω
    have hs := abs_davisStoppedElapsedOccupationCenteredResetSum_le_envelope S hflow ξ hne initial g N s ω
    calc |davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g N t ω - davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g N s ω|
        ≤ |davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g N t ω| + |davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g N s ω| := abs_sub _ _
      _ ≤ davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω + davisElapsedOccupationEnvelope S hflow ξ hne initial g s ω := add_le_add ht hs
      _ = bound ω := add_comm _ _
  -- bound is integrable on A
  have hbound_integrable : Integrable bound (P.restrict A) := hsenvelope.add htenvelope
  -- For each N, the integral of the stopped increment is zero
  have hzero : ∀ N, ∫ ω in A, davisStoppedElapsedOccupationCenteredResetIncrement S hflow ξ hne initial g N s t ω ∂P = 0 := by
    intro N
    exact hlaw.centered_on_earlier_events N s t hst A hA hAfin
  -- Use dominated convergence to pass the limit
  have : Filter.Tendsto (fun N => ∫ ω in A, davisStoppedElapsedOccupationCenteredResetIncrement S hflow ξ hne initial g N s t ω ∂P) Filter.atTop (nhds (∫ ω in A, davisElapsedOccupationCenteredResetIncrement S hflow ξ hne initial g s t ω ∂P)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    · -- AEStronglyMeasurable for each N (from hlaw.integrable)
      exact Filter.Eventually.of_forall (fun N => (hlaw.integrable N s t).aestronglyMeasurable.restrict)
    · -- The bound holds eventually
      exact Filter.Eventually.of_forall (fun N => ae_of_all (P.restrict A) (fun ω => by simpa [Real.norm_eq_abs] using hbound N ω))
    · -- The bound is integrable
      exact hbound_integrable
    · -- Pointwise convergence
      exact Filter.Eventually.of_forall htendsto
  exact tendsto_nhds_unique this (by simp [hzero])

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Conditional cap removal: the full elapsed increment has zero conditional
expectation with respect to the earlier filtration. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.condExp_elapsed_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hle : filtration s ≤ mΩ) [SigmaFinite (P.trim hle)]
    (hint : Integrable (davisElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g s t) P)
    (henvelopes : ∀ A, MeasurableSet[filtration s] A → P A < ⊤ →
      Integrable (davisElapsedOccupationEnvelope
        S hflow ξ hne initial g s) (P.restrict A) ∧
      Integrable (davisElapsedOccupationEnvelope
        S hflow ξ hne initial g t) (P.restrict A)) :
    P[davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g s t | filtration s] =ᵐ[P]
      (0 : Ω → ℝ) := by
  have hcharacterize : (0 : Ω → ℝ) =ᵐ[P]
      P[davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g s t | filtration s] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hle hint
    · intro A hA hAfin
      exact integrableOn_zero
    · intro A hA hAfin
      rw [setIntegral_davisElapsedOccupationCenteredResetIncrement_eq_zero_of_law S hflow P filtration ξ hne initial g hlaw s t hst A hA hAfin (henvelopes A hA hAfin).1 (henvelopes A hA hAfin).2]
      simp
    · exact aestronglyMeasurable_zero
  exact hcharacterize.symm

end SHS
