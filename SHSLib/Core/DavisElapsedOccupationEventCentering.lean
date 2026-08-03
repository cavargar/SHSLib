import SHSLib.Core.DavisElapsedOccupationEnvelopeMeasurable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Event-localized fixed-time occupation centering

Dominated cap removal is stable under restriction to a measurable event.  This
is the set-integral form needed to pass from fixed-time centering to conditional
expectation and martingale statements.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Zero set integrals for every deterministic jump cap pass to the full
elapsed occupation-centered reset sum. -/
theorem setIntegral_davisElapsedOccupationCenteredResetSum_eq_zero_of_stopped
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (A : Set Ω)
    (hstopped : ∀ N, AEStronglyMeasurable
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) (P.restrict A))
    (henvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t)
      (P.restrict A))
    (hzero : ∀ N, ∫ ω in A,
      davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω ∂P = 0) :
    ∫ ω in A, davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t ω ∂P = 0 := by
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := P.restrict A)
    (F := fun N => davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g N t)
    (bound := davisElapsedOccupationEnvelope S hflow ξ hne initial g t)
    (F_measurable := fun N => hstopped N)
    (h_bound := fun N => Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_davisStoppedElapsedOccupationCenteredResetSum_le_envelope
        S hflow ξ hne initial g N t ω)
    (bound_integrable := henvelope)
    (h_lim := Filter.Eventually.of_forall fun ω => tendsto_davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g t ω)
  have htends_zero : Filter.Tendsto (fun N => ∫ ω in A, davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t ω ∂P) Filter.atTop (nhds 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hdct htends_zero

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Equivalent indicator form of event-localized centering. -/
theorem integral_indicator_davisElapsedOccupationCenteredResetSum_eq_zero_of_stopped
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet A)
    (hstopped : ∀ N, AEStronglyMeasurable
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) (P.restrict A))
    (henvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t)
      (P.restrict A))
    (hzero : ∀ N, ∫ ω in A,
      davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω ∂P = 0) :
    ∫ ω, A.indicator (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t) ω ∂P = 0 := by
  rw [MeasureTheory.integral_indicator hA]
  exact setIntegral_davisElapsedOccupationCenteredResetSum_eq_zero_of_stopped S hflow P ξ hne initial g t A hstopped henvelope hzero

end SHS
