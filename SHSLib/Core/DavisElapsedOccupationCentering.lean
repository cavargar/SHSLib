import SHSLib.Core.DavisStoppedElapsedOccupationEnvelope

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Full fixed-time occupation centering

Dominated convergence removes the deterministic jump cap from the elapsed
occupation-centered reset sums.  The cap-independent envelope constructed in
the preceding module supplies both integrability of the limit and convergence
of expectations.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- An integrable common envelope makes the full elapsed occupation-centered
reset sum integrable. -/
theorem integrable_davisElapsedOccupationCenteredResetSum_of_envelope
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0)
    (hstopped : ∀ N, AEStronglyMeasurable
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) P)
    (henvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Integrable (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t) P := by
  -- First show the full sum is bounded by the envelope
  have hbdd : ∀ ω, ‖davisElapsedOccupationCenteredResetSum S hflow ξ hne initial g t ω‖ ≤
      davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω := by
    intro ω
    rw [Real.norm_eq_abs]
    -- The stopped sum equals the full sum for large enough N
    let k := ξ.activeSegmentIndex hne t ω
    have heq := davisStoppedElapsedOccupationCenteredResetSum_eq_elapsed_of_activeSegmentIndex_lt
      S hflow ξ hne initial g (k + 1) t ω (Nat.lt_add_one k)
    rw [← heq]
    exact abs_davisStoppedElapsedOccupationCenteredResetSum_le_envelope
      S hflow ξ hne initial g (k + 1) t ω
  -- The function is AE-strongly measurable as a pointwise limit
  have hmeas : AEStronglyMeasurable
      (davisElapsedOccupationCenteredResetSum S hflow ξ hne initial g t) P := by
    -- Use that it's the limit of the stopped sums
    have htendsto : ∀ ω, Filter.Tendsto (fun N =>
        davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g N t ω)
      Filter.atTop (nhds (davisElapsedOccupationCenteredResetSum S hflow ξ hne initial g t ω)) :=
      tendsto_davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g t
    exact aestronglyMeasurable_of_tendsto_ae _
      (fun N => hstopped N) (Filter.Eventually.of_forall htendsto)
  -- Use dominated convergence to get integrability
  exact MeasureTheory.Integrable.mono' henvelope hmeas (Filter.Eventually.of_forall hbdd)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- If every deterministic jump-capped approximation has expectation zero,
then the full fixed-time occupation-centered reset sum also has expectation
zero. -/
theorem integral_davisElapsedOccupationCenteredResetSum_eq_zero_of_stopped
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0)
    (hstopped : ∀ N, AEStronglyMeasurable
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) P)
    (henvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P)
    (hzero : ∀ N, ∫ ω,
      davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω ∂P = 0) :
    ∫ ω, davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t ω ∂P = 0 := by
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := P)
    (F := fun N => davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g N t)
    (bound := davisElapsedOccupationEnvelope S hflow ξ hne initial g t)
    (F_measurable := fun N => hstopped N)
    (h_bound := fun N => Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_davisStoppedElapsedOccupationCenteredResetSum_le_envelope
        S hflow ξ hne initial g N t ω)
    (bound_integrable := henvelope)
    (h_lim := Filter.Eventually.of_forall fun ω => tendsto_davisStoppedElapsedOccupationCenteredResetSum S hflow ξ hne initial g t ω)
  have htends_zero : Filter.Tendsto (fun N => ∫ ω, davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t ω ∂P) Filter.atTop (nhds 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hdct htends_zero

end SHS
