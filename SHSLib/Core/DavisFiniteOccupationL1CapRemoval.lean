import SHSLib.Core.DavisFiniteOccupationEnvelope

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Finite `L¹` removal of duration caps

An abstract increasing family of deterministic duration caps is sufficient:
for each sample point, it need only eventually dominate the finitely many
holding times under consideration.  The cap-independent envelope from the
preceding module then permits dominated convergence.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Eventual domination of the first `N` holding times gives pointwise
convergence (indeed eventual equality) of capped and full finite sums. -/
theorem tendsto_davisFiniteCappedOccupationCenteredResetSum_of_eventually_holdingTime_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℕ → ℝ≥0) (N : ℕ) (ω : Ω)
    (hcap : ∀ᶠ j in Filter.atTop,
      ∀ k < N, ξ.holdingTime k ω ≤ cap j k) :
    Filter.Tendsto (fun j =>
      davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N ω) Filter.atTop
      (nhds (davisFiniteOccupationCenteredResetSum
        S hflow ξ initial g N ω)) := by
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [hcap] with j hj
  exact (davisFiniteCappedOccupationCenteredResetSum_eq_full_of_holdingTime_le
    S hflow ξ initial g (cap j) N ω hj).symm

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A common integrable envelope makes the full finite occupation-centered sum
integrable once the capped sums converge pointwise. -/
theorem integrable_davisFiniteOccupationCenteredResetSum_of_cap_envelope
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℕ → ℝ≥0) (N : ℕ)
    (bound : Ω → ℝ) (hbound : Integrable bound P)
    (hcapped : ∀ j, AEStronglyMeasurable
      (davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N) P)
    (hdom : ∀ j, ∀ᵐ ω ∂P,
      ‖davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N ω‖ ≤ bound ω)
    (hcap : ∀ ω, ∀ᶠ j in Filter.atTop,
      ∀ k < N, ξ.holdingTime k ω ≤ cap j k) :
    Integrable (davisFiniteOccupationCenteredResetSum
      S hflow ξ initial g N) P := by
  have htendsto : ∀ᵐ ω ∂P, Filter.Tendsto
      (fun j => davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N ω) Filter.atTop
      (nhds (davisFiniteOccupationCenteredResetSum
        S hflow ξ initial g N ω)) := by
    filter_upwards [MeasureTheory.ae_of_all P hcap] with ω hω
    exact tendsto_davisFiniteCappedOccupationCenteredResetSum_of_eventually_holdingTime_le
      S hflow ξ initial g (cap) N ω hω
  have hcapped_int : ∀ j, Integrable
      (davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N) P := by
    intro j
    refine Integrable.mono hbound (hcapped j) ?_
    filter_upwards [hdom j] with ω hω
    exact le_trans hω (le_abs_self _)
  -- The limit is AEStronglyMeasurable
  have hlim_meas : AEStronglyMeasurable
      (davisFiniteOccupationCenteredResetSum
        S hflow ξ initial g N) P := by
    exact aestronglyMeasurable_of_tendsto_ae Filter.atTop (fun j => hcapped j) htendsto
  -- Each term is bounded by |bound ω| a.e.
  have hall : ∀ᵐ ω ∂P, ∀ j, ‖davisFiniteCappedOccupationCenteredResetSum
      S hflow ξ initial g (cap j) N ω‖ ≤ |bound ω| := by
    have h1 : ∀ᵐ ω ∂P, ∀ j, ‖davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N ω‖ ≤ bound ω := by
      exact ae_all_iff.2 hdom
    filter_upwards [h1] with ω hω j
    exact le_trans (hω j) (le_abs_self _)
  -- Show the limit is also bounded by |bound|
  have hlim_bound : ∀ᵐ ω ∂P, ‖davisFiniteOccupationCenteredResetSum
      S hflow ξ initial g N ω‖ ≤ |bound ω| := by
    filter_upwards [htendsto, hall] with ω hω htall
    -- The sequence of norms converges to the norm of the limit
    have hnorm_conv : Filter.Tendsto (fun j => ‖davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N ω‖) Filter.atTop (nhds ‖davisFiniteOccupationCenteredResetSum
        S hflow ξ initial g N ω‖) := hω.norm
    exact le_of_tendsto hnorm_conv (Filter.Eventually.of_forall htall)
  refine hbound.abs.mono hlim_meas ?_
  filter_upwards [hlim_bound] with ω hω
  exact le_trans hω (le_abs_self _)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Dominated convergence transfers the zero-expectation identity from every
finite duration cap to the full finite occupation-centered sum. -/
theorem integral_davisFiniteOccupationCenteredResetSum_eq_zero_of_caps
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℕ → ℝ≥0) (N : ℕ)
    (bound : Ω → ℝ) (hbound : Integrable bound P)
    (hcapped : ∀ j, AEStronglyMeasurable
      (davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N) P)
    (hdom : ∀ j, ∀ᵐ ω ∂P,
      ‖davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N ω‖ ≤ bound ω)
    (hzero : ∀ j, ∫ ω, davisFiniteCappedOccupationCenteredResetSum
      S hflow ξ initial g (cap j) N ω ∂P = 0)
    (hcap : ∀ ω, ∀ᶠ j in Filter.atTop,
      ∀ k < N, ξ.holdingTime k ω ≤ cap j k) :
    ∫ ω, davisFiniteOccupationCenteredResetSum
      S hflow ξ initial g N ω ∂P = 0 := by
  have htendsto : ∀ ω, Filter.Tendsto
      (fun j => davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N ω) Filter.atTop
      (nhds (davisFiniteOccupationCenteredResetSum
        S hflow ξ initial g N ω)) := fun ω =>
    tendsto_davisFiniteCappedOccupationCenteredResetSum_of_eventually_holdingTime_le
      S hflow ξ initial g cap N ω (hcap ω)
  have hintegral := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F_measurable := hcapped)
    (bound_integrable := hbound)
    (h_bound := hdom)
    (h_lim := Filter.Eventually.of_forall htendsto)
  have hzero_tendsto : Filter.Tendsto
      (fun j => ∫ ω, davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (cap j) N ω ∂P) Filter.atTop (nhds 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hintegral hzero_tendsto

end SHS
