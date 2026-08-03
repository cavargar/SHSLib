import SHSLib.Core.DavisFiniteOccupationL1CapRemoval

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Natural-number duration caps

The abstract finite cap-removal results are specialized to the constant cap
`j` on every segment.  The Archimedean property makes these caps eventually
dominate any fixed finite collection of sampled holding times.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The constant duration cap associated with a natural number. -/
def davisNaturalDurationCap (j : ℕ) : ℕ → ℝ≥0 :=
  fun _ => j

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Constant natural-number caps eventually dominate the first `N` sampled
holding times at every sample point. -/
theorem DavisJumpNoise.eventually_holdingTime_le_naturalDurationCap
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (N : ℕ) (ω : Ω) :
    ∀ᶠ j in Filter.atTop,
      ∀ k < N, ξ.holdingTime k ω ≤ davisNaturalDurationCap j k := by
  rw [Filter.eventually_atTop]
  simp [davisNaturalDurationCap]
  by_cases hN : N = 0
  · simp [hN]
  · -- N > 0, so we have finitely many holding times to bound
    -- For each k < N, the holding time is some ℝ≥0 value
    -- We need to find j large enough to exceed all of them
    let S : Finset ℕ := Finset.range N
    have hS : ∀ k < N, k ∈ S := fun k hk => Finset.mem_range.mpr hk
    let M : ℝ≥0 := sSup ((fun k => ξ.holdingTime k ω) '' S)
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, M ≤ J := by
      have := Archimedean.arch (M : ℝ) one_pos
      rcases this with ⟨J, hJ⟩
      simp [mul_one] at hJ
      exact ⟨J, NNReal.coe_le_coe.mpr hJ⟩
    refine ⟨J, fun j hj => ?_⟩
    intro k hk
    calc ξ.holdingTime k ω ≤ M := by
           apply le_csSup
           · exact Set.Finite.bddAbove (Set.toFinite _)
           · exact Set.mem_image_of_mem _ (hS k hk)
         _ ≤ J := hJ
         _ ≤ j := mod_cast hj

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Finite occupation-centered sums with constant natural duration caps
converge pointwise to the corresponding full finite sum. -/
theorem tendsto_davisFiniteNaturalCappedOccupationCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) :
    Filter.Tendsto (fun j =>
      davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (davisNaturalDurationCap j) N ω)
      Filter.atTop
      (nhds (davisFiniteOccupationCenteredResetSum
        S hflow ξ initial g N ω)) := by
  have hcap : ∀ᶠ j in Filter.atTop,
      ∀ k < N, ξ.holdingTime k ω ≤ davisNaturalDurationCap j k :=
    DavisJumpNoise.eventually_holdingTime_le_naturalDurationCap ξ N ω
  exact tendsto_davisFiniteCappedOccupationCenteredResetSum_of_eventually_holdingTime_le
    S hflow ξ initial g (davisNaturalDurationCap) N ω hcap

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Dominated convergence for the concrete constant natural-number caps
transfers their zero-expectation identities to the full finite sum. -/
theorem integral_davisFiniteOccupationCenteredResetSum_eq_zero_of_naturalCaps
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ)
    (bound : Ω → ℝ) (hbound : Integrable bound P)
    (hcapped : ∀ j, AEStronglyMeasurable
      (davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (davisNaturalDurationCap j) N) P)
    (hdom : ∀ j, ∀ᵐ ω ∂P,
      ‖davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (davisNaturalDurationCap j) N ω‖ ≤ bound ω)
    (hzero : ∀ j, ∫ ω, davisFiniteCappedOccupationCenteredResetSum
      S hflow ξ initial g (davisNaturalDurationCap j) N ω ∂P = 0) :
    ∫ ω, davisFiniteOccupationCenteredResetSum
      S hflow ξ initial g N ω ∂P = 0 := by
  have hcap : ∀ ω, ∀ᶠ j in Filter.atTop,
      ∀ k < N, ξ.holdingTime k ω ≤ davisNaturalDurationCap j k := fun ω =>
    DavisJumpNoise.eventually_holdingTime_le_naturalDurationCap ξ N ω
  have htendsto : ∀ ω, Filter.Tendsto
      (fun j => davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (davisNaturalDurationCap j) N ω) Filter.atTop
      (nhds (davisFiniteOccupationCenteredResetSum
        S hflow ξ initial g N ω)) := fun ω =>
    tendsto_davisFiniteCappedOccupationCenteredResetSum_of_eventually_holdingTime_le
      S hflow ξ initial g (davisNaturalDurationCap) N ω (hcap ω)
  have hintegral := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F_measurable := hcapped)
    (bound_integrable := hbound)
    (h_bound := hdom)
    (h_lim := Filter.Eventually.of_forall htendsto)
  have hzero_tendsto : Filter.Tendsto
      (fun j => ∫ ω, davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g (davisNaturalDurationCap j) N ω ∂P) Filter.atTop (nhds 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hintegral hzero_tendsto

end SHS
