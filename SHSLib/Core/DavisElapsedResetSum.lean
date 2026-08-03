import SHSLib.Core.DavisStoppedResetSum

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Full elapsed-time centered reset sums

This module removes the deterministic jump cap from the stopped reset sums.
An integrable completed-jump count supplies the common domination needed to
pass the zero-expectation identity to the uncapped sum.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The full elapsed-time sum has the finite-sum bound determined by the actual
number of jumps completed by time `t`. -/
theorem abs_davisElapsedCenteredResetSum_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (t : ℝ≥0) (ω : Ω) :
    |davisElapsedCenteredResetSum S hflow ξ hne initial g t ω| ≤
      (ξ.activeSegmentIndex hne t ω : ℝ) * (4 * C) := by
  unfold davisElapsedCenteredResetSum
  exact abs_davisFiniteCenteredResetSum_le S hflow ξ initial g C hg _ ω

/-- Every deterministic cap is dominated by the same random completed-jump
count bound.  This is the uniform envelope used for dominated convergence. -/
theorem abs_davisStoppedCenteredResetSum_le_activeSegmentIndex
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    |davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω| ≤
      (ξ.activeSegmentIndex hne t ω : ℝ) * (4 * C) := by
  unfold davisStoppedCenteredResetSum
  apply le_trans (abs_davisFiniteCenteredResetSum_le S hflow ξ initial g C hg _ ω)
  apply mul_le_mul_of_nonneg_right _ (by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    linarith [abs_nonneg (g initial), hg initial])
  norm_cast
  exact min_le_left _ _

/-- At fixed elapsed time, the uncapped centered reset sum is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.elapsedCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hg : Measurable g) (t : ℝ≥0) :
    Measurable (davisElapsedCenteredResetSum S hflow ξ hne initial g t) := by
  have hlim : ∀ ω, Filter.Tendsto (fun N => davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω) Filter.atTop (nhds (davisElapsedCenteredResetSum S hflow ξ hne initial g t ω)) :=
    fun ω => davisStoppedCenteredResetSum_tendsto_elapsed S hflow ξ hne initial g t ω
  refine measurable_of_tendsto_metrizable (fun N => stoppedCenteredResetSum S hflow hf hr hξ hne initial g hg N t) ?_
  exact tendsto_pi_nhds.mpr hlim

/-- Integrability of the completed-jump count implies integrability of the full
elapsed-time centered reset sum for every bounded measurable test function. -/
theorem DavisJumpNoise.MeasurableNoise.integrable_elapsedCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (t : ℝ≥0)
    (hcount : Integrable (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P) :
    Integrable (davisElapsedCenteredResetSum S hflow ξ hne initial g t) P := by
  have hmeas := DavisJumpNoise.MeasurableNoise.elapsedCenteredResetSum
    S hflow hf hr hξ hne initial g hgmeas t
  have hC_nonneg : 0 ≤ C := le_trans (abs_nonneg _) (hg initial)
  have hC_eq : C = |C| := (abs_of_nonneg hC_nonneg).symm
  have habsC_eq : abs (abs C) = |C| := abs_abs C
  have hbound : ∀ ω, |davisElapsedCenteredResetSum S hflow ξ hne initial g t ω| ≤
      (ξ.activeSegmentIndex hne t ω : ℝ) * (4 * |C|) := by
    intro ω
    exact le_trans (abs_davisElapsedCenteredResetSum_le S hflow ξ hne initial g C hg t ω)
      (by rw [hC_eq, habsC_eq])
  -- The bound function is integrable: constant times integrable
  have hbnd_int : Integrable (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ) * (4 * |C|)) P :=
    hcount.mul_const _
  refine MeasureTheory.Integrable.mono' hbnd_int ?_ ?_
  · exact hmeas.aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hbound ω

/-- Under an integrable completed-jump count, bounded optional stopping passes
from deterministic caps to the full elapsed-time centered reset sum. -/
theorem DavisJumpNoise.ConditionalChannelLaw.integral_elapsedCenteredResetSum_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (g : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (t : ℝ≥0)
    (hcount : Integrable (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P) :
    ∫ ω, davisElapsedCenteredResetSum S hflow ξ hne initial g t ω ∂P = 0 := by
  -- Use dominated convergence
  have hbound : ∀ N, ∀ ω, |davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω| ≤
      (ξ.activeSegmentIndex hne t ω : ℝ) * (4 * |C|) := by
    intro N ω
    exact abs_davisStoppedCenteredResetSum_le_activeSegmentIndex S hflow ξ hne initial g |C|
      (fun z => le_trans (hg z) (le_abs_self C)) N t ω
  -- The dominating function is integrable
  have hdom_int : Integrable (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ) * (4 * |C|)) P := by
    exact hcount.mul_const _
  -- Pointwise convergence
  have hconv : ∀ ω, Filter.Tendsto (fun N => davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω)
      Filter.atTop (nhds (davisElapsedCenteredResetSum S hflow ξ hne initial g t ω)) :=
    fun ω => davisStoppedCenteredResetSum_tendsto_elapsed S hflow ξ hne initial g t ω
  -- Apply dominated convergence theorem
  have hint_stopped : ∀ N, Integrable (davisStoppedCenteredResetSum S hflow ξ hne initial g N t) P := by
    intro N
    exact DavisJumpNoise.MeasurableNoise.integrable_stoppedCenteredResetSum S hflow hf hr hξ hne initial g hgmeas |C|
      (fun z => le_trans (hg z) (le_abs_self C)) N t
  -- Use dominated convergence
  have hdct := tendsto_integral_of_dominated_convergence
    (μ := P)
    (F := fun N => davisStoppedCenteredResetSum S hflow ξ hne initial g N t)
    (bound := fun ω => (ξ.activeSegmentIndex hne t ω : ℝ) * (4 * |C|))
    (F_measurable := fun N => (hint_stopped N).aestronglyMeasurable)
    (h_bound := fun N => Filter.Eventually.of_forall (hbound N))
    (bound_integrable := hdom_int)
    (h_lim := Filter.Eventually.of_forall hconv)
  -- Each stopped integral is zero
  have hint_zero : ∀ N, ∫ ω, davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω ∂P = 0 := by
    intro N
    exact DavisJumpNoise.ConditionalChannelLaw.integral_stoppedCenteredResetSum_eq_zero hf hr hξ hne hlaw g hgmeas |C|
      (fun z => le_trans (hg z) (le_abs_self C)) N t
  -- The limit of zeros is zero
  have htends_zero : Filter.Tendsto (fun N => ∫ ω, davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω ∂P)
      Filter.atTop (nhds 0) := by
    simp_rw [hint_zero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hdct htends_zero

end SHS
