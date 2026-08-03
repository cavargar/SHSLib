import SHSLib.Core.DavisFiniteResetMartingale

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Centered reset sums stopped at elapsed time

This module connects the discrete jump-index martingale to elapsed time.  The
active segment index is exactly the number of resets completed by time `t`.
Capping that index by `N` gives a bounded stopping rule and hence a finite
centered reset sum suitable for localization.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The centered reset sum accumulated by elapsed time `t`, capped after `N`
completed jumps. -/
def davisStoppedCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisFiniteCenteredResetSum S hflow ξ initial g
    (min (ξ.activeSegmentIndex hne t ω) N) ω

/-- A bounded stopped reset sum is the sum of the first `N` centered
increments whose reset times have occurred by `t`. -/
theorem davisStoppedCenteredResetSum_eq_sum_indicator
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω =
      ∑ k ∈ Finset.range N,
        if ξ.jumpTime (k + 1) ω ≤ t then
          davisCenteredResetIncrement S hflow ξ initial g k ω else 0 := by
  unfold davisStoppedCenteredResetSum
  rw [davisFiniteCenteredResetSum]
  have h : ∀ k : ℕ, ξ.jumpTime (k + 1) ω ≤ t ↔
      k < ξ.activeSegmentIndex hne t ω := by
    intro k
    rw [ξ.jumpTime_le_iff_le_activeSegmentIndex hne (k + 1) t ω]
    exact ⟨Nat.lt_of_succ_le, Nat.succ_le_of_lt⟩
  simp_rw [h]
  have hfilter :
      Finset.filter (fun k => k < ξ.activeSegmentIndex hne t ω) (Finset.range N) =
        Finset.range (min (ξ.activeSegmentIndex hne t ω) N) := by
    ext k
    simp [Finset.mem_filter, Finset.mem_range]
    tauto
  conv_rhs => rw [← Finset.sum_filter]
  rw [hfilter]

/-- For fixed elapsed time and jump cap, the stopped centered reset sum is an
ambient measurable random variable. -/
theorem DavisJumpNoise.MeasurableNoise.stoppedCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hg : Measurable g) (N : ℕ) (t : ℝ≥0) :
    Measurable (davisStoppedCenteredResetSum S hflow ξ hne initial g N t) := by
  rw [show (davisStoppedCenteredResetSum S hflow ξ hne initial g N t) =
      (fun ω => ∑ k ∈ Finset.range N,
        if ξ.jumpTime (k + 1) ω ≤ t then
          davisCenteredResetIncrement S hflow ξ initial g k ω else 0) by
    funext ω
    exact davisStoppedCenteredResetSum_eq_sum_indicator
      S hflow ξ hne initial g N t ω]
  apply Finset.measurable_sum
  intro k _
  apply Measurable.ite
  · have hset : {ω | ξ.jumpTime (k + 1) ω ≤ t} =
        (ξ.jumpTime (k + 1)) ⁻¹' Set.Iic t := rfl
    rw [hset]
    exact measurableSet_Iic.preimage (hξ.jumpTime (k + 1))
  · exact Measurable.mono
      (DavisJumpNoise.centeredResetIncrement_measurable_history_succ
        S hflow hf hr ξ initial g hg k)
      (hξ.preJumpHistorySpace_le S hflow hf hr initial (k + 1)) le_rfl
  · exact measurable_const

/-- The stopped sum obeys the same deterministic `4 C`-per-jump bound as a
fixed finite sum. -/
theorem abs_davisStoppedCenteredResetSum_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    |davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω| ≤
      (N : ℝ) * (4 * C) := by
  unfold davisStoppedCenteredResetSum
  apply le_trans
    (abs_davisFiniteCenteredResetSum_le S hflow ξ initial g C hg _ ω)
  have hC_nonneg : (0 : ℝ) ≤ C := by
    linarith [abs_nonneg (g initial), hg initial]
  apply mul_le_mul_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4 * C)
  norm_cast
  exact min_le_right _ _

/-- On a finite measure space, every bounded-jump stopped reset sum of a
bounded measurable test function is integrable. -/
theorem DavisJumpNoise.MeasurableNoise.integrable_stoppedCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (N : ℕ) (t : ℝ≥0) :
    Integrable (davisStoppedCenteredResetSum S hflow ξ hne initial g N t) P := by
  have hmeas := stoppedCenteredResetSum S hflow hf hr hξ hne initial g hgmeas N t
  exact Integrable.of_bound hmeas.aestronglyMeasurable ((N : ℝ) * 4 * |C|)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      have hbound := abs_davisStoppedCenteredResetSum_le S hflow ξ hne initial g |C|
        (fun z => le_trans (hg z) (le_abs_self C)) N t ω
      linarith)

/-- Whether reset `k + 1` has occurred by `t` is known immediately before
sampling channel `k`: its cumulative time uses the completed history and the
newly revealed holding time, but not that channel. -/
theorem DavisJumpNoise.jumpTime_succ_le_measurable_preChannel
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) (t : ℝ≥0) :
    MeasurableSet[ξ.preChannelSpace S hflow initial k]
      {ω | ξ.jumpTime (k + 1) ω ≤ t} := by
  -- jumpTime (k + 1) = jumpTime k + holdingTime k
  -- jumpTime k is determined by the pre-jump-history at k
  -- holdingTime k is directly available in pre-channel-space
  
  -- Define the function that computes jumpTime (k + 1) from (history, holdingTime k)
  let f : DavisPreJumpHistory Q n m k × ℝ≥0 → ℝ≥0 := fun ⟨H, u⟩ => 
    (∑ i : Fin k, H.holdingTime i) + u
  
  have hf_meas : Measurable f := by
    apply Measurable.add
    · apply Finset.measurable_sum
      intro i _
      show Measurable (fun p : DavisPreJumpHistory Q n m k × ℝ≥0 => p.1.holdingTime i)
      have : Measurable (fun p : DavisPreJumpHistory Q n m k × ℝ≥0 => p.1.holdingTime i) := by
        have h1 : Measurable (fun H : DavisPreJumpHistory Q n m k => H.holdingTime i) := by
          rw [measurable_iff_comap_le, DavisPreJumpHistory.instMeasurableSpace]
          show MeasurableSpace.comap (fun (H : DavisPreJumpHistory Q n m k) => H.holdingTime i) NNReal.measurableSpace ≤
            MeasurableSpace.comap (fun (H : DavisPreJumpHistory Q n m k) => (H.holdingTime, H.channel, H.stateAfterJump)) inferInstance
          have heq : (fun H : DavisPreJumpHistory Q n m k => H.holdingTime i) =
            (fun p : (Fin k → ℝ≥0) × (Fin k → Fin m) × (Fin (k + 1) → DavisState Q n) => p.1 i) ∘ (fun H : DavisPreJumpHistory Q n m k => (H.holdingTime, H.channel, H.stateAfterJump)) := rfl
          rw [heq, ← MeasurableSpace.comap_comp]
          apply MeasurableSpace.comap_mono
          have : Measurable fun p : (Fin k → ℝ≥0) × (Fin k → Fin m) × (Fin (k + 1) → DavisState Q n) => p.1 i :=
            (measurable_pi_apply i : Measurable fun a : Fin k → ℝ≥0 => a i).comp measurable_fst
          rw [measurable_iff_comap_le] at this
          exact this
        exact h1.comp measurable_fst
      exact this
    · exact measurable_snd
  
  have h_jumpTime_eq : ∀ j : ℕ, (hj : j ≤ k) → ∀ ω, ξ.jumpTime j ω = ∑ i : Fin j, (davisPreJumpHistory S hflow ξ initial k ω).holdingTime (Fin.castLE hj i) := by
    intro j hj ω
    induction j with
    | zero => simp [ξ.jumpTime_zero]
    | succ j ih =>
      rw [ξ.jumpTime_succ]
      rw [ih (Nat.le_of_succ_le hj), Fin.sum_univ_castSucc]
      simp [davisPreJumpHistory_holdingTime]
  
  have h_eq : (fun ω => ξ.jumpTime (k + 1) ω) = f ∘ (fun ω => (davisPreJumpHistory S hflow ξ initial k ω, ξ.holdingTime k ω)) := by
    funext ω
    simp only [f, Function.comp_apply]
    rw [ξ.jumpTime_succ]
    congr 1
    exact h_jumpTime_eq k (le_refl k) ω

  have h_mem : {ω | ξ.jumpTime (k + 1) ω ≤ t} = (f ∘ fun ω => (davisPreJumpHistory S hflow ξ initial k ω, ξ.holdingTime k ω)) ⁻¹' Set.Iic t := by
    ext ω
    simp only [Set.mem_setOf_eq, Function.comp_apply, Set.mem_preimage, Set.mem_Iic]
    have := congrFun h_eq ω
    simp only [Function.comp_apply] at this
    rw [this]
  rw [h_mem]
  rw [Set.preimage_comp]
  exact MeasurableSpace.measurableSet_comap.mpr ⟨f ⁻¹' Set.Iic t, hf_meas measurableSet_Iic, rfl⟩

/-- A predictable occurrence indicator times one centered reset increment
has expectation zero. -/
theorem DavisJumpNoise.ConditionalChannelLaw.integral_occurred_mul_centeredResetIncrement_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (g : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (k : ℕ) (t : ℝ≥0) :
    ∫ ω, (if ξ.jumpTime (k + 1) ω ≤ t then
      davisCenteredResetIncrement S hflow ξ initial g k ω else 0) ∂P = 0 := by
  -- Rewrite as set integral
  have h_eq : (fun ω => if ξ.jumpTime (k + 1) ω ≤ t then
      davisCenteredResetIncrement S hflow ξ initial g k ω else 0) =
      Set.indicator {ω | ξ.jumpTime (k + 1) ω ≤ t}
        (davisCenteredResetIncrement S hflow ξ initial g k) := by
    ext ω; simp [Set.indicator]
  rw [h_eq]
  -- The centered increment has conditional expectation zero
  have h_cond := condExp_centeredResetIncrement hf hr hξ hlaw g hgmeas C hg k
  -- Integrability of centered increment
  have h_int : Integrable (davisCenteredResetIncrement S hflow ξ initial g k) P := by
    apply Integrable.mono' (integrable_const (4 * C))
    · exact (hξ.centeredResetIncrement S hflow hf hr initial g hgmeas k).aestronglyMeasurable
    · filter_upwards with ω
      exact abs_davisCenteredResetIncrement_le S hflow ξ initial g C hg k ω
  -- The set is measurable with respect to preChannelSpace (and hence also mΩ)
  have h_le : ξ.preChannelSpace S hflow initial k ≤ mΩ :=
    hξ.preChannelSpace_le S hflow hf hr initial k
  -- Use setIntegral_condExp: ∫_A E[X|G] = ∫_A X
  have h_set_int := MeasureTheory.setIntegral_condExp
    (μ := P) (hm := hξ.preChannelSpace_le S hflow hf hr initial k)
    (hf := h_int) (hs := jumpTime_succ_le_measurable_preChannel S hflow ξ initial k t)
  -- Rewrite indicator integral as set integral
  have h_indicator : integral P ({ω | ξ.jumpTime (k + 1) ω ≤ t}.indicator
      (davisCenteredResetIncrement S hflow ξ initial g k)) =
      ∫ ω in {ω | ξ.jumpTime (k + 1) ω ≤ t}, davisCenteredResetIncrement S hflow ξ initial g k ω ∂P := by
    have h_meas := jumpTime_succ_le_measurable_preChannel S hflow ξ initial k t
    obtain ⟨s', hs'_meas, hs'_eq⟩ := h_meas
    have h_m : MeasurableSet {ω | ξ.jumpTime (k + 1) ω ≤ t} := h_le _ ⟨s', hs'_meas, hs'_eq⟩
    exact MeasureTheory.integral_indicator h_m
  rw [h_indicator]
  -- Rewrite using h_cond: ∫_A X = ∫_A E[X|G] = ∫_A 0 = 0
  rw [← h_set_int]
  rw [MeasureTheory.integral_congr_ae (h_cond.restrict)]
  simp

/-- Bounded optional stopping for the reset martingale: the expected centered
reset sum accumulated by time `t` and capped at `N` jumps is zero. -/
theorem DavisJumpNoise.ConditionalChannelLaw.integral_stoppedCenteredResetSum_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (g : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (N : ℕ) (t : ℝ≥0) :
    ∫ ω, davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω ∂P = 0 := by
  -- Rewrite stopped sum as finite sum of indicators times centered increments
  simp_rw [davisStoppedCenteredResetSum_eq_sum_indicator S hflow ξ hne initial g N t]
  -- Apply linearity: integral of sum = sum of integrals
  rw [integral_finset_sum]
  · -- Each term has integral zero
    exact Finset.sum_eq_zero fun k _ => integral_occurred_mul_centeredResetIncrement_eq_zero hf hr hξ hlaw g hgmeas C hg k t
  · -- Integrability: each term is bounded, hence integrable
    intro k _
    apply Integrable.mono' (integrable_const (4 * |C|))
    · exact ((hξ.centeredResetIncrement S hflow hf hr initial g hgmeas k).indicator
        (hξ.preChannelSpace_le S hflow hf hr initial k _
          (jumpTime_succ_le_measurable_preChannel S hflow ξ initial k t))).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs]
      split_ifs with h
      · exact abs_davisCenteredResetIncrement_le S hflow ξ initial g |C|
          (fun z => le_trans (hg z) (le_abs_self C)) k ω
      · simp only [abs_zero]
        linarith [abs_nonneg C]

/-- The uncapped elapsed-time reset sum.  Non-explosion makes the number of
completed jumps finite at every finite elapsed time. -/
def davisElapsedCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisFiniteCenteredResetSum S hflow ξ initial g
    (ξ.activeSegmentIndex hne t ω) ω

/-- Once the cap exceeds the number of completed jumps, the stopped sum equals
the uncapped elapsed-time sum. -/
theorem davisStoppedCenteredResetSum_eq_elapsed_of_activeSegmentIndex_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω)
    (hN : ξ.activeSegmentIndex hne t ω ≤ N) :
    davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω =
      davisElapsedCenteredResetSum S hflow ξ hne initial g t ω := by
  simp [davisStoppedCenteredResetSum, davisElapsedCenteredResetSum, min_eq_left hN]

/-- At every sample point and finite elapsed time, bounded-jump stopped sums
are eventually equal to the full elapsed-time centered reset sum. -/
theorem davisStoppedCenteredResetSum_tendsto_elapsed
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    Filter.Tendsto
      (fun N => davisStoppedCenteredResetSum S hflow ξ hne initial g N t ω)
      Filter.atTop
      (nhds (davisElapsedCenteredResetSum S hflow ξ hne initial g t ω)) := by
  let k := ξ.activeSegmentIndex hne t ω
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.Ici_mem_atTop k] with N hN
  exact (davisStoppedCenteredResetSum_eq_elapsed_of_activeSegmentIndex_le S hflow ξ hne initial g N t ω hN).symm

end SHS
