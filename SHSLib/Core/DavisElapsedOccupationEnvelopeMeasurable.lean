import SHSLib.Core.DavisElapsedOccupationEnvelopeIntegrable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Measurability of the elapsed occupation envelope

The full envelope is obtained as the eventually constant limit of deterministic
jump-capped envelopes.  Each capped envelope is a fixed finite sum selected by
measurable comparisons with the active segment index.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A deterministic jump-capped version of the fixed-time occupation envelope. -/
def davisStoppedElapsedOccupationEnvelope (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  let k := ξ.activeSegmentIndex hne t ω
  (∑ i ∈ Finset.range (min N k),
      |davisRealizedResetIncrement S hflow ξ initial g i ω|) +
    (∑ i ∈ Finset.range (min N k),
      |davisSampledResetOccupationCompensator S hflow g ξ initial i ω|) +
    if k < N then
      |davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial k ω)
        (t - ξ.jumpTime k ω)|
    else 0

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Once the deterministic cap exceeds the active segment index, the capped
and full envelopes agree pointwise. -/
theorem davisStoppedElapsedOccupationEnvelope_eq_elapsed_of_activeSegmentIndex_lt
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω)
    (hk : ξ.activeSegmentIndex hne t ω < N) :
    davisStoppedElapsedOccupationEnvelope
      S hflow ξ hne initial g N t ω =
      davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω := by
  unfold davisStoppedElapsedOccupationEnvelope
  unfold davisElapsedOccupationEnvelope
  simp [hk, min_eq_right hk.le]

/-- Every deterministic jump-capped elapsed occupation envelope is measurable
under the standard flow, reset, noise, and occupation regularity assumptions. -/
theorem DavisResetOccupationRegular.measurable_stoppedElapsedOccupationEnvelope
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g)
    (N : ℕ) (t : ℝ≥0) :
    Measurable (davisStoppedElapsedOccupationEnvelope
      S hflow ξ hne initial g N t) := by
  unfold davisStoppedElapsedOccupationEnvelope
  let k : Ω → ℕ := fun ω => ξ.activeSegmentIndex hne t ω
  have hk : Measurable k := hξ.activeSegmentIndex hne t
  have hmin : Measurable (fun ω => min N (k ω)) := (measurable_const).min hk
  -- Rewrite sum of |davisRealizedResetIncrement| using sum_filter
  have sum_inc_eq : ∀ ω, (∑ i ∈ Finset.range (min N (k ω)),
      |davisRealizedResetIncrement S hflow ξ initial g i ω|) =
      ∑ i ∈ Finset.range N, (if i < k ω then |davisRealizedResetIncrement S hflow ξ initial g i ω| else 0) := by
    intro ω
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp [Finset.mem_range, Finset.mem_filter]
  -- Rewrite sum of |davisSampledResetOccupationCompensator| using sum_filter
  have sum_occ_eq : ∀ ω, (∑ i ∈ Finset.range (min N (k ω)),
      |davisSampledResetOccupationCompensator S hflow g ξ initial i ω|) =
      ∑ i ∈ Finset.range N, (if i < k ω then |davisSampledResetOccupationCompensator S hflow g ξ initial i ω| else 0) := by
    intro ω
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp [Finset.mem_range, Finset.mem_filter]
  -- Rewrite conditional segment as sum with indicator
  have seg_eq : ∀ ω, (if k ω < N then
      |davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial (k ω) ω)
        (t - ξ.jumpTime (k ω) ω)|
      else 0) =
      ∑ i ∈ Finset.range N, (if i = k ω then
        |davisSegmentResetOccupationCompensator S hflow g
          (davisStateAfterJump S hflow ξ initial i ω)
          (t - ξ.jumpTime i ω)|
        else 0) := by
    intro ω
    by_cases h : k ω < N
    · rw [Finset.sum_ite_eq']
      simp [h]
    · simp [h]
  -- Combine everything
  have goal_eq : (fun ω => (∑ i ∈ Finset.range (min N (k ω)), |davisRealizedResetIncrement S hflow ξ initial g i ω|) +
      (∑ i ∈ Finset.range (min N (k ω)), |davisSampledResetOccupationCompensator S hflow g ξ initial i ω|) +
      if k ω < N then |davisSegmentResetOccupationCompensator S hflow g (davisStateAfterJump S hflow ξ initial (k ω) ω) (t - ξ.jumpTime (k ω) ω)| else 0) =
      (fun ω => ∑ i ∈ Finset.range N,
        ((if i < k ω then |davisRealizedResetIncrement S hflow ξ initial g i ω| else 0) +
         (if i < k ω then |davisSampledResetOccupationCompensator S hflow g ξ initial i ω| else 0) +
         (if i = k ω then |davisSegmentResetOccupationCompensator S hflow g (davisStateAfterJump S hflow ξ initial i ω) (t - ξ.jumpTime i ω)| else 0))) := by
    ext ω
    rw [sum_inc_eq ω, sum_occ_eq ω, seg_eq ω]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [goal_eq]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.add
  apply Measurable.add
  · apply Measurable.ite
    · exact measurableSet_lt measurable_const hk
    · exact Measurable.abs (hξ.realizedResetIncrement S hflow hf hr initial g hg i)
    · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_lt measurable_const hk
    · exact Measurable.abs (@hreg.measurable_sampled_stoppedCompensator Q _ _ n m S hflow hf hr g Ω _ ξ hξ initial i)
    · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_eq_fun measurable_const hk
    · exact Measurable.abs (hreg.stoppedCompensator_measurable.comp
        ((hξ.stateAfterJump S hflow hf hr initial i).prodMk (measurable_const.sub (hξ.jumpTime i))))
    · exact measurable_const

/-- The cap-independent full fixed-time envelope is measurable. -/
theorem DavisResetOccupationRegular.measurable_elapsedOccupationEnvelope
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g)
    (t : ℝ≥0) :
    Measurable (davisElapsedOccupationEnvelope
      S hflow ξ hne initial g t) := by
  -- Helper: stopped envelope is always ≤ full envelope
  have stopped_le : ∀ (N : ℕ) (ω : Ω),
      davisStoppedElapsedOccupationEnvelope S hflow ξ hne initial g N t ω ≤
      davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω := by
    intro N ω
    unfold davisStoppedElapsedOccupationEnvelope davisElapsedOccupationEnvelope
    by_cases h : ξ.activeSegmentIndex hne t ω < N
    · simp [h, min_eq_right h.le]
    · push_neg at h
      have h1 : min N (ξ.activeSegmentIndex hne t ω) = N := min_eq_left h
      simp [h1]
      have h2 : ¬(ξ.activeSegmentIndex hne t ω < N) := by omega
      simp [h2]
      have hs1 : ∑ x ∈ Finset.range N, |S.davisRealizedResetIncrement hflow ξ initial g x ω| ≤
          ∑ x ∈ Finset.range (ξ.activeSegmentIndex hne t ω), |S.davisRealizedResetIncrement hflow ξ initial g x ω| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
        intro _ _ _; exact abs_nonneg _
      have hs2 : ∑ x ∈ Finset.range N, |S.davisSampledResetOccupationCompensator hflow g ξ initial x ω| ≤
          ∑ x ∈ Finset.range (ξ.activeSegmentIndex hne t ω), |S.davisSampledResetOccupationCompensator hflow g ξ initial x ω| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
        intro _ _ _; exact abs_nonneg _
      linarith [abs_nonneg (S.davisSegmentResetOccupationCompensator hflow g
        (S.davisStateAfterJump hflow ξ initial (ξ.activeSegmentIndex hne t ω) ω)
        (t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω))]
  -- The full envelope equals the supremum of stopped envelopes
  have eq_sup : davisElapsedOccupationEnvelope S hflow ξ hne initial g t =
      fun ω => ⨆ N : ℕ, davisStoppedElapsedOccupationEnvelope S hflow ξ hne initial g (N + 1) t ω := by
    ext ω
    apply le_antisymm
    · -- Full ≤ Sup (since Full = stopped(k+1) for some k)
      let k := ξ.activeSegmentIndex hne t ω
      have hle : davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω =
          davisStoppedElapsedOccupationEnvelope S hflow ξ hne initial g (k + 1) t ω :=
        (davisStoppedElapsedOccupationEnvelope_eq_elapsed_of_activeSegmentIndex_lt
          S hflow ξ hne initial g (k + 1) t ω (by simp [k])).symm
      have hbdd : BddAbove (Set.range fun N => davisStoppedElapsedOccupationEnvelope S hflow ξ hne initial g (N + 1) t ω) :=
        ⟨davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω, by
          intro b hb
          obtain ⟨N', rfl⟩ := hb
          exact stopped_le (N' + 1) ω⟩
      rw [hle]
      exact le_ciSup hbdd k
    · -- Supremum ≤ Full (since every stopped ≤ full)
      apply ciSup_le
      intro N
      exact stopped_le (N + 1) ω
  rw [eq_sup]
  apply Measurable.iSup
  intro N
  exact @DavisResetOccupationRegular.measurable_stoppedElapsedOccupationEnvelope Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial hg (N + 1) t

end SHS
