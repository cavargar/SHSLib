import SHSLib.Core.DavisConditionalResetExpectation

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The discrete martingale of centered reset increments

This module connects the one-step conditional mean-zero identity to the finite
history filtration.  Completed history through jump `N` contains every
holding time and channel mark used by the first `N` centered reset increments,
so their finite sums form a discrete-time martingale.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Information available immediately before channel `k` is contained in the
completed history after that channel has been sampled. -/
theorem DavisJumpNoise.preChannelSpace_le_preJumpHistory_succ
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n) (k : ℕ) :
    ξ.preChannelSpace S hflow initial k ≤
      ξ.preJumpHistorySpace S hflow initial (k + 1) := by
  rw [DavisJumpNoise.preChannelSpace, DavisJumpNoise.preJumpHistorySpace]
  apply measurable_iff_comap_le.mpr
  have g_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) => 
      (DavisPreJumpHistory.restrict (by omega : k ≤ k + 1) H, H.holdingTime ⟨k, by omega⟩)) := by
    apply Measurable.prodMk
    · exact DavisPreJumpHistory.measurable_restrict (by omega : k ≤ k + 1)
    · rw [measurable_iff_comap_le, DavisPreJumpHistory.instMeasurableSpace]
      have heq2 : (fun a : DavisPreJumpHistory Q n m (k+1) => a.holdingTime ⟨k, by omega⟩) = 
          (fun p : (Fin (k+1) → ℝ≥0) × _ => p.1 ⟨k, by omega⟩) ∘ 
          (fun H => (H.holdingTime, H.channel, H.stateAfterJump)) := rfl
      rw [heq2, ← MeasurableSpace.comap_comp]
      apply MeasurableSpace.comap_mono
      have : Measurable (fun p : (Fin (k+1) → ℝ≥0) × (Fin (k+1) → Fin m) × (Fin (k+2) → DavisState Q n) => p.1 ⟨k, by omega⟩) :=
        (measurable_pi_apply (⟨k, by omega⟩ : Fin (k+1))) |>.comp measurable_fst
      rw [measurable_iff_comap_le] at this
      exact this
  have heq : (fun ω => (davisPreJumpHistory S hflow ξ initial k ω, ξ.holdingTime k ω)) =
      (fun H => (DavisPreJumpHistory.restrict (by omega : k ≤ k + 1) H, 
                 H.holdingTime ⟨k, by omega⟩)) ∘
      (davisPreJumpHistory S hflow ξ initial (k + 1)) := rfl
  show MeasurableSpace.comap id (MeasurableSpace.comap (fun ω => (davisPreJumpHistory S hflow ξ initial k ω, ξ.holdingTime k ω)) inferInstance) ≤ _
  rw [MeasurableSpace.comap_id, heq]
  have : MeasurableSpace.comap ((fun H => (DavisPreJumpHistory.restrict (by omega : k ≤ k + 1) H, 
                 H.holdingTime ⟨k, by omega⟩)) ∘ (davisPreJumpHistory S hflow ξ initial (k + 1))) inferInstance = 
         MeasurableSpace.comap (davisPreJumpHistory S hflow ξ initial (k + 1)) 
           (MeasurableSpace.comap (fun H => (DavisPreJumpHistory.restrict (by omega : k ≤ k + 1) H, 
                 H.holdingTime ⟨k, by omega⟩)) inferInstance) := by
    rw [MeasurableSpace.comap_comp]
  rw [this]
  refine MeasurableSpace.comap_mono ?_
  rw [← measurable_iff_comap_le]
  exact g_meas

/-- The channel sampled at index `k` is measurable in the completed history
through jump `k + 1`. -/
theorem DavisJumpNoise.channel_measurable_preJumpHistory_succ
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n) (k : ℕ) :
    Measurable[ξ.preJumpHistorySpace S hflow initial (k + 1)]
      (ξ.channel k) := by
  rw [measurable_iff_comap_le]
  set f := davisPreJumpHistory S hflow ξ initial (k + 1)
  show MeasurableSpace.comap (ξ.channel k) _ ≤ MeasurableSpace.comap f _
  have heq : ξ.channel k = (fun H : DavisPreJumpHistory Q n m (k + 1) => H.channel ⟨k, by omega⟩) ∘ f := rfl
  rw [heq, ← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono
  unfold DavisPreJumpHistory.instMeasurableSpace
  show MeasurableSpace.comap (fun H : DavisPreJumpHistory Q n m (k + 1) => H.channel ⟨k, by omega⟩) (Fin.instMeasurableSpace m) ≤
      MeasurableSpace.comap (fun H => (H.holdingTime, H.channel, H.stateAfterJump)) _
  have heq2 : (fun H : DavisPreJumpHistory Q n m (k + 1) => H.channel ⟨k, by omega⟩) =
      (fun p : (Fin (k+1) → ℝ≥0) × (Fin (k+1) → Fin m) × (Fin (k+2) → DavisState Q n) => p.2.1 ⟨k, by omega⟩) ∘
      (fun H : DavisPreJumpHistory Q n m (k + 1) => (H.holdingTime, H.channel, H.stateAfterJump)) := rfl
  rw [heq2, ← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono
  rw [← measurable_iff_comap_le]
  exact (measurable_pi_apply (⟨k, by omega⟩ : Fin (k + 1))).comp measurable_snd.fst

/-- A centered reset increment is measurable once its channel mark has been
added to the finite history. -/
theorem DavisJumpNoise.centeredResetIncrement_measurable_history_succ
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hg : Measurable g) (k : ℕ) :
    Measurable[ξ.preJumpHistorySpace S hflow initial (k + 1)]
      (davisCenteredResetIncrement S hflow ξ initial g k) := by
  rw [DavisJumpNoise.preJumpHistorySpace]
  rw [measurable_iff_comap_le]
  -- We need to show that davisCenteredResetIncrement is measurable w.r.t. davisPreJumpHistory
  -- The key insight is that davisCenteredResetIncrement k is a function of:
  -- - channel k, holdingTime k, stateAfterJump k (all in DavisPreJumpHistory (k+1))
  have h_eq : (fun ω => S.davisCenteredResetIncrement hflow ξ initial g k ω) =
    (fun H : DavisPreJumpHistory Q n m (k+1) =>
      let state_k := H.stateAfterJump ⟨k, by omega⟩
      let state_before := S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) state_k
      let realized := g (S.resetDavisState (H.channel ⟨k, by omega⟩) state_before) - g state_before
      let expected := davisExpectedResetIncrement S g state_before
      realized - expected) ∘ (S.davisPreJumpHistory hflow ξ initial (k + 1)) := by
    ext ω
    rfl
  have h_eq' : S.davisCenteredResetIncrement hflow ξ initial g k =
    (fun H : DavisPreJumpHistory Q n m (k+1) =>
      let state_k := H.stateAfterJump ⟨k, by omega⟩
      let state_before := S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) state_k
      let realized := g (S.resetDavisState (H.channel ⟨k, by omega⟩) state_before) - g state_before
      let expected := davisExpectedResetIncrement S g state_before
      realized - expected) ∘ (S.davisPreJumpHistory hflow ξ initial (k + 1)) := by
    rfl
  rw [h_eq']
  rw [← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono
  -- Goal: comap outer Real ≤ DavisPreJumpHistory.instMeasurableSpace
  -- This is equivalent to: outer is measurable
  have h_outer_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) =>
      let state_k := H.stateAfterJump ⟨k, by omega⟩
      let state_before := S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) state_k
      let realized := g (S.resetDavisState (H.channel ⟨k, by omega⟩) state_before) - g state_before
      let expected := davisExpectedResetIncrement S g state_before
      realized - expected) := by
    -- Extract components using the same pattern as in preChannelSpace_le_preJumpHistory_succ
    have holdingTime_k_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) => H.holdingTime ⟨k, by omega⟩) := by
      rw [measurable_iff_comap_le, DavisPreJumpHistory.instMeasurableSpace]
      have heq : (fun H : DavisPreJumpHistory Q n m (k+1) => H.holdingTime ⟨k, by omega⟩) = 
          (fun p : (Fin (k+1) → ℝ≥0) × (Fin (k+1) → Fin m) × (Fin (k+2) → DavisState Q n) => p.1 ⟨k, by omega⟩) ∘ 
          (fun H => (H.holdingTime, H.channel, H.stateAfterJump)) := rfl
      rw [heq, ← MeasurableSpace.comap_comp]
      apply MeasurableSpace.comap_mono
      have : Measurable (fun p : (Fin (k+1) → ℝ≥0) × (Fin (k+1) → Fin m) × (Fin (k+2) → DavisState Q n) => p.1 ⟨k, by omega⟩) :=
        (measurable_pi_apply (⟨k, by omega⟩ : Fin (k+1))) |>.comp measurable_fst
      rw [measurable_iff_comap_le] at this
      exact this
    have stateAfterJump_k_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) => H.stateAfterJump ⟨k, by omega⟩) := by
      rw [measurable_iff_comap_le, DavisPreJumpHistory.instMeasurableSpace]
      have heq : (fun H : DavisPreJumpHistory Q n m (k+1) => H.stateAfterJump ⟨k, by omega⟩) = 
          (fun p : (Fin (k+1) → ℝ≥0) × (Fin (k+1) → Fin m) × (Fin (k+2) → DavisState Q n) => p.2.2 ⟨k, by omega⟩) ∘ 
          (fun H => (H.holdingTime, H.channel, H.stateAfterJump)) := rfl
      rw [heq, ← MeasurableSpace.comap_comp]
      apply MeasurableSpace.comap_mono
      have : Measurable (fun p : (Fin (k+1) → ℝ≥0) × (Fin (k+1) → Fin m) × (Fin (k+2) → DavisState Q n) => p.2.2 ⟨k, by omega⟩) :=
        (measurable_pi_apply (⟨k, by omega⟩ : Fin (k+2))) |>.comp (measurable_snd.snd)
      rw [measurable_iff_comap_le] at this
      exact this
    have channel_k_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) => H.channel ⟨k, by omega⟩) := by
      rw [measurable_iff_comap_le, DavisPreJumpHistory.instMeasurableSpace]
      have heq : (fun H : DavisPreJumpHistory Q n m (k+1) => H.channel ⟨k, by omega⟩) = 
          (fun p : (Fin (k+1) → ℝ≥0) × (Fin (k+1) → Fin m) × (Fin (k+2) → DavisState Q n) => p.2.1 ⟨k, by omega⟩) ∘ 
          (fun H => (H.holdingTime, H.channel, H.stateAfterJump)) := rfl
      rw [heq, ← MeasurableSpace.comap_comp]
      apply MeasurableSpace.comap_mono
      have : Measurable (fun p : (Fin (k+1) → ℝ≥0) × (Fin (k+1) → Fin m) × (Fin (k+2) → DavisState Q n) => p.2.1 ⟨k, by omega⟩) :=
        (measurable_pi_apply (⟨k, by omega⟩ : Fin (k+1))) |>.comp (measurable_snd.fst)
      rw [measurable_iff_comap_le] at this
      exact this
    -- state_before = davisFlow (holdingTime k) (stateAfterJump k)
    have state_before_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) => 
        S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) (H.stateAfterJump ⟨k, by omega⟩)) := 
      hf.measurable_joint.comp (Measurable.prodMk holdingTime_k_meas stateAfterJump_k_meas)
    -- reset function: (channel, state) ↦ resetDavisState channel state
    have reset_meas : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n => S.resetDavisState ℓ z) := 
      fun ℓ => hr.reset_measurable ℓ
    -- realized = g (resetDavisState channel state_before) - g state_before
    -- Follow the pattern from DavisFiniteCompensatorMeasurable.lean lines 108-123
    have h_pair : Measurable (fun a : DavisPreJumpHistory Q n m (k+1) => 
           (a.channel ⟨k, by omega⟩, S.davisFlow hflow (a.holdingTime ⟨k, by omega⟩) (a.stateAfterJump ⟨k, by omega⟩))) := 
      Measurable.prodMk channel_k_meas state_before_meas
    have reset_part_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) =>
        g (S.resetDavisState (H.channel ⟨k, by omega⟩) (S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) (H.stateAfterJump ⟨k, by omega⟩)))) := by
      suffices h : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) => 
          ∑ ℓ : Fin m, (if H.channel ⟨k, by omega⟩ = ℓ then 
            g (S.resetDavisState ℓ (S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) (H.stateAfterJump ⟨k, by omega⟩))) else 0)) by
        convert h using 1
        ext H
        simp
      apply Finset.measurable_sum
      intro ℓ _
      refine Measurable.ite ?_ ?_ measurable_const
      · exact measurableSet_singleton ℓ |> MeasurableSet.preimage <| channel_k_meas
      · exact hg.comp ((hr.reset_measurable ℓ).comp state_before_meas)
    have g_state_before_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) =>
        g (S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) (H.stateAfterJump ⟨k, by omega⟩))) := hg.comp state_before_meas
    have h_realized_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) =>
        g (S.resetDavisState (H.channel ⟨k, by omega⟩) (S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) (H.stateAfterJump ⟨k, by omega⟩))) - 
        g (S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) (H.stateAfterJump ⟨k, by omega⟩))) := 
      Measurable.sub reset_part_meas g_state_before_meas
    -- expected = davisExpectedResetIncrement S g state_before
    have expected_meas : Measurable (fun H : DavisPreJumpHistory Q n m (k+1) =>
        davisExpectedResetIncrement S g (S.davisFlow hflow (H.holdingTime ⟨k, by omega⟩) (H.stateAfterJump ⟨k, by omega⟩))) := 
      (measurable_davisExpectedResetIncrement S hr g hg).comp state_before_meas
    exact Measurable.sub h_realized_meas expected_meas
  rw [measurable_iff_comap_le] at h_outer_meas
  exact h_outer_meas

/-- The finite centered reset sum through `N` is measurable with respect to
completed history through `N`. -/
theorem DavisJumpNoise.finiteCenteredResetSum_measurable_history
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hg : Measurable g) (N : ℕ) :
    Measurable[ξ.preJumpHistorySpace S hflow initial N]
      (davisFiniteCenteredResetSum S hflow ξ initial g N) := by
  unfold davisFiniteCenteredResetSum
  refine Finset.measurable_sum _ (fun k hk => ?_)
  have hk_lt : k < N := Finset.mem_range.mp hk
  have hmono : ξ.preJumpHistorySpace S hflow initial (k + 1) ≤ ξ.preJumpHistorySpace S hflow initial N :=
    ξ.preJumpHistorySpace_mono S hflow initial (by omega : k + 1 ≤ N)
  exact (centeredResetIncrement_measurable_history_succ S hflow hf hr ξ initial g hg k).mono hmono le_rfl

/-- Under the conditional channel law, finite sums of centered reset
increments form a martingale in the completed finite-history filtration. -/
theorem DavisJumpNoise.ConditionalChannelLaw.finiteCenteredResetSum_martingale
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (g : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C) :
    Martingale
      (fun N => davisFiniteCenteredResetSum S hflow ξ initial g N)
      (ξ.preJumpHistoryFiltration S hflow hf hr hξ initial) P := by
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro N
    exact (ξ.finiteCenteredResetSum_measurable_history S hflow hf hr initial g hgmeas N).stronglyMeasurable
  · intro N
    exact hξ.integrable_finiteCenteredResetSum S hflow hf hr initial g hgmeas C hg N
  · intro N
    have hdiff : (fun ω =>
        davisFiniteCenteredResetSum S hflow ξ initial g (N + 1) ω -
          davisFiniteCenteredResetSum S hflow ξ initial g N ω) =
        davisCenteredResetIncrement S hflow ξ initial g N := by
      funext ω
      rw [davisFiniteCenteredResetSum_succ]
      ring
    change P[(fun ω =>
        davisFiniteCenteredResetSum S hflow ξ initial g (N + 1) ω -
          davisFiniteCenteredResetSum S hflow ξ initial g N ω) |
        ξ.preJumpHistorySpace S hflow initial N] =ᵐ[P] (0 : Ω → ℝ)
    rw [hdiff]
    have hzero := hlaw.condExp_centeredResetIncrement hf hr hξ g hgmeas C hg N
    have htower := condExp_condExp_of_le
      (ξ.preJumpHistorySpace_le_preChannel S hflow initial N)
      (hξ.preChannelSpace_le S hflow hf hr initial N)
      (μ := P) (f := davisCenteredResetIncrement S hflow ξ initial g N)
    refine htower.symm.trans ?_
    exact (condExp_congr_ae hzero).trans
      (ae_of_all P fun ω => congrFun (condExp_zero (μ := P)
        (m := ξ.preJumpHistorySpace S hflow initial N)) ω)

end SHS
