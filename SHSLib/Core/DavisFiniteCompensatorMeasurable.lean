import SHSLib.Core.DavisFiniteCompensator

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Measurability of finite reset-compensator terms

This module supplies the measurable-function infrastructure needed to turn the
finite centered reset sums into a discrete-time martingale.  In particular, it
shows that the predictable normalized reset increment is measurable before the
channel mark is sampled.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Reading the current post-jump state from a finite history is measurable. -/
theorem DavisPreJumpHistory.measurable_currentState (k : ℕ) :
    Measurable (DavisPreJumpHistory.currentState
      (Q := Q) (n := n) (m := m) (k := k)) := by
  unfold DavisPreJumpHistory.currentState
  refine measurable_pi_apply (Fin.last k) |>.comp ?_
  rw [DavisPreJumpHistory.instMeasurableSpace]
  rw [measurable_iff_comap_le]
  have h1 : MeasurableSpace.comap (stateAfterJump : DavisPreJumpHistory Q n m k → Fin (k + 1) → DavisState Q n) (α := _) inferInstance ≤ 
         MeasurableSpace.comap (fun H : DavisPreJumpHistory Q n m k => (H.holdingTime, H.channel, H.stateAfterJump)) inferInstance := by
    rw [← measurable_iff_comap_le]
    have hcomp : stateAfterJump = (fun p : (Fin k → ℝ≥0) × (Fin k → Fin m) × (Fin (k + 1) → DavisState Q n) => p.2.2) ∘ 
             (fun H : DavisPreJumpHistory Q n m k => (H.holdingTime, H.channel, H.stateAfterJump)) := rfl
    rw [hcomp]
    refine Measurable.comp (measurable_snd.snd : Measurable (fun p : (Fin k → ℝ≥0) × (Fin k → Fin m) × (Fin (k + 1) → DavisState Q n) => p.2.2)) ?_
    rw [measurable_iff_comap_le]
    exact le_refl _
  show MeasurableSpace.comap _ _ ≤ DavisPreJumpHistory.instMeasurableSpace
  rw [DavisPreJumpHistory.instMeasurableSpace]
  exact h1

/-- The normalized expected reset increment is a measurable function of the
pre-reset state. -/
theorem measurable_davisExpectedResetIncrement
    (S : SHS Q n m) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (g : DavisState Q n → ℝ)
    (hg : Measurable g) :
    Measurable (davisExpectedResetIncrement S g) := by
  unfold davisExpectedResetIncrement
  apply Finset.measurable_sum
  intro ℓ _
  apply Measurable.mul
  · exact Measurable.div (IntensitiesMeasurable.measurable ℓ) (Finset.measurable_sum _ fun i _ => IntensitiesMeasurable.measurable i)
  · apply Measurable.sub
    · exact hg.comp (hr.reset_measurable ℓ)
    · exact hg

/-- The recursively constructed state immediately before jump `k` is
measurable with respect to the information containing the finite history and
the newly revealed holding time. -/
theorem DavisJumpNoise.stateBeforeJump_measurable_preChannel
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) :
    Measurable[ξ.preChannelSpace S hflow initial k]
      (davisStateBeforeJump S hflow ξ initial k) := by
  -- davisStateBeforeJump = davisFlow (holdingTime k) (currentState of pre-jump-history)
  have heq : davisStateBeforeJump S hflow ξ initial k = fun ω =>
      davisFlow S hflow (ξ.holdingTime k ω) ((davisPreJumpHistory S hflow ξ initial k ω).currentState) := by
    funext ω
    simp [davisStateBeforeJump, DavisPreJumpHistory.currentState]
  rw [heq]
  -- Use joint measurability of davisFlow
  exact hf.measurable_joint.comp
    (Measurable.prodMk (DavisJumpNoise.holdingTime_measurable_preChannel S hflow ξ initial k)
      (DavisPreJumpHistory.measurable_currentState k |> Measurable.comp <|
        DavisJumpNoise.preJumpHistory_measurable_preChannel S hflow ξ initial k))

/-- The predictable normalized reset increment is measurable before the
channel mark is sampled. -/
theorem DavisJumpNoise.expectedResetIncrement_measurable_preChannel
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hg : Measurable g) (k : ℕ) :
    Measurable[ξ.preChannelSpace S hflow initial k]
      (fun ω => davisExpectedResetIncrement S g
        (davisStateBeforeJump S hflow ξ initial k ω)) := by
  exact (measurable_davisExpectedResetIncrement S hr g hg).comp
    (DavisJumpNoise.stateBeforeJump_measurable_preChannel S hflow hf ξ initial k)

/-- Under measurable noise, an actual reset increment is an ambient measurable
random variable. -/
theorem DavisJumpNoise.MeasurableNoise.realizedResetIncrement
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hg : Measurable g) (k : ℕ) :
    Measurable (davisRealizedResetIncrement S hflow ξ initial g k) := by
  unfold davisRealizedResetIncrement
  have hstate : Measurable (davisStateBeforeJump S hflow ξ initial k) :=
    hξ.stateBeforeJump S hflow hf hr initial k
  have hch : Measurable (ξ.channel k) := hξ.channel k
  have hreset_meas : ∀ ℓ : Fin m, Measurable (S.resetDavisState ℓ) := hr.reset_measurable
  have hF : Measurable (fun (p : Fin m × DavisState Q n) =>
      g (S.resetDavisState p.1 p.2) - g p.2) := by
    apply Measurable.sub
    · have heq : (fun (p : Fin m × DavisState Q n) =>
          g (S.resetDavisState p.1 p.2)) = fun p => ∑ ℓ : Fin m,
          (if p.1 = ℓ then g (S.resetDavisState ℓ p.2) else 0) := by
        ext ⟨ℓ₀, z⟩
        simp
      rw [heq]
      apply Finset.measurable_sum
      intro ℓ _
      refine Measurable.ite ?_ ?_ measurable_const
      exact measurableSet_singleton ℓ |> MeasurableSet.preimage <| measurable_fst
      exact hg.comp (hreset_meas ℓ |> Measurable.comp <| measurable_snd)
    · exact hg.comp measurable_snd
  exact hF.comp (Measurable.prodMk hch hstate)

/-- Under measurable noise, every centered reset increment is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.centeredResetIncrement
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hg : Measurable g) (k : ℕ) :
    Measurable (davisCenteredResetIncrement S hflow ξ initial g k) := by
  unfold davisCenteredResetIncrement
  apply Measurable.sub
  · unfold davisRealizedResetIncrement
    apply Measurable.sub
    · have hpre : Measurable (fun ω => (ξ.channel k ω, davisStateBeforeJump S hflow ξ initial k ω)) :=
        Measurable.prodMk (hξ.channel k) (DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k)
      have hjoint : Measurable (fun (x : Fin m × DavisState Q n) => S.resetDavisState x.1 x.2) := by
        intro s hs
        have hp : (fun (x : Fin m × DavisState Q n) => S.resetDavisState x.1 x.2) ⁻¹' s =
          ⋃ ℓ : Fin m, {x : Fin m × DavisState Q n | x.1 = ℓ} ∩ (fun (x : Fin m × DavisState Q n) => S.resetDavisState x.1 x.2) ⁻¹' s := by
          ext x; simp
        rw [hp]
        apply MeasurableSet.iUnion
        intro ℓ
        have hset : {x : Fin m × DavisState Q n | x.1 = ℓ} ∩ (fun (x : Fin m × DavisState Q n) => S.resetDavisState x.1 x.2) ⁻¹' s =
          {ℓ} ×ˢ ((fun z => S.resetDavisState ℓ z) ⁻¹' s) := by
          ext ⟨a, b⟩
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
          constructor <;> intro h <;> rcases h with ⟨ha, hb⟩ <;> simp_all
        rw [hset]
        exact MeasurableSet.prod (measurableSet_singleton ℓ) (hr.reset_measurable ℓ hs)
      exact hg.comp (hjoint.comp hpre)
    · exact hg.comp (DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k)
  · exact (measurable_davisExpectedResetIncrement S hr g hg).comp
      (DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k)

/-- Every finite centered reset sum is an ambient measurable random variable. -/
theorem DavisJumpNoise.MeasurableNoise.finiteCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hg : Measurable g) (N : ℕ) :
    Measurable (davisFiniteCenteredResetSum S hflow ξ initial g N) := by
  unfold davisFiniteCenteredResetSum
  apply Finset.measurable_sum
  intro k _
  exact centeredResetIncrement S hflow hf hr hξ initial g hg k

end SHS
