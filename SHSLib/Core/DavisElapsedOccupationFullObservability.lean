import SHSLib.Core.DavisElapsedGeneratorMartingale

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Discharging observability for the full-information filtration

The martingale and generator theorems take componentwise observability of the
elapsed occupation-centered reset process as an input.  This module discharges
that input in the one case where it is unconditionally available: the
full-information filtration, which reveals the whole ambient sigma-algebra at
every elapsed time.

Each of the three components — completed realized resets, completed reset
occupation, and the active partial occupation — is shown to be an ambient
measurable random variable under the existing jump-noise and reset-occupation
regularity interfaces.  Observability is also shown to be inherited by every
finer filtration, so the full-information instance certifies the interface for
any filtration containing it.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The completed realized-reset contribution below a deterministic jump cap
is ambient measurable. -/
theorem DavisJumpNoise.MeasurableNoise.measurable_stoppedElapsedRealizedResetContribution
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) (hg : Measurable g)
    (N : ℕ) (t : ℝ≥0) :
    Measurable (davisStoppedElapsedRealizedResetContribution
      S hflow ξ hne initial g N t) := by
  unfold davisStoppedElapsedRealizedResetContribution
  let k : Ω → ℕ := fun ω => ξ.activeSegmentIndex hne t ω
  have hk : Measurable k := hξ.activeSegmentIndex hne t
  -- Rewrite the sum using a fixed range with conditional
  have key : ∀ ω, S.davisFiniteRealizedResetSum hflow ξ initial g (min N (k ω)) ω =
      ∑ j ∈ Finset.range N, if j < k ω then
        S.davisRealizedResetIncrement hflow ξ initial g j ω else 0 := by
    intro ω
    unfold davisFiniteRealizedResetSum
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [Finset.mem_range, Finset.mem_filter]
  rw [show (fun ω =>
      S.davisFiniteRealizedResetSum hflow ξ initial g (min N (k ω)) ω) =
    (fun ω =>
      ∑ j ∈ Finset.range N, if j < k ω then
        S.davisRealizedResetIncrement hflow ξ initial g j ω else 0) by
      funext ω; exact key ω]
  -- Each term in the sum is measurable for fixed j
  apply Finset.measurable_sum
  intro j _
  -- Measurability of: if j < k ω then ... else 0
  apply Measurable.ite
  · exact measurableSet_lt measurable_const hk
  · exact hξ.realizedResetIncrement S hflow hf hr initial g hg j
  · exact measurable_const

/-- The completed reset-occupation contribution below a deterministic jump cap
is ambient measurable. -/
theorem DavisResetOccupationRegular.measurable_stoppedElapsedCompletedResetOccupation
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (N : ℕ) (t : ℝ≥0) :
    Measurable (davisStoppedElapsedCompletedResetOccupation
      S hflow ξ hne initial g N t) := by
  unfold davisStoppedElapsedCompletedResetOccupation
  let k : Ω → ℕ := fun ω => ξ.activeSegmentIndex hne t ω
  have hk : Measurable k := hξ.activeSegmentIndex hne t
  -- Rewrite the sum using a fixed range with conditional
  have key : ∀ ω, S.davisFiniteResetOccupation hflow g ξ initial (min N (k ω)) ω =
      ∑ j ∈ Finset.range N, if j < k ω then
        S.davisSegmentResetOccupationCompensator hflow g
          (S.davisPreJumpHistory hflow ξ initial j ω).currentState
          (ξ.holdingTime j ω) else 0 := by
    intro ω
    unfold davisFiniteResetOccupation
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [Finset.mem_range, Finset.mem_filter]
  rw [show (fun ω =>
      S.davisFiniteResetOccupation hflow g ξ initial (min N (k ω)) ω) =
      (fun ω =>
        ∑ j ∈ Finset.range N, if j < k ω then
          S.davisSegmentResetOccupationCompensator hflow g
            (S.davisPreJumpHistory hflow ξ initial j ω).currentState
            (ξ.holdingTime j ω) else 0) by
      funext ω; exact key ω]
  -- Each term in the sum is measurable for fixed j
  apply Finset.measurable_sum
  intro j _
  -- Measurability of: if j < k ω then ... else 0
  apply Measurable.ite
  · exact measurableSet_lt measurable_const hk
  · exact @hreg.measurable_sampled_stoppedCompensator Q _ _ n m S hflow hf hr g Ω _ ξ hξ initial j
  · exact measurable_const

/-- The active partial reset occupation below a deterministic jump cap is
ambient measurable. -/
theorem DavisResetOccupationRegular.measurable_stoppedElapsedActiveResetOccupation
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (N : ℕ) (t : ℝ≥0) :
    Measurable (davisStoppedElapsedActiveResetOccupation
      S hflow ξ hne initial g N t) := by
  unfold davisStoppedElapsedActiveResetOccupation
  let k : Ω → ℕ := fun ω => ξ.activeSegmentIndex hne t ω
  have hk : Measurable k := hξ.activeSegmentIndex hne t
  -- Rewrite as sum over range N with indicator for i = k
  have heq : ∀ ω, (if ξ.activeSegmentIndex hne t ω < N
      then davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial (ξ.activeSegmentIndex hne t ω) ω)
        (t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω)
      else 0) =
    ∑ i ∈ Finset.range N, (if i = ξ.activeSegmentIndex hne t ω
      then davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial i ω)
        (t - ξ.jumpTime i ω) else 0) := by
    intro ω
    let k := ξ.activeSegmentIndex hne t ω
    by_cases hk : k < N <;> simp_all
  rw [show (fun a => if ξ.activeSegmentIndex hne t a < N
      then davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial (ξ.activeSegmentIndex hne t a) a)
        (t - ξ.jumpTime (ξ.activeSegmentIndex hne t a) a)
      else 0) =
    (fun a => ∑ i ∈ Finset.range N, (if i = ξ.activeSegmentIndex hne t a
      then davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial i a)
        (t - ξ.jumpTime i a) else 0)) by
    funext ω; exact heq ω]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_const) hk
  · exact hreg.stoppedCompensator_measurable.comp
        ((hξ.stateAfterJump S hflow hf hr initial i).prodMk
          (measurable_const.sub (hξ.jumpTime i)))
  · exact measurable_const

/-- Componentwise observability holds for the full-information filtration. -/
theorem DavisResetOccupationRegular.elapsedOccupationObservable_full
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g) :
    DavisElapsedOccupationObservable
      S hflow ξ.fullFiltration ξ hne initial g where
  realized_measurable := fun N t =>
    hξ.measurable_stoppedElapsedRealizedResetContribution
      S hflow hf hr hne initial g hg N t
  completed_occupation_measurable := fun N t =>
    @DavisResetOccupationRegular.measurable_stoppedElapsedCompletedResetOccupation
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial N t
  active_occupation_measurable := fun N t =>
    @DavisResetOccupationRegular.measurable_stoppedElapsedActiveResetOccupation
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial N t

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Observability is inherited by every finer filtration. -/
theorem DavisElapsedOccupationObservable.mono
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {filtration filtration' : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g)
    (hle : filtration ≤ filtration') :
    DavisElapsedOccupationObservable
      S hflow filtration' ξ hne initial g where
  realized_measurable := fun N t =>
    (hobs.realized_measurable N t).mono (hle t) le_rfl
  completed_occupation_measurable := fun N t =>
    (hobs.completed_occupation_measurable N t).mono (hle t) le_rfl
  active_occupation_measurable := fun N t =>
    (hobs.active_occupation_measurable N t).mono (hle t) le_rfl

/-- Martingale property for the full-information filtration, with the
observability input discharged. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_full
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale
    Q _ _ n m S hflow hf hr g hreg Ω _ P _ ξ.fullFiltration ξ hξ hne initial hg
    (@DavisResetOccupationRegular.elapsedOccupationObservable_full
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial hg)
    hlaw henv

/-- Compensated generator process martingale for the full-information
filtration, with the observability input discharged. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_compensatedGenerator_full
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {a g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        S hflow ξ hne initial a g) ξ.fullFiltration P :=
  martingale_davisElapsedCompensatedGeneratorProcess
    S hflow P ξ.fullFiltration ξ hne initial a g hga
    (@DavisStoppedElapsedOccupationIncrementLaw.martingale_full
      Q _ _ n m S hflow hf hr g hreg Ω _ P _ ξ hξ hne initial hg hlaw henv)

end SHS
