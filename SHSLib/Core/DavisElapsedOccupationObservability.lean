import SHSLib.Core.DavisElapsedOccupationProcessIntegrable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Filtration-level observability of elapsed reset occupation

A state path need not reveal resets that leave the observed state unchanged.
This module therefore records the exact componentwise observability needed to
make the elapsed occupation-centered reset process adapted to an arbitrary
filtration.  The interface separates completed realized resets, completed
reset occupation, and the active partial occupation.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Completed realized-reset contribution below a deterministic jump cap. -/
def davisStoppedElapsedRealizedResetContribution (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisFiniteRealizedResetSum S hflow ξ initial g
    (min N (ξ.activeSegmentIndex hne t ω)) ω

/-- Completed reset-occupation contribution below a deterministic jump cap. -/
def davisStoppedElapsedCompletedResetOccupation (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisFiniteResetOccupation S hflow g ξ initial
    (min N (ξ.activeSegmentIndex hne t ω)) ω

/-- Active partial reset occupation, retained when the active segment lies
below the deterministic jump cap. -/
def davisStoppedElapsedActiveResetOccupation (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  let k := ξ.activeSegmentIndex hne t ω
  if k < N then
    davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial k ω)
      (t - ξ.jumpTime k ω)
  else 0

/-- Componentwise observability sufficient for adaptedness of the elapsed
occupation-centered reset process to `filtration`.

This condition is intentionally independent of how the filtration was
constructed.  It can be instantiated by a marked jump-history filtration, or
by a natural state-path filtration once resets are known to be observable. -/
structure DavisElapsedOccupationObservable
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) : Prop where
  realized_measurable : ∀ N t,
    Measurable[filtration t]
      (davisStoppedElapsedRealizedResetContribution
        S hflow ξ hne initial g N t)
  completed_occupation_measurable : ∀ N t,
    Measurable[filtration t]
      (davisStoppedElapsedCompletedResetOccupation
        S hflow ξ hne initial g N t)
  active_occupation_measurable : ∀ N t,
    Measurable[filtration t]
      (davisStoppedElapsedActiveResetOccupation
        S hflow ξ hne initial g N t)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The stopped centered sum is the difference of the three observable
components. -/
theorem davisStoppedElapsedOccupationCenteredResetSum_eq_observableComponents
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω =
      davisStoppedElapsedRealizedResetContribution
          S hflow ξ hne initial g N t ω -
        (davisStoppedElapsedCompletedResetOccupation
            S hflow ξ hne initial g N t ω +
          davisStoppedElapsedActiveResetOccupation
            S hflow ξ hne initial g N t ω) := by
  rfl

omit [MeasurableSingletonClass Q] in
/-- Componentwise observability makes every deterministic jump-capped
approximation measurable at its observation time. -/
theorem DavisElapsedOccupationObservable.measurable_stopped
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g)
    (N : ℕ) (t : ℝ≥0) :
    Measurable[filtration t]
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) := by
  rw [show davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t =
    fun ω => davisStoppedElapsedRealizedResetContribution
        S hflow ξ hne initial g N t ω -
      (davisStoppedElapsedCompletedResetOccupation
          S hflow ξ hne initial g N t ω +
        davisStoppedElapsedActiveResetOccupation
          S hflow ξ hne initial g N t ω) by
    funext ω
    exact davisStoppedElapsedOccupationCenteredResetSum_eq_observableComponents
      S hflow ξ hne initial g N t ω]
  exact (hobs.realized_measurable N t).sub
    ((hobs.completed_occupation_measurable N t).add
      (hobs.active_occupation_measurable N t))

/-- Componentwise observability passes from deterministic jump caps to the
full elapsed occupation-centered reset value. -/
theorem DavisElapsedOccupationObservable.measurable_elapsed
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g)
    (t : ℝ≥0) :
    Measurable[filtration t]
      (davisElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g t) := by
  have hstopped : ∀ N, Measurable[filtration t]
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) :=
    fun N => hobs.measurable_stopped N t
  letI : MeasurableSpace Ω := filtration t
  change Measurable (davisElapsedOccupationCenteredResetSum
    S hflow ξ hne initial g t)
  refine measurable_of_tendsto_metrizable hstopped ?_
  exact tendsto_pi_nhds.mpr (fun ω =>
    tendsto_davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t ω)

/-- The elapsed occupation-centered reset process is adapted to every
filtration satisfying the componentwise observability interface. -/
theorem DavisElapsedOccupationObservable.adapted
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g) :
    Adapted filtration
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) := by
  intro t
  exact hobs.measurable_elapsed t

end SHS
