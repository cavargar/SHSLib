import SHSLib.Core.DavisElapsedOccupationObservability

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Deterministic-cap increments of elapsed reset occupation

This module exposes increments of the deterministic jump-capped
approximations.  It supplies the elementary measurability, integrability, and
event-centering assembly used after segmentwise conditional compensation has
been established.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Increment between two times of a fixed deterministic jump-capped
occupation-centered approximation. -/
def davisStoppedElapsedOccupationCenteredResetIncrement
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t ω -
    davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N s ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Fixed-cap increments converge pointwise to the full process increment. -/
theorem tendsto_davisStoppedElapsedOccupationCenteredResetIncrement
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (s t : ℝ≥0) (ω : Ω) :
    Filter.Tendsto (fun N =>
      davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t ω) Filter.atTop
      (nhds (davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g s t ω)) := by
  unfold davisStoppedElapsedOccupationCenteredResetIncrement
  unfold davisElapsedOccupationCenteredResetIncrement
  unfold davisElapsedOccupationCenteredResetProcess
  exact (tendsto_davisStoppedElapsedOccupationCenteredResetSum
    S hflow ξ hne initial g t ω).sub
      (tendsto_davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g s ω)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Measurability of capped endpoint values gives measurability of their
increment. -/
theorem measurable_davisStoppedElapsedOccupationCenteredResetIncrement
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*}
    (m' : MeasurableSpace Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s t : ℝ≥0)
    (hs : Measurable[m']
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s))
    (ht : Measurable[m']
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t)) :
    Measurable[m']
      (davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t) := by
  exact ht.sub hs

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Integrable capped endpoint values give an integrable capped increment. -/
theorem integrable_davisStoppedElapsedOccupationCenteredResetIncrement
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s t : ℝ≥0)
    (hs : Integrable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N s) P)
    (ht : Integrable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t) P) :
    Integrable (davisStoppedElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g N s t) P :=
  ht.sub hs

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- If both capped endpoint values are centered on an event, then their
capped increment is centered on that event. -/
theorem setIntegral_davisStoppedElapsedOccupationCenteredResetIncrement_eq_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s t : ℝ≥0) (A : Set Ω)
    (hs : Integrable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N s) (P.restrict A))
    (ht : Integrable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t) (P.restrict A))
    (hszero : ∫ ω in A, davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N s ω ∂P = 0)
    (htzero : ∫ ω in A, davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t ω ∂P = 0) :
    ∫ ω in A, davisStoppedElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g N s t ω ∂P = 0 := by
  unfold davisStoppedElapsedOccupationCenteredResetIncrement
  rw [integral_sub ht hs, htzero, hszero, sub_zero]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Vanishing integrals on all finite earlier-time events are equivalent to a
zero conditional expectation for an integrable fixed-cap increment. -/
theorem condExp_davisStoppedElapsedOccupationCenteredResetIncrement_eq_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s t : ℝ≥0)
    (hle : filtration s ≤ mΩ) [SigmaFinite (P.trim hle)]
    (hint : Integrable
      (davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t) P)
    (hzero : ∀ A, MeasurableSet[filtration s] A → P A < ⊤ →
      ∫ ω in A, davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t ω ∂P = 0) :
    P[davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t | filtration s] =ᵐ[P]
      (0 : Ω → ℝ) := by
  have hcharacterize : (0 : Ω → ℝ) =ᵐ[P]
      P[davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t | filtration s] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hle hint
    · intro A hA hAfin
      exact integrableOn_zero
    · intro A hA hAfin
      rw [hzero A hA hAfin]
      simp
    · exact aestronglyMeasurable_zero
  exact hcharacterize.symm

end SHS
