import SHSLib.Core.DavisElapsedOccupationSegmentwise
import SHSLib.Core.DavisOneSegmentTruncatedCompensation

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The conditional step of the one-segment martingale

The segmentwise decomposition reduced the deterministic-cap increment law —
the last structural input of the elapsed occupation theory — to the martingale
property of the contribution of a single flow segment.  Its deterministic half
is the truncated one-segment compensation identity.  This module supplies the
missing conditional step.

The contribution of segment `N` splits pathwise into a *completed part*,
carried by the realized reset once the segment has ended, and an *active
part*, the partial occupation compensator accumulated while the segment is
still running.  Conditionally on the history available at time `s`, on the
event that segment `N` is active at `s` with age `u = s − T_N`, the holding
time has the integrated-hazard law renormalized by the survivor factor
`Sur(u)`, and the channel has the normalized intensity law.  The conditional
means of the two parts at a later time `t`, with `v = t − T_N`, are therefore

* completed part: `Sur(u)⁻¹ · ∫_u^v haz(r) · (E[reset] − comp)(r) dr`;
* active part:    `Sur(u)⁻¹ · Sur(v) · comp(v)`.

The truncated one-segment compensation identity evaluates the first integral
as `Sur(v)·comp(v) − Sur(u)·comp(u)`, so the difference of the two conditional
means is exactly `−comp(u)`, which is the value of the segment contribution at
time `s`.  That is the conditional step, and it makes the single-segment
contribution a martingale; by the segmentwise decomposition the
deterministic-cap increment law follows.

The conditional laws themselves — the two integral identities on events of the
filtration, and the centering of a segment not yet started at `s` — are
collected in `DavisSegmentConditionalStepLaw`, an interface a concrete model
verifies from its holding-time and channel laws.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Pathwise splitting of the single-segment contribution -/

/-- The fully realized and compensated contribution of segment `N`, carried
once that segment has been completed. -/
def davisSegmentCompletedContribution (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  davisRealizedResetIncrement S hflow ξ initial g N ω -
    davisSampledResetOccupationCompensator S hflow g ξ initial N ω

/-- The completed part of the contribution of segment `N` at elapsed time `t`:
the realized centered reset, retained once the segment has ended. -/
def davisSegmentCompletedPart (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ξ.jumpTime (N + 1) ω ≤ t then
    davisSegmentCompletedContribution S hflow ξ initial g N ω
  else 0

/-- The active part of the contribution of segment `N` at elapsed time `t`:
the partial occupation compensator accumulated while the segment is still
running. -/
def davisSegmentActivePart (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ξ.jumpTime (N + 1) ω ≤ t then 0
  else if ξ.jumpTime N ω ≤ t then
    davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial N ω) (t - ξ.jumpTime N ω)
  else 0

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Jump-time form of the single-segment contribution. -/
theorem davisElapsedOccupationSegmentContribution_eq_ite_jumpTime
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t ω =
      if ξ.jumpTime (N + 1) ω ≤ t then
        davisSegmentCompletedContribution S hflow ξ initial g N ω
      else if ξ.jumpTime N ω ≤ t then
        -davisSegmentResetOccupationCompensator S hflow g
          (davisStateAfterJump S hflow ξ initial N ω) (t - ξ.jumpTime N ω)
      else 0 := by
  have hsucc : ξ.jumpTime (N + 1) ω ≤ t ↔ N < ξ.activeSegmentIndex hne t ω := by
    rw [ξ.jumpTime_le_iff_le_activeSegmentIndex hne (N + 1) t ω]
    exact Nat.succ_le_iff
  have hN : ξ.jumpTime N ω ≤ t ↔ N ≤ ξ.activeSegmentIndex hne t ω :=
    ξ.jumpTime_le_iff_le_activeSegmentIndex hne N t ω
  unfold davisElapsedOccupationSegmentContribution davisSegmentCompletedContribution
  by_cases h1 : N < ξ.activeSegmentIndex hne t ω
  · rw [if_pos h1, if_pos (hsucc.mpr h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (hsucc.mp h))]
    by_cases h2 : N = ξ.activeSegmentIndex hne t ω
    · rw [if_pos h2, if_pos (hN.mpr (le_of_eq h2)), h2]
    · rw [if_neg h2, if_neg]
      intro h
      exact h2 (le_antisymm (hN.mp h) (Nat.le_of_not_lt h1))

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The single-segment contribution is the completed part minus the active
part. -/
theorem davisElapsedOccupationSegmentContribution_eq_sub
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t ω =
      davisSegmentCompletedPart S hflow ξ initial g N t ω -
        davisSegmentActivePart S hflow ξ initial g N t ω := by
  rw [davisElapsedOccupationSegmentContribution_eq_ite_jumpTime]
  unfold davisSegmentCompletedPart davisSegmentActivePart
  by_cases h1 : ξ.jumpTime (N + 1) ω ≤ t
  · rw [if_pos h1, if_pos h1, if_pos h1, sub_zero]
  · rw [if_neg h1, if_neg h1, if_neg h1, zero_sub]
    by_cases h2 : ξ.jumpTime N ω ≤ t
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, neg_zero]

/-! ## The two conditional means -/

/-- Conditional mean of the completed part of segment `N` at age `v`, given
that the segment is still active at age `u`: the hazard average of the
centered reset increment over `[u, v]`, renormalized by the survivor
factor at `u`. -/
def davisSegmentConditionalCompletedMean (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (u v : ℝ≥0) : ℝ :=
  (davisSegmentSurvivor S hflow z u)⁻¹ *
    ∫ r in Set.Icc (u : ℝ) (v : ℝ),
      davisSegmentHazardDensity S hflow z r *
        (davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z) -
          davisSegmentResetOccupationCompensator S hflow g z r.toNNReal)

/-- Conditional mean of the active part of segment `N` at age `v`, given that
the segment is still active at age `u`: the partial occupation compensator at
`v`, weighted by the conditional survival probability from `u` to `v`. -/
def davisSegmentConditionalActiveMean (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (u v : ℝ≥0) : ℝ :=
  (davisSegmentSurvivor S hflow z u)⁻¹ * davisSegmentSurvivor S hflow z v *
    davisSegmentResetOccupationCompensator S hflow g z v

/-- **The deterministic core of the conditional step.**  The difference of the
two conditional means is the value the segment contribution already had at
age `u`. -/
theorem davisSegmentConditionalMean_sub
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (z : DavisState Q n) (u v : ℝ≥0) (huv : u ≤ v) :
    davisSegmentConditionalCompletedMean S hflow g z u v -
        davisSegmentConditionalActiveMean S hflow g z u v =
      -davisSegmentResetOccupationCompensator S hflow g z u := by
  have hpos : 0 < davisSegmentSurvivor S hflow z u :=
    davisSegmentSurvivor_pos S hflow z u
  unfold davisSegmentConditionalCompletedMean davisSegmentConditionalActiveMean
  rw [integral_Icc_hazardDensity_mul_centered_resetIncrement_sub
    S hflow hcont g hgcont z u v huv]
  field_simp
  ring

/-! ## The conditional step law -/

/-- The conditional step of the one-segment martingale: the conditional laws
of the holding time and of the channel, expressed as integral identities on
the events of the filtration.

On an event of the filtration at time `s` on which segment `N` is active, the
completed and active parts at a later time `t` integrate to the two
conditional means, and a segment not yet started at `s` carries a centered
contribution at `t`. -/
structure DavisSegmentConditionalStepLaw (S : SHS Q n m)
    (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) (N : ℕ) : Prop where
  /-- The contribution of segment `N` is observable at every elapsed time. -/
  adapted : ∀ t, StronglyMeasurable[filtration t]
    (davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t)
  /-- Cumulative jump times are observable. -/
  jumpTime_observable : ∀ (k : ℕ) (t : ℝ≥0),
    MeasurableSet[filtration t] {ω | ξ.jumpTime k ω ≤ t}
  /-- The completed part is integrable. -/
  integrable_completedPart : ∀ t,
    Integrable (davisSegmentCompletedPart S hflow ξ initial g N t) P
  /-- The active part is integrable. -/
  integrable_activePart : ∀ t,
    Integrable (davisSegmentActivePart S hflow ξ initial g N t) P
  /-- The conditional mean of the active part is integrable on the event that
  segment `N` is active at `s`. -/
  integrableOn_conditionalActiveMean : ∀ s t, s ≤ t →
    IntegrableOn (fun ω => davisSegmentConditionalActiveMean S hflow g
      (davisStateAfterJump S hflow ξ initial N ω)
      (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω))
      {ω | ξ.jumpTime N ω ≤ s ∧ ¬ ξ.jumpTime (N + 1) ω ≤ s} P
  /-- Conditional law of the completed part on an active event. -/
  completed_conditional : ∀ s t, s ≤ t → ∀ A, MeasurableSet[filtration s] A →
    A ⊆ {ω | ξ.jumpTime N ω ≤ s ∧ ¬ ξ.jumpTime (N + 1) ω ≤ s} →
      ∫ ω in A, davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
        ∫ ω in A, davisSegmentConditionalCompletedMean S hflow g
          (davisStateAfterJump S hflow ξ initial N ω)
          (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) ∂P
  /-- Conditional law of the active part on an active event. -/
  active_conditional : ∀ s t, s ≤ t → ∀ A, MeasurableSet[filtration s] A →
    A ⊆ {ω | ξ.jumpTime N ω ≤ s ∧ ¬ ξ.jumpTime (N + 1) ω ≤ s} →
      ∫ ω in A, davisSegmentActivePart S hflow ξ initial g N t ω ∂P =
        ∫ ω in A, davisSegmentConditionalActiveMean S hflow g
          (davisStateAfterJump S hflow ξ initial N ω)
          (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) ∂P
  /-- A segment not yet started at `s` carries a centered contribution. -/
  fresh_centered : ∀ s t, s ≤ t → ∀ A, MeasurableSet[filtration s] A →
    A ⊆ {ω | ¬ ξ.jumpTime N ω ≤ s} →
      ∫ ω in A, davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N t ω ∂P = 0

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The contribution of a segment already completed at `s` no longer changes. -/
theorem davisElapsedOccupationSegmentContribution_eq_of_completed
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω)
    (hω : ξ.jumpTime (N + 1) ω ≤ s) :
    davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t ω =
      davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N s ω := by
  rw [davisElapsedOccupationSegmentContribution_eq_ite_jumpTime,
    davisElapsedOccupationSegmentContribution_eq_ite_jumpTime,
    if_pos hω, if_pos (le_trans hω hst)]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A segment not yet started at `s` carries no contribution at `s`. -/
theorem davisElapsedOccupationSegmentContribution_eq_zero_of_fresh
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s : ℝ≥0) (ω : Ω) (hω : ¬ ξ.jumpTime N ω ≤ s) :
    davisElapsedOccupationSegmentContribution
      S hflow ξ hne initial g N s ω = 0 := by
  have hsucc : ¬ ξ.jumpTime (N + 1) ω ≤ s := fun h =>
    hω (le_trans (ξ.jumpTime_mono ω (Nat.le_succ N)) h)
  rw [davisElapsedOccupationSegmentContribution_eq_ite_jumpTime,
    if_neg hsucc, if_neg hω]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- On an active segment the contribution is minus the partial occupation
compensator at the current age. -/
theorem davisElapsedOccupationSegmentContribution_eq_neg_of_active
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s : ℝ≥0) (ω : Ω)
    (hω : ξ.jumpTime N ω ≤ s) (hω' : ¬ ξ.jumpTime (N + 1) ω ≤ s) :
    davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N s ω =
      -davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial N ω) (s - ξ.jumpTime N ω) := by
  rw [davisElapsedOccupationSegmentContribution_eq_ite_jumpTime,
    if_neg hω', if_pos hω]


/-! ## From the conditional step to the one-segment martingale -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The single-segment contribution is integrable at every elapsed time. -/
theorem DavisSegmentConditionalStepLaw.integrable
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ} {N : ℕ}
    (hlaw : DavisSegmentConditionalStepLaw
      S hflow P filtration ξ hne initial g N) (t : ℝ≥0) :
    Integrable (davisElapsedOccupationSegmentContribution
      S hflow ξ hne initial g N t) P := by
  refine ((hlaw.integrable_completedPart t).sub
    (hlaw.integrable_activePart t)).congr ?_
  filter_upwards with ω
  exact (davisElapsedOccupationSegmentContribution_eq_sub
    S hflow ξ hne initial g N t ω).symm

/-- **The conditional step.**  Under the conditional step law the increment of
the single-segment contribution is centered on every event of the filtration
at the earlier time. -/
theorem DavisSegmentConditionalStepLaw.setIntegral_sub_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {g : DavisState Q n → ℝ}
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {N : ℕ}
    (hlaw : DavisSegmentConditionalStepLaw
      S hflow P filtration ξ hne initial g N)
    (s t : ℝ≥0) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[filtration s] A) :
    ∫ ω in A, (davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N t ω -
      davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N s ω) ∂P = 0 := by
  classical
  set X : ℝ≥0 → Ω → ℝ := fun r =>
    davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N r
    with hXdef
  set C : Set Ω := {ω | ξ.jumpTime N ω ≤ s} with hCdef
  set B : Set Ω := {ω | ξ.jumpTime (N + 1) ω ≤ s} with hBdef
  have hC' : MeasurableSet[filtration s] C := hlaw.jumpTime_observable N s
  have hB' : MeasurableSet[filtration s] B := hlaw.jumpTime_observable (N + 1) s
  have hCm : MeasurableSet C := filtration.le s _ hC'
  have hBm : MeasurableSet B := filtration.le s _ hB'
  have hAm : MeasurableSet A := filtration.le s _ hA
  have hDint : Integrable (fun ω => X t ω - X s ω) P :=
    (hlaw.integrable t).sub (hlaw.integrable s)
  -- the completed part of the segment: nothing changes any more
  have h1 : ∫ ω in A ∩ C ∩ B, (X t ω - X s ω) ∂P = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero (fun ω hω => ?_)
    have : X t ω = X s ω :=
      davisElapsedOccupationSegmentContribution_eq_of_completed
        S hflow ξ hne initial g N s t hst ω hω.2
    rw [this, sub_self]
  -- the segment has not started yet at `s`
  have h3 : ∫ ω in A \ C, (X t ω - X s ω) ∂P = 0 := by
    have hsub : ∫ ω in A \ C, (X t ω - X s ω) ∂P =
        (∫ ω in A \ C, X t ω ∂P) - ∫ ω in A \ C, X s ω ∂P :=
      integral_sub (hlaw.integrable t).integrableOn
        (hlaw.integrable s).integrableOn
    have hzs : ∫ ω in A \ C, X s ω ∂P = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun ω hω =>
        davisElapsedOccupationSegmentContribution_eq_zero_of_fresh
          S hflow ξ hne initial g N s ω hω.2)
    have hzt : ∫ ω in A \ C, X t ω ∂P = 0 :=
      hlaw.fresh_centered s t hst (A \ C) (hA.diff hC') (fun ω hω => hω.2)
    rw [hsub, hzs, hzt, sub_zero]
  -- the segment is active at `s`: the genuine conditional step
  have h2 : ∫ ω in (A ∩ C) \ B, (X t ω - X s ω) ∂P = 0 := by
    set A₂ : Set Ω := (A ∩ C) \ B with hA₂def
    have hA₂' : MeasurableSet[filtration s] A₂ := (hA.inter hC').diff hB'
    have hA₂m : MeasurableSet A₂ := (hAm.inter hCm).diff hBm
    have hA₂sub : A₂ ⊆ {ω | ξ.jumpTime N ω ≤ s ∧ ¬ ξ.jumpTime (N + 1) ω ≤ s} :=
      fun ω hω => ⟨hω.1.2, hω.2⟩
    set aMean : Ω → ℝ := fun ω => davisSegmentConditionalActiveMean S hflow g
      (davisStateAfterJump S hflow ξ initial N ω)
      (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) with haMeanDef
    set cMean : Ω → ℝ := fun ω => davisSegmentConditionalCompletedMean S hflow g
      (davisStateAfterJump S hflow ξ initial N ω)
      (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) with hcMeanDef
    -- on the active event the contribution at `s` is minus the partial compensator
    have hXs : ∀ ω ∈ A₂, X s ω = cMean ω - aMean ω := by
      intro ω hω
      have hactive := hA₂sub hω
      simp only [hXdef, hcMeanDef, haMeanDef]
      rw [davisElapsedOccupationSegmentContribution_eq_neg_of_active
        S hflow ξ hne initial g N s ω hactive.1 hactive.2]
      exact (davisSegmentConditionalMean_sub S hflow hcont g hgcont
        (davisStateAfterJump S hflow ξ initial N ω)
        (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω)
        (tsub_le_tsub_right hst _)).symm
    have haInt : IntegrableOn aMean A₂ P :=
      (hlaw.integrableOn_conditionalActiveMean s t hst).mono_set hA₂sub
    have hXsInt : IntegrableOn (X s) A₂ P := (hlaw.integrable s).integrableOn
    have hcInt : IntegrableOn cMean A₂ P := by
      have hadd : IntegrableOn (fun ω => aMean ω + X s ω) A₂ P :=
        haInt.add hXsInt
      refine MeasureTheory.IntegrableOn.congr_fun hadd (fun ω hω => ?_) hA₂m
      rw [hXs ω hω]
      ring
    -- the two conditional laws
    have hcm := hlaw.completed_conditional s t hst A₂ hA₂' hA₂sub
    have ham := hlaw.active_conditional s t hst A₂ hA₂' hA₂sub
    have hXt : ∫ ω in A₂, X t ω ∂P =
        (∫ ω in A₂, cMean ω ∂P) - ∫ ω in A₂, aMean ω ∂P := by
      rw [setIntegral_congr_fun hA₂m (fun ω _ =>
        davisElapsedOccupationSegmentContribution_eq_sub
          S hflow ξ hne initial g N t ω)]
      rw [integral_sub (hlaw.integrable_completedPart t).integrableOn
        (hlaw.integrable_activePart t).integrableOn, hcm, ham]
    have hXsEq : ∫ ω in A₂, X s ω ∂P =
        (∫ ω in A₂, cMean ω ∂P) - ∫ ω in A₂, aMean ω ∂P := by
      rw [setIntegral_congr_fun hA₂m (fun ω hω => hXs ω hω),
        integral_sub hcInt haInt]
    rw [integral_sub (hlaw.integrable t).integrableOn
      (hlaw.integrable s).integrableOn, hXt, hXsEq, sub_self]
  have e2 : ∫ ω in A ∩ C ∩ B, (X t ω - X s ω) ∂P +
      ∫ ω in (A ∩ C) \ B, (X t ω - X s ω) ∂P =
      ∫ ω in A ∩ C, (X t ω - X s ω) ∂P :=
    integral_inter_add_diff hBm hDint.integrableOn
  have e1 : ∫ ω in A ∩ C, (X t ω - X s ω) ∂P +
      ∫ ω in A \ C, (X t ω - X s ω) ∂P =
      ∫ ω in A, (X t ω - X s ω) ∂P :=
    integral_inter_add_diff hCm hDint.integrableOn
  rw [← e1, ← e2, h1, h2, h3]
  ring

/-- **The one-segment martingale.**  The conditional step law makes the
contribution of a single flow segment a martingale. -/
theorem martingale_davisElapsedOccupationSegmentContribution_of_conditionalStep
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {g : DavisState Q n → ℝ}
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {N : ℕ}
    (hlaw : DavisSegmentConditionalStepLaw
      S hflow P filtration ξ hne initial g N) :
    Martingale (fun t => davisElapsedOccupationSegmentContribution
      S hflow ξ hne initial g N t) filtration P := by
  refine ⟨hlaw.adapted, ?_⟩
  intro s t hst
  haveI : SigmaFinite (P.trim (filtration.le s)) :=
    (isFiniteMeasure_trim _).toSigmaFinite
  have hXs_int := hlaw.integrable s
  have hXt_int := hlaw.integrable t
  have hcond : P[fun ω => davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N t ω -
      davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N s ω | filtration s] =ᵐ[P] (0 : Ω → ℝ) := by
    have hchar : (0 : Ω → ℝ) =ᵐ[P]
        P[fun ω => davisElapsedOccupationSegmentContribution
            S hflow ξ hne initial g N t ω -
          davisElapsedOccupationSegmentContribution
            S hflow ξ hne initial g N s ω | filtration s] := by
      apply ae_eq_condExp_of_forall_setIntegral_eq (filtration.le s)
        (hXt_int.sub hXs_int)
      · intro A _ _
        exact integrableOn_zero
      · intro A hA _
        have hzero := hlaw.setIntegral_sub_eq_zero hcont hgcont s t hst A hA
        simp only [Pi.sub_apply, Pi.zero_apply]
        rw [hzero]
        simp
      · exact aestronglyMeasurable_zero
    exact hchar.symm
  have hself : P[davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N s | filtration s] =ᵐ[P]
      davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N s :=
    Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (filtration.le s) (hlaw.adapted s) hXs_int)
  have hsub := condExp_sub hXt_int hXs_int (filtration s : MeasurableSpace Ω)
  filter_upwards [hcond, hself, hsub] with ω h1 h2 h3
  simp only [Pi.sub_apply, Pi.zero_apply] at h1 h3
  have h1' : P[davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N t -
      davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N s |
      (filtration s : MeasurableSpace Ω)] ω = 0 := h1
  rw [h3, h2] at h1'
  linarith

/-- Segmentwise conditional step laws give the deterministic-cap increment
law, the last structural input of the elapsed occupation theory. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.of_conditional_step_laws
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {g : DavisState Q n → ℝ}
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n}
    (hlaw : ∀ N, DavisSegmentConditionalStepLaw
      S hflow P filtration ξ hne initial g N) :
    DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g :=
  DavisStoppedElapsedOccupationIncrementLaw.of_segment_martingales
    S hflow P filtration ξ hne initial g
    (fun N => martingale_davisElapsedOccupationSegmentContribution_of_conditionalStep
      hcont hgcont (hlaw N))

/-! ## Consistency: the interface is satisfiable

The conditional step law is an interface, so it is worth recording that it is
not vacuous.  For the zero test function every ingredient vanishes and the
law holds for the full-information filtration; this is the degenerate witness
that the hypotheses are mutually consistent. -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The expected reset increment of the zero test function vanishes. -/
theorem davisExpectedResetIncrement_zero_fun (S : SHS Q n m)
    (z : DavisState Q n) :
    davisExpectedResetIncrement S (fun _ => (0 : ℝ)) z = 0 := by
  simp [davisExpectedResetIncrement]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The partial occupation compensator of the zero test function vanishes. -/
theorem davisSegmentResetOccupationCompensator_zero_fun (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (z : DavisState Q n) (u : ℝ≥0) :
    davisSegmentResetOccupationCompensator S hflow (fun _ => (0 : ℝ)) z u = 0 := by
  simp [davisSegmentResetOccupationCompensator,
    davisSegmentResetOccupationDensity, davisExpectedResetIncrement]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The single-segment contribution of the zero test function vanishes. -/
theorem davisElapsedOccupationSegmentContribution_zero_fun
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationSegmentContribution
      S hflow ξ hne initial (fun _ => (0 : ℝ)) N t ω = 0 := by
  rw [davisElapsedOccupationSegmentContribution_eq_ite_jumpTime]
  simp [davisSegmentCompletedContribution, davisRealizedResetIncrement,
    davisSampledResetOccupationCompensator,
    davisSegmentResetOccupationCompensator_zero_fun]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The completed part of the zero test function vanishes. -/
theorem davisSegmentCompletedPart_zero_fun
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisSegmentCompletedPart S hflow ξ initial (fun _ => (0 : ℝ)) N t ω = 0 := by
  simp [davisSegmentCompletedPart, davisSegmentCompletedContribution,
    davisRealizedResetIncrement, davisSampledResetOccupationCompensator,
    davisSegmentResetOccupationCompensator_zero_fun]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The active part of the zero test function vanishes. -/
theorem davisSegmentActivePart_zero_fun
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisSegmentActivePart S hflow ξ initial (fun _ => (0 : ℝ)) N t ω = 0 := by
  simp [davisSegmentActivePart, davisSegmentResetOccupationCompensator_zero_fun]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Both conditional means of the zero test function vanish. -/
theorem davisSegmentConditionalActiveMean_zero_fun
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (z : DavisState Q n) (u v : ℝ≥0) :
    davisSegmentConditionalActiveMean S hflow (fun _ => (0 : ℝ)) z u v = 0 := by
  simp [davisSegmentConditionalActiveMean,
    davisSegmentResetOccupationCompensator_zero_fun]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The conditional step law holds for the zero test function. -/
theorem DavisSegmentConditionalStepLaw.of_zero_test_function
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (N : ℕ) :
    DavisSegmentConditionalStepLaw S hflow P ξ.fullFiltration ξ hne initial
      (fun _ => (0 : ℝ)) N := by
  have hzero : ∀ t : ℝ≥0, davisElapsedOccupationSegmentContribution
      S hflow ξ hne initial (fun _ => (0 : ℝ)) N t = fun _ => (0 : ℝ) := by
    intro t
    funext ω
    exact davisElapsedOccupationSegmentContribution_zero_fun
      S hflow ξ hne initial N t ω
  have hcomp : ∀ t : ℝ≥0, davisSegmentCompletedPart
      S hflow ξ initial (fun _ => (0 : ℝ)) N t = fun _ => (0 : ℝ) := by
    intro t
    funext ω
    exact davisSegmentCompletedPart_zero_fun S hflow ξ initial N t ω
  have hact : ∀ t : ℝ≥0, davisSegmentActivePart
      S hflow ξ initial (fun _ => (0 : ℝ)) N t = fun _ => (0 : ℝ) := by
    intro t
    funext ω
    exact davisSegmentActivePart_zero_fun S hflow ξ initial N t ω
  refine
    { adapted := fun t => ?_
      jumpTime_observable := fun k t => ?_
      integrable_completedPart := fun t => ?_
      integrable_activePart := fun t => ?_
      integrableOn_conditionalActiveMean := fun s t _ => ?_
      completed_conditional := fun s t _ A _ _ => ?_
      active_conditional := fun s t _ A _ _ => ?_
      fresh_centered := fun s t _ A _ _ => ?_ }
  · rw [hzero t]
    exact stronglyMeasurable_const
  · exact (hξ.jumpTime k) measurableSet_Iic
  · rw [hcomp t]
    exact integrable_zero _ _ _
  · rw [hact t]
    exact integrable_zero _ _ _
  · simp only [davisSegmentConditionalActiveMean_zero_fun]
    exact integrableOn_zero
  · simp only [hcomp t, davisSegmentConditionalCompletedMean,
      davisExpectedResetIncrement_zero_fun,
      davisSegmentResetOccupationCompensator_zero_fun]
    simp
  · simp only [hact t, davisSegmentConditionalActiveMean_zero_fun]
  · simp only [hzero t]
    simp

end SHS
