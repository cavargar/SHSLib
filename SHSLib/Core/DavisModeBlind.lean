import SHSLib.Core.DavisTransitionFree

open MeasureTheory MeasurableSpace Topology Filter
open scoped ENNReal NNReal

noncomputable section

/-! # Theorem 1 for systems whose resets only move the discrete mode

`SHSLib.Core.DavisTransitionFree` inhabits the hypothesis bundles of
`SHS.theorem1_generator_formula` for a system with no transition channels at
all, so the sample path there is deterministic.  This module removes that
restriction: it allows an arbitrary number `m` of transition channels, driven
by arbitrary jump noise on an arbitrary probability space, and only asks that
none of the data of the problem should *see* the discrete mode:

* the drift, the flow, the intensities and the test function do not depend on
  the mode;
* the reset maps leave the continuous state unchanged (they may permute the
  mode arbitrarily).

The mode is then a genuinely random component of the state — jumps occur at the
random times sampled by the noise — while everything that enters Eq. (8) is
evaluated along the deterministic flow.  In particular the jump part of the
extended generator vanishes and the compensated jump process is identically
zero, so all the Davis data can again be constructed.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}

/-- **Mode-blind data.**  None of the ingredients of the SHS or of the test
function depends on the discrete mode, and the reset channels do not move the
continuous state.  Channels may relabel the mode arbitrarily. -/
structure ModeBlind (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (ψ : TestFunction Q n) : Prop where
  /-- The drift does not depend on the mode. -/
  drift : ∀ q q' x t, S.f q x t = S.f q' x t
  /-- The flow does not depend on the mode. -/
  flow : ∀ t₀ q q' x t, hflow.flow t₀ q x t = hflow.flow t₀ q' x t
  /-- Resets leave the continuous state unchanged. -/
  reset_state : ∀ ℓ q x t, S.phi_x ℓ q x t = x
  /-- The intensities do not depend on the mode. -/
  intensity : ∀ ℓ q q' x t, S.intensity ℓ q x t = S.intensity ℓ q' x t
  /-- The test function does not depend on the mode. -/
  test : ∀ q q' x t, ψ.toFun q x t = ψ.toFun q' x t
  /-- Its spatial gradient does not depend on the mode. -/
  grad : ∀ q q' x t, ψ.grad_x q x t = ψ.grad_x q' x t
  /-- Its time derivative does not depend on the mode. -/
  time_deriv : ∀ q q' x t, ψ.partial_t q x t = ψ.partial_t q' x t

namespace ModeBlind

variable {S : SHS Q n m} {hflow : S.HasGlobalFlow} {ψ : TestFunction Q n}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Two augmented states with the same continuous coordinate and clock have the
same lifted test value. -/
theorem toDavisFunction_congr (h : ModeBlind S hflow ψ) {z w : DavisState Q n}
    (hzw : z.2 = w.2) : ψ.toDavisFunction z = ψ.toDavisFunction w := by
  obtain ⟨q, x, t⟩ := z
  obtain ⟨q', x', t'⟩ := w
  cases hzw
  exact h.test q q' x t

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Two augmented states with the same continuous coordinate and clock have the
same flow generator value. -/
theorem flowGenerator_congr (h : ModeBlind S hflow ψ) {z w : DavisState Q n}
    (hzw : z.2 = w.2) : S.flowGenerator ψ z = S.flowGenerator ψ w := by
  obtain ⟨q, x, t⟩ := z
  obtain ⟨q', x', t'⟩ := w
  cases hzw
  simp only [SHS.flowGenerator]
  rw [h.grad q q' x t, h.drift q q' x t, h.time_deriv q q' x t]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Two augmented states with the same continuous coordinate and clock have the
same total intensity. -/
theorem totalIntensity_congr (h : ModeBlind S hflow ψ) {z w : DavisState Q n}
    (hzw : z.2 = w.2) : S.totalIntensity z = S.totalIntensity w := by
  obtain ⟨q, x, t⟩ := z
  obtain ⟨q', x', t'⟩ := w
  cases hzw
  exact Finset.sum_congr rfl fun ℓ _ => h.intensity ℓ q q' x t

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A reset does not change the lifted test value. -/
theorem toDavisFunction_reset (h : ModeBlind S hflow ψ) (ℓ : Fin m)
    (z : DavisState Q n) :
    ψ.toDavisFunction (S.resetDavisState ℓ z) = ψ.toDavisFunction z := by
  refine h.toDavisFunction_congr ?_
  simp [SHS.resetDavisState, h.reset_state]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- **The jump term of the extended generator vanishes.** -/
theorem extendedGenerator_eq_flowGenerator (h : ModeBlind S hflow ψ)
    (z : DavisState Q n) :
    S.extendedGenerator ψ z.1 z.2.1 z.2.2 = S.flowGenerator ψ z := by
  have hzero : ∀ ℓ : Fin m,
      (ψ.toFun (S.phi_q ℓ z.1 z.2.1 z.2.2) (S.phi_x ℓ z.1 z.2.1 z.2.2) z.2.2 -
        ψ.toFun z.1 z.2.1 z.2.2) * S.intensity ℓ z.1 z.2.1 z.2.2 = 0 := by
    intro ℓ
    have := h.toDavisFunction_reset ℓ z
    simp only [TestFunction.toDavisFunction, SHS.resetDavisState] at this
    rw [this]
    ring
  simp only [SHS.extendedGenerator, SHS.flowGenerator]
  rw [Finset.sum_congr rfl fun ℓ _ => hzero ℓ]
  simp

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The augmented flow does not see the mode. -/
theorem davisFlow_snd (h : ModeBlind S hflow ψ) (u : ℝ≥0)
    {z w : DavisState Q n} (hzw : z.2 = w.2) :
    (davisFlow S hflow u z).2 = (davisFlow S hflow u w).2 := by
  obtain ⟨q, x, t⟩ := z
  obtain ⟨q', x', t'⟩ := w
  cases hzw
  simp only [davisFlow]
  rw [h.flow t q q' x (t + (u : ℝ))]

/-- Along the recursive post-jump chain, the continuous coordinate and the
clock agree with the deterministic augmented flow. -/
theorem stateAfterJump_snd (h : ModeBlind S hflow ψ)
    (hf : DavisFlowRegular S hflow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (k : ℕ) (ω : Ω) :
    (davisStateAfterJump S hflow ξ initial k ω).2 =
      (davisFlow S hflow (ξ.jumpTime k ω) initial).2 := by
  induction k with
  | zero => simp [davisFlow, hflow.flow_init]
  | succ k ih =>
    have hreset : (davisStateAfterJump S hflow ξ initial (k + 1) ω).2 =
        (davisFlow S hflow (ξ.holdingTime k ω)
          (davisStateAfterJump S hflow ξ initial k ω)).2 := by
      show (S.resetDavisState (ξ.channel k ω)
        (davisFlow S hflow (ξ.holdingTime k ω)
          (davisStateAfterJump S hflow ξ initial k ω))).2 = _
      simp [SHS.resetDavisState, h.reset_state]
    rw [hreset, h.davisFlow_snd (ψ := ψ) (ξ.holdingTime k ω) ih,
      ← hf.add, DavisJumpNoise.jumpTime_succ, add_comm (ξ.jumpTime k ω)]

/-- **The observable part of the sample path is deterministic.**  Along the
assembled jump path the continuous coordinate and the clock coincide with those
of the deterministic augmented flow. -/
theorem jumpPath_snd (h : ModeBlind S hflow ψ) (hf : DavisFlowRegular S hflow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    (davisJumpPath S hflow ξ hne initial t ω).2 =
      (davisFlow S hflow t initial).2 := by
  set k := ξ.activeSegmentIndex hne t ω with hk
  have hle : ξ.jumpTime k ω ≤ t := ξ.jumpTime_activeSegmentIndex_le hne t ω
  have hmin : min (t - ξ.jumpTime k ω) (ξ.holdingTime k ω)
      = t - ξ.jumpTime k ω :=
    min_eq_left (ξ.activeSegmentElapsed_le_holdingTime hne t ω)
  show (davisJumpSegment S hflow ξ initial k (t - ξ.jumpTime k ω) ω).2 = _
  rw [davisJumpSegment, hmin,
    h.davisFlow_snd (ψ := ψ) (t - ξ.jumpTime k ω)
      (h.stateAfterJump_snd (ψ := ψ) hf ξ initial k ω),
    ← hf.add, tsub_add_cancel_of_le hle]

end ModeBlind

/-! ## The realization driven by arbitrary jump noise -/

/-- Standing regularity for the mode-blind construction: mode blindness, the
`C¹` conditions of the deterministic Dynkin identity, and Davis's domain
conditions for the lifted test function. -/
structure ModeBlindRegular (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (ψ : TestFunction Q n) : Prop where
  blind : ModeBlind S hflow ψ
  partials : ψ.HasPartials
  drift_cont : ∀ q x t₀ t₁,
    ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s) (Set.Icc t₀ t₁)
  gen_cont : ∀ q x t₀ t₁,
    ContinuousOn (fun s => S.flowGenerator ψ (q, hflow.flow t₀ q x s, s))
      (Set.Icc t₀ t₁)
  measurable : Measurable ψ.toDavisFunction
  bounded : ∃ C : ℝ, ∀ z, |ψ.toDavisFunction z| ≤ C

section Realization

variable (S : SHS Q n m) (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
  (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
  (hli : DavisLocallyIntegrable S hflow) (hne : DavisNonExplosive S hflow hf hr)
  {Ω : Type*} [mOmega : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (filtration : Filtration ℝ≥0 mOmega) [SigmaFiniteFiltration P filtration]
  (ξ : DavisJumpNoise m Ω) (hxi : ξ.NonExplosive)
  (hpos : ξ.PositiveHoldingTimes) (initial : DavisState Q n)

/-- The Davis process realization of a mode-blind SHS driven by arbitrary jump
noise. -/
def modeBlindRealization : DavisProcessRealization S hflow hf hr hli hne :=
  DavisProcessRealization.ofJumpNoise S hflow hf hr hli hne P filtration ξ hxi
    hpos initial

@[simp] theorem modeBlindRealization_Omega :
    (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
      initial).Omega = Ω := rfl

@[simp] theorem modeBlindRealization_process (t : ℝ≥0) (ω : Ω) :
    (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
        initial).process t ω = davisJumpPath S hflow ξ hxi initial t ω := rfl

@[simp] theorem modeBlindRealization_P :
    (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
      initial).P = P := rfl

@[simp] theorem modeBlindRealization_filtration :
    (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
      initial).filtration = filtration := rfl

variable {ψ : TestFunction Q n}

omit [S.IntensitiesMeasurable] mOmega in
include hf in
/-- Along the realized path the lifted test function is deterministic. -/
theorem modeBlind_toDavisFunction_process (h : ModeBlind S hflow ψ)
    (t : ℝ≥0) (ω : Ω) :
    ψ.toDavisFunction (davisJumpPath S hflow ξ hxi initial t ω) =
      ψ.toDavisFunction (davisFlow S hflow t initial) :=
  h.toDavisFunction_congr (h.jumpPath_snd hf ξ hxi initial t ω)

omit mOmega in
/-- Along the realized path the Davis generator of the lifted test function is
the deterministic flow generator. -/
theorem modeBlind_pdpGenerator_process (h : ModeBlind S hflow ψ)
    (hmeas : Measurable ψ.toDavisFunction) (t : ℝ≥0) (ω : Ω) :
    Davis.pdpGenerator (toDavisPDPStandard S hflow hf hr hli hne).toPDP
        (S.flowGenerator ψ) ψ.toDavisFunction
        (davisJumpPath S hflow ξ hxi initial t ω) =
      S.flowGenerator ψ (davisFlow S hflow t initial) := by
  show Davis.pdpGenerator (toDavisPDP S hflow hf hr) (S.flowGenerator ψ)
      ψ.toDavisFunction (davisJumpPath S hflow ξ hxi initial t ω) = _
  rw [(toDavisPDP_compatible S hflow hf hr).pdpGenerator_eq_extendedGenerator
    ψ hmeas, h.extendedGenerator_eq_flowGenerator]
  exact h.flowGenerator_congr (h.jumpPath_snd hf ξ hxi initial t ω)

omit [S.IntensitiesMeasurable] mOmega in
include hf in
/-- Along the realized path the SHS extended generator is deterministic. -/
theorem modeBlind_extendedGenerator_process (h : ModeBlind S hflow ψ)
    (t : ℝ≥0) (ω : Ω) :
    S.extendedGenerator ψ (davisJumpPath S hflow ξ hxi initial t ω).1
        (davisJumpPath S hflow ξ hxi initial t ω).2.1
        (davisJumpPath S hflow ξ hxi initial t ω).2.2 =
      S.flowGenerator ψ (davisFlow S hflow t initial) := by
  rw [h.extendedGenerator_eq_flowGenerator]
  exact h.flowGenerator_congr (h.jumpPath_snd hf ξ hxi initial t ω)

omit mOmega in
include hpos in
/-- **The compensated test process of a mode-blind realization vanishes.** -/
theorem modeBlind_compensated_eq_zero (hreg : ModeBlindRegular S hflow ψ)
    (s : ℝ≥0) (ω : Ω) :
    ψ.toDavisFunction (davisJumpPath S hflow ξ hxi initial s ω) -
        ψ.toDavisFunction (davisJumpPath S hflow ξ hxi initial 0 ω) -
        (∫ u in Set.Icc (0 : ℝ) (s : ℝ),
          Davis.pdpGenerator (toDavisPDPStandard S hflow hf hr hli hne).toPDP
            (S.flowGenerator ψ) ψ.toDavisFunction
            (davisJumpPath S hflow ξ hxi initial u.toNNReal ω)) = 0 := by
  have hzero : davisJumpPath S hflow ξ hxi initial 0 ω = initial :=
    davisJumpPath_zero S hflow ξ hxi hpos initial ω
  have hint : (∫ u in Set.Icc (0 : ℝ) (s : ℝ),
      Davis.pdpGenerator (toDavisPDPStandard S hflow hf hr hli hne).toPDP
        (S.flowGenerator ψ) ψ.toDavisFunction
        (davisJumpPath S hflow ξ hxi initial u.toNNReal ω)) =
      ∫ u in Set.Icc (0 : ℝ) (s : ℝ),
        S.flowGenerator ψ (davisFlow S hflow u.toNNReal initial) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    exact modeBlind_pdpGenerator_process S hflow hf hr hli hne ξ hxi initial
      hreg.blind hreg.measurable u.toNNReal ω
  have hkey := flowGenerator_integral_elapsed S hflow ψ hreg.partials
    hreg.drift_cont hreg.gen_cont initial (s.coe_nonneg)
  rw [Real.toNNReal_coe] at hkey
  rw [hint, hkey, hzero,
    modeBlind_toDavisFunction_process S hflow hf ξ hxi initial hreg.blind s ω]
  ring

/-- Davis's domain regularity for the lifted test function. -/
theorem modeBlindTestFunctionRegular (hreg : ModeBlindRegular S hflow ψ) :
    DavisTestFunctionRegular S hflow hf hr hli hne
      (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
        initial) ψ where
  measurable := hreg.measurable
  flow_regular := fun z =>
    (continuous_testFun_along_davisFlow S hflow ψ hreg.partials
      hreg.drift_cont z).locallyIntegrable
  bounded := hreg.bounded

/-- **The compensator data of a mode-blind realization.**  The compensated jump
process vanishes identically, so the localizing sequence may be taken
deterministic. -/
def modeBlindCompensatorData (hreg : ModeBlindRegular S hflow ψ) :
    DavisCompensatorData S hflow hf hr hli hne
      (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
        initial) ψ where
  sigma := fun k _ => (k : ℝ≥0)
  sigma_stopping := fun k => isStoppingTime_const _ _
  sigma_tendsto := Filter.Eventually.of_forall (fun _ => by
    simpa using ENNReal.tendsto_nat_nhds_top)
  jumpCompensated := fun _ _ => 0
  decomposition := by
    intro k t ω
    rw [← NNReal.coe_min]
    exact modeBlind_compensated_eq_zero S hflow hf hr hli hne ξ hxi hpos initial
      hreg (min t (k : ℝ≥0)) ω
  jump_martingale := fun k => by
    simpa using martingale_zero (Ω := Ω) ℝ filtration P

/-- **The true-martingale data of a mode-blind realization.**  Every quantity
appearing in conditions (15)–(16) is deterministic, so integrability on a
probability space is automatic, and the compensated process is zero. -/
def modeBlindTrueMartingaleData (hreg : ModeBlindRegular S hflow ψ) :
    DavisTrueMartingaleData S hflow hf hr hli hne
      (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
        initial) ψ where
  finite_transitions := fun t => by
    have hconst : (fun ω => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        S.totalIntensity (davisJumpPath S hflow ξ hxi initial u.toNNReal ω)) =
        fun _ : Ω => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          S.totalIntensity (davisFlow S hflow u.toNNReal initial) := by
      funext ω
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
      exact hreg.blind.totalIntensity_congr
        (hreg.blind.jumpPath_snd hf ξ hxi initial u.toNNReal ω)
    rw [show (fun ω => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
      S.totalIntensity ((modeBlindRealization S hflow hf hr hli hne P filtration
        ξ hxi hpos initial).process u.toNNReal ω)) = _ from hconst]
    exact integrable_const _
  finite_jumps := fun t => by
    refine (integrable_zero Ω ℝ P).congr ?_
    filter_upwards with ω
    symm
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun u _ => ?_
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hreg.blind.toDavisFunction_reset l]
    simp
  endpoint_integrable := fun t => by
    rw [show (fun ω => ψ.toDavisFunction
        ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
          initial).process t ω)) =
        fun _ : Ω => ψ.toDavisFunction (davisFlow S hflow t initial) from
      funext fun ω => modeBlind_toDavisFunction_process S hflow hf ξ hxi initial
        hreg.blind t ω]
    exact integrable_const _
  generator_integrable := fun t => by
    have hconst : ∀ ω : Ω, (∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        S.extendedGenerator ψ (davisJumpPath S hflow ξ hxi initial u.toNNReal ω).1
          (davisJumpPath S hflow ξ hxi initial u.toNNReal ω).2.1
          (davisJumpPath S hflow ξ hxi initial u.toNNReal ω).2.2) =
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          S.flowGenerator ψ (davisFlow S hflow u.toNNReal initial) := by
      intro ω
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
      exact modeBlind_extendedGenerator_process S hflow hf ξ hxi initial
        hreg.blind u.toNNReal ω
    rw [show (fun ω => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
      S.extendedGenerator ψ ((modeBlindRealization S hflow hf hr hli hne P
          filtration ξ hxi hpos initial).process u.toNNReal ω).1
        ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
          initial).process u.toNNReal ω).2.1
        ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
          initial).process u.toNNReal ω).2.2) =
        fun _ : Ω => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          S.flowGenerator ψ (davisFlow S hflow u.toNNReal initial) from
      funext hconst]
    exact integrable_const _
  adapted := by
    intro t
    have hconst : Measurable[filtration t] (fun _ : Ω => (0 : ℝ)) :=
      measurable_const
    convert hconst using 1
    funext ω
    exact modeBlind_compensated_eq_zero S hflow hf hr hli hne ξ hxi hpos initial
      hreg t ω
  envelope := fun _ => 0
  envelope_integrable := integrable_const _
  dominated := by
    intro t ω
    simp only [modeBlindRealization_process]
    rw [modeBlind_compensated_eq_zero S hflow hf hr hli hne ξ hxi hpos initial
      hreg t ω]
    simp

/-! ## Hespanha's Eq. (8) for a mode-blind SHS with jumps -/

@[simp] theorem modeBlindRealization_initial :
    (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
      initial).initial = initial := rfl

/-- The continuous coordinate of the realization, read in absolute time, is the
deterministic flow. -/
theorem modeBlind_xProcAbsolute (h : ModeBlind S hflow ψ)
    (z₀ : InitialCondition Q n) {s : ℝ} (hs : z₀.t₀ ≤ s) (ω : Ω) :
    (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
        z₀.toDavisState).xProcAbsolute s ω =
      hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s := by
  have hsub : (((s - z₀.t₀).toNNReal : ℝ≥0) : ℝ) = s - z₀.t₀ :=
    Real.coe_toNNReal _ (by linarith)
  have h1 : (davisJumpPath S hflow ξ hxi z₀.toDavisState
        (s - z₀.t₀).toNNReal ω).2.1 =
      (davisFlow S hflow (s - z₀.t₀).toNNReal z₀.toDavisState).2.1 :=
    congrArg Prod.fst
      (h.jumpPath_snd hf ξ hxi z₀.toDavisState (s - z₀.t₀).toNNReal ω)
  show (davisJumpPath S hflow ξ hxi z₀.toDavisState
    (s - z₀.t₀).toNNReal ω).2.1 = _
  rw [h1]
  simp only [davisFlow, InitialCondition.toDavisState, hsub]
  congr 1
  ring

include hf hr hli hne P filtration ξ hxi hpos in
/-- **Hespanha's Eq. (8) for a mode-blind SHS driven by arbitrary jump noise.**

The transition channels fire at the random times sampled by `ξ`, so the sample
path really does jump; because none of the data of the problem sees the
discrete mode, the expectation in Eq. (8) collapses and the identity holds
pathwise.  As in the transition-free case, all the Davis data required by
`SHS.theorem1_generator_formula` are constructed rather than assumed. -/
theorem eq8_modeBlind [Fintype Q] (hreg : ModeBlindRegular S hflow ψ)
    (z₀ : InitialCondition Q n) (t : ℝ≥0) :
    ψ.toFun z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ (z₀.t₀ + (t : ℝ)))
        (z₀.t₀ + (t : ℝ)) =
      ψ.toFun z₀.q₀ z₀.x₀ z₀.t₀ +
        ∫ s in Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ)),
          S.extendedGenerator ψ z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s := by
  have hle : z₀.t₀ ≤ z₀.t₀ + (t : ℝ) := by
    have : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
    linarith
  have h := theorem1_generator_formula S hflow hf hr (hli := hli) (hne := hne)
    (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
      z₀.toDavisState) ψ
    (modeBlindTestFunctionRegular S hflow hf hr hli hne P filtration ξ hxi hpos
      z₀.toDavisState hreg)
    (modeBlindCompensatorData S hflow hf hr hli hne P filtration ξ hxi hpos
      z₀.toDavisState hreg)
    (modeBlindTrueMartingaleData S hflow hf hr hli hne P filtration ξ hxi hpos
      z₀.toDavisState hreg)
    z₀ rfl t
  have hpsi : ∀ (s : ℝ), z₀.t₀ ≤ s →
      ∀ ω : (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
        z₀.toDavisState).Omega,
      ψ.toFun ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi
          hpos z₀.toDavisState).qProcAbsolute s ω)
        ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
          z₀.toDavisState).xProcAbsolute s ω) s =
        ψ.toFun z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s := by
    intro s hs ω
    rw [modeBlind_xProcAbsolute S hflow hf hr hli hne P filtration ξ hxi hpos
      hreg.blind z₀ hs ω]
    exact hreg.blind.test _ _ _ _
  have hgen : ∀ (s : ℝ), z₀.t₀ ≤ s →
      ∀ ω : (modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
        z₀.toDavisState).Omega,
      S.extendedGenerator ψ
          ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
            z₀.toDavisState).qProcAbsolute s ω)
          ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
            z₀.toDavisState).xProcAbsolute s ω) s =
        S.extendedGenerator ψ z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s := by
    intro s hs ω
    rw [modeBlind_xProcAbsolute S hflow hf hr hli hne P filtration ξ hxi hpos
      hreg.blind z₀ hs ω,
      hreg.blind.extendedGenerator_eq_flowGenerator
        (_, hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s, s),
      hreg.blind.extendedGenerator_eq_flowGenerator
        (z₀.q₀, hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s, s)]
    exact hreg.blind.flowGenerator_congr rfl
  have hinner : ∀ ω : (modeBlindRealization S hflow hf hr hli hne P filtration
      ξ hxi hpos z₀.toDavisState).Omega,
      (∫ s in Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ)),
      S.extendedGenerator ψ
        ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
          z₀.toDavisState).qProcAbsolute s ω)
        ((modeBlindRealization S hflow hf hr hli hne P filtration ξ hxi hpos
          z₀.toDavisState).xProcAbsolute s ω) s) =
      ∫ s in Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ)),
        S.extendedGenerator ψ z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s := by
    intro ω
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      fun s hs => hgen s hs.1 ω
  rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => hpsi _ hle ω),
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun ω => hinner ω)] at h
  simpa using h

end Realization

end SHS
