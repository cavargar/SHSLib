import SHSLib.Core.DavisElapsedOccupationPathFiltration
import SHSLib.Core.DavisElapsedAccumulatedHazardMeasurable
import SHSLib.Core.DavisOneSegmentConditionalStep

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Instances of current-state observability

The natural state-path filtration satisfies the componentwise observability
interface as soon as the three elapsed occupation components are measurable
functions of the current augmented state.  That hypothesis is stated abstractly
in `DavisElapsedOccupationCurrentStateObservable`; this module verifies it for
concrete model classes, so the martingale theory for the state-path filtration
is not vacuous.

Three instances are given.

* **Constant components.**  Whenever the three components do not depend on the
  sample point, current-state observability holds with constant reporting
  functions.  This is the criterion used by the next two instances.
* **The zero test function**, and, more generally, deterministic jump noise:
  if the holding times and the channel marks are the same for every sample
  point, every component is a deterministic function of the elapsed time and
  the jump cap alone.
* **Segment-history encodings.**  If the augmented state exposes the index of
  the active segment, the realized reset increment and the sampled occupation
  of each completed segment, and the partial occupation accumulated on the
  active segment, then the three components — which additionally depend on the
  deterministic jump cap and on the elapsed time — are recovered from the
  current state by a randomly indexed finite sum.  This is the model class the
  theory is aimed at: a state that carries the elapsed time since the last
  reset together with the accumulated reset bookkeeping.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The constant criterion -/

/-- If the three elapsed occupation components do not depend on the sample
point, current-state observability holds with constant reporting functions. -/
def davisElapsedOccupationCurrentStateObservable_of_constant
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (cr cc ca : ℕ → ℝ≥0 → ℝ)
    (hr : ∀ N t ω, davisStoppedElapsedRealizedResetContribution
      S hflow ξ hne initial g N t ω = cr N t)
    (hc : ∀ N t ω, davisStoppedElapsedCompletedResetOccupation
      S hflow ξ hne initial g N t ω = cc N t)
    (ha : ∀ N t ω, davisStoppedElapsedActiveResetOccupation
      S hflow ξ hne initial g N t ω = ca N t) :
    DavisElapsedOccupationCurrentStateObservable S hflow ξ hne initial g where
  realized N t := fun _ => cr N t
  realized_measurable _ _ := measurable_const
  realized_eq N t ω := hr N t ω
  completed N t := fun _ => cc N t
  completed_measurable _ _ := measurable_const
  completed_eq N t ω := hc N t ω
  active N t := fun _ => ca N t
  active_measurable _ _ := measurable_const
  active_eq N t ω := ha N t ω

/-! ## The zero test function -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The realized reset increment of the zero test function vanishes. -/
theorem davisRealizedResetIncrement_zero_fun
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n) (k : ℕ) (ω : Ω) :
    davisRealizedResetIncrement S hflow ξ initial (fun _ => (0 : ℝ)) k ω = 0 := by
  simp [davisRealizedResetIncrement]

/-- Current-state observability for the zero test function. -/
def davisElapsedOccupationCurrentStateObservable_zero_fun
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) :
    DavisElapsedOccupationCurrentStateObservable S hflow ξ hne initial
      (fun _ => (0 : ℝ)) := by
  refine davisElapsedOccupationCurrentStateObservable_of_constant
    S hflow ξ hne initial _ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun N t ω => ?_) (fun N t ω => ?_) (fun N t ω => ?_)
  · simp [davisStoppedElapsedRealizedResetContribution,
      davisFiniteRealizedResetSum, davisRealizedResetIncrement_zero_fun]
  · simp [davisStoppedElapsedCompletedResetOccupation,
      davisFiniteResetOccupation, davisSegmentResetOccupationCompensator_zero_fun]
  · simp [davisStoppedElapsedActiveResetOccupation,
      davisSegmentResetOccupationCompensator_zero_fun]

/-! ## Deterministic jump noise -/

/-- Jump noise whose holding times and channel marks do not depend on the
sample point. -/
structure DavisJumpNoise.Deterministic {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) : Prop where
  holdingTime_const : ∀ k ω ω', ξ.holdingTime k ω = ξ.holdingTime k ω'
  channel_const : ∀ k ω ω', ξ.channel k ω = ξ.channel k ω'

/-- The active segment index is characterized by bracketing the elapsed time
between two consecutive cumulative jump times. -/
theorem DavisJumpNoise.activeSegmentIndex_eq_of_bracket {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (t : ℝ≥0) (ω : Ω) (k : ℕ) (hle : ξ.jumpTime k ω ≤ t)
    (hlt : t < ξ.jumpTime (k + 1) ω) :
    ξ.activeSegmentIndex hne t ω = k := by
  unfold DavisJumpNoise.activeSegmentIndex
  apply Nat.sub_eq_of_eq_add
  exact (Nat.find_eq_iff _).2 ⟨hlt, fun j hj => fun h =>
    not_lt.mpr (le_trans (ξ.jumpTime_mono ω (Nat.le_of_lt_succ hj)) hle) h⟩

theorem DavisJumpNoise.Deterministic.jumpTime_const {m : ℕ} {Ω : Type*}
    {ξ : DavisJumpNoise m Ω} (hdet : ξ.Deterministic) (k : ℕ) (ω ω' : Ω) :
    ξ.jumpTime k ω = ξ.jumpTime k ω' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [DavisJumpNoise.jumpTime_succ, DavisJumpNoise.jumpTime_succ, ih,
      hdet.holdingTime_const k ω ω']

theorem DavisJumpNoise.Deterministic.activeSegmentIndex_const {m : ℕ} {Ω : Type*}
    {ξ : DavisJumpNoise m Ω} (hdet : ξ.Deterministic) (hne : ξ.NonExplosive)
    (t : ℝ≥0) (ω ω' : Ω) :
    ξ.activeSegmentIndex hne t ω = ξ.activeSegmentIndex hne t ω' := by
  refine ξ.activeSegmentIndex_eq_of_bracket hne t ω _ ?_ ?_
  · rw [hdet.jumpTime_const _ ω ω']
    exact ξ.jumpTime_activeSegmentIndex_le hne t ω'
  · rw [hdet.jumpTime_const _ ω ω']
    exact ξ.lt_jumpTime_activeSegmentIndex_succ hne t ω'

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
theorem DavisJumpNoise.Deterministic.stateAfterJump_const
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    {ξ : DavisJumpNoise m Ω} (hdet : ξ.Deterministic)
    (initial : DavisState Q n) (k : ℕ) (ω ω' : Ω) :
    davisStateAfterJump S hflow ξ initial k ω =
      davisStateAfterJump S hflow ξ initial k ω' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show S.resetDavisState (ξ.channel k ω)
        (davisFlow S hflow (ξ.holdingTime k ω)
          (davisStateAfterJump S hflow ξ initial k ω)) =
      S.resetDavisState (ξ.channel k ω')
        (davisFlow S hflow (ξ.holdingTime k ω')
          (davisStateAfterJump S hflow ξ initial k ω'))
    rw [ih, hdet.channel_const k ω ω', hdet.holdingTime_const k ω ω']

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
theorem DavisJumpNoise.Deterministic.stateBeforeJump_const
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    {ξ : DavisJumpNoise m Ω} (hdet : ξ.Deterministic)
    (initial : DavisState Q n) (k : ℕ) (ω ω' : Ω) :
    davisStateBeforeJump S hflow ξ initial k ω =
      davisStateBeforeJump S hflow ξ initial k ω' := by
  simp only [davisStateBeforeJump, hdet.holdingTime_const k ω ω',
    hdet.stateAfterJump_const S hflow initial k ω ω']

/-- With deterministic jump noise, every model quantity along a trajectory is
the same for all sample points, so current-state observability holds. -/
def davisElapsedOccupationCurrentStateObservable_of_deterministic
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [Nonempty Ω] {ξ : DavisJumpNoise m Ω}
    (hdet : ξ.Deterministic) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) :
    DavisElapsedOccupationCurrentStateObservable S hflow ξ hne initial g := by
  classical
  set ω₀ : Ω := Classical.arbitrary Ω with hω₀
  have hcur : ∀ (k : ℕ) (ω ω' : Ω),
      (davisPreJumpHistory S hflow ξ initial k ω).currentState =
        (davisPreJumpHistory S hflow ξ initial k ω').currentState := by
    intro k ω ω'
    show davisStateAfterJump S hflow ξ initial (Fin.last k) ω =
      davisStateAfterJump S hflow ξ initial (Fin.last k) ω'
    exact hdet.stateAfterJump_const S hflow initial _ ω ω'
  refine davisElapsedOccupationCurrentStateObservable_of_constant
    S hflow ξ hne initial g
    (fun N t => davisStoppedElapsedRealizedResetContribution
      S hflow ξ hne initial g N t ω₀)
    (fun N t => davisStoppedElapsedCompletedResetOccupation
      S hflow ξ hne initial g N t ω₀)
    (fun N t => davisStoppedElapsedActiveResetOccupation
      S hflow ξ hne initial g N t ω₀)
    (fun N t ω => ?_) (fun N t ω => ?_) (fun N t ω => ?_)
  · unfold davisStoppedElapsedRealizedResetContribution davisFiniteRealizedResetSum
    rw [hdet.activeSegmentIndex_const hne t ω ω₀]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [davisRealizedResetIncrement, hdet.channel_const k ω ω₀,
      hdet.stateBeforeJump_const S hflow initial k ω ω₀]
  · unfold davisStoppedElapsedCompletedResetOccupation davisFiniteResetOccupation
    rw [hdet.activeSegmentIndex_const hne t ω ω₀]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcur k ω ω₀, hdet.holdingTime_const k ω ω₀]
  · unfold davisStoppedElapsedActiveResetOccupation
    simp only [hdet.activeSegmentIndex_const hne t ω ω₀]
    by_cases h : ξ.activeSegmentIndex hne t ω₀ < N
    · simp only [h, ↓reduceIte]
      rw [hdet.stateAfterJump_const S hflow initial _ ω ω₀,
        hdet.jumpTime_const _ ω ω₀]
    · simp only [h, ↓reduceIte]

/-! ## Segment-history encodings -/

/-- A segment-history encoding: the augmented state exposes the index of the
active segment, the realized reset increment and the sampled reset occupation
of every completed segment, and the partial occupation accumulated on the
active segment. -/
structure DavisElapsedOccupationSegmentEncoding
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) where
  /-- Index of the active segment, read off the current state. -/
  index : DavisState Q n → ℕ
  index_measurable : Measurable index
  index_eq : ∀ t ω, index (davisJumpPath S hflow ξ hne initial t ω) =
    ξ.activeSegmentIndex hne t ω
  /-- Realized reset increment of a completed segment, read off the current
  state. -/
  realizedIncrement : DavisState Q n → ℕ → ℝ
  realizedIncrement_measurable : ∀ j, Measurable fun z => realizedIncrement z j
  realizedIncrement_eq : ∀ t ω j, j < ξ.activeSegmentIndex hne t ω →
    realizedIncrement (davisJumpPath S hflow ξ hne initial t ω) j =
      davisRealizedResetIncrement S hflow ξ initial g j ω
  /-- Sampled reset occupation of a completed segment, read off the current
  state. -/
  segmentOccupation : DavisState Q n → ℕ → ℝ
  segmentOccupation_measurable : ∀ j, Measurable fun z => segmentOccupation z j
  segmentOccupation_eq : ∀ t ω j, j < ξ.activeSegmentIndex hne t ω →
    segmentOccupation (davisJumpPath S hflow ξ hne initial t ω) j =
      davisSegmentResetOccupationCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial j ω).currentState
        (ξ.holdingTime j ω)
  /-- Partial occupation accumulated on the active segment, read off the
  current state. -/
  activeOccupation : DavisState Q n → ℝ
  activeOccupation_measurable : Measurable activeOccupation
  activeOccupation_eq : ∀ t ω,
    activeOccupation (davisJumpPath S hflow ξ hne initial t ω) =
      davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial
          (ξ.activeSegmentIndex hne t ω) ω)
        (t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω)

/-- A segment-history encoding gives current-state observability: each
component is the finite sum of the encoded per-segment quantities below the
jump cap, plus, for the active component, the encoded partial occupation. -/
def DavisElapsedOccupationSegmentEncoding.currentStateObservable
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (henc : DavisElapsedOccupationSegmentEncoding S hflow ξ hne initial g) :
    DavisElapsedOccupationCurrentStateObservable S hflow ξ hne initial g where
  realized N _ := fun z =>
    ∑ j ∈ Finset.range (min N (henc.index z)), henc.realizedIncrement z j
  realized_measurable N _ :=
    measurable_sum_range_measurable_index
      (fun z => min N (henc.index z))
      (measurable_from_top.comp henc.index_measurable)
      (fun j z => henc.realizedIncrement z j)
      (fun j => henc.realizedIncrement_measurable j)
  realized_eq N t ω := by
    unfold davisStoppedElapsedRealizedResetContribution davisFiniteRealizedResetSum
    rw [henc.index_eq t ω]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact (henc.realizedIncrement_eq t ω j
      (lt_of_lt_of_le (Finset.mem_range.1 hj) (min_le_right _ _))).symm
  completed N _ := fun z =>
    ∑ j ∈ Finset.range (min N (henc.index z)), henc.segmentOccupation z j
  completed_measurable N _ :=
    measurable_sum_range_measurable_index
      (fun z => min N (henc.index z))
      (measurable_from_top.comp henc.index_measurable)
      (fun j z => henc.segmentOccupation z j)
      (fun j => henc.segmentOccupation_measurable j)
  completed_eq N t ω := by
    unfold davisStoppedElapsedCompletedResetOccupation davisFiniteResetOccupation
    rw [henc.index_eq t ω]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact (henc.segmentOccupation_eq t ω j
      (lt_of_lt_of_le (Finset.mem_range.1 hj) (min_le_right _ _))).symm
  active N _ := fun z => if henc.index z < N then henc.activeOccupation z else 0
  active_measurable N _ := by
    refine Measurable.ite ?_ henc.activeOccupation_measurable measurable_const
    exact henc.index_measurable (measurableSet_lt measurable_id measurable_const)
  active_eq N t ω := by
    unfold davisStoppedElapsedActiveResetOccupation
    rw [henc.index_eq t ω]
    by_cases h : ξ.activeSegmentIndex hne t ω < N
    · simp only [h, ↓reduceIte]
      exact (henc.activeOccupation_eq t ω).symm
    · simp only [h, ↓reduceIte]

/-- The martingale property for the natural state-path filtration under a
segment-history encoding. -/
theorem DavisElapsedOccupationSegmentEncoding.martingale_natural
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (henc : DavisElapsedOccupationSegmentEncoding S hflow ξ hne initial g)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.naturalPathFiltration S hflow hf hr hξ hne initial)
      ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g)
      (ξ.naturalPathFiltration S hflow hf hr hξ hne initial) P :=
  DavisStoppedElapsedOccupationIncrementLaw.martingale_natural
    (hf := hf) (hr := hr) hreg P hξ initial hg
    henc.currentStateObservable hlaw henv

end SHS
