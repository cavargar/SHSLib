import SHSLib.Core.DavisNaturalStopping

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Mode-level jump counters for Davis paths

This module gives a model-facing sufficient condition for the observability
interface in `DavisNaturalStopping`.  If a measurable natural-valued rank on
the discrete mode starts at zero and every reset increments it by one, then the
current augmented state records exactly how many resets have occurred.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A measurable rank on modes which is incremented by every reset. -/
structure ModeJumpCounter (S : SHS Q n m) (initial : DavisState Q n) where
  count : Q → ℕ
  measurable_count : Measurable count
  count_initial : count initial.1 = 0
  count_reset : ∀ (ℓ : Fin m) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
    count (S.phi_q ℓ q x t) = count q + 1

/-- The rank of the recursively constructed post-jump mode is the jump index. -/
theorem ModeJumpCounter.count_stateAfterJump
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (hc : ModeJumpCounter S initial) (k : ℕ) (ω : Ω) :
    hc.count (davisStateAfterJump S hflow ξ initial k ω).1 = k := by
  induction k with
  | zero => simp [davisStateAfterJump_zero, hc.count_initial]
  | succ k ih =>
      simp only [davisStateAfterJump_succ, davisStateBeforeJump]
      unfold resetDavisState
      simp only
      rw [hc.count_reset]
      simp only [davisFlow]
      rw [ih]

/-- The mode of the assembled path is the mode of its active post-jump state. -/
theorem davisJumpPath_mode_eq_stateAfterJump
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    (davisJumpPath S hflow ξ hne initial t ω).1 =
      (davisStateAfterJump S hflow ξ initial
        (ξ.activeSegmentIndex hne t ω) ω).1 := by
  simp [davisJumpPath, davisJumpSegment, davisFlow]

/-- A cumulative jump time has occurred by `t` exactly when its index does not
exceed the active segment index. -/
theorem DavisJumpNoise.jumpTime_le_iff_le_activeSegmentIndex
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (k : ℕ) (t : ℝ≥0) (ω : Ω) :
    ξ.jumpTime k ω ≤ t ↔ k ≤ ξ.activeSegmentIndex hne t ω := by
  constructor
  · intro hkt
    by_contra hk_gt
    push_neg at hk_gt
    have : k ≥ ξ.activeSegmentIndex hne t ω + 1 := Nat.succ_le_of_lt hk_gt
    have hk_le : ξ.jumpTime k ω ≥ ξ.jumpTime (ξ.activeSegmentIndex hne t ω + 1) ω :=
      DavisJumpNoise.jumpTime_mono ξ ω this
    have hlt := DavisJumpNoise.lt_jumpTime_activeSegmentIndex_succ ξ hne t ω
    exact not_le.mpr (lt_of_lt_of_le hlt hk_le) hkt
  · intro hk_le_k
    exact le_trans (DavisJumpNoise.jumpTime_mono ξ ω hk_le_k)
      (DavisJumpNoise.jumpTime_activeSegmentIndex_le ξ hne t ω)

/-- A mode-level counter supplies current-state jump-count observability. -/
def ModeJumpCounter.toCurrentStateJumpCountObservable
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hc : ModeJumpCounter S initial) :
    ξ.CurrentStateJumpCountObservable S hflow hne initial where
  jumpCount := fun _ z => hc.count z.1
  jumpCount_measurable := fun _ => hc.measurable_count.comp measurable_fst
  occurred_iff := by
    intro k t ω
    rw [ξ.jumpTime_le_iff_le_activeSegmentIndex hne k t ω]
    rw [davisJumpPath_mode_eq_stateAfterJump S hflow ξ hne initial t ω]
    rw [hc.count_stateAfterJump S hflow ξ initial]

/-- Consequently all cumulative jump times are stopping times for the natural
path filtration whenever the discrete mode carries such a counter. -/
theorem ModeJumpCounter.jumpTime_isStoppingTime_natural
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hc : ModeJumpCounter S initial) (k : ℕ) :
    IsStoppingTime (ξ.naturalPathFiltration S hflow hf hr hξ hne initial)
      (fun ω => ((ξ.jumpTime k ω : ℝ≥0) : ℝ≥0∞)) := by
  exact DavisJumpNoise.CurrentStateJumpCountObservable.jumpTime_isStoppingTime_natural
    S hflow hf hr hξ hne initial
    (hc.toCurrentStateJumpCountObservable S hflow ξ hne initial) k

end SHS
