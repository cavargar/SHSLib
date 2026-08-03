import SHSLib.Core.DavisElapsedResetOccupation

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Elapsed reset occupation stopped by a jump cap

A deterministic jump cap retains the first `N` completed reset increments and
occupation segments.  It also retains the active partial occupation exactly
when the active segment lies below the cap.  These stopped quantities therefore
stabilize pathwise at every fixed elapsed time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Raw reset occupation through elapsed time `t`, stopped before segment `N`.
The active partial segment is included only if its index is below `N`. -/
def davisStoppedElapsedResetOccupation (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  let k := ξ.activeSegmentIndex hne t ω
  davisFiniteResetOccupation S hflow g ξ initial (min N k) ω +
    if k < N then
      davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial k ω)
        (t - ξ.jumpTime k ω)
    else 0

/-- Realized completed resets centered by stopped elapsed reset occupation. -/
def davisStoppedElapsedOccupationCenteredResetSum (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisFiniteRealizedResetSum S hflow ξ initial g
      (min N (ξ.activeSegmentIndex hne t ω)) ω -
    davisStoppedElapsedResetOccupation
      S hflow ξ hne initial g N t ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Once the jump cap lies strictly above the active segment, the stopped raw
occupation is exactly the full elapsed occupation. -/
theorem davisStoppedElapsedResetOccupation_eq_elapsed_of_activeSegmentIndex_lt
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω)
    (hN : ξ.activeSegmentIndex hne t ω < N) :
    davisStoppedElapsedResetOccupation S hflow ξ hne initial g N t ω =
      davisElapsedResetOccupation S hflow ξ hne initial g t ω := by
  unfold davisStoppedElapsedResetOccupation davisElapsedResetOccupation
  simp only [min_eq_right_of_lt hN, hN, ↓reduceIte]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Under the same cap condition, the stopped occupation-centered sum is the
full elapsed occupation-centered sum. -/
theorem davisStoppedElapsedOccupationCenteredResetSum_eq_elapsed_of_activeSegmentIndex_lt
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω)
    (hN : ξ.activeSegmentIndex hne t ω < N) :
    davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω =
      davisElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g t ω := by
  unfold davisStoppedElapsedOccupationCenteredResetSum davisElapsedOccupationCenteredResetSum
  have hmin : min N (ξ.activeSegmentIndex hne t ω) = ξ.activeSegmentIndex hne t ω :=
    Nat.min_eq_right (le_of_lt hN)
  rw [hmin]
  congr 1
  exact davisStoppedElapsedResetOccupation_eq_elapsed_of_activeSegmentIndex_lt S hflow ξ hne initial g N t ω hN

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- At fixed elapsed time, deterministic jump-cap approximations converge by
eventual equality to the full elapsed occupation-centered sum. -/
theorem tendsto_davisStoppedElapsedOccupationCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    Filter.Tendsto (fun N =>
      davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω) Filter.atTop
      (nhds (davisElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g t ω)) := by
  have h := davisStoppedElapsedOccupationCenteredResetSum_eq_elapsed_of_activeSegmentIndex_lt
    S hflow ξ hne initial g (ξ.activeSegmentIndex hne t ω + 1) t ω
  have hcond : ξ.activeSegmentIndex hne t ω < ξ.activeSegmentIndex hne t ω + 1 := Nat.lt_add_one _
  have h' := h hcond
  exact Filter.Tendsto.congr' (Filter.eventually_atTop.mpr ⟨ξ.activeSegmentIndex hne t ω + 1,
    fun N hN => (davisStoppedElapsedOccupationCenteredResetSum_eq_elapsed_of_activeSegmentIndex_lt
      S hflow ξ hne initial g N t ω (Nat.lt_of_lt_of_le hcond hN)).symm⟩) tendsto_const_nhds

end SHS
