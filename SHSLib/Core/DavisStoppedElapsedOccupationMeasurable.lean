import SHSLib.Core.DavisStoppedElapsedOccupation
import SHSLib.Core.DavisResetOccupationRegular

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Measurability of jump-capped elapsed reset occupation

Fixed finite occupation prefixes and the active partial-segment contribution
are measurable under the existing jump-noise and reset-occupation regularity
interfaces.  A measurable branch selection by the active segment index then
gives measurability of the stopped elapsed quantities.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A deterministic finite prefix of full sampled reset occupations is
measurable. -/
theorem DavisResetOccupationRegular.measurable_finiteResetOccupation
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (N : ℕ) :
    Measurable (davisFiniteResetOccupation S hflow g ξ initial N) := by
  unfold davisFiniteResetOccupation
  apply Finset.measurable_sum
  intro k _
  exact @hreg.measurable_sampled_stoppedCompensator Q _ _ n m S hflow hf hr g Ω _ ξ hξ initial k

/-- A deterministic finite prefix of realized reset increments is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.measurable_finiteRealizedResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hg : Measurable g) (N : ℕ) :
    Measurable (davisFiniteRealizedResetSum S hflow ξ initial g N) := by
  unfold davisFiniteRealizedResetSum
  apply Finset.measurable_sum
  intro k _
  exact hξ.realizedResetIncrement S hflow hf hr initial g hg k

/-- At fixed elapsed time and jump cap, stopped reset occupation is an ambient
measurable random variable. -/
theorem DavisResetOccupationRegular.measurable_stoppedElapsedResetOccupation
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (N : ℕ) (t : ℝ≥0) :
    Measurable (davisStoppedElapsedResetOccupation
      S hflow ξ hne initial g N t) := by
  unfold davisStoppedElapsedResetOccupation
  let k : Ω → ℕ := fun ω => ξ.activeSegmentIndex hne t ω
  have hk : Measurable k := hξ.activeSegmentIndex hne t
  have hmin : Measurable (fun ω => min N (k ω)) := (measurable_const).min hk
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
  -- Rewrite the goal using key
  have goal_eq : (fun ω =>
      let k := ξ.activeSegmentIndex hne t ω
      S.davisFiniteResetOccupation hflow g ξ initial (min N k) ω +
        if k < N then S.davisSegmentResetOccupationCompensator hflow g
          (S.davisStateAfterJump hflow ξ initial k ω) (t - ξ.jumpTime k ω) else 0) =
      (fun ω =>
        (∑ j ∈ Finset.range N, if j < k ω then
          S.davisSegmentResetOccupationCompensator hflow g
            (S.davisPreJumpHistory hflow ξ initial j ω).currentState
            (ξ.holdingTime j ω) else 0) +
        if k ω < N then S.davisSegmentResetOccupationCompensator hflow g
          (S.davisStateAfterJump hflow ξ initial (k ω) ω) (t - ξ.jumpTime (k ω) ω) else 0) := by
    ext ω
    simp only [k]
    rw [key ω]
  rw [goal_eq]
  -- Combine into a single sum over Finset.range N
  have goal_eq2 : (fun ω =>
        (∑ j ∈ Finset.range N, if j < k ω then
          S.davisSegmentResetOccupationCompensator hflow g
            (S.davisPreJumpHistory hflow ξ initial j ω).currentState
            (ξ.holdingTime j ω) else 0) +
        if k ω < N then S.davisSegmentResetOccupationCompensator hflow g
          (S.davisStateAfterJump hflow ξ initial (k ω) ω) (t - ξ.jumpTime (k ω) ω) else 0) =
      (fun ω => ∑ j ∈ Finset.range N,
        ((if j < k ω then S.davisSegmentResetOccupationCompensator hflow g
          (S.davisPreJumpHistory hflow ξ initial j ω).currentState
          (ξ.holdingTime j ω) else 0) +
        (if j = k ω then S.davisSegmentResetOccupationCompensator hflow g
          (S.davisStateAfterJump hflow ξ initial j ω) (t - ξ.jumpTime j ω) else 0))) := by
    ext ω
    by_cases h : k ω < N
    · -- Case k ω < N
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite_eq']
      simp [h]
    · -- Case k ω ≥ N
      simp [h]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range] at hj ⊢
      simp [show j ≠ k ω from fun hji => by omega]
  rw [goal_eq2]
  -- Each term in the sum is measurable for fixed j
  apply Finset.measurable_sum
  intro j _
  -- Measurability of: (if j < k ω then ... else 0) + (if j = k ω then ... else 0)
  apply Measurable.add
  · -- First term: if j < k ω then ... else 0
    apply Measurable.ite
    · exact measurableSet_lt measurable_const hk
    · exact @measurable_sampled_stoppedCompensator Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ initial j
    · exact measurable_const
  · -- Second term: if j = k ω then ... else 0
    apply Measurable.ite
    · exact measurableSet_eq_fun measurable_const hk
    · exact hreg.stoppedCompensator_measurable.comp
        ((hξ.stateAfterJump S hflow hf hr initial j).prodMk
          (measurable_const.sub (hξ.jumpTime j)))
    · exact measurable_const

/-- The stopped elapsed occupation-centered reset sum is measurable. -/
theorem DavisResetOccupationRegular.measurable_stoppedElapsedOccupationCenteredResetSum
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g)
    (N : ℕ) (t : ℝ≥0) :
    Measurable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t) := by
  unfold davisStoppedElapsedOccupationCenteredResetSum
  apply Measurable.sub
  · -- Goal: Measurable (fun ω => davisFiniteRealizedResetSum ... (min N k) ω)
    have heq : ∀ ω, davisFiniteRealizedResetSum S hflow ξ initial g
        (min N (ξ.activeSegmentIndex hne t ω)) ω =
      ∑ i ∈ Finset.range N, (if i < ξ.activeSegmentIndex hne t ω
        then davisRealizedResetIncrement S hflow ξ initial g i ω else 0) := by
      intro ω
      unfold davisFiniteRealizedResetSum
      let k := ξ.activeSegmentIndex hne t ω
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp [Finset.mem_filter, Finset.mem_range]
    rw [show (fun ω => davisFiniteRealizedResetSum S hflow ξ initial g
        (min N (ξ.activeSegmentIndex hne t ω)) ω) =
      (fun ω => ∑ i ∈ Finset.range N, (if i < ξ.activeSegmentIndex hne t ω
        then davisRealizedResetIncrement S hflow ξ initial g i ω else 0)) by
      funext ω; exact heq ω]
    apply Finset.measurable_sum
    intro i _
    apply Measurable.ite
    · exact measurableSet_lt measurable_const (hξ.activeSegmentIndex hne t)
    · exact hξ.realizedResetIncrement S hflow hf hr initial g hg i
    · exact measurable_const
  · have : Measurable (davisStoppedElapsedResetOccupation
        S hflow ξ hne initial g N t) := by
      unfold davisStoppedElapsedResetOccupation
      apply Measurable.add
      · -- davisFiniteResetOccupation S hflow g ξ initial (min N k)
        have heq : ∀ ω, davisFiniteResetOccupation S hflow g ξ initial
            (min N (ξ.activeSegmentIndex hne t ω)) ω =
          ∑ i ∈ Finset.range N, (if i < ξ.activeSegmentIndex hne t ω
            then davisSegmentResetOccupationCompensator S hflow g
              (davisPreJumpHistory S hflow ξ initial i ω).currentState
              (ξ.holdingTime i ω) else 0) := by
          intro ω
          unfold davisFiniteResetOccupation
          let k := ξ.activeSegmentIndex hne t ω
          rw [← Finset.sum_filter]
          congr 1
          ext i
          simp [Finset.mem_filter, Finset.mem_range]
        rw [show (fun ω => davisFiniteResetOccupation S hflow g ξ initial
            (min N (ξ.activeSegmentIndex hne t ω)) ω) =
          (fun ω => ∑ i ∈ Finset.range N, (if i < ξ.activeSegmentIndex hne t ω
            then davisSegmentResetOccupationCompensator S hflow g
              (davisPreJumpHistory S hflow ξ initial i ω).currentState
              (ξ.holdingTime i ω) else 0)) by
          funext ω; exact heq ω]
        apply Finset.measurable_sum
        intro i _
        apply Measurable.ite
        · exact measurableSet_lt measurable_const (hξ.activeSegmentIndex hne t)
        · exact @hreg.measurable_sampled_stoppedCompensator Q _ _ n m S hflow hf hr g Ω _ ξ hξ initial i
        · exact measurable_const
      · -- conditional compensator
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
        · exact measurableSet_eq_fun (measurable_const) (hξ.activeSegmentIndex hne t)
        · have hstate : Measurable (davisStateAfterJump S hflow ξ initial i) :=
            hξ.stateAfterJump S hflow hf hr initial i
          have hjump : Measurable (ξ.jumpTime i) := hξ.jumpTime i
          have hcomp : (fun x => davisSegmentResetOccupationCompensator S hflow g
              (davisStateAfterJump S hflow ξ initial i x) (t - ξ.jumpTime i x)) =
            (fun p : DavisState Q n × ℝ≥0 => davisSegmentResetOccupationCompensator S hflow g p.1 p.2) ∘
            (fun x => (davisStateAfterJump S hflow ξ initial i x, t - ξ.jumpTime i x)) := rfl
          rw [hcomp]
          apply Measurable.comp (hreg.stoppedCompensator_measurable)
          exact Measurable.prodMk hstate (Measurable.sub measurable_const hjump)
        · exact measurable_const
    exact this

end SHS
