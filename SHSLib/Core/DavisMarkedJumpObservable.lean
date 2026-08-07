import SHSLib.Core.DavisSegmentProfileRegularity
import SHSLib.Core.DavisElapsedOccupationObservability

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Observability of the elapsed occupation for the marked jump filtration

The elapsed occupation theory asks for three quantities to be observable at
every time: the realized reset sum below a deterministic jump cap, the
completed reset occupation below the cap, and the partial occupation of the
segment that is active.  This module proves all three for the observation
filtration of the marked jump history, and packages them into the
`DavisElapsedOccupationObservable` interface.

The mechanism is the one already used for a single segment contribution: a
function that, on the event that segment `M` is active at time `t`, agrees with
a function of the pre-jump history at index `M` is observable at `t`.  That
step is isolated here as a reusable gluing lemma for an arbitrary target
measurable space; the three components then only require the history forms of
the finite realized sum, of the finite reset occupation, and of the partial
compensator of the active segment.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The gluing lemma -/

/-- **Gluing along the active events.**  A function that coincides, on the
event that segment `M` is active at `t`, with a function of the pre-jump
history at index `M`, is measurable for the observation filtration at `t`. -/
theorem DavisJumpNoise.measurable_markedJump_of_historyValues
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (t : ℝ≥0)
    {α : Type*} [MeasurableSpace α] {F : Ω → α} {Fhist : ℕ → Ω → α}
    (hFhist : ∀ M, Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ
      initial M] (Fhist M))
    (hagree : ∀ M ω, ω ∈ ξ.activeEvent M t → F ω = Fhist M ω) :
    Measurable[ξ.markedJumpSpace S hflow hf hr hξ initial t] F := by
  intro E hE M
  refine ⟨Fhist M ⁻¹' E ∩ {ω | ξ.jumpTime M ω ≤ t}, ((hFhist M) hE).inter
    (ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial M M
      le_rfl t), fun ω hω => hω.2, ?_⟩
  ext ω
  constructor
  · rintro ⟨hωE, hωact⟩
    refine ⟨⟨?_, hωact.1⟩, hωact⟩
    show Fhist M ω ∈ E
    rw [← hagree M ω hωact]
    exact hωE
  · rintro ⟨⟨hωE, -⟩, hωact⟩
    refine ⟨?_, hωact⟩
    show F ω ∈ E
    rw [hagree M ω hωact]
    exact hωE

/-! ## History measurability of the finite sums -/

/-- The finite realized reset sum before index `j` is observable in the
pre-jump history at any index at least `j`. -/
theorem DavisJumpNoise.measurable_finiteRealizedResetSum_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    {g : DavisState Q n → ℝ} (hg : Measurable g) (j k : ℕ) (hjk : j ≤ k) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (davisFiniteRealizedResetSum S hflow ξ initial g j) := by
  have hsum : davisFiniteRealizedResetSum S hflow ξ initial g j =
      fun ω => ∑ i ∈ Finset.range j,
        davisRealizedResetIncrement S hflow ξ initial g i ω := rfl
  rw [hsum]
  refine Finset.measurable_sum _ fun i hi => ?_
  have hik : i + 1 ≤ k :=
    le_trans (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) hjk
  exact (ξ.measurable_realizedResetIncrement_preJumpHistory S hflow hf hr hξ
    initial g hg i).mono
    ((ξ.preJumpHistoryFiltration S hflow hf hr hξ initial).mono hik) le_rfl

/-- The finite reset occupation before index `j` is observable in the pre-jump
history at any index at least `j`. -/
theorem DavisJumpNoise.measurable_finiteResetOccupation_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    {g : DavisState Q n → ℝ} (hreg : DavisResetOccupationRegular S hflow g)
    (j k : ℕ) (hjk : j ≤ k) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (davisFiniteResetOccupation S hflow g ξ initial j) := by
  have hsum : davisFiniteResetOccupation S hflow g ξ initial j =
      fun ω => ∑ i ∈ Finset.range j,
        davisSampledResetOccupationCompensator S hflow g ξ initial i ω := rfl
  rw [hsum]
  refine Finset.measurable_sum _ fun i hi => ?_
  have hik : i + 1 ≤ k :=
    le_trans (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) hjk
  exact (ξ.measurable_sampledCompensator_preJumpHistory S hflow hf hr hξ
    initial hreg i).mono
    ((ξ.preJumpHistoryFiltration S hflow hf hr hξ initial).mono hik) le_rfl

/-! ## The three components -/

/-- The realized reset contribution below a deterministic jump cap is
observable for the marked jump filtration. -/
theorem DavisJumpNoise.measurable_markedJump_stoppedElapsedRealizedResetContribution
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) {g : DavisState Q n → ℝ} (hg : Measurable g)
    (N : ℕ) (t : ℝ≥0) :
    Measurable[ξ.markedJumpSpace S hflow hf hr hξ initial t]
      (davisStoppedElapsedRealizedResetContribution
        S hflow ξ hne initial g N t) := by
  refine ξ.measurable_markedJump_of_historyValues S hflow hf hr hξ initial t
    (Fhist := fun M => davisFiniteRealizedResetSum S hflow ξ initial g
      (min N M)) (fun M => ?_) (fun M ω hω => ?_)
  · exact ξ.measurable_finiteRealizedResetSum_preJumpHistory S hflow hf hr hξ
      initial hg (min N M) M (min_le_right _ _)
  · have hM : ξ.activeSegmentIndex hne t ω = M :=
      (ξ.mem_activeEvent_iff_activeSegmentIndex hne M t ω).1 hω
    show davisFiniteRealizedResetSum S hflow ξ initial g
      (min N (ξ.activeSegmentIndex hne t ω)) ω = _
    rw [hM]

/-- The completed reset occupation below a deterministic jump cap is observable
for the marked jump filtration. -/
theorem DavisJumpNoise.measurable_markedJump_stoppedElapsedCompletedResetOccupation
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g) (N : ℕ) (t : ℝ≥0) :
    Measurable[ξ.markedJumpSpace S hflow hf hr hξ initial t]
      (davisStoppedElapsedCompletedResetOccupation
        S hflow ξ hne initial g N t) := by
  refine ξ.measurable_markedJump_of_historyValues S hflow hf hr hξ initial t
    (Fhist := fun M => davisFiniteResetOccupation S hflow g ξ initial
      (min N M)) (fun M => ?_) (fun M ω hω => ?_)
  · exact ξ.measurable_finiteResetOccupation_preJumpHistory S hflow hf hr hξ
      initial hreg (min N M) M (min_le_right _ _)
  · have hM : ξ.activeSegmentIndex hne t ω = M :=
      (ξ.mem_activeEvent_iff_activeSegmentIndex hne M t ω).1 hω
    show davisFiniteResetOccupation S hflow g ξ initial
      (min N (ξ.activeSegmentIndex hne t ω)) ω = _
    rw [hM]

/-- The partial occupation of the active segment, retained below the
deterministic jump cap, is observable for the marked jump filtration. -/
theorem DavisJumpNoise.measurable_markedJump_stoppedElapsedActiveResetOccupation
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g) (N : ℕ) (t : ℝ≥0) :
    Measurable[ξ.markedJumpSpace S hflow hf hr hξ initial t]
      (davisStoppedElapsedActiveResetOccupation
        S hflow ξ hne initial g N t) := by
  refine ξ.measurable_markedJump_of_historyValues S hflow hf hr hξ initial t
    (Fhist := fun M ω => if M < N then davisSegmentResetOccupationCompensator
      S hflow g (davisStateAfterJump S hflow ξ initial M ω)
      (t - ξ.jumpTime M ω) else 0) (fun M => ?_) (fun M ω hω => ?_)
  · by_cases hMN : M < N
    · simp only [if_pos hMN]
      exact hreg.stoppedCompensator_measurable.comp
        ((ξ.measurable_stateAfterJump_preJumpHistory S hflow hf hr hξ initial M
            M le_rfl).prodMk
          (measurable_const.sub (ξ.measurable_jumpTime_preJumpHistory S hflow
            hf hr hξ initial M)))
    · simp only [if_neg hMN]
      exact measurable_const
  · have hM : ξ.activeSegmentIndex hne t ω = M :=
      (ξ.mem_activeEvent_iff_activeSegmentIndex hne M t ω).1 hω
    show (if ξ.activeSegmentIndex hne t ω < N then
        davisSegmentResetOccupationCompensator S hflow g
          (davisStateAfterJump S hflow ξ initial
            (ξ.activeSegmentIndex hne t ω) ω)
          (t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω) else 0) = _
    rw [hM]

/-! ## The observability package -/

/-- **The elapsed occupation is observable for the marked jump filtration.**
All three components of the elapsed occupation-centered reset process are
measurable for the observation filtration of the marked jump history. -/
theorem davisElapsedOccupationObservable_markedJump
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) {g : DavisState Q n → ℝ} (hg : Measurable g)
    (hreg : DavisResetOccupationRegular S hflow g) :
    DavisElapsedOccupationObservable S hflow
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g where
  realized_measurable N t :=
    ξ.measurable_markedJump_stoppedElapsedRealizedResetContribution S hflow hf
      hr hξ hne initial hg N t
  completed_occupation_measurable N t :=
    ξ.measurable_markedJump_stoppedElapsedCompletedResetOccupation S hflow hf
      hr hξ hne initial hreg N t
  active_occupation_measurable N t :=
    ξ.measurable_markedJump_stoppedElapsedActiveResetOccupation S hflow hf hr
      hξ hne initial hreg N t

end SHS
