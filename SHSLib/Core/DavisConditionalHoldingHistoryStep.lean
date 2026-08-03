import SHSLib.Core.DavisResetOccupationConditional

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Holding-time threshold steps with finite-history events

The earlier threshold-step interface has deterministic coefficients.  Reset
occupation, however, also depends on the state encoded by the pre-jump history.
This module adds the missing elementary layer: coefficients may be localized to
pre-jump-history events.  The conditional survivor law then applies after
intersecting the testing event with each such history event.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A finite nonnegative holding-time threshold step localized by events from
pre-jump history. -/
def davisHoldingHistoryThresholdStep
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (k : ℕ) {ι : Type*}
    (s : Finset ι) (event : ι → Set Ω) (u : ι → ℝ≥0)
    (w : ι → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∑ i ∈ s, w i *
    ((event i ∩ {ω' | u i < ξ.holdingTime k ω'}).indicator
      (fun _ => (1 : ℝ≥0∞))) ω

/-- The survivor-side transform of a history-localized threshold step. -/
def davisHoldingHistoryThresholdSurvivorStep
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) {ι : Type*} (s : Finset ι) (event : ι → Set Ω)
    (u : ι → ℝ≥0) (w : ι → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∑ i ∈ s, w i * (event i).indicator (fun ω' => ENNReal.ofReal
    ((davisPreJumpHistory S hflow ξ initial k ω').nextSurvivor S hflow (u i))) ω

/-- Conditional holding-time integration for finite threshold steps whose
terms are localized by pre-jump-history events. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_historyThresholdStep
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) {ι : Type*} (s : Finset ι) (event : ι → Set Ω)
    (u : ι → ℝ≥0) (w : ι → ℝ≥0∞) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hevent : ∀ i ∈ s,
      MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] (event i))
    (hsurvivor : ∀ i ∈ s, Measurable (fun ω => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u i)))) :
    ∫⁻ ω in A, davisHoldingHistoryThresholdStep ξ k s event u w ω ∂P =
      ∫⁻ ω in A, davisHoldingHistoryThresholdSurvivorStep
        S hflow ξ initial k s event u w ω ∂P := by
  unfold davisHoldingHistoryThresholdStep davisHoldingHistoryThresholdSurvivorStep
  have hRHS_meas : ∀ b ∈ s, Measurable (fun ω => w b * (event b).indicator (fun ω' => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω').nextSurvivor S hflow (u b))) ω) := by
    intro b hb
    obtain ⟨s', hs', heq⟩ := hevent b hb
    have hevent' : MeasurableSet (event b) := by rw [← heq]; exact hs'.preimage (hξ.preJumpHistory S hflow hf hr initial k)
    exact (hsurvivor b hb).indicator hevent' |>.const_mul (w b)
  rw [MeasureTheory.lintegral_finset_sum _ hRHS_meas]
  have hLHS_meas : ∀ i ∈ s, Measurable (fun ω => w i * (event i ∩ {ω' | u i < ξ.holdingTime k ω'}).indicator
      (fun _ => (1 : ℝ≥0∞)) ω) := by
    intro i hi
    obtain ⟨s', hs', heq⟩ := hevent i hi
    have hevent' : MeasurableSet (event i) := by rw [← heq]; exact hs'.preimage (hξ.preJumpHistory S hflow hf hr initial k)
    exact (measurable_const.indicator (hevent'.inter ((hξ.holdingTime k) measurableSet_Ioi)) |>.const_mul (w i))
  rw [MeasureTheory.lintegral_finset_sum _ hLHS_meas]
  apply Finset.sum_congr rfl
  intro i hi
  have hA' : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] (A ∩ event i) :=
    hA.inter (hevent i hi)
  have hset : MeasurableSet {ω | u i < ξ.holdingTime k ω} :=
    (hξ.holdingTime k) measurableSet_Ioi
  obtain ⟨s', hs', heq⟩ := hevent i hi
  have hevent' : MeasurableSet (event i) := by rw [← heq]; exact hs'.preimage (hξ.preJumpHistory S hflow hf hr initial k)
  have hmeas : Measurable ((event i ∩ {ω' | u i < ξ.holdingTime k ω'}).indicator
      (fun _ => (1 : ℝ≥0∞))) := by
    apply Measurable.indicator measurable_const
    exact hevent'.inter hset
  have hms2 : Measurable ((event i).indicator (fun ω' => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω').nextSurvivor S hflow (u i)))) :=
    ((hsurvivor i hi).indicator hevent')
  have hkey : ∫⁻ ω in A, (event i ∩ {ω' | u i < ξ.holdingTime k ω'}).indicator
      (fun _ => (1 : ℝ≥0∞)) ω ∂P =
    ∫⁻ ω in A, (event i).indicator (fun ω' => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω').nextSurvivor S hflow (u i))) ω ∂P := by
    have := hlaw.lintegral_weighted_survival_indicator k (u i) 1 (A ∩ event i) hA'
    simp at this
    rw [MeasureTheory.lintegral_indicator (hevent'.inter hset)]
    simp_all [Set.inter_comm, Set.inter_assoc]
  rw [MeasureTheory.lintegral_const_mul (w i) hmeas, MeasureTheory.lintegral_const_mul (w i) hms2]
  simp_all

end SHS
