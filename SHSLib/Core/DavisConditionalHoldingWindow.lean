import SHSLib.Core.DavisConditionalHoldingWeighted

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The window law of the holding time

The weighted survivor identity evaluates the mean of a history-measurable
weight over the part of a history event on which the current segment survives
past a history-measurable threshold.  The conditional law of the *completed*
part of the one-segment contribution needs the analogous statement for a
*window*: the event that the holding time has already elapsed at the later
age `v` but had not yet elapsed at the earlier age `u`,

`A ∩ {u < h_k ≤ v}`.

Since the survival event at the later threshold is contained in the survival
event at the earlier one, the window event is the set difference of the two,
and its weighted mean is the difference of the two weighted survivor
identities:

`∫_{A ∩ {u < h_k ≤ v}} w = ∫_A w · (Sur_k(u) − Sur_k(v))`.

This module records that identity, the decomposition of the survival event it
rests on, and the unweighted special case.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The decomposition of a survival event -/

/-- The window between two thresholds is the difference of the two survival
events. -/
theorem davisHoldingWindow_eq_diff {Ω : Type*} (h : Ω → ℝ≥0) (u v : Ω → ℝ≥0) :
    {ω | u ω < h ω ∧ h ω ≤ v ω} = {ω | u ω < h ω} \ {ω | v ω < h ω} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]

/-- The survival event at the earlier threshold splits into the survival event
at the later threshold and the window between them. -/
theorem davisHoldingWindow_union {Ω : Type*} (h : Ω → ℝ≥0) (u v : Ω → ℝ≥0)
    (huv : ∀ ω, u ω ≤ v ω) :
    {ω | u ω < h ω} =
      {ω | v ω < h ω} ∪ {ω | u ω < h ω ∧ h ω ≤ v ω} := by
  ext ω
  constructor
  · intro hω
    by_cases hle : h ω ≤ v ω
    · exact Or.inr ⟨hω, hle⟩
    · exact Or.inl (not_le.1 hle)
  · rintro (hω | ⟨hω, -⟩)
    · exact lt_of_le_of_lt (huv ω) hω
    · exact hω

/-- The survival event at the later threshold and the window between the two
thresholds are disjoint. -/
theorem davisHoldingWindow_disjoint {Ω : Type*} (h : Ω → ℝ≥0) (u v : Ω → ℝ≥0) :
    Disjoint {ω | v ω < h ω} {ω | u ω < h ω ∧ h ω ≤ v ω} := by
  rw [Set.disjoint_left]
  rintro ω hω ⟨-, hle⟩
  exact absurd hle (not_le.2 hω)

/-! ## The weighted window identity -/

/-- **The weighted window identity.**  For two history-measurable thresholds
`u ≤ v` and a bounded history-measurable real weight, the mean of the weight
over the part of a history event on which the holding time of segment `k` lies
in the window `(u, v]` is the mean of the weight against the loss of the
survivor factor across the window. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_holdingTime_window_weighted
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (k : ℕ) (u v : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (hv : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] v)
    (huv : ∀ ω, u ω ≤ v ω)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (w : Ω → ℝ)
    (hw : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] w)
    (C : ℝ) (hwC : ∀ ω, |w ω| ≤ C) :
    ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧ ξ.holdingTime k ω ≤ v ω},
        w ω ∂P =
      ∫ ω in A, w ω *
        (((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
            (u ω)) -
          ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
            (v ω))) ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  have hm : (F k : MeasurableSpace Ω) ≤ mΩ := F.le k
  have hAm : MeasurableSet A := hm _ hA
  have hwm : Measurable w := hw.mono hm le_rfl
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right C 0
  have hwC' : ∀ ω, |w ω| ≤ C' := fun ω => le_trans (hwC ω) (le_max_left C 0)
  -- integrability of the weight
  have hwint : Integrable w P := by
    refine (integrable_const C').mono' hwm.aestronglyMeasurable ?_
    filter_upwards with ω
    simpa using hwC' ω
  -- integrability of the survivor-weighted weight
  have hprodint : ∀ r : Ω → ℝ≥0, Measurable[F k] r →
      Integrable (fun ω => w ω *
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
          (r ω))) P := by
    intro r hr'
    have hsm : Measurable fun ω =>
        (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
          (r ω) :=
      hsurv.comp (((DavisPreJumpHistory.measurable_currentState k).comp
        (hξ.preJumpHistory S hflow hf hr initial k)).prodMk
          (hr'.mono hm le_rfl))
    refine (integrable_const C').mono' (hwm.mul hsm).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 : |(davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
        (r ω)| ≤ 1 := by
      have h := DavisPreJumpHistory.nextSurvivor_mem_Ioc S hflow
        (davisPreJumpHistory S hflow ξ initial k ω) (r ω)
      rw [abs_of_pos h.1]
      exact h.2
    have : |w ω * (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor
        S hflow (r ω)| ≤ C' := by
      rw [abs_mul]
      calc |w ω| * |_| ≤ C' * 1 :=
            mul_le_mul (hwC' ω) h1 (abs_nonneg _) hC0
        _ = C' := mul_one C'
    simpa [Real.norm_eq_abs, abs_of_nonneg hC0] using this
  set Su : Set Ω := {ω | u ω < ξ.holdingTime k ω} with hSu
  set Sv : Set Ω := {ω | v ω < ξ.holdingTime k ω} with hSv
  set W : Set Ω := {ω | u ω < ξ.holdingTime k ω ∧ ξ.holdingTime k ω ≤ v ω}
    with hW
  have hSum : MeasurableSet Su :=
    measurableSet_lt (hu.mono hm le_rfl) (hξ.holdingTime k)
  have hSvm : MeasurableSet Sv :=
    measurableSet_lt (hv.mono hm le_rfl) (hξ.holdingTime k)
  have hWeq : W = Su \ Sv := davisHoldingWindow_eq_diff (ξ.holdingTime k) u v
  have hWm : MeasurableSet W := hWeq ▸ hSum.diff hSvm
  have hunion : A ∩ Su = (A ∩ Sv) ∪ (A ∩ W) := by
    rw [← Set.inter_union_distrib_left, ← davisHoldingWindow_union
      (ξ.holdingTime k) u v huv]
  have hdisj : Disjoint (A ∩ Sv) (A ∩ W) :=
    (davisHoldingWindow_disjoint (ξ.holdingTime k) u v).mono
      Set.inter_subset_right Set.inter_subset_right
  have hsplit : ∫ ω in A ∩ Su, w ω ∂P =
      ∫ ω in A ∩ Sv, w ω ∂P + ∫ ω in A ∩ W, w ω ∂P := by
    rw [hunion]
    exact setIntegral_union hdisj (hAm.inter hWm)
      hwint.integrableOn hwint.integrableOn
  have hIu := hlaw.setIntegral_lt_holdingTime_weighted hcont hsurv k u hu A hA
    w hw C hwC
  have hIv := hlaw.setIntegral_lt_holdingTime_weighted hcont hsurv k v hv A hA
    w hw C hwC
  have hsub : ∫ ω in A ∩ W, w ω ∂P =
      ∫ ω in A ∩ Su, w ω ∂P - ∫ ω in A ∩ Sv, w ω ∂P := by
    rw [hsplit]; ring
  rw [hsub, hIu, hIv, ← integral_sub ((hprodint u hu).integrableOn)
    ((hprodint v hv).integrableOn)]
  exact setIntegral_congr_fun hAm fun ω _ => by ring

/-- **The window identity.**  Unweighted special case: the probability of the
part of a history event on which the holding time of segment `k` falls in the
window `(u, v]` is the mean of the loss of the survivor factor across the
window. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_holdingTime_window
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (k : ℕ) (u v : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (hv : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] v)
    (huv : ∀ ω, u ω ≤ v ω)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    (P (A ∩ {ω | u ω < ξ.holdingTime k ω ∧ ξ.holdingTime k ω ≤ v ω})).toReal =
      ∫ ω in A,
        (((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
            (u ω)) -
          ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
            (v ω))) ∂P := by
  have h := hlaw.setIntegral_holdingTime_window_weighted hcont hsurv k u v hu hv
    huv A hA (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)
  simp only [one_mul] at h
  rw [← h, setIntegral_const, smul_eq_mul, mul_one]
  rfl

end SHS
