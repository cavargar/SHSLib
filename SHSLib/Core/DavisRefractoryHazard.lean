import SHSLib.Core.DavisBoundedHazardVacuity

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # What a lower bound on the holding times costs

The model-level statements for the observation filtration keep one hypothesis
on the noise besides the two conditional laws: the holding times are bounded
below by a strictly positive `d`.  The vacuity module showed that a *uniform
bound on the accumulated hazard* is incompatible with the conditional
holding-time law; it is natural to ask what the lower bound on the holding
times costs in the same sense.

The answer is that it is a condition on the model rather than a contradiction:
it forces the hazard accumulated along the flow to vanish below the age `d`,
starting from a.e. visited state — a *refractory window* at the beginning of
each segment, during which no jump can occur.  Conversely nothing in the
conditional holding-time law forbids an intensity that vanishes on an initial
age window, so the hypothesis is restrictive but, unlike the bounded
accumulated hazard, not vacuous.

The proof is the equality case of an inequality.  The law says that the
survival event `{u < h_k}` has measure `∫ Sur(u)`, and `Sur(u) ≤ 1`; if the
holding times are at least `d` and `u < d`, the survival event is everything,
so the integral of `Sur(u)` equals the total mass, which forces `Sur(u) = 1`
almost everywhere, i.e. a vanishing accumulated hazard.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- **A refractory window.**  If the holding times are bounded below by `d`,
then below the age `d` the hazard accumulated along the flow from the state
reached after the `k`-th jump vanishes almost surely. -/
theorem davisIntegratedHazard_currentState_eq_zero_of_holdingTime_ge
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (d : ℝ≥0) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (k : ℕ) (u : ℝ≥0) (hu : u < d) :
    ∀ᵐ ω ∂P, davisIntegratedHazard S hflow
      (davisPreJumpHistory S hflow ξ initial k ω).currentState u = 0 := by
  classical
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u)
  -- the survival event is everything
  have hall : {ω | u < ξ.holdingTime k ω} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact lt_of_lt_of_le hu (hd k ω)
  have hmass : P Set.univ = ∫⁻ ω, f ω ∂P := by
    have h := hlaw.measure_holdingTime_gt k u
    rw [hall] at h
    exact h
  -- the survivor factor is at most one
  have hle : f ≤ᵐ[P] fun _ => (1 : ℝ≥0∞) := by
    filter_upwards with ω
    have h1 : (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u
        ≤ 1 := ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor_mem_Ioc
          S hflow u).2
    calc f ω ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h1
      _ = 1 := ENNReal.ofReal_one
  have hone : ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P = P Set.univ := by simp
  have hfin : ∫⁻ ω, f ω ∂P ≠ ⊤ := by
    rw [← hmass]
    exact measure_ne_top P Set.univ
  have hge : ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P ≤ ∫⁻ ω, f ω ∂P := by
    rw [hone, hmass]
  have haeq : f =ᵐ[P] fun _ => (1 : ℝ≥0∞) :=
    MeasureTheory.ae_eq_of_ae_le_of_lintegral_le hle hfin aemeasurable_const hge
  filter_upwards [haeq] with ω hω
  have hsur : (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor
      S hflow u = 1 :=
    ENNReal.ofReal_eq_one.1 hω
  have hexp : Real.exp (-davisIntegratedHazard S hflow
      (davisPreJumpHistory S hflow ξ initial k ω).currentState u) = 1 := hsur
  have hzero : -davisIntegratedHazard S hflow
      (davisPreJumpHistory S hflow ξ initial k ω).currentState u = 0 :=
    (Real.exp_eq_one_iff _).1 hexp
  linarith [hzero]

/-- The refractory window at the initial state: if the holding times are
bounded below by `d` and the measure does not vanish, the hazard accumulated
along the flow from the initial state vanishes below the age `d`. -/
theorem davisIntegratedHazard_initial_eq_zero_of_holdingTime_ge
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hP : P ≠ 0) (d : ℝ≥0) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (u : ℝ≥0) (hu : u < d) :
    davisIntegratedHazard S hflow initial u = 0 := by
  have h := davisIntegratedHazard_currentState_eq_zero_of_holdingTime_ge hlaw d
    hd 0 u hu
  have hconst : ∀ ω : Ω,
      (davisPreJumpHistory S hflow ξ initial 0 ω).currentState = initial :=
    fun _ => rfl
  simp only [hconst] at h
  have : (MeasureTheory.ae P).NeBot := MeasureTheory.ae_neBot.2 hP
  obtain ⟨_, h0⟩ := h.exists
  exact h0

/-! ## The converse: a refractory model has holding times bounded below -/

/-- If the hazard accumulated along the flow from the state reached after the
`k`-th jump vanishes at the age `u`, the `k`-th holding time exceeds `u`
almost surely. -/
theorem measure_holdingTime_le_eq_zero_of_integratedHazard_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (u : ℝ≥0)
    (href : ∀ ω, davisIntegratedHazard S hflow
      (davisPreJumpHistory S hflow ξ initial k ω).currentState u = 0) :
    P {ω | ξ.holdingTime k ω ≤ u} = 0 := by
  have hsurv : ∀ ω : Ω, ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u)
        = 1 := by
    intro ω
    have : (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u
        = Real.exp (-davisIntegratedHazard S hflow
          (davisPreJumpHistory S hflow ξ initial k ω).currentState u) := rfl
    rw [this, href ω]
    simp
  have hgt : P {ω | u < ξ.holdingTime k ω} = P Set.univ := by
    rw [hlaw.measure_holdingTime_gt k u]
    simp only [hsurv]
    simp
  have hmeas : MeasurableSet {ω | u < ξ.holdingTime k ω} :=
    measurableSet_lt measurable_const (hξ.holdingTime k)
  have hcompl : {ω | u < ξ.holdingTime k ω}ᶜ = {ω | ξ.holdingTime k ω ≤ u} := by
    ext ω
    simp [not_lt]
  have hsum := measure_add_measure_compl (μ := P) hmeas
  rw [hgt, hcompl] at hsum
  have hfin : P Set.univ ≠ ⊤ := measure_ne_top P Set.univ
  have := ENNReal.add_right_inj hfin (b := P {ω | ξ.holdingTime k ω ≤ u})
    (c := 0)
  simpa using this.1 (by simpa using hsum)

/-- **A refractory model has holding times bounded below.**  If the hazard
accumulated along the flow vanishes below the age `d` from every state, then
almost surely every holding time is at least `d`.  Together with
`SHS.davisIntegratedHazard_currentState_eq_zero_of_holdingTime_ge` this
identifies the lower bound on the holding times with a refractory window of the
model. -/
theorem ae_le_holdingTime_of_refractory
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (d : ℝ≥0) (hd0 : 0 < d)
    (href : ∀ (z : DavisState Q n) (u : ℝ≥0), u < d →
      davisIntegratedHazard S hflow z u = 0)
    (k : ℕ) :
    ∀ᵐ ω ∂P, d ≤ ξ.holdingTime k ω := by
  have hsub : {ω | ξ.holdingTime k ω < d} ⊆
      ⋃ j : ℕ, {ω | ξ.holdingTime k ω ≤ d - 1 / (j + 1 : ℝ≥0)} := by
    intro ω hω
    have hpos : 0 < d - ξ.holdingTime k ω := tsub_pos_of_lt hω
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    have hle : ξ.holdingTime k ω + 1 / (j + 1 : ℝ≥0) ≤ d := by
      have : ξ.holdingTime k ω + (d - ξ.holdingTime k ω) = d :=
        add_tsub_cancel_of_le (le_of_lt hω)
      calc ξ.holdingTime k ω + 1 / (j + 1 : ℝ≥0)
          ≤ ξ.holdingTime k ω + (d - ξ.holdingTime k ω) := by
            gcongr
        _ = d := this
    exact le_tsub_of_add_le_right hle
  have hzero : ∀ j : ℕ,
      P {ω | ξ.holdingTime k ω ≤ d - 1 / (j + 1 : ℝ≥0)} = 0 := by
    intro j
    refine measure_holdingTime_le_eq_zero_of_integratedHazard_eq_zero hlaw k _
      (fun ω => href _ _ ?_)
    exact tsub_lt_self hd0 (by positivity)
  have hunion : P (⋃ j : ℕ, {ω | ξ.holdingTime k ω ≤ d - 1 / (j + 1 : ℝ≥0)})
      = 0 := measure_iUnion_null hzero
  have : P {ω | ξ.holdingTime k ω < d} = 0 :=
    measure_mono_null hsub hunion
  rw [ae_iff]
  simpa only [not_le] using this

end SHS
