import SHSLib.Core.DavisMarkedJumpGeneratorMartingale

open MeasureTheory MeasurableSpace Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! # A uniformly bounded accumulated hazard forces the zero measure

Several results in this development take as a hypothesis that the hazard
accumulated along the flow is bounded uniformly in the age,

`∀ z u, davisIntegratedHazard S hflow z u ≤ Hmax`,

which is what makes the centered reset profile bounded uniformly in the age.
This module records that the hypothesis is *incompatible* with the conditional
holding-time law of the noise, except for the zero measure.

The reason is simple.  The law says that a holding time survives past the age
`u` with the survivor factor `exp(−H)` of the accumulated hazard, so a uniform
bound `H ≤ Hmax` keeps the survival probability above `exp(−Hmax) > 0` at every
age.  Holding times take values in `ℝ≥0`, hence are finite, so the survival
events shrink to the empty set as the age grows and their measures tend to
zero.  Both together force the total mass to vanish.

The consequence is that any theorem carrying both hypotheses — for instance
the model-level conditional step law and the model-level Dynkin identity —
is only satisfiable for `P = 0`.  A hypothesis set that avoids this is a
*linear* growth bound on the profile: the following module establishes it, and
the ones after it thread the resulting age horizon through the conditional
laws.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The initial segment survives past every age with probability at least the
survivor factor at that age. -/
theorem measure_holdingTime_zero_gt_eq
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (u : ℝ≥0) :
    P {ω | u < ξ.holdingTime 0 ω} =
      ENNReal.ofReal (davisSegmentSurvivor S hflow initial u) * P Set.univ := by
  have h := hlaw.measure_holdingTime_gt 0 u
  have hconst : ∀ ω : Ω,
      (davisPreJumpHistory S hflow ξ initial 0 ω).nextSurvivor S hflow u =
        davisSegmentSurvivor S hflow initial u := by
    intro ω
    show davisSegmentSurvivor S hflow
      (davisPreJumpHistory S hflow ξ initial 0 ω).currentState u = _
    congr 1
  rw [h]
  simp only [hconst]
  rw [lintegral_const]

/-- **A uniformly bounded accumulated hazard forces the zero measure.**  Under
the conditional holding-time law, a uniform bound on the hazard accumulated
along the flow from the initial state leaves the initial segment alive at every
age with a probability bounded below, which a finite measure of finite holding
times cannot sustain. -/
theorem measure_univ_eq_zero_of_conditionalHoldingTimeLaw_of_boundedHazard
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (Hmax : ℝ)
    (hHmax : ∀ u : ℝ≥0, davisIntegratedHazard S hflow initial u ≤ Hmax) :
    P Set.univ = 0 := by
  classical
  set c : ℝ := Real.exp (-Hmax) with hc
  have hcpos : 0 < c := Real.exp_pos _
  -- the survival events at integer ages
  set A : ℕ → Set Ω := fun k => {ω | ((k : ℝ≥0)) < ξ.holdingTime 0 ω} with hA
  have hAmeas : ∀ k, MeasurableSet (A k) := fun k =>
    measurableSet_lt measurable_const (hξ.holdingTime 0)
  have hAanti : Antitone A := by
    intro i j hij ω hω
    have hcast : ((i : ℕ) : ℝ≥0) ≤ ((j : ℕ) : ℝ≥0) := by exact_mod_cast hij
    exact lt_of_le_of_lt hcast hω
  have hAempty : (⋂ k, A k) = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := exists_nat_gt ((ξ.holdingTime 0 ω : ℝ≥0) : ℝ)
    refine ⟨k, ?_⟩
    simp only [hA, Set.mem_setOf_eq, not_lt]
    exact_mod_cast le_of_lt hk
  -- their measures tend to zero
  have htend : Tendsto (fun k => P (A k)) atTop (𝓝 (P (⋂ k, A k))) :=
    tendsto_measure_iInter_atTop (fun k => (hAmeas k).nullMeasurableSet) hAanti
      ⟨0, measure_ne_top P _⟩
  rw [hAempty, measure_empty] at htend
  -- but they are bounded below by a positive multiple of the total mass
  have hlower : ∀ k, ENNReal.ofReal c * P Set.univ ≤ P (A k) := by
    intro k
    rw [measure_holdingTime_zero_gt_eq hlaw (k : ℝ≥0)]
    have hsurv : c ≤ davisSegmentSurvivor S hflow initial (k : ℝ≥0) :=
      Real.exp_le_exp.2 (by linarith [hHmax ((k : ℝ≥0))])
    gcongr
  have hle : ENNReal.ofReal c * P Set.univ ≤ 0 := ge_of_tendsto' htend hlower
  have hzero : ENNReal.ofReal c * P Set.univ = 0 := le_antisymm hle (zero_le _)
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (ENNReal.ofReal_pos.mpr hcpos).ne'
  · exact h

/-- The zero-measure conclusion in the form used by the model-level theorems:
under the conditional holding-time law, a uniformly bounded accumulated hazard
makes the measure itself vanish. -/
theorem measure_eq_zero_of_conditionalHoldingTimeLaw_of_boundedHazard
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (Hmax : ℝ)
    (hHmax : ∀ (z : DavisState Q n) (u : ℝ≥0),
      davisIntegratedHazard S hflow z u ≤ Hmax) :
    P = 0 :=
  Measure.measure_univ_eq_zero.mp
    (measure_univ_eq_zero_of_conditionalHoldingTimeLaw_of_boundedHazard hlaw
      Hmax fun u => hHmax initial u)

end SHS
