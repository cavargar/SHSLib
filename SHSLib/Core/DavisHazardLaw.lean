import SHSLib.Core.DavisPreJumpHistory

open MeasureTheory MeasurableSpace
open scoped NNReal

noncomputable section

/-! # Integrated hazards and conditional holding-time laws

This module packages the deterministic hazard accumulated along the next flow
segment from a finite pre-jump history.  It also gives an event-integral
interface for saying that the next holding time has the corresponding
conditional survivor law.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The state from which the next deterministic segment starts. -/
def DavisPreJumpHistory.currentState {k : ℕ}
    (H : DavisPreJumpHistory Q n m k) : DavisState Q n :=
  H.stateAfterJump (Fin.last k)

/-- Total hazard accumulated for elapsed duration `u` along the deterministic
flow starting from `z`. -/
def davisIntegratedHazard (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (z : DavisState Q n) (u : ℝ≥0) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
    S.totalIntensity (davisFlow S hflow s.toNNReal z)

/-- Survivor factor associated with the integrated total hazard. -/
def davisSegmentSurvivor (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (z : DavisState Q n) (u : ℝ≥0) : ℝ :=
  Real.exp (-davisIntegratedHazard S hflow z u)

/-- Integrated hazard for the next segment selected by a finite history. -/
def DavisPreJumpHistory.integratedHazard (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {k : ℕ} (H : DavisPreJumpHistory Q n m k)
    (u : ℝ≥0) : ℝ :=
  davisIntegratedHazard S hflow H.currentState u

/-- Survivor factor for the next holding time selected by a finite history. -/
def DavisPreJumpHistory.nextSurvivor (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {k : ℕ} (H : DavisPreJumpHistory Q n m k)
    (u : ℝ≥0) : ℝ :=
  davisSegmentSurvivor S hflow H.currentState u

@[simp] theorem davisIntegratedHazard_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (z : DavisState Q n) :
    davisIntegratedHazard S hflow z 0 = 0 := by
  simp [davisIntegratedHazard]

@[simp] theorem davisSegmentSurvivor_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (z : DavisState Q n) :
    davisSegmentSurvivor S hflow z 0 = 1 := by
  simp [davisSegmentSurvivor, davisIntegratedHazard_zero]

/-- Accumulated total hazard is nonnegative. -/
theorem davisIntegratedHazard_nonneg
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (z : DavisState Q n)
    (u : ℝ≥0) :
    0 ≤ davisIntegratedHazard S hflow z u := by
  unfold davisIntegratedHazard
  apply MeasureTheory.integral_nonneg
  intro s
  apply totalIntensity_nonneg

/-- A segment survivor factor is strictly positive. -/
theorem davisSegmentSurvivor_pos
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (z : DavisState Q n)
    (u : ℝ≥0) :
    0 < davisSegmentSurvivor S hflow z u := by
  exact Real.exp_pos _

/-- A segment survivor factor is at most one. -/
theorem davisSegmentSurvivor_le_one
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (z : DavisState Q n)
    (u : ℝ≥0) :
    davisSegmentSurvivor S hflow z u ≤ 1 := by
  unfold davisSegmentSurvivor
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  linarith [davisIntegratedHazard_nonneg S hflow z u]

/-- The history-level survivor factor is always a probability value. -/
theorem DavisPreJumpHistory.nextSurvivor_mem_Ioc
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {k : ℕ}
    (H : DavisPreJumpHistory Q n m k) (u : ℝ≥0) :
    H.nextSurvivor S hflow u ∈ Set.Ioc (0 : ℝ) 1 := by
  exact ⟨davisSegmentSurvivor_pos S hflow H.currentState u,
    davisSegmentSurvivor_le_one S hflow H.currentState u⟩

/-- Event-integral formulation of the conditional survivor law for successive
holding times.  For every event determined by the first `k` jumps, intersecting
with survival of the next holding time multiplies its probability by the
history-dependent survivor factor under integration. -/
structure DavisJumpNoise.ConditionalHoldingTimeLaw
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) : Prop where
  survivor_identity : ∀ (k : ℕ) (u : ℝ≥0) (A : Set Ω),
    MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A →
      P (A ∩ {ω | u < ξ.holdingTime k ω}) =
        ∫⁻ ω in A,
          ENNReal.ofReal
            ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u) ∂P

/-- The conditional holding-time law specializes to the unconditional survivor
probability by taking the history event to be the whole sample space. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.measure_holdingTime_gt
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (u : ℝ≥0) :
    P {ω | u < ξ.holdingTime k ω} =
      ∫⁻ ω,
        ENNReal.ofReal
          ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u) ∂P := by
  have h := hlaw.survivor_identity k u Set.univ (by measurability)
  simpa using h

end SHS
