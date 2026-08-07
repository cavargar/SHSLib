import SHSLib.Core.DavisRefractoryHazard

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # A concrete Davis model: the constant-rate clock

Every conditional law used in this development has so far been an assumption on
the noise.  This module provides the *model* half of a genuine instance: a
concrete stochastic hybrid system whose data satisfy all the regularity
hypotheses used by the Davis construction, and whose accumulated hazard is
computed in closed form.

The model has two discrete modes (`Bool`), no continuous coordinate (`n = 0`),
one reset channel, a constant transition intensity `lam ≥ 0`, and the reset
that toggles the mode.  Its time-augmented flow only advances the clock, so the
total intensity along a trajectory is constantly `lam` and the hazard
accumulated over an elapsed duration `u` is `lam * u`; the survivor factor is
`exp (-(lam * u))`, i.e. the holding times must be exponential with rate `lam`.
The matching noise is built in `SHSLib.Core.DavisPoissonClockNoise`.
-/

namespace SHS

/-- **The constant-rate clock.**  Two modes, no continuous state, one reset
channel that toggles the mode, and a constant intensity `lam`. -/
def poissonClockSHS (lam : ℝ) (hlam : 0 ≤ lam) : SHS Bool 0 1 where
  f := fun _ _ _ => 0
  phi := fun _ q x _ => (!q, x)
  intensity := fun _ _ _ _ => lam
  intensity_nonneg := fun _ _ _ _ => hlam

/-- The trivial global flow of the constant-rate clock: with no continuous
state there is nothing to move. -/
def poissonClockFlow (lam : ℝ) (hlam : 0 ≤ lam) :
    (poissonClockSHS lam hlam).HasGlobalFlow where
  flow := fun _ _ x₀ _ => x₀
  flow_init := fun _ _ _ => rfl
  flow_ode := by intro t₀ q₀ x₀ t; simp [poissonClockSHS]

@[simp] theorem poissonClock_totalIntensity (lam : ℝ) (hlam : 0 ≤ lam)
    (z : DavisState Bool 0) :
    (poissonClockSHS lam hlam).totalIntensity z = lam := by
  simp [totalIntensity, poissonClockSHS]

/-- The time-augmented flow of the constant-rate clock advances the clock. -/
@[simp] theorem poissonClock_davisFlow (lam : ℝ) (hlam : 0 ≤ lam)
    (u : ℝ≥0) (z : DavisState Bool 0) :
    davisFlow (poissonClockSHS lam hlam) (poissonClockFlow lam hlam) u z
      = (z.1, z.2.1, z.2.2 + (u : ℝ)) := rfl

/-- The reset channel of the constant-rate clock toggles the mode. -/
@[simp] theorem poissonClock_resetDavisState (lam : ℝ) (hlam : 0 ≤ lam)
    (ℓ : Fin 1) (z : DavisState Bool 0) :
    (poissonClockSHS lam hlam).resetDavisState ℓ z = (!z.1, z.2.1, z.2.2) :=
  rfl

/-- The augmented flow of the constant-rate clock is regular. -/
theorem poissonClock_flowRegular (lam : ℝ) (hlam : 0 ≤ lam) :
    DavisFlowRegular (poissonClockSHS lam hlam) (poissonClockFlow lam hlam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    show Measurable fun z : DavisState Bool 0 => (z.1, z.2.1, z.2.2 + (u : ℝ))
    fun_prop
  · simp only [poissonClock_davisFlow]
    refine Measurable.prodMk measurable_snd.fst
      (Measurable.prodMk measurable_snd.snd.fst ?_)
    exact measurable_snd.snd.snd.add (by fun_prop)
  · intro s t z
    simp only [poissonClock_davisFlow]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    push_cast
    ring

/-- The reset channel of the constant-rate clock is regular: it is measurable
and, toggling the mode, it always changes the state. -/
theorem poissonClock_resetRegular (lam : ℝ) (hlam : 0 ≤ lam) :
    DavisResetRegular (poissonClockSHS lam hlam) := by
  refine ⟨?_, ?_⟩
  · intro ℓ
    show Measurable fun z : DavisState Bool 0 => ((!z.1), z.2.1, z.2.2)
    fun_prop
  · intro ℓ z _
    simp only [poissonClock_resetDavisState]
    intro h
    have : (!z.1) = z.1 := congrArg (fun y => y.1) h
    exact (Bool.not_ne_self z.1) this

/-- **The accumulated hazard of the constant-rate clock is linear.** -/
@[simp] theorem poissonClock_integratedHazard (lam : ℝ) (hlam : 0 ≤ lam)
    (z : DavisState Bool 0) (u : ℝ≥0) :
    davisIntegratedHazard (poissonClockSHS lam hlam) (poissonClockFlow lam hlam)
      z u = lam * (u : ℝ) := by
  rw [davisIntegratedHazard]
  simp only [poissonClock_totalIntensity]
  rw [setIntegral_const]
  simp [Real.volume_real_Icc, u.coe_nonneg, mul_comm]

/-- **The survivor factor of the constant-rate clock is exponential.** -/
@[simp] theorem poissonClock_segmentSurvivor (lam : ℝ) (hlam : 0 ≤ lam)
    (z : DavisState Bool 0) (u : ℝ≥0) :
    davisSegmentSurvivor (poissonClockSHS lam hlam) (poissonClockFlow lam hlam)
      z u = Real.exp (-(lam * (u : ℝ))) := by
  rw [davisSegmentSurvivor, poissonClock_integratedHazard]

end SHS
