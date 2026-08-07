import SHSLib.Core.DavisRefractoryHazard

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # A concrete refractory Davis model

Batch 125 identified the lower bound on the holding times, carried by the
model-level martingale and Dynkin statements, with a *refractory window*: the
hazard accumulated along the flow has to vanish below the age `d`.  This module
builds a model with exactly such a window.

The state carries the age since the last jump as its single continuous
coordinate: the drift is constant equal to one, the reset sets the age back to
zero (and toggles a Boolean mode, so that the reset genuinely moves the state),
and the intensity vanishes while the age is below `d` and equals `lam` above
it.  The hazard accumulated from an age-zero state over an elapsed duration `u`
is then `lam * max (u - d) 0`, so the survivor factor is
`exp (-(lam * max (u - d) 0))`: the holding times must be `d` plus an
exponential variable of rate `lam`, and in particular they are at least `d`.
-/

namespace SHS

/-- The unit drift of the age coordinate. -/
def ageDrift : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

@[simp] theorem ageDrift_apply : ageDrift (0 : Fin 1) = 1 := by
  simp [ageDrift]

/-- **The refractory clock.**  Two modes, the age since the last jump as the
continuous coordinate, one reset channel that toggles the mode and resets the
age, and an intensity that vanishes below the age `d`. -/
def refractoryClockSHS (lam d : ℝ) (hlam : 0 ≤ lam) : SHS Bool 1 1 where
  f := fun _ _ _ => ageDrift
  phi := fun _ q _ _ => (!q, 0)
  intensity := fun _ _ x _ => if d ≤ x 0 then lam else 0
  intensity_nonneg := by
    intro _ _ x _
    split <;> simp [hlam]

/-- The flow of the refractory clock: the age grows at unit speed. -/
def refractoryClockFlow (lam d : ℝ) (hlam : 0 ≤ lam) :
    (refractoryClockSHS lam d hlam).HasGlobalFlow where
  flow := fun t₀ _ x₀ t => x₀ + (max (t - t₀) 0) • ageDrift
  flow_init := by intro t₀ q₀ x₀; simp
  flow_ode := by
    intro t₀ q₀ x₀ t
    have : ∫ _s in Set.Icc t₀ t, (refractoryClockSHS lam d hlam).f q₀
        (x₀ + (max (_s - t₀) 0) • ageDrift) _s = (max (t - t₀) 0) • ageDrift := by
      show ∫ _s in Set.Icc t₀ t, ageDrift = _
      rw [setIntegral_const]
      simp [Real.volume_real_Icc]
    rw [this]

@[simp] theorem refractoryClock_totalIntensity (lam d : ℝ) (hlam : 0 ≤ lam)
    (z : DavisState Bool 1) :
    (refractoryClockSHS lam d hlam).totalIntensity z =
      if d ≤ z.2.1 0 then lam else 0 := by
  simp [totalIntensity, refractoryClockSHS]

@[simp] theorem refractoryClock_resetDavisState (lam d : ℝ) (hlam : 0 ≤ lam)
    (ℓ : Fin 1) (z : DavisState Bool 1) :
    (refractoryClockSHS lam d hlam).resetDavisState ℓ z = (!z.1, 0, z.2.2) := rfl

/-- The age after a reset is zero. -/
@[simp] theorem refractoryClock_reset_age (lam d : ℝ) (hlam : 0 ≤ lam)
    (ℓ : Fin 1) (z : DavisState Bool 1) :
    ((refractoryClockSHS lam d hlam).resetDavisState ℓ z).2.1 0 = 0 := by
  simp

/-- Flowing for a duration `u` increases the age by `u`. -/
@[simp] theorem refractoryClock_davisFlow_age (lam d : ℝ) (hlam : 0 ≤ lam)
    (u : ℝ≥0) (z : DavisState Bool 1) :
    (davisFlow (refractoryClockSHS lam d hlam) (refractoryClockFlow lam d hlam)
      u z).2.1 0 = z.2.1 0 + (u : ℝ) := by
  show (z.2.1 + (max (z.2.2 + (u : ℝ) - z.2.2) 0) • ageDrift) 0 = _
  simp

/-- The augmented flow of the refractory clock is regular. -/
theorem refractoryClock_flowRegular (lam d : ℝ) (hlam : 0 ≤ lam) :
    DavisFlowRegular (refractoryClockSHS lam d hlam)
      (refractoryClockFlow lam d hlam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    show Measurable fun z : DavisState Bool 1 =>
      (z.1, z.2.1 + (max (z.2.2 + (u : ℝ) - z.2.2) 0) • ageDrift, z.2.2 + (u : ℝ))
    fun_prop
  · show Measurable fun p : ℝ≥0 × DavisState Bool 1 =>
      (p.2.1, p.2.2.1 + (max (p.2.2.2 + (p.1 : ℝ) - p.2.2.2) 0) • ageDrift,
        p.2.2.2 + (p.1 : ℝ))
    have hcoe : Measurable fun p : ℝ≥0 × DavisState Bool 1 => (p.1 : ℝ) :=
      measurable_coe_nnreal_real.comp measurable_fst
    fun_prop
  · intro s t z
    show ((z.1, z.2.1 + (max (z.2.2 + ((s : ℝ) + (t : ℝ)) - z.2.2) 0) • ageDrift,
        z.2.2 + ((s : ℝ) + (t : ℝ))) : DavisState Bool 1) = _
    show _ = ((z.1, (z.2.1 + (max (z.2.2 + (t : ℝ) - z.2.2) 0) • ageDrift) +
        (max ((z.2.2 + (t : ℝ)) + (s : ℝ) - (z.2.2 + (t : ℝ))) 0) • ageDrift,
        (z.2.2 + (t : ℝ)) + (s : ℝ)) : DavisState Bool 1)
    have hs : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
    refine Prod.ext rfl (Prod.ext ?_ (by push_cast; ring))
    show z.2.1 + (max (z.2.2 + ((s : ℝ) + (t : ℝ)) - z.2.2) 0) • ageDrift = _
    rw [show z.2.2 + ((s : ℝ) + (t : ℝ)) - z.2.2 = (s : ℝ) + (t : ℝ) by ring,
      show z.2.2 + (t : ℝ) - z.2.2 = (t : ℝ) by ring,
      show (z.2.2 + (t : ℝ)) + (s : ℝ) - (z.2.2 + (t : ℝ)) = (s : ℝ) by ring,
      max_eq_left (by linarith : (0 : ℝ) ≤ (s : ℝ) + (t : ℝ)),
      max_eq_left hs, max_eq_left ht, add_smul]
    abel_nf

/-- The reset channel of the refractory clock is regular. -/
theorem refractoryClock_resetRegular (lam d : ℝ) (hlam : 0 ≤ lam) :
    DavisResetRegular (refractoryClockSHS lam d hlam) := by
  refine ⟨?_, ?_⟩
  · intro ℓ
    show Measurable fun z : DavisState Bool 1 => ((!z.1), (0 : EuclideanSpace ℝ (Fin 1)), z.2.2)
    fun_prop
  · intro ℓ z _ h
    have : (!z.1) = z.1 := congrArg (fun y => y.1) h
    exact (Bool.not_ne_self z.1) this

/-- **The accumulated hazard of the refractory clock vanishes below the age
`d`.**  From a state of age zero, the hazard accumulated over an elapsed
duration `u` is `lam * max (u - d) 0`. -/
theorem refractoryClock_integratedHazard (lam d : ℝ) (hlam : 0 ≤ lam)
    (hd : 0 ≤ d) (z : DavisState Bool 1) (hz : z.2.1 0 = 0) (u : ℝ≥0) :
    davisIntegratedHazard (refractoryClockSHS lam d hlam)
      (refractoryClockFlow lam d hlam) z u = lam * max ((u : ℝ) - d) 0 := by
  rw [davisIntegratedHazard]
  have hcongr : Set.EqOn
      (fun s : ℝ => (refractoryClockSHS lam d hlam).totalIntensity
        (davisFlow (refractoryClockSHS lam d hlam) (refractoryClockFlow lam d hlam)
          s.toNNReal z))
      (Set.indicator (Set.Ici d) (fun _ => lam)) (Set.Icc (0 : ℝ) (u : ℝ)) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1
    simp only [refractoryClock_totalIntensity, refractoryClock_davisFlow_age, hz,
      Real.coe_toNNReal _ hs0, zero_add, Set.indicator_apply, Set.mem_Ici]
  rw [setIntegral_congr_fun measurableSet_Icc hcongr,
    setIntegral_indicator measurableSet_Ici]
  have hinter : Set.Icc (0 : ℝ) (u : ℝ) ∩ Set.Ici d = Set.Icc d (u : ℝ) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨le_trans hd h1, h2⟩, h1⟩
  rw [hinter, setIntegral_const]
  simp [Real.volume_real_Icc, mul_comm]

/-- **The survivor factor of the refractory clock.** -/
theorem refractoryClock_segmentSurvivor (lam d : ℝ) (hlam : 0 ≤ lam)
    (hd : 0 ≤ d) (z : DavisState Bool 1) (hz : z.2.1 0 = 0) (u : ℝ≥0) :
    davisSegmentSurvivor (refractoryClockSHS lam d hlam)
      (refractoryClockFlow lam d hlam) z u
      = Real.exp (-(lam * max ((u : ℝ) - d) 0)) := by
  rw [davisSegmentSurvivor, refractoryClock_integratedHazard lam d hlam hd z hz u]

/-- Every state reached after a jump has age zero, and so does the initial
state if it is chosen with age zero. -/
theorem refractoryClock_stateAfterJump_age (lam d : ℝ) (hlam : 0 ≤ lam)
    {Ω : Type*} (ξ : DavisJumpNoise 1 Ω) (initial : DavisState Bool 1)
    (hinit : initial.2.1 0 = 0) (k : ℕ) (ω : Ω) :
    (davisStateAfterJump (refractoryClockSHS lam d hlam)
      (refractoryClockFlow lam d hlam) ξ initial k ω).2.1 0 = 0 := by
  cases k with
  | zero => exact hinit
  | succ k => simp

end SHS
