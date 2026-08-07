import SHSLib.Core.DavisRefractoryClockModel

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Age-dependent clocks

The refractory clock of `SHSLib.Core.DavisRefractoryClockModel` is one member of
a family: a two-mode model whose single continuous coordinate is the age since
the last jump, whose reset toggles the mode and sets the age back to zero, and
whose intensity is an arbitrary nonnegative function `rate` of the age.

This module records that family once and for all — the flow, its regularity,
the regularity of the reset, measurability of the intensities, continuity of
the hazard along the flow, a uniform bound on the total intensity, and the
accumulated hazard as a one-dimensional integral of `rate`.  Concrete clocks
are then obtained by choosing `rate`; the ramped clock of
`SHSLib.Core.DavisRampedClockModel` is the choice that makes the intensity
itself continuous while keeping a refractory window.
-/

namespace SHS

/-- **The age clock at an age-dependent rate.**  Two modes, the age since the
last jump as the continuous coordinate, one reset channel that toggles the mode
and resets the age, and the intensity `rate` evaluated at the age. -/
def ageClockSHS (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y) : SHS Bool 1 1 where
  f := fun _ _ _ => ageDrift
  phi := fun _ q _ _ => (!q, 0)
  intensity := fun _ _ x _ => rate (x 0)
  intensity_nonneg := fun _ _ x _ => hrate (x 0)

/-- The flow of the age clock: the age grows at unit speed. -/
def ageClockFlow (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y) :
    (ageClockSHS rate hrate).HasGlobalFlow where
  flow := fun t₀ _ x₀ t => x₀ + (max (t - t₀) 0) • ageDrift
  flow_init := by intro t₀ q₀ x₀; simp
  flow_ode := by
    intro t₀ q₀ x₀ t
    have : ∫ _s in Set.Icc t₀ t, (ageClockSHS rate hrate).f q₀
        (x₀ + (max (_s - t₀) 0) • ageDrift) _s = (max (t - t₀) 0) • ageDrift := by
      show ∫ _s in Set.Icc t₀ t, ageDrift = _
      rw [setIntegral_const]
      simp [Real.volume_real_Icc]
    rw [this]

@[simp] theorem ageClock_totalIntensity (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y)
    (z : DavisState Bool 1) :
    (ageClockSHS rate hrate).totalIntensity z = rate (z.2.1 0) := by
  simp [totalIntensity, ageClockSHS]

@[simp] theorem ageClock_resetDavisState (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y)
    (ℓ : Fin 1) (z : DavisState Bool 1) :
    (ageClockSHS rate hrate).resetDavisState ℓ z = (!z.1, 0, z.2.2) := rfl

/-- The age after a reset is zero. -/
@[simp] theorem ageClock_reset_age (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y)
    (ℓ : Fin 1) (z : DavisState Bool 1) :
    ((ageClockSHS rate hrate).resetDavisState ℓ z).2.1 0 = 0 := by
  simp

/-- Flowing for a duration `u` increases the age by `u`. -/
@[simp] theorem ageClock_davisFlow_age (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y)
    (u : ℝ≥0) (z : DavisState Bool 1) :
    (davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) u z).2.1 0
      = z.2.1 0 + (u : ℝ) := by
  show (z.2.1 + (max (z.2.2 + (u : ℝ) - z.2.2) 0) • ageDrift) 0 = _
  simp

/-- The mode is unchanged along the flow. -/
@[simp] theorem ageClock_davisFlow_mode (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y)
    (u : ℝ≥0) (z : DavisState Bool 1) :
    (davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) u z).1 = z.1 := rfl

/-- The augmented flow of the age clock is regular. -/
theorem ageClock_flowRegular (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y) :
    DavisFlowRegular (ageClockSHS rate hrate) (ageClockFlow rate hrate) := by
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

/-- The reset channel of the age clock is regular. -/
theorem ageClock_resetRegular (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y) :
    DavisResetRegular (ageClockSHS rate hrate) := by
  refine ⟨?_, ?_⟩
  · intro ℓ
    show Measurable fun z : DavisState Bool 1 =>
      ((!z.1), (0 : EuclideanSpace ℝ (Fin 1)), z.2.2)
    fun_prop
  · intro ℓ z _ h
    have : (!z.1) = z.1 := congrArg (fun y => y.1) h
    exact (Bool.not_ne_self z.1) this

/-- The intensities of the age clock are measurable as soon as the rate is. -/
theorem ageClock_intensitiesMeasurable {rate : ℝ → ℝ} (hrate : ∀ y, 0 ≤ rate y)
    (hm : Measurable rate) : (ageClockSHS rate hrate).IntensitiesMeasurable where
  measurable := fun _ => by
    have hage : Measurable fun p : Bool × EuclideanSpace ℝ (Fin 1) × ℝ => p.2.1 0 := by
      fun_prop
    exact hm.comp hage

/-- Every state reached after a jump has age zero, and so does the initial
state if it is chosen with age zero. -/
theorem ageClock_stateAfterJump_age (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y)
    {Ω : Type*} (ξ : DavisJumpNoise 1 Ω) (initial : DavisState Bool 1)
    (hinit : initial.2.1 0 = 0) (k : ℕ) (ω : Ω) :
    (davisStateAfterJump (ageClockSHS rate hrate) (ageClockFlow rate hrate) ξ
      initial k ω).2.1 0 = 0 := by
  cases k with
  | zero => exact hinit
  | succ k => simp

/-- **The hazard of the age clock is continuous along the flow** as soon as the
rate is continuous. -/
theorem ageClock_hazardContinuousAlongFlow {rate : ℝ → ℝ} (hrate : ∀ y, 0 ≤ rate y)
    (hc : Continuous rate) :
    DavisHazardContinuousAlongFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) := by
  intro z
  simp only [ageClock_totalIntensity, ageClock_davisFlow_age]
  have hcoe : Continuous fun s : ℝ => ((s.toNNReal : ℝ)) := by
    simp only [Real.coe_toNNReal']
    exact continuous_id.max continuous_const
  exact hc.comp (continuous_const.add hcoe)

/-- A uniform bound on the rate bounds the total intensity of the age clock. -/
theorem ageClock_totalIntensity_le {rate : ℝ → ℝ} (hrate : ∀ y, 0 ≤ rate y)
    {Lam : ℝ} (hL : ∀ y, rate y ≤ Lam) (z : DavisState Bool 1) :
    (ageClockSHS rate hrate).totalIntensity z ≤ Lam := by
  simpa using hL (z.2.1 0)

/-- **The accumulated hazard of the age clock** is the integral of the rate
along the ages visited by the flow. -/
theorem ageClock_integratedHazard (rate : ℝ → ℝ) (hrate : ∀ y, 0 ≤ rate y)
    (z : DavisState Bool 1) (u : ℝ≥0) :
    davisIntegratedHazard (ageClockSHS rate hrate) (ageClockFlow rate hrate) z u
      = ∫ s in Set.Icc (0 : ℝ) (u : ℝ), rate (z.2.1 0 + s) := by
  rw [davisIntegratedHazard]
  refine setIntegral_congr_fun measurableSet_Icc ?_
  intro s hs
  simp only [ageClock_totalIntensity, ageClock_davisFlow_age,
    Real.coe_toNNReal _ hs.1]

/-! ## Shifted integrals along the age -/

/-- The primitive of a function of the age, based at zero. -/
def agePrimitive (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..y, f t

theorem continuous_agePrimitive {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (agePrimitive f) :=
  intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) 0

/-- An integral of a continuous function of the age over an elapsed window is a
difference of values of its primitive. -/
theorem integral_Icc_comp_add {f : ℝ → ℝ} (hf : Continuous f) (a u : ℝ)
    (hu : 0 ≤ u) :
    ∫ s in Set.Icc (0 : ℝ) u, f (a + s) = agePrimitive f (a + u) - agePrimitive f a := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu,
    intervalIntegral.integral_comp_add_left f a, add_zero]
  exact (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)).symm

/-- **The accumulated hazard of the age clock in closed form**: a difference of
values of the primitive of the rate. -/
theorem ageClock_integratedHazard_eq_primitive {rate : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hc : Continuous rate) (z : DavisState Bool 1)
    (u : ℝ≥0) :
    davisIntegratedHazard (ageClockSHS rate hrate) (ageClockFlow rate hrate) z u
      = agePrimitive rate (z.2.1 0 + (u : ℝ)) - agePrimitive rate (z.2.1 0) := by
  rw [ageClock_integratedHazard rate hrate z u, integral_Icc_comp_add hc _ _ u.coe_nonneg]

/-- The survivor factor of the age clock is jointly continuous in the state and
the elapsed duration. -/
theorem ageClock_continuous_survivor {rate : ℝ → ℝ} (hc : Continuous rate) :
    Continuous fun p : ℝ × ℝ≥0 =>
      Real.exp (-(agePrimitive rate (p.1 + (p.2 : ℝ)) - agePrimitive rate p.1)) := by
  have hcoe : Continuous fun p : ℝ × ℝ≥0 => (p.2 : ℝ) :=
    NNReal.continuous_coe.comp continuous_snd
  exact Real.continuous_exp.comp
    (((continuous_agePrimitive hc).comp (continuous_fst.add hcoe)).sub
      ((continuous_agePrimitive hc).comp continuous_fst)).neg

end SHS
