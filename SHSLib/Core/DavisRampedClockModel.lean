import SHSLib.Core.DavisAgeClockTestFunction

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The ramped refractory clock

The refractory clock of `SHSLib.Core.DavisRefractoryClockModel` switches its
intensity on abruptly at the age `d`, so the hazard is *not* continuous along
the flow — a hypothesis of the model-level martingale and Dynkin statements.

This module builds a refractory clock whose intensity is continuous: it stays
zero below the age `d`, rises linearly on `[d, d+1]` and is capped at `lam`
afterwards,

`rate y = lam · min (max (y - d) 0) 1`.

The accumulated hazard from an age-zero state is then available in closed form,

`Λ u = lam · (max (u - d) 0 ^ 2 / 2 − max (u - (d+1)) 0 ^ 2 / 2)`,

by the fundamental theorem of calculus — the antiderivative of a positive part
is differentiable *through* the corner.  The module also builds the test
function used with this clock: the profile of the age obtained by integrating
the bump `rate 1 d − rate 1 (d+1)`, which is zero below the age `d`, rises to
one on `[d, d+2]` and stays there.  Being constant where the rate vanishes, it
is exactly the compatibility condition of
`SHSLib.Core.DavisAgeClockTestFunction`, and it is bounded by one with a
derivative bounded by one.
-/

namespace SHS

/-! ## Calculus of positive parts -/

/-- The antiderivative of a positive part is differentiable everywhere, the
corner included. -/
theorem hasDerivAt_posPart_sq_half (c x : ℝ) :
    HasDerivAt (fun y : ℝ => max (y - c) 0 ^ 2 / 2) (max (x - c) 0) x := by
  rcases lt_trichotomy x c with hx | hx | hx
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] fun y : ℝ => max (y - c) 0 ^ 2 / 2 := by
      filter_upwards [gt_mem_nhds hx] with y hy
      rw [max_eq_right (by linarith : y - c ≤ 0)]
      norm_num
    rw [max_eq_right (by linarith : x - c ≤ 0)]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev.symm
  · subst hx
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro e he
    filter_upwards [Metric.ball_mem_nhds x (by positivity : (0 : ℝ) < 2 * e)] with y hy
    have hy' : |y - x| < 2 * e := by simpa [Real.dist_eq] using hy
    have h1 : max (y - x) 0 ≤ |y - x| := max_le (le_abs_self _) (abs_nonneg _)
    have h2 : (0 : ℝ) ≤ max (y - x) 0 := le_max_right _ _
    have hb : max (y - x) 0 ^ 2 / 2 ≤ e * |y - x| := by
      nlinarith [abs_nonneg (y - x)]
    have hn : ‖max (y - x) 0 ^ 2 / 2‖ ≤ e * ‖y - x‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb
    simpa using hn
  · have hev : (fun y : ℝ => (y - c) ^ 2 / 2) =ᶠ[nhds x] fun y : ℝ => max (y - c) 0 ^ 2 / 2 := by
      filter_upwards [lt_mem_nhds hx] with y hy
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ y - c)]
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ x - c)]
    have h : HasDerivAt (fun y : ℝ => (y - c) ^ 2 / 2) ((2 * (x - c) ^ 1 * 1) / 2) x :=
      (((hasDerivAt_id x).sub_const c).pow 2).div_const 2
    have h2 : (2 * (x - c) ^ 1 * 1) / 2 = x - c := by ring
    rw [h2] at h
    exact h.congr_of_eventuallyEq hev.symm

/-- A capped positive part is a difference of two positive parts. -/
theorem min_max_zero_one (y : ℝ) : min (max y 0) 1 = max y 0 - max (y - 1) 0 := by
  rcases le_total y 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : y - 1 ≤ 0),
      min_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
    ring
  · rcases le_total y 1 with h1 | h1
    · rw [max_eq_left h, max_eq_right (by linarith : y - 1 ≤ 0), min_eq_left h1]
      ring
    · rw [max_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ y - 1), min_eq_right h1]
      ring

/-! ## The ramped rate and its accumulated hazard -/

/-- The ramped intensity: zero below the age `d`, rising linearly, capped at
`lam`. -/
def rampRate (lam d : ℝ) : ℝ → ℝ := fun y => lam * min (max (y - d) 0) 1

/-- The hazard accumulated by the ramped rate from age zero. -/
def rampedHazard (lam d : ℝ) : ℝ → ℝ := fun u =>
  lam * (max (u - d) 0 ^ 2 / 2 - max (u - (d + 1)) 0 ^ 2 / 2)

theorem rampRate_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (d y : ℝ) :
    0 ≤ rampRate lam d y :=
  mul_nonneg hlam (le_min (le_max_right _ _) zero_le_one)

theorem rampRate_le {lam : ℝ} (hlam : 0 ≤ lam) (d y : ℝ) : rampRate lam d y ≤ lam := by
  rw [rampRate]
  have h1 : min (max (y - d) 0) 1 ≤ 1 := min_le_right _ _
  nlinarith

theorem continuous_rampRate (lam d : ℝ) : Continuous (rampRate lam d) :=
  continuous_const.mul
    (((continuous_id.sub continuous_const).max continuous_const).min continuous_const)

theorem rampRate_eq_zero_iff {lam : ℝ} (hlam : 0 < lam) (d y : ℝ) :
    rampRate lam d y = 0 ↔ y ≤ d := by
  rw [rampRate, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (ne_of_gt hlam)
    · by_contra hy
      push_neg at hy
      have h1 : 0 < max (y - d) 0 := lt_max_of_lt_left (by linarith)
      have h2 : 0 < min (max (y - d) 0) 1 := lt_min h1 zero_lt_one
      exact absurd h (ne_of_gt h2)
  · intro hy
    right
    rw [max_eq_right (by linarith : y - d ≤ 0), min_eq_left (by norm_num : (0 : ℝ) ≤ 1)]

theorem hasDerivAt_rampedHazard (lam d s : ℝ) :
    HasDerivAt (rampedHazard lam d) (rampRate lam d s) s := by
  have h := ((hasDerivAt_posPart_sq_half d s).sub
    (hasDerivAt_posPart_sq_half (d + 1) s)).const_mul lam
  have he : lam * (max (s - d) 0 - max (s - (d + 1)) 0) = rampRate lam d s := by
    rw [rampRate, min_max_zero_one]
    ring_nf
  rw [he] at h
  exact h

theorem continuous_rampedHazard (lam d : ℝ) : Continuous (rampedHazard lam d) := by
  unfold rampedHazard
  fun_prop

theorem rampedHazard_zero_of_le {lam d u : ℝ} (hu : u ≤ d) :
    rampedHazard lam d u = 0 := by
  rw [rampedHazard, max_eq_right (by linarith : u - d ≤ 0),
    max_eq_right (by linarith : u - (d + 1) ≤ 0)]
  ring

theorem rampedHazard_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (d u : ℝ) :
    0 ≤ rampedHazard lam d u := by
  rw [rampedHazard]
  have h1 : max (u - (d + 1)) 0 ≤ max (u - d) 0 :=
    max_le_max (by linarith) le_rfl
  have h2 : (0 : ℝ) ≤ max (u - (d + 1)) 0 := le_max_right _ _
  have : max (u - (d + 1)) 0 ^ 2 ≤ max (u - d) 0 ^ 2 := by nlinarith
  nlinarith

/-- **The integral of the ramped rate is the closed-form hazard.** -/
theorem integral_rampRate (lam : ℝ) {d u : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u) :
    ∫ s in Set.Icc (0 : ℝ) u, rampRate lam d s = rampedHazard lam d u := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_rampedHazard lam d s)
      ((continuous_rampRate lam d).intervalIntegrable 0 u),
    rampedHazard_zero_of_le hd, sub_zero]

/-! ## The bump profile used as a test function -/

/-- The bump of unit height supported by the ages between `d` and `d + 2`. -/
def rampBump (d : ℝ) : ℝ → ℝ := fun y => rampRate 1 d y - rampRate 1 (d + 1) y

/-- The profile of the age obtained by integrating the bump: zero below the age
`d`, one above the age `d + 2`. -/
def rampProfile (d : ℝ) : ℝ → ℝ := fun y => rampedHazard 1 d y - rampedHazard 1 (d + 1) y

theorem continuous_rampBump (d : ℝ) : Continuous (rampBump d) :=
  (continuous_rampRate 1 d).sub (continuous_rampRate 1 (d + 1))

theorem continuous_rampProfile (d : ℝ) : Continuous (rampProfile d) :=
  (continuous_rampedHazard 1 d).sub (continuous_rampedHazard 1 (d + 1))

theorem hasDerivAt_rampProfile (d y : ℝ) :
    HasDerivAt (rampProfile d) (rampBump d y) y :=
  (hasDerivAt_rampedHazard 1 d y).sub (hasDerivAt_rampedHazard 1 (d + 1) y)

theorem rampProfile_eq_zero_of_le {d y : ℝ} (hy : y ≤ d) : rampProfile d y = 0 := by
  rw [rampProfile, rampedHazard_zero_of_le hy,
    rampedHazard_zero_of_le (by linarith : y ≤ d + 1), sub_zero]

theorem rampBump_nonneg (d y : ℝ) : 0 ≤ rampBump d y := by
  rw [rampBump, rampRate, rampRate, one_mul, one_mul, sub_nonneg]
  exact min_le_min (max_le_max (by linarith) le_rfl) le_rfl

theorem rampBump_le_one (d y : ℝ) : rampBump d y ≤ 1 := by
  have h1 : rampRate 1 d y ≤ 1 := rampRate_le zero_le_one d y
  have h2 : 0 ≤ rampRate 1 (d + 1) y := rampRate_nonneg zero_le_one (d + 1) y
  rw [rampBump]
  linarith

theorem abs_rampBump_le_one (d y : ℝ) : |rampBump d y| ≤ 1 :=
  abs_le.2 ⟨by linarith [rampBump_nonneg d y], rampBump_le_one d y⟩

theorem rampProfile_nonneg (d y : ℝ) : 0 ≤ rampProfile d y := by
  rw [rampProfile, rampedHazard, rampedHazard, one_mul, one_mul, sub_nonneg]
  set w := y - d with hw
  have e1 : y - (d + 1) = w - 1 := by rw [hw]; ring
  have e2 : y - (d + 1 + 1) = w - 2 := by rw [hw]; ring
  rw [e1, e2]
  rcases le_total w 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : w - 1 ≤ 0),
      max_eq_right (by linarith : w - 2 ≤ 0)]
  rcases le_total w 1 with h1 | h1
  · rw [max_eq_left h, max_eq_right (by linarith : w - 1 ≤ 0),
      max_eq_right (by linarith : w - 2 ≤ 0)]
    nlinarith
  rcases le_total w 2 with h2 | h2
  · rw [max_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ w - 1),
      max_eq_right (by linarith : w - 2 ≤ 0)]
    nlinarith
  · rw [max_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ w - 1),
      max_eq_left (by linarith : (0 : ℝ) ≤ w - 2)]
    nlinarith

theorem rampProfile_le_one (d y : ℝ) : rampProfile d y ≤ 1 := by
  rw [rampProfile, rampedHazard, rampedHazard, one_mul, one_mul]
  set w := y - d with hw
  have e1 : y - (d + 1) = w - 1 := by rw [hw]; ring
  have e2 : y - (d + 1 + 1) = w - 2 := by rw [hw]; ring
  rw [e1, e2]
  rcases le_total w 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : w - 1 ≤ 0),
      max_eq_right (by linarith : w - 2 ≤ 0)]
    norm_num
  rcases le_total w 1 with h1 | h1
  · rw [max_eq_left h, max_eq_right (by linarith : w - 1 ≤ 0),
      max_eq_right (by linarith : w - 2 ≤ 0)]
    nlinarith
  rcases le_total w 2 with h2 | h2
  · rw [max_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ w - 1),
      max_eq_right (by linarith : w - 2 ≤ 0)]
    nlinarith
  · rw [max_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ w - 1),
      max_eq_left (by linarith : (0 : ℝ) ≤ w - 2)]
    nlinarith

theorem abs_rampProfile_le_one (d y : ℝ) : |rampProfile d y| ≤ 1 :=
  abs_le.2 ⟨by linarith [rampProfile_nonneg d y], rampProfile_le_one d y⟩

/-- The profile of the age is one-Lipschitz, its derivative being bounded by
one. -/
theorem rampProfile_lipschitz (d y y' : ℝ) :
    |rampProfile d y - rampProfile d y'| ≤ 1 * |y - y'| := by
  have hlip : LipschitzWith 1 (rampProfile d) := by
    refine lipschitzWith_of_nnnorm_deriv_le
      (fun x => (hasDerivAt_rampProfile d x).differentiableAt) fun x => ?_
    rw [(hasDerivAt_rampProfile d x).deriv]
    simp only [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs]
    exact abs_rampBump_le_one d x
  have := hlip.dist_le_mul y y'
  rw [Real.dist_eq, Real.dist_eq] at this
  simpa using this

/-! ## The model -/

/-- **The ramped refractory clock.** -/
def rampedClockSHS (lam d : ℝ) (hlam : 0 ≤ lam) : SHS Bool 1 1 :=
  ageClockSHS (rampRate lam d) (rampRate_nonneg hlam d)

/-- Its flow. -/
def rampedClockFlow (lam d : ℝ) (hlam : 0 ≤ lam) :
    (rampedClockSHS lam d hlam).HasGlobalFlow :=
  ageClockFlow (rampRate lam d) (rampRate_nonneg hlam d)

/-- **The accumulated hazard of the ramped clock from an age-zero state.** -/
theorem rampedClock_integratedHazard {lam d : ℝ} (hlam : 0 ≤ lam) (hd : 0 ≤ d)
    (z : DavisState Bool 1) (hz : z.2.1 0 = 0) (u : ℝ≥0) :
    davisIntegratedHazard (rampedClockSHS lam d hlam) (rampedClockFlow lam d hlam) z u
      = rampedHazard lam d (u : ℝ) := by
  have h := ageClock_integratedHazard (rampRate lam d) (rampRate_nonneg hlam d) z u
  rw [hz] at h
  simp only [zero_add] at h
  rw [show davisIntegratedHazard (rampedClockSHS lam d hlam)
      (rampedClockFlow lam d hlam) z u
        = davisIntegratedHazard (ageClockSHS (rampRate lam d) (rampRate_nonneg hlam d))
          (ageClockFlow (rampRate lam d) (rampRate_nonneg hlam d)) z u from rfl, h]
  exact integral_rampRate lam hd u.coe_nonneg

/-- **The survivor factor of the ramped clock from an age-zero state.** -/
theorem rampedClock_segmentSurvivor {lam d : ℝ} (hlam : 0 ≤ lam) (hd : 0 ≤ d)
    (z : DavisState Bool 1) (hz : z.2.1 0 = 0) (u : ℝ≥0) :
    davisSegmentSurvivor (rampedClockSHS lam d hlam) (rampedClockFlow lam d hlam) z u
      = Real.exp (-rampedHazard lam d (u : ℝ)) := by
  rw [davisSegmentSurvivor, rampedClock_integratedHazard hlam hd z hz u]

/-- **The hazard of the ramped clock is continuous along the flow** — the point
of the ramp. -/
theorem rampedClock_hazardContinuousAlongFlow {lam d : ℝ} (hlam : 0 ≤ lam) :
    DavisHazardContinuousAlongFlow (rampedClockSHS lam d hlam)
      (rampedClockFlow lam d hlam) :=
  ageClock_hazardContinuousAlongFlow (rampRate_nonneg hlam d) (continuous_rampRate lam d)

/-- The total intensity of the ramped clock is bounded by `lam`. -/
theorem rampedClock_totalIntensity_le {lam d : ℝ} (hlam : 0 ≤ lam)
    (z : DavisState Bool 1) :
    (rampedClockSHS lam d hlam).totalIntensity z ≤ lam :=
  ageClock_totalIntensity_le (rampRate_nonneg hlam d) (rampRate_le hlam d) z

/-- The test function of the ramped clock: the bump profile of the age. -/
def rampedClockTest (d : ℝ) : DavisState Bool 1 → ℝ := ageTestFunction (rampProfile d)

/-- Its flow generator. -/
def rampedClockTestGenerator (d : ℝ) : DavisState Bool 1 → ℝ :=
  ageTestFunction (rampBump d)

/-- The profile is constant where the ramped rate vanishes, which is the
compatibility condition required of a test function of the age. -/
theorem rampProfile_vanish {lam d : ℝ} (hlam : 0 < lam) (hd : 0 ≤ d) (y : ℝ) :
    rampRate lam d y = 0 → rampProfile d y = rampProfile d 0 := by
  intro h
  rw [rampProfile_eq_zero_of_le ((rampRate_eq_zero_iff hlam d y).1 h),
    rampProfile_eq_zero_of_le hd]

end SHS
