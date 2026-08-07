import SHSLib.Core.DavisTwoChannelClock
import SHSLib.Core.DavisAgeCounterAgeTest

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # An age test function on the two-channel refractory clock

Every Dynkin identity proved so far on the two-channel refractory clock of
`SHSLib.Core.DavisTwoChannelClock` uses a test function of the counter, which is
constant along the flow; its flow generator vanishes.  This module proves the
first identity on that object with a **nonzero flow generator**, using the age
test functions of `SHSLib.Core.DavisAgeCounterAgeTest`.

The obstruction to overcome is the compatibility condition: the intensity of the
model vanishes below the dead time `dd`, so an admissible age profile must be
constant on `(−∞, dd]`, and, being required to be continuously differentiable,
must have vanishing derivative at `dd`.  A ramp will not do.  The profile used
here is the *flat ramp*

`flatRamp d y = φ (max (y − d) 0)`,  `φ t = t² / (1 + t²)`,

which is zero below `d`, increases to one above it, is bounded by one,
one-Lipschitz, and continuously differentiable everywhere — the quadratic
vanishing of `φ` at the origin is exactly what glues the two branches into a
`C¹` function at `y = d`.

The gluing itself is isolated as `hasDerivAt_comp_max_sub`: if `φ` is
differentiable with derivative `ψ` and `ψ 0 = 0`, then `y ↦ φ (max (y − d) 0)`
is differentiable everywhere with derivative `ψ (max (y − d) 0)`.  The two open
branches are handled by local equality of functions, and the junction by gluing
the one-sided derivatives on `Iic d` and `Ici d`.
-/

namespace SHS

/-! ## Gluing a profile with a flat piece -/

/-- **A profile composed with a truncated shift is differentiable everywhere**,
provided its derivative vanishes at the origin: the derivative of
`y ↦ φ (max (y − d) 0)` is `ψ (max (y − d) 0)`.  At the junction `y = d` the two
one-sided derivatives are both zero, so they glue. -/
theorem hasDerivAt_comp_max_sub {phi psi : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt phi (psi t) t) (h0 : psi 0 = 0) (d y : ℝ) :
    HasDerivAt (fun x : ℝ => phi (max (x - d) 0)) (psi (max (y - d) 0)) y := by
  have hinner : ∀ z c : ℝ, HasDerivAt (fun x : ℝ => x - c) 1 z := fun z c => by
    simpa using (hasDerivAt_id z).sub_const c
  rcases lt_trichotomy y d with hlt | heq | hgt
  · have hev : (fun x : ℝ => phi (max (x - d) 0)) =ᶠ[nhds y] fun _ => phi 0 := by
      filter_upwards [eventually_lt_nhds hlt] with x hx
      rw [max_eq_right (by linarith)]
    have hm : max (y - d) 0 = 0 := max_eq_right (by linarith)
    rw [hm, h0]
    exact (hasDerivAt_const y (phi 0)).congr_of_eventuallyEq hev
  · have hz : max (y - d) 0 = 0 := max_eq_right (by rw [heq]; simp)
    rw [hz, h0]
    have hleft : HasDerivWithinAt (fun x : ℝ => phi (max (x - d) 0)) 0 (Set.Iic y) y := by
      refine (hasDerivWithinAt_const y (Set.Iic y) (phi 0)).congr ?_ ?_
      · intro x hx
        have hxy := Set.mem_Iic.mp hx
        rw [heq] at hxy
        show phi (max (x - d) 0) = phi 0
        rw [max_eq_right (by linarith)]
      · show phi (max (y - d) 0) = phi 0
        rw [hz]
    have hright : HasDerivWithinAt (fun x : ℝ => phi (max (x - d) 0)) 0 (Set.Ici y) y := by
      have hcomp : HasDerivAt (phi ∘ fun x : ℝ => x - d) (psi (y - d) * 1) y :=
        (hd (y - d)).comp y (hinner y d)
      have hcomp0 : HasDerivAt (fun x : ℝ => phi (x - d)) 0 y := by
        have hzero : psi (y - d) * 1 = 0 := by
          rw [mul_one, show y - d = 0 by rw [heq]; ring, h0]
        rw [hzero] at hcomp
        exact hcomp
      refine hcomp0.hasDerivWithinAt.congr ?_ ?_
      · intro x hx
        have hxy := Set.mem_Ici.mp hx
        rw [heq] at hxy
        show phi (max (x - d) 0) = phi (x - d)
        rw [max_eq_left (by linarith)]
      · show phi (max (y - d) 0) = phi (y - d)
        rw [hz, show y - d = 0 by rw [heq]; ring]
    have hu := hleft.union hright
    rw [Set.Iic_union_Ici] at hu
    exact hasDerivWithinAt_univ.mp hu
  · have hev : (fun x : ℝ => phi (max (x - d) 0)) =ᶠ[nhds y] fun x => phi (x - d) := by
      filter_upwards [eventually_gt_nhds hgt] with x hx
      rw [max_eq_left (by linarith)]
    have hm : max (y - d) 0 = y - d := max_eq_left (by linarith)
    rw [hm]
    have hbase : HasDerivAt (fun x : ℝ => phi (x - d)) (psi (y - d)) y := by
      have hcomp : HasDerivAt (phi ∘ fun x : ℝ => x - d) (psi (y - d) * 1) y :=
        (hd (y - d)).comp y (hinner y d)
      rw [mul_one] at hcomp
      exact hcomp
    exact hbase.congr_of_eventuallyEq hev

/-! ## The quadratic saturation profile -/

/-- The saturating profile `t ↦ t² / (1 + t²)`. -/
def sqRamp : ℝ → ℝ := fun t => t ^ 2 / (1 + t ^ 2)

/-- Its derivative `t ↦ 2 t / (1 + t²)²`. -/
def sqRampDeriv : ℝ → ℝ := fun t => 2 * t / (1 + t ^ 2) ^ 2

@[simp] theorem sqRamp_zero : sqRamp 0 = 0 := by simp [sqRamp]

@[simp] theorem sqRampDeriv_zero : sqRampDeriv 0 = 0 := by simp [sqRampDeriv]

theorem hasDerivAt_sqRamp (t : ℝ) : HasDerivAt sqRamp (sqRampDeriv t) t := by
  have hd : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have h2 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
    simpa using h1.const_add 1
  have h3 := h1.div h2 hd
  have heq : (2 * t * (1 + t ^ 2) - t ^ 2 * (2 * t)) / (1 + t ^ 2) ^ 2
      = sqRampDeriv t := by
    unfold sqRampDeriv
    congr 1
    ring
  rw [heq] at h3
  exact h3

theorem continuous_sqRamp : Continuous sqRamp := by
  unfold sqRamp
  fun_prop (disch := intro x; positivity)

theorem continuous_sqRampDeriv : Continuous sqRampDeriv := by
  unfold sqRampDeriv
  fun_prop (disch := intro x; positivity)

theorem sqRamp_nonneg (t : ℝ) : 0 ≤ sqRamp t := by
  unfold sqRamp; positivity

theorem sqRamp_le_one (t : ℝ) : sqRamp t ≤ 1 := by
  unfold sqRamp
  rw [div_le_one (by positivity)]
  linarith

theorem abs_sqRampDeriv_le (t : ℝ) : |sqRampDeriv t| ≤ 1 := by
  unfold sqRampDeriv
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + t ^ 2) ^ 2),
    div_le_one (by positivity)]
  have h : |2 * t| ≤ 1 + t ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (t + 1), sq_nonneg (t - 1)]
  nlinarith [sq_nonneg t, abs_nonneg (2 * t)]

/-- The saturating profile is one-Lipschitz, by the mean value inequality. -/
theorem sqRamp_lipschitz (a b : ℝ) : |sqRamp a - sqRamp b| ≤ 1 * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := sqRamp) (f' := sqRampDeriv) (s := Set.univ) (C := 1)
    (fun x _ => (hasDerivAt_sqRamp x).hasDerivWithinAt)
    (fun x _ => by simpa [Real.norm_eq_abs] using abs_sqRampDeriv_le x)
    convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h

/-! ## The flat ramp -/

/-- **The flat ramp**: zero below `d`, saturating to one above it, bounded,
one-Lipschitz and continuously differentiable. -/
def flatRamp (d : ℝ) : ℝ → ℝ := fun y => sqRamp (max (y - d) 0)

/-- The derivative of the flat ramp. -/
def flatRampDeriv (d : ℝ) : ℝ → ℝ := fun y => sqRampDeriv (max (y - d) 0)

theorem flatRamp_of_le {d y : ℝ} (h : y ≤ d) : flatRamp d y = 0 := by
  rw [flatRamp, max_eq_right (by linarith), sqRamp_zero]

theorem continuous_flatRamp (d : ℝ) : Continuous (flatRamp d) :=
  continuous_sqRamp.comp ((continuous_id.sub continuous_const).max continuous_const)

theorem continuous_flatRampDeriv (d : ℝ) : Continuous (flatRampDeriv d) :=
  continuous_sqRampDeriv.comp
    ((continuous_id.sub continuous_const).max continuous_const)

theorem measurable_flatRamp (d : ℝ) : Measurable (flatRamp d) :=
  (continuous_flatRamp d).measurable

theorem abs_flatRamp_le (d y : ℝ) : |flatRamp d y| ≤ 1 := by
  show |sqRamp (max (y - d) 0)| ≤ 1
  rw [abs_of_nonneg (sqRamp_nonneg _)]
  exact sqRamp_le_one _

/-- The flat ramp genuinely increases above `d`, so the flow generator of the
corresponding test function does not vanish identically. -/
theorem flatRampDeriv_pos {d y : ℝ} (h : d < y) : 0 < flatRampDeriv d y := by
  show 0 < sqRampDeriv (max (y - d) 0)
  rw [max_eq_left (by linarith)]
  exact div_pos (by linarith) (by positivity)

theorem hasDerivAt_flatRamp (d y : ℝ) :
    HasDerivAt (flatRamp d) (flatRampDeriv d y) y :=
  hasDerivAt_comp_max_sub hasDerivAt_sqRamp sqRampDeriv_zero d y

theorem flatRamp_lipschitz (d y y' : ℝ) :
    |flatRamp d y - flatRamp d y'| ≤ 1 * |y - y'| := by
  have h1 : |flatRamp d y - flatRamp d y'|
      ≤ 1 * |max (y - d) 0 - max (y' - d) 0| := sqRamp_lipschitz _ _
  have h2 : |max (y - d) 0 - max (y' - d) 0| ≤ |(y - d) - (y' - d)| :=
    abs_max_sub_max_le_abs _ _ _
  have h3 : |(y - d) - (y' - d)| = |y - y'| := by
    congr 1
    ring
  rw [one_mul] at h1 ⊢
  exact h1.trans (h2.trans (le_of_eq h3))

end SHS

namespace SHS

section TwoChannelAge

variable {lam : ℝ} (hlam : 0 < lam) {dd : ℝ≥0} (hdd : 0 < dd) {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {hfun hfun' : ℝ → ℝ} {C L : ℝ}

include hlam hdd hp0 hp1

set_option maxHeartbeats 1000000 in
/-- **The Dynkin identity on the two-channel refractory clock for a test
function of the age.**  The flow generator is the derivative of the profile
evaluated at the age, so — unlike for the test functions of the counter — the
compensator carries a genuine flow term.  The profile is required to be
constant, equal to its value at age zero, below the dead time. -/
theorem twoChannel_dynkin_ageProfile (hfm : Measurable hfun) (hfc : Continuous hfun)
    (hC : ∀ y, |hfun y| ≤ C) (hL0 : 0 ≤ L)
    (hL : ∀ y y' : ℝ, |hfun y - hfun y'| ≤ L * |y - y'|)
    (hflat : ∀ y : ℝ, y ≤ (dd : ℝ) → hfun y = hfun 0)
    (hderiv : ∀ y, HasDerivAt hfun (hfun' y) y) (hc' : Continuous hfun')
    (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (ageCounterAgeTest hfun') (ageCounterAgeTest hfun) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 := by
  haveI : (twoChannelModel lam hlam dd p hp0 hp1).IntensitiesMeasurable :=
    twoChannel_intensitiesMeasurable hlam hp0 hp1
  have hvanish : ∀ y, rampRate lam (dd : ℝ) y = 0 → hfun y = hfun 0 := fun y hy =>
    hflat y ((rampRate_eq_zero_iff hlam (dd : ℝ) y).mp hy)
  exact integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_boundedIntensity
    (hf := ageCounter_flowRegular _ _)
    (hr := ageCounter_resetRegular _ _ (twoShifts_measurable _))
    (hξ := twoChannelNoise_measurable lam dd)
    (twoChannel_nonExplosive hdd)
    (twoChannel_conditionalHoldingTimeLaw hlam hp0 hp1 t₀)
    (twoChannel_conditionalChannelLaw hlam hp0 hp1 t₀)
    (ageCounter_hazardContinuousAlongFlow _ _ (twoWeights_sum p)
      (continuous_rampRate lam (dd : ℝ)))
    (ageCounter_ageResetOccupationContinuousAlongFlow _ _ (twoWeights_sum p)
      hvanish (continuous_rampRate lam (dd : ℝ)) hfc)
    (ageCounter_ageResetOccupationRegular _ _ (twoWeights_sum p) hvanish
      (continuous_rampRate lam (dd : ℝ)).measurable (continuous_rampRate lam (dd : ℝ))
      hfm hfc (twoShifts_measurable (dd : ℝ)))
    (measurable_ageCounterAgeTest hfm) C
    (fun z => abs_ageCounterAgeTest_le hC z)
    (ageCounter_ageExpectedResetIncrement_continuous _ _ (twoWeights_sum p)
      hvanish hfc)
    lam (ageCounter_totalIntensity_le _ _ (twoWeights_sum p) (rampRate_le hlam.le _))
    L hL0
    (ageCounter_ageExpectedResetIncrement_lipschitz _ _ (twoWeights_sum p) hvanish hL)
    dd hdd (le_twoChannelNoise_holdingTime lam dd)
    (ageCounter_ageFlowIntegralIdentity _ _ hderiv hc') t

set_option maxHeartbeats 1000000 in
/-- **The martingale property on the two-channel refractory clock for a test
function of the age.** -/
theorem twoChannel_martingale_ageProfile (hfm : Measurable hfun)
    (hfc : Continuous hfun) (hC : ∀ y, |hfun y| ≤ C) (hL0 : 0 ≤ L)
    (hL : ∀ y y' : ℝ, |hfun y - hfun y'| ≤ L * |y - y'|)
    (hflat : ∀ y : ℝ, y ≤ (dd : ℝ) → hfun y = hfun 0)
    (hderiv : ∀ y, HasDerivAt hfun (hfun' y) y) (hc' : Continuous hfun') (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (ageCounterAgeTest hfun') (ageCounterAgeTest hfun))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) := by
  haveI : (twoChannelModel lam hlam dd p hp0 hp1).IntensitiesMeasurable :=
    twoChannel_intensitiesMeasurable hlam hp0 hp1
  have hvanish : ∀ y, rampRate lam (dd : ℝ) y = 0 → hfun y = hfun 0 := fun y hy =>
    hflat y ((rampRate_eq_zero_iff hlam (dd : ℝ) y).mp hy)
  exact martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_boundedIntensity
    (twoChannel_nonExplosive hdd)
    (twoChannel_conditionalHoldingTimeLaw hlam hp0 hp1 t₀)
    (twoChannel_conditionalChannelLaw hlam hp0 hp1 t₀)
    (ageCounter_hazardContinuousAlongFlow _ _ (twoWeights_sum p)
      (continuous_rampRate lam (dd : ℝ)))
    (ageCounter_ageResetOccupationContinuousAlongFlow _ _ (twoWeights_sum p)
      hvanish (continuous_rampRate lam (dd : ℝ)) hfc)
    (ageCounter_ageResetOccupationRegular _ _ (twoWeights_sum p) hvanish
      (continuous_rampRate lam (dd : ℝ)).measurable (continuous_rampRate lam (dd : ℝ))
      hfm hfc (twoShifts_measurable (dd : ℝ)))
    (measurable_ageCounterAgeTest hfm) C
    (fun z => abs_ageCounterAgeTest_le hC z)
    (ageCounter_ageExpectedResetIncrement_continuous _ _ (twoWeights_sum p)
      hvanish hfc)
    lam (ageCounter_totalIntensity_le _ _ (twoWeights_sum p) (rampRate_le hlam.le _))
    L hL0
    (ageCounter_ageExpectedResetIncrement_lipschitz _ _ (twoWeights_sum p) hvanish hL)
    dd hdd (le_twoChannelNoise_holdingTime lam dd)
    (ageCounter_ageFlowIntegralIdentity _ _ hderiv hc')

/-- **The Dynkin identity at the flat ramp of the age.**  This is the first
identity on the two-channel refractory clock whose compensator has a nonzero
flow term: the flow generator is `flatRampDeriv dd` evaluated at the age. -/
theorem twoChannel_dynkin_flatRamp (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (ageCounterAgeTest (flatRampDeriv (dd : ℝ)))
      (ageCounterAgeTest (flatRamp (dd : ℝ))) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  twoChannel_dynkin_ageProfile hlam hdd hp0 hp1 (measurable_flatRamp (dd : ℝ))
    (continuous_flatRamp (dd : ℝ)) (abs_flatRamp_le (dd : ℝ)) zero_le_one
    (flatRamp_lipschitz (dd : ℝ))
    (fun y hy => by
      rw [flatRamp_of_le hy, flatRamp_of_le (le_of_lt (by exact_mod_cast hdd))])
    (hasDerivAt_flatRamp (dd : ℝ)) (continuous_flatRampDeriv (dd : ℝ)) t₀ t

/-- **The martingale property at the flat ramp of the age.** -/
theorem twoChannel_martingale_flatRamp (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (ageCounterAgeTest (flatRampDeriv (dd : ℝ)))
        (ageCounterAgeTest (flatRamp (dd : ℝ))))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) :=
  twoChannel_martingale_ageProfile hlam hdd hp0 hp1 (measurable_flatRamp (dd : ℝ))
    (continuous_flatRamp (dd : ℝ)) (abs_flatRamp_le (dd : ℝ)) zero_le_one
    (flatRamp_lipschitz (dd : ℝ))
    (fun y hy => by
      rw [flatRamp_of_le hy, flatRamp_of_le (le_of_lt (by exact_mod_cast hdd))])
    (hasDerivAt_flatRamp (dd : ℝ)) (continuous_flatRampDeriv (dd : ℝ)) t₀

end TwoChannelAge

end SHS
