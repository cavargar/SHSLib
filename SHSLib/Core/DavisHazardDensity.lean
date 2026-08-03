import SHSLib.Core.DavisSegmentCompensator

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Density calculus for Davis holding-time hazards

This module supplies the deterministic calculus behind the holding-time
compensator.  Under continuity of total intensity along every deterministic
flow segment, the survivor has hazard density and the accumulated density mass
through elapsed time `u` is `1 - survivor(u)`.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Continuity of the total jump intensity along each time-augmented Davis flow
trajectory.  This is the additional analytic regularity needed to differentiate
the integrated hazard. -/
def DavisHazardContinuousAlongFlow (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) : Prop :=
  ∀ z : DavisState Q n, Continuous (fun s : ℝ =>
    S.totalIntensity (davisFlow S hflow s.toNNReal z))

/-- The hazard-weighted survivor density along a deterministic segment. -/
def davisSegmentHazardDensity (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (z : DavisState Q n) (s : ℝ) : ℝ :=
  S.totalIntensity (davisFlow S hflow s.toNNReal z) *
    Real.exp (-davisIntegratedHazard S hflow z s.toNNReal)

/-- Generic calculus identity: a continuous hazard times its exponential
survivor factor integrates to the loss of that factor. -/
theorem integral_hazard_mul_survivor_Icc
    (lam : ℝ → ℝ) (hlam : Continuous lam)
    (u : ℝ) (hu : 0 ≤ u) :
    ∫ s in Set.Icc (0 : ℝ) u,
        lam s * Real.exp (-(∫ r in Set.Icc (0 : ℝ) s, lam r)) =
      1 - Real.exp (-(∫ r in Set.Icc (0 : ℝ) u, lam r)) := by
  -- Define the cumulative hazard function  
  let F := fun s => ∫ r in (0 : ℝ)..s, lam r
  -- Convert all Icc integrals to interval integrals
  have hF : ∀ s ∈ Set.Icc (0 : ℝ) u, ∫ r in Set.Icc (0 : ℝ) s, lam r = F s := by
    intro s hs
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.1]
  have hFu : ∫ r in Set.Icc (0 : ℝ) u, lam r = F u := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu]
  rw [hFu]
  -- Convert integrand
  have h_eq : Set.EqOn (fun s => lam s * Real.exp (-(∫ r in Set.Icc (0 : ℝ) s, lam r)))
           (fun s => lam s * Real.exp (-F s)) (Set.uIcc 0 u) := by
    intro s hs
    simp only
    have hs' : s ∈ Set.Icc (0 : ℝ) u := by rwa [Set.uIcc_of_le hu] at hs
    rw [hF s hs']
  rw [intervalIntegral.integral_congr h_eq]
  -- Use FTC: derivative of (1 - exp(-F x)) is lam x * exp(-F x)
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) u, HasDerivAt (fun s => 1 - Real.exp (-F s)) (lam x * Real.exp (-F x)) x := by
    intro x hx
    have hF_deriv : HasDerivAt F (lam x) x := by
      apply_rules [ intervalIntegral.integral_hasDerivAt_right ]
      · apply ContinuousOn.intervalIntegrable
        exact hlam.continuousOn
      · exact hlam.stronglyMeasurable.stronglyMeasurableAtFilter
      · exact hlam.continuousAt
    have h := HasDerivAt.const_sub 1 (HasDerivAt.exp (hF_deriv.neg))
    convert h using 1 <;> simp [neg_neg, mul_comm]
  have h_cont : ContinuousOn (fun x => lam x * Real.exp (-F x)) (Set.Icc (0 : ℝ) u) := by
    apply ContinuousOn.mul hlam.continuousOn
    exact ContinuousOn.rexp (ContinuousOn.neg (intervalIntegral.continuous_primitive hlam.intervalIntegrable _).continuousOn)
  let G := fun s => 1 - Real.exp (-F s)
  have hG : ∀ x ∈ Set.uIcc (0 : ℝ) u, HasDerivAt G (lam x * Real.exp (-F x)) x := h_deriv
  have h_int : IntervalIntegrable (fun x => lam x * Real.exp (-F x)) volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hu]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG h_int]
  show (1 - Real.exp (-F u)) - (1 - Real.exp (-F 0)) = 1 - Real.exp (-F u)
  rw [hF0]
  simp

/-- The segment hazard density has total mass equal to one minus the endpoint
survivor. -/
theorem integral_davisSegmentHazardDensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (z : DavisState Q n) (u : ℝ≥0) :
    ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s =
      1 - davisSegmentSurvivor S hflow z u := by
  unfold davisSegmentHazardDensity davisSegmentSurvivor davisIntegratedHazard
  have h_eq : ∀ s ∈ Set.Icc (0 : ℝ) (u : ℝ), ↑s.toNNReal = s := by
    intro s hs
    exact congrArg NNReal.toReal (Real.toNNReal_of_nonneg hs.1)
  let lam : ℝ → ℝ := fun s => S.totalIntensity (S.davisFlow hflow s.toNNReal z)
  have hlam_cont : Continuous lam := by
    exact hcont z
  have hlam_nonneg : ∀ s, 0 ≤ lam s := by
    intro s
    exact totalIntensity_nonneg S _
  have h_int_eq : ∀ s ∈ Set.Icc (0 : ℝ) (u : ℝ),
      ∫ (x : ℝ) in Set.Icc 0 ↑s.toNNReal, S.totalIntensity (S.davisFlow hflow x.toNNReal z) =
      ∫ (x : ℝ) in Set.Icc 0 s, lam x := by
    intro s hs
    simp only [lam]
    have hs_eq : ↑s.toNNReal = s := h_eq s hs
    rw [hs_eq]
  have h_outer_eq : (u : ℝ) ≥ 0 := by positivity
  refine Eq.trans ?_ (integral_hazard_mul_survivor_Icc lam hlam_cont u h_outer_eq)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro s hs
  simp only [lam]
  rw [h_int_eq s hs]

/-- Equivalently, survivor mass plus accumulated jump-density mass is one. -/
theorem davisSegmentSurvivor_add_integral_hazardDensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (z : DavisState Q n) (u : ℝ≥0) :
    davisSegmentSurvivor S hflow z u +
        ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          davisSegmentHazardDensity S hflow z s = 1 := by
  rw [integral_davisSegmentHazardDensity S hflow hcont z u]
  ring

/-- The accumulated hazard-density mass is nonnegative. -/
theorem integral_davisSegmentHazardDensity_nonneg
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (z : DavisState Q n) (u : ℝ≥0) :
    0 ≤ ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
      davisSegmentHazardDensity S hflow z s := by
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Icc
  · intro s _
    unfold davisSegmentHazardDensity
    exact mul_nonneg (totalIntensity_nonneg S _) (Real.exp_nonneg _)

end SHS
