import SHSLib.Core.DavisResetOccupationBridge

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Truncated one-segment reset compensation

The single-segment contribution isolated by the segmentwise decomposition of
the capped martingale property is, along one deterministic flow segment
started at `z`, the realized reset increment centered by the occupation
compensator accumulated up to the sampled holding time on a completed segment,
and minus the partial occupation compensator on the segment still active at
the observation time.

This module supplies the deterministic core of the corresponding martingale
statement: averaging that contribution over the holding-time hazard law of the
segment, truncated at an arbitrary elapsed time `u`, gives zero.  Equivalently,
the hazard-averaged centered reset increment accumulated before `u` is exactly
the survivor-weighted partial compensator carried by the segment still active
at `u`.

Everything here is deterministic calculus: an integration by parts against the
survivor factor.  The probabilistic step — replacing the hazard average by a
conditional expectation given the pre-jump history — is the remaining input.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Continuity of the reset occupation density along every deterministic Davis
flow segment.  This is the reset-side analogue of
`DavisHazardContinuousAlongFlow`, and is the regularity needed to
differentiate the partial occupation compensator. -/
def DavisResetOccupationContinuousAlongFlow (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ) : Prop :=
  ∀ z : DavisState Q n, Continuous
    (fun s : ℝ => davisSegmentResetOccupationDensity S hflow g z s)

/-! ## A generic integration-by-parts identity -/

/-- Generic calculus identity behind the truncated compensation: for a
continuous hazard `lam` with survivor factor `exp (-∫ lam)` and a continuous
density `d` with primitive `D`, the hazard average of `D` truncated at `u`,
plus the survivor-weighted endpoint value `exp (-∫₀ᵘ lam) * D u`, equals the
survivor-weighted integral of `d`. -/
theorem integral_hazard_mul_primitive_Icc
    (lam d : ℝ → ℝ) (hlam : Continuous lam) (hd : Continuous d)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫ s in Set.Icc (0 : ℝ) u,
        lam s * Real.exp (-(∫ r in Set.Icc (0 : ℝ) s, lam r)) *
          (∫ r in Set.Icc (0 : ℝ) s, d r)) +
        Real.exp (-(∫ r in Set.Icc (0 : ℝ) u, lam r)) *
          (∫ r in Set.Icc (0 : ℝ) u, d r) =
      ∫ s in Set.Icc (0 : ℝ) u,
        Real.exp (-(∫ r in Set.Icc (0 : ℝ) s, lam r)) * d s := by
  -- Define F(s) = exp(-∫ lam) * ∫ d, use FTC with product rule
  let F := fun s => Real.exp (-(∫ r in (0 : ℝ)..s, lam r)) * (∫ r in (0 : ℝ)..s, d r)
  -- Convert all Icc integrals to interval integrals
  have hF_intlam : ∀ s ∈ Set.Icc (0 : ℝ) u, ∫ r in Set.Icc (0 : ℝ) s, lam r = ∫ r in (0 : ℝ)..s, lam r := by
    intro s hs; rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.1]
  have hF_intd : ∀ s ∈ Set.Icc (0 : ℝ) u, ∫ r in Set.Icc (0 : ℝ) s, d r = ∫ r in (0 : ℝ)..s, d r := by
    intro s hs; rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.1]
  have hF_u_lam : ∫ r in Set.Icc (0 : ℝ) u, lam r = ∫ r in (0 : ℝ)..u, lam r := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu]
  have hF_u_d : ∫ r in Set.Icc (0 : ℝ) u, d r = ∫ r in (0 : ℝ)..u, d r := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu]
  rw [hF_u_d]
  -- Convert integrand using F
  have h_eq : Set.EqOn (fun s => lam s * Real.exp (-(∫ r in Set.Icc (0 : ℝ) s, lam r)) * (∫ r in Set.Icc (0 : ℝ) s, d r))
           (fun s => lam s * Real.exp (-∫ r in (0 : ℝ)..s, lam r) * ∫ r in (0 : ℝ)..s, d r) (Set.uIcc 0 u) := by
    intro s hs
    simp only
    have hs' : s ∈ Set.Icc (0 : ℝ) u := by rwa [Set.uIcc_of_le hu] at hs
    rw [hF_intlam s hs', hF_intd s hs']
  rw [intervalIntegral.integral_congr h_eq]
  -- The derivative of F is: F' = -lam * exp * ∫d + exp * d
  -- So ∫ lam * exp * ∫d = -∫ F' + ∫ exp * d = -(F(u) - F(0)) + ∫ exp * d
  -- Since F(0) = exp(0) * 0 = 0, we get ∫ lam * exp * ∫d = -F(u) + ∫ exp * d
  -- So ∫ lam * exp * ∫d + F(u) = ∫ exp * d
  have hF0 : F 0 = 0 := by simp [F]
  -- Check continuity of lam and d for integrability (for any interval)
  have hlam_int : ∀ a b, IntervalIntegrable lam MeasureTheory.volume a b := hlam.intervalIntegrable
  have hd_int : ∀ a b, IntervalIntegrable d MeasureTheory.volume a b := hd.intervalIntegrable
  -- Define the derivative function
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) u, HasDerivAt F (-(lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r) + Real.exp (-∫ r in (0 : ℝ)..x, lam r) * d x) x := by
    intro x hx
    have hlam_x : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, lam r) (lam x) x := by
      apply_rules [ intervalIntegral.integral_hasDerivAt_right ]
      · exact hlam.stronglyMeasurable.stronglyMeasurableAtFilter
      · exact hlam.continuousAt
    have hd_x : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, d r) (d x) x := by
      apply_rules [ intervalIntegral.integral_hasDerivAt_right ]
      · exact hd.stronglyMeasurable.stronglyMeasurableAtFilter
      · exact hd.continuousAt
    have hexp_deriv : HasDerivAt (fun s => Real.exp (-∫ r in (0 : ℝ)..s, lam r)) (-lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r)) x := by
      convert HasDerivAt.exp (hlam_x.neg) using 1
      simp only [Pi.neg_apply]
      ring
    have hF_deriv : HasDerivAt F (-(lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r) + Real.exp (-∫ r in (0 : ℝ)..x, lam r) * d x) x := by
      convert HasDerivAt.mul hexp_deriv hd_x using 1
      ring
    exact hF_deriv
  have hexp_cont : ContinuousOn (fun x => Real.exp (-∫ r in (0 : ℝ)..x, lam r)) (Set.Icc 0 u) := by
    apply ContinuousOn.rexp
    apply ContinuousOn.neg
    exact intervalIntegral.continuous_primitive hlam_int _ |>.continuousOn
  have hd_int_cont : ContinuousOn (fun x => ∫ r in (0 : ℝ)..x, d r) (Set.Icc 0 u) := by
    exact intervalIntegral.continuous_primitive hd_int _ |>.continuousOn
  have hF_cont : ContinuousOn (fun x => -(lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r) + Real.exp (-∫ r in (0 : ℝ)..x, lam r) * d x) (Set.Icc 0 u) := by
    apply ContinuousOn.add
    · apply ContinuousOn.neg
      apply ContinuousOn.mul (ContinuousOn.mul hlam.continuousOn hexp_cont) hd_int_cont
    · exact hexp_cont.mul hd.continuousOn
  -- Integrate F' from 0 to u
  have hF_int_deriv : IntervalIntegrable (fun x => -(lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r) + Real.exp (-∫ r in (0 : ℝ)..x, lam r) * d x) MeasureTheory.volume 0 u := by
    exact hF_cont.intervalIntegrable_of_Icc hu
  -- Use FTC to get: ∫ F' = F(u) - F(0) = F(u) (since F(0) = 0)
  have h_ftc : ∫ x in (0 : ℝ)..u, -(lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r) + Real.exp (-∫ r in (0 : ℝ)..x, lam r) * d x = F u - F 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv hF_int_deriv]
  rw [hF0, sub_zero] at h_ftc
  -- Split the integral
  have h_split_integral : ∫ x in (0 : ℝ)..u, -(lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r) + Real.exp (-∫ r in (0 : ℝ)..x, lam r) * d x =
               (∫ x in (0 : ℝ)..u, -(lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r)) + (∫ x in (0 : ℝ)..u, Real.exp (-∫ r in (0 : ℝ)..x, lam r) * d x) := by
    rw [intervalIntegral.integral_add]
    · apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.neg (ContinuousOn.mul (ContinuousOn.mul hlam.continuousOn (hexp_cont.mono (Set.uIcc_of_le hu).subset)) (hd_int_cont.mono (Set.uIcc_of_le hu).subset))
    · apply ContinuousOn.intervalIntegrable
      exact (hexp_cont.mono (Set.uIcc_of_le hu).subset).mul hd.continuousOn
  have h_neg_integral : ∫ x in (0 : ℝ)..u, -(lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r) = -∫ x in (0 : ℝ)..u, lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r := by
    rw [intervalIntegral.integral_neg]
  -- Now: -∫ lam*exp*∫d + ∫ exp*d = F(u)
  -- So: ∫ lam*exp*∫d + F(u) = ∫ exp*d
  have h_eq : (∫ x in (0 : ℝ)..u, lam x * Real.exp (-∫ r in (0 : ℝ)..x, lam r) * ∫ r in (0 : ℝ)..x, d r) + F u = ∫ x in (0 : ℝ)..u, Real.exp (-∫ r in (0 : ℝ)..x, lam r) * d x := by linarith [h_ftc, h_split_integral, h_neg_integral]
  -- Convert Set.Icc integrals in the goal to interval integrals
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu]
  rw [h_eq]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu]
  exact intervalIntegral.integral_congr fun s hs => by rw [← hF_intlam s (Set.uIcc_of_le hu ▸ hs)]

/-! ## Continuity of the two segment profiles -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The segment hazard density is continuous in elapsed time. -/
theorem continuous_davisSegmentHazardDensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow) (z : DavisState Q n) :
    Continuous (fun s : ℝ => davisSegmentHazardDensity S hflow z s) := by
  unfold davisSegmentHazardDensity
  apply Continuous.mul
  · exact hcont z
  · refine Continuous.rexp ?_
    refine Continuous.neg ?_
    show Continuous (S.davisIntegratedHazard hflow z ∘ Real.toNNReal)
    apply Continuous.comp
    · have heq : S.davisIntegratedHazard hflow z =
          fun u : ℝ≥0 => ∫ s in (0)..(u : ℝ),
            S.totalIntensity (S.davisFlow hflow s.toNNReal z) := by
        ext u
        unfold davisIntegratedHazard
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
        erw [← intervalIntegral.integral_of_le u.2]
        rfl
      rw [heq]
      have hcont_prim : Continuous (fun b : ℝ => ∫ s in (0)..b,
          S.totalIntensity (S.davisFlow hflow s.toNNReal z)) := by
        apply intervalIntegral.continuous_primitive
        intro a b
        exact (hcont z).intervalIntegrable a b
      exact hcont_prim.comp (by continuity : Continuous (↑· : ℝ≥0 → ℝ))
    · exact continuous_real_toNNReal

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The partial reset occupation compensator is continuous in elapsed time. -/
theorem continuous_davisSegmentResetOccupationCompensator
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (z : DavisState Q n) :
    Continuous (fun s : ℝ =>
      davisSegmentResetOccupationCompensator S hflow g z s.toNNReal) := by
  have hdensity_cont : Continuous (fun s : ℝ => davisSegmentResetOccupationDensity S hflow g z s) :=
    hgcont z
  -- The compensator is the integral of the density
  unfold davisSegmentResetOccupationCompensator
  -- Compose with s ↦ s.toNNReal which is continuous
  have hnnreal_cont : Continuous (fun s : ℝ => s.toNNReal) :=
    continuous_real_toNNReal
  -- Convert set integral to interval integral for u ≥ 0
  have hint_eq : ∀ u : ℝ≥0, ∫ s in Set.Icc 0 (u : ℝ), davisSegmentResetOccupationDensity S hflow g z s =
      ∫ s in (0)..(u : ℝ), davisSegmentResetOccupationDensity S hflow g z s := by
    intro u
    rw [intervalIntegral.integral_of_le (by simp : (0 : ℝ) ≤ u)]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc
  -- The density is integrable on any bounded interval since it's continuous
  have hint_int : ∀ a b : ℝ, IntervalIntegrable (fun s => davisSegmentResetOccupationDensity S hflow g z s) MeasureTheory.volume a b :=
    hdensity_cont.intervalIntegrable
  -- Rewrite the goal using hint_eq
  have goal_eq : (fun s : ℝ => ∫ t in Set.Icc 0 (s.toNNReal : ℝ), davisSegmentResetOccupationDensity S hflow g z t) =
      (fun s : ℝ => ∫ t in (0)..(s.toNNReal : ℝ), davisSegmentResetOccupationDensity S hflow g z t) := by
    ext s
    exact hint_eq ⟨s.toNNReal, NNReal.coe_nonneg _⟩
  rw [goal_eq]
  -- Use continuity of the interval integral primitive composed with toNNReal
  have hprim : Continuous (fun x : ℝ => ∫ t in (0 : ℝ)..x, davisSegmentResetOccupationDensity S hflow g z t) :=
    intervalIntegral.continuous_primitive hint_int 0
  exact hprim.comp (NNReal.continuous_coe.comp hnnreal_cont)

/-! ## The truncated one-segment compensation identity -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Hazard average of the partial occupation compensator, plus its
survivor-weighted endpoint value, is the one-segment expected reset
compensator. -/
theorem integral_hazardDensity_mul_resetOccupationCompensator_add_survivor
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (z : DavisState Q n) (u : ℝ≥0) :
    (∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          davisSegmentResetOccupationCompensator S hflow g z s.toNNReal) +
        davisSegmentSurvivor S hflow z u *
          davisSegmentResetOccupationCompensator S hflow g z u =
      davisSegmentExpectedResetCompensator S hflow g z u := by
  -- Map to the generic identity: lam = totalIntensity, d = occupation density
  let lam : ℝ → ℝ := fun s => S.totalIntensity (S.davisFlow hflow s.toNNReal z)
  let d : ℝ → ℝ := fun s => S.totalIntensity (S.davisFlow hflow s.toNNReal z) *
      davisExpectedResetIncrement S g (S.davisFlow hflow s.toNNReal z)
  -- Continuity of lam from DavisHazardContinuousAlongFlow
  have hlam_cont : Continuous lam := hcont z
  -- Continuity of the occupation density
  have hdensity_cont : Continuous (fun s => davisSegmentResetOccupationDensity S hflow g z s) :=
    hgcont z
  have hd_cont : Continuous d := hdensity_cont
  -- Duration u is nonnegative
  have hu : 0 ≤ (u : ℝ) := NNReal.coe_nonneg u
  -- Key lemma: inside [0, u], s.toNNReal = s
  have hnnreal_eq : ∀ s ∈ Set.Icc (0 : ℝ) (u : ℝ), (s.toNNReal : ℝ) = s := by
    intro s hs
    simp [Real.toNNReal_of_nonneg hs.1]
  -- Hazard density = lam * survivor
  have hdensity_eq : ∀ s : ℝ, davisSegmentHazardDensity S hflow z s =
      lam s * Real.exp (-(∫ r in Set.Icc (0 : ℝ) (s.toNNReal : ℝ), lam r)) := by
    intro s
    unfold davisSegmentHazardDensity davisIntegratedHazard
    simp only [lam]
  -- Survivor = exp(-integrated hazard)
  have hsurvivor : davisSegmentSurvivor S hflow z u =
      Real.exp (-(∫ r in Set.Icc (0 : ℝ) (u : ℝ), lam r)) := by
    unfold davisSegmentSurvivor davisIntegratedHazard
    rfl
  -- Reset occupation compensator at s = ∫ d from 0 to s.toNNReal
  have hcomp_eq : ∀ s ∈ Set.Icc (0 : ℝ) (u : ℝ),
      davisSegmentResetOccupationCompensator S hflow g z s.toNNReal =
      ∫ r in Set.Icc (0 : ℝ) (s : ℝ), d r := by
    intro s hs
    have hs_nnreal : (s.toNNReal : ℝ) = s := hnnreal_eq s hs
    unfold davisSegmentResetOccupationCompensator
    rw [hs_nnreal]
    simp only [davisSegmentResetOccupationDensity, d]
  -- Expected compensator = ∫ survivor * d
  have hexpcomp : davisSegmentExpectedResetCompensator S hflow g z u =
      ∫ s in Set.Icc (0 : ℝ) (u : ℝ), Real.exp (-(∫ r in Set.Icc (0 : ℝ) (s.toNNReal : ℝ), lam r)) * d s := by
    unfold davisSegmentExpectedResetCompensator
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro s _
    exact davisSegmentExpectedResetDensity_eq_survivor_mul_occupation S hflow g z s
  -- Reset occupation compensator at u = ∫ d from 0 to u
  have hcomp_u : davisSegmentResetOccupationCompensator S hflow g z u =
      ∫ r in Set.Icc (0 : ℝ) (u : ℝ), d r := by
    unfold davisSegmentResetOccupationCompensator
    simp only [davisSegmentResetOccupationDensity, d]
  -- Convert the LHS integrand
  have hlhs_eq : ∀ s ∈ Set.Icc (0 : ℝ) (u : ℝ),
      davisSegmentHazardDensity S hflow z s * davisSegmentResetOccupationCompensator S hflow g z s.toNNReal =
      lam s * Real.exp (-(∫ r in Set.Icc (0 : ℝ) (s : ℝ), lam r)) * (∫ r in Set.Icc (0 : ℝ) (s : ℝ), d r) := by
    intro s hs
    rw [hdensity_eq s, hcomp_eq s hs]
    simp [hnnreal_eq s hs]
  -- Rewrite the LHS integral
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hlhs_eq]
  -- Rewrite the product term
  rw [hsurvivor, hcomp_u, hexpcomp]
  -- Convert RHS integrand: s.toNNReal = s for s ∈ [0, u]
  have hrhs_eq : ∀ s ∈ Set.Icc (0 : ℝ) (u : ℝ),
      Real.exp (-(∫ r in Set.Icc (0 : ℝ) (s.toNNReal : ℝ), lam r)) * d s =
      Real.exp (-(∫ r in Set.Icc (0 : ℝ) s, lam r)) * d s := by
    intro s hs
    simp [hnnreal_eq s hs]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hrhs_eq]
  -- Apply the generic identity
  rw [eq_comm]
  change ∫ s in Set.Icc (0 : ℝ) (u : ℝ), Real.exp (-∫ r in Set.Icc (0 : ℝ) s, lam r) * d s =
    (∫ s in Set.Icc (0 : ℝ) (u : ℝ), lam s * Real.exp (-∫ r in Set.Icc (0 : ℝ) s, lam r) * ∫ r in Set.Icc (0 : ℝ) s, d r) +
      Real.exp (-∫ r in Set.Icc (0 : ℝ) (u : ℝ), lam r) * ∫ r in Set.Icc (0 : ℝ) (u : ℝ), d r
  exact (integral_hazard_mul_primitive_Icc lam d hlam_cont hd_cont (u : ℝ) hu).symm

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The survivor factor of a segment is continuous in elapsed time. -/
theorem continuous_davisSegmentSurvivorProfile
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow) (z : DavisState Q n) :
    Continuous (fun s : ℝ =>
      Real.exp (-davisIntegratedHazard S hflow z s.toNNReal)) := by
  refine Continuous.rexp ?_
  refine Continuous.neg ?_
  show Continuous (davisIntegratedHazard S hflow z ∘ Real.toNNReal)
  apply Continuous.comp
  · have heq : davisIntegratedHazard S hflow z =
        fun u : ℝ≥0 => ∫ s in (0)..(u : ℝ),
          S.totalIntensity (S.davisFlow hflow s.toNNReal z) := by
      ext u
      unfold davisIntegratedHazard
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      erw [← intervalIntegral.integral_of_le u.2]
      rfl
    rw [heq]
    have hcont_prim : Continuous (fun b : ℝ => ∫ s in (0)..b,
        S.totalIntensity (S.davisFlow hflow s.toNNReal z)) := by
      apply intervalIntegral.continuous_primitive
      intro a b
      exact (hcont z).intervalIntegrable a b
    exact hcont_prim.comp (by continuity : Continuous (↑· : ℝ≥0 → ℝ))
  · exact continuous_real_toNNReal

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The expected reset density of a segment is continuous in elapsed time. -/
theorem continuous_davisSegmentExpectedResetDensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (z : DavisState Q n) :
    Continuous (fun s : ℝ =>
      davisSegmentExpectedResetDensity S hflow g z s) := by
  unfold davisSegmentExpectedResetDensity
  have heq : ∀ s : ℝ,
      davisSegmentHazardDensity S hflow z s * davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) =
      Real.exp (-davisIntegratedHazard S hflow z s.toNNReal) *
        davisSegmentResetOccupationDensity S hflow g z s := by
    intro s
    exact davisSegmentExpectedResetDensity_eq_survivor_mul_occupation S hflow g z s
  simp_rw [heq]
  apply Continuous.mul
  · -- Survivor factor is continuous
    refine Continuous.rexp ?_
    refine Continuous.neg ?_
    show Continuous (S.davisIntegratedHazard hflow z ∘ Real.toNNReal)
    apply Continuous.comp
    · have heq' : S.davisIntegratedHazard hflow z =
          fun u : ℝ≥0 => ∫ s in (0)..(u : ℝ),
            S.totalIntensity (S.davisFlow hflow s.toNNReal z) := by
        ext u
        unfold davisIntegratedHazard
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
        erw [← intervalIntegral.integral_of_le u.2]
        rfl
      rw [heq']
      -- First derive continuity of totalIntensity ∘ davisFlow from hcont
      -- We know: hazardDensity = totalIntensity * exp(-integratedHazard)
      -- So: totalIntensity = hazardDensity * exp(integratedHazard)
      -- But we need to be careful about the circular dependency...
      -- Key insight: on compact intervals, continuous functions are integrable
      -- We'll prove integrability using the hazard density which we know is continuous
      -- Need to show: Continuous (fun u : ℝ≥0 => ∫ s in 0..u, totalIntensity(flow(s)))
      -- First show integrability on any interval [a, b] in ℝ
      have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => S.totalIntensity (S.davisFlow hflow s.toNNReal z)) MeasureTheory.volume a b := by
        intro a b
        exact (hcont z).intervalIntegrable a b
      exact (intervalIntegral.continuous_primitive hint 0).comp continuous_subtype_val
    · exact continuous_real_toNNReal
  · exact hgcont z

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The hazard average of the normalized expected reset increment is the
one-segment expected reset compensator. -/
theorem integral_hazardDensity_mul_expectedResetIncrement
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (u : ℝ≥0) :
    (∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z)) =
      davisSegmentExpectedResetCompensator S hflow g z u := rfl

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The truncated one-segment compensation identity: the hazard average of the
centered reset increment accumulated strictly inside the segment equals the
survivor-weighted partial compensator carried by the segment still active at
the truncation time. -/
theorem integral_hazardDensity_mul_centered_resetIncrement
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (z : DavisState Q n) (u : ℝ≥0) :
    (∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) =
      davisSegmentSurvivor S hflow z u *
        davisSegmentResetOccupationCompensator S hflow g z u := by
  -- Use integral_hazardDensity_mul_expectedResetIncrement: ∫ hazard * expected = expectedResetCompensator
  have h1 := integral_hazardDensity_mul_expectedResetIncrement S hflow g z u
  -- Use integral_hazardDensity_mul_resetOccupationCompensator_add_survivor:
  --   ∫ hazard * compensator + survivor * compensator = expectedResetCompensator
  have h2 := integral_hazardDensity_mul_resetOccupationCompensator_add_survivor
    S hflow hcont g hgcont z u
  -- From h2: expectedResetCompensator - ∫ hazard * compensator = survivor * compensator
  have h3 : S.davisSegmentExpectedResetCompensator hflow g z u -
      ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          davisSegmentResetOccupationCompensator S hflow g z s.toNNReal =
      davisSegmentSurvivor S hflow z u *
        davisSegmentResetOccupationCompensator S hflow g z u := by linarith
  -- Show the integral equals the difference
  have h4 : ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal) =
      (∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z)) -
      (∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          davisSegmentResetOccupationCompensator S hflow g z s.toNNReal) := by
    have heq : ∀ s ∈ Set.Icc (0 : ℝ) (u : ℝ), davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal) =
        davisSegmentHazardDensity S hflow z s *
          davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
        davisSegmentHazardDensity S hflow z s *
          davisSegmentResetOccupationCompensator S hflow g z s.toNNReal := by
      intro s _
      ring_nf
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc heq]
    -- Prove integrability from continuity
    have hcont1 : Continuous (fun s : ℝ => davisSegmentHazardDensity S hflow z s *
          davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z)) :=
      continuous_davisSegmentExpectedResetDensity S hflow hcont g hgcont z
    have hcont2 : Continuous (fun s : ℝ => davisSegmentHazardDensity S hflow z s *
          davisSegmentResetOccupationCompensator S hflow g z s.toNNReal) := by
      apply Continuous.mul
      · exact continuous_davisSegmentHazardDensity S hflow hcont z
      · exact continuous_davisSegmentResetOccupationCompensator S hflow g hgcont z
    rw [← MeasureTheory.integral_sub]
    exacts [hcont1.integrableOn_Icc, hcont2.integrableOn_Icc]
  rw [h4, integral_hazardDensity_mul_expectedResetIncrement S hflow g z u]
  exact h3

/-! ## The mean of the single-segment contribution -/

/-- Hazard average, truncated at elapsed time `u`, of the single-segment
contribution to the occupation-centered approximation: the completed-segment
part (realized reset centered by its sampled compensator, averaged over the
holding-time hazard density) minus the survivor-weighted active-segment
partial compensator. -/
def davisSegmentContributionMean (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (z : DavisState Q n) (u : ℝ≥0) : ℝ :=
  (∫ s in Set.Icc (0 : ℝ) (u : ℝ),
      davisSegmentHazardDensity S hflow z s *
        (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
          davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) -
    davisSegmentSurvivor S hflow z u *
      davisSegmentResetOccupationCompensator S hflow g z u

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The single-segment contribution has zero hazard average at every
truncation time: the deterministic core of the one-segment martingale
property. -/
theorem davisSegmentContributionMean_eq_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (z : DavisState Q n) (u : ℝ≥0) :
    davisSegmentContributionMean S hflow g z u = 0 := by
  rw [davisSegmentContributionMean,
    integral_hazardDensity_mul_centered_resetIncrement S hflow hcont g hgcont z u,
    sub_self]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Increment form: between two truncation times the hazard average of the
centered reset increment is exactly the increment of the survivor-weighted
partial compensator.  This is the deterministic statement that feeds the
conditional martingale step. -/
theorem integral_Icc_hazardDensity_mul_centered_resetIncrement_sub
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (z : DavisState Q n) (u v : ℝ≥0) (huv : u ≤ v) :
    (∫ s in Set.Icc (u : ℝ) (v : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) =
      davisSegmentSurvivor S hflow z v *
          davisSegmentResetOccupationCompensator S hflow g z v -
        davisSegmentSurvivor S hflow z u *
          davisSegmentResetOccupationCompensator S hflow g z u := by
  have huv' : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
  have hu_pos : (0 : ℝ) ≤ (u : ℝ) := by simp
  -- Get the identities for times u and v
  have hu_eq := integral_hazardDensity_mul_centered_resetIncrement S hflow hcont g hgcont z u
  have hv_eq := integral_hazardDensity_mul_centered_resetIncrement S hflow hcont g hgcont z v
  -- Split the integral: ∫[0,v] = ∫[0,u] + ∫[u,v]
  have h_split : (∫ s in Set.Icc (0 : ℝ) (v : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) =
      (∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) +
      (∫ s in Set.Icc (u : ℝ) (v : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by simp : (0 : ℝ) ≤ v),
        ← intervalIntegral.integral_of_le hu_pos,
        ← intervalIntegral.integral_of_le huv']
    -- The integrand equals expectedDensity - hazardDensity * compensator
    have h_integrand_eq : ∀ s : ℝ,
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal) =
        davisSegmentExpectedResetDensity S hflow g z s -
          davisSegmentHazardDensity S hflow z s *
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal := by
      intro s
      simp [davisSegmentExpectedResetDensity]
      ring
    -- Continuity of the integrand
    have hcont_sub : Continuous (fun x =>
        davisSegmentExpectedResetDensity S hflow g z x -
          davisSegmentHazardDensity S hflow z x *
            davisSegmentResetOccupationCompensator S hflow g z x.toNNReal) :=
      Continuous.sub (continuous_davisSegmentExpectedResetDensity S hflow hcont g hgcont z)
        (Continuous.mul (continuous_davisSegmentHazardDensity S hflow hcont z)
          (continuous_davisSegmentResetOccupationCompensator S hflow g hgcont z))
    -- Rewrite the integrals using the integrand equality
    simp_rw [h_integrand_eq]
    rw [intervalIntegral.integral_add_adjacent_intervals]
    all_goals exact Continuous.intervalIntegrable hcont_sub _ _
  have h_split' : (∫ s in Set.Icc (u : ℝ) (v : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) =
      (∫ s in Set.Icc (0 : ℝ) (v : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) -
      (∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s *
          (davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z) -
            davisSegmentResetOccupationCompensator S hflow g z s.toNNReal)) := by
    linarith
  rw [hv_eq, hu_eq] at h_split'
  exact h_split'

end SHS
