import SHSLib.Core.DavisOneSegmentTruncatedCompensation
import SHSLib.Core.DavisConditionalHoldingWeighted

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Riemann approximation of a hazard average over an age window

The conditional law of the *completed* part of the one-segment contribution
compares an integral against the law of the holding time with an integral
against the hazard density.  The bridge between the two is a Riemann-sum
estimate: over a window of ages split into `M` equal cells, the hazard average
of a Lipschitz profile differs from the corresponding step-function sum by at
most the Lipschitz constant times the mesh.

Two ingredients make the estimate clean.  First, the hazard density integrates
over an age window to the *loss of the survivor factor* across that window —
exactly the mass the window law of the holding time assigns to it.  Second, on
each cell the profile deviates from its left endpoint value by at most
`L · mesh`, so the error committed on the cell is at most `L · mesh` times the
mass of the cell, and the masses of the cells telescope.

The resulting bound, `L · mesh · (Sur(u) − Sur(v)) ≤ L · mesh`, tends to zero
as the mesh is refined; that is what turns the window law into the density form
of the conditional holding-time law.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Splitting an integral at an intermediate age -/

/-- A continuous integrand splits at an intermediate point. -/
theorem integral_Icc_split_of_continuous (f : ℝ → ℝ) (hf : Continuous f)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    ∫ s in Set.Icc a c, f s =
      (∫ s in Set.Icc a b, f s) + ∫ s in Set.Icc b c, f s := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_trans hab hbc),
    ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hbc]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable a b) (hf.intervalIntegrable b c)).symm

/-! ## The window mass of the hazard density -/

/-- **The window mass of the hazard density.**  Over an age window the hazard
density integrates to the loss of the survivor factor across the window. -/
theorem integral_Icc_davisSegmentHazardDensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (z : DavisState Q n) (u v : ℝ≥0) (huv : u ≤ v) :
    ∫ s in Set.Icc (u : ℝ) (v : ℝ),
        davisSegmentHazardDensity S hflow z s =
      davisSegmentSurvivor S hflow z u - davisSegmentSurvivor S hflow z v := by
  have huv' : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
  have h0u : (0 : ℝ) ≤ (u : ℝ) := u.coe_nonneg
  have hsplit := integral_Icc_split_of_continuous
    (davisSegmentHazardDensity S hflow z)
    (continuous_davisSegmentHazardDensity S hflow hcont z) 0 u v h0u huv'
  have hu := integral_davisSegmentHazardDensity S hflow hcont z u
  have hv := integral_davisSegmentHazardDensity S hflow hcont z v
  rw [hu, hv] at hsplit
  linarith

/-! ## The one-cell estimate -/

/-- **The one-cell estimate.**  On a single age cell the hazard average of a
Lipschitz profile differs from the left endpoint value times the mass of the
cell by at most the Lipschitz constant times the length of the cell times that
mass. -/
theorem abs_integral_Icc_hazardDensity_mul_sub_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (z : DavisState Q n) (phi : ℝ → ℝ) (hphi : Continuous phi)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ r r' : ℝ, |phi r - phi r'| ≤ L * |r - r'|)
    (a b : ℝ≥0) (hab : a ≤ b) :
    |(∫ s in Set.Icc (a : ℝ) (b : ℝ),
          davisSegmentHazardDensity S hflow z s * phi s) -
        phi a * (davisSegmentSurvivor S hflow z a -
          davisSegmentSurvivor S hflow z b)| ≤
      L * ((b : ℝ) - (a : ℝ)) *
        (davisSegmentSurvivor S hflow z a -
          davisSegmentSurvivor S hflow z b) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hdens_cont : Continuous (davisSegmentHazardDensity S hflow z) :=
    continuous_davisSegmentHazardDensity S hflow hcont z
  have hdens_nonneg : ∀ s : ℝ, 0 ≤ davisSegmentHazardDensity S hflow z s := by
    intro s
    unfold davisSegmentHazardDensity
    exact mul_nonneg (totalIntensity_nonneg S _) (Real.exp_nonneg _)
  have hmass := integral_Icc_davisSegmentHazardDensity S hflow hcont z a b hab
  -- the constant term as an integral
  have hconst : phi a * (davisSegmentSurvivor S hflow z a -
      davisSegmentSurvivor S hflow z b) =
      ∫ s in Set.Icc (a : ℝ) (b : ℝ),
        davisSegmentHazardDensity S hflow z s * phi a := by
    rw [← hmass, MeasureTheory.integral_mul_const]
    ring
  have hfint : IntegrableOn (fun s => davisSegmentHazardDensity S hflow z s *
      phi s - davisSegmentHazardDensity S hflow z s * phi a)
      (Set.Icc (a : ℝ) (b : ℝ)) :=
    ((hdens_cont.mul hphi).sub
      (hdens_cont.mul continuous_const)).continuousOn.integrableOn_compact
        isCompact_Icc
  have hint : IntegrableOn
      (fun s => L * ((b : ℝ) - (a : ℝ)) *
        davisSegmentHazardDensity S hflow z s) (Set.Icc (a : ℝ) (b : ℝ)) :=
    (continuous_const.mul hdens_cont).continuousOn.integrableOn_compact
      isCompact_Icc
  have hbound : ∀ s ∈ Set.Icc (a : ℝ) (b : ℝ),
      |davisSegmentHazardDensity S hflow z s * phi s -
        davisSegmentHazardDensity S hflow z s * phi a| ≤
      L * ((b : ℝ) - (a : ℝ)) * davisSegmentHazardDensity S hflow z s := by
    intro s hs
    rw [← mul_sub, abs_mul, abs_of_nonneg (hdens_nonneg s)]
    have h1 : |phi s - phi a| ≤ L * ((b : ℝ) - (a : ℝ)) := by
      refine le_trans (hlip s a) ?_
      refine mul_le_mul_of_nonneg_left ?_ hL
      rw [abs_of_nonneg (by linarith [hs.1] : (0:ℝ) ≤ s - (a : ℝ))]
      linarith [hs.2]
    calc davisSegmentHazardDensity S hflow z s * |phi s - phi a|
        ≤ davisSegmentHazardDensity S hflow z s * (L * ((b:ℝ) - (a:ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (hdens_nonneg s)
      _ = L * ((b : ℝ) - (a : ℝ)) * davisSegmentHazardDensity S hflow z s := by
          ring
  have hcomb : (∫ s in Set.Icc (a : ℝ) (b : ℝ),
        davisSegmentHazardDensity S hflow z s * phi s) -
      (∫ s in Set.Icc (a : ℝ) (b : ℝ),
        davisSegmentHazardDensity S hflow z s * phi a) =
      ∫ s in Set.Icc (a : ℝ) (b : ℝ),
        (davisSegmentHazardDensity S hflow z s * phi s -
          davisSegmentHazardDensity S hflow z s * phi a) :=
    (integral_sub
      ((hdens_cont.mul hphi).continuousOn.integrableOn_compact isCompact_Icc)
      ((hdens_cont.mul continuous_const).continuousOn.integrableOn_compact
        isCompact_Icc)).symm
  rw [hconst, hcomb]
  calc |∫ s in Set.Icc (a : ℝ) (b : ℝ),
          (davisSegmentHazardDensity S hflow z s * phi s -
            davisSegmentHazardDensity S hflow z s * phi a)|
      ≤ ∫ s in Set.Icc (a : ℝ) (b : ℝ),
          |davisSegmentHazardDensity S hflow z s * phi s -
            davisSegmentHazardDensity S hflow z s * phi a| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Icc (a : ℝ) (b : ℝ)))
            (f := fun s => davisSegmentHazardDensity S hflow z s * phi s -
              davisSegmentHazardDensity S hflow z s * phi a)
    _ ≤ ∫ s in Set.Icc (a : ℝ) (b : ℝ),
          L * ((b : ℝ) - (a : ℝ)) *
            davisSegmentHazardDensity S hflow z s :=
        setIntegral_mono_on hfint.abs hint measurableSet_Icc hbound
    _ = L * ((b : ℝ) - (a : ℝ)) *
          (davisSegmentSurvivor S hflow z a -
            davisSegmentSurvivor S hflow z b) := by
        rw [integral_const_mul, hmass]

/-! ## The Riemann sum over a uniform grid -/

/-- The `i`-th point of the uniform age grid of mesh `delta` starting at `u`. -/
def davisHazardGridPoint (u delta : ℝ≥0) (i : ℕ) : ℝ≥0 :=
  u + (i : ℝ≥0) * delta

@[simp] theorem davisHazardGridPoint_zero (u delta : ℝ≥0) :
    davisHazardGridPoint u delta 0 = u := by
  simp [davisHazardGridPoint]

theorem davisHazardGridPoint_mono (u delta : ℝ≥0) {i j : ℕ} (hij : i ≤ j) :
    davisHazardGridPoint u delta i ≤ davisHazardGridPoint u delta j := by
  unfold davisHazardGridPoint
  gcongr

theorem davisHazardGridPoint_succ_sub (u delta : ℝ≥0) (i : ℕ) :
    ((davisHazardGridPoint u delta (i + 1) : ℝ≥0) : ℝ) -
      ((davisHazardGridPoint u delta i : ℝ≥0) : ℝ) = (delta : ℝ) := by
  unfold davisHazardGridPoint
  push_cast
  ring

/-- The step-function sum approximating the hazard average of a profile over
the window of `M` cells of mesh `delta` starting at age `u`: each cell
contributes the value of the profile at its left endpoint times the mass the
holding time assigns to the cell. -/
def davisHazardRiemannSum (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (z : DavisState Q n) (phi : ℝ → ℝ) (u delta : ℝ≥0) (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M,
    phi ((davisHazardGridPoint u delta i : ℝ≥0) : ℝ) *
      (davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta i) -
        davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta (i + 1)))

/-- **The Riemann estimate.**  Over a uniform grid the hazard average of a
Lipschitz profile differs from its step-function sum by at most the Lipschitz
constant times the mesh times the total mass of the window. -/
theorem abs_integral_Icc_hazardDensity_mul_sub_riemannSum_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (z : DavisState Q n) (phi : ℝ → ℝ) (hphi : Continuous phi)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ r r' : ℝ, |phi r - phi r'| ≤ L * |r - r'|)
    (u delta : ℝ≥0) (M : ℕ) :
    |(∫ s in Set.Icc (u : ℝ)
          ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ),
          davisSegmentHazardDensity S hflow z s * phi s) -
        davisHazardRiemannSum S hflow z phi u delta M| ≤
      L * (delta : ℝ) *
        (davisSegmentSurvivor S hflow z u -
          davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta M)) := by
  induction M with
  | zero => simp [davisHazardRiemannSum]
  | succ M ih =>
    have hua : u ≤ davisHazardGridPoint u delta M := by
      simpa using davisHazardGridPoint_mono u delta (Nat.zero_le M)
    have hab : davisHazardGridPoint u delta M ≤
        davisHazardGridPoint u delta (M + 1) :=
      davisHazardGridPoint_mono u delta (Nat.le_succ M)
    have hsplit := integral_Icc_split_of_continuous
      (fun s => davisSegmentHazardDensity S hflow z s * phi s)
      ((continuous_davisSegmentHazardDensity S hflow hcont z).mul hphi)
      (u : ℝ) ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ)
      ((davisHazardGridPoint u delta (M + 1) : ℝ≥0) : ℝ)
      (by exact_mod_cast hua) (by exact_mod_cast hab)
    have hcell := abs_integral_Icc_hazardDensity_mul_sub_le S hflow hcont z phi
      hphi L hL hlip (davisHazardGridPoint u delta M)
      (davisHazardGridPoint u delta (M + 1)) hab
    rw [davisHazardGridPoint_succ_sub] at hcell
    have hsum : davisHazardRiemannSum S hflow z phi u delta (M + 1) =
        davisHazardRiemannSum S hflow z phi u delta M +
          phi ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ) *
            (davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta M) -
              davisSegmentSurvivor S hflow z
                (davisHazardGridPoint u delta (M + 1))) := by
      rw [davisHazardRiemannSum, Finset.sum_range_succ, ← davisHazardRiemannSum]
    rw [hsplit, hsum]
    set I1 : ℝ := ∫ s in Set.Icc (u : ℝ)
      ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ),
      davisSegmentHazardDensity S hflow z s * phi s with hI1
    set I2 : ℝ := ∫ s in Set.Icc ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ)
      ((davisHazardGridPoint u delta (M + 1) : ℝ≥0) : ℝ),
      davisSegmentHazardDensity S hflow z s * phi s with hI2
    set R1 : ℝ := davisHazardRiemannSum S hflow z phi u delta M with hR1
    set R2 : ℝ := phi ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ) *
      (davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta M) -
        davisSegmentSurvivor S hflow z
          (davisHazardGridPoint u delta (M + 1))) with hR2
    have htri : |I1 + I2 - (R1 + R2)| ≤ |I1 - R1| + |I2 - R2| := by
      calc |I1 + I2 - (R1 + R2)| = |(I1 - R1) + (I2 - R2)| := by ring_nf
        _ ≤ |I1 - R1| + |I2 - R2| := abs_add_le _ _
    refine le_trans htri ?_
    have hstep : L * (delta : ℝ) *
        (davisSegmentSurvivor S hflow z u -
          davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta M)) +
        L * (delta : ℝ) *
          (davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta M) -
            davisSegmentSurvivor S hflow z
              (davisHazardGridPoint u delta (M + 1))) =
        L * (delta : ℝ) *
          (davisSegmentSurvivor S hflow z u -
            davisSegmentSurvivor S hflow z
              (davisHazardGridPoint u delta (M + 1))) := by ring
    rw [← hstep]
    exact add_le_add ih hcell

/-- The Riemann estimate in its crude form: the error is at most the Lipschitz
constant times the mesh. -/
theorem abs_integral_Icc_hazardDensity_mul_sub_riemannSum_le'
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (z : DavisState Q n) (phi : ℝ → ℝ) (hphi : Continuous phi)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ r r' : ℝ, |phi r - phi r'| ≤ L * |r - r'|)
    (u delta : ℝ≥0) (M : ℕ) :
    |(∫ s in Set.Icc (u : ℝ)
          ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ),
          davisSegmentHazardDensity S hflow z s * phi s) -
        davisHazardRiemannSum S hflow z phi u delta M| ≤
      L * (delta : ℝ) := by
  refine le_trans (abs_integral_Icc_hazardDensity_mul_sub_riemannSum_le S hflow
    hcont z phi hphi L hL hlip u delta M) ?_
  have h1 : davisSegmentSurvivor S hflow z u -
      davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta M) ≤ 1 := by
    have h2 := davisSegmentSurvivor_le_one S hflow z u
    have h3 := davisSegmentSurvivor_pos S hflow z
      (davisHazardGridPoint u delta M)
    linarith
  have h0 : 0 ≤ L * (delta : ℝ) := mul_nonneg hL delta.coe_nonneg
  calc L * (delta : ℝ) * (davisSegmentSurvivor S hflow z u -
        davisSegmentSurvivor S hflow z (davisHazardGridPoint u delta M))
      ≤ L * (delta : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = L * (delta : ℝ) := mul_one _

end SHS
