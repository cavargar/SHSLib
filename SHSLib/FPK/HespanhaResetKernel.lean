/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The reset kernel of a Hespanha SHS as a Markov kernel

`SHS.resetKernel` (in `SHSLib/FPK/HespanhaBridge.lean`) is the measure

  `K(x, ·) = Σ_ℓ (λ_ℓ(x) / λ(x)) δ_{φ_ℓ(x)}`,

Eq. (31) of Example 18 of Bect (2010).  The weak formulation of the generalized FPK
equation (`GSHS.FPKData`) requires it as a *kernel*, i.e. together with the
measurability of `x ↦ K(x, Γ)`.  This file provides that packaging, at a fixed value of
the clock coordinate: `SHS.resetKernelAt` is a Markov kernel on the SHS state space
`Q × ℝⁿ`.
-/
import SHSLib.FPK.HespanhaBridge

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] {n m : ℕ}

/-- The individual jump intensities of an SHS are measurable in the state, at a fixed
time. -/
theorem measurable_intensity_state (S : SHS Q n m) [S.IntensitiesMeasurable] (ℓ : Fin m)
    (t : ℝ) :
    Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => S.intensity ℓ z.1 z.2 t :=
  (SHS.IntensitiesMeasurable.measurable ℓ).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

/-- The total jump intensity `λ = Σ_ℓ λ_ℓ` of an SHS is measurable in the state, at a
fixed time. -/
theorem measurable_levyTotalIntensity (S : SHS Q n m) [S.IntensitiesMeasurable] (t : ℝ) :
    Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => S.levyTotalIntensity z.1 z.2 t := by
  simpa only [levyTotalIntensity] using
    Finset.measurable_sum Finset.univ fun ℓ _ => S.measurable_intensity_state ℓ t

/-- Measurability of `z ↦ K(z, Γ)` for the reset kernel of an SHS at a fixed time. -/
theorem measurable_resetKernel_coe (S : SHS Q n m) [S.IntensitiesMeasurable] (t : ℝ)
    (hphi : ∀ ℓ, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => S.phi ℓ z.1 z.2 t) :
    Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => S.resetKernel z.1 z.2 t := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hlam : Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      S.levyTotalIntensity z.1 z.2 t := S.measurable_levyTotalIntensity t
  have hset : MeasurableSet {z : Q × EuclideanSpace ℝ (Fin n) | 0 < S.levyTotalIntensity z.1 z.2 t} :=
    measurableSet_lt measurable_const hlam
  have hind : ∀ g : Q × EuclideanSpace ℝ (Fin n) → Q × EuclideanSpace ℝ (Fin n),
      Measurable g → Measurable fun z => (Measure.dirac (g z)) A := by
    intro g hg
    have : (fun z => (Measure.dirac (g z)) A) = fun z => A.indicator (fun _ => (1 : ℝ≥0∞)) (g z) :=
      funext fun z => Measure.dirac_apply' _ hA
    rw [this]
    exact (measurable_one.indicator hA).comp hg
  have hpos : Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      (∑ ℓ : Fin m, (ENNReal.ofReal (S.intensity ℓ z.1 z.2 t / S.levyTotalIntensity z.1 z.2 t)) •
        Measure.dirac (S.phi ℓ z.1 z.2 t)) A := by
    have hfun : (fun z : Q × EuclideanSpace ℝ (Fin n) =>
        (∑ ℓ : Fin m, (ENNReal.ofReal (S.intensity ℓ z.1 z.2 t / S.levyTotalIntensity z.1 z.2 t)) •
          Measure.dirac (S.phi ℓ z.1 z.2 t)) A)
        = fun z => ∑ ℓ : Fin m,
            ENNReal.ofReal (S.intensity ℓ z.1 z.2 t / S.levyTotalIntensity z.1 z.2 t) *
              (Measure.dirac (S.phi ℓ z.1 z.2 t)) A := by
      funext z
      rw [Measure.finset_sum_apply]
      exact Finset.sum_congr rfl fun ℓ _ => by simp
    rw [hfun]
    refine Finset.measurable_sum Finset.univ fun ℓ _ => ?_
    exact (((S.measurable_intensity_state ℓ t).div hlam).ennreal_ofReal).mul
      (hind _ (hphi ℓ))
  have hneg : Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => (Measure.dirac z) A :=
    hind id measurable_id
  have hsplit : (fun z : Q × EuclideanSpace ℝ (Fin n) => (S.resetKernel z.1 z.2 t) A)
      = fun z => if 0 < S.levyTotalIntensity z.1 z.2 t then
          (∑ ℓ : Fin m, (ENNReal.ofReal (S.intensity ℓ z.1 z.2 t / S.levyTotalIntensity z.1 z.2 t)) •
            Measure.dirac (S.phi ℓ z.1 z.2 t)) A
        else (Measure.dirac z) A := by
    funext z
    by_cases hz : 0 < S.levyTotalIntensity z.1 z.2 t
    · simp [resetKernel, hz]
    · simp [resetKernel, hz]
  rw [hsplit]
  exact Measurable.ite hset hpos hneg

/-- The reset kernel of an SHS at a fixed value of the clock coordinate, packaged as a
kernel on the state space `Q × ℝⁿ` (Eq. (31) of Bect (2010)). -/
def resetKernelAt (S : SHS Q n m) [S.IntensitiesMeasurable] (t : ℝ)
    (hphi : ∀ ℓ, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => S.phi ℓ z.1 z.2 t) :
    Kernel (Q × EuclideanSpace ℝ (Fin n)) (Q × EuclideanSpace ℝ (Fin n)) where
  toFun z := S.resetKernel z.1 z.2 t
  measurable' := S.measurable_resetKernel_coe t hphi

@[simp] theorem resetKernelAt_apply (S : SHS Q n m) [S.IntensitiesMeasurable] (t : ℝ)
    (hphi : ∀ ℓ, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => S.phi ℓ z.1 z.2 t)
    (z : Q × EuclideanSpace ℝ (Fin n)) :
    S.resetKernelAt t hphi z = S.resetKernel z.1 z.2 t := rfl

/-- The reset kernel of an SHS is a Markov kernel. -/
instance isMarkovKernel_resetKernelAt (S : SHS Q n m) [S.IntensitiesMeasurable] (t : ℝ)
    (hphi : ∀ ℓ, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => S.phi ℓ z.1 z.2 t) :
    IsMarkovKernel (S.resetKernelAt t hphi) :=
  ⟨fun z => S.resetKernel_isProbabilityMeasure z.1 z.2 t⟩

end SHS
