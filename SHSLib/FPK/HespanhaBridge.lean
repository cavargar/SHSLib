/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hespanha SHS as a GSHS with spontaneous jumps (Example 18 of Bect, 2010)

Bect's framework describes the jumps of a GSHS through a Lévy system (Eqs. (5)–(6)):
a stochastic intensity `λ` and a Markov reset kernel `K`.  A stochastic hybrid system
in the sense of Hespanha — the model formalized in `SHSLib.Core.Basic` — has `m`
transitions with individual intensities `λ_ℓ` and reset maps `φ_ℓ`.  This file relates
the two descriptions:

* `SHS.levyTotalIntensity` is `λ = Σ_ℓ λ_ℓ`, the stochastic intensity of the Lévy system;
* `SHS.resetKernel` is the corresponding Markov reset kernel
  `K(x, ·) = Σ_ℓ (λ_ℓ / λ) δ_{φ_ℓ(x)}`, which is Eq. (31) of Example 18 with
  `π_ℓ = λ_ℓ / λ`;
* `SHS.extendedGenerator_eq_levy` rewrites the SHS extended generator of
  `SHSLib.Core.GeneratorDefs` in Bect's form, drift plus `λ (K − I)`;
* `SHS.integral_extendedGenerator_eq_levy` integrates this against the law `μ_t` of the
  state, producing exactly the two terms `μ_t(L₀ψ) + r_t(K − I)ψ` of the generalized
  Dynkin formula (13), with the mean jump intensity `r_t = λ μ_t` of Eq. (8).
-/
import SHSLib.Core.GeneratorDefs
import SHSLib.FPK.GeneralizedFPK

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The total jump intensity `λ = Σ_ℓ λ_ℓ` of an SHS: the stochastic intensity of the
Lévy system (6) of Bect (2010). -/
def levyTotalIntensity (S : SHS Q n m) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  ∑ ℓ : Fin m, S.intensity ℓ q x t

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
theorem levyTotalIntensity_nonneg (S : SHS Q n m) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) : 0 ≤ S.levyTotalIntensity q x t :=
  Finset.sum_nonneg fun ℓ _ => S.intensity_nonneg ℓ q x t

/-- The Markov reset kernel `K(x, ·) = Σ_ℓ (λ_ℓ/λ) δ_{φ_ℓ(x)}` of an SHS (Eq. (31)
of Example 18).  When the total intensity vanishes no jump can occur and the kernel is
set to `δ_x`, so that `K` is a Markov kernel at every point. -/
def resetKernel (S : SHS Q n m) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Measure (Q × EuclideanSpace ℝ (Fin n)) :=
  if 0 < S.levyTotalIntensity q x t then
    ∑ ℓ : Fin m, (ENNReal.ofReal (S.intensity ℓ q x t / S.levyTotalIntensity q x t)) •
      Measure.dirac (S.phi ℓ q x t)
  else Measure.dirac (q, x)

omit [MeasurableSingletonClass Q] in
/-- The reset kernel of an SHS is a probability measure at every point. -/
theorem resetKernel_isProbabilityMeasure (S : SHS Q n m) (q : Q)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    IsProbabilityMeasure (S.resetKernel q x t) := by
  classical
  by_cases hpos : 0 < S.levyTotalIntensity q x t
  · constructor
    rw [resetKernel, if_pos hpos]
    rw [Measure.finset_sum_apply]
    have hterm : ∀ ℓ : Fin m,
        ((ENNReal.ofReal (S.intensity ℓ q x t / S.levyTotalIntensity q x t)) •
          Measure.dirac (S.phi ℓ q x t)) univ
          = ENNReal.ofReal (S.intensity ℓ q x t / S.levyTotalIntensity q x t) := by
      intro ℓ
      simp
    simp only [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => by
      have := S.intensity_nonneg ℓ q x t
      positivity)]
    rw [← Finset.sum_div]
    have hsum : ∑ ℓ : Fin m, S.intensity ℓ q x t = S.levyTotalIntensity q x t := rfl
    rw [hsum, div_self (ne_of_gt hpos)]
    simp
  · constructor
    rw [resetKernel, if_neg hpos]
    simp

/-- Integrability of a test function against the reset kernel. -/
theorem integrable_resetKernel (S : SHS Q n m) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (g : Q × EuclideanSpace ℝ (Fin n) → ℝ) :
    Integrable g (S.resetKernel q x t) := by
  classical
  by_cases hpos : 0 < S.levyTotalIntensity q x t
  · rw [resetKernel, if_pos hpos]
    refine integrable_finset_sum_measure.mpr fun ℓ _ => ?_
    refine Integrable.smul_measure ?_ (by simp)
    exact integrable_dirac (by simp [enorm_lt_top])
  · rw [resetKernel, if_neg hpos]
    exact integrable_dirac (by simp [enorm_lt_top])

/-- The value `∫ ψ dK(x, ·)` of a test function against the reset kernel, written out
as the intensity-weighted average of the post-jump values. -/
theorem integral_resetKernel_mul (S : SHS Q n m) (ψ : SHS.TestFunction Q n)
    (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    S.levyTotalIntensity q x t *
        ((∫ y, ψ.toFun y.1 y.2 t ∂(S.resetKernel q x t)) - ψ.toFun q x t)
      = ∑ ℓ : Fin m,
          (ψ.toFun (S.phi_q ℓ q x t) (S.phi_x ℓ q x t) t - ψ.toFun q x t) *
            S.intensity ℓ q x t := by
  classical
  by_cases hpos : 0 < S.levyTotalIntensity q x t
  · have hint : (∫ y, ψ.toFun y.1 y.2 t ∂(S.resetKernel q x t))
        = ∑ ℓ : Fin m, (S.intensity ℓ q x t / S.levyTotalIntensity q x t) *
            ψ.toFun (S.phi_q ℓ q x t) (S.phi_x ℓ q x t) t := by
      rw [resetKernel, if_pos hpos]
      rw [integral_finset_sum_measure (fun ℓ _ => by
        refine Integrable.smul_measure ?_ (by simp)
        exact integrable_dirac (by simp [enorm_lt_top]))]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [integral_smul_measure, integral_dirac]
      have hnn : 0 ≤ S.intensity ℓ q x t / S.levyTotalIntensity q x t := by
        have := S.intensity_nonneg ℓ q x t
        positivity
      rw [ENNReal.toReal_ofReal hnn]
      rfl
    have h1 : S.levyTotalIntensity q x t *
        (∑ ℓ : Fin m, S.intensity ℓ q x t / S.levyTotalIntensity q x t *
          ψ.toFun (S.phi_q ℓ q x t) (S.phi_x ℓ q x t) t)
        = ∑ ℓ : Fin m,
            ψ.toFun (S.phi_q ℓ q x t) (S.phi_x ℓ q x t) t * S.intensity ℓ q x t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      field_simp
    have h2 : S.levyTotalIntensity q x t * ψ.toFun q x t
        = ∑ ℓ : Fin m, ψ.toFun q x t * S.intensity ℓ q x t := by
      rw [levyTotalIntensity, Finset.sum_mul]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    rw [hint, mul_sub, h1, h2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  · -- all intensities vanish
    have hle : S.levyTotalIntensity q x t ≤ 0 := not_lt.mp hpos
    have hzero : ∀ ℓ : Fin m, S.intensity ℓ q x t = 0 := by
      intro ℓ
      have hsum : S.levyTotalIntensity q x t = 0 :=
        le_antisymm hle (S.levyTotalIntensity_nonneg q x t)
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun ℓ _ => S.intensity_nonneg ℓ q x t)).1 hsum ℓ (Finset.mem_univ ℓ)
      exact this
    have hΛ : S.levyTotalIntensity q x t = 0 := le_antisymm hle (S.levyTotalIntensity_nonneg q x t)
    simp [hΛ, hzero]

/-- **Lévy-system form of the SHS extended generator.**

The extended generator of `SHSLib.Core.GeneratorDefs` decomposes as the drift term of
Bect's Eq. (4) plus the jump term `λ (K − I)ψ` of the Lévy system (5)–(6), with the
total intensity `λ` and the Markov reset kernel `K` of an SHS. -/
theorem extendedGenerator_eq_levy (S : SHS Q n m) (ψ : SHS.TestFunction Q n)
    (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    S.extendedGenerator ψ q x t
      = (@inner ℝ _ _ (ψ.grad_x q x t) (S.f q x t) + ψ.partial_t q x t)
        + S.levyTotalIntensity q x t *
            ((∫ y, ψ.toFun y.1 y.2 t ∂(S.resetKernel q x t)) - ψ.toFun q x t) := by
  rw [S.integral_resetKernel_mul ψ q x t, SHS.extendedGenerator]

/-- Integration against a measure with an `ENNReal.ofReal` density. -/
theorem integral_withDensity_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w : α → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (f : α → ℝ) :
    ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (w x)) = ∫ x, w x * f x ∂μ := by
  have hcoe : (fun x => ENNReal.ofReal (w x))
      = fun x => ((Real.toNNReal (w x) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hcoe, integral_withDensity_eq_integral_smul (hw.real_toNNReal) f]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (Real.toNNReal (w x)) • f x = w x * f x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hw0 x)]

/-- **The generalized Dynkin integrand for a Hespanha SHS.**

Integrating the Lévy-system form of the extended generator against the law `μ_t` of the
hybrid state produces exactly the two terms of the right-hand side of Bect's Eq. (13):
the drift term `μ_t(L₀ψ)` and the jump term `r_t(K − I)ψ`, where
`r_t = λ μ_t` is the mean jump intensity of Eq. (8). -/
theorem integral_extendedGenerator_eq_levy (S : SHS Q n m) (ψ : SHS.TestFunction Q n)
    (t : ℝ) (μ : Measure (Q × EuclideanSpace ℝ (Fin n)))
    (hΛ : Measurable fun z : Q × EuclideanSpace ℝ (Fin n) => S.levyTotalIntensity z.1 z.2 t)
    (hflow : Integrable (fun z : Q × EuclideanSpace ℝ (Fin n) =>
      @inner ℝ _ _ (ψ.grad_x z.1 z.2 t) (S.f z.1 z.2 t) + ψ.partial_t z.1 z.2 t) μ)
    (hjump : Integrable (fun z : Q × EuclideanSpace ℝ (Fin n) =>
      S.levyTotalIntensity z.1 z.2 t *
        ((∫ y, ψ.toFun y.1 y.2 t ∂(S.resetKernel z.1 z.2 t)) - ψ.toFun z.1 z.2 t)) μ) :
    ∫ z, S.extendedGenerator ψ z.1 z.2 t ∂μ
      = (∫ z, (@inner ℝ _ _ (ψ.grad_x z.1 z.2 t) (S.f z.1 z.2 t)
            + ψ.partial_t z.1 z.2 t) ∂μ)
        + ∫ z, ((∫ y, ψ.toFun y.1 y.2 t ∂(S.resetKernel z.1 z.2 t)) - ψ.toFun z.1 z.2 t)
            ∂(μ.withDensity fun z => ENNReal.ofReal (S.levyTotalIntensity z.1 z.2 t)) := by
  rw [integral_withDensity_ofReal hΛ (fun z => S.levyTotalIntensity_nonneg z.1 z.2 t)]
  rw [← integral_add hflow hjump]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact S.extendedGenerator_eq_levy ψ z.1 z.2 t

end SHS
