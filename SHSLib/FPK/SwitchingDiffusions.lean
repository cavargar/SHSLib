/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Example 17 of Bect (2010): switching diffusions

For a switching diffusion the hybrid state space is `E = Q × Z` (with `Q` countable and
`Z = ℝⁿ`), the reference measure is `m = (counting measure on Q) ⊗ mZ` and the reset
kernel only changes the discrete mode,

  `K((q, z), ·) = Σ_{q'} π_{q q'}(z) δ_{(q', z)}`,          (28)

with `π(z)` a stochastic matrix.  Bect's **Assumption 14** — the existence of a dual
kernel `K*` with `m(dx) K(x, dy) = m(dy) K*(y, dx)` — then holds with the transposed
matrix,

  `K*((q, z), ·) = Σ_{q'} π_{q' q}(z) δ_{(q', z)}`.          (29)

This file constructs the two kernels (`GSHS.switchingKernel`, `GSHS.switchingKernelDual`),
proves the duality (`GSHS.isDualKernel_switching`), and computes the source density
`K*(λ p_t)` appearing in Corollary 15, which is exactly the jump term
`Σ_{q'} λ_{q' q}(z) p_t(q', z)` of the classical FPK equation (30) for switching
diffusions.
-/
import SHSLib.FPK.DensityEvolution

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

variable {Q : Type*} [Countable Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {Z : Type*} [MeasurableSpace Z]

/-- The reset measure of a switching diffusion at the state `x = (q, z)`:
`Σ_{q'} π_{q q'}(z) δ_{(q', z)}` (Eq. (28)). -/
def switchingMeasure (pi : Q → Q → Z → ℝ≥0∞) (x : Q × Z) : Measure (Q × Z) :=
  Measure.sum fun q' => pi x.1 q' x.2 • Measure.dirac (q', x.2)

/-- The candidate dual reset measure of a switching diffusion at `y = (q, z)`:
`Σ_{q'} π_{q' q}(z) δ_{(q', z)}` (Eq. (29)). -/
def switchingMeasureDual (pi : Q → Q → Z → ℝ≥0∞) (y : Q × Z) : Measure (Q × Z) :=
  Measure.sum fun q => pi q y.1 y.2 • Measure.dirac (q, y.2)

omit [Countable Q] [MeasurableSingletonClass Q] in
theorem lintegral_switchingMeasure (pi : Q → Q → Z → ℝ≥0∞) (x : Q × Z)
    {f : Q × Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(switchingMeasure pi x) = ∑' q', pi x.1 q' x.2 * f (q', x.2) := by
  rw [switchingMeasure, lintegral_sum_measure]
  refine tsum_congr fun q' => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ hf]
  rfl

omit [Countable Q] [MeasurableSingletonClass Q] in
theorem lintegral_switchingMeasureDual (pi : Q → Q → Z → ℝ≥0∞) (y : Q × Z)
    {f : Q × Z → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(switchingMeasureDual pi y) = ∑' q, pi q y.1 y.2 * f (q, y.2) := by
  rw [switchingMeasureDual, lintegral_sum_measure]
  refine tsum_congr fun q => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ hf]
  rfl

theorem measurable_switchingMeasure {pi : Q → Q → Z → ℝ≥0∞}
    (hpi : ∀ q q', Measurable (pi q q')) : Measurable (switchingMeasure pi) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  have hval : ∀ x : Q × Z, switchingMeasure pi x s
      = ∑' q', pi x.1 q' x.2 * s.indicator (1 : Q × Z → ℝ≥0∞) (q', x.2) := by
    intro x
    rw [switchingMeasure, Measure.sum_apply _ hs]
    refine tsum_congr fun q' => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  simp only [hval]
  refine measurable_from_prod_countable_right fun q => ?_
  refine Measurable.ennreal_tsum fun q' => ?_
  exact (hpi q q').mul
    (((measurable_one.indicator hs).comp measurable_prodMk_left).comp measurable_id)

theorem measurable_switchingMeasureDual {pi : Q → Q → Z → ℝ≥0∞}
    (hpi : ∀ q q', Measurable (pi q q')) : Measurable (switchingMeasureDual pi) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  have hval : ∀ y : Q × Z, switchingMeasureDual pi y s
      = ∑' q, pi q y.1 y.2 * s.indicator (1 : Q × Z → ℝ≥0∞) (q, y.2) := by
    intro y
    rw [switchingMeasureDual, Measure.sum_apply _ hs]
    refine tsum_congr fun q => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  simp only [hval]
  refine measurable_from_prod_countable_right fun q₀ => ?_
  refine Measurable.ennreal_tsum fun q => ?_
  exact (hpi q q₀).mul
    (((measurable_one.indicator hs).comp measurable_prodMk_left).comp measurable_id)

/-- The reset kernel `K` of a switching diffusion (Eq. (28)). -/
def switchingKernel {pi : Q → Q → Z → ℝ≥0∞} (hpi : ∀ q q', Measurable (pi q q')) :
    Kernel (Q × Z) (Q × Z) :=
  ⟨switchingMeasure pi, measurable_switchingMeasure hpi⟩

/-- The dual reset kernel `K*` of a switching diffusion (Eq. (29)). -/
def switchingKernelDual {pi : Q → Q → Z → ℝ≥0∞} (hpi : ∀ q q', Measurable (pi q q')) :
    Kernel (Q × Z) (Q × Z) :=
  ⟨switchingMeasureDual pi, measurable_switchingMeasureDual hpi⟩

theorem switchingKernel_apply {pi : Q → Q → Z → ℝ≥0∞} (hpi : ∀ q q', Measurable (pi q q'))
    (x : Q × Z) : switchingKernel hpi x = switchingMeasure pi x := rfl

theorem switchingKernelDual_apply {pi : Q → Q → Z → ℝ≥0∞}
    (hpi : ∀ q q', Measurable (pi q q')) (y : Q × Z) :
    switchingKernelDual hpi y = switchingMeasureDual pi y := rfl

/-- **Example 17** (Bect, 2010): the reset kernel (28) of a switching diffusion satisfies
Assumption 14 with respect to the reference measure `m = count ⊗ mZ`, the dual kernel
being given by the transposed switching matrix, Eq. (29). -/
theorem isDualKernel_switching (mZ : Measure Z) [SFinite mZ] {pi : Q → Q → Z → ℝ≥0∞}
    (hpi : ∀ q q', Measurable (pi q q')) :
    IsDualKernel ((Measure.count : Measure Q).prod mZ)
      (switchingKernel hpi) (switchingKernelDual hpi) := by
  intro f hf
  have hsec : ∀ q q' : Q, Measurable fun z : Z => f (q, z) (q', z) := by
    intro q q'
    have hmap : Measurable fun z : Z => (((q, z) : Q × Z), ((q', z) : Q × Z)) :=
      (measurable_const.prodMk measurable_id).prodMk
        (measurable_const.prodMk measurable_id)
    exact hf.comp hmap
  -- the two inner integrals
  have hfx : ∀ x : Q × Z, Measurable (f x) := fun x =>
    hf.comp (measurable_const.prodMk measurable_id)
  have hfy : ∀ y : Q × Z, Measurable fun x => f x y := fun y =>
    hf.comp (measurable_id.prodMk measurable_const)
  have hL : ∀ x : Q × Z, (∫⁻ y, f x y ∂(switchingKernel hpi x))
      = ∑' q', pi x.1 q' x.2 * f x (q', x.2) := fun x => by
    rw [switchingKernel_apply, lintegral_switchingMeasure _ _ (hfx x)]
  have hR : ∀ y : Q × Z, (∫⁻ x, f x y ∂(switchingKernelDual hpi y))
      = ∑' q, pi q y.1 y.2 * f (q, y.2) y := fun y => by
    rw [switchingKernelDual_apply, lintegral_switchingMeasureDual _ _ (hfy y)]
  have hmeasL : Measurable fun x : Q × Z => ∑' q', pi x.1 q' x.2 * f x (q', x.2) := by
    refine measurable_from_prod_countable_right fun q => ?_
    exact Measurable.ennreal_tsum fun q' => (hpi q q').mul (hsec q q')
  have hmeasR : Measurable fun y : Q × Z => ∑' q, pi q y.1 y.2 * f (q, y.2) y := by
    refine measurable_from_prod_countable_right fun q' => ?_
    exact Measurable.ennreal_tsum fun q => (hpi q q').mul (hsec q q')
  simp only [hL, hR]
  rw [lintegral_prod _ hmeasL.aemeasurable, lintegral_prod _ hmeasR.aemeasurable]
  rw [lintegral_count, lintegral_count]
  have hswapL : ∀ q : Q, (∫⁻ z, ∑' q', pi q q' z * f (q, z) (q', z) ∂mZ)
      = ∑' q', ∫⁻ z, pi q q' z * f (q, z) (q', z) ∂mZ := fun q =>
    lintegral_tsum fun q' => ((hpi q q').mul (hsec q q')).aemeasurable
  have hswapR : ∀ q' : Q, (∫⁻ z, ∑' q, pi q q' z * f (q, z) (q', z) ∂mZ)
      = ∑' q, ∫⁻ z, pi q q' z * f (q, z) (q', z) ∂mZ := fun q' =>
    lintegral_tsum fun q => ((hpi q q').mul (hsec q q')).aemeasurable
  simp only [hswapL, hswapR]
  exact ENNReal.tsum_comm

/-- The source term of Corollary 15 for a switching diffusion: the density
`K*(λ p_t)` of `r_t^src = r_t K` with respect to the reference measure is
`Σ_{q'} λ_{q' q}(z) p_t(q', z)` with `λ_{q' q}(z) = λ(q', z) π_{q' q}(z)`, which is
exactly the jump term of the classical FPK equation (30) for switching diffusions. -/
theorem lintegral_switchingKernelDual_density {pi : Q → Q → Z → ℝ≥0∞}
    (hpi : ∀ q q', Measurable (pi q q')) {lam p : Q × Z → ℝ≥0∞}
    (hlam : Measurable lam) (hp : Measurable p) (q : Q) (z : Z) :
    (∫⁻ x, lam x * p x ∂(switchingKernelDual hpi (q, z)))
      = ∑' q', (lam (q', z) * pi q' q z) * p (q', z) := by
  rw [switchingKernelDual_apply, lintegral_switchingMeasureDual _ _ (hlam.mul hp)]
  exact tsum_congr fun q' => by ring

/-- Measurability of the source density of a switching diffusion. -/
theorem measurable_switchingDualDensity {pi : Q → Q → Z → ℝ≥0∞}
    (hpi : ∀ q q', Measurable (pi q q')) {lam p : Q × Z → ℝ≥0∞}
    (hlam : Measurable lam) (hp : Measurable p) :
    Measurable fun x : Q × Z => ∑' q', lam (q', x.2) * pi q' x.1 x.2 * p (q', x.2) := by
  refine Measurable.ennreal_tsum fun q' => ?_
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact hlam.comp (measurable_const.prodMk measurable_snd)
  · exact measurable_from_prod_countable_right fun q => by simpa using hpi q' q
  · exact hp.comp (measurable_const.prodMk measurable_snd)

/-- **Example 17, Eq. (30)** (Bect, 2010): the generalized FPK equation for a switching
diffusion.  With reference measure `m = count ⊗ mZ`, mean jump intensity `r_t = λ μ_t`
and reset kernel (28), Corollary 15 gives

  `∂p/∂t (q, z) = (L* p_t)(q, z) + Σ_{q'} λ_{q' q}(z) p_t(q', z) − λ(q, z) p_t(q, z)`,

with `λ_{q' q}(z) = λ(q', z) π_{q' q}(z)`. -/
theorem switching_fpk_equation (mZ : Measure Z) [SFinite mZ]
    [SigmaFinite ((Measure.count : Measure Q).prod mZ)]
    {pi : Q → Q → Z → ℝ≥0∞} (hpi : ∀ q q', Measurable (pi q q'))
    {lam p : Q × Z → ℝ≥0∞} (hlam : Measurable lam) (hp : Measurable p)
    {dp Fp : Q × Z → ℝ}
    (hsrc_lt_top : ∀ x : Q × Z, (∑' q', lam (q', x.2) * pi q' x.1 x.2 * p (q', x.2)) < ⊤)
    (hsink_lt_top : ∀ x : Q × Z, lam x * p x < ⊤)
    (hdp : ∀ s, MeasurableSet s → ((Measure.count : Measure Q).prod mZ) s < ⊤ →
      IntegrableOn dp s ((Measure.count : Measure Q).prod mZ))
    (hFp : ∀ s, MeasurableSet s → ((Measure.count : Measure Q).prod mZ) s < ⊤ →
      IntegrableOn Fp s ((Measure.count : Measure Q).prod mZ))
    (hsrc : ∀ s, MeasurableSet s → ((Measure.count : Measure Q).prod mZ) s < ⊤ →
      IntegrableOn (fun x : Q × Z =>
        (∑' q', lam (q', x.2) * pi q' x.1 x.2 * p (q', x.2)).toReal) s
        ((Measure.count : Measure Q).prod mZ))
    (hsink : ∀ s, MeasurableSet s → ((Measure.count : Measure Q).prod mZ) s < ⊤ →
      IntegrableOn (fun x : Q × Z => (lam x * p x).toReal) s
        ((Measure.count : Measure Q).prod mZ))
    (hbal : ∀ s, MeasurableSet s → ((Measure.count : Measure Q).prod mZ) s < ⊤ →
      ∫ x in s, dp x ∂((Measure.count : Measure Q).prod mZ)
        = (∫ x in s, Fp x ∂((Measure.count : Measure Q).prod mZ))
          + ((switchingKernel hpi ∘ₘ
              (((Measure.count : Measure Q).prod mZ).withDensity
                fun x => lam x * p x)) s).toReal
          - ((((Measure.count : Measure Q).prod mZ).withDensity
                fun x => lam x * p x) s).toReal) :
    dp =ᵐ[(Measure.count : Measure Q).prod mZ] fun x : Q × Z =>
      Fp x + (∑' q', lam (q', x.2) * pi q' x.1 x.2 * p (q', x.2)).toReal
        - (lam x * p x).toReal := by
  have hdens : ∀ x : Q × Z, (∫⁻ y, lam y * p y ∂(switchingKernelDual hpi x))
      = ∑' q', lam (q', x.2) * pi q' x.1 x.2 * p (q', x.2) := by
    rintro ⟨q, z⟩
    exact lintegral_switchingKernelDual_density hpi hlam hp q z
  have hsrc_meas : Measurable fun x : Q × Z =>
      ∫⁻ y, lam y * p y ∂(switchingKernelDual hpi x) := by
    simp only [hdens]
    exact measurable_switchingDualDensity hpi hlam hp
  have h := corollary15_pdf_evolution ((Measure.count : Measure Q).prod mZ)
    (isDualKernel_switching mZ hpi) hlam hp hsrc_meas
    (by simpa only [hdens] using hsrc_lt_top) hsink_lt_top hdp hFp
    (by simpa only [hdens] using hsrc) hsink hbal
  simpa only [hdens] using h

end GSHS
