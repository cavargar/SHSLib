/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Example 18 of Bect (2010): deterministic reset maps and their Jacobians

In the SHS of Hespanha the post-jump state is obtained by applying a reset map
`Ψ : E → E⁰` to the pre-jump state, so that the reset kernel is a Dirac mass,
`K(x, ·) = δ_{Ψ(x)}` (Eq. (31), one reset map).  If `Ψ` is a `C¹`-diffeomorphism then
**Assumption 14** holds with

  `K*(y, ·) = |J(y)|⁻¹ δ_{Ψ⁻¹(y)}`,   (32)

`J` being the Jacobian determinant of `Ψ`.  Note that `K*` is *not* a Markov kernel.

This file proves that identity, by the change-of-variables formula:

* `GSHS.lintegral_deterministic_reset_dual` — the duality relation
  `m(dx) K(x, dy) = m(dy) K*(y, dx)` in integrated form;
* `GSHS.jacobianDualKernel` — the kernel `K*` of Eq. (32);
* `GSHS.isDualKernel_deterministic_reset` — Assumption 14 for `K(x, ·) = δ_{Ψ(x)}`.

Together with `GSHS.corollary15_source_density` this yields the density
`d(r_tK)/dm = K*(λ p_t)` of Eq. (25), which is Hespanha's FPK equation (33).
-/
import SHSLib.FPK.SpontaneousJumps

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]

variable {Psi PsiInv : V → V} {Psi' : V → V →L[ℝ] V}

/-- **Change of variables for a deterministic reset** (Example 18, Eq. (32)).  If the
reset map `Ψ` is a diffeomorphism with derivative `Ψ'` and nonvanishing Jacobian, then
for every nonnegative jointly measurable `f`

  `∫ f(x, Ψ x) m(dx) = ∫ |J(Ψ⁻¹ y)|⁻¹ f(Ψ⁻¹ y, y) m(dy)`,

which is the duality relation `m(dx) δ_{Ψ(x)}(dy) = m(dy) K*(y, dx)` of Assumption 14. -/
theorem lintegral_deterministic_reset_dual
    (hderiv : ∀ x, HasFDerivAt Psi (Psi' x) x) (hdet : ∀ x, (Psi' x).det ≠ 0)
    (hleft : Function.LeftInverse PsiInv Psi) (hright : Function.RightInverse PsiInv Psi)
    (f : V → V → ℝ≥0∞) :
    ∫⁻ x, f x (Psi x) ∂m
      = ∫⁻ y, ENNReal.ofReal |(Psi' (PsiInv y)).det|⁻¹ * f (PsiInv y) y ∂m := by
  have hinj : Set.InjOn Psi univ := fun a _ b _ hab => by
    have := congrArg PsiInv hab
    rwa [hleft a, hleft b] at this
  have himage : Psi '' univ = univ := by
    ext y
    simp only [image_univ, mem_range, mem_univ, iff_true]
    exact ⟨PsiInv y, hright y⟩
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := m) MeasurableSet.univ
    (f := Psi) (f' := Psi') (fun x _ => (hderiv x).hasFDerivWithinAt) hinj
    (fun y => ENNReal.ofReal |(Psi' (PsiInv y)).det|⁻¹ * f (PsiInv y) y)
  rw [himage] at hcv
  simp only [Measure.restrict_univ] at hcv
  rw [hcv]
  refine lintegral_congr fun x => ?_
  rw [hleft x]
  have hpos : 0 < |(Psi' x).det| := abs_pos.2 (hdet x)
  rw [← mul_assoc, ENNReal.ofReal_inv_of_pos hpos,
    ENNReal.mul_inv_cancel (by simpa using hpos.ne') ENNReal.ofReal_ne_top, one_mul]

/-- The dual kernel `K*(y, ·) = |J(y)|⁻¹ δ_{Ψ⁻¹(y)}` of Eq. (32). -/
def jacobianDualKernel (PsiInv : V → V) (hPsiInv : Measurable PsiInv)
    (Psi' : V → V →L[ℝ] V) : Kernel V V :=
  Kernel.withDensity (Kernel.deterministic PsiInv hPsiInv)
    fun _ x => ENNReal.ofReal |(Psi' x).det|⁻¹

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Evaluating the dual kernel: `∫ g dK*(y, ·) = |J(Ψ⁻¹ y)|⁻¹ g(Ψ⁻¹ y)`. -/
theorem lintegral_jacobianDualKernel (hPsiInv : Measurable PsiInv)
    (hdetmeas : Measurable fun x => (Psi' x).det) {g : V → ℝ≥0∞} (hg : Measurable g) (y : V) :
    ∫⁻ x, g x ∂(jacobianDualKernel PsiInv hPsiInv Psi' y)
      = ENNReal.ofReal |(Psi' (PsiInv y)).det|⁻¹ * g (PsiInv y) := by
  have hdensity : Measurable
      (Function.uncurry fun _ x : V => ENNReal.ofReal |(Psi' x).det|⁻¹) := by
    have : (Function.uncurry fun _ x : V => ENNReal.ofReal |(Psi' x).det|⁻¹)
        = fun q : V × V => ENNReal.ofReal |(Psi' q.2).det|⁻¹ := rfl
    rw [this]
    exact (ENNReal.measurable_ofReal.comp (((hdetmeas.abs).inv).comp measurable_snd))
  have hd : Measurable fun x => ENNReal.ofReal |(Psi' x).det|⁻¹ :=
    ENNReal.measurable_ofReal.comp (hdetmeas.abs).inv
  rw [jacobianDualKernel, Kernel.withDensity_apply _ hdensity, Kernel.deterministic_apply,
    lintegral_withDensity_eq_lintegral_mul _ hd hg]
  exact lintegral_dirac' (a := PsiInv y)
    (f := fun x => ENNReal.ofReal |(Psi' x).det|⁻¹ * g x) (hd.mul hg)

/-- **Assumption 14 for a deterministic reset map** (Example 18): the reset kernel
`K(x, ·) = δ_{Ψ(x)}` of a `C¹`-diffeomorphism `Ψ` admits the dual kernel
`K*(y, ·) = |J(y)|⁻¹ δ_{Ψ⁻¹(y)}` of Eq. (32). -/
theorem isDualKernel_deterministic_reset (hPsi : Measurable Psi) (hPsiInv : Measurable PsiInv)
    (hderiv : ∀ x, HasFDerivAt Psi (Psi' x) x) (hdet : ∀ x, (Psi' x).det ≠ 0)
    (hdetmeas : Measurable fun x => (Psi' x).det)
    (hleft : Function.LeftInverse PsiInv Psi) (hright : Function.RightInverse PsiInv Psi) :
    IsDualKernel m (Kernel.deterministic Psi hPsi) (jacobianDualKernel PsiInv hPsiInv Psi') := by
  intro f hf
  have hleftside : ∀ x : V, ∫⁻ y, f x y ∂((Kernel.deterministic Psi hPsi) x) = f x (Psi x) := by
    intro x
    have hfx : Measurable fun y => f x y := hf.comp measurable_prodMk_left
    rw [Kernel.deterministic_apply, lintegral_dirac' _ hfx]
  have hrightside : ∀ y : V,
      ∫⁻ x, f x y ∂(jacobianDualKernel PsiInv hPsiInv Psi' y)
        = ENNReal.ofReal |(Psi' (PsiInv y)).det|⁻¹ * f (PsiInv y) y := by
    intro y
    have hfy : Measurable fun x => f x y := by
      have hswap : (Function.uncurry fun y x => f x y) = (Function.uncurry f) ∘ Prod.swap := by
        funext q; simp [Function.uncurry]
      have : Measurable (Function.uncurry fun y x => f x y) := by
        rw [hswap]; exact hf.comp measurable_swap
      exact this.comp measurable_prodMk_left
    exact lintegral_jacobianDualKernel hPsiInv hdetmeas hfy y
  simp only [hleftside, hrightside]
  exact lintegral_deterministic_reset_dual m hderiv hdet hleft hright f

end GSHS
