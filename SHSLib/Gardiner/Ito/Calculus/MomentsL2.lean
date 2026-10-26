/-
# GBM moment equations for unbounded initial values

`Gardiner.Ito.IsFWiener.geomBM_mean_eq` and `geomBM_second_eq` (`Moments.lean`) derive the moment
equations of `dx = λx dt + μx dW` from Itô's formula for a *bounded* initial value.  With
`Gardiner.Ito.IsFWiener.geomBM_ito_of_memLp` the same derivation works for

* `x₀ ∈ L²` (mean equation `⟨x(T)⟩ = ⟨x₀⟩ + λ∫₀ᵀ⟨x⟩`, ODE `m' = λm`), and
* `x₀² ∈ L²`, i.e. `⟨x₀⁴⟩ < ∞` (second-moment equation, ODE `m' = (2λ+μ²)m`): Itô's formula is
  applied to `x²`, a GBM with initial value `x₀²`, and its noise term `∫ 2μx² dW` must be an Itô
  integral with mean zero.
-/
import SHSLib.Gardiner.Ito.Calculus.Moments
import SHSLib.Gardiner.Ito.Calculus.MulLeftL2

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **The mean equation of `dx = λx dt + μx dW` from Itô's formula, `x₀ ∈ L²`**:
`⟨x(T)⟩ = ⟨x₀⟩ + λ ∫₀ᵀ ⟨x(s)⟩ ds`. -/
theorem IsFWiener.geomBM_mean_eq_of_memLp (hWj : Measurable (Function.uncurry W)) {T : ℝ}
    (hT : 0 < T) (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0)
    (hx02 : MemLp x0 2 P) :
    ∫ ω, geomBM lam mu x0 W T ω ∂P =
      ∫ ω, x0 ω ∂P + lam * ∫ s in (0 : ℝ)..T, ∫ ω, geomBM lam mu x0 W s ω ∂P := by
  have := hW.isProbabilityMeasure
  have hx0i : Integrable x0 P := hx02.integrable one_le_two
  have h := hW.geomBM_ito_of_memLp hWj hT lam mu hx0 hx02
  have hI := hW.isItoIntegrand_geomBM_of_memLp hWj T lam mu mu hx0 hx02
  have hD := hW.isItoIntegrand_geomBM_of_memLp hWj T lam mu lam hx0 hx02
  have hDi : Integrable (Function.uncurry fun s ω => lam * geomBM lam mu x0 W s ω)
      (tsMeasure P T) := hD.memLp.integrable one_le_two
  have hDω : Integrable (fun ω => ∫ s in (0 : ℝ)..T, lam * geomBM lam mu x0 W s ω) P := by
    simp_rw [intervalIntegral.integral_of_le hT.le]
    exact hDi.integral_prod_right
  have e1 := integral_congr_ae h
  rw [integral_sub (hW.integral_geomBM lam mu hx0 hx0i hT.le).1 hx0i,
    integral_add hDω ((memLp_itoInt hW hI).integrable one_le_two), itoInt_mean hW hI, add_zero,
    integral_intervalIntegral_swap hT.le hDi] at e1
  simp_rw [integral_const_mul] at e1
  rw [intervalIntegral.integral_const_mul] at e1
  linarith

/-- **The second-moment equation of `dx = λx dt + μx dW` from Itô's formula for `x²`**, for an
initial value with `x₀² ∈ L²`: `⟨x(T)²⟩ = ⟨x₀²⟩ + (2λ + μ²) ∫₀ᵀ ⟨x(s)²⟩ ds`. -/
theorem IsFWiener.geomBM_second_eq_of_memLp (hWj : Measurable (Function.uncurry W)) {T : ℝ}
    (hT : 0 < T) (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0)
    (hx04 : MemLp (fun ω => x0 ω ^ 2) 2 P) :
    ∫ ω, geomBM lam mu x0 W T ω ^ 2 ∂P =
      ∫ ω, x0 ω ^ 2 ∂P +
        (2 * lam + mu ^ 2) * ∫ s in (0 : ℝ)..T, ∫ ω, geomBM lam mu x0 W s ω ^ 2 ∂P := by
  simp_rw [geomBM_sq]
  exact hW.geomBM_mean_eq_of_memLp hWj hT (2 * lam + mu ^ 2) (2 * mu) (hx0.pow 2) hx04

/-- **Differential form of the mean equation**, `x₀ ∈ L²`: `d⟨x⟩/dt = λ⟨x⟩` for `t > 0`. -/
theorem IsFWiener.geomBM_mean_hasDerivAt_of_memLp (hWj : Measurable (Function.uncurry W))
    (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun T => ∫ ω, geomBM lam mu x0 W T ω ∂P)
      (lam * ∫ ω, geomBM lam mu x0 W t ω ∂P) t := by
  have := hW.isProbabilityMeasure
  have hx0i : Integrable x0 P := hx02.integrable one_le_two
  exact hasDerivAt_of_integral_eq (m' := fun s => (∫ ω, x0 ω ∂P) * Real.exp (lam * s))
    (by fun_prop) (fun s hs => (hW.integral_geomBM lam mu hx0 hx0i hs).2)
    (fun T hT => hW.geomBM_mean_eq_of_memLp hWj hT lam mu hx0 hx02) ht

/-- **Differential form of the second-moment equation**, `x₀² ∈ L²`:
`d⟨x²⟩/dt = (2λ + μ²)⟨x²⟩` for `t > 0` (the ODE of job D's `gbmSecond`). -/
theorem IsFWiener.geomBM_second_hasDerivAt_of_memLp (hWj : Measurable (Function.uncurry W))
    (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0)
    (hx04 : MemLp (fun ω => x0 ω ^ 2) 2 P) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun T => ∫ ω, geomBM lam mu x0 W T ω ^ 2 ∂P)
      ((2 * lam + mu ^ 2) * ∫ ω, geomBM lam mu x0 W t ω ^ 2 ∂P) t := by
  simp_rw [geomBM_sq]
  exact hW.geomBM_mean_hasDerivAt_of_memLp hWj (2 * lam + mu ^ 2) (2 * mu) (hx0.pow 2) hx04 ht

end Gardiner.Ito
