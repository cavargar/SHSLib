/-
# An Itô process with drift: `x(t) = μt + σW(t)` (Gardiner §4.3.3)

A non-degenerate instance of the general one-dimensional Itô formula
`Gardiner.Ito.IsFWiener.ito_formula` (4.3.14) for an Itô process with nonzero drift `a = μ` and
noise coefficient `b = σ`, applied to `f(x) = eˣ`, which does not have bounded derivatives:

`e^{x(T)} - 1 = ∫₀ᵀ (μ + σ²/2) e^{x(s)} ds + ∫₀ᵀ σ e^{x(s)} dW(s)` a.s.
(`Gardiner.Ito.IsFWiener.ito_formula_exp_drift`).

It also records the moments of geometric Brownian motion with a deterministic initial value
`x(0) = x₀`, in the closed forms `x₀ e^{λt}` and `x₀² e^{(2λ+μ²)t}` used by the SDE layer
(`Gardiner.Ito.IsFWiener.integral_geomBM_const`, `Gardiner.Ito.IsFWiener.integral_geomBM_sq_const`).
-/
import SHSLib.Gardiner.Ito.Calculus.GBM

open MeasureTheory ProbabilityTheory Filter Topology Set

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **Itô's formula (4.3.14) for `eˣ` along the Itô process `x(t) = μt + σW(t)`**
(`a = μ`, `b = σ`, `x(0) = 0`):
`e^{x(T)} - 1 = ∫₀ᵀ (μ e^{x(s)} + σ²/2 e^{x(s)}) ds + ∫₀ᵀ σ e^{x(s)} dW(s)` a.s. -/
theorem IsFWiener.ito_formula_exp_drift (hWj : Measurable (Function.uncurry W)) {T : ℝ}
    (hT : 0 < T) (μ σ : ℝ) :
    (fun ω => Real.exp (μ * T + σ * W T ω) - 1) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, (μ * Real.exp (μ * s + σ * W s ω) +
          σ ^ 2 / 2 * Real.exp (μ * s + σ * W s ω))) +
        itoInt W 𝓕 P T (fun s ω => σ * Real.exp (μ * s + σ * W s ω)) ω := by
  have hF : IsC12 (fun _ x => Real.exp x) (fun _ _ => 0) (fun _ x => Real.exp x)
      (fun _ x => Real.exp x) :=
    ⟨continuous_const, by fun_prop, by fun_prop, fun _ _ => hasDerivAt_const _ _,
      fun _ x => Real.hasDerivAt_exp x, fun _ x => Real.hasDerivAt_exp x⟩
  have hg : (fun t ω => Real.exp (μ * t + σ * W t ω)) =
      fun t ω => (fun t x => 1 * Real.exp (σ * x + μ * t)) t (W t ω) := by
    funext t ω; ring_nf
  have hb : MSBounded P T fun t ω => Real.exp (μ * t + σ * W t ω) := by
    rw [hg]; exact (expGrowth_exp 1 σ μ T).msBounded hW
  have hc : MSUnifCont P T fun t ω => Real.exp (μ * t + σ * W t ω) := by
    rw [hg]; exact (expGrowth_exp 1 σ μ T).msUnifCont hW
  have h := hW.ito_formula hT hF (x := fun t ω => μ * t + σ * W t ω) (a := fun _ _ => μ)
    (x0 := fun _ => 0) (b := σ)
    (Eventually.of_forall fun ω t => by simp [intervalIntegral.integral_const]; ring)
    (Eventually.of_forall fun _ => continuous_const)
    ((measurable_fst.const_mul μ).add (hWj.const_mul σ))
    (fun t ht => stronglyMeasurable_const.add ((hW.adapted t ht).const_mul σ)) hb hc hb
  filter_upwards [h, hW.zero] with ω hω h0
  simp only [h0, mul_zero, add_zero, Real.exp_zero] at hω
  rw [hω]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp

/-- Mean of geometric Brownian motion with deterministic initial value `x₀`:
`⟨x(t)⟩ = x₀ e^{λt}` for `t ≥ 0`. -/
theorem IsFWiener.integral_geomBM_const (lam mu x0 : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, geomBM lam mu (fun _ => x0) W t ω ∂P = x0 * Real.exp (lam * t) := by
  have := hW.isProbabilityMeasure
  rw [(hW.integral_geomBM lam mu stronglyMeasurable_const (integrable_const x0) ht).2]
  simp

/-- Second moment of geometric Brownian motion with deterministic initial value `x₀`:
`⟨x(t)²⟩ = x₀² e^{(2λ+μ²)t}` for `t ≥ 0`. -/
theorem IsFWiener.integral_geomBM_sq_const (lam mu x0 : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, geomBM lam mu (fun _ => x0) W t ω ^ 2 ∂P = x0 ^ 2 * Real.exp ((2 * lam + mu ^ 2) * t) := by
  have := hW.isProbabilityMeasure
  rw [(hW.integral_geomBM_sq lam mu stronglyMeasurable_const (memLp_const x0) ht).2]
  simp

end Gardiner.Ito
