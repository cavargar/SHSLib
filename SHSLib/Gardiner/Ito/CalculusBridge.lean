/-
# Bridge: the E1/E2 Wiener process → the E3 Itô calculus

The general Itô calculus `SHSLib.Gardiner.Ito.Calculus.*` (job E3) is stated for an abstract
Wiener process with respect to a filtration, `Gardiner.Ito.IsFWiener W 𝓕 P`. This file shows
that a Wiener process in the sense of E1, `Gardiner.Ito.IsWiener W P`, is such a process for its
natural filtration `Gardiner.Ito.wienerFiltration`. As a result, every E3 result applies to the
standard Wiener process `Gardiner.Ito.stdWiener` built from the brownian-motion dependency.

This is deferred item 1 of `research/docs/plans/plan_gardiner_ito_formula.md`.

| Lean | content |
| --- | --- |
| `IsWiener.isFWiener` | `IsWiener W P → IsFWiener W (wienerFiltration W _) P` |
| `isFWiener_stdWiener` | the standard Wiener process as an `IsFWiener` process |
| `measurable_uncurry_stdWiener` | joint measurability of `stdWiener` (needed by several E3 results) |
| `itoInt_W_stdWiener` | (4.2.20) `∫₀ᵀ W dW = ½(W(T)² − T)` for `stdWiener` |
| `IsWiener.integral_geomBM_const`, `IsWiener.integral_geomBM_sq_const` | GBM moments equal `Gardiner.SDE.gbmMean` and `Gardiner.SDE.gbmSecond` |
| `geomBM_ito_stdWiener` | GBM solves `dx = λx dt + μx dW` driven by `stdWiener` |
-/
import SHSLib.Gardiner.Ito.Brownian
import SHSLib.Gardiner.Ito.Calculus
import SHSLib.Gardiner.Ito.WienerIntegral
import SHSLib.Gardiner.SDE.WeakError

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- An E1 Wiener process is an E3 Wiener process for its natural filtration. The fields coincide;
adaptedness is `IsWiener.stronglyAdapted`. -/
theorem IsWiener.isFWiener (hW : IsWiener W P) :
    IsFWiener W (wienerFiltration W hW.measurable) P where
  isProbabilityMeasure := hW.isProbabilityMeasure
  measurable := hW.measurable
  zero := hW.zero
  cont := hW.cont
  adapted _ ht := hW.stronglyAdapted ht
  law_sub := hW.law_sub
  indep_past := hW.indep_past

/-- The standard Wiener process is an `IsFWiener` process for its natural filtration. -/
theorem isFWiener_stdWiener :
    IsFWiener stdWiener (wienerFiltration stdWiener measurable_stdWiener) stdWienerMeasure :=
  isWiener_stdWiener.isFWiener

/-- `(t, ω) ↦ stdWiener t ω` is jointly measurable: every path is continuous and every
`stdWiener t` is measurable. -/
theorem measurable_uncurry_stdWiener : Measurable (Function.uncurry stdWiener) :=
  measurable_uncurry_of_continuous_of_measurable continuous_stdWiener measurable_stdWiener

/-- (4.2.20) as a genuine Itô integral for the standard Wiener process:
`∫₀ᵀ W dW = ½(W(T)² − T)` almost surely. -/
theorem itoInt_W_stdWiener {T : ℝ} (hT : 0 < T) :
    itoInt stdWiener (wienerFiltration stdWiener measurable_stdWiener) stdWienerMeasure T stdWiener
      =ᵐ[stdWienerMeasure] fun ω => (stdWiener T ω ^ 2 - T) / 2 :=
  isFWiener_stdWiener.itoInt_W measurable_uncurry_stdWiener hT

/-- The mean of geometric Brownian motion with deterministic `x₀` is job D's `gbmMean`. -/
theorem IsWiener.integral_geomBM_const (hW : IsWiener W P) (lam mu x0 : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ ω, geomBM lam mu (fun _ => x0) W t ω ∂P = Gardiner.SDE.gbmMean lam x0 t :=
  hW.isFWiener.integral_geomBM_const lam mu x0 ht

/-- The second moment of geometric Brownian motion with deterministic `x₀` is job D's
`gbmSecond`, which job D only checked against its moment ODE. -/
theorem IsWiener.integral_geomBM_sq_const (hW : IsWiener W P) (lam mu x0 : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ ω, geomBM lam mu (fun _ => x0) W t ω ^ 2 ∂P = Gardiner.SDE.gbmSecond lam mu x0 t :=
  hW.isFWiener.integral_geomBM_sq_const lam mu x0 ht

/-- Geometric Brownian motion driven by the standard Wiener process solves
`x(T) − x₀ = ∫₀ᵀ λx dt + ∫₀ᵀ μx dW` almost surely, for any deterministic `x₀`. -/
theorem geomBM_ito_stdWiener {T : ℝ} (hT : 0 < T) (lam mu x0 : ℝ) :
    (fun ω => geomBM lam mu (fun _ => x0) stdWiener T ω - x0) =ᵐ[stdWienerMeasure] fun ω =>
      (∫ s in (0 : ℝ)..T, lam * geomBM lam mu (fun _ => x0) stdWiener s ω) +
        itoInt stdWiener (wienerFiltration stdWiener measurable_stdWiener) stdWienerMeasure T
          (fun s ω => mu * geomBM lam mu (fun _ => x0) stdWiener s ω) ω :=
  isFWiener_stdWiener.geomBM_ito_of_memLp measurable_uncurry_stdWiener hT lam mu
    stronglyMeasurable_const (memLp_const x0)

omit mΩ in
/-- E2's left-point Riemann sums on `[0, T]` are E3's. -/
lemma riemannSum_eq_itoRiemann (f : ℝ → ℝ) (T : ℝ) (n : ℕ) :
    riemannSum W f 0 T n = itoRiemann W (fun t _ => f t) T n := by
  funext ω
  simp only [riemannSum, itoRiemann, grid, unifPart, gridPt, zero_add, sub_zero]
  push_cast
  rfl

/-- For continuous deterministic `f`, the general Itô integral (E3) agrees almost surely with the
Wiener integral (E2). Both are mean-square limits of the same left-point Riemann sums. This is
deferred item 3 of `plan_gardiner_ito_formula.md`. -/
theorem IsWiener.itoInt_det_eq_wienerInt (hW : IsWiener W P) {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Continuous f) :
    itoInt W (wienerFiltration W hW.measurable) P T (fun t _ => f t) =ᵐ[P] wienerInt W P f 0 T := by
  have := hW.isProbabilityMeasure
  have hF := hW.isFWiener
  obtain ⟨hI, hlim⟩ := hW.wienerInt_spec hf le_rfl hT.le
  have h1 := itoInt_det_tendsto hF hT hf
  simp_rw [← riemannSum_eq_itoRiemann] at h1
  exact l2_ae_unique (memLp_riemannSum hW le_rfl hT.le) (memLp_itoInt hF (isItoIntegrand_det T hf))
    hI h1 hlim

/-- Instance: `∫₀¹ s dW(s)` is the same random variable for E2's Wiener integral and E3's Itô
integral, driven by `stdWiener`. -/
theorem itoInt_id_eq_wienerInt_stdWiener :
    itoInt stdWiener (wienerFiltration stdWiener measurable_stdWiener) stdWienerMeasure 1
        (fun t _ => t) =ᵐ[stdWienerMeasure] wienerInt stdWiener stdWienerMeasure id 0 1 :=
  isWiener_stdWiener.itoInt_det_eq_wienerInt one_pos continuous_id

/-- Non-degenerate instance: for `λ = 0`, `μ = 1`, `x₀ = 1`, the second moment of the
exponential martingale `exp(W(t) − t/2)` is `eᵗ`. -/
theorem integral_geomBM_sq_stdWiener_example {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, geomBM 0 1 (fun _ => 1) stdWiener t ω ^ 2 ∂stdWienerMeasure = Real.exp t := by
  rw [isWiener_stdWiener.integral_geomBM_sq_const 0 1 1 ht]
  simp [Gardiner.SDE.gbmSecond]

end Gardiner.Ito
