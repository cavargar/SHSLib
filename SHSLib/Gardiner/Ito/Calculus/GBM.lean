/-
# Geometric Brownian motion (Gardiner §4.4.2, (4.4.3)–(4.4.13))

`geomBM λ μ x₀ W t = x₀ exp((λ - μ²/2) t + μ W(t))` solves the linear multiplicative-noise
equation `dx = λ x dt + μ x dW` of job D in the integral sense
(`Gardiner.Ito.IsFWiener.geomBM_ito`); `λ = 0`, `μ = c` is Gardiner's (4.4.7) with `t₀ = 0`.

* mean (4.4.9) / `⟨x(t)⟩ = ⟨x₀⟩ e^{λt}`: `Gardiner.Ito.IsFWiener.integral_geomBM`;
* second moment `⟨x(t)²⟩ = ⟨x₀²⟩ e^{(2λ+μ²)t}`: `Gardiner.Ito.IsFWiener.integral_geomBM_sq`;
* autocorrelation (4.4.10): `Gardiner.Ito.IsFWiener.integral_geomBM_mul`;
* Stratonovich solution `x₀ e^{cW(t)}` (4.4.11) and its moments (4.4.12), (4.4.13):
  `Gardiner.Ito.IsFWiener.integral_stratGBM`, `Gardiner.Ito.IsFWiener.integral_stratGBM_mul`.

The initial value `x₀` is `𝓕 0`-measurable, i.e. independent of the Wiener increments.
-/
import SHSLib.Gardiner.Ito.Calculus.ItoExamples
import SHSLib.Gardiner.Ito.Calculus.MulLeft

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*}

/-- **Geometric Brownian motion** `x(t) = x₀ exp((λ - μ²/2) t + μ W(t))`, the solution of
`dx = λ x dt + μ x dW`, `x(0) = x₀`. -/
def geomBM (lam mu : ℝ) (x0 : Ω → ℝ) (W : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  x0 ω * Real.exp ((lam - mu ^ 2 / 2) * t + mu * W t ω)

/-- The **Stratonovich solution** `x₀ exp(c W(t))` of `dx = c x dW` (Gardiner (4.4.11)). -/
def stratGBM (c : ℝ) (x0 : Ω → ℝ) (W : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  x0 ω * Real.exp (c * W t ω)

lemma stratGBM_eq_geomBM (c : ℝ) (x0 : Ω → ℝ) (W : ℝ → Ω → ℝ) :
    stratGBM c x0 W = geomBM (c ^ 2 / 2) c x0 W := by
  funext t ω; simp [stratGBM, geomBM]

/-- The square of a geometric Brownian motion is again one. -/
lemma geomBM_sq (lam mu : ℝ) (x0 : Ω → ℝ) (W : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    geomBM lam mu x0 W t ω ^ 2 = geomBM (2 * lam + mu ^ 2) (2 * mu) (fun ω => x0 ω ^ 2) W t ω := by
  simp only [geomBM, mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast; ring

variable [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω} {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

lemma IsFWiener.geomBM_sm {lam mu : ℝ} {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) {t : ℝ}
    (ht : 0 ≤ t) : StronglyMeasurable[𝓕 t] (geomBM lam mu x0 W t) := by
  have h1 : StronglyMeasurable[𝓕 t] x0 := hx0.mono (𝓕.mono ht)
  have h2 : StronglyMeasurable[𝓕 t] (fun ω => Real.exp ((lam - mu ^ 2 / 2) * t + mu * W t ω)) :=
    Real.continuous_exp.comp_stronglyMeasurable
      (stronglyMeasurable_const.add (stronglyMeasurable_const.mul (hW.adapted t ht)))
  exact h1.mul h2

/-- `x(t) = x₀ · e^{(λ-μ²/2)t} · e^{μ(W(t) - W(0))}` almost surely. -/
lemma IsFWiener.geomBM_ae (lam mu : ℝ) (x0 : Ω → ℝ) (t : ℝ) :
    geomBM lam mu x0 W t =ᵐ[P] fun ω =>
      x0 ω * (Real.exp ((lam - mu ^ 2 / 2) * t) * Real.exp (mu * (W t ω - W 0 ω))) := by
  filter_upwards [hW.zero] with ω h0
  simp [geomBM, h0, Real.exp_add]

/-- **Mean of geometric Brownian motion**: `⟨x(t)⟩ = ⟨x₀⟩ e^{λt}`.  For `λ = 0` this is
Gardiner (4.4.9), `⟨x(t)⟩ = ⟨x(t₀)⟩`. -/
theorem IsFWiener.integral_geomBM (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0)
    (hx0i : Integrable x0 P) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (geomBM lam mu x0 W t) P ∧
      ∫ ω, geomBM lam mu x0 W t ω ∂P = (∫ ω, x0 ω ∂P) * Real.exp (lam * t) := by
  have := hW.isProbabilityMeasure
  obtain ⟨h1, h2⟩ := hW.mul_incr_fun le_rfl ht hx0 hx0i
    (g := fun y => Real.exp ((lam - mu ^ 2 / 2) * t) * Real.exp (mu * y)) (by fun_prop)
    ((hW.integrable_exp_mul_incr le_rfl ht mu).const_mul _)
  have hae := hW.geomBM_ae lam mu x0 t
  refine ⟨h1.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, h2, integral_const_mul, hW.integral_exp_mul_incr le_rfl ht,
    ← Real.exp_add]
  congr 2; ring

/-- **Second moment of geometric Brownian motion**: `⟨x(t)²⟩ = ⟨x₀²⟩ e^{(2λ+μ²)t}`. -/
theorem IsFWiener.integral_geomBM_sq (lam mu : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => geomBM lam mu x0 W t ω ^ 2) P ∧
      ∫ ω, geomBM lam mu x0 W t ω ^ 2 ∂P =
        (∫ ω, x0 ω ^ 2 ∂P) * Real.exp ((2 * lam + mu ^ 2) * t) := by
  simp_rw [geomBM_sq]
  exact hW.integral_geomBM _ _ (hx0.pow 2) hx02.integrable_sq ht

/-- **Autocorrelation of geometric Brownian motion** for `s ≤ t`:
`⟨x(t) x(s)⟩ = ⟨x₀²⟩ e^{λ(t+s) + μ² s}`. -/
theorem IsFWiener.integral_geomBM_mul_of_le (lam mu : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    ∫ ω, geomBM lam mu x0 W t ω * geomBM lam mu x0 W s ω ∂P =
      (∫ ω, x0 ω ^ 2 ∂P) * Real.exp (lam * (t + s) + mu ^ 2 * s) := by
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hsq⟩ := hW.integral_geomBM_sq lam mu hx0 hx02 hs
  have hZ : StronglyMeasurable[𝓕 s] (fun ω => geomBM lam mu x0 W s ω ^ 2) :=
    (hW.geomBM_sm hx0 hs).pow 2
  obtain ⟨-, h2⟩ := hW.mul_incr_fun hs hst hZ hi
    (g := fun y => Real.exp ((lam - mu ^ 2 / 2) * (t - s)) * Real.exp (mu * y)) (by fun_prop)
    ((hW.integrable_exp_mul_incr hs hst mu).const_mul _)
  have e : (fun ω => geomBM lam mu x0 W t ω * geomBM lam mu x0 W s ω) = fun ω =>
      geomBM lam mu x0 W s ω ^ 2 *
        (Real.exp ((lam - mu ^ 2 / 2) * (t - s)) * Real.exp (mu * (W t ω - W s ω))) := by
    funext ω
    simp only [geomBM]
    have hC : (lam - mu ^ 2 / 2) * (t - s) + mu * (W t ω - W s ω) =
        ((lam - mu ^ 2 / 2) * t + mu * W t ω) - ((lam - mu ^ 2 / 2) * s + mu * W s ω) := by ring
    rw [← Real.exp_add, hC, Real.exp_sub]
    field_simp
  rw [e, h2, hsq, integral_const_mul, hW.integral_exp_mul_incr hs hst, mul_assoc,
    ← Real.exp_add, ← Real.exp_add]
  congr 2; ring

/-- **Gardiner (4.4.10)** (with `t₀ = 0`, general drift `λ`):
`⟨x(t) x(s)⟩ = ⟨x₀²⟩ e^{λ(t+s) + μ² min(t,s)}`. -/
theorem IsFWiener.integral_geomBM_mul (lam mu : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) :
    ∫ ω, geomBM lam mu x0 W t ω * geomBM lam mu x0 W s ω ∂P =
      (∫ ω, x0 ω ^ 2 ∂P) * Real.exp (lam * (t + s) + mu ^ 2 * min t s) := by
  rcases le_total s t with hst | hts
  · rw [min_eq_right hst]; exact hW.integral_geomBM_mul_of_le lam mu hx0 hx02 hs hst
  · rw [min_eq_left hts]
    simp_rw [mul_comm (geomBM lam mu x0 W t _)]
    rw [hW.integral_geomBM_mul_of_le lam mu hx0 hx02 ht hts, add_comm s t]

/-- **Gardiner (4.4.12)**: `⟨x₀ e^{cW(t)}⟩ = ⟨x₀⟩ e^{c² t/2}`. -/
theorem IsFWiener.integral_stratGBM (c : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0)
    (hx0i : Integrable x0 P) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, stratGBM c x0 W t ω ∂P = (∫ ω, x0 ω ∂P) * Real.exp (c ^ 2 * t / 2) := by
  rw [stratGBM_eq_geomBM, (hW.integral_geomBM _ c hx0 hx0i ht).2]
  congr 2; ring

/-- **Gardiner (4.4.13)**: `⟨x(t) x(s)⟩ = ⟨x₀²⟩ e^{½c²(t + s + 2 min(t,s))}` for the
Stratonovich solution. -/
theorem IsFWiener.integral_stratGBM_mul (c : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0)
    (hx02 : MemLp x0 2 P) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ ω, stratGBM c x0 W t ω * stratGBM c x0 W s ω ∂P =
      (∫ ω, x0 ω ^ 2 ∂P) * Real.exp (c ^ 2 / 2 * (t + s + 2 * min t s)) := by
  rw [stratGBM_eq_geomBM, hW.integral_geomBM_mul _ c hx0 hx02 hs ht]
  congr 2; ring

/-- The exponential factor of `geomBM` is an Itô integrand on `[0, T]` after multiplication by
any constant. -/
lemma IsFWiener.isItoIntegrand_expW (hWj : Measurable (Function.uncurry W)) (A c d T : ℝ) :
    IsItoIntegrand 𝓕 P T (fun s ω => A * Real.exp (c * W s ω + d * s)) := by
  have := hW.isProbabilityMeasure
  have hcont : Continuous fun p : ℝ × ℝ => A * Real.exp (c * p.2 + d * p.1) := by fun_prop
  refine isItoIntegrand_of_msBounded ?_ (fun t ht _ => ?_)
    ((expGrowth_exp A c d T).msBounded hW)
  · exact hcont.measurable.comp (measurable_fst.prodMk hWj)
  · exact (hcont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
      (hW.adapted t ht)

/-- **Geometric Brownian motion solves `dx = λx dt + μx dW`** in the integral sense:
`x(T) - x₀ = ∫₀ᵀ λ x dt + ∫₀ᵀ μ x dW` a.s., for a bounded `𝓕 0`-measurable initial value `x₀`
(independent of `W`).  With `λ = 0` this is Gardiner (4.4.3)/(4.4.7). -/
theorem IsFWiener.geomBM_ito (hWj : Measurable (Function.uncurry W)) {T : ℝ} (hT : 0 < T)
    (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) {C : ℝ}
    (hx0b : ∀ ω, |x0 ω| ≤ C) :
    (fun ω => geomBM lam mu x0 W T ω - x0 ω) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, lam * geomBM lam mu x0 W s ω) +
        itoInt W 𝓕 P T (fun s ω => mu * geomBM lam mu x0 W s ω) ω := by
  set d := lam - mu ^ 2 / 2 with hd
  have hF : IsC12 (fun t x => 1 * Real.exp (mu * x + d * t))
      (fun t x => d * (1 * Real.exp (mu * x + d * t)))
      (fun t x => mu * Real.exp (mu * x + d * t))
      (fun t x => mu ^ 2 * Real.exp (mu * x + d * t)) := by
    refine ⟨by fun_prop, by fun_prop, by fun_prop, fun t x => ?_, fun t x => ?_, fun t x => ?_⟩
    · have := (((hasDerivAt_id t).const_mul d).const_add (mu * x)).exp.const_mul 1
      convert this using 1; simp; ring
    · have := (((hasDerivAt_id x).const_mul mu).add_const (d * t)).exp.const_mul 1
      convert this using 1; simp; ring
    · have := (((hasDerivAt_id x).const_mul mu).add_const (d * t)).exp.const_mul mu
      convert this using 1; simp; ring
  have h := hW.ito_formula_W_growth hWj hT hF (expGrowth_exp mu mu d T)
    (expGrowth_exp (mu ^ 2) mu d T)
  have hG := hW.isItoIntegrand_expW hWj mu mu d T
  have hm := itoInt_mul_left hW hG hx0 hx0b
  have hcongr : (fun s ω => mu * geomBM lam mu x0 W s ω) =
      fun s ω => x0 ω * (mu * Real.exp (mu * W s ω + d * s)) := by
    funext s ω; simp only [geomBM, hd]; ring_nf
  rw [hcongr]
  filter_upwards [h, hm, hW.zero] with ω hω hmω h0
  rw [hmω]
  simp only [h0, mul_zero, zero_add, Real.exp_zero, one_mul] at hω
  have hT1 : geomBM lam mu x0 W T ω = x0 ω * Real.exp (mu * W T ω + d * T) := by
    simp only [geomBM, hd]; ring_nf
  have hI : ∫ s in (0 : ℝ)..T, lam * geomBM lam mu x0 W s ω =
      x0 ω * ∫ s in (0 : ℝ)..T, (d * Real.exp (mu * W s ω + d * s) +
        mu ^ 2 * Real.exp (mu * W s ω + d * s) / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [geomBM, hd]; ring_nf
  rw [hT1, hI]
  calc x0 ω * Real.exp (mu * W T ω + d * T) - x0 ω
      = x0 ω * (Real.exp (mu * W T ω + d * T) - 1) := by ring
    _ = _ := by rw [hω]; ring

end Gardiner.Ito
