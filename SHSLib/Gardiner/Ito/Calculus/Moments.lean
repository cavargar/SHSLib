/-
# Moment equations from Itô's formula (job D's moment ODEs)

For the linear multiplicative-noise equation `dx = λx dt + μx dW` of the SDE layer, the moment
equations are *derived* here from Itô's formula and the mean-value formula (4.2.40):

* `Gardiner.Ito.IsFWiener.geomBM_mean_eq`:
  `⟨x(T)⟩ = ⟨x₀⟩ + λ ∫₀ᵀ ⟨x(s)⟩ ds` — take expectations in the integral equation
  `x(T) - x₀ = ∫ λx ds + ∫ μx dW` (`geomBM_ito`, itself Itô's formula), use `⟨∫ μx dW⟩ = 0`
  (`itoInt_mean`) and Fubini;
* `Gardiner.Ito.IsFWiener.geomBM_second_eq`:
  `⟨x(T)²⟩ = ⟨x₀²⟩ + (2λ + μ²) ∫₀ᵀ ⟨x(s)²⟩ ds` — Itô's formula for `x²`, Gardiner's
  `d(x²) = 2x dx + (dx)² = (2λ + μ²)x² dt + 2μx² dW`;
* the differential forms `geomBM_mean_hasDerivAt`, `geomBM_second_hasDerivAt`: these are exactly
  the ODEs `m' = λ m` and `m' = (2λ + μ²) m` verified by `Gardiner.SDE.gbmMean_hasDerivAt` and
  `Gardiner.SDE.gbmSecond_hasDerivAt`.
-/
import SHSLib.Gardiner.Ito.Calculus.GBM

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

/-- An ODE in integral form with a continuous representative has the expected derivative. -/
lemma hasDerivAt_of_integral_eq {m m' : ℝ → ℝ} {c a : ℝ} (hm' : Continuous m')
    (heq : ∀ s, 0 ≤ s → m s = m' s) (hint : ∀ T, 0 < T → m T = c + a * ∫ s in (0 : ℝ)..T, m s)
    {t : ℝ} (ht : 0 < t) : HasDerivAt m (a * m t) t := by
  have hφ : HasDerivAt (fun T => c + a * ∫ s in (0 : ℝ)..T, m' s) (a * m' t) t :=
    ((intervalIntegral.integral_hasDerivAt_right (hm'.intervalIntegrable 0 t)
      (hm'.stronglyMeasurableAtFilter _ _) hm'.continuousAt).const_mul a).const_add c
  rw [heq t ht.le]
  refine hφ.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with T hT
  rw [hint T hT]
  congr 2
  refine intervalIntegral.integral_congr fun s hs => heq s ?_
  rw [Set.uIcc_of_le (le_of_lt hT)] at hs
  exact hs.1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Fubini for the time integral of a jointly integrable process. -/
lemma integral_intervalIntegral_swap {T : ℝ} (hT : 0 ≤ T) [SFinite P] {f : ℝ → Ω → ℝ}
    (hf : Integrable (Function.uncurry f) (tsMeasure P T)) :
    ∫ ω, (∫ s in (0 : ℝ)..T, f s ω) ∂P = ∫ s in (0 : ℝ)..T, ∫ ω, f s ω ∂P := by
  simp_rw [intervalIntegral.integral_of_le hT]
  exact (integral_integral_swap hf).symm

variable {𝓕 : Filtration ℝ mΩ} {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

lemma IsFWiener.isItoIntegrand_geomBM (hWj : Measurable (Function.uncurry W)) (lam mu c T : ℝ)
    {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) {C : ℝ} (hx0b : ∀ ω, |x0 ω| ≤ C) :
    IsItoIntegrand 𝓕 P T (fun s ω => c * geomBM lam mu x0 W s ω) := by
  have h := isItoIntegrand_mul_left (hW.isItoIntegrand_expW hWj c mu (lam - mu ^ 2 / 2) T)
    hx0 hx0b
  convert h using 1
  funext s ω; simp only [geomBM]; ring_nf

/-- **The mean equation of `dx = λx dt + μx dW`, derived from Itô's formula**:
`⟨x(T)⟩ = ⟨x₀⟩ + λ ∫₀ᵀ ⟨x(s)⟩ ds`. -/
theorem IsFWiener.geomBM_mean_eq (hWj : Measurable (Function.uncurry W)) {T : ℝ} (hT : 0 < T)
    (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) {C : ℝ}
    (hx0b : ∀ ω, |x0 ω| ≤ C) :
    ∫ ω, geomBM lam mu x0 W T ω ∂P =
      ∫ ω, x0 ω ∂P + lam * ∫ s in (0 : ℝ)..T, ∫ ω, geomBM lam mu x0 W s ω ∂P := by
  have := hW.isProbabilityMeasure
  have hx0m : Measurable x0 := (hx0.mono (𝓕.le 0)).measurable
  have hx0i : Integrable x0 P :=
    (integrable_const C).mono' hx0m.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hx0b ω)
  have h := hW.geomBM_ito hWj hT lam mu hx0 hx0b
  have hI := hW.isItoIntegrand_geomBM hWj lam mu mu T hx0 hx0b
  have hD := hW.isItoIntegrand_geomBM hWj lam mu lam T hx0 hx0b
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

/-- **The second-moment equation of `dx = λx dt + μx dW`, derived from Itô's formula for `x²`**:
`⟨x(T)²⟩ = ⟨x₀²⟩ + (2λ + μ²) ∫₀ᵀ ⟨x(s)²⟩ ds`. -/
theorem IsFWiener.geomBM_second_eq (hWj : Measurable (Function.uncurry W)) {T : ℝ} (hT : 0 < T)
    (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) {C : ℝ}
    (hx0b : ∀ ω, |x0 ω| ≤ C) :
    ∫ ω, geomBM lam mu x0 W T ω ^ 2 ∂P =
      ∫ ω, x0 ω ^ 2 ∂P + (2 * lam + mu ^ 2) * ∫ s in (0 : ℝ)..T, ∫ ω, geomBM lam mu x0 W s ω ^ 2 ∂P := by
  have hb : ∀ ω, |x0 ω ^ 2| ≤ C ^ 2 := fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hx0b ω) 2
  simp_rw [geomBM_sq]
  exact hW.geomBM_mean_eq hWj hT (2 * lam + mu ^ 2) (2 * mu) (hx0.pow 2) hb

/-- **Differential form of the mean equation**: `d⟨x⟩/dt = λ ⟨x⟩` for `t > 0` (the ODE of
`Gardiner.SDE.gbmMean_hasDerivAt`), obtained from `geomBM_mean_eq`. -/
theorem IsFWiener.geomBM_mean_hasDerivAt (hWj : Measurable (Function.uncurry W)) (lam mu : ℝ)
    {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) {C : ℝ} (hx0b : ∀ ω, |x0 ω| ≤ C) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun T => ∫ ω, geomBM lam mu x0 W T ω ∂P)
      (lam * ∫ ω, geomBM lam mu x0 W t ω ∂P) t := by
  have := hW.isProbabilityMeasure
  have hx0m : Measurable x0 := (hx0.mono (𝓕.le 0)).measurable
  have hx0i : Integrable x0 P :=
    (integrable_const C).mono' hx0m.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hx0b ω)
  exact hasDerivAt_of_integral_eq (m' := fun s => (∫ ω, x0 ω ∂P) * Real.exp (lam * s))
    (by fun_prop) (fun s hs => (hW.integral_geomBM lam mu hx0 hx0i hs).2)
    (fun T hT => hW.geomBM_mean_eq hWj hT lam mu hx0 hx0b) ht

/-- **Differential form of the second-moment equation**: `d⟨x²⟩/dt = (2λ + μ²)⟨x²⟩` for `t > 0`
(the ODE of `Gardiner.SDE.gbmSecond_hasDerivAt`), obtained from `geomBM_second_eq`. -/
theorem IsFWiener.geomBM_second_hasDerivAt (hWj : Measurable (Function.uncurry W)) (lam mu : ℝ)
    {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) {C : ℝ} (hx0b : ∀ ω, |x0 ω| ≤ C) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun T => ∫ ω, geomBM lam mu x0 W T ω ^ 2 ∂P)
      ((2 * lam + mu ^ 2) * ∫ ω, geomBM lam mu x0 W t ω ^ 2 ∂P) t := by
  have := hW.isProbabilityMeasure
  have hx0m : Measurable x0 := (hx0.mono (𝓕.le 0)).measurable
  have hx02 : MemLp x0 2 P :=
    MemLp.of_bound hx0m.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hx0b ω)
  exact hasDerivAt_of_integral_eq
    (m' := fun s => (∫ ω, x0 ω ^ 2 ∂P) * Real.exp ((2 * lam + mu ^ 2) * s))
    (by fun_prop) (fun s hs => (hW.integral_geomBM_sq lam mu hx0 hx02 hs).2)
    (fun T hT => hW.geomBM_second_eq hWj hT lam mu hx0 hx0b) ht

end Gardiner.Ito

/-! ### The Ornstein–Uhlenbeck moment equations -/

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma MSBounded.const_mul {T : ℝ} {G : ℝ → Ω → ℝ} (hG : MSBounded P T G) (c : ℝ) :
    MSBounded P T fun t ω => c * G t ω := by
  obtain ⟨M, hM⟩ := hG
  refine ⟨c ^ 2 * M, fun t ht => ⟨(hM t ht).1.const_mul c, ?_⟩⟩
  have e : (fun ω => (c * G t ω) ^ 2) = fun ω => c ^ 2 * G t ω ^ 2 := by funext ω; ring
  rw [e, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hM t ht).2 (sq_nonneg c)

lemma MSUnifCont.const_mul {T : ℝ} {G : ℝ → Ω → ℝ} (hG : MSUnifCont P T G) (c : ℝ) :
    MSUnifCont P T fun t ω => c * G t ω := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hG (ε / (c ^ 2 + 1)) (by positivity)
  refine ⟨δ, hδ, fun s t hs hsT ht htT hst => ?_⟩
  have e : (fun ω => (c * G s ω - c * G t ω) ^ 2) = fun ω => c ^ 2 * (G s ω - G t ω) ^ 2 := by
    funext ω; ring
  rw [e, integral_const_mul]
  have h1 := h s t hs hsT ht htT hst
  have h0 : 0 ≤ ∫ ω, (G s ω - G t ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  calc c ^ 2 * ∫ ω, (G s ω - G t ω) ^ 2 ∂P ≤ c ^ 2 * (ε / (c ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left h1.le (sq_nonneg c)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

variable {𝓕 : Filtration ℝ mΩ} {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **The OU mean equation from the SDE and the mean-value formula**: for any process with
`x(t) = x(0) - γ ∫₀ᵗ x ds + σ W(t)` (Gardiner (4.4.24)) which is square integrable on
`[0, T]`, `⟨x(T)⟩ = ⟨x(0)⟩ - γ ∫₀ᵀ ⟨x(s)⟩ ds` — the ODE of `Gardiner.SDE.ouMean_hasDerivAt`. -/
theorem IsFWiener.ou_mean_eq {T : ℝ} (hT : 0 < T) {γ σ : ℝ} {x : ℝ → Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, ∀ t, x t ω = x 0 ω + (∫ s in (0 : ℝ)..t, -γ * x s ω) + σ * W t ω)
    (hxm : Measurable (Function.uncurry x))
    (hxad : ∀ t, 0 ≤ t → StronglyMeasurable[𝓕 t] (x t)) (hxb : MSBounded P T x) :
    ∫ ω, x T ω ∂P = ∫ ω, x 0 ω ∂P - γ * ∫ s in (0 : ℝ)..T, ∫ ω, x s ω ∂P := by
  have := hW.isProbabilityMeasure
  have hI : IsItoIntegrand 𝓕 P T fun s ω => -γ * x s ω :=
    isItoIntegrand_of_msBounded ((measurable_const.mul hxm)) (fun t ht _ =>
      stronglyMeasurable_const.mul (hxad t ht)) (hxb.const_mul (-γ))
  have hDi : Integrable (Function.uncurry fun s ω => -γ * x s ω) (tsMeasure P T) :=
    hI.memLp.integrable one_le_two
  have hDω : Integrable (fun ω => ∫ s in (0 : ℝ)..T, -γ * x s ω) P := by
    simp_rw [intervalIntegral.integral_of_le hT.le]
    exact hDi.integral_prod_right
  obtain ⟨M, hM⟩ := hxb
  have hxT := (hM T ⟨hT.le, le_rfl⟩).1.integrable one_le_two
  have hx0 := (hM 0 ⟨le_rfl, hT.le⟩).1.integrable one_le_two
  have hWT : Integrable (fun ω => σ * W T ω) P := (hW.integrable hT.le).const_mul σ
  have hWm : ∫ ω, σ * W T ω ∂P = 0 := by
    rw [integral_const_mul, integral_congr_ae (hW.W_eq_incr_ae T), hW.integral_incr le_rfl hT.le,
      mul_zero]
  have e : (fun ω => x T ω) =ᵐ[P] fun ω =>
      x 0 ω + (∫ s in (0 : ℝ)..T, -γ * x s ω) + σ * W T ω := by
    filter_upwards [hx] with ω hω using hω T
  have e1 := integral_congr_ae e
  rw [integral_add (f := fun ω => x 0 ω + ∫ s in (0 : ℝ)..T, -γ * x s ω) (hx0.add hDω) hWT,
    integral_add hx0 hDω, hWm, add_zero,
    integral_intervalIntegral_swap hT.le hDi] at e1
  simp_rw [integral_const_mul] at e1
  rw [intervalIntegral.integral_const_mul] at e1
  linarith

/-- **The OU second-moment equation from Itô's formula** (applied to `x²`, Gardiner (4.3.14)):
for any process with `x(t) = x(0) - γ ∫₀ᵗ x ds + σ W(t)`, continuous paths, and `x` bounded and
uniformly continuous in mean square on `[0, T]`,
`⟨x(T)²⟩ = ⟨x(0)²⟩ + ∫₀ᵀ (σ² - 2γ⟨x(s)²⟩) ds` — the ODE of `Gardiner.SDE.ouSecond_hasDerivAt`. -/
theorem IsFWiener.ou_second_eq {T : ℝ} (hT : 0 < T) {γ σ : ℝ} {x : ℝ → Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, ∀ t, x t ω = x 0 ω + (∫ s in (0 : ℝ)..t, -γ * x s ω) + σ * W t ω)
    (hxc : ∀ᵐ ω ∂P, Continuous fun t => x t ω)
    (hxm : Measurable (Function.uncurry x))
    (hxad : ∀ t, 0 ≤ t → StronglyMeasurable[𝓕 t] (x t)) (hxb : MSBounded P T x)
    (hxu : MSUnifCont P T x) :
    ∫ ω, x T ω ^ 2 ∂P =
      ∫ ω, x 0 ω ^ 2 ∂P + ∫ s in (0 : ℝ)..T, (σ ^ 2 - 2 * γ * ∫ ω, x s ω ^ 2 ∂P) := by
  have := hW.isProbabilityMeasure
  have hF : IsC12 (fun _ y => y ^ 2) (fun _ _ => 0) (fun _ y => 2 * y) (fun _ _ => 2) := by
    refine ⟨continuous_const, by fun_prop, continuous_const, fun _ _ => hasDerivAt_const _ _,
      fun t y => ?_, fun t y => ?_⟩
    · simpa using hasDerivAt_pow 2 y
    · simpa using (hasDerivAt_id y).const_mul 2
  have hFxx : MSBounded P T fun (_ : ℝ) (_ : Ω) => (2 : ℝ) :=
    ⟨4, fun t _ => ⟨memLp_const 2, by simp; norm_num⟩⟩
  have h := hW.ito_formula hT hF (x := x) (a := fun s ω => -γ * x s ω) (x0 := x 0) (b := σ)
    hx (by filter_upwards [hxc] with ω hω using continuous_const.mul hω) hxm hxad
    (hxb.const_mul 2) (hxu.const_mul 2) hFxx
  -- integrability
  have hxI : IsItoIntegrand 𝓕 P T x := isItoIntegrand_of_msBounded hxm (fun t ht _ => hxad t ht) hxb
  have hI : IsItoIntegrand 𝓕 P T fun s ω => σ * (2 * x s ω) :=
    isItoIntegrand_of_msBounded (measurable_const.mul (measurable_const.mul hxm))
      (fun t ht _ => stronglyMeasurable_const.mul (stronglyMeasurable_const.mul (hxad t ht)))
      ((hxb.const_mul 2).const_mul σ)
  set f : ℝ → Ω → ℝ := fun s ω => 0 + -γ * x s ω * (2 * x s ω) + σ ^ 2 / 2 * 2 with hf
  have hfi : Integrable (Function.uncurry f) (tsMeasure P T) := by
    have h2 : Integrable (fun p : ℝ × Ω => Function.uncurry x p ^ 2) (tsMeasure P T) :=
      hxI.memLp.integrable_sq
    refine ((h2.const_mul (-2 * γ)).add (integrable_const (σ ^ 2))).congr
      (Eventually.of_forall fun p => ?_)
    show -2 * γ * x p.1 p.2 ^ 2 + σ ^ 2 = 0 + -γ * x p.1 p.2 * (2 * x p.1 p.2) + σ ^ 2 / 2 * 2
    ring
  have hfω : Integrable (fun ω => ∫ s in (0 : ℝ)..T, f s ω) P := by
    simp_rw [intervalIntegral.integral_of_le hT.le]
    exact hfi.integral_prod_right
  obtain ⟨M, hM⟩ := hxb
  have hxT := (hM T ⟨hT.le, le_rfl⟩).1.integrable_sq
  have hx0 := (hM 0 ⟨le_rfl, hT.le⟩).1.integrable_sq
  have e1 := integral_congr_ae h
  rw [integral_sub hxT hx0, integral_add hfω ((memLp_itoInt hW hI).integrable one_le_two),
    itoInt_mean hW hI, add_zero, integral_intervalIntegral_swap hT.le hfi] at e1
  have e2 : ∫ s in (0 : ℝ)..T, ∫ ω, f s ω ∂P =
      ∫ s in (0 : ℝ)..T, (σ ^ 2 - 2 * γ * ∫ ω, x s ω ^ 2 ∂P) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hT.le] at hs
    have hs2 := (hM s hs).1.integrable_sq
    have e : f s = fun ω => (-2 * γ) * x s ω ^ 2 + σ ^ 2 := by
      funext ω; simp only [hf]; ring
    simp only [e]
    rw [integral_add (hs2.const_mul _) (integrable_const _), integral_const_mul]
    simp; ring
  rw [e2] at e1
  linarith

end Gardiner.Ito
