/-
# Geometric Brownian motion: Dynkin's formula and the weak Fokker–Planck equation

For GBM `X(t) = x₀ exp((λ - μ²/2) t + μ W(t))` (`Gardiner.Ito.geomBM`, the solution of
`dx = λ x dt + μ x dW`, Gardiner §4.4.2) the noise coefficient `b(x) = μ x` is unbounded, so the
general SDE theorems (which need a bounded `b`) do not apply.  For test functions `φ ∈ C²_c` we
instead write `φ(X(t)) = F(t, W(t))` with `F(t, w) = φ(x₀ e^{(λ - μ²/2)t + μ w})` and apply the
time-dependent Itô formula of job E3 along `W`; `F_w`, `F_ww` are bounded because `φ'`, `φ''`
have compact support.

* `gbm_ito_formula`: `φ(X(t)) - φ(x₀) = ∫₀ᵗ L φ(X(s)) ds + ∫₀ᵗ μ X φ'(X) dW` a.s.;
* `gbm_dynkin`: `E φ(X(t)) = φ(x₀) + E ∫₀ᵗ (λ X φ'(X) + ½ μ² X² φ''(X)) ds`;
* `gbm_weakFP_integrated`: `∫ φ dμ_t = φ(x₀) + ∫₀ᵗ (∫ L φ dμ_s) ds`.

The file also records `wiener_martingale_clamp`: the Mathlib-`Martingale` form of the martingale
problem for `W` itself (generator `½ φ''`), when every path of `W` is continuous.
-/
import SHSLib.Gardiner.Ito.Generator.Examples
import SHSLib.Gardiner.Ito.Calculus.GBM

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.Generator

open Gardiner.Ito

/-- A compactly supported continuous `g` makes `z ↦ g(z) zⁿ` bounded. -/
lemma exists_bound_mul_pow {g : ℝ → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (n : ℕ) :
    ∃ C, ∀ z, |g z * z ^ n| ≤ C := by
  obtain ⟨C, hC⟩ := (hg.mul (continuous_pow n)).bounded_above_of_compact_support
    (hgs.mul_right (f' := fun z : ℝ => z ^ n))
  exact ⟨C, fun z => by simpa using hC z⟩

/-- The GBM generator: `L φ (y) = λ y φ'(y) + ½ (μ y)² φ''(y)`. -/
lemma itoGen_gbm (lam mu : ℝ) (φ : ℝ → ℝ) (t y : ℝ) :
    itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ t y =
      lam * y * deriv φ y + (mu * y) ^ 2 / 2 * deriv (deriv φ) y := rfl

section GBM

variable (lam mu x0 : ℝ) {φ : ℝ → ℝ}

/-- `g(s, w) = x₀ e^{(λ - μ²/2) s + μ w}`. -/
def gbmMap (s w : ℝ) : ℝ := x0 * exp ((lam - mu ^ 2 / 2) * s + mu * w)

/-- `F(s, w) = φ(g(s, w))` and its partial derivatives. -/
def gbmF (φ : ℝ → ℝ) (s w : ℝ) : ℝ := φ (gbmMap lam mu x0 s w)
def gbmFt (φ : ℝ → ℝ) (s w : ℝ) : ℝ :=
  deriv φ (gbmMap lam mu x0 s w) * ((lam - mu ^ 2 / 2) * gbmMap lam mu x0 s w)
def gbmFx (φ : ℝ → ℝ) (s w : ℝ) : ℝ := deriv φ (gbmMap lam mu x0 s w) * (mu * gbmMap lam mu x0 s w)
def gbmFxx (φ : ℝ → ℝ) (s w : ℝ) : ℝ :=
  mu ^ 2 * (deriv (deriv φ) (gbmMap lam mu x0 s w) * gbmMap lam mu x0 s w ^ 2 +
    deriv φ (gbmMap lam mu x0 s w) * gbmMap lam mu x0 s w)

lemma continuous_gbmMap : Continuous (Function.uncurry (gbmMap lam mu x0)) := by
  unfold gbmMap Function.uncurry; fun_prop

lemma isC12_gbmF (hφ : IsC2c φ) :
    IsC12 (gbmF lam mu x0 φ) (gbmFt lam mu x0 φ) (gbmFx lam mu x0 φ) (gbmFxx lam mu x0 φ) := by
  have hg := continuous_gbmMap lam mu x0
  have h1 := hφ.continuous_deriv
  have h2 := hφ.continuous_deriv2
  have hgt : ∀ s w, HasDerivAt (fun s => gbmMap lam mu x0 s w)
      ((lam - mu ^ 2 / 2) * gbmMap lam mu x0 s w) s := fun s w => by
    have := (((hasDerivAt_id s).const_mul (lam - mu ^ 2 / 2)).add_const (mu * w)).exp.const_mul x0
    convert this using 1
    simp only [gbmMap, id, mul_one]; ring
  have hgw : ∀ s w, HasDerivAt (fun w => gbmMap lam mu x0 s w) (mu * gbmMap lam mu x0 s w) w :=
    fun s w => by
    have := (((hasDerivAt_id w).const_mul mu).const_add ((lam - mu ^ 2 / 2) * s)).exp.const_mul x0
    convert this using 1
    simp only [gbmMap, id, mul_one]; ring
  refine ⟨?_, ?_, ?_, fun s w => ?_, fun s w => ?_, fun s w => ?_⟩
  · exact (h1.comp hg).mul (continuous_const.mul hg)
  · exact (h1.comp hg).mul (continuous_const.mul hg)
  · exact continuous_const.mul (((h2.comp hg).mul (hg.pow 2)).add ((h1.comp hg).mul hg))
  · exact (hφ.hasDerivAt _).comp s (hgt s w)
  · exact (hφ.hasDerivAt _).comp w (hgw s w)
  · have := ((hφ.hasDerivAt_deriv _).comp w (hgw s w)).mul ((hgw s w).const_mul mu)
    convert this using 1
    simp only [gbmFxx, Function.comp]; ring

lemma gbmFx_bdd (hφ : IsC2c φ) : ∃ C, ∀ s w, |gbmFx lam mu x0 φ s w| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_mul_pow hφ.continuous_deriv hφ.hasCompactSupport.deriv 1
  refine ⟨|mu| * C, fun s w => ?_⟩
  have := hC (gbmMap lam mu x0 s w)
  simp only [pow_one] at this
  calc |gbmFx lam mu x0 φ s w| = |mu| * |deriv φ (gbmMap lam mu x0 s w) * gbmMap lam mu x0 s w| := by
        simp only [gbmFx]; rw [← abs_mul]; ring_nf
    _ ≤ |mu| * C := mul_le_mul_of_nonneg_left this (abs_nonneg _)

lemma gbmFxx_bdd (hφ : IsC2c φ) : ∃ C, ∀ s w, |gbmFxx lam mu x0 φ s w| ≤ C := by
  obtain ⟨C1, hC1⟩ := exists_bound_mul_pow hφ.continuous_deriv hφ.hasCompactSupport.deriv 1
  obtain ⟨C2, hC2⟩ := exists_bound_mul_pow hφ.continuous_deriv2
    hφ.hasCompactSupport.deriv.deriv 2
  refine ⟨mu ^ 2 * (C2 + C1), fun s w => ?_⟩
  have h1 := hC1 (gbmMap lam mu x0 s w)
  have h2 := hC2 (gbmMap lam mu x0 s w)
  simp only [pow_one] at h1
  simp only [gbmFxx, abs_mul, abs_pow, sq_abs]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (sq_nonneg _)
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) (hWj : Measurable (Function.uncurry W))
include hW hWj

omit mΩ hW hWj in
lemma geomBM_eq_gbmMap (s : ℝ) (ω : Ω) :
    geomBM lam mu (fun _ => x0) W s ω = gbmMap lam mu x0 s (W s ω) := rfl

omit hW hWj in
/-- The generator integrand along `W`: `F_t + ½ F_ww = L φ ∘ g`. -/
lemma gbm_generator_eq (s w : ℝ) :
    gbmFt lam mu x0 φ s w + 0 * gbmFx lam mu x0 φ s w + 1 ^ 2 / 2 * gbmFxx lam mu x0 φ s w =
      itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ s (gbmMap lam mu x0 s w) := by
  simp only [gbmFt, gbmFx, gbmFxx, itoGen]; ring

omit hWj in
lemma isItoIntegrand_gbmNoise (hφ : IsC2c φ) (t : ℝ) (hWj : Measurable (Function.uncurry W)) :
    IsItoIntegrand 𝓕 P t (fun s ω => (fun _ _ => (1 : ℝ)) s ω * gbmFx lam mu x0 φ s (W s ω)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC⟩ := gbmFx_bdd lam mu x0 hφ
  have hF := isC12_gbmF lam mu x0 hφ
  have h := isItoIntegrand_mul_bdd (g := fun s ω => gbmFx lam mu x0 φ s (W s ω)) (C := C)
    (isItoIntegrand_det (𝓕 := 𝓕) (P := P) t (continuous_const (y := (1 : ℝ))))
    (hF.cont_Fx.measurable.comp (measurable_fst.prodMk hWj))
    (fun s h0 _ => (hF.cont_Fx.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
      (hW.adapted s h0)) (fun s ω => hC _ _)
  convert h using 1
  funext s ω; ring

/-- **Itô's formula for `φ(X(t))`, `X` geometric Brownian motion, `φ ∈ C²_c`**:
`φ(X(t)) - φ(x₀) = ∫₀ᵗ L φ(X(s)) ds + ∫₀ᵗ F_w(s, W(s)) dW` almost surely. -/
theorem gbm_ito_formula (hφ : IsC2c φ) {t : ℝ} (ht : 0 < t) :
    (fun ω => φ (geomBM lam mu (fun _ => x0) W t ω) - φ x0) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..t,
        itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ s (geomBM lam mu (fun _ => x0) W s ω)) +
        itoInt W 𝓕 P t (fun s ω => (fun _ _ => (1 : ℝ)) s ω * gbmFx lam mu x0 φ s (W s ω)) ω := by
  obtain ⟨C1, hC1⟩ := gbmFx_bdd lam mu x0 hφ
  obtain ⟨C2, hC2⟩ := gbmFxx_bdd lam mu x0 hφ
  have h := hW.ito_formula_process ht (isC12_gbmF lam mu x0 hφ) hC1 hC2 (hW.isItoProcess_W hWj t)
    zero_le_one (fun _ _ _ => by simp)
  filter_upwards [h, hW.zero] with ω hω h0
  have e0 : gbmF lam mu x0 φ 0 (W 0 ω) = φ x0 := by simp [gbmF, gbmMap, h0]
  show gbmF lam mu x0 φ t (W t ω) - φ x0 = _
  rw [← e0, hω]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [geomBM_eq_gbmMap]
  exact gbm_generator_eq lam mu x0 s (W s ω)

/-- **Dynkin's formula for geometric Brownian motion** (`φ ∈ C²_c`, deterministic `x₀`):
`E φ(X(t)) = φ(x₀) + E ∫₀ᵗ (λ X φ'(X) + ½ μ² X² φ''(X)) ds`. -/
theorem gbm_dynkin (hφ : IsC2c φ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, φ (geomBM lam mu (fun _ => x0) W t ω) ∂P = φ x0 +
      ∫ ω, (∫ s in (0 : ℝ)..t,
        itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ s (geomBM lam mu (fun _ => x0) W s ω)) ∂P := by
  have := hW.isProbabilityMeasure
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [intervalIntegral.integral_same, integral_zero, add_zero]
    rw [integral_congr_ae (g := fun _ => φ x0) (by
      filter_upwards [hW.zero] with ω hω
      simp [geomBM, hω])]
    simp
  obtain ⟨C0, -, -, hC0, -⟩ := exists_c2BddDeriv_of_hasCompactSupport hφ.contDiff
    hφ.hasCompactSupport
  have hG := isItoIntegrand_gbmNoise lam mu x0 hW hφ t hWj
  have hI := (memLp_itoInt hW hG).integrable one_le_two
  have hXm : Measurable fun ω => geomBM lam mu (fun _ => x0) W t ω :=
    (continuous_gbmMap lam mu x0).measurable.comp (measurable_const.prodMk (hW.measurable t))
  have hφX : Integrable (fun ω => φ (geomBM lam mu (fun _ => x0) W t ω)) P :=
    Integrable.of_bound (hφ.contDiff.continuous.measurable.comp hXm).aestronglyMeasurable C0
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC0 _)
  have h := gbm_ito_formula lam mu x0 hW hWj hφ hpos
  set D : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..t,
    itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ s (geomBM lam mu (fun _ => x0) W s ω)
  have hDe : D =ᵐ[P] fun ω => (φ (geomBM lam mu (fun _ => x0) W t ω) - φ x0) -
      itoInt W 𝓕 P t (fun s ω => (fun _ _ => (1 : ℝ)) s ω * gbmFx lam mu x0 φ s (W s ω)) ω := by
    filter_upwards [h] with ω hω
    rw [hω]; ring
  have hD : Integrable D P := ((hφX.sub (integrable_const _)).sub hI).congr hDe.symm
  have hmean := itoInt_mean hW hG
  have e := integral_congr_ae h
  rw [integral_sub hφX (integrable_const _), integral_add hD hI, hmean] at e
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, add_zero] at e
  linarith

/-- **The weak Fokker–Planck equation for geometric Brownian motion**, integrated form:
`∫ φ dμ_t = φ(x₀) + ∫₀ᵗ (∫ L φ dμ_s) ds`, `μ_t` the law of `X(t)`, `φ ∈ C²_c`. -/
theorem gbm_weakFP_integrated (hφ : IsC2c φ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y, φ y ∂(lawAt P (geomBM lam mu (fun _ => x0) W) t) = φ x0 +
      ∫ s in (0 : ℝ)..t, ∫ y, itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ s y
        ∂(lawAt P (geomBM lam mu (fun _ => x0) W) s) := by
  have := hW.isProbabilityMeasure
  have hXm : ∀ s, Measurable fun ω => geomBM lam mu (fun _ => x0) W s ω := fun s =>
    (continuous_gbmMap lam mu x0).measurable.comp (measurable_const.prodMk (hW.measurable s))
  have hLc : Continuous fun p : ℝ × ℝ =>
      itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ p.1 p.2 :=
    continuous_itoGen (a := fun z _ => lam * z) (b := fun z _ => mu * z)
      (continuous_const.mul continuous_fst) (continuous_const.mul continuous_fst) hφ.contDiff
  rw [integral_lawAt (hXm t) hφ.contDiff.continuous, gbm_dynkin lam mu x0 hW hWj hφ ht]
  congr 1
  have e : (∫ s in (0 : ℝ)..t, ∫ y, itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ s y
      ∂(lawAt P (geomBM lam mu (fun _ => x0) W) s)) = ∫ s in (0 : ℝ)..t, ∫ ω,
        itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ s (geomBM lam mu (fun _ => x0) W s ω)
          ∂P :=
    intervalIntegral.integral_congr fun s _ =>
      integral_lawAt (hXm s) (hLc.comp ((continuous_const (y := s)).prodMk continuous_id))
  rw [e]
  -- `L φ` is bounded (compact support of `φ'`, `φ''`)
  obtain ⟨C1, hC1⟩ := exists_bound_mul_pow hφ.continuous_deriv hφ.hasCompactSupport.deriv 1
  obtain ⟨C2, hC2⟩ := exists_bound_mul_pow hφ.continuous_deriv2
    hφ.hasCompactSupport.deriv.deriv 2
  have hLb : ∀ s y, |itoGen (fun z _ => lam * z) (fun z _ => mu * z) φ s y| ≤
      |lam| * C1 + mu ^ 2 / 2 * C2 := by
    intro s y
    have h1 := hC1 y
    have h2 := hC2 y
    simp only [pow_one] at h1
    rw [itoGen_gbm]
    have e : lam * y * deriv φ y + (mu * y) ^ 2 / 2 * deriv (deriv φ) y =
        lam * (deriv φ y * y) + mu ^ 2 / 2 * (deriv (deriv φ) y * y ^ 2) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    · rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hgm : Measurable (Function.uncurry fun s ω => itoGen (fun z _ => lam * z)
      (fun z _ => mu * z) φ s (geomBM lam mu (fun _ => x0) W s ω)) := by
    have hX : Measurable fun p : ℝ × Ω => geomBM lam mu (fun _ => x0) W p.1 p.2 :=
      (continuous_gbmMap lam mu x0).measurable.comp (measurable_fst.prodMk hWj)
    exact hLc.measurable.comp (measurable_fst.prodMk hX)
  refine (intervalIntegral_integral_swap ?_).symm
  rw [uIoc_of_le ht]
  exact Integrable.of_bound hgm.aestronglyMeasurable _
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hLb p.1 _)

end GBM

section WienerMartingale

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **The martingale problem for `W`, Mathlib form** (instance of
`martingale_itoDynkinProc_clamp`): if every path of `W` is continuous, then
`φ(W(t∧T)) - φ(W(0)) - ∫₀^{t∧T} ½ φ''(W(s)) ds` (frozen at `0` for `t < 0`) is an
`𝓕`-martingale. -/
theorem wiener_martingale_clamp (hWj : Measurable (Function.uncurry W))
    (hWc : ∀ ω, Continuous fun t => W t ω) {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ} {C1 C2 : ℝ}
    (hf : C2BddDeriv f C1 C2) :
    Martingale (fun t => itoDynkinProc (fun _ _ => 0) (fun _ _ => 1) f W (max 0 (min t T))) 𝓕 P :=
  martingale_itoDynkinProc_clamp hW hT (hW.isItoProcess_W hWj T) zero_le_one (fun _ _ _ => by simp)
    hf hWc continuous_const continuous_const

end WienerMartingale

end Gardiner.Ito.Generator
