/-
# Concrete instances for the SDE small-noise and numerics layer

Every main theorem of `SHSLib.Gardiner.SDE` is applied here (or next to its statement) to a
concrete, non-degenerate instance.

* **Driving noise exists.**  An i.i.d. sequence of `N(0, τ)` increments exists on some probability
  space (`Gardiner.SDE.exists_gaussian_increments`), so the hypotheses of the weak-error and
  mean-square theorems are satisfiable.
* **Weak error, Ornstein–Uhlenbeck** `dx = -x dt + dW`, `x(0) = 1`: Euler and semi-implicit
  second moments are within `(19/2)Tτ` and `(29/2)Tτ` of the exact `⟨x²⟩(T)`
  (`Gardiner.SDE.ou_weak_instance`).
* **Weak error, multiplicative noise** `dx = -x dt + x dW`, `x(0) = 1`: Euler, Milstein and
  semi-implicit means and second moments (`Gardiner.SDE.gbm_weak_instance`).
* **Mean-square stability** of the same equation: Euler and Milstein second moments decay iff
  `τ < 1`, resp. `τ < 2/3`; drift-implicit Euler decays for every `τ > 0`
  (`Gardiner.SDE.gbm_ms_instance`).
* **Linearisation (6.2.9)–(6.2.13) for the cubic process**: `|x - εw| ≤ C ε²`
  (`Gardiner.SDE.cubic_linearisation`), an instance of `Gardiner.SDE.linearisation_error`.
* **Statistics (6.2.25)–(6.2.35)** for the linearised OU process `k = b = 1`
  (`Gardiner.SDE.linearised_ou_statistics`), and the mean expansion
  (`Gardiner.SDE.mean_expansion_instance`).
* **Error recursions (10.1.24)–(10.1.29)** at `A = B = C = D = P = 1`
  (`Gardiner.SDE.error_recursion_instance`).
-/
import SHSLib.Gardiner.SDE.Vector
import SHSLib.Gardiner.SDE.Stability
import SHSLib.Gardiner.SDE.Statistics
import SHSLib.Gardiner.SDE.Cubic

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

noncomputable section

namespace Gardiner.SDE

/-- An i.i.d. sequence of `N(0, τ)` increments exists. -/
theorem exists_gaussian_increments (τ : ℝ≥0) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ ξ : ℕ → Ω → ℝ,
      IsProbabilityMeasure P ∧ (∀ n, Measurable (ξ n)) ∧ iIndepFun ξ P ∧
      ∀ n, P.map (ξ n) = gaussianReal 0 τ := by
  obtain ⟨Ω, mΩ, P, ξ, hm, hlaw, hind, hP⟩ := exists_iid ℕ (gaussianReal 0 τ)
  exact ⟨Ω, mΩ, P, ξ, hP, hm, hind, fun n => (hlaw n).map_eq⟩

section Weak

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : ℝ≥0} {ξ : ℕ → Ω → ℝ}

/-- **Instance: Ornstein–Uhlenbeck `dx = -x dt + dW`, `x(0) = 1`, step `τ ≤ 1/2`.**  With
`T = Nτ`, the Euler and semi-implicit second moments satisfy
`|⟨y_N²⟩ - ⟨x²⟩(T)| ≤ (19/2)Tτ`, resp. `(29/2)Tτ`, and the Euler mean is within `T e^T τ` of
`e^{-T}`. -/
theorem ou_weak_instance (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hτ : (τ : ℝ) ≤ 1 / 2) (N : ℕ) :
    |∫ ω, linScheme (eulerOU 1 1 τ) 1 ξ N ω ^ 2 ∂P - ouSecond 1 1 1 (N * τ)| ≤
        19 / 2 * (N * τ) * τ ∧
    |∫ ω, linScheme (semiOU 1 1 τ) 1 ξ N ω ^ 2 ∂P - ouSecond 1 1 1 (N * τ)| ≤
        29 / 2 * (N * τ) * τ ∧
    |∫ ω, linScheme (eulerOU 1 1 τ) 1 ξ N ω ∂P - ouMean 1 1 (N * τ)| ≤
        (N * τ) * Real.exp (N * τ) * τ := by
  have hτ0 : (0 : ℝ) ≤ τ := τ.2
  refine ⟨?_, ?_, ?_⟩
  · have h := eulerOU_weak_second hξm hind hlaw (γ := 1) (σ := 1) (x0 := 1) one_pos
      (by linarith) N
    calc _ ≤ _ := h
      _ = _ := by ring
  · have h := semiOU_weak_second hξm hind hlaw (γ := 1) (σ := 1) (x0 := 1) one_pos
      (by linarith) N
    calc _ ≤ _ := h
      _ = _ := by ring
  · have h := eulerOU_weak_mean hξm hind hlaw (γ := 1) (σ := 1) (x0 := 1) (by linarith)
      (by rw [one_mul, abs_of_nonneg hτ0]; linarith) N
    calc _ ≤ _ := h
      _ = _ := by simp

/-- **Instance: multiplicative noise `dx = -x dt + x dW`, `x(0) = 1`, step `τ ≤ 1`.**  Exact
moments `⟨x⟩ = e^{-T}`, `⟨x²⟩ = e^{-T}`; the Euler, Milstein and semi-implicit schemes are weakly
first order with the explicit constants below. -/
theorem gbm_weak_instance (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hτ : (τ : ℝ) ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (eulerGBM (-1) 1 τ) 1 ξ N ω ∂P - gbmMean (-1) 1 (N * τ)| ≤
        (N * τ) * Real.exp (N * τ) * τ ∧
    |∫ ω, linScheme (eulerGBM (-1) 1 τ) 1 ξ N ω ^ 2 ∂P - gbmSecond (-1) 1 1 (N * τ)| ≤
        2 * (N * τ) * Real.exp (2 * (N * τ)) * τ ∧
    |∫ ω, linScheme (milsteinGBM (-1) 1 τ) 1 ξ N ω ^ 2 ∂P - gbmSecond (-1) 1 1 (N * τ)| ≤
        5 / 2 * (N * τ) * Real.exp (5 / 2 * (N * τ)) * τ ∧
    |∫ ω, linScheme (semiGBM (-1) 1 τ) 1 ξ N ω ∂P - gbmMean (-1) 1 (N * τ)| ≤
        17 / 8 * (N * τ) * Real.exp (17 / 8 * (N * τ)) * τ := by
  have hτ0 : (0 : ℝ) ≤ τ := τ.2
  have h1 : |(-1 : ℝ) * τ| ≤ 1 := by rw [abs_mul, abs_of_nonneg hτ0]; norm_num; exact hτ
  have h2 : |(2 * (-1) + (1 : ℝ) ^ 2) * τ| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hτ0]; norm_num; exact hτ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := eulerGBM_weak_mean hξm hind hlaw (mu := 1) (x0 := 1) hτ h1 N
    calc _ ≤ _ := h
      _ = _ := by norm_num
  · have h := eulerGBM_weak_second hξm hind hlaw (x0 := 1) hτ h2 N
    calc _ ≤ _ := h
      _ = _ := by norm_num
  · have h := milsteinGBM_weak_second hξm hind hlaw (x0 := 1) hτ h2 N
    calc _ ≤ _ := h
      _ = _ := by norm_num
  · have h := semiGBM_weak_mean hξm hind hlaw (mu := 1) (x0 := 1) hτ h1 N
    calc _ ≤ _ := h
      _ = _ := by norm_num

/-- **Instance: mean-square stability of `dx = -x dt + x dW`** (`2λ + μ² = -1 < 0`).  With
`y₀ = 1`: Euler decays in mean square iff `τ < 1`, Milstein iff `τ < 2/3`, and drift-implicit
Euler for every `τ > 0`. -/
theorem gbm_ms_instance (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hτ : 0 < (τ : ℝ)) :
    (Tendsto (fun n => ∫ ω, linScheme (eulerGBM (-1) 1 τ) 1 ξ n ω ^ 2 ∂P) atTop (𝓝 0) ↔
      (τ : ℝ) < 1) ∧
    (Tendsto (fun n => ∫ ω, linScheme (milsteinGBM (-1) 1 τ) 1 ξ n ω ^ 2 ∂P) atTop (𝓝 0) ↔
      (τ : ℝ) < 2 / 3) ∧
    Tendsto (fun n => ∫ ω, linScheme (implicitGBM (-1) 1 τ) 1 ξ n ω ^ 2 ∂P) atTop (𝓝 0) := by
  refine ⟨?_, ?_, implicitGBM_ms_tendsto hξm hind hlaw hτ (by norm_num) 1⟩
  · rw [eulerGBM_ms_tendsto_iff hξm hind hlaw hτ one_ne_zero]
    constructor <;> intro h <;> nlinarith
  · rw [milsteinGBM_ms_tendsto_iff hξm hind hlaw hτ one_ne_zero]
    constructor <;> intro h <;> nlinarith

end Weak

/-! ### Small-noise expansion instances -/

/-- **Erratum (text after (6.2.13))**: it is `A₁`, not `A₀`, that vanishes: `a₁ = x₁a'(x₀)`, so
`A₁ = 0` identically. -/
theorem snA_one (D X : ℕ → ℝ) : snA D X 1 = 0 := by
  have h := snCoeff_split D X (n := 1) le_rfl
  rw [snCoeff_one] at h
  linarith

/-- Instance of (6.2.6): for `a = sin` at `x₀ = 0` (`a' = 1`, `a'' = 0`, `a''' = -1`),
`a₃ = x₃ - x₁³/6`. -/
example (X : ℕ → ℝ) :
    snCoeff (fun p => iteratedDeriv p Real.sin 0) X 3 = X 3 - X 1 ^ 3 / 6 := by
  rw [snCoeff_three]
  simp [iteratedDeriv_succ, Real.deriv_sin]
  ring

/-- A hierarchy solved up to order `N` is solved up to any lower order. -/
lemma IsHierarchy.mono {Da : ℕ → ℝ → ℝ} {w : ℝ → ℝ} {x0 : ℝ} {xs : ℕ → ℝ → ℝ} {N N' : ℕ}
    {T : ℝ} (h : IsHierarchy Da w x0 xs N T) (hN : N' ≤ N) : IsHierarchy Da w x0 xs N' T :=
  ⟨h.cont, fun n hn => h.eq n (hn.trans hN)⟩

/-- **Instance of `Gardiner.SDE.linearisation_error`: the cubic process**
`dx = -x³dt + ε dw`, `x(0) = 0`, driven by any continuous path with `|w(t) - w(0)| ≤ W` on
`[0, T]`: the linearised solution `εw` is within `C ε²` of the true path, uniformly on `[0, T]`. -/
theorem cubic_linearisation {ε T W : ℝ} (hε : |ε| ≤ 1) (hT : 0 < T) {w x : ℝ → ℝ}
    (hw : Continuous w) (hW : ∀ t ∈ Icc 0 T, |w t - w 0| ≤ W)
    (hx : IsPathSol (cubicD 0) ε w x T) (hx0 : x 0 = 0) :
    ∀ t ∈ Icc 0 T, |x t - (0 + ε * (w t - w 0))| ≤
      T * Real.exp (0 * T + 1 / 2) * (2 * (8 * W ^ 3 + 12 * W ^ 2 + 12 * W + 6) *
        Real.exp (2 * W)) * ε ^ 2 := by
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0 ⟨le_rfl, hT.le⟩)
  have hH : IsHierarchy cubicD w (x 0) (cubicHier w) 1 T := by
    rw [hx0]; exact (cubicHier_isHierarchy hw T).mono (by norm_num)
  have h := linearisation_error cubicD (fun k _ y => cubicD_hasDerivAt k y) cubicD_continuous
    (R := W) (M := 8 * W ^ 3 + 12 * W ^ 2 + 12 * W + 6) le_rfl cubic_osl hε hT hW0 hx hH (fun t ht => by simpa [cubicHier] using hW t ht)
    (fun p hp t _ z hz => by
      simp only [cubicHier, sub_zero] at hz
      have hz2 : z ^ 2 ≤ 4 * W ^ 2 := by
        have := sq_abs z ▸ pow_le_pow_left₀ (abs_nonneg z) hz 2; nlinarith
      interval_cases p
      · simp only [cubicD, abs_neg, abs_pow]
        have := pow_le_pow_left₀ (abs_nonneg z) hz 3
        nlinarith [sq_nonneg W, pow_nonneg hW0 3]
      · simp only [cubicD, abs_mul, abs_neg, abs_pow, sq_abs]
        norm_num; nlinarith [sq_nonneg W, pow_nonneg hW0 3]
      · simp only [cubicD, abs_mul, abs_neg]
        norm_num; nlinarith [sq_nonneg W, pow_nonneg hW0 3])
  intro t ht
  simpa [cubicHier] using h t ht

/-- **Instance: statistics of the linearised OU process `k = b = 1`** (6.2.25)–(6.2.35):
the variance is `(1 - e^{-2t})/2`, tends to the stationary value `1/2`, and if `x₁` has the law
of the linearised process its two-time correlation is `e^{-(t-s)}(1 - e^{-2s})/2`. -/
theorem linearised_ou_statistics {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ → Ω → ℝ} (hX : IsLinearisedLaw P X (fun _ => 1) (fun _ => 1)) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    linVar (fun _ => 1) (fun _ => 1) t = (1 - Real.exp (-2 * t)) / 2 ∧
    Tendsto (linVar (fun _ => 1) (fun _ => 1)) atTop (𝓝 (1 / 2)) ∧
    ∫ ω, X t ω * X s ω ∂P = Real.exp (-(t - s)) * ((1 - Real.exp (-2 * s)) / 2) := by
  have hv : ∀ u, linVar (fun _ => 1) (fun _ => 1) u = (1 - Real.exp (-2 * u)) / 2 := by
    intro u; rw [linVar_const one_ne_zero]; ring_nf
  refine ⟨hv t, ?_, ?_⟩
  · have := linVar_tendsto_stationary (k := 1) one_pos 1
    simpa using this
  · rw [hX.correlation_eq continuous_const hs hst, linCov, hv s]
    simp

/-- **Instance of `Gardiner.SDE.mean_expansion_of_pathwise`**: if `x = ε + ε²Z` with `|Z| ≤ 1`,
then `|⟨x⟩ - ε| ≤ ε²`. -/
theorem mean_expansion_instance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Integrable Z P) (hZ1 : ∀ ω, |Z ω| ≤ 1) (ε : ℝ) :
    |∫ ω, (ε + ε ^ 2 * Z ω) ∂P - ε| ≤ |ε| ^ 2 := by
  have h := mean_expansion_of_pathwise (P := P) (fun ω => ε + ε ^ 2 * Z ω) (fun _ => 1)
    (fun n _ => if n = 1 then 1 else 0) 1 ε
    ((integrable_const ε).add (hZ.const_mul _)) (fun n => integrable_const _) (integrable_const _)
    (Eventually.of_forall fun ω => by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
      norm_num
      exact mul_le_of_le_one_right (sq_nonneg _) (hZ1 ω))
  simpa [Finset.sum_range_succ] using h

/-- **Instance of the error-recursion bounds** (10.1.24)–(10.1.29) with `A = B = C = 1`,
`D = P = 1`, `τ = 1/10`: `v_N ≤ (e^{(31/10)T} - 1)/3 · τ` and `|m_N| ≤ (e^T - 1) τ`. -/
theorem error_recursion_instance (v m : ℕ → ℝ) (hv0 : v 0 = 0) (hm0 : m 0 = 0)
    (hv : ∀ n, v (n + 1) ≤ ((1 + 1 * (1 / 10)) ^ 2 + 1 * (1 / 10)) * v n + 1 * (1 / 10) ^ 2)
    (hm : ∀ n, |m (n + 1)| ≤ (1 + 1 * (1 / 10)) * |m n| + 1 * (1 / 10) ^ 2) (N : ℕ) :
    v N ≤ (Real.exp ((2 * 1 + 1 + 1 ^ 2 * (1 / 10)) * (N * (1 / 10))) - 1) / (2 * 1 + 1) *
      (1 * (1 / 10)) ∧
    |m N| ≤ (Real.exp (1 * (N * (1 / 10))) - 1) / 1 * (1 * (1 / 10)) :=
  ⟨(strong_error_bound (by norm_num) (by norm_num) (by norm_num) v hv0 hv N).2,
    mean_error_bound (by norm_num) (by norm_num) (by norm_num) m hm0 hm N⟩

/-- **Instance of `Gardiner.SDE.multipleIntegral_moments`** with `τ = 1`: on any probability
space carrying uncorrelated standard `ξ, η`, `⟨ΔWΔZ⟩ = 1/2` and `⟨ΔZ²⟩ = 1/3`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ η : Ω → ℝ}
    (hξ : Integrable ξ P) (hη : Integrable η P) (hξ2 : Integrable (fun ω => ξ ω ^ 2) P)
    (hη2 : Integrable (fun ω => η ω ^ 2) P) (hξη : Integrable (fun ω => ξ ω * η ω) P)
    (m1 : ∫ ω, ξ ω ∂P = 0) (m2 : ∫ ω, η ω ∂P = 0) (v1 : ∫ ω, ξ ω ^ 2 ∂P = 1)
    (v2 : ∫ ω, η ω ^ 2 ∂P = 1) (c : ∫ ω, ξ ω * η ω ∂P = 0) :
    ∫ ω, √1 * ξ ω * (1 / 2 * 1 * √1 * (ξ ω + η ω / √3)) ∂P = 1 / 2 ∧
      ∫ ω, (1 / 2 * 1 * √1 * (ξ ω + η ω / √3)) ^ 2 ∂P = 1 / 3 := by
  obtain ⟨-, h2, h3, -, -⟩ := multipleIntegral_moments (P := P) 1 zero_le_one hξ hη hξ2 hη2 hξη
    m1 m2 v1 v2 c
  exact ⟨by simpa using h2, by simpa using h3⟩

end Gardiner.SDE
