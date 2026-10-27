/-
# Examples: Ornstein–Uhlenbeck, the Wiener process, and `dx = -sin x dt + σ dW`

* **Ornstein–Uhlenbeck** `dx = -k x dt + √D dW` (Gardiner §4.4.4):
  - `ou_density_fokkerPlanck`: the Gaussian density with mean `x₀ e^{-kt}` and variance
    `D(1 - e^{-2kt})/(2k)` solves the Fokker–Planck equation `∂ₜp = ∂_y(k y p) + ½ D ∂²_y p`
    explicitly; `ou_stationary_fokkerPlanck`: the stationary density `N(0, D/2k)` is a stationary
    solution;
  - `ou_dynkin`, `ou_weakFP`, `ou_isMartingaleOn`: Dynkin's formula, the weak Fokker–Planck
    equation and the martingale problem for every solution of the OU SDE.
* **The Wiener process** as the solution of `dx = dW` (`isSDESol_wiener`), and
  `wiener_strongFP`: an instance of the strong Fokker–Planck theorem `IsSDESol.strongFP` with all
  its hypotheses verified (the law of `W(t)` is `N(0, t)`, whose density is the heat kernel).
* **A nonlinear SDE** `dx = -sin x dt + σ dW`: `sin_dynkin`, `sin_weakFP`, `sin_weakFP_integrated`,
  `sin_isMartingaleOn`, and the instances `sinSDE_exists_dynkin_weakFP` (a solution exists and
  satisfies Dynkin's formula and the weak Fokker–Planck equation).
-/
import SHSLib.Gardiner.Ito.Generator.Gaussian
import SHSLib.Gardiner.Ito.StochDE.Examples
import SHSLib.Gardiner.Ito.Calculus.ItoGeneralExamples

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.Generator

open Gardiner.Ito Gardiner.Ito.StochDE

/-! ### Ornstein–Uhlenbeck: the explicit Gaussian density -/

/-- Mean of the OU process started at `x₀`: `x₀ e^{-kt}` (Gardiner (4.4.30)). -/
def ouMean (k x0 t : ℝ) : ℝ := x0 * exp (-k * t)

/-- Variance of the OU process started at a deterministic point: `D (1 - e^{-2kt}) / (2k)`
(Gardiner (4.4.31) with `σ² = D`). -/
def ouVar (k D t : ℝ) : ℝ := D / (2 * k) * (1 - exp (-2 * k * t))

/-- The OU generator: `L φ (y) = -k y φ'(y) + ½ D φ''(y)`. -/
lemma itoGen_ou (k : ℝ) {D : ℝ} (hD : 0 ≤ D) (φ : ℝ → ℝ) (t y : ℝ) :
    itoGen (fun z _ => -k * z) (fun _ _ => √D) φ t y =
      -k * y * deriv φ y + D / 2 * deriv (deriv φ) y := by
  simp [itoGen, Real.sq_sqrt hD]

lemma ouVar_pos {k D t : ℝ} (hk : 0 < k) (hD : 0 < D) (ht : 0 < t) : 0 < ouVar k D t := by
  unfold ouVar
  have : exp (-2 * k * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h2 : 0 < D / (2 * k) := by positivity
  nlinarith

/-- **The Gaussian density of the OU process solves the Fokker–Planck equation**: with
`m(t) = x₀ e^{-kt}`, `v(t) = D(1 - e^{-2kt})/(2k)`, `p(t, y) = N(m(t), v(t))(y)` satisfies
`∂ₜp = -∂_y[(-k y) p] + ½ ∂²_y[D p]` for `t > 0`. -/
theorem ou_density_fokkerPlanck {k D : ℝ} (x0 : ℝ) (hk : 0 < k) (hD : 0 < D) {t : ℝ}
    (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun s => gaussDens (ouMean k x0 s) (ouVar k D s) y)
      (itoFPRHS (fun z _ => -k * z) (fun _ _ => √D)
        (fun s z => gaussDens (ouMean k x0 s) (ouVar k D s) z) t y) t := by
  have hm : HasDerivAt (ouMean k x0) (-k * ouMean k x0 t) t := by
    have := ((hasDerivAt_id t).const_mul (-k)).exp.const_mul x0
    convert this using 1
    simp only [ouMean, id, mul_one]; ring
  have hv : HasDerivAt (ouVar k D) (D - 2 * k * ouVar k D t) t := by
    have := (((hasDerivAt_id t).const_mul (-2 * k)).exp.const_sub 1).const_mul (D / (2 * k))
    convert this using 1
    simp only [ouVar, id, mul_one]
    field_simp
    ring
  exact gaussDens_fokkerPlanck_linear hD.le hm hv (ouVar_pos hk hD ht) y

/-- **The stationary OU density** `N(0, D/(2k))` is a stationary solution of the Fokker–Planck
equation: the right-hand side of (4.3.20) vanishes. -/
theorem ou_stationary_fokkerPlanck {k D : ℝ} (hk : 0 < k) (hD : 0 < D) (t y : ℝ) :
    itoFPRHS (fun z _ => -k * z) (fun _ _ => √D) (fun _ z => gaussDens 0 (D / (2 * k)) z) t y =
      0 := by
  have hm : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-k * 0) t := by
    simpa using hasDerivAt_const t (0 : ℝ)
  have hv : HasDerivAt (fun _ : ℝ => D / (2 * k)) (D - 2 * k * (D / (2 * k))) t := by
    have : D - 2 * k * (D / (2 * k)) = 0 := by field_simp; ring
    rw [this]; exact hasDerivAt_const t _
  have h := gaussDens_fokkerPlanck_linear (m := fun _ => 0) (v := fun _ => D / (2 * k)) hD.le hm hv
    (by positivity) y
  exact (h.unique (hasDerivAt_const t _)).symm ▸ rfl

/-! ### Ornstein–Uhlenbeck: Dynkin, weak Fokker–Planck, martingale problem -/

lemma continuous_ou_drift (k : ℝ) : Continuous (Function.uncurry fun (z : ℝ) (_ : ℝ) => -k * z) :=
  continuous_const.mul continuous_fst

lemma continuous_const_coeff (σ : ℝ) : Continuous (Function.uncurry fun (_ _ : ℝ) => σ) :=
  continuous_const

lemma continuous_sin_drift : Continuous (Function.uncurry fun (z : ℝ) (_ : ℝ) => -Real.sin z) :=
  (Real.continuous_sin.comp continuous_fst).neg

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

section OU

variable {k D T : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ}

/-- **Dynkin's formula for the OU process**: for every solution of `dx = -k x dt + √D dW` on
`[0, T]` with `E ξ² < ∞` and `f ∈ C²` with bounded `f'`, `f''`,
`E f(x(t)) = E f(x(s)) + E ∫ₛᵗ (-k x f'(x) + ½ D f''(x)) du`. -/
theorem ou_dynkin (hD : 0 ≤ D) (hx : IsSDESol W 𝓕 P (fun z _ => -k * z) (fun _ _ => √D) 0 T ξ x)
    (hξ : MemLp ξ 2 P) {f : ℝ → ℝ} {C1 C2 : ℝ} (hf : C2BddDeriv f C1 C2) {s t : ℝ} (hs0 : 0 ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) :
    ∫ ω, f (x t ω) ∂P = ∫ ω, f (x s ω) ∂P +
      ∫ ω, (∫ u in s..t, (-k * x u ω * deriv f (x u ω) + D / 2 * deriv (deriv f) (x u ω))) ∂P := by
  have h := IsSDESol.dynkin hW hx (sdeCoeffs_ou k (√D) 0 T) hξ (continuous_ou_drift k)
    (continuous_const_coeff _) (B := √D) (fun _ _ => (abs_of_nonneg (Real.sqrt_nonneg D)).le) hf
    hs0 hst htT
  simpa only [itoGen_ou k hD] using h

/-- **The weak Fokker–Planck equation for the OU process**: for `φ ∈ C²_c`,
`d/dt ∫ φ dμ_t = ∫ (-k y φ'(y) + ½ D φ''(y)) dμ_t(y)` on `[0, T]`. -/
theorem ou_weakFP (hD : 0 ≤ D) (hx : IsSDESol W 𝓕 P (fun z _ => -k * z) (fun _ _ => √D) 0 T ξ x)
    {φ : ℝ → ℝ} (hφ : IsC2c φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => ∫ y, φ y ∂(lawAt P x s))
      (∫ y, (-k * y * deriv φ y + D / 2 * deriv (deriv φ) y) ∂(lawAt P x t)) (Icc 0 T) t := by
  have h := IsSDESol.weakFP_hasDerivWithinAt hW hx (sdeCoeffs_ou k (√D) 0 T)
    (continuous_ou_drift k) (continuous_const_coeff _) (B := √D)
    (fun _ _ => (abs_of_nonneg (Real.sqrt_nonneg D)).le) hφ ht
  simpa only [itoGen_ou k hD] using h

/-- **The martingale problem for the OU process.** -/
theorem ou_isMartingaleOn (hT : 0 ≤ T)
    (hx : IsSDESol W 𝓕 P (fun z _ => -k * z) (fun _ _ => √D) 0 T ξ x) {f : ℝ → ℝ} {C1 C2 : ℝ}
    (hf : C2BddDeriv f C1 C2) :
    IsMartingaleOn (itoDynkinProc (fun z _ => -k * z) (fun _ _ => √D) f x) 𝓕 P T :=
  IsSDESol.isMartingaleOn_itoDynkinProc hW hx hT (sdeCoeffs_ou k (√D) 0 T)
    (continuous_ou_drift k) (continuous_const_coeff _) (B := √D)
    (fun _ _ => (abs_of_nonneg (Real.sqrt_nonneg D)).le) hf

end OU

/-! ### A nonlinear SDE: `dx = -sin x dt + σ dW` -/

section Sin

variable {σ T : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ}

omit hW in
/-- The generator of `dx = -sin x dt + σ dW`: `L φ (y) = -sin y φ'(y) + ½ σ² φ''(y)`. -/
lemma itoGen_sin (σ : ℝ) (φ : ℝ → ℝ) (t y : ℝ) :
    itoGen (fun z _ => -Real.sin z) (fun _ _ => σ) φ t y =
      -Real.sin y * deriv φ y + σ ^ 2 / 2 * deriv (deriv φ) y := rfl

omit hW in
lemma abs_const_coeff_le (σ : ℝ) : ∀ y t : ℝ, |(fun (_ _ : ℝ) => σ) y t| ≤ |σ| :=
  fun _ _ => le_rfl

/-- **Dynkin's formula for `dx = -sin x dt + σ dW`**. -/
theorem sin_dynkin (hx : IsSDESol W 𝓕 P (fun z _ => -Real.sin z) (fun _ _ => σ) 0 T ξ x)
    (hξ : MemLp ξ 2 P) {f : ℝ → ℝ} {C1 C2 : ℝ} (hf : C2BddDeriv f C1 C2) {s t : ℝ} (hs0 : 0 ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) :
    ∫ ω, f (x t ω) ∂P = ∫ ω, f (x s ω) ∂P +
      ∫ ω, (∫ u in s..t, (-Real.sin (x u ω) * deriv f (x u ω) +
        σ ^ 2 / 2 * deriv (deriv f) (x u ω))) ∂P :=
  IsSDESol.dynkin hW hx (sdeCoeffs_sin σ 0 T) hξ continuous_sin_drift (continuous_const_coeff σ)
    (abs_const_coeff_le σ) hf hs0 hst htT

/-- **The weak Fokker–Planck equation for `dx = -sin x dt + σ dW`**:
`d/dt ∫ φ dμ_t = ∫ (-sin y φ'(y) + ½ σ² φ''(y)) dμ_t(y)` on `[0, T]`, `φ ∈ C²_c`. -/
theorem sin_weakFP (hx : IsSDESol W 𝓕 P (fun z _ => -Real.sin z) (fun _ _ => σ) 0 T ξ x)
    {φ : ℝ → ℝ} (hφ : IsC2c φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => ∫ y, φ y ∂(lawAt P x s))
      (∫ y, (-Real.sin y * deriv φ y + σ ^ 2 / 2 * deriv (deriv φ) y) ∂(lawAt P x t))
      (Icc 0 T) t :=
  IsSDESol.weakFP_hasDerivWithinAt hW hx (sdeCoeffs_sin σ 0 T) continuous_sin_drift
    (continuous_const_coeff σ) (abs_const_coeff_le σ) hφ ht

/-- **The weak Fokker–Planck equation for `dx = -sin x dt + σ dW`, integrated form.** -/
theorem sin_weakFP_integrated
    (hx : IsSDESol W 𝓕 P (fun z _ => -Real.sin z) (fun _ _ => σ) 0 T ξ x) {φ : ℝ → ℝ}
    (hφ : IsC2c φ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ y, φ y ∂(lawAt P x t) - ∫ y, φ y ∂(lawAt P x 0) =
      ∫ s in (0 : ℝ)..t,
        ∫ y, (-Real.sin y * deriv φ y + σ ^ 2 / 2 * deriv (deriv φ) y) ∂(lawAt P x s) :=
  IsSDESol.weakFP_integrated hW hx (sdeCoeffs_sin σ 0 T) continuous_sin_drift
    (continuous_const_coeff σ) (abs_const_coeff_le σ) hφ ht0 htT

/-- **The martingale problem for `dx = -sin x dt + σ dW`.** -/
theorem sin_isMartingaleOn (hT : 0 ≤ T)
    (hx : IsSDESol W 𝓕 P (fun z _ => -Real.sin z) (fun _ _ => σ) 0 T ξ x) {f : ℝ → ℝ}
    {C1 C2 : ℝ} (hf : C2BddDeriv f C1 C2) :
    IsMartingaleOn (itoDynkinProc (fun z _ => -Real.sin z) (fun _ _ => σ) f x) 𝓕 P T :=
  IsSDESol.isMartingaleOn_itoDynkinProc hW hx hT (sdeCoeffs_sin σ 0 T) continuous_sin_drift
    (continuous_const_coeff σ) (abs_const_coeff_le σ) hf

/-- **Instance**: for every square-integrable `𝓕 0`-measurable initial value, the nonlinear SDE
`dx = -sin x dt + σ dW` has a solution on `[0, T]`, and that solution satisfies Dynkin's formula,
the weak Fokker–Planck equation and the martingale problem. -/
theorem sinSDE_exists_dynkin_weakFP (hT : 0 ≤ T) (σ : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) :
    ∃ x, IsSDESol W 𝓕 P (fun z _ => -Real.sin z) (fun _ _ => σ) 0 T x0 x ∧
      (∀ (f : ℝ → ℝ) (C1 C2 : ℝ), C2BddDeriv f C1 C2 → ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
        ∫ ω, f (x t ω) ∂P = ∫ ω, f (x s ω) ∂P +
          ∫ ω, (∫ u in s..t, itoGen (fun z _ => -Real.sin z) (fun _ _ => σ) f u (x u ω)) ∂P) ∧
      (∀ φ, IsC2c φ → ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => ∫ y, φ y ∂(lawAt P x s))
          (∫ y, itoGen (fun z _ => -Real.sin z) (fun _ _ => σ) φ t y ∂(lawAt P x t)) (Icc 0 T) t) ∧
      (∀ (f : ℝ → ℝ) (C1 C2 : ℝ), C2BddDeriv f C1 C2 →
        IsMartingaleOn (itoDynkinProc (fun z _ => -Real.sin z) (fun _ _ => σ) f x) 𝓕 P T) := by
  obtain ⟨x, hx, -⟩ := sinSDE_existsUnique hW hT σ hx0 hx02
  exact ⟨x, hx, fun f C1 C2 hf s t hs hst htT => sin_dynkin hW hx hx02 hf hs hst htT,
    fun φ hφ t ht => sin_weakFP hW hx hφ ht, fun f C1 C2 hf => sin_isMartingaleOn hW hT hx hf⟩

end Sin

/-! ### The Wiener process: an instance of the strong Fokker–Planck theorem -/

section Wiener

omit hW in
/-- The coefficients `a = 0`, `b = 1` of `dx = dW` satisfy (4.3.10)–(4.3.11) with `K = 1`. -/
lemma sdeCoeffs_wiener (t₀ T : ℝ) : SDECoeffs (fun _ _ => 0) (fun _ _ => 1) t₀ T 1 where
  measurable_a := measurable_const
  measurable_b := measurable_const
  K_nonneg := zero_le_one
  lipschitz t _ x y := by simp
  growth t _ x := by simp; positivity

/-- **The Wiener process solves `dx = dW`, `x(0) = 0`** on every `[0, T]`. -/
theorem isSDESol_wiener (hWj : Measurable (Function.uncurry W)) (T : ℝ) :
    IsSDESol W 𝓕 P (fun _ _ => 0) (fun _ _ => 1) 0 T (fun _ => 0) W := by
  have := hW.isProbabilityMeasure
  have had : ∀ t ∈ Icc (0 : ℝ) T, StronglyMeasurable[𝓕 t] (W t) := fun t ht => hW.adapted t ht.1
  have hsq := sq_int_of_memLp_tsMeasure hWj (hW.isItoIntegrand_W hWj T).memLp
  refine ⟨hWj, had, hW.cont.mono fun ω h => h.continuousOn, hsq, fun t ht => ?_⟩
  have hD := isItoIntegrand_drive (sdeCoeffs_wiener 0 T) le_rfl hWj had hsq
  have h1 := itoInt_congr_of_eq_on hW (hD.mono ht.2)
    (isItoIntegrand_det (𝓕 := 𝓕) (P := P) t (continuous_const (y := (1 : ℝ))))
    (fun s hs ω => by simp [drive, afterInd_of_lt hs.1])
  filter_upwards [h1, hW.itoInt_one hWj ht.1, hW.zero] with ω e1 e2 e3
  simp only [intervalIntegral.integral_zero, zero_add]
  rw [e1, e2, e3, sub_zero]

/-- Time derivative of the heat kernel `gaussDens 0 s z`. -/
def heatKernelDt (s z : ℝ) : ℝ :=
  gaussDens 0 s z * ((z - 0) * 0 / s + 1 / (2 * s) * ((z - 0) ^ 2 / s - 1))

omit hW in
lemma hasDerivAt_heatKernel {s : ℝ} (hs : 0 < s) (z : ℝ) :
    HasDerivAt (fun s => gaussDens 0 s z) (heatKernelDt s z) s := by
  have := hasDerivAt_gaussDens_t (m := fun _ => 0) (v := id) (hasDerivAt_const s 0)
    (hasDerivAt_id s) hs z
  simpa [heatKernelDt] using this

omit hW in
lemma continuousOn_heatKernelDt (T : ℝ) :
    ContinuousOn (Function.uncurry heatKernelDt) (Ioo 0 T ×ˢ univ) := by
  refine continuousOn_of_forall_continuousAt fun p hp => ?_
  have hs : 0 < p.1 := hp.1.1
  have h1 : √(2 * π * p.1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  show ContinuousAt (fun p : ℝ × ℝ => heatKernelDt p.1 p.2) p
  unfold heatKernelDt gaussDens
  fun_prop (disch := first | exact hs.ne' | exact h1 | positivity)

/-- **Instance of the strong Fokker–Planck theorem** (`IsSDESol.strongFP`): the law of `W(t)`,
`t ∈ (0, T)`, has the heat-kernel density `p(t, y) = N(0, t)(y)`, all regularity hypotheses
hold, and the theorem yields the heat equation `∂ₜp = ½ ∂²_y p`, i.e. (4.3.20) with `a = 0`,
`b = 1`. -/
theorem wiener_strongFP (hWj : Measurable (Function.uncurry W)) {T t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (y : ℝ) :
    heatKernelDt t y = itoFPRHS (fun _ _ => 0) (fun _ _ => 1) (fun s z => gaussDens 0 s z) t y := by
  refine IsSDESol.strongFP hW (isSDESol_wiener hW hWj T) (sdeCoeffs_wiener 0 T)
    continuous_const continuous_const (B := 1) (fun _ _ => by simp)
    (fun s _ z => gaussDens_nonneg 0 s z) (fun s hs => ?_)
    (fun s _ => (contDiff_gaussDens 0 s (n := 0)).continuous)
    (fun s hs z => hasDerivAt_heatKernel hs.1 z) (continuousOn_heatKernelDt T)
    (fun s _ => by simpa using (contDiff_const (c := (0 : ℝ))))
    (fun s _ => by simpa using (contDiff_gaussDens 0 s (n := 2))) ht y
  have := hW.isProbabilityMeasure
  have hs0 : s.toNNReal ≠ 0 := by simpa using hs.1
  simp only [lawAt]
  rw [hW.map_eval hs.1.le, gaussianReal_of_var_ne_zero 0 hs0]
  congr 1
  funext z
  rw [gaussianPDF, ← gaussDens_eq_gaussianPDFReal, Real.coe_toNNReal _ hs.1.le]

end Wiener

end Gardiner.Ito.Generator
