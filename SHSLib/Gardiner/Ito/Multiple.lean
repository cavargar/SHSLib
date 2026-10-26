import SHSLib.Gardiner.Ito.WienerIntegral
import SHSLib.Gardiner.SDE.Schemes
import SHSLib.Gardiner.SDE.GaussianMoments

/-!
# Multiple stochastic integrals (Gardiner §10.1, (10.1.9)–(10.1.12))

For a Wiener process `W` (`Gardiner.Ito.IsWiener`), `t ≥ 0` and `τ ≥ 0` let

  `ΔW = W(t+τ) - W(t)`  (`Gardiner.Ito.incrW`),
  `ΔZ = ∫_t^{t+τ} (W(s) - W(t)) ds = ∫_t^{t+τ} ds ∫_t^s dW(s')`  (`Gardiner.Ito.incrZ`).

`ΔZ` is a pathwise Riemann integral.  Integration by parts identifies both quantities with
Wiener integrals of deterministic functions:

* `ΔW = ∫_t^{t+τ} dW` and `ΔZ = ∫_t^{t+τ} (t + τ - s) dW(s)` a.s.
  (`Gardiner.Ito.IsWiener.incrW_ae`, `Gardiner.Ito.IsWiener.incrZ_ae`);
* the companion integral `∫_t^{t+τ} dW(s) ∫_t^s ds' = ∫_t^{t+τ} (s - t) dW(s) = τΔW - ΔZ` a.s.
  (`Gardiner.Ito.IsWiener.companion_ae`).

Consequently (`Gardiner.Ito.IsWiener.incr_hasGaussianLaw`, `…incr_lin_map`, `…incr_moments`)
`(ΔW, ΔZ)` is jointly Gaussian, centred, with covariance matrix

  `⟨ΔW²⟩ = τ`,  `⟨ΔW ΔZ⟩ = τ²/2`,  `⟨ΔZ²⟩ = τ³/3`.

For `τ > 0`, `ξ = ΔW/√τ` and `η = √3 (2ΔZ/τ^{3/2} - ξ)` (`Gardiner.Ito.xiN`, `Gardiner.Ito.etaN`)
are independent standard normals built from `W`, and `ΔW = √τ ξ`, `ΔZ = ½τ^{3/2}(ξ + η/√3)`
hold identically (`Gardiner.Ito.IsWiener.xi_eta_indep`, `Gardiner.Ito.incrW_eq_xi`,
`Gardiner.Ito.incrZ_eq_xi_eta`).  This discharges the hypotheses of the Itô-free theorem
`Gardiner.SDE.multipleIntegral_moments` (`Gardiner.Ito.IsWiener.multiple_moments`).

**Erratum (10.1.10)/(10.1.11).**  The printed (10.1.10) and (10.1.11) are identical.  The intended
pair is `ΔZ = ∫_t^{t+τ} ds ∫_t^s dW(s')` (10.1.10) and its companion
`∫_t^{t+τ} dW(s) ∫_t^s ds' = τΔW - ΔZ` (10.1.11); both are formalized above.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set intervalIntegral
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- The increment `ΔW = W(t+τ) - W(t)` (10.1.9). -/
def incrW (W : ℝ → Ω → ℝ) (t τ : ℝ) (ω : Ω) : ℝ := W (t + τ) ω - W t ω

/-- The double integral `ΔZ = ∫_t^{t+τ} ds ∫_t^s dW(s') = ∫_t^{t+τ} (W(s) - W(t)) ds` (10.1.10),
a pathwise Riemann integral. -/
def incrZ (W : ℝ → Ω → ℝ) (t τ : ℝ) (ω : Ω) : ℝ := ∫ s in t..t + τ, (W s ω - W t ω)

/-- The kernel `t + τ - s` representing `ΔZ` as a Wiener integral. -/
def kerZ (t τ s : ℝ) : ℝ := t + τ - s

lemma continuous_kerZ (t τ : ℝ) : Continuous (kerZ t τ) := by unfold kerZ; fun_prop

lemma integral_kerZ_quad (t τ a b c d : ℝ) :
    ∫ s in t..t + τ, (a + b * kerZ t τ s) * (c + d * kerZ t τ s) =
      a * c * τ + (a * d + b * c) * τ ^ 2 / 2 + b * d * τ ^ 3 / 3 := by
  have hF : ∀ s, HasDerivAt (fun s => a * c * s - (a * d + b * c) * (t + τ - s) ^ 2 / 2 -
      b * d * (t + τ - s) ^ 3 / 3) ((a + b * kerZ t τ s) * (c + d * kerZ t τ s)) s := by
    intro s
    have h1 : HasDerivAt (fun s => t + τ - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (t + τ)
    have := (((hasDerivAt_id s).const_mul (a * c)).sub (((h1.pow 2).const_mul
      (a * d + b * c)).div_const 2)).sub (((h1.pow 3).const_mul (b * d)).div_const 3)
    convert this using 1
    simp only [kerZ]
    norm_num
    ring
  rw [integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
    (((continuous_const.add (continuous_const.mul (continuous_kerZ t τ))).mul
      (continuous_const.add (continuous_const.mul (continuous_kerZ t τ)))).intervalIntegrable _ _)]
  ring

lemma integral_one_kerZ (t τ : ℝ) : ∫ s in t..t + τ, (fun _ => (1 : ℝ)) s * kerZ t τ s = τ ^ 2 / 2 := by
  simpa using integral_kerZ_quad t τ 1 0 0 1

lemma integral_kerZ_kerZ (t τ : ℝ) : ∫ s in t..t + τ, kerZ t τ s * kerZ t τ s = τ ^ 3 / 3 := by
  simpa using integral_kerZ_quad t τ 0 1 0 1

lemma integral_lin_kerZ_sq (t τ α β : ℝ) :
    ∫ s in t..t + τ, (α * 1 + β * kerZ t τ s) ^ 2 =
      α ^ 2 * τ + α * β * τ ^ 2 + β ^ 2 * τ ^ 3 / 3 := by
  simp only [mul_one, sq]
  rw [integral_kerZ_quad]
  ring

/-- A real random variable with law `N(0, v)` is square integrable with mean `0` and second moment
`v`. -/
lemma moments_of_map_gaussian {X : Ω → ℝ} {v : ℝ≥0} (hX : AEMeasurable X P)
    (h : P.map X = gaussianReal 0 v) :
    MemLp X 2 P ∧ ∫ ω, X ω ∂P = 0 ∧ ∫ ω, X ω ^ 2 ∂P = v := by
  refine ⟨?_, ?_, ?_⟩
  · have h' : MemLp id 2 (P.map X) := by rw [h]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id hX).mp h'
  · have := integral_map (μ := P) (f := fun x : ℝ => x) hX aestronglyMeasurable_id
    rw [h, integral_id_gaussianReal] at this
    exact this.symm
  · have := integral_map (μ := P) (f := fun x : ℝ => x ^ 2) hX
      (continuous_pow 2).aestronglyMeasurable
    rw [h, Gardiner.SDE.gauss_m2] at this
    exact this.symm

namespace IsWiener

variable (hW : IsWiener W P) {t τ : ℝ}
include hW

/-- `ΔW = ∫_t^{t+τ} dW` almost surely. -/
theorem incrW_ae (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    incrW W t τ =ᵐ[P] wienerInt W P (fun _ => 1) t (t + τ) :=
  (hW.wienerInt_one ht (by linarith)).symm

/-- **`ΔZ = ∫_t^{t+τ} (t + τ - s) dW(s)`** almost surely (integration by parts). -/
theorem incrZ_ae (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    incrZ W t τ =ᵐ[P] wienerInt W P (kerZ t τ) t (t + τ) := by
  have h := hW.wienerInt_ibp (f := kerZ t τ) (f' := fun _ => -1) (a := t) (b := t + τ)
    (fun s => by simpa [kerZ] using (hasDerivAt_id s).const_sub (t + τ)) continuous_const ht
    (by linarith)
  filter_upwards [h, hW.cont] with ω h1 hω
  rw [h1]
  simp only [kerZ, incrZ]
  rw [intervalIntegral.integral_sub (hω.intervalIntegrable _ _) _root_.intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [neg_one_mul, intervalIntegral.integral_neg, smul_eq_mul]
  ring

/-- **The companion integral (10.1.11), corrected**:
`∫_t^{t+τ} dW(s) ∫_t^s ds' = ∫_t^{t+τ} (s - t) dW(s) = τΔW - ΔZ` almost surely. -/
theorem companion_ae (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    wienerInt W P (fun s => s - t) t (t + τ) =ᵐ[P]
      fun ω => τ * incrW W t τ ω - incrZ W t τ ω := by
  have h := hW.wienerInt_ibp (f := fun s => s - t) (f' := fun _ => 1) (a := t) (b := t + τ)
    (fun s => by simpa using (hasDerivAt_id s).sub_const t) continuous_const ht (by linarith)
  filter_upwards [h, hW.cont] with ω h1 hω
  rw [h1]
  simp only [incrW, incrZ]
  rw [intervalIntegral.integral_sub (hω.intervalIntegrable _ _) _root_.intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [one_mul, smul_eq_mul]
  ring

lemma aemeasurable_incrW : AEMeasurable (incrW W t τ) P :=
  ((hW.measurable _).sub (hW.measurable _)).aemeasurable

lemma aemeasurable_incrZ (ht : 0 ≤ t) (hτ : 0 ≤ τ) : AEMeasurable (incrZ W t τ) P :=
  (hW.wienerInt_spec (continuous_kerZ t τ) ht (by linarith)).1.aestronglyMeasurable.aemeasurable
    |>.congr (hW.incrZ_ae ht hτ).symm

/-- **Every linear combination of `ΔW` and `ΔZ` is centred Gaussian**:
`αΔW + βΔZ ~ N(0, α²τ + αβτ² + β²τ³/3)`. -/
theorem incr_lin_map (ht : 0 ≤ t) (hτ : 0 ≤ τ) (α β : ℝ) :
    P.map (fun ω => α * incrW W t τ ω + β * incrZ W t τ ω) =
      gaussianReal 0 (α ^ 2 * τ + α * β * τ ^ 2 + β ^ 2 * τ ^ 3 / 3).toNNReal := by
  have hab : t ≤ t + τ := by linarith
  have h := hW.wienerInt_add_smul (f := fun _ => 1) (g := kerZ t τ) continuous_const
    (continuous_kerZ t τ) ht hab α β
  have hae : (fun ω => α * incrW W t τ ω + β * incrZ W t τ ω) =ᵐ[P]
      wienerInt W P (fun s => α * 1 + β * kerZ t τ s) t (t + τ) := by
    filter_upwards [h, hW.incrW_ae ht hτ, hW.incrZ_ae ht hτ] with ω h1 h2 h3
    rw [h1, h2, h3]
  rw [Measure.map_congr hae,
    hW.wienerInt_map (f := fun s => α * 1 + β * kerZ t τ s) (continuous_const.add (continuous_const.mul (continuous_kerZ t τ))) ht hab,
    integral_lin_kerZ_sq]

/-- **`(ΔW, ΔZ)` is jointly Gaussian** (10.1.9)–(10.1.10). -/
theorem incr_hasGaussianLaw (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    HasGaussianLaw (fun ω => (incrW W t τ ω, incrZ W t τ ω)) P :=
  hasGaussianLaw_pair hW.aemeasurable_incrW (hW.aemeasurable_incrZ ht hτ)
    fun α β => ⟨0, _, hW.incr_lin_map ht hτ α β⟩

/-- **The covariance of `(ΔW, ΔZ)`** (10.1.12): both are centred,
`⟨ΔW²⟩ = τ`, `⟨ΔW ΔZ⟩ = τ²/2`, `⟨ΔZ²⟩ = τ³/3`. -/
theorem incr_moments (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    ∫ ω, incrW W t τ ω ∂P = 0 ∧ ∫ ω, incrZ W t τ ω ∂P = 0 ∧
      ∫ ω, incrW W t τ ω ^ 2 ∂P = τ ∧ ∫ ω, incrW W t τ ω * incrZ W t τ ω ∂P = τ ^ 2 / 2 ∧
      ∫ ω, incrZ W t τ ω ^ 2 ∂P = τ ^ 3 / 3 := by
  have hab : t ≤ t + τ := by linarith
  have hW1 := hW.incrW_ae ht hτ
  have hZ1 := hW.incrZ_ae ht hτ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [integral_congr_ae hW1, hW.wienerInt_mean continuous_const ht hab]
  · rw [integral_congr_ae hZ1, hW.wienerInt_mean (continuous_kerZ t τ) ht hab]
  · rw [integral_congr_ae (show (fun ω => incrW W t τ ω ^ 2) =ᵐ[P]
        fun ω => wienerInt W P (fun _ => 1) t (t + τ) ω ^ 2 by
          filter_upwards [hW1] with ω h; rw [h]), hW.wienerInt_sq continuous_const ht hab]
    simp
  · rw [integral_congr_ae (show (fun ω => incrW W t τ ω * incrZ W t τ ω) =ᵐ[P]
        fun ω => wienerInt W P (fun _ => 1) t (t + τ) ω * wienerInt W P (kerZ t τ) t (t + τ) ω by
          filter_upwards [hW1, hZ1] with ω h h'; rw [h, h']),
      hW.wienerInt_mul_same continuous_const (continuous_kerZ t τ) ht hab hab, min_self,
      integral_one_kerZ]
  · simp_rw [sq]
    rw [integral_congr_ae (show (fun ω => incrZ W t τ ω * incrZ W t τ ω) =ᵐ[P]
        fun ω => wienerInt W P (kerZ t τ) t (t + τ) ω * wienerInt W P (kerZ t τ) t (t + τ) ω by
          filter_upwards [hZ1] with ω h; rw [h]),
      hW.wienerInt_mul_same (continuous_kerZ t τ) (continuous_kerZ t τ) ht hab hab, min_self,
      integral_kerZ_kerZ]

end IsWiener

/-! ### The representation `ΔW = √τ ξ`, `ΔZ = ½τ^{3/2}(ξ + η/√3)` -/

/-- `ξ = ΔW / √τ`. -/
def xiN (W : ℝ → Ω → ℝ) (t τ : ℝ) (ω : Ω) : ℝ := incrW W t τ ω / Real.sqrt τ

/-- `η = √3 (2ΔZ/τ^{3/2} - ξ)`. -/
def etaN (W : ℝ → Ω → ℝ) (t τ : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt 3 * (2 * incrZ W t τ ω / (τ * Real.sqrt τ) - xiN W t τ ω)

omit [MeasurableSpace Ω] in
lemma incrW_eq_xi {t τ : ℝ} (hτ : 0 < τ) (ω : Ω) :
    incrW W t τ ω = Real.sqrt τ * xiN W t τ ω := by
  have : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
  simp only [xiN]; field_simp

omit [MeasurableSpace Ω] in
lemma incrZ_eq_xi_eta {t τ : ℝ} (hτ : 0 < τ) (ω : Ω) :
    incrZ W t τ ω = 1 / 2 * τ * Real.sqrt τ * (xiN W t τ ω + etaN W t τ ω / Real.sqrt 3) := by
  have : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  simp only [etaN]; field_simp; ring

omit [MeasurableSpace Ω] in
lemma xi_eta_lin {t τ : ℝ} (α β : ℝ) :
    (fun ω => α * xiN W t τ ω + β * etaN W t τ ω) = fun ω =>
      ((α - β * Real.sqrt 3) / Real.sqrt τ) * incrW W t τ ω +
        (2 * Real.sqrt 3 * β / (τ * Real.sqrt τ)) * incrZ W t τ ω := by
  funext ω; simp only [xiN, etaN]; ring

lemma xi_eta_var {τ : ℝ} (hτ : 0 < τ) (α β : ℝ) :
    ((α - β * Real.sqrt 3) / Real.sqrt τ) ^ 2 * τ +
      ((α - β * Real.sqrt 3) / Real.sqrt τ) * (2 * Real.sqrt 3 * β / (τ * Real.sqrt τ)) * τ ^ 2 +
      (2 * Real.sqrt 3 * β / (τ * Real.sqrt τ)) ^ 2 * τ ^ 3 / 3 = α ^ 2 + β ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ τ = r ^ 2 :=
    ⟨Real.sqrt τ, Real.sqrt_pos.mpr hτ, (Real.sq_sqrt hτ.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  field_simp
  linear_combination β ^ 2 * h3

namespace IsWiener

variable (hW : IsWiener W P) {t τ : ℝ}
include hW

lemma xi_eta_lin_map (ht : 0 ≤ t) (hτ : 0 < τ) (α β : ℝ) :
    P.map (fun ω => α * xiN W t τ ω + β * etaN W t τ ω) =
      gaussianReal 0 (α ^ 2 + β ^ 2).toNNReal := by
  rw [xi_eta_lin, hW.incr_lin_map ht hτ.le, xi_eta_var hτ]

lemma aemeasurable_xi : AEMeasurable (xiN W t τ) P :=
  hW.aemeasurable_incrW.div_const _

lemma aemeasurable_eta (ht : 0 ≤ t) (hτ : 0 ≤ τ) : AEMeasurable (etaN W t τ) P :=
  (((hW.aemeasurable_incrZ ht hτ).const_mul 2).div_const _ |>.sub hW.aemeasurable_xi).const_mul _

/-- **`ξ` and `η` are independent standard normals** built from `W`. -/
theorem xi_eta_indep (ht : 0 ≤ t) (hτ : 0 < τ) :
    P.map (xiN W t τ) = gaussianReal 0 1 ∧ P.map (etaN W t τ) = gaussianReal 0 1 ∧
      HasGaussianLaw (fun ω => (xiN W t τ ω, etaN W t τ ω)) P ∧
      IndepFun (xiN W t τ) (etaN W t τ) P := by
  have := hW.isProbabilityMeasure
  have hξ := hW.xi_eta_lin_map ht hτ 1 0
  have hη := hW.xi_eta_lin_map ht hτ 0 1
  have hξη := hW.xi_eta_lin_map ht hτ 1 1
  simp only [one_mul, zero_mul, add_zero, zero_add, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Real.toNNReal_one] at hξ hη
  have hpair : HasGaussianLaw (fun ω => (xiN W t τ ω, etaN W t τ ω)) P :=
    hasGaussianLaw_pair hW.aemeasurable_xi (hW.aemeasurable_eta ht hτ.le)
      fun α β => ⟨0, _, hW.xi_eta_lin_map ht hτ α β⟩
  refine ⟨by simpa using hξ, by simpa using hη, hpair, hpair.indepFun_of_covariance_eq_zero ?_⟩
  -- the covariance vanishes by polarization
  obtain ⟨m1, e1, s1⟩ := moments_of_map_gaussian hW.aemeasurable_xi hξ
  obtain ⟨m2, e2, s2⟩ := moments_of_map_gaussian (hW.aemeasurable_eta ht hτ.le) hη
  obtain ⟨m3, -, s3⟩ := moments_of_map_gaussian
    ((hW.aemeasurable_xi.const_mul 1).add ((hW.aemeasurable_eta ht hτ.le).const_mul 1)) hξη
  rw [covariance_eq_sub m1 m2, e1, e2, mul_zero, sub_zero]
  have hpol : (fun ω => xiN W t τ ω * etaN W t τ ω) = fun ω =>
      1 / 2 * (1 * xiN W t τ ω + 1 * etaN W t τ ω) ^ 2 - 1 / 2 * xiN W t τ ω ^ 2 -
        1 / 2 * etaN W t τ ω ^ 2 := by
    funext ω; ring
  have i3 : Integrable (fun ω => 1 / 2 * (1 * xiN W t τ ω + 1 * etaN W t τ ω) ^ 2) P :=
    m3.integrable_sq.const_mul _
  have i1 : Integrable (fun ω => 1 / 2 * xiN W t τ ω ^ 2) P := m1.integrable_sq.const_mul _
  have i2 : Integrable (fun ω => 1 / 2 * etaN W t τ ω ^ 2) P := m2.integrable_sq.const_mul _
  have i31 : Integrable (fun ω => 1 / 2 * (1 * xiN W t τ ω + 1 * etaN W t τ ω) ^ 2 -
      1 / 2 * xiN W t τ ω ^ 2) P := i3.sub i1
  rw [show (xiN W t τ * etaN W t τ) = fun ω => xiN W t τ ω * etaN W t τ ω from rfl, hpol,
    integral_sub i31 i2, integral_sub i3 i1,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, s1, s2, s3]
  norm_num

/-- **(10.1.9)–(10.1.12) from the Wiener process**: the hypotheses of the Itô-free theorem
`Gardiner.SDE.multipleIntegral_moments` hold for `ξ = ΔW/√τ`, `η = √3(2ΔZ/τ^{3/2} - ξ)`, and its
conclusions are statements about the actual increments `ΔW`, `ΔZ`:
`⟨ΔZ⟩ = 0`, `⟨ΔWΔZ⟩ = τ²/2`, `⟨ΔZ²⟩ = τ³/3`, and for the companion `τΔW - ΔZ`:
`⟨ΔW(τΔW - ΔZ)⟩ = τ²/2`, `⟨(τΔW - ΔZ)²⟩ = τ³/3`. -/
theorem multiple_moments (ht : 0 ≤ t) (hτ : 0 < τ) :
    ∫ ω, incrZ W t τ ω ∂P = 0 ∧ ∫ ω, incrW W t τ ω * incrZ W t τ ω ∂P = τ ^ 2 / 2 ∧
      ∫ ω, incrZ W t τ ω ^ 2 ∂P = τ ^ 3 / 3 ∧
      ∫ ω, incrW W t τ ω * (τ * incrW W t τ ω - incrZ W t τ ω) ∂P = τ ^ 2 / 2 ∧
      ∫ ω, (τ * incrW W t τ ω - incrZ W t τ ω) ^ 2 ∂P = τ ^ 3 / 3 := by
  have := hW.isProbabilityMeasure
  obtain ⟨hξ, hη, -, hind⟩ := hW.xi_eta_indep ht hτ
  obtain ⟨m1, e1, s1⟩ := moments_of_map_gaussian hW.aemeasurable_xi hξ
  obtain ⟨m2, e2, s2⟩ := moments_of_map_gaussian (hW.aemeasurable_eta ht hτ.le) hη
  have c : ∫ ω, xiN W t τ ω * etaN W t τ ω ∂P = 0 := by
    have := hind.integral_mul_eq_mul_integral m1.aestronglyMeasurable m2.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, e1, zero_mul]
  have h := Gardiner.SDE.multipleIntegral_moments (P := P) τ hτ.le (m1.integrable one_le_two)
    (m2.integrable one_le_two) m1.integrable_sq m2.integrable_sq (m1.integrable_mul m2) e1 e2
    (by simpa using s1) (by simpa using s2) c
  simp only [← incrW_eq_xi hτ, ← incrZ_eq_xi_eta hτ] at h
  exact h

end IsWiener

/-- **Instance (standard Wiener process).** For `W = stdWiener`, `t = 1`, `τ = 1`:
`(ΔW, ΔZ)` is jointly Gaussian with `⟨ΔW²⟩ = 1`, `⟨ΔWΔZ⟩ = 1/2`, `⟨ΔZ²⟩ = 1/3`, and
`ξ = ΔW`, `η = √3(2ΔZ - ΔW)` are independent standard normals. -/
theorem multiple_stdWiener :
    HasGaussianLaw (fun ω => (incrW stdWiener 1 1 ω, incrZ stdWiener 1 1 ω)) stdWienerMeasure ∧
    ∫ ω, incrW stdWiener 1 1 ω ^ 2 ∂stdWienerMeasure = 1 ∧
    ∫ ω, incrW stdWiener 1 1 ω * incrZ stdWiener 1 1 ω ∂stdWienerMeasure = 1 / 2 ∧
    ∫ ω, incrZ stdWiener 1 1 ω ^ 2 ∂stdWienerMeasure = 1 / 3 ∧
    stdWienerMeasure.map (xiN stdWiener 1 1) = gaussianReal 0 1 ∧
    stdWienerMeasure.map (etaN stdWiener 1 1) = gaussianReal 0 1 ∧
    IndepFun (xiN stdWiener 1 1) (etaN stdWiener 1 1) stdWienerMeasure := by
  obtain ⟨-, -, h2, h3, h4⟩ := isWiener_stdWiener.incr_moments (t := 1) (τ := 1) zero_le_one
    zero_le_one
  obtain ⟨h5, h6, -, h7⟩ := isWiener_stdWiener.xi_eta_indep (t := 1) (τ := 1) zero_le_one one_pos
  refine ⟨isWiener_stdWiener.incr_hasGaussianLaw zero_le_one zero_le_one, h2, ?_, ?_, h5, h6, h7⟩
  · rw [h3]; norm_num
  · rw [h4]; norm_num

end Gardiner.Ito
