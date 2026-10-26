/-
# White noise as a limit of non-white noise (Gardiner §6.5)

Gardiner, *Handbook of Stochastic Methods*, §6.5, (6.5.1)–(6.5.74).

* **(6.5.7)–(6.5.12)**: the rescaled correlation `γ² g(γ² t)` has integral `∫ g` for every `γ`
  (`Gardiner.Adiabatic.scaled_corr_integral`, (6.5.11)) and tends to `δ(t)` with an explicit
  rate: for a test function with `|f(t) - f(0)| ≤ L|t|`,
  `|∫ γ² g(γ² t) f(t) dt - f(0) ∫ g| ≤ L τ_c / γ²`, `τ_c = ∫ |t| g(t) dt` (6.5.9)
  (`Gardiner.Adiabatic.scaled_corr_delta`).  Instance: Gaussian-correlated noise
  (`Gardiner.Adiabatic.gaussian_corr_delta`).
* **(6.5.41)–(6.5.42)**: `D = ∫₀^∞ g = ½ ∫ g` for an even correlation function
  (`Gardiner.Adiabatic.half_integral_of_even`).
* **(6.5.45) ⟺ (6.5.47)**: the Stratonovich and Itô forms of the limiting Fokker–Planck operator
  agree (`Gardiner.Adiabatic.strat_ito_flux`, `Gardiner.Adiabatic.strat_ito_backward`).
* **(6.5.14)–(6.5.53), generator form with explicit error.**  For `dx/dt = a(x) + γψ(x, α(γ²t))`
  with a fast Markov process `α` of generator `𝓛` (`L₁` of (6.5.15) is its adjoint), let `χ` solve
  the Poisson equation `𝓛χ = -ψ` (so that `D = ⟨ψχ⟩_s = ∫₀^∞⟨ψ(t)ψ(0)⟩`, (6.5.31)–(6.5.41), (6.5.51))
  and `ρ₁, ρ₂` solve `𝓛ρ₁ = D - ψχ`, `𝓛ρ₂ = E - ψ∂ₓχ` (solvable exactly because `D` and `E` are the
  stationary averages (6.5.51)–(6.5.52)).  Then on the perturbed test function
  `φ = f + γ⁻¹ χ f' + γ⁻² (ρ₁ f'' + ρ₂ f')` the full backward generator
  `γ² 𝓛 + γ ψ ∂ₓ + a ∂ₓ` equals `(a + E) f' + D f'' + γ⁻¹ R₁ + γ⁻² R₂`, the backward form of
  (6.5.53), with `R₁, R₂` explicit (`Gardiner.Adiabatic.wn_generator`,
  `Gardiner.Adiabatic.wn_generator_bound`).  For `ψ = b(x) α` this is the Stratonovich operator
  (6.5.45) (`Gardiner.Adiabatic.wn_stratonovich`).  The only use of `𝓛` is its linearity on the
  test function (hypothesis `hL`); the general fast process of §6.5.1 is covered.
* **Instances**: Ornstein–Uhlenbeck noise `dα = -α dt + dW` (correlation `½e^{-|t|}`, `D = ½`) with
  multiplicative coupling `b(x) = x`, `a(x) = -x` (`Gardiner.Adiabatic.wn_ou_instance`), and
  random-telegraph noise `α = ±1` (§6.5.1) with the same coupling
  (`Gardiner.Adiabatic.wn_telegraph_instance`).
* **§6.5.3–§6.5.4 (time-dependent systems)**: with the extra variable `τ`, `dτ = dt` (6.5.57), the
  same expansion holds with an additional `∂_τ` and with `a, b, D, E` evaluated at `τ = t`
  (`Gardiner.Adiabatic.wn_generator_time`); `D(τ)` may depend on `τ`, which is (6.5.73)–(6.5.74).
-/
import SHSLib.Gardiner.Adiabatic.KramersGenerator

open MeasureTheory Set

noncomputable section

namespace Gardiner.Adiabatic

/-! ### (6.5.7)–(6.5.12): the rescaled correlation function tends to `δ` -/

/-- **(6.5.11)**: `∫ γ² g(γ² t) dt = ∫ g` for every `γ ≠ 0`. -/
theorem scaled_corr_integral (g : ℝ → ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    ∫ s, γ ^ 2 * g (γ ^ 2 * s) = ∫ s, g s := by
  have hγ2 : (0 : ℝ) < γ ^ 2 := by positivity
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.2 hγ2), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hγ2.ne', one_mul]

/-- **(6.5.12) with an explicit rate.**  Let `g ≥ 0` be integrable with finite correlation time
`τ_c = ∫ |t| g(t) dt` (6.5.9), and let `f` be continuous with `|f(t) - f(0)| ≤ L|t|`.  Then
`|∫ γ² g(γ² t) f(t) dt - f(0) ∫ g| ≤ L τ_c / γ²`: the correlation function (6.5.7) of
`α₀(t) = γα(γ²t)` converges to `(∫ g) δ(t)` at rate `γ⁻²`. -/
theorem scaled_corr_delta (g f : ℝ → ℝ) (L : ℝ) (hg : Integrable g)
    (hg1 : Integrable (fun s => |s| * g s)) (hg0 : ∀ s, 0 ≤ g s) (hf : Continuous f)
    (hL : ∀ s, |f s - f 0| ≤ L * |s|) {γ : ℝ} (hγ : γ ≠ 0) :
    |(∫ s, γ ^ 2 * g (γ ^ 2 * s) * f s) - f 0 * ∫ s, g s|
      ≤ L / γ ^ 2 * ∫ s, |s| * g s := by
  have hγ2 : (0:ℝ) < γ ^ 2 := by positivity
  set k : ℝ → ℝ := fun s => γ ^ 2 * g (γ ^ 2 * s)
  have hk : Integrable k := (hg.comp_mul_left' hγ2.ne').const_mul _
  have hkint : ∫ s, k s = ∫ s, g s := scaled_corr_integral g hγ
  have hh : ∀ s, L * (|γ ^ 2 * s| * g (γ ^ 2 * s)) = L * |s| * k s := by
    intro s; simp only [k]; rw [abs_mul, abs_of_pos hγ2]; ring
  have hhint : Integrable (fun s => L * |s| * k s) := by
    have := (hg1.comp_mul_left' hγ2.ne').const_mul L
    simpa only [hh] using this
  have hdiff : Integrable (fun s => k s * (f s - f 0)) := by
    refine Integrable.mono' hhint ?_ ?_
    · exact hk.aestronglyMeasurable.mul (hf.sub continuous_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun s => ?_)
      have hks : 0 ≤ k s := mul_nonneg hγ2.le (hg0 _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hks]
      have := hL s
      nlinarith
  have hkf : Integrable (fun s => k s * f s) := by
    have : (fun s => k s * f s) = fun s => k s * (f s - f 0) + f 0 * k s := by ext s; ring
    rw [this]; exact hdiff.add (hk.const_mul _)
  have e : (∫ s, k s * f s) - f 0 * ∫ s, g s = ∫ s, k s * (f s - f 0) := by
    rw [← hkint, ← integral_const_mul, ← integral_sub hkf (hk.const_mul (f 0))]
    congr 1; ext s; ring
  have e2 : ∫ s, L * |s| * k s = L / γ ^ 2 * ∫ s, |s| * g s := by
    have : (fun s => L * |s| * k s) = fun s => L * ((fun σ => |σ| * g σ) (γ ^ 2 * s)) := by
      ext s; rw [← hh s]
    have h2 := Measure.integral_comp_mul_left (fun σ => |σ| * g σ) (γ ^ 2)
    rw [this, integral_const_mul, h2, abs_of_pos (inv_pos.2 hγ2), smul_eq_mul]
    ring
  change |(∫ s, k s * f s) - f 0 * ∫ s, g s| ≤ _
  rw [e, ← e2]
  refine (abs_integral_le_integral_abs).trans (integral_mono hdiff.abs hhint (fun s => ?_))
  have hks : 0 ≤ k s := mul_nonneg hγ2.le (hg0 _)
  simp only
  rw [abs_mul, abs_of_nonneg hks]
  have := hL s
  nlinarith

/-- **(6.5.41)–(6.5.42)**: for an even correlation function, `D = ∫₀^∞ g = ½ ∫ g`; with the
normalisation (6.5.8), `D = 1/2`. -/
theorem half_integral_of_even (g : ℝ → ℝ) (hev : ∀ s, g (-s) = g s) :
    ∫ s in Ioi 0, g s = (1 / 2) * ∫ s, g s := by
  have : ∫ s, g s = 2 * ∫ s in Ioi 0, g s := by
    rw [← integral_comp_abs]
    congr 1; ext s
    rcases abs_choice s with h | h <;> rw [h]; rw [hev]
  rw [this]; ring

/-- The Gaussian correlation function `g(t) = e^{-t²}/√π`. -/
def gaussCorr (t : ℝ) : ℝ := Real.exp (-t ^ 2) / Real.sqrt Real.pi

/-- **Instance of (6.5.8)–(6.5.12): Gaussian-correlated noise.**  `g(t) = e^{-t²}/√π` is
normalised, even (so `D = ½`), and for every test function `f = sin` (Lipschitz with `L = 1`)
the rescaled correlation approaches `δ` at rate `τ_c/γ²`. -/
theorem gaussian_corr_delta {γ : ℝ} (hγ : γ ≠ 0) :
    ∫ s, gaussCorr s = 1 ∧ ∫ s in Ioi 0, gaussCorr s = 1 / 2 ∧
      |(∫ s, γ ^ 2 * gaussCorr (γ ^ 2 * s) * Real.sin s) - Real.sin 0 * ∫ s, gaussCorr s|
        ≤ 1 / γ ^ 2 * ∫ s, |s| * gaussCorr s := by
  have hint : ∫ s, gaussCorr s = 1 := by
    simp only [gaussCorr, div_eq_mul_inv]
    rw [integral_mul_const]
    have := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at this
    rw [this, mul_inv_cancel₀ (Real.sqrt_pos.2 Real.pi_pos).ne']
  have hgi : Integrable gaussCorr := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).div_const (Real.sqrt Real.pi)
    simpa [gaussCorr] using this
  refine ⟨hint, ?_, ?_⟩
  · rw [half_integral_of_even _ (fun s => by simp [gaussCorr]), hint]; norm_num
  · refine scaled_corr_delta gaussCorr Real.sin 1 hgi ?_ (fun s => by unfold gaussCorr; positivity)
      Real.continuous_sin (fun s => ?_) hγ
    · have := ((integrable_mul_exp_neg_mul_sq (b := 1) one_pos).norm).div_const
        (Real.sqrt Real.pi)
      refine this.congr (Filter.Eventually.of_forall fun s => ?_)
      simp only [gaussCorr, Real.norm_eq_abs, abs_mul, neg_mul, one_mul,
        abs_of_pos (Real.exp_pos _)]
      ring
    · simpa using Real.abs_sin_sub_sin_le s 0

/-! ### (6.5.45) ⟺ (6.5.47): Stratonovich versus Itô -/

/-- **(6.5.45) ⟺ (6.5.47)**, at the level of probability fluxes: the Stratonovich flux
`½ b ∂ₓ(b p)` equals the Itô flux `½ ∂ₓ(b² p) - ½ b b' p`, so
`-∂ₓ(a p) + ½∂ₓ b ∂ₓ (b p) = -∂ₓ[(a + ½bb')p] + ½∂ₓ²(b²p)`. -/
theorem strat_ito_flux {b p : ℝ → ℝ} {x b' p' : ℝ} (hb : HasDerivAt b b' x)
    (hp : HasDerivAt p p' x) :
    HasDerivAt (fun y => b y * p y) (b' * p x + b x * p') x ∧
      HasDerivAt (fun y => b y ^ 2 * p y) (2 * b x * b' * p x + b x ^ 2 * p') x ∧
      (1 / 2) * b x * (b' * p x + b x * p')
        = (1 / 2) * (2 * b x * b' * p x + b x ^ 2 * p') - (1 / 2) * b x * b' * p x := by
  refine ⟨hb.mul hp, ?_, by ring⟩
  convert (hb.pow 2).mul hp using 1
  simp

/-- **Backward form of (6.5.45) ⟺ (6.5.47)**: `½ b (b f')' = ½ b² f'' + ½ b b' f'`. -/
theorem strat_ito_backward (b b' f₁ f₂ : ℝ) :
    (1 / 2) * b * (b' * f₁ + b * f₂) = (1 / 2) * b ^ 2 * f₂ + (1 / 2) * b * b' * f₁ := by ring

/-! ### The white-noise limit as a generator expansion -/

/-- The backward generator `γ²𝓛 + γψ∂ₓ + a∂ₓ` (with `γ = ε⁻¹`), applied to a function whose
fast-generator image is `Lφ` and whose `x`-derivative is `φx`. -/
def wnGen (ε a ψ Lφ φx : ℝ) : ℝ := ε⁻¹ ^ 2 * Lφ + ε⁻¹ * ψ * φx + a * φx

/-- `x`-derivative of the perturbed test function `f + εχf' + ε²(ρ₁f'' + ρ₂f')`. -/
def wnPhix (ε χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3 : ℝ) : ℝ :=
  f1 + ε * (χx * f1 + χ * f2) + ε ^ 2 * (ρ1x * f2 + ρ1 * f3 + ρ2x * f1 + ρ2 * f2)

/-- First remainder `R₁ = ψ ∂ₓφ₂ + a ∂ₓφ₁`. -/
def wnR1 (a ψ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3 : ℝ) : ℝ :=
  ψ * (ρ1x * f2 + ρ1 * f3 + ρ2x * f1 + ρ2 * f2) + a * (χx * f1 + χ * f2)

/-- Second remainder `R₂ = a ∂ₓφ₂`. -/
def wnR2 (a ρ1 ρ1x ρ2 ρ2x f1 f2 f3 : ℝ) : ℝ := a * (ρ1x * f2 + ρ1 * f3 + ρ2x * f1 + ρ2 * f2)

/-- **(6.5.14)–(6.5.53) as an exact generator identity.**  Assume the Poisson equations
`𝓛χ = -ψ`, `𝓛ρ₁ = D - ψχ`, `𝓛ρ₂ = E - ψ ∂ₓχ` (values `Lχ, Lρ1, Lρ2` at the current `(x, α)`)
and linearity of `𝓛` on the test function, `𝓛φ = εf'𝓛χ + ε²(f''𝓛ρ₁ + f'𝓛ρ₂)`.  Then
`(γ²𝓛 + γψ∂ₓ + a∂ₓ)φ = (a + E) f' + D f'' + γ⁻¹R₁ + γ⁻²R₂`. -/
theorem wn_generator {ε : ℝ} (hε : ε ≠ 0) (a ψ χ χx ρ1 ρ1x ρ2 ρ2x D E Lχ Lρ1 Lρ2 Lφ f1 f2 f3 : ℝ)
    (hχ : Lχ = -ψ) (hρ1 : Lρ1 = D - ψ * χ) (hρ2 : Lρ2 = E - ψ * χx)
    (hL : Lφ = ε * f1 * Lχ + ε ^ 2 * (f2 * Lρ1 + f1 * Lρ2)) :
    wnGen ε a ψ Lφ (wnPhix ε χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3)
      = (a + E) * f1 + D * f2 + ε * wnR1 a ψ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3
        + ε ^ 2 * wnR2 a ρ1 ρ1x ρ2 ρ2x f1 f2 f3 := by
  subst hL hχ hρ1 hρ2
  simp only [wnGen, wnPhix, wnR1, wnR2]
  field_simp
  ring

/-- **The white-noise limit with an explicit error.**  Under the hypotheses of `wn_generator`,
`|(γ²𝓛 + γψ∂ₓ + a∂ₓ)φ - [(a + E)f' + Df'']| ≤ γ⁻¹|R₁| + γ⁻²|R₂|`. -/
theorem wn_generator_bound {γ : ℝ} (hγ : 0 < γ)
    (a ψ χ χx ρ1 ρ1x ρ2 ρ2x D E Lχ Lρ1 Lρ2 Lφ f1 f2 f3 : ℝ)
    (hχ : Lχ = -ψ) (hρ1 : Lρ1 = D - ψ * χ) (hρ2 : Lρ2 = E - ψ * χx)
    (hL : Lφ = γ⁻¹ * f1 * Lχ + γ⁻¹ ^ 2 * (f2 * Lρ1 + f1 * Lρ2)) :
    |wnGen γ⁻¹ a ψ Lφ (wnPhix γ⁻¹ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3) - ((a + E) * f1 + D * f2)|
      ≤ γ⁻¹ * |wnR1 a ψ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3| + γ⁻¹ ^ 2 * |wnR2 a ρ1 ρ1x ρ2 ρ2x f1 f2 f3| := by
  rw [wn_generator (inv_ne_zero hγ.ne') a ψ χ χx ρ1 ρ1x ρ2 ρ2x D E Lχ Lρ1 Lρ2 Lφ f1 f2 f3
    hχ hρ1 hρ2 hL]
  set R1 := wnR1 a ψ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3
  set R2 := wnR2 a ρ1 ρ1x ρ2 ρ2x f1 f2 f3
  have e : (a + E) * f1 + D * f2 + γ⁻¹ * R1 + γ⁻¹ ^ 2 * R2 - ((a + E) * f1 + D * f2)
      = γ⁻¹ * R1 + γ⁻¹ ^ 2 * R2 := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hγ), abs_of_pos (by positivity : 0 < γ⁻¹ ^ 2)]

/-- **(6.5.43)–(6.5.47)**: for `ψ = b(x)α`, with `𝓛χ₀ = -α`, `D₀ = ⟨αχ₀⟩_s` and
`𝓛ψ₀ = D₀ - αχ₀`, the correctors `χ = bχ₀`, `ρ₁ = b²ψ₀`, `ρ₂ = bb'ψ₀` solve the Poisson equations
of `wn_generator` with `D = D₀b²`, `E = D₀bb'`, so the limit operator is
`a f' + D₀ b(bf')'`, i.e. the Stratonovich operator (6.5.45) when `D₀ = ½`. -/
theorem wn_stratonovich {ε : ℝ} (hε : ε ≠ 0) (a b b' α χ₀ ψ₀ D₀ Lχ₀ Lψ₀ Lφ f1 f2 f3 b'' : ℝ)
    (hχ : Lχ₀ = -α) (hψ : Lψ₀ = D₀ - α * χ₀)
    (hL : Lφ = ε * f1 * (b * Lχ₀) + ε ^ 2 * (f2 * (b ^ 2 * Lψ₀) + f1 * (b * b' * Lψ₀))) :
    wnGen ε a (b * α) Lφ
        (wnPhix ε (b * χ₀) (b' * χ₀) (b ^ 2 * ψ₀) (2 * b * b' * ψ₀) (b * b' * ψ₀)
          ((b' ^ 2 + b * b'') * ψ₀) f1 f2 f3)
      = a * f1 + D₀ * (b * (b' * f1 + b * f2))
        + ε * wnR1 a (b * α) (b * χ₀) (b' * χ₀) (b ^ 2 * ψ₀) (2 * b * b' * ψ₀) (b * b' * ψ₀)
          ((b' ^ 2 + b * b'') * ψ₀) f1 f2 f3
        + ε ^ 2 * wnR2 a (b ^ 2 * ψ₀) (2 * b * b' * ψ₀) (b * b' * ψ₀)
          ((b' ^ 2 + b * b'') * ψ₀) f1 f2 f3 := by
  rw [wn_generator hε a (b * α) (b * χ₀) (b' * χ₀) (b ^ 2 * ψ₀) (2 * b * b' * ψ₀) (b * b' * ψ₀)
    ((b' ^ 2 + b * b'') * ψ₀) (D₀ * b ^ 2) (D₀ * (b * b')) (b * Lχ₀) (b ^ 2 * Lψ₀)
    (b * b' * Lψ₀) Lφ f1 f2 f3 (by rw [hχ]; ring) (by rw [hψ]; ring) (by rw [hψ]; ring) hL]
  ring

/-- **§6.5.3–§6.5.4: time-dependent coefficients.**  With the extra variable `τ` of
(6.5.55)–(6.5.57) the backward generator acquires `∂_τ`.  If the `τ`-derivative of the perturbed
test function is `f_τ + εT₁ + ε²T₂` (the correctors depend on `τ` through `a, b, A, B`), then the
expansion of `wn_generator` holds with `∂_τ` added and remainders `R₁ + T₁`, `R₂ + T₂`; all of
`a, ψ, D, E` may depend on `τ = t`, which gives (6.5.62)–(6.5.64) and (6.5.73)–(6.5.74). -/
theorem wn_generator_time {ε : ℝ} (hε : ε ≠ 0)
    (a ψ χ χx ρ1 ρ1x ρ2 ρ2x D E Lχ Lρ1 Lρ2 Lφ f1 f2 f3 fτ φτ T1 T2 : ℝ)
    (hχ : Lχ = -ψ) (hρ1 : Lρ1 = D - ψ * χ) (hρ2 : Lρ2 = E - ψ * χx)
    (hL : Lφ = ε * f1 * Lχ + ε ^ 2 * (f2 * Lρ1 + f1 * Lρ2)) (hτ : φτ = fτ + ε * T1 + ε ^ 2 * T2) :
    φτ + wnGen ε a ψ Lφ (wnPhix ε χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3)
      = fτ + (a + E) * f1 + D * f2 + ε * (wnR1 a ψ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3 + T1)
        + ε ^ 2 * (wnR2 a ρ1 ρ1x ρ2 ρ2x f1 f2 f3 + T2) := by
  rw [wn_generator hε a ψ χ χx ρ1 ρ1x ρ2 ρ2x D E Lχ Lρ1 Lρ2 Lφ f1 f2 f3 hχ hρ1 hρ2 hL, hτ]
  ring

/-! ### Instances -/

/-- The perturbed test function of the Ornstein–Uhlenbeck instance (`b(x) = x`, `κ = σ = 1`):
`φ = f + εxαf' + ε²(x²α²f''/2 + xα²f'/2)`. -/
def ouPhi (F : ℕ → ℝ → ℝ) (ε x α : ℝ) : ℝ :=
  F 0 x + ε * (x * α) * F 1 x + ε ^ 2 * (x ^ 2 * α ^ 2 / 2 * F 2 x + x * α ^ 2 / 2 * F 1 x)

/-- **Instance: Ornstein–Uhlenbeck noise with multiplicative coupling.**  For
`dx/dt = -x + γ x α(γ²t)`, `dα = -α dt + dW` (correlation `½e^{-|t|}`, `D₀ = ½`), the backward
generator `γ²(-α∂_α + ½∂_α²) + γxα∂ₓ - x∂ₓ`, applied to `ouPhi` with its genuine partial
derivatives, equals `-(x/2) f' + (x²/2) f'' + γ⁻¹R₁ + γ⁻²R₂`: the Stratonovich operator
`-x f' + ½x(xf')'` of `(S) dx = -x dt + x dW`, equivalently the Itô drift `-x + x/2` (6.5.47). -/
theorem wn_ou_instance (F : ℕ → ℝ → ℝ) (hF : ∀ k y, HasDerivAt (F k) (F (k + 1) y) y)
    {γ : ℝ} (hγ : 0 < γ) (x α : ℝ) :
    ∃ φx φα φαα : ℝ,
      HasDerivAt (fun x => ouPhi F γ⁻¹ x α) φx x ∧
      HasDerivAt (fun α => ouPhi F γ⁻¹ x α) φα α ∧
      HasDerivAt (fun α => γ⁻¹ * x * F 1 x + γ⁻¹ ^ 2 * (x ^ 2 * α * F 2 x + x * α * F 1 x))
        φαα α ∧
      φα = γ⁻¹ * x * F 1 x + γ⁻¹ ^ 2 * (x ^ 2 * α * F 2 x + x * α * F 1 x) ∧
      |γ ^ 2 * (-α * φα + (1 / 2) * φαα) + γ * (x * α) * φx + (-x) * φx
          - ((-x + x / 2) * F 1 x + x ^ 2 / 2 * F 2 x)|
        ≤ γ⁻¹ * |wnR1 (-x) (x * α) (x * α) α (x ^ 2 * α ^ 2 / 2) (x * α ^ 2) (x * α ^ 2 / 2)
            (α ^ 2 / 2) (F 1 x) (F 2 x) (F 3 x)|
          + γ⁻¹ ^ 2 * |wnR2 (-x) (x ^ 2 * α ^ 2 / 2) (x * α ^ 2) (x * α ^ 2 / 2) (α ^ 2 / 2)
            (F 1 x) (F 2 x) (F 3 x)| := by
  set ε := γ⁻¹
  refine ⟨wnPhix ε (x * α) α (x ^ 2 * α ^ 2 / 2) (x * α ^ 2) (x * α ^ 2 / 2) (α ^ 2 / 2)
    (F 1 x) (F 2 x) (F 3 x), ε * x * F 1 x + ε ^ 2 * (x ^ 2 * α * F 2 x + x * α * F 1 x),
    ε ^ 2 * (x ^ 2 * F 2 x + x * F 1 x), ?_, ?_, ?_, rfl, ?_⟩
  · have h0 := hF 0 x; have h1 := hF 1 x; have h2 := hF 2 x
    have hx := hasDerivAt_id x
    have := (h0.add (((hx.mul_const α).mul h1).const_mul ε)).add
      ((((((hx.pow 2).mul_const (α ^ 2)).div_const 2).mul h2).add
        (((hx.mul_const (α ^ 2)).div_const 2).mul h1)).const_mul (ε ^ 2))
    convert this using 1 <;> first
      | (funext y; simp only [ouPhi, id, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring)
      | (simp only [wnPhix, id, Pi.pow_apply]; push_cast; ring)
  · have hα := hasDerivAt_id α
    have := ((hasDerivAt_const α (F 0 x)).add ((hα.const_mul x).const_mul ε |>.mul_const (F 1 x))).add
      (((((hα.pow 2).const_mul (x ^ 2)).div_const 2).mul_const (F 2 x)).add
        ((((hα.pow 2).const_mul x).div_const 2).mul_const (F 1 x)) |>.const_mul (ε ^ 2))
    convert this using 1
    simp only [id]; push_cast; ring
  · have hα := hasDerivAt_id α
    have := (hasDerivAt_const α (ε * x * F 1 x)).add
      ((((hα.const_mul (x ^ 2)).mul_const (F 2 x)).add ((hα.const_mul x).mul_const (F 1 x))).const_mul
        (ε ^ 2))
    convert this using 1
    ring
  · -- apply the general bound with the OU fast generator `𝓛 = -α∂_α + ½∂_α²`
    have hb := wn_generator_bound hγ (-x) (x * α) (x * α) α (x ^ 2 * α ^ 2 / 2) (x * α ^ 2)
      (x * α ^ 2 / 2) (α ^ 2 / 2) (x ^ 2 / 2) (x / 2) (-(x * α)) (x ^ 2 / 2 - x ^ 2 * α ^ 2)
      (x / 2 - x * α ^ 2)
      (-α * (ε * x * F 1 x + ε ^ 2 * (x ^ 2 * α * F 2 x + x * α * F 1 x))
        + (1 / 2) * (ε ^ 2 * (x ^ 2 * F 2 x + x * F 1 x)))
      (F 1 x) (F 2 x) (F 3 x) rfl (by ring) (by ring) (by ring)
    have e : γ ^ 2 * (-α * (ε * x * F 1 x + ε ^ 2 * (x ^ 2 * α * F 2 x + x * α * F 1 x))
          + (1 / 2) * (ε ^ 2 * (x ^ 2 * F 2 x + x * F 1 x)))
        + γ * (x * α) * wnPhix ε (x * α) α (x ^ 2 * α ^ 2 / 2) (x * α ^ 2) (x * α ^ 2 / 2)
          (α ^ 2 / 2) (F 1 x) (F 2 x) (F 3 x)
        + (-x) * wnPhix ε (x * α) α (x ^ 2 * α ^ 2 / 2) (x * α ^ 2) (x * α ^ 2 / 2)
          (α ^ 2 / 2) (F 1 x) (F 2 x) (F 3 x)
        = wnGen ε (-x) (x * α)
          (-α * (ε * x * F 1 x + ε ^ 2 * (x ^ 2 * α * F 2 x + x * α * F 1 x))
            + (1 / 2) * (ε ^ 2 * (x ^ 2 * F 2 x + x * F 1 x)))
          (wnPhix ε (x * α) α (x ^ 2 * α ^ 2 / 2) (x * α ^ 2) (x * α ^ 2 / 2) (α ^ 2 / 2)
            (F 1 x) (F 2 x) (F 3 x)) := by
      simp only [wnGen, ε, inv_inv]
    rw [e]
    convert hb using 3

/-- The fast generator of the random telegraph process `α = ±1` with flip rate `λ`:
`(𝓛h)(α) = λ(h(-α) - h(α))`. -/
def tgFast (lam : ℝ) (h : ℝ → ℝ) (α : ℝ) : ℝ := lam * (h (-α) - h α)

/-- **Instance: random-telegraph noise (§6.5.1).**  For `dx/dt = -x + γ x α(γ²t)` with
`α = ±1` flipping at rate `λ > 0` (correlation `e^{-2λ|t|}`, `D₀ = 1/(2λ)`), the corrector is
`χ = xα/(2λ)` and the second-order correctors vanish (`α² = 1`); the backward generator on
`φ = f + γ⁻¹ χ f'` equals `(-x + x/(2λ)) f' + (x²/(2λ)) f'' + γ⁻¹R₁`, with
`R₁ = -x(αf'/(2λ) + xαf''/(2λ))`.  The limit is the Stratonovich equation
`(S) dx = -x dt + λ^{-1/2} x dW`, so the result does not depend on the noise being Gaussian. -/
theorem wn_telegraph_instance (F : ℕ → ℝ → ℝ) {lam γ : ℝ} (hlam : 0 < lam) (hγ : 0 < γ)
    (x α : ℝ) (hα : α = 1 ∨ α = -1) :
    let φ : ℝ → ℝ := fun a => F 0 x + γ⁻¹ * (x * a / (2 * lam)) * F 1 x
    γ ^ 2 * tgFast lam φ α + γ * (x * α) * (F 1 x + γ⁻¹ * (α / (2 * lam) * F 1 x
        + x * α / (2 * lam) * F 2 x)) + (-x) * (F 1 x + γ⁻¹ * (α / (2 * lam) * F 1 x
        + x * α / (2 * lam) * F 2 x))
      = (-x + x / (2 * lam)) * F 1 x + x ^ 2 / (2 * lam) * F 2 x
        + γ⁻¹ * (-x * (α / (2 * lam) * F 1 x + x * α / (2 * lam) * F 2 x)) := by
  intro φ
  have hα2 : α ^ 2 = 1 := by rcases hα with h | h <;> subst h <;> norm_num
  have e := wn_generator (inv_ne_zero hγ.ne') (-x) (x * α) (x * α / (2 * lam))
    (α / (2 * lam)) 0 0 0 0 (x ^ 2 / (2 * lam)) (x / (2 * lam)) (-(x * α)) 0 0
    (tgFast lam φ α) (F 1 x) (F 2 x) (F 3 x) rfl
    (by field_simp; rw [hα2]; ring) (by field_simp; rw [hα2]; ring)
    (by simp only [tgFast, φ]; field_simp; ring)
  simp only [wnGen, wnPhix, wnR1, wnR2, inv_inv] at e
  convert e using 1 <;> ring

/-- **Instance of `wn_stratonovich`**: Ornstein–Uhlenbeck noise (`𝓛 = -α∂_α + ½∂_α²`,
`χ₀ = α`, `ψ₀ = α²/2`, `D₀ = ½`) with `b(x) = x`, `a(x) = -x`: the limit operator is
`-x f' + ½ x (x f')'`, the Stratonovich operator of `(S) dx = -x dt + x dW`. -/
theorem wn_stratonovich_ou {ε : ℝ} (hε : ε ≠ 0) (x α f1 f2 f3 : ℝ) :
    wnGen ε (-x) (x * α)
        (ε * f1 * (x * -α) + ε ^ 2 * (f2 * (x ^ 2 * (1 / 2 - α ^ 2))
          + f1 * (x * 1 * (1 / 2 - α ^ 2))))
        (wnPhix ε (x * α) (1 * α) (x ^ 2 * (α ^ 2 / 2)) (2 * x * 1 * (α ^ 2 / 2))
          (x * 1 * (α ^ 2 / 2)) ((1 ^ 2 + x * 0) * (α ^ 2 / 2)) f1 f2 f3)
      = -x * f1 + (1 / 2) * (x * (1 * f1 + x * f2))
        + ε * wnR1 (-x) (x * α) (x * α) (1 * α) (x ^ 2 * (α ^ 2 / 2)) (2 * x * 1 * (α ^ 2 / 2))
          (x * 1 * (α ^ 2 / 2)) ((1 ^ 2 + x * 0) * (α ^ 2 / 2)) f1 f2 f3
        + ε ^ 2 * wnR2 (-x) (x ^ 2 * (α ^ 2 / 2)) (2 * x * 1 * (α ^ 2 / 2)) (x * 1 * (α ^ 2 / 2))
          ((1 ^ 2 + x * 0) * (α ^ 2 / 2)) f1 f2 f3 :=
  wn_stratonovich hε (-x) x 1 α α (α ^ 2 / 2) (1 / 2) (-α) (1 / 2 - α ^ 2) _ f1 f2 f3 0 rfl
    (by ring) rfl

/-- **Instance of `wn_generator_time` (§6.5.3)**: `dx/dt = -x + γ cos(t) α(γ²t)` with
Ornstein–Uhlenbeck `α` (`D₀ = ½`).  With `τ` as an extra variable, the perturbed test function
`φ = f + ε cos τ α f' + ε² cos²τ α² f''/2` has `∂_τφ = εT₁ + ε²T₂`, and the generator
`∂_τ + γ²𝓛 + γ cos τ α ∂ₓ - x∂ₓ` on `φ` equals `-x f' + ½cos²τ f'' + O(γ⁻¹)`: (6.5.64) with
`b(x, t) = cos t`. -/
theorem wn_time_instance {ε : ℝ} (hε : ε ≠ 0) (x α τ f0 f1 f2 f3 : ℝ) :
    HasDerivAt (fun τ => f0 + ε * (Real.cos τ * α) * f1 + ε ^ 2 * (Real.cos τ ^ 2 * α ^ 2 / 2) * f2)
        (ε * (-Real.sin τ * α * f1) + ε ^ 2 * (-(Real.cos τ * Real.sin τ) * α ^ 2 * f2)) τ ∧
      (ε * (-Real.sin τ * α * f1) + ε ^ 2 * (-(Real.cos τ * Real.sin τ) * α ^ 2 * f2))
        + wnGen ε (-x) (Real.cos τ * α)
          (ε * f1 * (-(Real.cos τ * α)) + ε ^ 2 * (f2 * (Real.cos τ ^ 2 / 2
            - Real.cos τ * α * (Real.cos τ * α)) + f1 * 0))
          (wnPhix ε (Real.cos τ * α) 0 (Real.cos τ ^ 2 * α ^ 2 / 2) 0 0 0 f1 f2 f3)
      = 0 + (-x + 0) * f1 + Real.cos τ ^ 2 / 2 * f2
        + ε * (wnR1 (-x) (Real.cos τ * α) (Real.cos τ * α) 0 (Real.cos τ ^ 2 * α ^ 2 / 2) 0 0 0
            f1 f2 f3 + (-Real.sin τ * α * f1))
        + ε ^ 2 * (wnR2 (-x) (Real.cos τ ^ 2 * α ^ 2 / 2) 0 0 0 f1 f2 f3
            + (-(Real.cos τ * Real.sin τ) * α ^ 2 * f2)) := by
  refine ⟨?_, ?_⟩
  · have hc := Real.hasDerivAt_cos τ
    have := ((hasDerivAt_const τ f0).add
      (((hc.mul_const α).const_mul ε).mul_const f1)).add
      (((((hc.pow 2).mul_const (α ^ 2)).div_const 2).const_mul (ε ^ 2)).mul_const f2)
    convert this using 1
    push_cast; ring
  · exact wn_generator_time hε (-x) (Real.cos τ * α) (Real.cos τ * α) 0
      (Real.cos τ ^ 2 * α ^ 2 / 2) 0 0 0 (Real.cos τ ^ 2 / 2) 0 (-(Real.cos τ * α))
      (Real.cos τ ^ 2 / 2 - Real.cos τ * α * (Real.cos τ * α)) 0 _ f1 f2 f3 0 _ _ _ rfl rfl
      (by ring) rfl (by ring)

end Gardiner.Adiabatic
