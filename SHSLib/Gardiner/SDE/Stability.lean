/-
# Stability of the Euler, implicit and semi-implicit schemes (Gardiner §10.3)

**Error propagation for the complex test equation.**  For the test equation (10.3.1),
`dx = λx dt + dW` (the printed equation omits the `dt`), with `λ ∈ ℂ`, each scheme is an affine
recursion `y_{n+1} = R yₙ + cₙ`, where `cₙ` depends only on the increment `ΔWₙ`.  Two runs driven by
the *same* increments, whatever they are, therefore differ by exactly `Rⁿ (y₀ - ȳ₀)`:

* explicit Euler (10.3.2): `R = 1 + λτ`, giving (10.3.3)–(10.3.4)
  (`Gardiner.SDE.euler_error_propagation`);
* fully implicit Euler (10.3.7)/(10.3.10): `R = (1 - λτ)⁻¹`, giving (10.3.11)
  (`Gardiner.SDE.implicit_error_propagation`);
* semi-implicit (10.3.13): `R = (1 + λτ/2)/(1 - λτ/2)`, giving (10.3.14)
  (`Gardiner.SDE.semi_error_propagation`).

The statements are pathwise: the increments are an arbitrary complex sequence, so no probability
is needed.  The error tends to zero iff `‖R‖ < 1` (`Gardiner.SDE.error_tendsto_zero_iff`), and the
regions of stability are characterised exactly: the open disc (10.3.5)
(`Gardiner.SDE.euler_stable_iff`), the exterior of a disc (10.3.12)
(`Gardiner.SDE.implicit_stable_iff`), and the open left half-plane (10.3.15)
(`Gardiner.SDE.semi_stable_iff`).  A-stability (§10.3 d)) holds for the implicit and
semi-implicit schemes and fails for explicit Euler (`Gardiner.SDE.implicit_AStable`,
`Gardiner.SDE.semi_AStable`, `Gardiner.SDE.euler_not_AStable`).

**Erratum (Fig. 10.1c).**  The caption of Fig. 10.1c describes the stability region of the fully
implicit scheme as the right half-plane `Re λ ≥ 0`; the text (10.3.12) correctly gives the
exterior of the disc `|λ - 1/τ| ≤ 1/τ`, which contains the whole left half-plane
(`Gardiner.SDE.fig10_1c_printed_wrong`).

**Mean-square stability.**  For the multiplicative test equation `dx = λx dt + μx dW` the schemes
are the multiplicative linear schemes of `SHSLib.Gardiner.SDE.SchemeMoments`, so
`⟨yₙ²⟩ = y₀² Fⁿ` with the explicit factor `F = ⟨G²⟩`, and `⟨yₙ²⟩ → 0` iff `F < 1`
(`Gardiner.SDE.ms_tendsto_zero_iff`).  We compute `F` and the mean-square stability regions:

* Euler: `F = (1 + λτ)² + μ²τ`; stable iff `λ²τ + 2λ + μ² < 0`
  (`Gardiner.SDE.eulerGBM_ms_stable_iff`); this forces `2λ + μ² < 0`, the mean-square
  stability condition of the exact solution (`Gardiner.SDE.eulerGBM_ms_stable_imp`), and conversely
  holds for all `0 < τ < -(2λ + μ²)/λ²` (`Gardiner.SDE.eulerGBM_ms_stable_of`);
* Milstein: `F = (1 + λτ)² + μ²τ + μ⁴τ²/2`; stable iff `λ²τ + 2λ + μ² + μ⁴τ/2 < 0`
  (`Gardiner.SDE.milsteinGBM_ms_stable_iff`);
* drift-implicit Euler `y_{n+1} = yₙ + λτ y_{n+1} + μ yₙ ΔWₙ`: `F = (1 + μ²τ)/(1 - λτ)²`; whenever
  the exact solution is mean-square stable (`2λ + μ² < 0`, `λ < 0`) it is mean-square stable for
  **every** `τ > 0` (`Gardiner.SDE.implicitGBM_ms_stable`).
-/
import SHSLib.Gardiner.SDE.WeakError

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

noncomputable section

namespace Gardiner.SDE

/-! ### Pathwise error propagation for the complex test equation -/

/-- Run of a one-step map `step : y ↦ ΔW ↦ y'` from `y₀` along the increments `dw`. -/
def schemeRun (step : ℂ → ℂ → ℂ) (y0 : ℂ) (dw : ℕ → ℂ) : ℕ → ℂ
  | 0 => y0
  | n + 1 => step (schemeRun step y0 dw n) (dw n)

/-- Explicit Euler (10.3.2) for `dx = λx dt + dW`. -/
def eulerStepC (lam : ℂ) (τ : ℝ) (y dw : ℂ) : ℂ := (1 + lam * τ) * y + dw

/-- Fully implicit Euler (10.3.10) for `dx = λx dt + dW`, solved for `y_{n+1}`. -/
def implicitStepC (lam : ℂ) (τ : ℝ) (y dw : ℂ) : ℂ := (y + dw) / (1 - lam * τ)

/-- Semi-implicit (10.3.13) for `dx = λx dt + dW`, solved for `y_{n+1}`. -/
def semiStepC (lam : ℂ) (τ : ℝ) (y dw : ℂ) : ℂ := ((1 + lam * τ / 2) * y + dw) / (1 - lam * τ / 2)

/-- `implicitStepC` solves the implicit equation (10.3.10). -/
theorem implicitStepC_spec {lam : ℂ} {τ : ℝ} (h : 1 - lam * τ ≠ 0) (y dw : ℂ) :
    implicitStepC lam τ y dw = y + lam * τ * implicitStepC lam τ y dw + dw := by
  unfold implicitStepC; field_simp; ring

/-- `semiStepC` solves the semi-implicit equation (10.3.13) with `a(x) = λx`, `b = 1`. -/
theorem semiStepC_spec {lam : ℂ} {τ : ℝ} (h : 1 - lam * τ / 2 ≠ 0) (y dw : ℂ) :
    semiStepC lam τ y dw = y + (lam * y + lam * semiStepC lam τ y dw) / 2 * τ + (1 + 1) / 2 * dw := by
  have hu : (1 - lam * τ / 2) * (1 - lam * τ / 2)⁻¹ = 1 := mul_inv_cancel₀ h
  unfold semiStepC
  rw [div_eq_mul_inv _ (1 - lam * τ / 2)]
  linear_combination ((1 + lam * τ / 2) * y + dw) * hu

/-- Two runs of an affine recursion with the same forcing differ by `Rⁿ (y₀ - ȳ₀)`. -/
lemma affine_run_diff {step : ℂ → ℂ → ℂ} {R : ℂ} (hstep : ∀ y y' w, step y w - step y' w = R * (y - y'))
    (y0 y0' : ℂ) (dw : ℕ → ℂ) (n : ℕ) :
    schemeRun step y0 dw n - schemeRun step y0' dw n = R ^ n * (y0 - y0') := by
  induction n with
  | zero => simp [schemeRun]
  | succ n ih => simp only [schemeRun]; rw [hstep, ih]; ring

/-- (10.3.3)–(10.3.4): `|yₙ - ȳₙ| = |1 + λτ|ⁿ |y₀ - ȳ₀|`, for any increments. -/
theorem euler_error_propagation (lam : ℂ) (τ : ℝ) (y0 y0' : ℂ) (dw : ℕ → ℂ) (n : ℕ) :
    ‖schemeRun (eulerStepC lam τ) y0 dw n - schemeRun (eulerStepC lam τ) y0' dw n‖ =
      ‖1 + lam * τ‖ ^ n * ‖y0 - y0'‖ := by
  rw [affine_run_diff (R := 1 + lam * τ) (fun y y' w => by unfold eulerStepC; ring), norm_mul,
    norm_pow]

/-- (10.3.11): `|yₙ - ȳₙ| = |1 - λτ|⁻ⁿ |y₀ - ȳ₀|`, for any increments. -/
theorem implicit_error_propagation (lam : ℂ) (τ : ℝ) (y0 y0' : ℂ) (dw : ℕ → ℂ) (n : ℕ) :
    ‖schemeRun (implicitStepC lam τ) y0 dw n - schemeRun (implicitStepC lam τ) y0' dw n‖ =
      ‖1 - lam * τ‖⁻¹ ^ n * ‖y0 - y0'‖ := by
  rw [affine_run_diff (R := (1 - lam * τ)⁻¹) (fun y y' w => by unfold implicitStepC; ring),
    norm_mul, norm_pow, norm_inv]

/-- (10.3.14): `|yₙ - ȳₙ| = |(1 + λτ/2)/(1 - λτ/2)|ⁿ |y₀ - ȳ₀|`, for any increments. -/
theorem semi_error_propagation (lam : ℂ) (τ : ℝ) (y0 y0' : ℂ) (dw : ℕ → ℂ) (n : ℕ) :
    ‖schemeRun (semiStepC lam τ) y0 dw n - schemeRun (semiStepC lam τ) y0' dw n‖ =
      ‖(1 + lam * τ / 2) / (1 - lam * τ / 2)‖ ^ n * ‖y0 - y0'‖ := by
  rw [affine_run_diff (R := (1 + lam * τ / 2) / (1 - lam * τ / 2))
    (fun y y' w => by unfold semiStepC; ring), norm_mul, norm_pow]

/-- An initial error `d ≠ 0` propagated by `‖R‖ⁿ d` dies out iff `‖R‖ < 1`. -/
theorem error_tendsto_zero_iff {r d : ℝ} (hr : 0 ≤ r) (hd : 0 < d) :
    Tendsto (fun n : ℕ => r ^ n * d) atTop (𝓝 0) ↔ r < 1 := by
  constructor
  · intro h
    have := h.mul_const d⁻¹
    simp only [zero_mul, mul_assoc, mul_inv_cancel₀ hd.ne', mul_one] at this
    exact abs_of_nonneg hr ▸ tendsto_pow_atTop_nhds_zero_iff.mp this
  · intro h
    have := (tendsto_pow_atTop_nhds_zero_iff.mpr (by rwa [abs_of_nonneg hr])).mul_const d
    simpa using this

lemma norm_one_add_sq_sub (w : ℂ) : ‖1 + w‖ ^ 2 - ‖1 - w‖ ^ 2 = 4 * w.re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]; simp; ring

/-- (10.3.5): the Euler region of stability is the open disc of radius `1/τ` centred at `-1/τ`. -/
theorem euler_stable_iff (lam : ℂ) {τ : ℝ} (hτ : 0 < τ) :
    ‖1 + lam * τ‖ < 1 ↔ ‖lam - (-1 / τ : ℝ)‖ < 1 / τ := by
  have : 1 + lam * τ = (τ : ℂ) * (lam - (-1 / τ : ℝ)) := by
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    push_cast; field_simp; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le, lt_div_iff₀ hτ, mul_comm]

/-- (10.3.12): for `λτ ≠ 1`, the implicit Euler region of stability is the exterior of the closed
disc of radius `1/τ` centred at `1/τ`. -/
theorem implicit_stable_iff (lam : ℂ) {τ : ℝ} (hτ : 0 < τ) (h : 1 - lam * τ ≠ 0) :
    ‖1 - lam * τ‖⁻¹ < 1 ↔ 1 / τ < ‖lam - (1 / τ : ℝ)‖ := by
  have : 1 - lam * τ = -((τ : ℂ) * (lam - (1 / τ : ℝ))) := by
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    push_cast; field_simp; ring
  rw [inv_lt_one₀ (norm_pos_iff.mpr h), this, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hτ.le, div_lt_iff₀ hτ, mul_comm]

/-- (10.3.15): `|1 + λτ/2| < |1 - λτ/2|` iff `Re λ < 0`. -/
theorem semi_region_iff (lam : ℂ) {τ : ℝ} (hτ : 0 < τ) :
    ‖1 + lam * τ / 2‖ < ‖1 - lam * τ / 2‖ ↔ lam.re < 0 := by
  have h := norm_one_add_sq_sub (lam * τ / 2)
  have hre : (lam * τ / 2).re = lam.re * τ / 2 := by simp
  rw [hre] at h
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  constructor
  · intro h1; nlinarith
  · intro h1; nlinarith

/-- (10.3.14)–(10.3.15): for `τ > 0` and `λτ ≠ 2` the semi-implicit amplification factor has
modulus `< 1` exactly on the open left half-plane. -/
theorem semi_stable_iff (lam : ℂ) {τ : ℝ} (hτ : 0 < τ) (h : 1 - lam * τ / 2 ≠ 0) :
    ‖(1 + lam * τ / 2) / (1 - lam * τ / 2)‖ < 1 ↔ lam.re < 0 := by
  rw [norm_div, div_lt_one (norm_pos_iff.mpr h)]; exact semi_region_iff lam hτ

/-- On the open left half-plane the semi-implicit denominator never vanishes. -/
lemma semi_denom_ne_zero {lam : ℂ} {τ : ℝ} (hτ : 0 < τ) (hl : lam.re < 0) :
    1 - lam * τ / 2 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  nlinarith

/-- On the open left half-plane the implicit denominator never vanishes. -/
lemma implicit_denom_ne_zero {lam : ℂ} {τ : ℝ} (hτ : 0 < τ) (hl : lam.re < 0) :
    1 - lam * τ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  nlinarith

/-- **A-stability** (§10.3 d)): a scheme with amplification factor `R(λ)` is A-stable if
`‖R(λ)‖ < 1` on the whole open left half-plane. -/
def AStable (R : ℂ → ℂ) : Prop := ∀ lam : ℂ, lam.re < 0 → ‖R lam‖ < 1

/-- The fully implicit Euler scheme is A-stable. -/
theorem implicit_AStable {τ : ℝ} (hτ : 0 < τ) : AStable (fun lam => (1 - lam * τ)⁻¹) := by
  intro lam hl
  have h := implicit_denom_ne_zero hτ hl
  rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr h)]
  have h2 := Complex.re_le_norm (1 - lam * τ)
  have hre : (1 - lam * τ).re = 1 - lam.re * τ := by simp
  rw [hre] at h2
  nlinarith

/-- The semi-implicit scheme is A-stable. -/
theorem semi_AStable {τ : ℝ} (hτ : 0 < τ) :
    AStable (fun lam => (1 + lam * τ / 2) / (1 - lam * τ / 2)) := fun lam hl =>
  (semi_stable_iff lam hτ (semi_denom_ne_zero hτ hl)).mpr hl

/-- The explicit Euler scheme is not A-stable: `λ = -3/τ` has `|1 + λτ| = 2`. -/
theorem euler_not_AStable {τ : ℝ} (hτ : 0 < τ) : ¬ AStable (fun lam => 1 + lam * τ) := by
  intro h
  have := h ((-3 / τ : ℝ) : ℂ) (by simp; exact div_neg_of_neg_of_pos (by norm_num) hτ)
  simp only at this
  have e : (1 : ℂ) + ((-3 / τ : ℝ) : ℂ) * τ = ((-2 : ℝ) : ℂ) := by
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    push_cast; field_simp; ring
  rw [e, Complex.norm_real] at this
  norm_num at this

/-- "The fully implicit method is stable even in regions where the solution itself can grow
exponentially": `λ = 3/τ` (`Re λ > 0`) is in the implicit region of stability. -/
theorem implicit_stable_growing {τ : ℝ} (hτ : 0 < τ) :
    0 < ((3 / τ : ℝ) : ℂ).re ∧ ‖1 - ((3 / τ : ℝ) : ℂ) * τ‖⁻¹ < 1 := by
  have e : (1 : ℂ) - ((3 / τ : ℝ) : ℂ) * τ = ((-2 : ℝ) : ℂ) := by
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    push_cast; field_simp; ring
  refine ⟨by simp; positivity, ?_⟩
  rw [e, Complex.norm_real]; norm_num

/-- **Erratum, Fig. 10.1c.**  The caption describes the implicit stability region as the right
half-plane `Re λ ≥ 0`.  This is wrong: `λ = -1/τ` is stable although `Re λ < 0`, and `λ = 1/(2τ)`
is unstable although `Re λ > 0`. -/
theorem fig10_1c_printed_wrong {τ : ℝ} (hτ : 0 < τ) :
    ¬ ∀ lam : ℂ, 1 - lam * τ ≠ 0 → (‖1 - lam * τ‖⁻¹ < 1 ↔ 0 ≤ lam.re) := by
  intro h
  have e : (1 : ℂ) - ((-1 / τ : ℝ) : ℂ) * τ = ((2 : ℝ) : ℂ) := by
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    push_cast; field_simp; ring
  have := h ((-1 / τ : ℝ) : ℂ) (by rw [e]; norm_num)
  rw [e, Complex.norm_real] at this
  have hn : (-1 / τ) < 0 := div_neg_of_neg_of_pos (by norm_num) hτ
  have := this.mp (by norm_num)
  simp only [Complex.ofReal_re] at this
  linarith

/-! ### Mean-square stability for `dx = λx dt + μx dW` -/

/-- Drift-implicit Euler for `dx = λx dt + μx dW`: `y_{n+1} = yₙ + λτ y_{n+1} + μ yₙ ΔWₙ`,
i.e. `y_{n+1} = (1 + μΔWₙ) yₙ / (1 - λτ)`. -/
def implicitGBM (lam mu t : ℝ) : LinStep := ⟨1 / (1 - lam * t), mu / (1 - lam * t), 0, 0, 0⟩

theorem implicitGBM_spec {lam t : ℝ} (h : 1 - lam * t ≠ 0) (mu y z : ℝ) :
    (implicitGBM lam mu t).apply y z = y + lam * t * (implicitGBM lam mu t).apply y z + mu * y * z := by
  simp only [implicitGBM, LinStep.apply, LinStep.G, LinStep.H]
  field_simp; ring

theorem eulerGBM_EG2 (lam mu t : ℝ) : (eulerGBM lam mu t).EG2 t = (1 + lam * t) ^ 2 + mu ^ 2 * t := by
  simp [LinStep.EG2, eulerGBM]

theorem milsteinGBM_EG2 (lam mu t : ℝ) :
    (milsteinGBM lam mu t).EG2 t = (1 + lam * t) ^ 2 + mu ^ 2 * t + mu ^ 4 * t ^ 2 / 2 := by
  simp [LinStep.EG2, milsteinGBM]; ring

theorem implicitGBM_EG2 (lam mu t : ℝ) :
    (implicitGBM lam mu t).EG2 t = (1 + mu ^ 2 * t) / (1 - lam * t) ^ 2 := by
  simp only [LinStep.EG2, implicitGBM, div_pow]; ring

/-- Euler mean-square stability region: `F < 1` iff `λ²τ + 2λ + μ² < 0`. -/
theorem eulerGBM_ms_stable_iff (lam mu : ℝ) {t : ℝ} (ht : 0 < t) :
    (eulerGBM lam mu t).EG2 t < 1 ↔ lam ^ 2 * t + 2 * lam + mu ^ 2 < 0 := by
  rw [eulerGBM_EG2]
  have : (1 + lam * t) ^ 2 + mu ^ 2 * t - 1 = t * (lam ^ 2 * t + 2 * lam + mu ^ 2) := by ring
  constructor
  · intro h; by_contra h'; push_neg at h'; nlinarith
  · intro h; nlinarith

/-- If Euler is mean-square stable for some `τ > 0`, the exact solution is mean-square stable:
`2λ + μ² < 0`. -/
theorem eulerGBM_ms_stable_imp {lam mu t : ℝ} (ht : 0 < t) (h : (eulerGBM lam mu t).EG2 t < 1) :
    2 * lam + mu ^ 2 < 0 := by
  have := (eulerGBM_ms_stable_iff lam mu ht).mp h
  nlinarith [mul_nonneg (sq_nonneg lam) ht.le]

/-- Conversely, if `2λ + μ² < 0`, Euler is mean-square stable for all `0 < τ` with
`λ²τ < -(2λ + μ²)`. -/
theorem eulerGBM_ms_stable_of {lam mu t : ℝ} (ht : 0 < t) (h : lam ^ 2 * t < -(2 * lam + mu ^ 2)) :
    (eulerGBM lam mu t).EG2 t < 1 :=
  (eulerGBM_ms_stable_iff lam mu ht).mpr (by linarith)

/-- Milstein mean-square stability region: `F < 1` iff `λ²τ + 2λ + μ² + μ⁴τ/2 < 0`. -/
theorem milsteinGBM_ms_stable_iff (lam mu : ℝ) {t : ℝ} (ht : 0 < t) :
    (milsteinGBM lam mu t).EG2 t < 1 ↔ lam ^ 2 * t + 2 * lam + mu ^ 2 + mu ^ 4 * t / 2 < 0 := by
  rw [milsteinGBM_EG2]
  have : (1 + lam * t) ^ 2 + mu ^ 2 * t + mu ^ 4 * t ^ 2 / 2 - 1 =
      t * (lam ^ 2 * t + 2 * lam + mu ^ 2 + mu ^ 4 * t / 2) := by ring
  constructor
  · intro h; by_contra h'; push_neg at h'; nlinarith
  · intro h; nlinarith

/-- Drift-implicit Euler is mean-square stable for **every** step `τ > 0` whenever the exact
solution is mean-square stable, `2λ + μ² < 0`. -/
theorem implicitGBM_ms_stable {lam mu t : ℝ} (ht : 0 < t) (h : 2 * lam + mu ^ 2 < 0) :
    (implicitGBM lam mu t).EG2 t < 1 := by
  have hl : lam < 0 := by nlinarith [sq_nonneg mu]
  have hd : 0 < (1 - lam * t) ^ 2 := by nlinarith [mul_neg_of_neg_of_pos hl ht]
  rw [implicitGBM_EG2, div_lt_one hd]
  nlinarith [mul_nonneg (sq_nonneg lam) (sq_nonneg t), mul_lt_mul_of_pos_right h ht]

section MeanSquare

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : ℝ≥0} {ξ : ℕ → Ω → ℝ}

/-- **Mean-square stability of a multiplicative linear scheme.**  For `y₀ ≠ 0`, `⟨yₙ²⟩ → 0` iff
`⟨G²⟩ < 1`. -/
theorem ms_tendsto_zero_iff (s : LinStep) (hH0 : s.h0 = 0) (hH1 : s.h1 = 0)
    (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {c : ℝ} (hc : c ≠ 0) (hF : 0 ≤ s.EG2 τ) :
    Tendsto (fun n => ∫ ω, linScheme s c ξ n ω ^ 2 ∂P) atTop (𝓝 0) ↔ s.EG2 τ < 1 := by
  simp_rw [linScheme_sq s c hξm hind hlaw hH0 hH1, mul_comm (c ^ 2)]
  exact error_tendsto_zero_iff hF (by positivity)

/-- Euler for `dx = λx dt + μx dW`: `⟨yₙ²⟩ → 0` iff `λ²τ + 2λ + μ² < 0`. -/
theorem eulerGBM_ms_tendsto_iff (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hτ : 0 < (τ : ℝ)) {lam mu c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun n => ∫ ω, linScheme (eulerGBM lam mu τ) c ξ n ω ^ 2 ∂P) atTop (𝓝 0) ↔
      lam ^ 2 * τ + 2 * lam + mu ^ 2 < 0 := by
  rw [ms_tendsto_zero_iff _ rfl rfl hξm hind hlaw hc (by rw [eulerGBM_EG2]; positivity),
    eulerGBM_ms_stable_iff lam mu hτ]

/-- Milstein for `dx = λx dt + μx dW`: `⟨yₙ²⟩ → 0` iff `λ²τ + 2λ + μ² + μ⁴τ/2 < 0`. -/
theorem milsteinGBM_ms_tendsto_iff (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hτ : 0 < (τ : ℝ)) {lam mu c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun n => ∫ ω, linScheme (milsteinGBM lam mu τ) c ξ n ω ^ 2 ∂P) atTop (𝓝 0) ↔
      lam ^ 2 * τ + 2 * lam + mu ^ 2 + mu ^ 4 * τ / 2 < 0 := by
  rw [ms_tendsto_zero_iff _ rfl rfl hξm hind hlaw hc (by rw [milsteinGBM_EG2]; positivity),
    milsteinGBM_ms_stable_iff lam mu hτ]

/-- Drift-implicit Euler: if `2λ + μ² < 0` then `⟨yₙ²⟩ → 0` for every step `τ > 0`. -/
theorem implicitGBM_ms_tendsto (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hτ : 0 < (τ : ℝ)) {lam mu : ℝ}
    (h : 2 * lam + mu ^ 2 < 0) (c : ℝ) :
    Tendsto (fun n => ∫ ω, linScheme (implicitGBM lam mu τ) c ξ n ω ^ 2 ∂P) atTop (𝓝 0) := by
  by_cases hc : c = 0
  · subst hc
    simp_rw [linScheme_sq (implicitGBM lam mu τ) 0 hξm hind hlaw rfl rfl]; simp
  · exact (ms_tendsto_zero_iff _ rfl rfl hξm hind hlaw hc
      (by rw [implicitGBM_EG2]; positivity)).mpr (implicitGBM_ms_stable hτ h)

end MeanSquare

/-! ### Instances -/

/-- Instance, Euler at `λ = -1`, `μ = 1`: mean-square stable exactly for `0 < τ < 1`;
here `τ = 1/2` is stable and `τ = 2` is not, whereas drift-implicit Euler is stable at `τ = 2`. -/
example : (eulerGBM (-1) 1 (1 / 2)).EG2 (1 / 2) < 1 ∧ ¬ (eulerGBM (-1) 1 2).EG2 2 < 1 ∧
    (implicitGBM (-1) 1 2).EG2 2 < 1 := by
  refine ⟨?_, ?_, implicitGBM_ms_stable (by norm_num) (by norm_num)⟩
  · rw [eulerGBM_EG2]; norm_num
  · rw [eulerGBM_EG2]; norm_num

/-- Instance of (10.3.4) and (10.3.14) at `λ = -1 + i`, `τ = 1`: Euler amplifies by `|i| = 1`
(not stable) while the semi-implicit factor has modulus `< 1`. -/
example (y0 y0' : ℂ) (dw : ℕ → ℂ) (n : ℕ) :
    ‖schemeRun (eulerStepC (-1 + Complex.I) 1) y0 dw n -
      schemeRun (eulerStepC (-1 + Complex.I) 1) y0' dw n‖ = ‖y0 - y0'‖ ∧
    ‖(1 + (-1 + Complex.I) * (1 : ℝ) / 2) / (1 - (-1 + Complex.I) * (1 : ℝ) / 2)‖ < 1 := by
  refine ⟨?_, (semi_stable_iff _ one_pos (semi_denom_ne_zero one_pos (by simp))).mpr (by simp)⟩
  rw [euler_error_propagation]; simp

end Gardiner.SDE
