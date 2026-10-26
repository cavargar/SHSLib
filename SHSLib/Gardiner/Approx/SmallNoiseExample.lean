/-
# The example of §6.3.2

Gardiner, *Handbook of Stochastic Methods*, §6.3.2, equations (6.3.36)–(6.3.51): the
Fokker–Planck equation `∂ₜ p = ∂ₓ[(x + x³) p] + (ε²/6) ∂ₓ² p`, i.e. (6.3.1) with
`A(x) = -(x + x³)` and `B = 1/3`.

* (6.3.37): the coefficients `Ã₁ = -1, Ã₂ = 0, Ã₃ = -1, B̃₀ = 1/3`; the expansions are
  exact (`Gardiner.ex_drift_expansion`, `Gardiner.ex_diff_expansion`).
* (6.3.38): `⟨x⟩ₛ = 0`, `var{x}ₛ = ε²/6`.
* (6.3.39)–(6.3.40): the exact correlation equations; (6.3.40) is their truncation
  (the `n = 3` equation contains the term `-3ε² c₅`, dropped in (6.3.40)).
* (6.3.41)–(6.3.43): eigenvalues, eigenvectors and the solution of (6.3.40).  The text's
  (6.3.43) writes `e^{-λᵢ t}`; since `λᵢ < 0` and the `λᵢ` are the eigenvalues of the
  matrix of (6.3.40), the solution is `Σ αᵢ e^{λᵢ t} uᵢ`.  The corrected form is formalized.
* (6.3.44)–(6.3.47): the initial condition and the coefficients `αᵢ`.
* **(6.3.48) with an explicit error**: `|c₁(t) - e^{λ₁ t}/6| ≤ ε⁴/(24 √(1-ε²))` for all
  `t ≥ 0` (`Gardiner.ex_c1_approx`); in fact
  `c₁(t) - e^{λ₁t}/6 = (1-√(1-ε²))²/(24√(1-ε²)) (e^{λ₁t} - e^{λ₂t})`.
* (6.3.50)–(6.3.51): the spectrum of `ε² c₁(|t|)`.  The Fourier integral is
  `∫ e^{-iωt} e^{λ|t|} dt = -2λ/(λ² + ω²)` (`Gardiner.fourier_exp_abs`), so that
  `S(ω) = -ε² λ₁ / (6π (λ₁² + ω²))`.  The text's (6.3.51), `ε²/(12π(λ₁² + ω²))`, differs from
  this by the factor `-2λ₁` (which tends to `2` as `ε → 0`).
-/
import SHSLib.Gardiner.Approx.SmallNoiseMoments

open MeasureTheory Filter Topology Set
open scoped BigOperators Nat

noncomputable section

namespace Gardiner

/-! ### (6.3.36)–(6.3.38) -/

/-- The drift `A(x) = -(x + x³)` of (6.3.36). -/
def exA (x : ℝ) : ℝ := -(x + x ^ 3)

/-- The diffusion coefficient `B = 1/3` of (6.3.36) (so that `½ ε² B = ε²/6`). -/
def exB (_x : ℝ) : ℝ := 1 / 3

/-- (6.3.37): `Ã₁ = -1`, `Ã₃ = -1`, all other `Ãq = 0`. -/
def exAt (n : ℕ) : ℝ := if n = 1 ∨ n = 3 then -1 else 0

/-- (6.3.37): `B̃q = δ_{q,0}/3`. -/
def exBt (n : ℕ) : ℝ := if n = 0 then 1 / 3 else 0

/-- (6.3.37), drift: `[A(εy) - A(0)]/ε = Σ_{q<3} ε^q Ã_{q+1} y^{q+1}` exactly (`α = 0`). -/
theorem ex_drift_expansion {ε : ℝ} (hε : ε ≠ 0) (y : ℝ) :
    (exA (0 + ε * y) - exA 0) / ε = ∑ q ∈ Finset.range 3, ε ^ q * exAt (q + 1) * y ^ (q + 1) := by
  simp [exA, exAt, Finset.sum_range_succ]
  field_simp
  ring

/-- (6.3.37), diffusion: `B(εy) = Σ_{q<3} ε^q B̃_q y^q` exactly. -/
theorem ex_diff_expansion (ε y : ℝ) :
    exB (0 + ε * y) = ∑ q ∈ Finset.range 3, ε ^ q * exBt q * y ^ q := by
  simp [exB, exBt]

/-- `α = 0` is a stationary solution of the deterministic equation (6.3.2) for (6.3.36). -/
theorem ex_alpha_stationary : exA 0 = 0 := by simp [exA]

/-- **(6.3.38)**: for (6.3.36), `⟨x⟩ₛ = 0` and `var{x}ₛ = ε²/6` (to the orders of
(6.3.30)–(6.3.31)). -/
theorem ex_stationary (M : ℕ → ℕ → ℝ) (ε : ℝ) (h00 : M 0 0 = 1) (h10 : M 1 0 = 0)
    (s01 : hierMomRHS exAt exBt M 0 1 = 0) (s02 : hierMomRHS exAt exBt M 0 2 = 0)
    (s03 : hierMomRHS exAt exBt M 0 3 = 0) (s11 : hierMomRHS exAt exBt M 1 1 = 0)
    (s12 : hierMomRHS exAt exBt M 1 2 = 0) (s21 : hierMomRHS exAt exBt M 2 1 = 0) :
    0 + ε * (M 0 1 + ε * M 1 1 + ε ^ 2 * M 2 1) = 0 ∧ ε ^ 2 * (M 0 2 - M 0 1 ^ 2) = ε ^ 2 / 6 := by
  have hA : exAt 1 ≠ 0 := by simp [exAt]
  constructor
  · rw [stationary_mean exAt exBt M 0 ε hA h00 h10 s01 s02 s03 s11 s12 s21]
    simp [exAt]
  · rw [stationary_variance exAt exBt M ε hA h00 h10 s01 s02 s03 s11 s12 s21]
    simp [exAt, exBt]
    ring

/-- (6.3.45): `M₀⁴ = -(3/2) B̃₀ M₀²/Ã₁ = 1/12`, given `M₀² = 1/6`. -/
theorem ex_fourth_moment (M : ℕ → ℕ → ℝ) (h02 : M 0 2 = 1 / 6)
    (s04 : hierMomRHS exAt exBt M 0 4 = 0) : M 0 4 = 1 / 12 := by
  rw [hierMomRHS_0_4, h02] at s04
  simp [exAt, exBt] at s04
  linarith

/-! ### (6.3.39)–(6.3.40): the correlation equations -/

section Correlation

variable {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')

/-- (6.3.39)–(6.3.40), first row: `dc₁/dt = -c₁ - ε² c₃`, where `cₙ(t) = ⟨y(t)ⁿ y(0)⟩ₛ`. -/
theorem ex_corr_one {ε : ℝ} (hε : ε ≠ 0) (Y : ℝ → Ω' → ℝ) (t : ℝ)
    (hint : ∀ k ≤ 3 + 1, Integrable (fun ω => Y t ω ^ k * Y 0 ω) μ)
    (h633 : HasDerivAt (fun t => ∫ ω, Y t ω ^ 1 * Y 0 ω ∂μ)
      (∫ ω, autocorrIntegrand exA exB 0 ε 1 (Y t ω) (Y 0 ω) ∂μ) t) :
    HasDerivAt (fun t => ∫ ω, Y t ω ^ 1 * Y 0 ω ∂μ)
      (-(∫ ω, Y t ω ^ 1 * Y 0 ω ∂μ) - ε ^ 2 * ∫ ω, Y t ω ^ 3 * Y 0 ω ∂μ) t := by
  have := autocorr_hierarchy_deriv μ exA exB 0 ε exAt exBt 3 1 (ex_drift_expansion hε)
    (fun y => ex_diff_expansion ε y) Y t hint h633
  convert this using 1
  simp [Finset.sum_range_succ, exAt, exBt]
  ring

/-- (6.3.39)–(6.3.40), second row, **exact form**: `dc₃/dt = c₁ - 3c₃ - 3ε² c₅`.
(6.3.40) is obtained by dropping the term `-3ε² c₅`. -/
theorem ex_corr_three {ε : ℝ} (hε : ε ≠ 0) (Y : ℝ → Ω' → ℝ) (t : ℝ)
    (hint : ∀ k ≤ 3 + 3, Integrable (fun ω => Y t ω ^ k * Y 0 ω) μ)
    (h633 : HasDerivAt (fun t => ∫ ω, Y t ω ^ 3 * Y 0 ω ∂μ)
      (∫ ω, autocorrIntegrand exA exB 0 ε 3 (Y t ω) (Y 0 ω) ∂μ) t) :
    HasDerivAt (fun t => ∫ ω, Y t ω ^ 3 * Y 0 ω ∂μ)
      ((∫ ω, Y t ω ^ 1 * Y 0 ω ∂μ) - 3 * (∫ ω, Y t ω ^ 3 * Y 0 ω ∂μ)
        - 3 * ε ^ 2 * ∫ ω, Y t ω ^ 5 * Y 0 ω ∂μ) t := by
  have := autocorr_hierarchy_deriv μ exA exB 0 ε exAt exBt 3 3 (ex_drift_expansion hε)
    (fun y => ex_diff_expansion ε y) Y t hint h633
  convert this using 1
  simp [Finset.sum_range_succ, exAt, exBt]
  ring

end Correlation

/-! ### (6.3.41)–(6.3.47): solution of the truncated system (6.3.40) -/

/-- The matrix of (6.3.40). -/
def exMat (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1, -ε ^ 2; 1, -3]

/-- `√(1 - ε²)`. -/
def exS (ε : ℝ) : ℝ := Real.sqrt (1 - ε ^ 2)

/-- (6.3.41): `λ₁ = -2 + √(1-ε²)`. -/
def exLam1 (ε : ℝ) : ℝ := -2 + exS ε

/-- (6.3.41): `λ₂ = -2 - √(1-ε²)`. -/
def exLam2 (ε : ℝ) : ℝ := -2 - exS ε

/-- (6.3.42): `u₁ = (1 + √(1-ε²), 1)`. -/
def exU1 (ε : ℝ) : Fin 2 → ℝ := ![1 + exS ε, 1]

/-- (6.3.42): `u₂ = (1 - √(1-ε²), 1)`. -/
def exU2 (ε : ℝ) : Fin 2 → ℝ := ![1 - exS ε, 1]

lemma exS_sq {ε : ℝ} (hε : ε ^ 2 ≤ 1) : exS ε ^ 2 = 1 - ε ^ 2 :=
  Real.sq_sqrt (by linarith)

/-- (6.3.41)–(6.3.42): `u₁` is an eigenvector of the matrix of (6.3.40) with eigenvalue
`λ₁`. -/
theorem ex_eigen1 {ε : ℝ} (hε : ε ^ 2 ≤ 1) : Matrix.mulVec (exMat ε) (exU1 ε) = exLam1 ε • exU1 ε := by
  have h := exS_sq hε
  ext i
  fin_cases i <;> simp [exMat, exU1, exLam1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [h]

/-- (6.3.41)–(6.3.42): `u₂` is an eigenvector with eigenvalue `λ₂`. -/
theorem ex_eigen2 {ε : ℝ} (hε : ε ^ 2 ≤ 1) : Matrix.mulVec (exMat ε) (exU2 ε) = exLam2 ε • exU2 ε := by
  have h := exS_sq hε
  ext i
  fin_cases i <;> simp [exMat, exU2, exLam2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [h]

/-- The first component of the solution (6.3.43) (with the corrected exponentials). -/
def exC1 (ε a₁ a₂ t : ℝ) : ℝ :=
  a₁ * Real.exp (exLam1 ε * t) * (1 + exS ε) + a₂ * Real.exp (exLam2 ε * t) * (1 - exS ε)

/-- The second component of the solution (6.3.43). -/
def exC3 (ε a₁ a₂ t : ℝ) : ℝ := a₁ * Real.exp (exLam1 ε * t) + a₂ * Real.exp (exLam2 ε * t)

/-- **(6.3.43)**, corrected: `c(t) = α₁ e^{λ₁ t} u₁ + α₂ e^{λ₂ t} u₂` solves the truncated
system (6.3.40) `ċ₁ = -c₁ - ε² c₃`, `ċ₃ = c₁ - 3 c₃`. -/
theorem ex_solution {ε : ℝ} (hε : ε ^ 2 ≤ 1) (a₁ a₂ t : ℝ) :
    HasDerivAt (exC1 ε a₁ a₂) (-exC1 ε a₁ a₂ t - ε ^ 2 * exC3 ε a₁ a₂ t) t ∧
      HasDerivAt (exC3 ε a₁ a₂) (exC1 ε a₁ a₂ t - 3 * exC3 ε a₁ a₂ t) t := by
  have h := exS_sq hε
  have e1 : ∀ c : ℝ, HasDerivAt (fun t => Real.exp (c * t)) (c * Real.exp (c * t)) t := by
    intro c
    have := (Real.hasDerivAt_exp (c * t)).comp t ((hasDerivAt_id t).const_mul c)
    simpa [mul_comm] using this
  constructor
  · have := (((e1 (exLam1 ε)).const_mul a₁).mul_const (1 + exS ε)).add
      (((e1 (exLam2 ε)).const_mul a₂).mul_const (1 - exS ε))
    convert this using 1
    simp only [exC1, exC3, exLam1, exLam2]
    linear_combination (-(a₁ * Real.exp ((-2 + exS ε) * t)) - a₂ * Real.exp ((-2 - exS ε) * t)) * h
  · have := ((e1 (exLam1 ε)).const_mul a₁).add ((e1 (exLam2 ε)).const_mul a₂)
    convert this using 1
    simp only [exC1, exC3, exLam1, exLam2]
    ring

/-- (6.3.47): the coefficients `α₁ = (1 + √(1-ε²))/(24√(1-ε²))`,
`α₂ = (-1 + √(1-ε²))/(24√(1-ε²))`. -/
def exA1 (ε : ℝ) : ℝ := (1 + exS ε) / (24 * exS ε)

/-- (6.3.47), second coefficient. -/
def exA2 (ε : ℝ) : ℝ := (-1 + exS ε) / (24 * exS ε)

lemma exS_pos {ε : ℝ} (hε : ε ^ 2 < 1) : 0 < exS ε := Real.sqrt_pos.2 (by linarith)

/-- **(6.3.44)–(6.3.47)**: with these coefficients the solution meets the initial
condition `c₁(0) = ⟨y²⟩ₛ = 1/6`, `c₃(0) = ⟨y⁴⟩ₛ = 1/12`. -/
theorem ex_initial {ε : ℝ} (hε : ε ^ 2 < 1) :
    exC1 ε (exA1 ε) (exA2 ε) 0 = 1 / 6 ∧ exC3 ε (exA1 ε) (exA2 ε) 0 = 1 / 12 := by
  have hs := exS_pos hε
  simp only [exC1, exC3, exA1, exA2, mul_zero, Real.exp_zero, mul_one]
  constructor <;> field_simp <;> ring

/-- The exact form of the error in (6.3.48):
`c₁(t) - e^{λ₁t}/6 = (1 - √(1-ε²))²/(24√(1-ε²)) · (e^{λ₁t} - e^{λ₂t})`. -/
theorem ex_c1_error_eq {ε : ℝ} (hε : ε ^ 2 < 1) (t : ℝ) :
    exC1 ε (exA1 ε) (exA2 ε) t - (1 / 6) * Real.exp (exLam1 ε * t)
      = (1 - exS ε) ^ 2 / (24 * exS ε) * (Real.exp (exLam1 ε * t) - Real.exp (exLam2 ε * t)) := by
  have hs := exS_pos hε
  simp only [exC1, exA1, exA2]
  field_simp
  ring

/-- **(6.3.48) with an explicit error bound**: for `ε² < 1` and all `t ≥ 0`,
`|c₁(t) - e^{λ₁ t}/6| ≤ ε⁴ / (24 √(1-ε²))`.  So `c₁(t) = e^{λ₁ t}/6 + O(ε⁴)` uniformly in
`t ≥ 0`, which is the statement "to 2nd order in ε" of the text. -/
theorem ex_c1_approx {ε : ℝ} (hε : ε ^ 2 < 1) {t : ℝ} (ht : 0 ≤ t) :
    |exC1 ε (exA1 ε) (exA2 ε) t - (1 / 6) * Real.exp (exLam1 ε * t)|
      ≤ ε ^ 4 / (24 * exS ε) := by
  have hs := exS_pos hε
  have hs1 : exS ε ≤ 1 := by
    rw [exS, Real.sqrt_le_one]; nlinarith [sq_nonneg ε]
  have hsq := exS_sq hε.le
  rw [ex_c1_error_eq hε, abs_mul, abs_of_nonneg (by positivity)]
  -- `0 ≤ 1 - s ≤ ε²`
  have h1 : 1 - exS ε ≤ ε ^ 2 := by nlinarith
  have h2 : (1 - exS ε) ^ 2 ≤ ε ^ 4 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - exS ε) h1 2
    nlinarith
  -- `|e^{λ₁t} - e^{λ₂t}| ≤ 1`
  have h3 : |Real.exp (exLam1 ε * t) - Real.exp (exLam2 ε * t)| ≤ 1 := by
    have hl1 : exLam1 ε * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by simp [exLam1]; linarith) ht
    have hl12 : exLam2 ε * t ≤ exLam1 ε * t :=
      mul_le_mul_of_nonneg_right (by simp [exLam1, exLam2]; linarith) ht
    have e1 := Real.exp_le_one_iff.2 hl1
    have e2 := Real.exp_le_exp.2 hl12
    have e3 := Real.exp_pos (exLam2 ε * t)
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc (1 - exS ε) ^ 2 / (24 * exS ε) * |Real.exp (exLam1 ε * t) - Real.exp (exLam2 ε * t)|
      ≤ ε ^ 4 / (24 * exS ε) * 1 := by gcongr
    _ = _ := mul_one _

/-! ### (6.3.49)–(6.3.51): the spectrum -/

/-- The Fourier integral of a two-sided exponential:
`∫ e^{-iωt} e^{λ|t|} dt = -2λ/(λ² + ω²)` for `λ < 0`. -/
theorem fourier_exp_abs {lam : ℝ} (hl : lam < 0) (ω : ℝ) :
    ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) * Real.exp (lam * |t|)
      = ((-2 * lam / (lam ^ 2 + ω ^ 2) : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun t => Complex.exp (-(Complex.I * ω * t)) * Real.exp (lam * |t|)
  set a : ℂ := lam - Complex.I * ω
  set b : ℂ := -lam - Complex.I * ω
  have hfa : ∀ t ∈ Ioi (0 : ℝ), f t = Complex.exp (a * t) := by
    intro t ht
    simp only [f, a, abs_of_pos (show (0 : ℝ) < t from ht)]
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  have hfb : ∀ t ∈ Iic (0 : ℝ), f t = Complex.exp (b * t) := by
    intro t ht
    simp only [f, b, abs_of_nonpos (show t ≤ 0 from ht)]
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  have ha : a.re < 0 := by simp [a, hl]
  have hb : 0 < b.re := by simp [b]; linarith
  have iR : IntegrableOn f (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi ha 0).congr_fun (fun t ht => (hfa t ht).symm)
      measurableSet_Ioi
  have iL : IntegrableOn f (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hb 0).congr_fun (fun t ht => (hfb t ht).symm)
      measurableSet_Iic
  rw [← intervalIntegral.integral_Iic_add_Ioi iL iR,
    setIntegral_congr_fun measurableSet_Iic hfb, setIntegral_congr_fun measurableSet_Ioi hfa,
    integral_exp_mul_complex_Ioi ha 0]
  have hL : ∫ t in Iic (0 : ℝ), Complex.exp (b * t) = 1 / b := by
    have := integral_comp_neg_Ioi 0 (fun t : ℝ => Complex.exp (b * t))
    simp only [neg_zero] at this
    rw [← this]
    have e : ∀ t : ℝ, Complex.exp (b * ((-t : ℝ) : ℂ)) = Complex.exp ((-b) * t) := by
      intro t; push_cast; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex_Ioi (by simp; linarith) 0]
    simp
  rw [hL]
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hden : (lam : ℂ) ^ 2 + (ω : ℂ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < lam ^ 2 + ω ^ 2 := by nlinarith [sq_nonneg ω, mul_pos (neg_pos.2 hl) (neg_pos.2 hl)]
    exact_mod_cast this.ne'
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  push_cast
  rw [div_add_div _ _ hb0 ha0, div_eq_div_iff (mul_ne_zero hb0 ha0) hden]
  simp only [a, b]
  linear_combination (2 * (lam : ℂ) * (ω : ℂ) ^ 2) * Complex.I_sq

/-- **(6.3.50)–(6.3.51)**, corrected: the spectrum of the stationary correlation
`ε² c₁(|t|) = (ε²/6) e^{λ₁|t|}` is `S(ω) = (ε²/2π) ∫ e^{-iωt} c₁(|t|) dt
= -ε² λ₁/(6π(λ₁² + ω²))`. -/
theorem ex_spectrum (ε ω : ℝ) :
    (ε ^ 2 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) * (((1 / 6 : ℝ) * Real.exp (exLam1 ε * |t|) : ℝ) : ℂ)
      = ((-ε ^ 2 * exLam1 ε / (6 * Real.pi * (exLam1 ε ^ 2 + ω ^ 2)) : ℝ) : ℂ) := by
  have hs1 : exS ε ≤ 1 := by
    rw [exS, Real.sqrt_le_one]; nlinarith [sq_nonneg ε]
  have hl : exLam1 ε < 0 := by simp [exLam1]; linarith
  have e : ∀ t : ℝ, Complex.exp (-(Complex.I * ω * t)) * (((1 / 6 : ℝ) * Real.exp (exLam1 ε * |t|) : ℝ) : ℂ)
      = (1 / 6 : ℂ) * (Complex.exp (-(Complex.I * ω * t)) * Real.exp (exLam1 ε * |t|)) := by
    intro t; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, fourier_exp_abs hl ω]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : exLam1 ε ^ 2 + ω ^ 2 ≠ 0 := by
    have : 0 < exLam1 ε ^ 2 + ω ^ 2 := by
      nlinarith [sq_nonneg ω, mul_pos (neg_pos.2 hl) (neg_pos.2 hl)]
    exact this.ne'
  push_cast
  field_simp

end Gardiner
