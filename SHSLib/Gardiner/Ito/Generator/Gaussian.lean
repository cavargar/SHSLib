/-
# Gaussian densities solve the Fokker–Planck equation of linear SDEs

* `gaussDens m v y = (2π v)^{-1/2} exp(-(y - m)²/(2v))` (equal to Mathlib's `gaussianPDFReal`,
  `gaussDens_eq_gaussianPDFReal`);
* its derivatives in `y` (`hasDerivAt_gaussDens_y`, `deriv_gaussDens_y`, …) and in `t` along
  differentiable mean and variance curves (`hasDerivAt_gaussDens_t`);
* `gaussDens_fokkerPlanck_linear`: if `m' = -k m` and `v' = D - 2 k v` (the moment equations of
  `dx = -k x dt + √D dW`), then `p(t, y) = gaussDens (m t) (v t) y` satisfies
  `∂ₜp = -∂_y[-k y p] + ½ ∂²_y[D p]`, i.e. Gardiner (4.3.20) for the OU coefficients.
-/
import SHSLib.Gardiner.Ito.Generator.StrongFP

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal

noncomputable section

namespace Gardiner.Ito.Generator

/-- The Gaussian density with mean `m` and variance `v`. -/
def gaussDens (m v y : ℝ) : ℝ := (√(2 * π * v))⁻¹ * exp (-(y - m) ^ 2 / (2 * v))

lemma gaussDens_eq_gaussianPDFReal (m : ℝ) (v : ℝ≥0) (y : ℝ) :
    gaussDens m v y = gaussianPDFReal m v y := by
  simp [gaussDens, gaussianPDFReal]

lemma gaussDens_nonneg (m v y : ℝ) : 0 ≤ gaussDens m v y := by
  unfold gaussDens; positivity

lemma contDiff_gaussDens (m v : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (gaussDens m v) := by
  unfold gaussDens
  fun_prop

/-- `∂_y gaussDens = -gaussDens · (y - m)/v`. -/
lemma hasDerivAt_gaussDens_y (m v y : ℝ) :
    HasDerivAt (gaussDens m v) (gaussDens m v y * (-(y - m) / v)) y := by
  unfold gaussDens
  have h : HasDerivAt (fun y => -(y - m) ^ 2 / (2 * v)) (-(2 * (y - m)) / (2 * v)) y := by
    have := ((hasDerivAt_id y).sub_const m).pow 2
    simpa using (this.neg).div_const (2 * v)
  have := (h.exp).const_mul (√(2 * π * v))⁻¹
  convert this using 1
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · field_simp

lemma deriv_gaussDens_y (m v : ℝ) :
    deriv (gaussDens m v) = fun y => gaussDens m v y * (-(y - m) / v) :=
  funext fun y => (hasDerivAt_gaussDens_y m v y).deriv

/-- `∂²_y gaussDens = gaussDens · ((y - m)²/v² - 1/v)`. -/
lemma hasDerivAt_gaussDens_yy (m v y : ℝ) :
    HasDerivAt (fun y => gaussDens m v y * (-(y - m) / v))
      (gaussDens m v y * ((y - m) ^ 2 / v ^ 2 - 1 / v)) y := by
  have h2 : HasDerivAt (fun y => -(y - m) / v) (-1 / v) y := by
    simpa using (((hasDerivAt_id y).sub_const m).neg).div_const v
  have := (hasDerivAt_gaussDens_y m v y).mul h2
  convert this using 1
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · field_simp; ring

/-- Time derivative of the Gaussian density along differentiable mean and variance curves. -/
lemma hasDerivAt_gaussDens_t {m v : ℝ → ℝ} {m' v' t : ℝ} (hm : HasDerivAt m m' t)
    (hv : HasDerivAt v v' t) (hv0 : 0 < v t) (y : ℝ) :
    HasDerivAt (fun s => gaussDens (m s) (v s) y)
      (gaussDens (m t) (v t) y *
        ((y - m t) * m' / v t + v' / (2 * v t) * ((y - m t) ^ 2 / v t - 1))) t := by
  unfold gaussDens
  have hu : 0 < 2 * π * v t := by positivity
  have hsq : HasDerivAt (fun s => √(2 * π * v s)) ((2 * π * v') / (2 * √(2 * π * v t))) t :=
    (hv.const_mul (2 * π)).sqrt hu.ne'
  have hsq0 : √(2 * π * v t) ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hc' := hsq.inv hsq0
  have hs2 : √(2 * π * v t) ^ 2 = 2 * π * v t := Real.sq_sqrt hu.le
  have hc : HasDerivAt (fun s => (√(2 * π * v s))⁻¹)
      (-(√(2 * π * v t))⁻¹ * v' / (2 * v t)) t := by
    convert hc' using 1
    rw [hs2]
    field_simp
  have he : HasDerivAt (fun s => -(y - m s) ^ 2 / (2 * v s))
      ((-(2 * (y - m t) * (-m')) * (2 * v t) - (-(y - m t) ^ 2) * (2 * v')) / (2 * v t) ^ 2) t := by
    have h1 : HasDerivAt (fun s => -(y - m s) ^ 2) (-(2 * (y - m t) * (-m'))) t := by
      have := ((hasDerivAt_const t y).sub hm).pow 2
      simpa using this.neg
    exact h1.div (hv.const_mul 2) (by positivity)
  have := hc.mul he.exp
  convert this using 1
  field_simp
  ring

/-- **The Gaussian solution of the Fokker–Planck equation of a linear SDE**: if `m' = -k m` and
`v' = D - 2 k v` with `v > 0`, `D ≥ 0`, then `p(t, y) = gaussDens (m t) (v t) y` satisfies
`∂ₜp = -∂_y[(-k y) p] + ½ ∂²_y[(√D)² p]` (Gardiner (4.3.20) for `a = -k y`, `b = √D`). -/
theorem gaussDens_fokkerPlanck_linear {k D : ℝ} (hD : 0 ≤ D) {m v : ℝ → ℝ} {t : ℝ}
    (hm : HasDerivAt m (-k * m t) t) (hv : HasDerivAt v (D - 2 * k * v t) t) (hv0 : 0 < v t)
    (y : ℝ) :
    HasDerivAt (fun s => gaussDens (m s) (v s) y)
      (itoFPRHS (fun z _ => -k * z) (fun _ _ => √D) (fun s z => gaussDens (m s) (v s) z) t y)
      t := by
  have ht := hasDerivAt_gaussDens_t hm hv hv0 y
  convert ht using 1
  set p := gaussDens (m t) (v t)
  have hA : deriv (fun z => -k * z * p z) y = -k * p y + -k * y * (p y * (-(y - m t) / v t)) := by
    have := ((hasDerivAt_id y).const_mul (-k)).mul (hasDerivAt_gaussDens_y (m t) (v t) y)
    simp only [mul_one, id] at this
    exact this.deriv
  have hB1 : deriv (fun z => √D ^ 2 * p z) = fun z => D * (p z * (-(z - m t) / v t)) := by
    funext z
    rw [Real.sq_sqrt hD]
    exact ((hasDerivAt_gaussDens_y (m t) (v t) z).const_mul D).deriv
  have hB2 : deriv (fun z => D * (p z * (-(z - m t) / v t))) y =
      D * (p y * ((y - m t) ^ 2 / v t ^ 2 - 1 / v t)) :=
    ((hasDerivAt_gaussDens_yy (m t) (v t) y).const_mul D).deriv
  simp only [itoFPRHS]
  rw [hA, hB1, hB2]
  field_simp
  ring

end Gardiner.Ito.Generator
