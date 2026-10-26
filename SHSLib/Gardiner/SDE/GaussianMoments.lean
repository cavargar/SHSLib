/-
# Moments of a centred Gaussian increment (Gardiner §10.1.4)

The numerical schemes of Gardiner Ch. 10 are driven by i.i.d. Gaussian increments
`ΔW ~ N(0, τ)`.  Every moment computation in the chapter only uses the first four moments

  `⟨ΔW⟩ = 0`, `⟨ΔW²⟩ = τ`, `⟨ΔW³⟩ = 0`, `⟨ΔW⁴⟩ = 3τ²`,

which we derive here from the moment generating function `exp(τ t²/2)` of `gaussianReal 0 τ`
(Mathlib only provides the first two).  As a corollary we obtain the three identities listed after
(10.1.21):

* i)  `⟨ΔW² - τ⟩ = 0`               (`Gardiner.SDE.gauss_i`);
* ii) `⟨(ΔW² - τ)²⟩ = 2τ²`          (`Gardiner.SDE.gauss_ii`);
* iii) `⟨ΔW(ΔW² - τ)⟩ = 0`           (`Gardiner.SDE.gauss_iii`);

and the expectation of an arbitrary polynomial of degree `≤ 4` in `ΔW`
(`Gardiner.SDE.gauss_poly4`).
-/
import Mathlib

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section

namespace Gardiner.SDE

/-- The moment generating function of `N(0, v)`. -/
private def gm (v : ℝ) (t : ℝ) : ℝ := Real.exp (v * t ^ 2 / 2)

private lemma hasDerivAt_poly_gm (v : ℝ) (P : ℝ → ℝ) (p t : ℝ) (hP : HasDerivAt P p t) :
    HasDerivAt (fun s => P s * gm v s) ((p + P t * (v * t)) * gm v t) t := by
  have hg : HasDerivAt (gm v) (gm v t * (v * t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => v * s ^ 2 / 2) (v * t) t := by
      have := ((hasDerivAt_pow 2 t).const_mul v).div_const 2
      convert this using 1; push_cast; ring
    exact h1.exp
  convert hP.mul hg using 1
  ring

private lemma iteratedDeriv_gm (v : ℝ) :
    iteratedDeriv 2 (gm v) = (fun t => (v + v ^ 2 * t ^ 2) * gm v t) ∧
    iteratedDeriv 3 (gm v) = (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gm v t) ∧
    iteratedDeriv 4 (gm v) =
      (fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * gm v t) := by
  have d1 : deriv (gm v) = fun t => (v * t) * gm v t := by
    funext t
    have := hasDerivAt_poly_gm v (fun _ => 1) 0 t (hasDerivAt_const t 1)
    simp only [one_mul, zero_add] at this
    exact this.deriv
  have d2 : deriv (fun t => (v * t) * gm v t) = fun t => (v + v ^ 2 * t ^ 2) * gm v t := by
    funext t
    have hP : HasDerivAt (fun s : ℝ => v * s) v t := by
      simpa using (hasDerivAt_id t).const_mul v
    rw [(hasDerivAt_poly_gm v _ v t hP).deriv]; ring
  have d3 : deriv (fun t => (v + v ^ 2 * t ^ 2) * gm v t) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gm v t := by
    funext t
    have hP : HasDerivAt (fun s : ℝ => v + v ^ 2 * s ^ 2) (v ^ 2 * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (v ^ 2)).const_add v
      convert this using 1; push_cast; ring
    rw [(hasDerivAt_poly_gm v _ _ t hP).deriv]; ring
  have d4 : deriv (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gm v t) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * gm v t := by
    funext t
    have hP : HasDerivAt (fun s : ℝ => 3 * v ^ 2 * s + v ^ 3 * s ^ 3)
        (3 * v ^ 2 + v ^ 3 * (3 * t ^ 2)) t := by
      have h1 : HasDerivAt (fun s : ℝ => 3 * v ^ 2 * s) (3 * v ^ 2) t := by
        simpa using (hasDerivAt_id t).const_mul (3 * v ^ 2)
      have h2 := (hasDerivAt_pow 3 t).const_mul (v ^ 3)
      convert h1.add h2 using 1
    rw [(hasDerivAt_poly_gm v _ _ t hP).deriv]; ring
  have e2 : iteratedDeriv 2 (gm v) = fun t => (v + v ^ 2 * t ^ 2) * gm v t := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, d1, d2]
  have e3 : iteratedDeriv 3 (gm v) = fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gm v t := by
    rw [iteratedDeriv_succ, e2, d3]
  have e4 : iteratedDeriv 4 (gm v) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * gm v t := by
    rw [iteratedDeriv_succ, e3, d4]
  exact ⟨e2, e3, e4⟩

private lemma moment_eq_iteratedDeriv (v : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal 0 v) = iteratedDeriv n (gm v) 0 := by
  have hm : mgf (fun x => x) (gaussianReal 0 v) = gm v := by
    rw [mgf_fun_id_gaussianReal]; funext t; simp [gm]
  rw [← hm, iteratedDeriv_mgf_zero]
  · rfl
  · have : integrableExpSet (fun x : ℝ => x) (gaussianReal 0 v) = Set.univ :=
      integrableExpSet_id_gaussianReal
    simp [this]

/-- First moment of `N(0, v)`. -/
theorem gauss_m1 (v : ℝ≥0) : ∫ x, x ∂(gaussianReal 0 v) = 0 := by simp

/-- Second moment of `N(0, v)`. -/
theorem gauss_m2 (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  rw [moment_eq_iteratedDeriv, (iteratedDeriv_gm v).1]; simp [gm]

/-- Third moment of `N(0, v)`. -/
theorem gauss_m3 (v : ℝ≥0) : ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
  rw [moment_eq_iteratedDeriv, (iteratedDeriv_gm v).2.1]; simp [gm]

/-- Fourth moment of `N(0, v)`: `⟨ΔW⁴⟩ = 3τ²`. -/
theorem gauss_m4 (v : ℝ≥0) : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  rw [moment_eq_iteratedDeriv, (iteratedDeriv_gm v).2.2]; simp [gm]

/-- Every power of a Gaussian increment is integrable. -/
lemma gauss_integrable_pow (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h : MemLp (fun x : ℝ => x) (n : ℝ≥0) (gaussianReal 0 v) := memLp_id_gaussianReal _
  have h' := h.integrable_norm_pow (by omega)
  refine h'.mono' (continuous_pow n).aestronglyMeasurable (Filter.Eventually.of_forall
    fun x => ?_)
  simp [Real.norm_eq_abs]

/-- Expectation of a polynomial of degree `≤ 4` in a `N(0, v)` increment. -/
theorem gauss_poly4 (v : ℝ≥0) (c₀ c₁ c₂ c₃ c₄ : ℝ) :
    ∫ x, (c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) ∂(gaussianReal 0 v) =
      c₀ + c₂ * v + 3 * c₄ * (v : ℝ) ^ 2 := by
  have i1 : Integrable (fun x : ℝ => c₁ * x) (gaussianReal 0 v) := by
    simpa using (gauss_integrable_pow v 1).const_mul c₁
  have i2 := (gauss_integrable_pow v 2).const_mul c₂
  have i3 := (gauss_integrable_pow v 3).const_mul c₃
  have i4 := (gauss_integrable_pow v 4).const_mul c₄
  have i0 : Integrable (fun _ : ℝ => c₀) (gaussianReal 0 v) := integrable_const _
  have j1 : Integrable (fun x : ℝ => c₀ + c₁ * x) (gaussianReal 0 v) := i0.add i1
  have j2 : Integrable (fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2) (gaussianReal 0 v) := j1.add i2
  have j3 : Integrable (fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3)
      (gaussianReal 0 v) := j2.add i3
  rw [integral_add j3 i4, integral_add j2 i3,
    integral_add j1 i2, integral_add i0 i1, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, gauss_m1, gauss_m2, gauss_m3, gauss_m4]
  simp; ring

/-- (10.1.21) i): `⟨ΔW² - τ⟩ = 0`. -/
theorem gauss_i (τ : ℝ≥0) : ∫ x, (x ^ 2 - τ) ∂(gaussianReal 0 τ) = 0 := by
  have := gauss_poly4 τ (-τ) 0 1 0 0
  rw [show (fun x : ℝ => x ^ 2 - τ) =
      fun x => -(τ : ℝ) + 0 * x + 1 * x ^ 2 + 0 * x ^ 3 + 0 * x ^ 4 by
    funext x; ring, this]
  ring

/-- (10.1.21) ii): `⟨(ΔW² - τ)²⟩ = 2τ²`. -/
theorem gauss_ii (τ : ℝ≥0) : ∫ x, (x ^ 2 - τ) ^ 2 ∂(gaussianReal 0 τ) = 2 * (τ : ℝ) ^ 2 := by
  have := gauss_poly4 τ ((τ : ℝ) ^ 2) 0 (-2 * τ) 0 1
  rw [show (fun x : ℝ => (x ^ 2 - τ) ^ 2) =
      fun x => (τ : ℝ) ^ 2 + 0 * x + (-2 * τ) * x ^ 2 + 0 * x ^ 3 + 1 * x ^ 4 by
    funext x; ring, this]
  ring

/-- (10.1.21) iii): `⟨ΔW (ΔW² - τ)⟩ = 0`. -/
theorem gauss_iii (τ : ℝ≥0) : ∫ x, x * (x ^ 2 - τ) ∂(gaussianReal 0 τ) = 0 := by
  have := gauss_poly4 τ 0 (-τ) 0 1 0
  rw [show (fun x : ℝ => x * (x ^ 2 - τ)) =
      fun x => 0 + (-(τ : ℝ)) * x + 0 * x ^ 2 + 1 * x ^ 3 + 0 * x ^ 4 by
    funext x; ring, this]
  ring

end Gardiner.SDE
