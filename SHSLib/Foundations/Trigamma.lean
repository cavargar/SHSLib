/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The trigamma function at `1`

This file proves the classical identity

  `(log ∘ Γ)'' (1) = π² / 6`,

i.e. `ψ'(1) = ζ(2)`, where `ψ = (log Γ)'` is the digamma function.

Mathlib provides Euler's reflection formula and Legendre's duplication formula
for `Real.Gamma`, but no polygamma theory; the value `ψ'(1)` is obtained here
from those two functional equations, avoiding any series manipulation:

* smoothness: `Complex.Gamma` is differentiable on the open half-plane
  `{re > 0}`, hence analytic there, and `Real.Gamma` is its restriction to the
  positive reals, so `log ∘ Γ` is `C^∞` on `(0, ∞)`
  (`SHSLib.Trigamma.contDiffAt_logGamma`);
* reflection: differentiating `log Γ(x) + log Γ(1 − x) = log π − log sin (π x)`
  twice at `x = 1/2` gives `ψ'(1/2) = π²/2`
  (`SHSLib.Trigamma.trigamma_half`);
* duplication: differentiating
  `log Γ(x) + log Γ(x + 1/2) = log Γ(2x) + (1 − 2x) log 2 + log √π`
  twice at `x = 1/2` gives `ψ'(1/2) + ψ'(1) = 4 ψ'(1)`
  (`SHSLib.Trigamma.trigamma_relation`),

and the two combine into `ψ'(1) = π²/6`
(`SHSLib.Trigamma.deriv_deriv_log_Gamma_one`).

The recurrence `Γ(x+1) = x Γ(x)`, differentiated twice, then propagates the two
values along the integers and the half-integers:
`ψ'(n+1) = π²/6 − ∑_{k<n} 1/(k+1)²` (`SHSLib.Trigamma.trigamma_nat_add_one`) and
`ψ'(n+1/2) = π²/2 − ∑_{k<n} 1/(k+1/2)²`
(`SHSLib.Trigamma.trigamma_nat_add_half`).
-/
import Mathlib

open Real Set Filter

namespace SHSLib.Trigamma

/-- `logGamma x = log (Γ x)`; on `(0, ∞)` this is the usual `log Γ`. -/
noncomputable def logGamma (x : ℝ) : ℝ := Real.log (Real.Gamma x)

theorem logGamma_eq_comp : Real.log ∘ Real.Gamma = logGamma := rfl

/-! ### Smoothness of `Γ` and of `log Γ` on the positive half-line -/

/-- `Real.Gamma` is `C^∞` at every positive real, obtained from the
differentiability (hence analyticity) of `Complex.Gamma` on `{re > 0}`. -/
theorem contDiffAt_Gamma {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ (⊤ : ℕ∞) Real.Gamma x := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have h1 : z.re = -(m : ℝ) := by rw [hm]; simp
    simp only [Set.mem_setOf_eq] at hz
    rw [h1] at hz
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hana : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := hdiff.analyticOnNhd hopen
  have h1 : ContDiffAt ℂ (⊤ : ℕ∞) Complex.Gamma (x : ℂ) := (hana _ (by simpa using hx)).contDiffAt
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) Complex.Gamma (x : ℂ) := h1.restrict_scalars ℝ
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (Complex.Gamma (y : ℂ)).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x
      (h2.comp x Complex.ofRealCLM.contDiff.contDiffAt)
  simpa [Complex.Gamma_ofReal] using h3

theorem contDiffAt_logGamma {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ (⊤ : ℕ∞) logGamma x :=
  (Real.contDiffAt_log.mpr (Real.Gamma_pos_of_pos hx).ne').comp x (contDiffAt_Gamma hx)

theorem contDiffOn_logGamma : ContDiffOn ℝ (⊤ : ℕ∞) logGamma (Ioi 0) :=
  fun _ hx => (contDiffAt_logGamma hx).contDiffWithinAt

theorem differentiableAt_logGamma {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ logGamma x :=
  (contDiffAt_logGamma hx).differentiableAt (by simp)

theorem contDiffOn_deriv_logGamma : ContDiffOn ℝ (⊤ : ℕ∞) (deriv logGamma) (Ioi 0) :=
  ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp contDiffOn_logGamma).2

/-- The digamma function `ψ = (log Γ)'` is differentiable on `(0, ∞)`. -/
theorem differentiableAt_deriv_logGamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv logGamma) x :=
  ((contDiffOn_deriv_logGamma x hx).differentiableWithinAt (by simp)).differentiableAt
    (Ioi_mem_nhds hx)

/-! ### Euler's reflection formula and `ψ'(1/2)` -/

theorem sin_pi_mul_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < Real.sin (π * x) := by
  obtain ⟨h0, h1⟩ := hx
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  nlinarith [Real.pi_pos]

/-- The logarithmic form of Euler's reflection formula on `(0, 1)`. -/
theorem reflection_logGamma {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    logGamma x + logGamma (1 - x) = Real.log π - Real.log (Real.sin (π * x)) := by
  obtain ⟨h0, h1⟩ := hx
  have hg1 : 0 < Real.Gamma x := Real.Gamma_pos_of_pos h0
  have hg2 : 0 < Real.Gamma (1 - x) := Real.Gamma_pos_of_pos (by linarith)
  have hs : 0 < Real.sin (π * x) := sin_pi_mul_pos ⟨h0, h1⟩
  have h := congrArg Real.log (Real.Gamma_mul_Gamma_one_sub x)
  rwa [Real.log_mul hg1.ne' hg2.ne', Real.log_div Real.pi_ne_zero hs.ne'] at h

/-- The first derivative of the reflection formula: `ψ(x) − ψ(1 − x) = −π cot (π x)`. -/
theorem reflection_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv logGamma x - deriv logGamma (1 - x)
      = -(π * Real.cos (π * x) / Real.sin (π * x)) := by
  obtain ⟨h0, h1⟩ := hx
  have hs : 0 < Real.sin (π * x) := sin_pi_mul_pos ⟨h0, h1⟩
  have hEq : (fun y : ℝ => logGamma y + logGamma (1 - y))
      =ᶠ[nhds x] fun y : ℝ => Real.log π - Real.log (Real.sin (π * y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo (0 : ℝ) 1 from ⟨h0, h1⟩)] with y hy
    exact reflection_logGamma hy
  have hA : HasDerivAt logGamma (deriv logGamma x) x := (differentiableAt_logGamma h0).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => logGamma (1 - y)) (deriv logGamma (1 - x) * (-1)) x := by
    have h2 : HasDerivAt logGamma (deriv logGamma (1 - x)) (1 - x) :=
      (differentiableAt_logGamma (by linarith)).hasDerivAt
    exact h2.comp x ((hasDerivAt_id x).const_sub 1)
  have hAB : HasDerivAt (fun y : ℝ => logGamma y + logGamma (1 - y))
      (deriv logGamma x + deriv logGamma (1 - x) * (-1)) x := hA.add hB
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (π * y)) (Real.cos (π * x) * π) x := by
    simpa using (Real.hasDerivAt_sin (π * x)).comp x ((hasDerivAt_id x).const_mul π)
  have hC : HasDerivAt (fun y : ℝ => Real.log π - Real.log (Real.sin (π * y)))
      (-(Real.cos (π * x) * π / Real.sin (π * x))) x := (hsin.log hs.ne').const_sub (Real.log π)
  have hd := hEq.deriv_eq
  rw [hAB.deriv, hC.deriv] at hd
  rw [show deriv logGamma x - deriv logGamma (1 - x)
      = deriv logGamma x + deriv logGamma (1 - x) * (-1) by ring, hd]
  ring

/-- `ψ'(1/2) = π²/2`, from the second derivative of the reflection formula. -/
theorem trigamma_half : deriv (deriv logGamma) (1 / 2) = π ^ 2 / 2 := by
  have hx : (1 : ℝ) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hEq : (fun y : ℝ => deriv logGamma y - deriv logGamma (1 - y))
      =ᶠ[nhds (1 / 2 : ℝ)] fun y : ℝ => -(π * Real.cos (π * y) / Real.sin (π * y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact reflection_deriv hy
  have hA : HasDerivAt (deriv logGamma) (deriv (deriv logGamma) (1 / 2)) (1 / 2 : ℝ) :=
    (differentiableAt_deriv_logGamma (by norm_num)).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => deriv logGamma (1 - y))
      (deriv (deriv logGamma) (1 / 2) * (-1)) (1 / 2 : ℝ) := by
    have h2 : HasDerivAt (deriv logGamma) (deriv (deriv logGamma) (1 - 1 / 2)) (1 - 1 / 2 : ℝ) :=
      (differentiableAt_deriv_logGamma (by norm_num)).hasDerivAt
    have h3 := h2.comp (1 / 2 : ℝ) ((hasDerivAt_id (1 / 2 : ℝ)).const_sub 1)
    norm_num at h3 ⊢
    convert h3 using 1
  have hAB : HasDerivAt (fun y : ℝ => deriv logGamma y - deriv logGamma (1 - y))
      (deriv (deriv logGamma) (1 / 2) - deriv (deriv logGamma) (1 / 2) * (-1)) (1 / 2 : ℝ) :=
    hA.sub hB
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (π * y))
      (Real.cos (π * (1 / 2 : ℝ)) * π) (1 / 2 : ℝ) := by
    simpa using
      (Real.hasDerivAt_sin (π * (1 / 2 : ℝ))).comp (1 / 2 : ℝ)
        ((hasDerivAt_id (1 / 2 : ℝ)).const_mul π)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (π * y))
      (-Real.sin (π * (1 / 2 : ℝ)) * π) (1 / 2 : ℝ) := by
    simpa using
      (Real.hasDerivAt_cos (π * (1 / 2 : ℝ))).comp (1 / 2 : ℝ)
        ((hasDerivAt_id (1 / 2 : ℝ)).const_mul π)
  have hs1 : Real.sin (π * (1 / 2 : ℝ)) = 1 := by
    rw [show π * (1 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two]
  have hc0 : Real.cos (π * (1 / 2 : ℝ)) = 0 := by
    rw [show π * (1 / 2 : ℝ) = π / 2 by ring, Real.cos_pi_div_two]
  have hdiv := hcos.div hsin (by rw [hs1]; norm_num)
  have hG : HasDerivAt (fun y : ℝ => -(π * (Real.cos (π * y) / Real.sin (π * y)))) (π ^ 2)
      (1 / 2 : ℝ) := by
    have h := (hdiv.const_mul π).neg
    convert h using 1
    rw [hs1, hc0]
    ring
  have hd := hEq.deriv_eq
  rw [hAB.deriv] at hd
  rw [show (fun y : ℝ => -(π * Real.cos (π * y) / Real.sin (π * y)))
      = fun y : ℝ => -(π * (Real.cos (π * y) / Real.sin (π * y))) by ext y; ring] at hd
  rw [hG.deriv] at hd
  linarith [hd]

/-! ### Legendre's duplication formula and the relation between `ψ'(1/2)` and `ψ'(1)` -/

/-- The logarithmic form of Legendre's duplication formula on `(0, ∞)`. -/
theorem duplication_logGamma {x : ℝ} (hx : 0 < x) :
    logGamma x + logGamma (x + 1 / 2)
      = logGamma (2 * x) + (1 - 2 * x) * Real.log 2 + Real.log (√π) := by
  have h1 : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have h2 : 0 < Real.Gamma (x + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h3 : 0 < Real.Gamma (2 * x) := Real.Gamma_pos_of_pos (by linarith)
  have h4 : (0 : ℝ) < 2 ^ (1 - 2 * x) := Real.rpow_pos_of_pos (by norm_num) _
  have h5 : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have h := congrArg Real.log (Real.Gamma_mul_Gamma_add_half x)
  rw [Real.log_mul h1.ne' h2.ne', Real.log_mul (by positivity) h5.ne',
    Real.log_mul h3.ne' h4.ne', Real.log_rpow (by norm_num)] at h
  simpa [logGamma] using h

/-- The first derivative of the duplication formula:
`ψ(x) + ψ(x + 1/2) = 2 ψ(2x) − 2 log 2`. -/
theorem duplication_deriv {x : ℝ} (hx : 0 < x) :
    deriv logGamma x + deriv logGamma (x + 1 / 2)
      = deriv logGamma (2 * x) * 2 - 2 * Real.log 2 := by
  have hEq : (fun y : ℝ => logGamma y + logGamma (y + 1 / 2))
      =ᶠ[nhds x] fun y : ℝ => logGamma (2 * y) + (1 - 2 * y) * Real.log 2 + Real.log (√π) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with y hy
    exact duplication_logGamma hy
  have hshift : HasDerivAt (fun y : ℝ => y + 1 / 2) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 / 2 : ℝ)
  have hdouble : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hA : HasDerivAt logGamma (deriv logGamma x) x := (differentiableAt_logGamma hx).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => logGamma (y + 1 / 2)) (deriv logGamma (x + 1 / 2)) x := by
    have h2 : HasDerivAt logGamma (deriv logGamma (x + 1 / 2)) (x + 1 / 2) :=
      (differentiableAt_logGamma (by linarith)).hasDerivAt
    simpa using h2.comp x hshift
  have hAB : HasDerivAt (fun y : ℝ => logGamma y + logGamma (y + 1 / 2))
      (deriv logGamma x + deriv logGamma (x + 1 / 2)) x := hA.add hB
  have hC : HasDerivAt (fun y : ℝ => logGamma (2 * y)) (deriv logGamma (2 * x) * 2) x := by
    have h2 : HasDerivAt logGamma (deriv logGamma (2 * x)) (2 * x) :=
      (differentiableAt_logGamma (by linarith)).hasDerivAt
    exact h2.comp x hdouble
  have hD : HasDerivAt
      (fun y : ℝ => logGamma (2 * y) + (1 - 2 * y) * Real.log 2 + Real.log (√π))
      (deriv logGamma (2 * x) * 2 + -2 * Real.log 2) x := by
    have h1 : HasDerivAt (fun y : ℝ => (1 - 2 * y) * Real.log 2) (-2 * Real.log 2) x := by
      simpa using (hdouble.const_sub 1).mul_const (Real.log 2)
    simpa using (hC.add h1).add_const (Real.log (√π))
  have hd := hEq.deriv_eq
  rw [hAB.deriv, hD.deriv] at hd
  rw [hd]; ring

/-- The second derivative of the duplication formula at `1/2`:
`ψ'(1/2) + ψ'(1) = 4 ψ'(1)`. -/
theorem trigamma_relation :
    deriv (deriv logGamma) (1 / 2) + deriv (deriv logGamma) 1
      = 4 * deriv (deriv logGamma) 1 := by
  have hEq : (fun y : ℝ => deriv logGamma y + deriv logGamma (y + 1 / 2))
      =ᶠ[nhds (1 / 2 : ℝ)] fun y : ℝ => deriv logGamma (2 * y) * 2 - 2 * Real.log 2 := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 / 2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)] with y hy
    exact duplication_deriv hy
  have hshift : HasDerivAt (fun y : ℝ => y + 1 / 2) 1 (1 / 2 : ℝ) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).add_const (1 / 2 : ℝ)
  have hdouble : HasDerivAt (fun y : ℝ => 2 * y) 2 (1 / 2 : ℝ) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_mul (2 : ℝ)
  have hone : HasDerivAt (deriv logGamma) (deriv (deriv logGamma) 1) (1 : ℝ) :=
    (differentiableAt_deriv_logGamma (by norm_num)).hasDerivAt
  have hA : HasDerivAt (deriv logGamma) (deriv (deriv logGamma) (1 / 2)) (1 / 2 : ℝ) :=
    (differentiableAt_deriv_logGamma (by norm_num)).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => deriv logGamma (y + 1 / 2))
      (deriv (deriv logGamma) 1) (1 / 2 : ℝ) := by
    simpa [Function.comp_def] using hone.comp_of_eq (1 / 2 : ℝ) hshift (by norm_num)
  have hAB : HasDerivAt (fun y : ℝ => deriv logGamma y + deriv logGamma (y + 1 / 2))
      (deriv (deriv logGamma) (1 / 2) + deriv (deriv logGamma) 1) (1 / 2 : ℝ) := hA.add hB
  have hC : HasDerivAt (fun y : ℝ => deriv logGamma (2 * y) * 2 - 2 * Real.log 2)
      (deriv (deriv logGamma) 1 * 2 * 2) (1 / 2 : ℝ) := by
    have h3 : HasDerivAt (fun y : ℝ => deriv logGamma (2 * y))
        (deriv (deriv logGamma) 1 * 2) (1 / 2 : ℝ) := by
      simpa [Function.comp_def] using hone.comp_of_eq (1 / 2 : ℝ) hdouble (by norm_num)
    simpa using (h3.mul_const (2 : ℝ)).sub_const (2 * Real.log 2)
  have hd := hEq.deriv_eq
  rw [hAB.deriv, hC.deriv] at hd
  rw [hd]; ring

/-! ### The value of the trigamma function at `1` -/

/-- `ψ'(1) = π²/6`, in the form `(log Γ)''(1) = π²/6`. -/
theorem trigamma_one : deriv (deriv logGamma) 1 = π ^ 2 / 6 := by
  have h1 := trigamma_half
  have h2 := trigamma_relation
  linarith

/-- **The trigamma function at one.** The second derivative of `log ∘ Γ` at `1`
equals `π²/6 = ζ(2)`. -/
theorem deriv_deriv_log_Gamma_one :
    deriv (deriv (Real.log ∘ Real.Gamma)) 1 = π ^ 2 / 6 := by
  rw [logGamma_eq_comp]
  exact trigamma_one

/-! ### The recurrence, and the values at the positive integers and half-integers -/

/-- The logarithmic form of the functional equation `Γ(x+1) = x Γ(x)`. -/
theorem logGamma_add_one {x : ℝ} (hx : 0 < x) :
    logGamma (x + 1) = Real.log x + logGamma x := by
  have h := Real.Gamma_add_one hx.ne'
  rw [logGamma, logGamma, h, Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']

/-- The digamma recurrence `ψ(x+1) = ψ(x) + 1/x`. -/
theorem digamma_add_one {x : ℝ} (hx : 0 < x) :
    deriv logGamma (x + 1) = deriv logGamma x + 1 / x := by
  have hEq : (fun y : ℝ => logGamma (y + 1))
      =ᶠ[nhds x] fun y : ℝ => Real.log y + logGamma y := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with y hy
    exact logGamma_add_one hy
  have hA : HasDerivAt (fun y : ℝ => logGamma (y + 1)) (deriv logGamma (x + 1)) x :=
    HasDerivAt.comp_add_const x 1 (differentiableAt_logGamma (by linarith)).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => Real.log y + logGamma y)
      (1 / x + deriv logGamma x) x := by
    simpa using (Real.hasDerivAt_log hx.ne').add (differentiableAt_logGamma hx).hasDerivAt
  have hd := hEq.deriv_eq
  rw [hA.deriv, hB.deriv] at hd
  rw [hd]; ring

/-- The trigamma recurrence `ψ'(x+1) = ψ'(x) − 1/x²`. -/
theorem trigamma_add_one {x : ℝ} (hx : 0 < x) :
    deriv (deriv logGamma) (x + 1) = deriv (deriv logGamma) x - 1 / x ^ 2 := by
  have hEq : (fun y : ℝ => deriv logGamma (y + 1))
      =ᶠ[nhds x] fun y : ℝ => deriv logGamma y + 1 / y := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with y hy
    exact digamma_add_one hy
  have hA : HasDerivAt (fun y : ℝ => deriv logGamma (y + 1))
      (deriv (deriv logGamma) (x + 1)) x :=
    HasDerivAt.comp_add_const x 1 (differentiableAt_deriv_logGamma (by linarith)).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => deriv logGamma y + 1 / y)
      (deriv (deriv logGamma) x + -(x ^ 2)⁻¹) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1 / y) (-(x ^ 2)⁻¹) x := by
      simpa using hasDerivAt_inv hx.ne'
    exact (differentiableAt_deriv_logGamma hx).hasDerivAt.add h1
  have hd := hEq.deriv_eq
  rw [hA.deriv, hB.deriv] at hd
  rw [hd, one_div]
  ring

/-- **The trigamma function at the positive integers**:
`ψ'(n+1) = π²/6 − ∑_{k<n} 1/(k+1)²`, the tail of the Basel series. -/
theorem trigamma_nat_add_one (n : ℕ) :
    deriv (deriv logGamma) ((n : ℝ) + 1)
      = π ^ 2 / 6 - ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2 := by
  induction n with
  | zero => simpa using trigamma_one
  | succ n ih =>
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h := trigamma_add_one hpos
      rw [show ((n : ℝ) + 1 + 1) = ((n + 1 : ℕ) : ℝ) + 1 by push_cast; ring] at h
      rw [h, ih, Finset.sum_range_succ]
      ring

/-- **The trigamma function at the positive half-integers**:
`ψ'(n + 1/2) = π²/2 − ∑_{k<n} 1/(k + 1/2)²`. -/
theorem trigamma_nat_add_half (n : ℕ) :
    deriv (deriv logGamma) ((n : ℝ) + 1 / 2)
      = π ^ 2 / 2 - ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1 / 2) ^ 2 := by
  induction n with
  | zero => simpa using trigamma_half
  | succ n ih =>
      have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
      have h := trigamma_add_one hpos
      rw [show ((n : ℝ) + 1 / 2 + 1) = ((n + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring] at h
      rw [h, ih, Finset.sum_range_succ]
      ring

/-- `ψ'(1)` is the Basel sum. -/
theorem trigamma_one_eq_tsum :
    deriv (deriv logGamma) 1 = ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
  rw [trigamma_one, hasSum_zeta_two.tsum_eq]

/-! ### The limits along the two progressions, and the two Basel series -/

/-- **Legendre duplication for the trigamma function**, at every positive point:
`ψ'(x) + ψ'(x + 1/2) = 4 ψ'(2x)`.  `trigamma_relation` is the case `x = 1/2`. -/
theorem trigamma_duplication {x : ℝ} (hx : 0 < x) :
    deriv (deriv logGamma) x + deriv (deriv logGamma) (x + 1 / 2)
      = 4 * deriv (deriv logGamma) (2 * x) := by
  have hEq : (fun y : ℝ => deriv logGamma y + deriv logGamma (y + 1 / 2))
      =ᶠ[nhds x] fun y : ℝ => deriv logGamma (2 * y) * 2 - 2 * Real.log 2 := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with y hy
    exact duplication_deriv hy
  have hdouble : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hA : HasDerivAt (deriv logGamma) (deriv (deriv logGamma) x) x :=
    (differentiableAt_deriv_logGamma hx).hasDerivAt
  have hB : HasDerivAt (fun y : ℝ => deriv logGamma (y + 1 / 2))
      (deriv (deriv logGamma) (x + 1 / 2)) x :=
    HasDerivAt.comp_add_const x (1 / 2)
      (differentiableAt_deriv_logGamma (by linarith)).hasDerivAt
  have hAB : HasDerivAt (fun y : ℝ => deriv logGamma y + deriv logGamma (y + 1 / 2))
      (deriv (deriv logGamma) x + deriv (deriv logGamma) (x + 1 / 2)) x := hA.add hB
  have hC : HasDerivAt (fun y : ℝ => deriv logGamma (2 * y) * 2 - 2 * Real.log 2)
      (deriv (deriv logGamma) (2 * x) * 2 * 2) x := by
    have h2 : HasDerivAt (deriv logGamma) (deriv (deriv logGamma) (2 * x)) (2 * x) :=
      (differentiableAt_deriv_logGamma (by linarith)).hasDerivAt
    have h3 : HasDerivAt (fun y : ℝ => deriv logGamma (2 * y))
        (deriv (deriv logGamma) (2 * x) * 2) x := h2.comp x hdouble
    simpa using (h3.mul_const (2 : ℝ)).sub_const (2 * Real.log 2)
  have hd := hEq.deriv_eq
  rw [hAB.deriv, hC.deriv] at hd
  rw [hd]; ring

/-- The Basel series in its shifted form. -/
theorem hasSum_basel_shift : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h : HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    have h0 : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2)
        (π ^ 2 / 6 + ∑ i ∈ Finset.range 1, 1 / (i : ℝ) ^ 2) := by
      simpa using hasSum_zeta_two
    exact (hasSum_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h0
  simpa using h

/-- The trigamma function vanishes along the integers: the Basel tails go to zero. -/
theorem tendsto_trigamma_nat_add_one :
    Tendsto (fun n : ℕ => deriv (deriv logGamma) ((n : ℝ) + 1)) atTop (nhds 0) := by
  have hsum := hasSum_basel_shift.tendsto_sum_nat
  have h : Tendsto (fun n : ℕ => π ^ 2 / 6 - ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2)
      atTop (nhds (π ^ 2 / 6 - π ^ 2 / 6)) := tendsto_const_nhds.sub hsum
  simpa [trigamma_nat_add_one] using h

/-- The trigamma function vanishes along the half-integers as well; this is read
off the duplication formula from the integer case, no asymptotics required. -/
theorem tendsto_trigamma_nat_add_half :
    Tendsto (fun n : ℕ => deriv (deriv logGamma) ((n : ℝ) + 1 / 2)) atTop (nhds 0) := by
  set a : ℕ → ℝ := fun m => deriv (deriv logGamma) ((m : ℝ) + 1) with ha
  have hkey : ∀ n : ℕ,
      deriv (deriv logGamma) (((n : ℝ) + 1) + 1 / 2) = 4 * a (2 * n + 1) - a n := by
    intro n
    have h := trigamma_duplication (x := (n : ℝ) + 1) (by positivity)
    have h2 : (2 : ℝ) * ((n : ℝ) + 1) = ((2 * n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2] at h
    simp only [ha] at *
    linarith
  have hstep : Tendsto (fun n : ℕ => 4 * a (2 * n + 1) - a n) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => a (2 * n + 1)) atTop (nhds 0) :=
      tendsto_trigamma_nat_add_one.comp (tendsto_atTop_atTop_of_monotone
        (fun _ _ hij => by omega) (fun b => ⟨b, by omega⟩))
    have h2 := (h1.const_mul (4 : ℝ)).sub tendsto_trigamma_nat_add_one
    simpa using h2
  have hshift : Tendsto (fun n : ℕ => deriv (deriv logGamma) (((n : ℝ) + 1) + 1 / 2))
      atTop (nhds 0) := hstep.congr fun n => (hkey n).symm
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hshift.congr fun n => ?_
  push_cast
  ring_nf

theorem summable_inv_sq_add_half : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1 / 2) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hasSum_basel_shift.summable.mul_left 4)
  have h1 : (0 : ℝ) < ((k : ℝ) + 1 / 2) ^ 2 := by positivity
  have h2 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show (4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) = 4 / ((k : ℝ) + 1) ^ 2 by ring,
    div_le_div_iff₀ h1 h2]
  nlinarith

/-- **The odd-denominator Basel series**: `∑_{k ≥ 0} 1/(k + 1/2)² = π²/2`, the
limiting form of the half-integer trigamma values. -/
theorem hasSum_inv_sq_add_half :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1 / 2) ^ 2) (π ^ 2 / 2) := by
  have hpartial : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1 / 2) ^ 2)
      atTop (nhds (π ^ 2 / 2)) := by
    have h : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1 / 2) ^ 2
        = π ^ 2 / 2 - deriv (deriv logGamma) ((n : ℝ) + 1 / 2) := by
      intro n; rw [trigamma_nat_add_half]; ring
    have h2 : Tendsto (fun n : ℕ => π ^ 2 / 2 - deriv (deriv logGamma) ((n : ℝ) + 1 / 2))
        atTop (nhds (π ^ 2 / 2 - 0)) := tendsto_const_nhds.sub tendsto_trigamma_nat_add_half
    rw [sub_zero] at h2
    exact h2.congr fun n => (h n).symm
  have hs := summable_inv_sq_add_half
  have heq : ∑' k : ℕ, 1 / ((k : ℝ) + 1 / 2) ^ 2 = π ^ 2 / 2 :=
    tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hpartial
  exact heq ▸ hs.hasSum

end SHSLib.Trigamma
