/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Euler integral for the real Beta function

Batch 167 defined `B(x,y) = Γ(x)Γ(y)/Γ(x+y)` and studied its asymptotics.
This batch identifies it with Euler's integral of the first kind,

  `B(x,y) = ∫₀¹ t^{x−1}(1−t)^{y−1} dt`   (`x, y > 0`),

by descending Mathlib's complex `Complex.Gamma_mul_Gamma_eq_betaIntegral` to
the reals: on `[0,1]` the complex integrand is the coercion of the real one
(`Complex.ofReal_cpow`), so the two interval integrals agree.

Three consequences are recorded:

* `B(½,½) = π`, i.e. `∫₀¹ dt/√(t(1−t)) = π`;
* `B(k+1, m+1) = k!·m!/(k+m+1)!` for naturals;
* the classical `∫₀¹ t^k(1−t)^{m} dt = k!·m!/(k+m+1)!`.
-/
import SHSLib.Foundations.StirlingBeta

open Real Set Filter Topology intervalIntegral

namespace SHSLib.Trigamma

/-- Mathlib's complex Beta integral at real arguments is the coercion of the
real interval integral. -/
theorem complex_betaIntegral_ofReal (x y : ℝ) :
    Complex.betaIntegral x y
      = ((∫ t in (0:ℝ)..1, t ^ (x - 1) * (1 - t) ^ (y - 1) : ℝ) : ℂ) := by
  rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  have h1 : ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((y : ℂ) - 1) = ((y - 1 : ℝ) : ℂ) := by push_cast; ring
  have h3 : (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  simp only [h1, h2, h3]
  rw [← Complex.ofReal_cpow ht.1, ← Complex.ofReal_cpow (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
  push_cast
  ring

/-- **Euler's integral of the first kind**: for `x, y > 0`,
`B(x,y) = ∫₀¹ t^{x−1}(1−t)^{y−1} dt`. -/
theorem betaFn_eq_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    betaFn x y = ∫ t in (0:ℝ)..1, t ^ (x - 1) * (1 - t) ^ (y - 1) := by
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (x:ℂ)) (t := (y:ℂ))
    (by simpa using hx) (by simpa using hy)
  rw [complex_betaIntegral_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_add, Complex.Gamma_ofReal] at hG
  have hGr : Real.Gamma x * Real.Gamma y
      = Real.Gamma (x + y) * ∫ t in (0:ℝ)..1, t ^ (x - 1) * (1 - t) ^ (y - 1) := by
    exact_mod_cast hG
  unfold betaFn
  rw [hGr]
  field_simp

/-- `B(½,½) = π`, i.e. `∫₀¹ dt/√(t(1−t)) = π`. -/
theorem betaFn_half_half : betaFn (1 / 2) (1 / 2) = π := by
  unfold betaFn
  rw [Real.Gamma_one_half_eq]
  norm_num [Real.mul_self_sqrt Real.pi_pos.le, Real.Gamma_one]

/-- `∫₀¹ t^{−1/2}(1−t)^{−1/2} dt = π` (the exponent `1/2 − 1` is `−1/2`). -/
theorem integral_inv_sqrt_mul_one_sub : (∫ t in (0:ℝ)..1,
    t ^ ((1:ℝ) / 2 - 1) * (1 - t) ^ ((1:ℝ) / 2 - 1)) = π := by
  rw [← betaFn_eq_integral (x := (1:ℝ) / 2) (y := (1:ℝ) / 2) (by norm_num) (by norm_num),
    betaFn_half_half]

/-- `B(k+1, m+1) = k!·m!/(k+m+1)!` for natural `k`, `m`. -/
theorem betaFn_nat_succ (k m : ℕ) :
    betaFn ((k : ℝ) + 1) ((m : ℝ) + 1)
      = (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ) / (Nat.factorial (k + m + 1) : ℝ) := by
  have hk : Real.Gamma ((k : ℝ) + 1) = (Nat.factorial k : ℝ) := Real.Gamma_nat_eq_factorial k
  have hm : Real.Gamma ((m : ℝ) + 1) = (Nat.factorial m : ℝ) := Real.Gamma_nat_eq_factorial m
  have hsum : ((k : ℝ) + 1) + ((m : ℝ) + 1) = ((k + m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have hkm : Real.Gamma (((k + m + 1 : ℕ) : ℝ) + 1) = (Nat.factorial (k + m + 1) : ℝ) :=
    Real.Gamma_nat_eq_factorial (k + m + 1)
  unfold betaFn
  rw [hk, hm, hsum, hkm]

/-- **The classical Beta integral for integer exponents**:
`∫₀¹ t^k (1−t)^m dt = k!·m!/(k+m+1)!`. -/
theorem integral_pow_mul_one_sub_pow (k m : ℕ) :
    (∫ t in (0:ℝ)..1, t ^ (k : ℕ) * (1 - t) ^ (m : ℕ))
      = (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ) / (Nat.factorial (k + m + 1) : ℝ) := by
  have h := betaFn_eq_integral (x := (k : ℝ) + 1) (y := (m : ℝ) + 1)
    (by positivity) (by positivity)
  rw [betaFn_nat_succ k m] at h
  rw [h]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  have h1 : ((k : ℝ) + 1 - 1) = (k : ℝ) := by ring
  have h2 : ((m : ℝ) + 1 - 1) = (m : ℝ) := by ring
  simp only [h1, h2, Real.rpow_natCast]

end SHSLib.Trigamma
