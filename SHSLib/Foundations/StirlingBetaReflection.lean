/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection and binomial coefficients through the Beta function

Two independent readings of the Beta function of batches 167–168.

**Reflection.** Since `Γ(1) = 1`, Euler's reflection formula
`Γ(x)Γ(1−x) = π/sin(πx)` says exactly `B(x, 1−x) = π/sin(πx)`, and combined
with Euler's integral this evaluates the classical

  `∫₀¹ t^{x−1}(1−t)^{−x} dt = π/sin(πx)`   (`0 < x < 1`),

with `B(⅓,⅔) = 2π/√3` and `B(½,½) = π` as sample values.

**Binomial coefficients.** For `k ≤ n`, `B(k+1, n−k+1) = k!(n−k)!/(n+1)!`, so

  `(n+1)·C(n,k)·B(k+1, n−k+1) = 1`,   `∫₀¹ t^k(1−t)^{n−k} dt = 1/((n+1)C(n,k))`.
-/
import SHSLib.Foundations.StirlingBetaIntegral

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-- **Euler's reflection formula in Beta form**: `B(x, 1−x) = π/sin(πx)`. -/
theorem betaFn_one_sub (x : ℝ) : betaFn x (1 - x) = π / Real.sin (π * x) := by
  have h : x + (1 - x) = 1 := by ring
  unfold betaFn
  rw [h, Real.Gamma_one, div_one, Real.Gamma_mul_Gamma_one_sub]

/-- `∫₀¹ t^{x−1}(1−t)^{−x} dt = π/sin(πx)` for `0 < x < 1`. -/
theorem integral_rpow_reflection {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (∫ t in (0:ℝ)..1, t ^ (x - 1) * (1 - t) ^ (1 - x - 1)) = π / Real.sin (π * x) := by
  rw [← betaFn_eq_integral hx0 (by linarith : (0:ℝ) < 1 - x), betaFn_one_sub]

/-- `B(⅓, ⅔) = 2π/√3`. -/
theorem betaFn_third : betaFn (1 / 3) (2 / 3) = 2 * π / Real.sqrt 3 := by
  have h : (2 : ℝ) / 3 = 1 - 1 / 3 := by norm_num
  have hs : Real.sin (π * (1 / 3)) = Real.sqrt 3 / 2 := by
    rw [show π * (1 / 3) = π / 3 by ring, Real.sin_pi_div_three]
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  rw [h, betaFn_one_sub, hs]
  field_simp

/-- `(n+1)·C(n,k)·B(k+1, n−k+1) = 1` for `k ≤ n`. -/
theorem betaFn_choose {n k : ℕ} (hk : k ≤ n) :
    ((n : ℝ) + 1) * (n.choose k : ℝ) * betaFn ((k : ℝ) + 1) (((n - k : ℕ) : ℝ) + 1) = 1 := by
  have hfac : (n.choose k : ℝ) * (Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)
      = (Nat.factorial n : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_mul_factorial_mul_factorial hk)
  have hsum : k + (n - k) + 1 = n + 1 := by omega
  have hbeta := betaFn_nat_succ k (n - k)
  rw [hsum] at hbeta
  have hn1 : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hpos : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos n).ne'
  rw [hbeta, hn1]
  field_simp
  linarith [hfac]

/-- **The binomial coefficient as a Beta integral**:
`∫₀¹ t^k(1−t)^{n−k} dt = 1/((n+1)·C(n,k))` for `k ≤ n`. -/
theorem integral_pow_mul_one_sub_pow_choose {n k : ℕ} (hk : k ≤ n) :
    (∫ t in (0:ℝ)..1, t ^ k * (1 - t) ^ (n - k))
      = 1 / (((n : ℝ) + 1) * (n.choose k : ℝ)) := by
  have hbeta := betaFn_choose hk
  have hchoose : (0 : ℝ) < (n.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hval : betaFn ((k : ℝ) + 1) (((n - k : ℕ) : ℝ) + 1)
      = 1 / (((n : ℝ) + 1) * (n.choose k : ℝ)) := by
    field_simp
    linarith [hbeta]
  rw [← hval, betaFn_nat_succ k (n - k), ← integral_pow_mul_one_sub_pow k (n - k)]

end SHSLib.Trigamma
