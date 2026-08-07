/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharp bounds on the central binomial coefficient

Batch 157 (`SHSLib/Foundations/StirlingBinetSecond.lean`) bracketed `n!`
between `√(2πn)(n/e)ⁿ e^{1/(12n) − 1/(360n³)}` and `√(2πn)(n/e)ⁿ e^{1/(12n)}`.
Applying that bracket at `2n` and at `n` and dividing, all the elementary
factors collapse: the main term of `C(2n, n) = (2n)!/(n!)²` is exactly
`4ⁿ/√(πn)`, and the Binet errors combine into

  `−1/(8n) − 1/(2880 n³) < log C(2n,n) − (n log 4 − ½ log (πn)) < −1/(8n) + 1/(180 n³)`.

Exponentiating gives two-sided bounds on `C(2n, n)` that are sharp to order
`n⁻³`, and in particular the clean pair

  `4ⁿ e^{−1/(7n)} / √(πn) < C(2n, n) < 4ⁿ / √(πn)`.
-/
import SHSLib.Foundations.StirlingBinetSecond

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The logarithm of the central binomial coefficient -/

/-- `log C(2n, n) = log (2n)! − 2 log n!`. -/
theorem log_centralBinom_eq (n : ℕ) :
    Real.log (Nat.centralBinom n)
      = Real.log (Nat.factorial (2 * n)) - 2 * Real.log (Nat.factorial n) := by
  have hchoose : Nat.centralBinom n * Nat.factorial n * Nat.factorial n
      = Nat.factorial (2 * n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left n (by norm_num) :
      n ≤ 2 * n)
    simpa [Nat.centralBinom, two_mul, Nat.add_sub_cancel] using h
  have hcast : (Nat.centralBinom n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)
      = (Nat.factorial (2 * n) : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hchoose
  have hcb : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos n
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h := congrArg Real.log hcast
  rw [Real.log_mul (by positivity) hfac.ne', Real.log_mul hcb.ne' hfac.ne'] at h
  linarith

/-! ### The bracket -/

/-- **Sharp two-sided bound on `log C(2n, n)`**: the Binet errors of the
factorial bracket at `2n` and at `n` combine to a deviation from
`n log 4 − ½ log (πn)` that lies between `−1/(8n) − 1/(2880 n³)` and
`−1/(8n) + 1/(180 n³)`. -/
theorem log_centralBinom_bracket {n : ℕ} (hn : 1 ≤ n) :
    -(1 / (8 * (n : ℝ))) - 1 / (2880 * (n : ℝ) ^ 3)
        < Real.log (Nat.centralBinom n)
          - ((n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n)) ∧
      Real.log (Nat.centralBinom n)
          - ((n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n))
        < -(1 / (8 * (n : ℝ))) + 1 / (180 * (n : ℝ) ^ 3) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨hA1, hA2⟩ := log_factorial_binet_second_bracket h2n
  obtain ⟨hB1, hB2⟩ := log_factorial_binet_second_bracket hn
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hcast] at hA1 hA2
  -- the main terms telescope to `n log 4 − ½ log (π n)`
  have hlog2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) :=
    Real.log_mul (by norm_num) hn0.ne'
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlogpin : Real.log (π * n) = Real.log π + Real.log (n : ℝ) :=
    Real.log_mul Real.pi_pos.ne' hn0.ne'
  have hlog2pi : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul (by norm_num) Real.pi_pos.ne'
  have hmain : (2 * (n : ℝ) + 1 / 2) * Real.log (2 * (n : ℝ)) - 2 * (n : ℝ)
        + 1 / 2 * Real.log (2 * π)
      - 2 * (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π))
      = (n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n) := by
    rw [hlog2n, hlog4, hlogpin, hlog2pi]
    ring
  have hkey : Real.log (Nat.centralBinom n)
      - ((n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n))
      = (Real.log (Nat.factorial (2 * n))
            - ((2 * (n : ℝ) + 1 / 2) * Real.log (2 * (n : ℝ)) - 2 * (n : ℝ)
              + 1 / 2 * Real.log (2 * π)))
        - 2 * (Real.log (Nat.factorial n)
            - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π))) := by
    rw [log_centralBinom_eq n, ← hmain]
    ring
  have harith1 : 1 / (12 * (2 * (n : ℝ))) - 1 / (360 * (2 * (n : ℝ)) ^ 3)
      - 2 * (1 / (12 * (n : ℝ)))
      = -(1 / (8 * (n : ℝ))) - 1 / (2880 * (n : ℝ) ^ 3) := by
    field_simp
    ring
  have harith2 : 1 / (12 * (2 * (n : ℝ)))
      - 2 * (1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3))
      = -(1 / (8 * (n : ℝ))) + 1 / (180 * (n : ℝ) ^ 3) := by
    field_simp
    ring
  rw [hkey]
  constructor
  · rw [← harith1]; linarith
  · rw [← harith2]; linarith

/-! ### The exponentiated form -/

/-- The main term of the central binomial coefficient:
`exp (n log 4 − ½ log (πn)) = 4ⁿ / √(πn)`. -/
theorem exp_centralBinom_main {n : ℕ} (hn : 1 ≤ n) :
    Real.exp ((n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n))
      = 4 ^ n / Real.sqrt (π * n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hpin : (0 : ℝ) < π * n := by positivity
  have hsqrt : Real.sqrt (π * n) = Real.exp (1 / 2 * Real.log (π * n)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpin]
    ring_nf
  have hpow : Real.exp ((n : ℝ) * Real.log 4) = 4 ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [Real.exp_sub, hpow, hsqrt]

/-- **Sharp two-sided bound on the central binomial coefficient**:
`4ⁿ/√(πn) · e^{−1/(8n) − 1/(2880n³)} < C(2n, n) < 4ⁿ/√(πn) · e^{−1/(8n) + 1/(180n³)}`. -/
theorem centralBinom_bracket {n : ℕ} (hn : 1 ≤ n) :
    4 ^ n / Real.sqrt (π * n)
          * Real.exp (-(1 / (8 * (n : ℝ))) - 1 / (2880 * (n : ℝ) ^ 3))
        < (Nat.centralBinom n : ℝ) ∧
      (Nat.centralBinom n : ℝ)
        < 4 ^ n / Real.sqrt (π * n)
            * Real.exp (-(1 / (8 * (n : ℝ))) + 1 / (180 * (n : ℝ) ^ 3)) := by
  have hcb : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  set M : ℝ := (n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n) with hM
  obtain ⟨h1, h2⟩ := log_centralBinom_bracket hn
  have hmain : Real.exp M = 4 ^ n / Real.sqrt (π * n) := exp_centralBinom_main hn
  refine ⟨?_, ?_⟩
  · have h : Real.exp (M + (-(1 / (8 * (n : ℝ))) - 1 / (2880 * (n : ℝ) ^ 3)))
        < (Nat.centralBinom n : ℝ) := by
      rw [← Real.exp_log hcb]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at h
    exact h
  · have h : (Nat.centralBinom n : ℝ)
        < Real.exp (M + (-(1 / (8 * (n : ℝ))) + 1 / (180 * (n : ℝ) ^ 3))) := by
      nth_rewrite 1 [← Real.exp_log hcb]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at h
    exact h

/-- **The clean central binomial bracket**:
`4ⁿ e^{−1/(7n)} / √(πn) < C(2n, n) < 4ⁿ / √(πn)` for every `n ≥ 1`. -/
theorem centralBinom_lt_and_gt {n : ℕ} (hn : 1 ≤ n) :
    4 ^ n / Real.sqrt (π * n) * Real.exp (-(1 / (7 * (n : ℝ)))) < (Nat.centralBinom n : ℝ) ∧
      (Nat.centralBinom n : ℝ) < 4 ^ n / Real.sqrt (π * n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hbase : (0 : ℝ) < 4 ^ n / Real.sqrt (π * n) := by
    have : (0 : ℝ) < Real.sqrt (π * n) := Real.sqrt_pos.mpr (by positivity)
    positivity
  obtain ⟨h1, h2⟩ := centralBinom_bracket hn
  refine ⟨?_, ?_⟩
  · refine lt_of_le_of_lt ?_ h1
    have hexp : Real.exp (-(1 / (7 * (n : ℝ))))
        ≤ Real.exp (-(1 / (8 * (n : ℝ))) - 1 / (2880 * (n : ℝ) ^ 3)) := by
      refine Real.exp_le_exp.mpr ?_
      have hcube : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
      have hkey : 1 / (2880 * (n : ℝ) ^ 3) ≤ 1 / (56 * (n : ℝ)) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
      have harith : 1 / (8 * (n : ℝ)) + 1 / (56 * (n : ℝ)) = 1 / (7 * (n : ℝ)) := by
        field_simp
        ring
      linarith
    exact mul_le_mul_of_nonneg_left hexp hbase.le
  · refine lt_of_lt_of_le h2 ?_
    have hexp : Real.exp (-(1 / (8 * (n : ℝ))) + 1 / (180 * (n : ℝ) ^ 3)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hcube : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
      have hkey : 1 / (180 * (n : ℝ) ^ 3) ≤ 1 / (8 * (n : ℝ)) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
      linarith
    exact mul_le_of_le_one_right hbase.le hexp

end SHSLib.Trigamma
