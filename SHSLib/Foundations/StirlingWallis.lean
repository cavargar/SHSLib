/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The central binomial coefficient to fifth order, and the Wallis products

Batch 159 (`SHSLib/Foundations/StirlingBinetThird.lean`) bracketed the Stirling
error `A(m) = log m! − ((m + ½) log m − m + ½ log(2π))` by

  `1/(12m) − 1/(360m³) < A(m) < 1/(12m) − 1/(360m³) + 1/(1260m⁵)`.

Feeding that into `log C(2n,n) = A(2n) − 2A(n) + (n log 4 − ½ log(πn))` — the
telescoping of batch 158 — sharpens the central binomial bracket from
`−1/(8n) ± O(n⁻³)` to

  `−1/(8n) + 1/(192n³) − 1/(630n⁵) < log C(2n,n) − (n log 4 − ½ log(πn))
     < −1/(8n) + 1/(192n³) + 1/(40320n⁵)`.

Since Wallis' partial product satisfies the exact identity

  `W(n) = 16ⁿ / (C(2n,n)² (2n+1))`,

the same bracket squared bounds `W(n)` around `πn/(2n+1)` with an error
`exp(1/(4n) − 1/(96n³) + O(n⁻⁵))` — in particular `W(n) < π/2` with an
explicit gap, and `W(n) → π/2` with rate.
-/
import SHSLib.Foundations.StirlingBinetThird
import SHSLib.Foundations.StirlingCentralBinom
import Mathlib.Analysis.Real.Pi.Wallis

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The central binomial bracket to fifth order -/

/-- **Fifth-order bracket for `log C(2n, n)`.** -/
theorem log_centralBinom_bracket_third {n : ℕ} (hn : 1 ≤ n) :
    -(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3) - 1 / (630 * (n : ℝ) ^ 5)
        < Real.log (Nat.centralBinom n)
          - ((n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n)) ∧
      Real.log (Nat.centralBinom n)
          - ((n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n))
        < -(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3)
            + 1 / (40320 * (n : ℝ) ^ 5) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨hA1, hA2⟩ := log_factorial_binet_third_bracket h2n
  obtain ⟨hB1, hB2⟩ := log_factorial_binet_third_bracket hn
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hcast] at hA1 hA2
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
      - 2 * (1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3) + 1 / (1260 * (n : ℝ) ^ 5))
      = -(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3) - 1 / (630 * (n : ℝ) ^ 5) := by
    field_simp
    ring
  have harith2 : 1 / (12 * (2 * (n : ℝ))) - 1 / (360 * (2 * (n : ℝ)) ^ 3)
      + 1 / (1260 * (2 * (n : ℝ)) ^ 5)
      - 2 * (1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3))
      = -(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3) + 1 / (40320 * (n : ℝ) ^ 5) := by
    field_simp
    ring
  rw [hkey]
  constructor
  · rw [← harith1]; linarith
  · rw [← harith2]; linarith

/-- **Fifth-order two-sided bound on `C(2n, n)`.** -/
theorem centralBinom_bracket_third {n : ℕ} (hn : 1 ≤ n) :
    4 ^ n / Real.sqrt (π * n)
          * Real.exp (-(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3)
            - 1 / (630 * (n : ℝ) ^ 5))
        < (Nat.centralBinom n : ℝ) ∧
      (Nat.centralBinom n : ℝ)
        < 4 ^ n / Real.sqrt (π * n)
            * Real.exp (-(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3)
              + 1 / (40320 * (n : ℝ) ^ 5)) := by
  have hcb : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  set M : ℝ := (n : ℝ) * Real.log 4 - 1 / 2 * Real.log (π * n) with hM
  obtain ⟨h1, h2⟩ := log_centralBinom_bracket_third hn
  have hmain : Real.exp M = 4 ^ n / Real.sqrt (π * n) := exp_centralBinom_main hn
  refine ⟨?_, ?_⟩
  · have h : Real.exp (M + (-(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3)
        - 1 / (630 * (n : ℝ) ^ 5))) < (Nat.centralBinom n : ℝ) := by
      rw [← Real.exp_log hcb]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at h
    exact h
  · have h : (Nat.centralBinom n : ℝ)
        < Real.exp (M + (-(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3)
          + 1 / (40320 * (n : ℝ) ^ 5))) := by
      nth_rewrite 1 [← Real.exp_log hcb]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at h
    exact h

/-! ### Wallis' partial products -/

/-- **Wallis' partial product in closed form**:
`W(n) = 16ⁿ / (C(2n, n)² (2n+1))`. -/
theorem wallis_eq_centralBinom (n : ℕ) :
    Real.Wallis.W n = 16 ^ n / ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1)) := by
  induction n with
  | zero => simp [Real.Wallis.W]
  | succ n ih =>
      have hcb : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
        exact_mod_cast Nat.centralBinom_pos n
      have hcb1 : (0 : ℝ) < (Nat.centralBinom (n + 1) : ℝ) := by
        exact_mod_cast Nat.centralBinom_pos (n + 1)
      have hrec : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
          = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
        have h := Nat.succ_mul_centralBinom_succ n
        have h' : ((n + 1) * Nat.centralBinom (n + 1) : ℕ)
            = (2 * (2 * n + 1) * Nat.centralBinom n : ℕ) := h
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h'
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2n1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have h2n3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      have hc1 : (Nat.centralBinom (n + 1) : ℝ)
          = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) / ((n : ℝ) + 1) := by
        rw [eq_div_iff hn1]
        linarith [hrec]
      rw [Real.Wallis.W_succ, ih, hcast, hc1]
      field_simp
      ring

/-- **Two-sided bound on Wallis' partial products**, sharp to order `n⁻⁵`:
`πn/(2n+1) · e^{1/(4n) − 1/(96n³) − 1/(20160n⁵)} < W(n)
   < πn/(2n+1) · e^{1/(4n) − 1/(96n³) + 1/(315n⁵)}`. -/
theorem wallis_bracket {n : ℕ} (hn : 1 ≤ n) :
    π * (n : ℝ) / (2 * (n : ℝ) + 1)
          * Real.exp (1 / (4 * (n : ℝ)) - 1 / (96 * (n : ℝ) ^ 3)
            - 1 / (20160 * (n : ℝ) ^ 5))
        < Real.Wallis.W n ∧
      Real.Wallis.W n
        < π * (n : ℝ) / (2 * (n : ℝ) + 1)
            * Real.exp (1 / (4 * (n : ℝ)) - 1 / (96 * (n : ℝ) ^ 3)
              + 1 / (315 * (n : ℝ) ^ 5)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hcb : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  have hsqrt : (0 : ℝ) < Real.sqrt (π * n) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (π * n) ^ 2 = π * n := Real.sq_sqrt (by positivity)
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  set E1 : ℝ := -(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3) - 1 / (630 * (n : ℝ) ^ 5)
    with hE1
  set E2 : ℝ := -(1 / (8 * (n : ℝ))) + 1 / (192 * (n : ℝ) ^ 3) + 1 / (40320 * (n : ℝ) ^ 5)
    with hE2
  obtain ⟨h1, h2⟩ := centralBinom_bracket_third hn
  -- square the bracket
  have hlow : (4 : ℝ) ^ n / Real.sqrt (π * n) * Real.exp E1 > 0 := by positivity
  have hsq1 : (4 ^ n / Real.sqrt (π * n) * Real.exp E1) ^ 2
      < (Nat.centralBinom n : ℝ) ^ 2 := by
    have := mul_self_lt_mul_self hlow.le h1
    nlinarith [this]
  have hsq2 : (Nat.centralBinom n : ℝ) ^ 2
      < (4 ^ n / Real.sqrt (π * n) * Real.exp E2) ^ 2 := by
    have := mul_self_lt_mul_self hcb.le h2
    nlinarith [this]
  have hexpand : ∀ E : ℝ, (4 ^ n / Real.sqrt (π * n) * Real.exp E) ^ 2
      = 16 ^ n / (π * (n : ℝ)) * Real.exp (2 * E) := by
    intro E
    have hexp2 : (Real.exp E) ^ 2 = Real.exp (2 * E) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    have hpow4 : ((4 : ℝ) ^ n) ^ 2 = 16 ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    rw [mul_pow, div_pow, hsq, hexp2, hpow4]
  rw [hexpand] at hsq1 hsq2
  rw [wallis_eq_centralBinom n]
  have hE1' : 2 * E1 = -(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
      - 1 / (315 * (n : ℝ) ^ 5) := by
    rw [hE1]; field_simp; ring
  have hE2' : 2 * E2 = -(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
      + 1 / (20160 * (n : ℝ) ^ 5) := by
    rw [hE2]; field_simp; ring
  rw [hE1'] at hsq1
  rw [hE2'] at hsq2
  set F1 : ℝ := 1 / (4 * (n : ℝ)) - 1 / (96 * (n : ℝ) ^ 3) - 1 / (20160 * (n : ℝ) ^ 5)
    with hF1
  set F2 : ℝ := 1 / (4 * (n : ℝ)) - 1 / (96 * (n : ℝ) ^ 3) + 1 / (315 * (n : ℝ) ^ 5)
    with hF2
  have hinvF1 : -(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
      + 1 / (20160 * (n : ℝ) ^ 5) = -F1 := by rw [hF1]; ring
  have hinvF2 : -(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
      - 1 / (315 * (n : ℝ) ^ 5) = -F2 := by rw [hF2]; ring
  rw [hinvF2] at hsq1
  rw [hinvF1] at hsq2
  have h16 : (0 : ℝ) < 16 ^ n := by positivity
  constructor
  · -- from `C² < 16ⁿ/(πn) · e^{−F1}`
    rw [lt_div_iff₀ (by positivity)]
    have hkey : π * (n : ℝ) / (2 * (n : ℝ) + 1) * Real.exp F1
        * ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1))
        = π * (n : ℝ) * Real.exp F1 * (Nat.centralBinom n : ℝ) ^ 2 := by
      field_simp
    rw [hkey]
    have hbound : π * (n : ℝ) * Real.exp F1 * (Nat.centralBinom n : ℝ) ^ 2
        < π * (n : ℝ) * Real.exp F1 * (16 ^ n / (π * (n : ℝ)) * Real.exp (-F1)) := by
      have hpos : (0 : ℝ) < π * (n : ℝ) * Real.exp F1 := by positivity
      exact mul_lt_mul_of_pos_left hsq2 hpos
    have hsimp : π * (n : ℝ) * Real.exp F1 * (16 ^ n / (π * (n : ℝ)) * Real.exp (-F1))
        = 16 ^ n := by
      rw [Real.exp_neg]
      field_simp
    rw [hsimp] at hbound
    exact hbound
  · rw [div_lt_iff₀ (by positivity)]
    have hkey : π * (n : ℝ) / (2 * (n : ℝ) + 1) * Real.exp F2
        * ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1))
        = π * (n : ℝ) * Real.exp F2 * (Nat.centralBinom n : ℝ) ^ 2 := by
      field_simp
    rw [hkey]
    have hbound : π * (n : ℝ) * Real.exp F2 * (16 ^ n / (π * (n : ℝ)) * Real.exp (-F2))
        < π * (n : ℝ) * Real.exp F2 * (Nat.centralBinom n : ℝ) ^ 2 := by
      have hpos : (0 : ℝ) < π * (n : ℝ) * Real.exp F2 := by positivity
      exact mul_lt_mul_of_pos_left hsq1 hpos
    have hsimp : π * (n : ℝ) * Real.exp F2 * (16 ^ n / (π * (n : ℝ)) * Real.exp (-F2))
        = 16 ^ n := by
      rw [Real.exp_neg]
      field_simp
    rw [hsimp] at hbound
    exact hbound

end SHSLib.Trigamma
