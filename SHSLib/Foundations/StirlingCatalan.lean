/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Catalan numbers, and the asymptotics `C(2n,n) ~ 4ⁿ/√(πn)` with explicit rate

Batch 158 (`SHSLib/Foundations/StirlingCentralBinom.lean`) proved

  `4ⁿ e^{−1/(7n)} / √(πn) < C(2n, n) < 4ⁿ / √(πn)`   for `n ≥ 1`.

Since `(n+1) · Cat(n) = C(2n, n)`, the same bracket divided by `n + 1` bounds
the Catalan numbers, and squeezing the two sides gives the classical
equivalences

  `C(2n,n) · √(πn) / 4ⁿ → 1`,   `Cat(n) · (n+1) √(πn) / 4ⁿ → 1`,

now with the *explicit* rate `e^{−1/(7n)} < · < 1` attached.
-/
import SHSLib.Foundations.StirlingCentralBinom

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### Catalan numbers -/

/-- **Two-sided bounds on the Catalan numbers**:
`4ⁿ e^{−1/(7n)} / ((n+1)√(πn)) < Cat(n) < 4ⁿ / ((n+1)√(πn))` for `n ≥ 1`. -/
theorem catalan_bracket {n : ℕ} (hn : 1 ≤ n) :
    4 ^ n / (((n : ℝ) + 1) * Real.sqrt (π * n)) * Real.exp (-(1 / (7 * (n : ℝ))))
        < (catalan n : ℝ) ∧
      (catalan n : ℝ) < 4 ^ n / (((n : ℝ) + 1) * Real.sqrt (π * n)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hsqrt : (0 : ℝ) < Real.sqrt (π * n) := Real.sqrt_pos.mpr (by positivity)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hcat : ((n : ℝ) + 1) * (catalan n : ℝ) = (Nat.centralBinom n : ℝ) := by
    have h := succ_mul_catalan_eq_centralBinom n
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  obtain ⟨h1, h2⟩ := centralBinom_lt_and_gt hn
  rw [← hcat] at h1 h2
  constructor
  · have key : 4 ^ n / (((n : ℝ) + 1) * Real.sqrt (π * n)) * Real.exp (-(1 / (7 * (n : ℝ))))
        * ((n : ℝ) + 1) = 4 ^ n / Real.sqrt (π * n) * Real.exp (-(1 / (7 * (n : ℝ)))) := by
      field_simp
    refine lt_of_mul_lt_mul_right ?_ hn1.le
    rw [key]
    linarith
  · have key : 4 ^ n / (((n : ℝ) + 1) * Real.sqrt (π * n)) * ((n : ℝ) + 1)
        = 4 ^ n / Real.sqrt (π * n) := by
      field_simp
    refine lt_of_mul_lt_mul_right ?_ hn1.le
    rw [key]
    linarith

/-! ### The asymptotic equivalences, with rate -/

private theorem tendsto_exp_neg_inv_nat : Tendsto (fun n : ℕ => Real.exp (-(1 / (7 * (n : ℝ)))))
    atTop (𝓝 1) := by
  have hnat : Tendsto (fun n : ℕ => 7 * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / (7 * (n : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp hnat
    simpa [Function.comp_def, one_div] using h
  have hneg : Tendsto (fun n : ℕ => -(1 / (7 * (n : ℝ)))) atTop (𝓝 0) := by
    simpa using hinv.neg
  simpa using (Real.continuous_exp.tendsto 0).comp hneg

/-- **`C(2n, n) ~ 4ⁿ/√(πn)`**: the normalised central binomial coefficient
tends to `1`. -/
theorem tendsto_centralBinom_div :
    Tendsto (fun n : ℕ => (Nat.centralBinom n : ℝ) * Real.sqrt (π * n) / 4 ^ n) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_exp_neg_inv_nat tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hsqrt : (0 : ℝ) < Real.sqrt (π * n) := Real.sqrt_pos.mpr (by positivity)
    have hpow : (0 : ℝ) < 4 ^ n := by positivity
    obtain ⟨h1, -⟩ := centralBinom_lt_and_gt hn
    have h1' := mul_lt_mul_of_pos_right h1 hsqrt
    have hsimp : 4 ^ n / Real.sqrt (π * n) * Real.exp (-(1 / (7 * (n : ℝ))))
        * Real.sqrt (π * n) = Real.exp (-(1 / (7 * (n : ℝ)))) * 4 ^ n := by
      field_simp
    rw [hsimp] at h1'
    rw [le_div_iff₀ hpow]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hsqrt : (0 : ℝ) < Real.sqrt (π * n) := Real.sqrt_pos.mpr (by positivity)
    have hpow : (0 : ℝ) < 4 ^ n := by positivity
    obtain ⟨-, h2⟩ := centralBinom_lt_and_gt hn
    have h2' := mul_lt_mul_of_pos_right h2 hsqrt
    have hsimp : 4 ^ n / Real.sqrt (π * n) * Real.sqrt (π * n) = 4 ^ n := by
      field_simp
    rw [hsimp] at h2'
    rw [div_le_one hpow]
    linarith

/-- **`Cat(n) ~ 4ⁿ/((n+1)√(πn))`**: the normalised Catalan number tends to `1`. -/
theorem tendsto_catalan_div :
    Tendsto (fun n : ℕ => (catalan n : ℝ) * (((n : ℝ) + 1) * Real.sqrt (π * n)) / 4 ^ n)
      atTop (𝓝 1) := by
  refine tendsto_centralBinom_div.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n _
  have hcat : ((n : ℝ) + 1) * (catalan n : ℝ) = (Nat.centralBinom n : ℝ) := by
    have h := succ_mul_catalan_eq_centralBinom n
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  rw [← hcat]
  ring

end SHSLib.Trigamma
