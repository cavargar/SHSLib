/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Stirling constant is `½ log (2π)`

`SHSLib/Foundations/StirlingLogGamma.lean` shows that the Stirling defect
`S(x) = log Γ(x) − (x − 1/2) log x + x` converges at infinity.  Its limit is
identified here by evaluating along the integers, where `Γ(n+1) = n!` connects
`S` with Mathlib's Stirling sequence

  `stirlingSeq n = n! / (√(2n) (n/e)^n)`,  `stirlingSeq n → √π`.

Indeed for `n ≥ 1`

  `S(n+1) = log (stirlingSeq n) + ½ log 2 + 1 − (n + ½) log (1 + 1/n)`,

and `(n + ½) log(1 + 1/n) → 1`, so `S(n+1) → ½ log π + ½ log 2 = ½ log (2π)`.
Since `S` converges along the reals, that value is the limit:

  `log Γ(x) = (x − 1/2) log x − x + ½ log (2π) + o(1)`
  (`tendsto_stirlingDefect`, `tendsto_logGamma_sub_stirling`).
-/
import SHSLib.Foundations.StirlingLogGamma
import Mathlib.Analysis.SpecialFunctions.Stirling

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### `(n + ½) log(1 + 1/n) → 1` -/

theorem tendsto_one_add_half_mul_log : Tendsto
    (fun n : ℕ => ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (n : ℝ))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlow : Tendsto (fun n : ℕ => 1 - 1 / 4 * (1 / (n : ℝ)) * (1 / (n : ℝ))) atTop (𝓝 1) := by
    have h := ((hinv.const_mul (1 / 4 : ℝ)).mul hinv)
    simpa using tendsto_const_nhds.sub h
  have hhigh : Tendsto (fun n : ℕ => 1 + 1 / 2 * (1 / (n : ℝ))) atTop (𝓝 1) := by
    have h := hinv.const_mul (1 / 2 : ℝ)
    simpa using tendsto_const_nhds.add h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hbound : 1 / (n : ℝ) - (1 / (n : ℝ)) ^ 2 / 2 ≤ Real.log (1 + 1 / (n : ℝ)) :=
      sub_sq_div_two_le_log_one_add (by positivity)
    have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hbound hpos.le
    have hid : ((n : ℝ) + 1 / 2) * (1 / (n : ℝ) - (1 / (n : ℝ)) ^ 2 / 2)
        = 1 - 1 / 4 * (1 / (n : ℝ)) * (1 / (n : ℝ)) := by
      field_simp
      ring
    rw [hid] at hmul
    exact hmul
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hbound : Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (n : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (x := 1 + 1 / (n : ℝ)) (by positivity)
      simpa using h
    have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hbound hpos.le
    have hid : ((n : ℝ) + 1 / 2) * (1 / (n : ℝ)) = 1 + 1 / 2 * (1 / (n : ℝ)) := by
      field_simp
    rw [hid] at hmul
    exact hmul

/-! ### The Stirling defect at the integers -/

theorem stirlingDefect_nat_add_one {n : ℕ} (hn : 1 ≤ n) :
    stirlingDefect ((n : ℝ) + 1)
      = Real.log (Stirling.stirlingSeq n) + 1 / 2 * Real.log 2 + 1
        - ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hfac : logGamma ((n : ℝ) + 1) = Real.log (Nat.factorial n) := by
    rw [logGamma]
    congr 1
    exact_mod_cast Real.Gamma_nat_eq_factorial n
  have hform := Stirling.log_stirlingSeq_formula n
  have hlogdiv : Real.log ((n : ℝ) / Real.exp 1) = Real.log (n : ℝ) - 1 := by
    rw [Real.log_div hn0.ne' (Real.exp_ne_zero 1), Real.log_exp]
  have hlog2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) hn0.ne']
  have hfact : Real.log (Nat.factorial n)
      = Real.log (Stirling.stirlingSeq n) + 1 / 2 * (Real.log 2 + Real.log (n : ℝ))
        + (n : ℝ) * (Real.log (n : ℝ) - 1) := by
    rw [hform, hlogdiv, hlog2n]
    ring
  have hsucc : Real.log ((n : ℝ) + 1) = Real.log (n : ℝ) + Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_mul hn0.ne' (by positivity)]
    congr 1
    field_simp
  rw [stirlingDefect, hfac, hfact, hsucc]
  ring

/-! ### The constant -/

/-- **Stirling's formula for `log Γ`**: the Stirling defect tends to
`½ log (2π)`. -/
theorem tendsto_stirlingDefect :
    Tendsto stirlingDefect atTop (𝓝 (1 / 2 * Real.log (2 * π))) := by
  obtain ⟨C, hC⟩ := exists_tendsto_stirlingDefect
  have hnat : Tendsto (fun n : ℕ => stirlingDefect ((n : ℝ) + 1)) atTop (𝓝 C) := by
    have hgo : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact hC.comp hgo
  have hlogseq : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log (√π))) := by
    have hpos : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
    exact (Real.continuousAt_log hpos.ne').tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hvalue : Tendsto (fun n : ℕ => stirlingDefect ((n : ℝ) + 1)) atTop
      (𝓝 (Real.log (√π) + 1 / 2 * Real.log 2 + 1 - 1)) := by
    have h := ((hlogseq.add_const (1 / 2 * Real.log 2)).add_const 1).sub
      tendsto_one_add_half_mul_log
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (stirlingDefect_nat_add_one hn).symm
  have hCval : C = Real.log (√π) + 1 / 2 * Real.log 2 + 1 - 1 :=
    tendsto_nhds_unique hnat hvalue
  have hsqrt : Real.log (√π) = 1 / 2 * Real.log π := by
    rw [Real.log_sqrt Real.pi_pos.le]
    ring
  have hfinal : C = 1 / 2 * Real.log (2 * π) := by
    rw [hCval, hsqrt, Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  rwa [hfinal] at hC

/-- Stirling's formula, written out: `log Γ(x) − ((x − 1/2) log x − x) → ½ log(2π)`. -/
theorem tendsto_logGamma_sub_stirling :
    Tendsto (fun x : ℝ => logGamma x - ((x - 1 / 2) * Real.log x - x)) atTop
      (𝓝 (1 / 2 * Real.log (2 * π))) := by
  refine tendsto_stirlingDefect.congr (fun x => ?_)
  rw [stirlingDefect]
  ring

end SHSLib.Trigamma
