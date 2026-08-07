/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Explicit Stirling bounds

`SHSLib/Foundations/StirlingLogGamma.lean` shows that the Stirling defect

  `S(x) = log Γ(x) − (x − 1/2) log x + x`

is strictly decreasing on `(0, ∞)` while `S(x) − 1/x` is strictly increasing,
and `SHSLib/Foundations/StirlingConstant.lean` identifies `S(x) → ½ log (2π)`.
Those two monotonicities immediately trap `S` between its limit and the limit
plus `1/x`:

  `½ log (2π) < S(x) < ½ log (2π) + 1/x`   for every `x > 0`,

an explicit, quantitative form of Stirling's formula
(`stirlingDefect_bracket`, `logGamma_bracket`).

Specialising at a positive integer, where `log Γ(n) = log n! − log n`, gives
two-sided bounds on `log n!` and, after exponentiating,

  `√(2πn) (n/e)^n < n! < √(2πn) (n/e)^n · e^{1/n}`

(`log_factorial_bracket`, `factorial_bracket`).
-/
import SHSLib.Foundations.StirlingConstant

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The two-sided bound on the Stirling defect -/

/-- The Stirling defect stays strictly above its limit. -/
theorem stirlingConstant_lt_stirlingDefect {x : ℝ} (hx : 0 < x) :
    1 / 2 * Real.log (2 * π) < stirlingDefect x := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hle : 1 / 2 * Real.log (2 * π) ≤ stirlingDefect (x + 1) := by
    refine le_of_tendsto tendsto_stirlingDefect ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases eq_or_lt_of_le hy with heq | hlt
    · rw [heq]
    · exact le_of_lt (stirlingDefect_strictAntiOn (mem_Ioi.mpr hx1)
        (mem_Ioi.mpr (by linarith)) hlt)
  have hstep := stirlingDefect_strictAntiOn (mem_Ioi.mpr hx) (mem_Ioi.mpr hx1)
    (by linarith : x < x + 1)
  linarith

/-- The Stirling defect stays strictly below its limit plus `1/x`. -/
theorem stirlingDefect_lt_stirlingConstant_add_inv {x : ℝ} (hx : 0 < x) :
    stirlingDefect x < 1 / 2 * Real.log (2 * π) + 1 / x := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hinv : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
  have hTlim : Tendsto (fun y : ℝ => stirlingDefect y - 1 / y) atTop
      (𝓝 (1 / 2 * Real.log (2 * π))) := by
    simpa using tendsto_stirlingDefect.sub hinv
  have hle : stirlingDefect (x + 1) - 1 / (x + 1) ≤ 1 / 2 * Real.log (2 * π) := by
    refine ge_of_tendsto hTlim ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases eq_or_lt_of_le hy with heq | hlt
    · rw [heq]
    · exact le_of_lt (stirlingDefect_sub_inv_strictMonoOn (mem_Ioi.mpr hx1)
        (mem_Ioi.mpr (by linarith)) hlt)
  have hstep := stirlingDefect_sub_inv_strictMonoOn (mem_Ioi.mpr hx) (mem_Ioi.mpr hx1)
    (by linarith : x < x + 1)
  simp only at hstep
  linarith

/-- **Explicit Stirling bracket for the defect.** -/
theorem stirlingDefect_bracket {x : ℝ} (hx : 0 < x) :
    1 / 2 * Real.log (2 * π) < stirlingDefect x ∧
      stirlingDefect x < 1 / 2 * Real.log (2 * π) + 1 / x :=
  ⟨stirlingConstant_lt_stirlingDefect hx, stirlingDefect_lt_stirlingConstant_add_inv hx⟩

/-- **Explicit Stirling formula with error bound**: the error in
`log Γ(x) ≈ (x − 1/2) log x − x + ½ log (2π)` lies in `(0, 1/x)`. -/
theorem logGamma_bracket {x : ℝ} (hx : 0 < x) :
    0 < logGamma x - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)) ∧
      logGamma x - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)) < 1 / x := by
  obtain ⟨h1, h2⟩ := stirlingDefect_bracket hx
  rw [stirlingDefect] at h1 h2
  constructor <;> linarith

/-! ### Bounds on the factorial -/

/-- `log Γ(n) = log n! − log n` for a positive integer `n`. -/
theorem logGamma_nat {n : ℕ} (hn : 1 ≤ n) :
    logGamma (n : ℝ) = Real.log (Nat.factorial n) - Real.log (n : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hΓ : Real.Gamma ((m : ℝ) + 1) = (Nat.factorial m : ℝ) := by
    exact_mod_cast Real.Gamma_nat_eq_factorial m
  have hfacpos : (0 : ℝ) < (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast, logGamma, hΓ, Nat.factorial_succ]
  push_cast
  rw [Real.log_mul (by positivity) hfacpos.ne']
  ring

/-- **Two-sided bound on `log n!`.** -/
theorem log_factorial_bracket {n : ℕ} (hn : 1 ≤ n) :
    0 < Real.log (Nat.factorial n)
        - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π)) ∧
      Real.log (Nat.factorial n)
        - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π)) < 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  obtain ⟨h1, h2⟩ := logGamma_bracket hn0
  rw [logGamma_nat hn] at h1 h2
  constructor <;> linarith

/-- The main Stirling term in exponential form. -/
theorem exp_stirling_main {x : ℝ} (hx : 0 < x) :
    Real.exp ((x + 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π))
      = Real.sqrt (2 * π * x) * Real.exp (x * (Real.log x - 1)) := by
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hsqrt : Real.sqrt (2 * π * x) = Real.exp (1 / 2 * Real.log (2 * π * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    ring_nf
  rw [hsqrt, ← Real.exp_add, Real.log_mul h2pi.ne' hx.ne']
  ring_nf

/-- **Stirling's bounds for the factorial**:
`√(2πn) (n/e)^n < n! < √(2πn) (n/e)^n · e^{1/n}`. -/
theorem factorial_bracket {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n < (Nat.factorial n : ℝ) ∧
      (Nat.factorial n : ℝ)
        < Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n * Real.exp (1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  set M : ℝ := ((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π) with hM
  obtain ⟨h1, h2⟩ := log_factorial_bracket hn
  have hbase : Real.exp (Real.log (n : ℝ) - 1) = (n : ℝ) / Real.exp 1 := by
    rw [Real.exp_sub, Real.exp_log hn0]
  have hpow : ((n : ℝ) / Real.exp 1) ^ n = Real.exp ((n : ℝ) * (Real.log (n : ℝ) - 1)) := by
    rw [Real.exp_nat_mul, hbase]
  have hmain : Real.exp M = Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n := by
    rw [hpow, hM]
    exact exp_stirling_main hn0
  constructor
  · have : Real.exp M < (Nat.factorial n : ℝ) := by
      rw [← Real.exp_log hfacpos]
      exact Real.exp_lt_exp.mpr (by linarith)
    rwa [hmain] at this
  · have : (Nat.factorial n : ℝ) < Real.exp (M + 1 / (n : ℝ)) := by
      nth_rewrite 1 [← Real.exp_log hfacpos]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at this
    exact this

end SHSLib.Trigamma
