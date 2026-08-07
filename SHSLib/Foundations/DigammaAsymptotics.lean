/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymptotics of `ψ`: `log x − 1/x < ψ(x) < log x`

The two functional facts already in the development —

* `logGamma (x+1) − logGamma x = log x` (`logGamma_add_one`), and
* `ψ` is strictly increasing on `(0, ∞)` (`digamma_strictMonoOn`, itself a
  consequence of `trigamma_pos`) —

combine through the mean value theorem into a sharp two-sided estimate.  Indeed
Lagrange's theorem on `[x, x+1]` produces a point `c` in the interior with
`ψ(c) = logGamma(x+1) − logGamma(x) = log x`, and monotonicity gives
`ψ(x) < ψ(c) < ψ(x+1) = ψ(x) + 1/x`, i.e.

  `log x − 1/x < ψ(x) < log x`   (`digamma_lt_log`, `log_sub_inv_lt_digamma`).

Consequences recorded here:

* `tendsto_digamma_sub_log_atTop` — `ψ(x) − log x → 0` as `x → ∞`;
* `harmonic_lt_log_add_eulerMascheroni` and the matching lower bound — the
  classical sandwich `log(n+1) + γ − 1/(n+1) < H_n < log(n+1) + γ`;
* `tendsto_harmonic_sub_log_succ` — `H_n − log(n+1) → γ`, an identification of
  the Euler–Mascheroni constant as the limit of the harmonic defect.
-/
import SHSLib.Foundations.DigammaEuler

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The mean value estimate -/

/-- Lagrange's theorem applied to `log Γ` on `[x, x+1]`: there is a point
`c ∈ (x, x+1)` with `ψ(c) = log x`. -/
theorem exists_digamma_eq_log {x : ℝ} (hx : 0 < x) :
    ∃ c ∈ Ioo x (x + 1), digamma c = Real.log x := by
  have hsub : Icc x (x + 1) ⊆ Ioi 0 := by
    intro y hy
    exact lt_of_lt_of_le hx hy.1
  have hcont : ContinuousOn logGamma (Icc x (x + 1)) :=
    contDiffOn_logGamma.continuousOn.mono hsub
  have hderiv : ∀ y ∈ Ioo x (x + 1), HasDerivAt logGamma (digamma y) y := by
    intro y hy
    exact (differentiableAt_logGamma (lt_trans hx hy.1)).hasDerivAt
  obtain ⟨c, hc, hceq⟩ :=
    exists_hasDerivAt_eq_slope logGamma digamma (by linarith) hcont hderiv
  refine ⟨c, hc, ?_⟩
  rw [hceq, logGamma_add_one hx]
  ring_nf

/-- `ψ(x) < log x` for every `x > 0`. -/
theorem digamma_lt_log {x : ℝ} (hx : 0 < x) : digamma x < Real.log x := by
  obtain ⟨c, hc, hceq⟩ := exists_digamma_eq_log hx
  have := digamma_strictMonoOn (mem_Ioi.mpr hx) (mem_Ioi.mpr (lt_trans hx hc.1)) hc.1
  rwa [hceq] at this

/-- `log x − 1/x < ψ(x)` for every `x > 0`. -/
theorem log_sub_inv_lt_digamma {x : ℝ} (hx : 0 < x) : Real.log x - 1 / x < digamma x := by
  obtain ⟨c, hc, hceq⟩ := exists_digamma_eq_log hx
  have hcx : c < x + 1 := hc.2
  have hc0 : 0 < c := lt_trans hx hc.1
  have hmono := digamma_strictMonoOn (mem_Ioi.mpr hc0)
    (mem_Ioi.mpr (by linarith : (0 : ℝ) < x + 1)) hcx
  rw [hceq] at hmono
  have hrec : digamma (x + 1) = digamma x + 1 / x := digamma_recurrence hx
  rw [hrec] at hmono
  linarith

/-- `ψ(x) − log x → 0` as `x → ∞`. -/
theorem tendsto_digamma_sub_log_atTop :
    Tendsto (fun x : ℝ => digamma x - Real.log x) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlow : Tendsto (fun x : ℝ => -x⁻¹) atTop (𝓝 0) := by simpa using h0.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h := log_sub_inv_lt_digamma hx
    rw [one_div] at h
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h := digamma_lt_log hx
    linarith

/-! ### Harmonic numbers -/

/-- `H_n < γ + log (n+1)`. -/
theorem harmonic_lt_log_add_eulerMascheroni (n : ℕ) :
    ((harmonic n : ℚ) : ℝ)
      < Real.eulerMascheroniConstant + Real.log ((n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := digamma_lt_log hpos
  rw [digamma_nat_add_one_eq_harmonic n] at h
  linarith

/-- `γ + log (n+1) − 1/(n+1) < H_n`. -/
theorem log_add_eulerMascheroni_sub_lt_harmonic (n : ℕ) :
    Real.eulerMascheroniConstant + Real.log ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1)
      < ((harmonic n : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := log_sub_inv_lt_digamma hpos
  rw [digamma_nat_add_one_eq_harmonic n] at h
  linarith

/-- **The Euler–Mascheroni constant as the limit of the harmonic defect**:
`H_n − log (n+1) → γ`. -/
theorem tendsto_harmonic_sub_log_succ :
    Tendsto (fun n : ℕ => ((harmonic n : ℚ) : ℝ) - Real.log ((n : ℝ) + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlow : Tendsto (fun n : ℕ => Real.eulerMascheroniConstant - 1 / ((n : ℝ) + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    simpa using tendsto_const_nhds.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards with n
    have h := log_add_eulerMascheroni_sub_lt_harmonic n
    linarith
  · filter_upwards with n
    have h := harmonic_lt_log_add_eulerMascheroni n
    linarith

end SHSLib.Trigamma
