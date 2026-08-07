/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Binet constant `1/(12x)`

Batch 155 (`SHSLib/Foundations/StirlingBounds.lean`) trapped the Stirling
defect between `½ log (2π)` and `½ log (2π) + 1/x`.  The optimal upper
envelope is `½ log (2π) + 1/(12x)`, and it is obtained by exactly the same
argument once the digamma lower bound is sharpened from

  `ψ(x) > log x − 1/(2x) − 1/x²`   (batch 154)

to

  `ψ(x) > log x − 1/(2x) − 1/(12x²)`.

The step inequality behind the sharpened bound cancels to fifth order, so no
low-order Taylor bound on `log (1+t)` suffices.  Instead the whole step
difference is recognised as one explicit function of `t = 1/x`,

  `binetAux t = log(1+t) − t + t²/(2(1+t)) + (2t³ + t⁴)/(12(1+t)²)`,

whose derivative collapses to the manifestly positive `t⁴/(6(1+t)³)`.  Since
`binetAux 0 = 0`, that gives `binetAux t > 0` for `t > 0` and hence the step
inequality for every `x > 0`.
-/
import SHSLib.Foundations.StirlingBounds

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The Binet auxiliary function -/

/-- `binetAux t = log(1+t) − t + t²/(2(1+t)) + (2t³ + t⁴)/(12(1+t)²)`.  It is the
unit-step decrement of `ψ(x) − log x + 1/(2x) + 1/(12x²)` expressed in
`t = 1/x`. -/
noncomputable def binetAux (t : ℝ) : ℝ :=
  Real.log (1 + t) - t + t ^ 2 / (2 * (1 + t)) + (2 * t ^ 3 + t ^ 4) / (12 * (1 + t) ^ 2)

theorem binetAux_zero : binetAux 0 = 0 := by
  simp [binetAux]

/-- The derivative of `binetAux` collapses to `t⁴ / (6 (1+t)³)`. -/
theorem hasDerivAt_binetAux {t : ℝ} (ht : -1 < t) :
    HasDerivAt binetAux (t ^ 4 / (6 * (1 + t) ^ 3)) t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hlog : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    have h : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    simpa [one_div] using (Real.hasDerivAt_log h1t.ne').comp t h
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hden1 : HasDerivAt (fun s : ℝ => 2 * (1 + s)) 2 t := by
    have h : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    simpa using h.const_mul (2 : ℝ)
  have hnum1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t)
  have hfrac1 : HasDerivAt (fun s : ℝ => s ^ 2 / (2 * (1 + s)))
      ((2 * t * (2 * (1 + t)) - t ^ 2 * 2) / (2 * (1 + t)) ^ 2) t :=
    hnum1.div hden1 (by positivity)
  have hden2 : HasDerivAt (fun s : ℝ => 12 * (1 + s) ^ 2) (12 * (2 * (1 + t))) t := by
    have h : HasDerivAt (fun s : ℝ => (1 + s) ^ 2) (2 * (1 + t)) t := by
      have h0 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
        simpa using (hasDerivAt_id t).const_add (1 : ℝ)
      simpa using (h0.pow 2)
    simpa using h.const_mul (12 : ℝ)
  have hnum2 : HasDerivAt (fun s : ℝ => 2 * s ^ 3 + s ^ 4) (2 * (3 * t ^ 2) + 4 * t ^ 3) t := by
    have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
      simpa using (hasDerivAt_pow 3 t)
    have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
      simpa using (hasDerivAt_pow 4 t)
    exact (h3.const_mul (2 : ℝ)).add h4
  have hfrac2 : HasDerivAt (fun s : ℝ => (2 * s ^ 3 + s ^ 4) / (12 * (1 + s) ^ 2))
      (((2 * (3 * t ^ 2) + 4 * t ^ 3) * (12 * (1 + t) ^ 2)
        - (2 * t ^ 3 + t ^ 4) * (12 * (2 * (1 + t)))) / (12 * (1 + t) ^ 2) ^ 2) t :=
    hnum2.div hden2 (by positivity)
  have htotal := ((hlog.sub hid).add hfrac1).add hfrac2
  have hval : 1 / (1 + t) - 1 + (2 * t * (2 * (1 + t)) - t ^ 2 * 2) / (2 * (1 + t)) ^ 2
      + ((2 * (3 * t ^ 2) + 4 * t ^ 3) * (12 * (1 + t) ^ 2)
        - (2 * t ^ 3 + t ^ 4) * (12 * (2 * (1 + t)))) / (12 * (1 + t) ^ 2) ^ 2
      = t ^ 4 / (6 * (1 + t) ^ 3) := by
    field_simp
    ring
  rw [← hval]
  exact htotal

/-- `binetAux` is strictly positive on `(0, ∞)`. -/
theorem binetAux_pos {t : ℝ} (ht : 0 < t) : 0 < binetAux t := by
  have hmono : StrictMonoOn binetAux (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · intro s hs
      have hs0 : (0 : ℝ) ≤ s := hs
      exact (hasDerivAt_binetAux (by linarith)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : (0 : ℝ) < s := hs
      rw [(hasDerivAt_binetAux (by linarith)).deriv]
      positivity
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr ht.le) ht
  rwa [binetAux_zero] at this

/-! ### The sharpened digamma lower bound -/

/-- The unit-step decrement of `ψ(x) − log x + 1/(2x) + 1/(12x²)` is `binetAux (1/x)`. -/
theorem digamma_binet_step_eq {x : ℝ} (hx : 0 < x) :
    (digamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2))
        - (digamma (x + 1) - Real.log (x + 1) + 1 / (2 * (x + 1)) + 1 / (12 * (x + 1) ^ 2))
      = binetAux (1 / x) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hrec : digamma (x + 1) = digamma x + 1 / x := digamma_recurrence hx
  have hlogdiff : Real.log (x + 1) - Real.log x = Real.log (1 + 1 / x) := by
    rw [← Real.log_div hx1.ne' hx.ne']
    congr 1
    field_simp
  have hone : (1 : ℝ) + 1 / x = (x + 1) / x := by field_simp
  rw [hrec, binetAux, ← hlogdiff]
  field_simp
  ring

/-- The unit-step decrement is strictly positive. -/
theorem digamma_binet_step {x : ℝ} (hx : 0 < x) :
    (digamma (x + 1) - Real.log (x + 1) + 1 / (2 * (x + 1)) + 1 / (12 * (x + 1) ^ 2))
      < digamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2) := by
  have h := digamma_binet_step_eq hx
  have hpos : 0 < binetAux (1 / x) := binetAux_pos (by positivity)
  linarith [h ▸ hpos]

/-- **`ψ(x) > log x − 1/(2x) − 1/(12x²)`** for every `x > 0`. -/
theorem digamma_gt_log_sub_half_inv_sub_binet {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) < digamma x := by
  set f : ℝ → ℝ := fun y => digamma y - Real.log y + 1 / (2 * y) + 1 / (12 * y ^ 2) with hf_def
  have hstep : ∀ y : ℝ, 0 < y → f (y + 1) < f y := fun y hy => digamma_binet_step hy
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => digamma y - Real.log y) atTop (𝓝 0) :=
      tendsto_digamma_sub_log_atTop
    have hinv : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
    have h2 : Tendsto (fun y : ℝ => 1 / (2 * y)) atTop (𝓝 0) := by
      have h := hinv.const_mul (1 / 2 : ℝ)
      simp only [mul_zero] at h
      refine h.congr (fun y => ?_)
      rcases eq_or_ne y 0 with rfl | hy
      · norm_num
      · field_simp
    have h3 : Tendsto (fun y : ℝ => 1 / (12 * y ^ 2)) atTop (𝓝 0) := by
      have h := ((hinv.mul hinv).const_mul (1 / 12 : ℝ))
      simp only [mul_zero] at h
      refine h.congr (fun y => ?_)
      rcases eq_or_ne y 0 with rfl | hy
      · norm_num
      · field_simp
    have := (h1.add h2).add h3
    simpa [hf_def] using this
  have hpos := pos_of_step_of_tendsto_atTop hstep hlim hx
  simp only [hf_def] at hpos
  linarith

/-! ### The sharp Stirling upper envelope -/

/-- `S(x) − 1/(12x)` is strictly increasing on `(0, ∞)`. -/
theorem stirlingDefect_sub_binet_strictMonoOn :
    StrictMonoOn (fun x : ℝ => stirlingDefect x - 1 / (12 * x)) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := mem_Ioi.mp hx
    have h1 := (hasDerivAt_stirlingDefect hx0).continuousAt
    have h2 : ContinuousAt (fun y : ℝ => 1 / (12 * y)) x :=
      continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity)
    exact (h1.sub h2).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0 : ℝ) < x := hx
    have hden : HasDerivAt (fun y : ℝ => 12 * y) 12 x := by
      simpa using (hasDerivAt_id x).const_mul (12 : ℝ)
    have hinv : HasDerivAt (fun y : ℝ => 1 / (12 * y)) (-(1 / (12 * x ^ 2))) x := by
      have h := (hasDerivAt_const x (1 : ℝ)).div hden (by positivity)
      simp only [zero_mul, zero_sub] at h
      convert h using 1
      field_simp
    have h : HasDerivAt (fun y : ℝ => stirlingDefect y - 1 / (12 * y))
        (digamma x - Real.log x + 1 / (2 * x) - -(1 / (12 * x ^ 2))) x :=
      (hasDerivAt_stirlingDefect hx0).sub hinv
    rw [h.deriv]
    have hlow := digamma_gt_log_sub_half_inv_sub_binet hx0
    linarith

/-- **The Binet upper bound**: `S(x) < ½ log(2π) + 1/(12x)`. -/
theorem stirlingDefect_lt_stirlingConstant_add_binet {x : ℝ} (hx : 0 < x) :
    stirlingDefect x < 1 / 2 * Real.log (2 * π) + 1 / (12 * x) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hinv : Tendsto (fun y : ℝ => 1 / (12 * y)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
    have h := h0.const_mul (1 / 12 : ℝ)
    simp only [mul_zero] at h
    refine h.congr (fun y => ?_)
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num
    · field_simp
  have hTlim : Tendsto (fun y : ℝ => stirlingDefect y - 1 / (12 * y)) atTop
      (𝓝 (1 / 2 * Real.log (2 * π))) := by
    simpa using tendsto_stirlingDefect.sub hinv
  have hle : stirlingDefect (x + 1) - 1 / (12 * (x + 1)) ≤ 1 / 2 * Real.log (2 * π) := by
    refine ge_of_tendsto hTlim ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases eq_or_lt_of_le hy with heq | hlt
    · rw [heq]
    · exact le_of_lt (stirlingDefect_sub_binet_strictMonoOn (mem_Ioi.mpr hx1)
        (mem_Ioi.mpr (by linarith)) hlt)
  have hstep := stirlingDefect_sub_binet_strictMonoOn (mem_Ioi.mpr hx) (mem_Ioi.mpr hx1)
    (by linarith : x < x + 1)
  simp only at hstep
  linarith

/-- **Stirling's formula with the Binet error bound**: the error in
`log Γ(x) ≈ (x − 1/2) log x − x + ½ log (2π)` lies in `(0, 1/(12x))`. -/
theorem logGamma_binet_bracket {x : ℝ} (hx : 0 < x) :
    0 < logGamma x - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)) ∧
      logGamma x - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π))
        < 1 / (12 * x) := by
  have h1 := stirlingConstant_lt_stirlingDefect hx
  have h2 := stirlingDefect_lt_stirlingConstant_add_binet hx
  rw [stirlingDefect] at h1 h2
  constructor <;> linarith

/-! ### The sharp factorial bounds -/

/-- **Two-sided bound on `log n!` with the Binet constant.** -/
theorem log_factorial_binet_bracket {n : ℕ} (hn : 1 ≤ n) :
    0 < Real.log (Nat.factorial n)
        - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π)) ∧
      Real.log (Nat.factorial n)
        - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π))
          < 1 / (12 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  obtain ⟨h1, h2⟩ := logGamma_binet_bracket hn0
  rw [logGamma_nat hn] at h1 h2
  constructor <;> linarith

/-- **Stirling's bounds for the factorial, sharp form**:
`√(2πn) (n/e)^n < n! < √(2πn) (n/e)^n · e^{1/(12n)}`. -/
theorem factorial_binet_bracket {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n < (Nat.factorial n : ℝ) ∧
      (Nat.factorial n : ℝ)
        < Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n
            * Real.exp (1 / (12 * (n : ℝ))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  set M : ℝ := ((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π) with hM
  obtain ⟨h1, h2⟩ := log_factorial_binet_bracket hn
  have hbase : Real.exp (Real.log (n : ℝ) - 1) = (n : ℝ) / Real.exp 1 := by
    rw [Real.exp_sub, Real.exp_log hn0]
  have hpow : ((n : ℝ) / Real.exp 1) ^ n = Real.exp ((n : ℝ) * (Real.log (n : ℝ) - 1)) := by
    rw [Real.exp_nat_mul, hbase]
  have hmain : Real.exp M = Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n := by
    rw [hpow, hM]
    exact exp_stirling_main hn0
  refine ⟨?_, ?_⟩
  · have : Real.exp M < (Nat.factorial n : ℝ) := by
      rw [← Real.exp_log hfacpos]
      exact Real.exp_lt_exp.mpr (by linarith)
    rwa [hmain] at this
  · have : (Nat.factorial n : ℝ) < Real.exp (M + 1 / (12 * (n : ℝ))) := by
      nth_rewrite 1 [← Real.exp_log hfacpos]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at this
    exact this

end SHSLib.Trigamma
