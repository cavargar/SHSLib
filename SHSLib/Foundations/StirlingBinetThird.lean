/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Binet's third-order envelope `1/(12x) − 1/(360x³) + 1/(1260x⁵)`

Batches 156 and 157 gave the two-sided Binet envelope

  `½log(2π) + 1/(12x) − 1/(360x³) < S(x) < ½log(2π) + 1/(12x)`

for the Stirling defect `S(x) = log Γ(x) − (x − ½) log x + x`.  The next term
of Binet's expansion is `+1/(1260x⁵)`, and it sharpens the *upper* envelope:

  `S(x) < ½log(2π) + 1/(12x) − 1/(360x³) + 1/(1260x⁵)`.

The engine is again the step device of batch 156: the digamma bound

  `ψ(x) > log x − 1/(2x) − 1/(12x²) + 1/(120x⁴) − 1/(252x⁶)`

is proved by writing the unit-step difference of
`g(y) = ψ(y) − log y + 1/(2y) + 1/(12y²) − 1/(120y⁴) + 1/(252y⁶)`
as one explicit function of `t = 1/y`,

  `binetAux3 t = binetAux2 t + t⁶/252 − t⁶/(252(1+t)⁶)`,

whose derivative collapses to
`t⁸ (63 + 126t + 98t² + 35t³ + 5t⁴) / (210(1+t)⁷) > 0`.  As at each earlier
order, the leading terms of the two contributions cancel — here through order
`t⁷` — leaving a root of order eight at `0`.
-/
import SHSLib.Foundations.StirlingBinetSecond

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The third-order Binet auxiliary function -/

/-- `binetAux3 t = binetAux2 t + t⁶/252 − t⁶/(252(1+t)⁶)`.  It is the unit-step
decrement of `ψ(x) − log x + 1/(2x) + 1/(12x²) − 1/(120x⁴) + 1/(252x⁶)`
expressed in `t = 1/x`. -/
noncomputable def binetAux3 (t : ℝ) : ℝ :=
  binetAux2 t + t ^ 6 / 252 - t ^ 6 / (252 * (1 + t) ^ 6)

theorem binetAux3_zero : binetAux3 0 = 0 := by
  simp [binetAux3, binetAux2_zero]

/-- The derivative of `binetAux3` collapses to
`t⁸ (63 + 126t + 98t² + 35t³ + 5t⁴) / (210(1+t)⁷)`. -/
theorem hasDerivAt_binetAux3 {t : ℝ} (ht : -1 < t) :
    HasDerivAt binetAux3
      (t ^ 8 * (63 + 126 * t + 98 * t ^ 2 + 35 * t ^ 3 + 5 * t ^ 4)
        / (210 * (1 + t) ^ 7)) t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hb := hasDerivAt_binetAux2 ht
  have hsix : HasDerivAt (fun s : ℝ => s ^ 6) (6 * t ^ 5) t := by
    simpa using (hasDerivAt_pow 6 t)
  have hquart : HasDerivAt (fun s : ℝ => s ^ 6 / 252) (6 * t ^ 5 / 252) t := by
    simpa [div_eq_mul_inv] using hsix.div_const (252 : ℝ)
  have hden : HasDerivAt (fun s : ℝ => 252 * (1 + s) ^ 6) (252 * (6 * (1 + t) ^ 5)) t := by
    have h0 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h : HasDerivAt (fun s : ℝ => (1 + s) ^ 6) (6 * (1 + t) ^ 5) t := by
      simpa using (h0.pow 6)
    simpa using h.const_mul (252 : ℝ)
  have hfrac : HasDerivAt (fun s : ℝ => s ^ 6 / (252 * (1 + s) ^ 6))
      ((6 * t ^ 5 * (252 * (1 + t) ^ 6) - t ^ 6 * (252 * (6 * (1 + t) ^ 5)))
        / (252 * (1 + t) ^ 6) ^ 2) t :=
    hsix.div hden (by positivity)
  have htotal := (hb.add hquart).sub hfrac
  have hval : -(t ^ 6 * (5 + 5 * t + t ^ 2) / (30 * (1 + t) ^ 5)) + 6 * t ^ 5 / 252
      - (6 * t ^ 5 * (252 * (1 + t) ^ 6) - t ^ 6 * (252 * (6 * (1 + t) ^ 5)))
        / (252 * (1 + t) ^ 6) ^ 2
      = t ^ 8 * (63 + 126 * t + 98 * t ^ 2 + 35 * t ^ 3 + 5 * t ^ 4)
        / (210 * (1 + t) ^ 7) := by
    have h1 : (1 + t) ≠ 0 := h1t.ne'
    field_simp
    ring
  rw [← hval]
  exact htotal

/-- `binetAux3` is strictly positive on `(0, ∞)`. -/
theorem binetAux3_pos {t : ℝ} (ht : 0 < t) : 0 < binetAux3 t := by
  have hmono : StrictMonoOn binetAux3 (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · intro s hs
      have hs0 : (0 : ℝ) ≤ s := hs
      exact (hasDerivAt_binetAux3 (by linarith)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : (0 : ℝ) < s := hs
      rw [(hasDerivAt_binetAux3 (by linarith)).deriv]
      positivity
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr ht.le) ht
  rwa [binetAux3_zero] at this

/-! ### The sharpened digamma lower bound -/

/-- The unit-step decrement of
`ψ(x) − log x + 1/(2x) + 1/(12x²) − 1/(120x⁴) + 1/(252x⁶)` is `binetAux3 (1/x)`. -/
theorem digamma_binet3_step_eq {x : ℝ} (hx : 0 < x) :
    (digamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4)
        + 1 / (252 * x ^ 6))
        - (digamma (x + 1) - Real.log (x + 1) + 1 / (2 * (x + 1)) + 1 / (12 * (x + 1) ^ 2)
            - 1 / (120 * (x + 1) ^ 4) + 1 / (252 * (x + 1) ^ 6))
      = binetAux3 (1 / x) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hb := digamma_binet2_step_eq hx
  have hextra : (1 / x) ^ 6 / 252 - (1 / x) ^ 6 / (252 * (1 + 1 / x) ^ 6)
      = 1 / (252 * x ^ 6) - 1 / (252 * (x + 1) ^ 6) := by
    have hone : (1 : ℝ) + 1 / x = (x + 1) / x := by field_simp
    rw [hone]
    field_simp
  rw [binetAux3]
  linarith [hb, hextra]

/-- The unit-step decrement is strictly positive. -/
theorem digamma_binet3_step {x : ℝ} (hx : 0 < x) :
    digamma (x + 1) - Real.log (x + 1) + 1 / (2 * (x + 1)) + 1 / (12 * (x + 1) ^ 2)
        - 1 / (120 * (x + 1) ^ 4) + 1 / (252 * (x + 1) ^ 6)
      < digamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4)
          + 1 / (252 * x ^ 6) := by
  have h := digamma_binet3_step_eq hx
  have hpos : 0 < binetAux3 (1 / x) := binetAux3_pos (by positivity)
  linarith [h ▸ hpos]

/-- **`ψ(x) > log x − 1/(2x) − 1/(12x²) + 1/(120x⁴) − 1/(252x⁶)`** for every `x > 0`. -/
theorem digamma_gt_log_sub_binet_third {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) + 1 / (120 * x ^ 4) - 1 / (252 * x ^ 6)
      < digamma x := by
  set f : ℝ → ℝ :=
    fun y => digamma y - Real.log y + 1 / (2 * y) + 1 / (12 * y ^ 2) - 1 / (120 * y ^ 4)
      + 1 / (252 * y ^ 6) with hf_def
  have hstep : ∀ y : ℝ, 0 < y → f (y + 1) < f y := fun y hy => digamma_binet3_step hy
  have hinv : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => digamma y - Real.log y) atTop (𝓝 0) :=
      tendsto_digamma_sub_log_atTop
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
    have h4 : Tendsto (fun y : ℝ => 1 / (120 * y ^ 4)) atTop (𝓝 0) := by
      have h := ((((hinv.mul hinv).mul hinv).mul hinv).const_mul (1 / 120 : ℝ))
      simp only [mul_zero] at h
      refine h.congr (fun y => ?_)
      rcases eq_or_ne y 0 with rfl | hy
      · norm_num
      · field_simp
    have h6 : Tendsto (fun y : ℝ => 1 / (252 * y ^ 6)) atTop (𝓝 0) := by
      have h := ((((((hinv.mul hinv).mul hinv).mul hinv).mul hinv).mul hinv).const_mul
        (1 / 252 : ℝ))
      simp only [mul_zero] at h
      refine h.congr (fun y => ?_)
      rcases eq_or_ne y 0 with rfl | hy
      · norm_num
      · field_simp
    have h := (((h1.add h2).add h3).sub h4).add h6
    simpa [hf_def] using h
  have hpos := pos_of_step_of_tendsto_atTop hstep hlim hx
  simp only [hf_def] at hpos
  linarith

/-! ### The sharpened Stirling upper envelope -/

/-- `S(x) − 1/(12x) + 1/(360x³) − 1/(1260x⁵)` is strictly increasing on `(0, ∞)`. -/
theorem stirlingDefect_binet_third_strictMonoOn :
    StrictMonoOn
      (fun x : ℝ => stirlingDefect x - 1 / (12 * x) + 1 / (360 * x ^ 3) - 1 / (1260 * x ^ 5))
      (Ioi 0) := by
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ =>
          stirlingDefect y - 1 / (12 * y) + 1 / (360 * y ^ 3) - 1 / (1260 * y ^ 5))
        (digamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4)
          + 1 / (252 * x ^ 6)) x := by
    intro x hx0
    have hden1 : HasDerivAt (fun y : ℝ => 12 * y) 12 x := by
      simpa using (hasDerivAt_id x).const_mul (12 : ℝ)
    have hinv1 : HasDerivAt (fun y : ℝ => 1 / (12 * y)) (-(1 / (12 * x ^ 2))) x := by
      have h := (hasDerivAt_const x (1 : ℝ)).div hden1 (by positivity)
      simp only [zero_mul, zero_sub] at h
      convert h using 1
      field_simp
    have hden2 : HasDerivAt (fun y : ℝ => 360 * y ^ 3) (360 * (3 * x ^ 2)) x := by
      have h : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
        simpa using (hasDerivAt_pow 3 x)
      simpa using h.const_mul (360 : ℝ)
    have hinv2 : HasDerivAt (fun y : ℝ => 1 / (360 * y ^ 3)) (-(1 / (120 * x ^ 4))) x := by
      have h := (hasDerivAt_const x (1 : ℝ)).div hden2 (by positivity)
      simp only [zero_mul, zero_sub] at h
      convert h using 1
      field_simp
      ring
    have hden3 : HasDerivAt (fun y : ℝ => 1260 * y ^ 5) (1260 * (5 * x ^ 4)) x := by
      have h : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by
        simpa using (hasDerivAt_pow 5 x)
      simpa using h.const_mul (1260 : ℝ)
    have hinv3 : HasDerivAt (fun y : ℝ => 1 / (1260 * y ^ 5)) (-(1 / (252 * x ^ 6))) x := by
      have h := (hasDerivAt_const x (1 : ℝ)).div hden3 (by positivity)
      simp only [zero_mul, zero_sub] at h
      convert h using 1
      field_simp
      ring
    have h := (((hasDerivAt_stirlingDefect hx0).sub hinv1).add hinv2).sub hinv3
    convert h using 1
    ring
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := mem_Ioi.mp hx
    exact (hderiv x hx0).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0 : ℝ) < x := hx
    rw [(hderiv x hx0).deriv]
    have hlow := digamma_gt_log_sub_binet_third hx0
    linarith

/-- **The third-order Binet upper bound**:
`S(x) < ½ log(2π) + 1/(12x) − 1/(360x³) + 1/(1260x⁵)`. -/
theorem stirlingDefect_lt_binet_third {x : ℝ} (hx : 0 < x) :
    stirlingDefect x
      < 1 / 2 * Real.log (2 * π) + 1 / (12 * x) - 1 / (360 * x ^ 3) + 1 / (1260 * x ^ 5) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hinv : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
  have h12 : Tendsto (fun y : ℝ => 1 / (12 * y)) atTop (𝓝 0) := by
    have h := hinv.const_mul (1 / 12 : ℝ)
    simp only [mul_zero] at h
    refine h.congr (fun y => ?_)
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num
    · field_simp
  have h360 : Tendsto (fun y : ℝ => 1 / (360 * y ^ 3)) atTop (𝓝 0) := by
    have h := (((hinv.mul hinv).mul hinv).const_mul (1 / 360 : ℝ))
    simp only [mul_zero] at h
    refine h.congr (fun y => ?_)
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num
    · field_simp
  have h1260 : Tendsto (fun y : ℝ => 1 / (1260 * y ^ 5)) atTop (𝓝 0) := by
    have h := (((((hinv.mul hinv).mul hinv).mul hinv).mul hinv).const_mul (1 / 1260 : ℝ))
    simp only [mul_zero] at h
    refine h.congr (fun y => ?_)
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num
    · field_simp
  have hTlim : Tendsto
      (fun y : ℝ => stirlingDefect y - 1 / (12 * y) + 1 / (360 * y ^ 3) - 1 / (1260 * y ^ 5))
      atTop (𝓝 (1 / 2 * Real.log (2 * π))) := by
    simpa using ((tendsto_stirlingDefect.sub h12).add h360).sub h1260
  have hle : stirlingDefect (x + 1) - 1 / (12 * (x + 1)) + 1 / (360 * (x + 1) ^ 3)
      - 1 / (1260 * (x + 1) ^ 5) ≤ 1 / 2 * Real.log (2 * π) := by
    refine ge_of_tendsto hTlim ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases eq_or_lt_of_le hy with heq | hlt
    · rw [heq]
    · exact le_of_lt (stirlingDefect_binet_third_strictMonoOn (mem_Ioi.mpr hx1)
        (mem_Ioi.mpr (by linarith)) hlt)
  have hstep := stirlingDefect_binet_third_strictMonoOn (mem_Ioi.mpr hx) (mem_Ioi.mpr hx1)
    (by linarith : x < x + 1)
  simp only at hstep
  linarith

/-- **Binet's third-order two-sided envelope for `log Γ`**: the error in
`log Γ(x) ≈ (x − ½) log x − x + ½ log(2π)` lies between `1/(12x) − 1/(360x³)`
and `1/(12x) − 1/(360x³) + 1/(1260x⁵)`. -/
theorem logGamma_binet_third_bracket {x : ℝ} (hx : 0 < x) :
    1 / (12 * x) - 1 / (360 * x ^ 3)
        < logGamma x - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)) ∧
      logGamma x - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π))
        < 1 / (12 * x) - 1 / (360 * x ^ 3) + 1 / (1260 * x ^ 5) := by
  have h1 := stirlingDefect_gt_stirlingConstant_add_binet_sub hx
  have h2 := stirlingDefect_lt_binet_third hx
  rw [stirlingDefect] at h1 h2
  constructor <;> linarith

/-- **Two-sided bound on `log n!` with three Binet terms.** -/
theorem log_factorial_binet_third_bracket {n : ℕ} (hn : 1 ≤ n) :
    1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3)
        < Real.log (Nat.factorial n)
          - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π)) ∧
      Real.log (Nat.factorial n)
        - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π))
          < 1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3) + 1 / (1260 * (n : ℝ) ^ 5) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  obtain ⟨h1, h2⟩ := logGamma_binet_third_bracket hn0
  rw [logGamma_nat hn] at h1 h2
  constructor <;> linarith

/-- **Stirling's bounds for the factorial, third-order form**:
`√(2πn)(n/e)ⁿ e^{1/(12n) − 1/(360n³)} < n! < √(2πn)(n/e)ⁿ e^{1/(12n) − 1/(360n³) + 1/(1260n⁵)}`. -/
theorem factorial_binet_third_bracket {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n
          * Real.exp (1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3))
        < (Nat.factorial n : ℝ) ∧
      (Nat.factorial n : ℝ)
        < Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n
            * Real.exp (1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3)
              + 1 / (1260 * (n : ℝ) ^ 5)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  set M : ℝ := ((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π) with hM
  obtain ⟨h1, h2⟩ := log_factorial_binet_third_bracket hn
  have hbase : Real.exp (Real.log (n : ℝ) - 1) = (n : ℝ) / Real.exp 1 := by
    rw [Real.exp_sub, Real.exp_log hn0]
  have hpow : ((n : ℝ) / Real.exp 1) ^ n = Real.exp ((n : ℝ) * (Real.log (n : ℝ) - 1)) := by
    rw [Real.exp_nat_mul, hbase]
  have hmain : Real.exp M = Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n := by
    rw [hpow, hM]
    exact exp_stirling_main hn0
  refine ⟨?_, ?_⟩
  · have h : Real.exp (M + (1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3)))
        < (Nat.factorial n : ℝ) := by
      rw [← Real.exp_log hfacpos]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at h
    exact h
  · have h : (Nat.factorial n : ℝ)
        < Real.exp (M + (1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3)
          + 1 / (1260 * (n : ℝ) ^ 5))) := by
      nth_rewrite 1 [← Real.exp_log hfacpos]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at h
    exact h

end SHSLib.Trigamma
