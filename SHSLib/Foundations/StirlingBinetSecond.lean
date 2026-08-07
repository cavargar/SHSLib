/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Binet's second-order envelope `1/(12x) − 1/(360x³)`

Batch 156 (`SHSLib/Foundations/StirlingBinet.lean`) trapped the Stirling defect
`S(x) = log Γ(x) − (x − ½) log x + x` in

  `½ log (2π) < S(x) < ½ log (2π) + 1/(12x)`.

The next term of Binet's asymptotic expansion is `−1/(360x³)`, giving the
sharper lower envelope

  `½ log (2π) + 1/(12x) − 1/(360x³) < S(x)`.

It follows from the matching digamma *upper* bound

  `ψ(x) < log x − 1/(2x) − 1/(12x²) + 1/(120x⁴)`,

which is proved by the reusable device of batch 156: the whole unit-step
difference of `g(y) = ψ(y) − log y + 1/(2y) + 1/(12y²) − 1/(120y⁴)` is one
explicit function of `t = 1/y`,

  `binetAux2 t = binetAux t − t⁴/120 + t⁴/(120(1+t)⁴)`,

whose derivative collapses to the manifestly negative
`−t⁶(5 + 5t + t²) / (30(1+t)⁵)`.  Note that the fifth-order terms of
`binetAux` and of the new quartic correction cancel exactly, which is why the
derivative starts at order six.
-/
import SHSLib.Foundations.StirlingBinet

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The second-order Binet auxiliary function -/

/-- `binetAux2 t = binetAux t − t⁴/120 + t⁴/(120(1+t)⁴)`.  It is the unit-step
decrement of `ψ(x) − log x + 1/(2x) + 1/(12x²) − 1/(120x⁴)` expressed in
`t = 1/x`. -/
noncomputable def binetAux2 (t : ℝ) : ℝ :=
  binetAux t - t ^ 4 / 120 + t ^ 4 / (120 * (1 + t) ^ 4)

theorem binetAux2_zero : binetAux2 0 = 0 := by
  simp [binetAux2, binetAux_zero]

/-- The derivative of `binetAux2` collapses to `−t⁶(5 + 5t + t²)/(30(1+t)⁵)`. -/
theorem hasDerivAt_binetAux2 {t : ℝ} (ht : -1 < t) :
    HasDerivAt binetAux2 (-(t ^ 6 * (5 + 5 * t + t ^ 2) / (30 * (1 + t) ^ 5))) t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hb := hasDerivAt_binetAux ht
  have hquart : HasDerivAt (fun s : ℝ => s ^ 4 / 120) (4 * t ^ 3 / 120) t := by
    have h : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
      simpa using (hasDerivAt_pow 4 t)
    simpa [div_eq_mul_inv] using h.div_const (120 : ℝ)
  have hnum : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
    simpa using (hasDerivAt_pow 4 t)
  have hden : HasDerivAt (fun s : ℝ => 120 * (1 + s) ^ 4) (120 * (4 * (1 + t) ^ 3)) t := by
    have h0 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h : HasDerivAt (fun s : ℝ => (1 + s) ^ 4) (4 * (1 + t) ^ 3) t := by
      simpa using (h0.pow 4)
    simpa using h.const_mul (120 : ℝ)
  have hfrac : HasDerivAt (fun s : ℝ => s ^ 4 / (120 * (1 + s) ^ 4))
      ((4 * t ^ 3 * (120 * (1 + t) ^ 4) - t ^ 4 * (120 * (4 * (1 + t) ^ 3)))
        / (120 * (1 + t) ^ 4) ^ 2) t :=
    hnum.div hden (by positivity)
  have htotal := (hb.sub hquart).add hfrac
  have hval : t ^ 4 / (6 * (1 + t) ^ 3) - 4 * t ^ 3 / 120
      + (4 * t ^ 3 * (120 * (1 + t) ^ 4) - t ^ 4 * (120 * (4 * (1 + t) ^ 3)))
        / (120 * (1 + t) ^ 4) ^ 2
      = -(t ^ 6 * (5 + 5 * t + t ^ 2) / (30 * (1 + t) ^ 5)) := by
    have h1 : (1 + t) ≠ 0 := h1t.ne'
    field_simp
    ring
  rw [← hval]
  exact htotal

/-- `binetAux2` is strictly negative on `(0, ∞)`. -/
theorem binetAux2_neg {t : ℝ} (ht : 0 < t) : binetAux2 t < 0 := by
  have hanti : StrictAntiOn binetAux2 (Ici 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici 0) ?_ ?_
    · intro s hs
      have hs0 : (0 : ℝ) ≤ s := hs
      exact (hasDerivAt_binetAux2 (by linarith)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : (0 : ℝ) < s := hs
      rw [(hasDerivAt_binetAux2 (by linarith)).deriv]
      have hpos : 0 < s ^ 6 * (5 + 5 * s + s ^ 2) / (30 * (1 + s) ^ 5) := by positivity
      linarith
  have := hanti (Set.self_mem_Ici) (Set.mem_Ici.mpr ht.le) ht
  rwa [binetAux2_zero] at this

/-! ### The sharpened digamma upper bound -/

/-- The unit-step decrement of `ψ(x) − log x + 1/(2x) + 1/(12x²) − 1/(120x⁴)` is
`binetAux2 (1/x)`. -/
theorem digamma_binet2_step_eq {x : ℝ} (hx : 0 < x) :
    (digamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4))
        - (digamma (x + 1) - Real.log (x + 1) + 1 / (2 * (x + 1)) + 1 / (12 * (x + 1) ^ 2)
            - 1 / (120 * (x + 1) ^ 4))
      = binetAux2 (1 / x) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hb := digamma_binet_step_eq hx
  have hextra : (1 / x) ^ 4 / (120 * (1 + 1 / x) ^ 4) - (1 / x) ^ 4 / 120
      = -(1 / (120 * x ^ 4)) + 1 / (120 * (x + 1) ^ 4) := by
    have hone : (1 : ℝ) + 1 / x = (x + 1) / x := by field_simp
    rw [hone]
    field_simp
    ring
  rw [binetAux2]
  linarith [hb, hextra]

/-- The unit-step decrement is strictly negative. -/
theorem digamma_binet2_step {x : ℝ} (hx : 0 < x) :
    digamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4)
      < digamma (x + 1) - Real.log (x + 1) + 1 / (2 * (x + 1)) + 1 / (12 * (x + 1) ^ 2)
          - 1 / (120 * (x + 1) ^ 4) := by
  have h := digamma_binet2_step_eq hx
  have hneg : binetAux2 (1 / x) < 0 := binetAux2_neg (by positivity)
  linarith [h ▸ hneg]

/-- **`ψ(x) < log x − 1/(2x) − 1/(12x²) + 1/(120x⁴)`** for every `x > 0`. -/
theorem digamma_lt_log_sub_half_inv_sub_binet_add {x : ℝ} (hx : 0 < x) :
    digamma x < Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) + 1 / (120 * x ^ 4) := by
  set f : ℝ → ℝ :=
    fun y => -(digamma y - Real.log y + 1 / (2 * y) + 1 / (12 * y ^ 2) - 1 / (120 * y ^ 4))
    with hf_def
  have hstep : ∀ y : ℝ, 0 < y → f (y + 1) < f y := by
    intro y hy
    have := digamma_binet2_step hy
    simp only [hf_def]
    linarith
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
    have h := ((h1.add h2).add h3).sub h4
    have h0 : Tendsto
        (fun y : ℝ => digamma y - Real.log y + 1 / (2 * y) + 1 / (12 * y ^ 2)
          - 1 / (120 * y ^ 4)) atTop (𝓝 0) := by
      simpa using h
    simpa [hf_def] using h0.neg
  have hpos := pos_of_step_of_tendsto_atTop hstep hlim hx
  simp only [hf_def] at hpos
  linarith

/-! ### The sharp Stirling lower envelope -/

/-- `S(x) − 1/(12x) + 1/(360x³)` is strictly decreasing on `(0, ∞)`. -/
theorem stirlingDefect_sub_binet_add_binet2_strictAntiOn :
    StrictAntiOn (fun x : ℝ => stirlingDefect x - 1 / (12 * x) + 1 / (360 * x ^ 3)) (Ioi 0) := by
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => stirlingDefect y - 1 / (12 * y) + 1 / (360 * y ^ 3))
        (digamma x - Real.log x + 1 / (2 * x) + 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4)) x := by
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
    have h := ((hasDerivAt_stirlingDefect hx0).sub hinv1).add hinv2
    convert h using 1
    ring
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := mem_Ioi.mp hx
    exact (hderiv x hx0).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0 : ℝ) < x := hx
    rw [(hderiv x hx0).deriv]
    have hup := digamma_lt_log_sub_half_inv_sub_binet_add hx0
    linarith

/-- **The second-order Binet lower bound**: `S(x) > ½ log(2π) + 1/(12x) − 1/(360x³)`. -/
theorem stirlingDefect_gt_stirlingConstant_add_binet_sub {x : ℝ} (hx : 0 < x) :
    1 / 2 * Real.log (2 * π) + 1 / (12 * x) - 1 / (360 * x ^ 3) < stirlingDefect x := by
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
  have hTlim : Tendsto (fun y : ℝ => stirlingDefect y - 1 / (12 * y) + 1 / (360 * y ^ 3)) atTop
      (𝓝 (1 / 2 * Real.log (2 * π))) := by
    simpa using (tendsto_stirlingDefect.sub h12).add h360
  have hge : 1 / 2 * Real.log (2 * π)
      ≤ stirlingDefect (x + 1) - 1 / (12 * (x + 1)) + 1 / (360 * (x + 1) ^ 3) := by
    refine le_of_tendsto hTlim ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases eq_or_lt_of_le hy with heq | hlt
    · rw [heq]
    · exact le_of_lt (stirlingDefect_sub_binet_add_binet2_strictAntiOn (mem_Ioi.mpr hx1)
        (mem_Ioi.mpr (by linarith)) hlt)
  have hstep := stirlingDefect_sub_binet_add_binet2_strictAntiOn (mem_Ioi.mpr hx)
    (mem_Ioi.mpr hx1) (by linarith : x < x + 1)
  simp only at hstep
  linarith

/-- **Binet's two-sided envelope for `log Γ`**: the error in
`log Γ(x) ≈ (x − ½) log x − x + ½ log (2π)` lies between `1/(12x) − 1/(360x³)`
and `1/(12x)`. -/
theorem logGamma_binet_second_bracket {x : ℝ} (hx : 0 < x) :
    1 / (12 * x) - 1 / (360 * x ^ 3)
        < logGamma x - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)) ∧
      logGamma x - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π))
        < 1 / (12 * x) := by
  have h1 := stirlingDefect_gt_stirlingConstant_add_binet_sub hx
  have h2 := stirlingDefect_lt_stirlingConstant_add_binet hx
  rw [stirlingDefect] at h1 h2
  constructor <;> linarith

/-! ### The sharp factorial bounds -/

/-- **Two-sided bound on `log n!` with both Binet terms.** -/
theorem log_factorial_binet_second_bracket {n : ℕ} (hn : 1 ≤ n) :
    1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3)
        < Real.log (Nat.factorial n)
          - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π)) ∧
      Real.log (Nat.factorial n)
        - (((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π))
          < 1 / (12 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  obtain ⟨h1, h2⟩ := logGamma_binet_second_bracket hn0
  rw [logGamma_nat hn] at h1 h2
  constructor <;> linarith

/-- **Stirling's bounds for the factorial, second-order form**:
`√(2πn) (n/e)^n · e^{1/(12n) − 1/(360n³)} < n! < √(2πn) (n/e)^n · e^{1/(12n)}`. -/
theorem factorial_binet_second_bracket {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n
          * Real.exp (1 / (12 * (n : ℝ)) - 1 / (360 * (n : ℝ) ^ 3))
        < (Nat.factorial n : ℝ) ∧
      (Nat.factorial n : ℝ)
        < Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n
            * Real.exp (1 / (12 * (n : ℝ))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  set M : ℝ := ((n : ℝ) + 1 / 2) * Real.log (n : ℝ) - n + 1 / 2 * Real.log (2 * π) with hM
  obtain ⟨h1, h2⟩ := log_factorial_binet_second_bracket hn
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
  · have h : (Nat.factorial n : ℝ) < Real.exp (M + 1 / (12 * (n : ℝ))) := by
      nth_rewrite 1 [← Real.exp_log hfacpos]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_add, hmain] at h
    exact h

end SHSLib.Trigamma
