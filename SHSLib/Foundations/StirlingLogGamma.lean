/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stirling's formula for `log Γ`, up to the constant

The *Stirling defect*

  `S(x) = log Γ(x) − (x − 1/2) log x + x`

has derivative `S'(x) = ψ(x) − log x + 1/(2x)`, which the estimates of batches
148–151 pin between `−1/x²` and `0`:

* `ψ(x) < log x − 1/(2x)` (batch 151) gives `S' < 0`, so `S` is strictly
  decreasing;
* `ψ(x) > log x − 1/(2x) − 1/x²` (`digamma_gt_log_sub_half_inv_sub_inv_sq`,
  proved here by the telescoping criterion of batch 151) gives
  `S'(x) > −1/x²`, so `x ↦ S(x) − 1/x` is strictly increasing.

An increasing function bounded above converges, so `S` has a finite limit at
infinity (`exists_tendsto_stirlingDefect`), which is Stirling's formula up to
the value of the constant:

  `log Γ(x) = (x − 1/2) log x − x + C + o(1)`.

The identification `C = ½ log(2π)` is the subject of the next file.
-/
import SHSLib.Foundations.TrigammaSharpBracket

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### A quadratic lower bound for the logarithm -/

/-- `t − t²/2 ≤ log (1+t)` for `t ≥ 0`. -/
theorem sub_sq_div_two_le_log_one_add {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 2 / 2 ≤ Real.log (1 + t) := by
  set g : ℝ → ℝ := fun s => Real.log (1 + s) - s + s ^ 2 / 2 with hg_def
  have hderiv : ∀ s ∈ Ici (0 : ℝ), HasDerivAt g (s ^ 2 / (1 + s)) s := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := hs
    have hpos : (0 : ℝ) < 1 + s := by linarith
    have hlog : HasDerivAt (fun w : ℝ => Real.log (1 + w)) (1 / (1 + s)) s := by
      have h := (Real.hasDerivAt_log hpos.ne').comp s ((hasDerivAt_id s).const_add (1 : ℝ))
      simpa [one_div] using h
    have hsq : HasDerivAt (fun w : ℝ => w ^ 2 / 2) (2 * s / 2) s := by
      simpa using (hasDerivAt_pow 2 s).div_const 2
    have h := (hlog.sub (hasDerivAt_id s)).add hsq
    convert h using 1
    field_simp
    ring
  have hmono : MonotoneOn g (Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt) ?_ ?_
    · intro s hs
      rw [interior_Ici] at hs
      exact ((hderiv s (mem_Ici.mpr (le_of_lt (mem_Ioi.mp hs)))).differentiableAt).differentiableWithinAt
    intro s hs
    rw [interior_Ici] at hs
    have hs0 : (0 : ℝ) < s := hs
    rw [(hderiv s (le_of_lt hs0)).deriv]
    positivity
  have h0 : g 0 = 0 := by simp [hg_def]
  have hle := hmono (Set.self_mem_Ici) (mem_Ici.mpr ht) ht
  rw [h0] at hle
  simp only [hg_def] at hle
  linarith

/-! ### A refined lower bound for `ψ` -/

/-- The unit-step decrement of `ψ(x) − log x + 1/(2x) + 1/x²`. -/
theorem digamma_refined_step {x : ℝ} (hx : 0 < x) :
    (digamma (x + 1) - Real.log (x + 1) + 1 / (2 * (x + 1)) + 1 / (x + 1) ^ 2)
      < digamma x - Real.log x + 1 / (2 * x) + 1 / x ^ 2 := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hrec : digamma (x + 1) = digamma x + 1 / x := digamma_recurrence hx
  have hlogdiff : Real.log (x + 1) - Real.log x = Real.log (1 + 1 / x) := by
    rw [← Real.log_div hx1.ne' hx.ne']
    congr 1
    field_simp
  have hbound : 1 / x - (1 / x) ^ 2 / 2 ≤ Real.log (1 + 1 / x) :=
    sub_sq_div_two_le_log_one_add (by positivity)
  have hid : -(1 / (2 * x ^ 2)) + (1 / (2 * x) - 1 / (2 * (x + 1)))
      + (1 / x ^ 2 - 1 / (x + 1) ^ 2) = (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 2) := by
    field_simp
    ring
  have hsq : (1 / x) ^ 2 / 2 = 1 / (2 * x ^ 2) := by
    field_simp
  rw [hsq] at hbound
  have hpos : 0 < (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 2) := by positivity
  rw [hrec]
  linarith [hbound, hid, hpos, hlogdiff]

/-- **`ψ(x) > log x − 1/(2x) − 1/x²`** for every `x > 0`. -/
theorem digamma_gt_log_sub_half_inv_sub_inv_sq {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - 1 / x ^ 2 < digamma x := by
  set f : ℝ → ℝ := fun y => digamma y - Real.log y + 1 / (2 * y) + 1 / y ^ 2 with hf_def
  have hstep : ∀ y : ℝ, 0 < y → f (y + 1) < f y := fun y hy => digamma_refined_step hy
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => digamma y - Real.log y) atTop (𝓝 0) :=
      tendsto_digamma_sub_log_atTop
    have h2 : Tendsto (fun y : ℝ => 1 / (2 * y)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have h := h0.const_mul (1 / 2 : ℝ)
      simp only [mul_zero] at h
      exact h.congr (fun y => by simp [one_div, mul_comm])
    have h3 : Tendsto (fun y : ℝ => 1 / y ^ 2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
        simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
      simpa [div_mul_div_comm, sq] using h0.mul h0
    have := (h1.add h2).add h3
    simpa [hf_def] using this
  have hpos := pos_of_step_of_tendsto_atTop hstep hlim hx
  simp only [hf_def] at hpos
  linarith

/-! ### The Stirling defect -/

/-- The Stirling defect `S(x) = log Γ(x) − (x − 1/2) log x + x`. -/
noncomputable def stirlingDefect (x : ℝ) : ℝ :=
  logGamma x - (x - 1 / 2) * Real.log x + x

theorem hasDerivAt_stirlingDefect {x : ℝ} (hx : 0 < x) :
    HasDerivAt stirlingDefect (digamma x - Real.log x + 1 / (2 * x)) x := by
  have hlog : HasDerivAt (fun y : ℝ => (y - 1 / 2) * Real.log y)
      (1 * Real.log x + (x - 1 / 2) * (1 / x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y - 1 / 2) 1 x := (hasDerivAt_id x).sub_const _
    have h2 : HasDerivAt Real.log (1 / x) x := by
      simpa [one_div] using Real.hasDerivAt_log hx.ne'
    simpa using h1.mul h2
  have hG : HasDerivAt logGamma (digamma x) x := (differentiableAt_logGamma hx).hasDerivAt
  have h := (hG.sub hlog).add (hasDerivAt_id x)
  have heq : digamma x - (1 * Real.log x + (x - 1 / 2) * (1 / x)) + 1
      = digamma x - Real.log x + 1 / (2 * x) := by
    field_simp
    ring
  rw [← heq]
  exact h

/-- `S` is strictly decreasing on `(0, ∞)`. -/
theorem stirlingDefect_strictAntiOn : StrictAntiOn stirlingDefect (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · exact fun x hx => (hasDerivAt_stirlingDefect (mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0 : ℝ) < x := hx
    rw [(hasDerivAt_stirlingDefect hx0).deriv]
    have := digamma_lt_log_sub_half_inv hx0
    linarith

/-- The corrected defect `T(x) = S(x) − 1/x` is strictly increasing on `(0, ∞)`. -/
theorem stirlingDefect_sub_inv_strictMonoOn :
    StrictMonoOn (fun x : ℝ => stirlingDefect x - 1 / x) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := mem_Ioi.mp hx
    have h1 := (hasDerivAt_stirlingDefect hx0).continuousAt
    have h2 : ContinuousAt (fun y : ℝ => 1 / y) x := by
      exact (continuousAt_const.div continuousAt_id hx0.ne')
    exact (h1.sub h2).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0 : ℝ) < x := hx
    have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
      simpa [one_div] using hasDerivAt_inv hx0.ne'
    have h : HasDerivAt (fun y : ℝ => stirlingDefect y - 1 / y)
        (digamma x - Real.log x + 1 / (2 * x) - -(1 / x ^ 2)) x :=
      (hasDerivAt_stirlingDefect hx0).sub hinv
    rw [h.deriv]
    have hlow := digamma_gt_log_sub_half_inv_sub_inv_sq hx0
    have : digamma x - Real.log x + 1 / (2 * x) > -(1 / x ^ 2) := by linarith
    linarith

/-! ### Existence of the Stirling constant -/

/-- **Stirling's formula for `log Γ`, up to the constant**: the Stirling defect
converges at infinity. -/
theorem exists_tendsto_stirlingDefect :
    ∃ C : ℝ, Tendsto stirlingDefect atTop (𝓝 C) := by
  set T : ℝ → ℝ := fun x => stirlingDefect x - 1 / x with hT_def
  set F : ℝ → ℝ := fun y => T (max y 1) with hF_def
  have hTmono : StrictMonoOn T (Ioi 0) := stirlingDefect_sub_inv_strictMonoOn
  have hFmono : Monotone F := by
    intro y₁ y₂ h
    have h1 : (1 : ℝ) ≤ max y₁ 1 := le_max_right _ _
    have h2 : (1 : ℝ) ≤ max y₂ 1 := le_max_right _ _
    have hmax : max y₁ 1 ≤ max y₂ 1 := max_le_max h le_rfl
    rcases eq_or_lt_of_le hmax with heq | hlt
    · simp [hF_def, heq]
    · exact le_of_lt (hTmono (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) hlt)
  have hFbdd : BddAbove (Set.range F) := by
    refine ⟨stirlingDefect 1, ?_⟩
    rintro z ⟨y, rfl⟩
    have h1 : (1 : ℝ) ≤ max y 1 := le_max_right _ _
    have hinv : 0 < 1 / max y 1 := by positivity
    have hS : stirlingDefect (max y 1) ≤ stirlingDefect 1 := by
      rcases eq_or_lt_of_le h1 with heq | hlt
      · rw [← heq]
      · exact le_of_lt (stirlingDefect_strictAntiOn (mem_Ioi.mpr one_pos)
          (mem_Ioi.mpr (by linarith)) hlt)
    simp only [hF_def, hT_def]
    linarith
  obtain ⟨C, hC⟩ : ∃ C, Tendsto F atTop (𝓝 C) := ⟨_, tendsto_atTop_ciSup hFmono hFbdd⟩
  have hTF : Tendsto T atTop (𝓝 C) := by
    refine hC.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    simp [hF_def, max_eq_left hy]
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  refine ⟨C, ?_⟩
  have := hTF.add hinv
  simpa [hT_def] using this

end SHSLib.Trigamma
