/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Quantitative decay of the polygamma functions

The mean value technique of batch 148, applied one derivative higher, brackets
the trigamma function:

  `1/x < ψ'(x)` for `x > 0`   (`inv_lt_trigamma`),
  `ψ'(x) < 1/(x−1)` for `x > 1`   (`trigamma_lt_inv_sub_one`).

Indeed Lagrange's theorem applied to `ψ` on `[x, x+1]` produces `c` in the
interior with `ψ'(c) = ψ(x+1) − ψ(x) = 1/x`, and `ψ'` is strictly decreasing.

Combined with the polygamma series of batch 150 and the termwise bound
`1/(x+k)^{j+2} ≤ x^{-j} (x+k)^{-2}`, this gives the decay of every polygamma
function:

  `|(log Γ)^{(j+2)}(x)| ≤ (j+1)! / (x^j (x−1))` for `x > 1`
  (`abs_polygamma_le`),

hence `(log Γ)^{(m)}(x) → 0` as `x → ∞` for every `m ≥ 2`
(`tendsto_polygamma_atTop`).
-/
import SHSLib.Foundations.Polygamma
import SHSLib.Foundations.DigammaAsymptotics

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### Bracketing the trigamma function -/

/-- Lagrange's theorem applied to `ψ` on `[x, x+1]`: there is `c ∈ (x, x+1)`
with `ψ'(c) = 1/x`. -/
theorem exists_trigamma_eq_inv {x : ℝ} (hx : 0 < x) :
    ∃ c ∈ Ioo x (x + 1), trigamma c = 1 / x := by
  have hsub : Icc x (x + 1) ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le hx hy.1
  have hcont : ContinuousOn digamma (Icc x (x + 1)) :=
    contDiffOn_deriv_logGamma.continuousOn.mono hsub
  have hderiv : ∀ y ∈ Ioo x (x + 1), HasDerivAt digamma (trigamma y) y :=
    fun y hy => deriv_digamma (lt_trans hx hy.1)
  obtain ⟨c, hc, hceq⟩ :=
    exists_hasDerivAt_eq_slope digamma trigamma (by linarith) hcont hderiv
  refine ⟨c, hc, ?_⟩
  rw [hceq, digamma_recurrence hx]
  ring_nf

/-- `1/x < ψ'(x)` for every `x > 0`. -/
theorem inv_lt_trigamma {x : ℝ} (hx : 0 < x) : 1 / x < trigamma x := by
  obtain ⟨c, hc, hceq⟩ := exists_trigamma_eq_inv hx
  have hlt := trigamma_strictAntiOn (mem_Ioi.mpr hx)
    (mem_Ioi.mpr (lt_trans hx hc.1)) hc.1
  rwa [hceq] at hlt

/-- `ψ'(x) < 1/(x−1)` for every `x > 1`. -/
theorem trigamma_lt_inv_sub_one {x : ℝ} (hx : 1 < x) : trigamma x < 1 / (x - 1) := by
  obtain ⟨c, hc, hceq⟩ := exists_trigamma_eq_inv (x := x - 1) (by linarith)
  have hcx : c < x := by
    have := hc.2
    linarith
  have hc0 : 0 < c := lt_trans (by linarith : (0 : ℝ) < x - 1) hc.1
  have hlt := trigamma_strictAntiOn (mem_Ioi.mpr hc0)
    (mem_Ioi.mpr (by linarith : (0 : ℝ) < x)) hcx
  rwa [hceq] at hlt

/-! ### Decay of the polygamma series -/

/-- For `x > 1`, `∑_{k ≥ 0} 1/(x+k)^{j+2} ≤ x^{-j}/(x−1)`. -/
theorem tsum_inv_pow_shift_le {x : ℝ} (hx : 1 < x) (j : ℕ) :
    (∑' k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 2)) ≤ (1 / x ^ j) * (1 / (x - 1)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hle : ∀ k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 2)
      ≤ (1 / x ^ j) * (1 / (x + (k : ℝ)) ^ 2) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hxk : (0 : ℝ) < x + k := by positivity
    have hpow : x ^ j ≤ (x + (k : ℝ)) ^ j := pow_le_pow_left₀ hx0.le (by linarith) j
    have hfac : (x + (k : ℝ)) ^ (j + 2) = (x + (k : ℝ)) ^ j * (x + (k : ℝ)) ^ 2 := by
      rw [pow_add]
    rw [hfac]
    have hstep : x ^ j * (x + (k : ℝ)) ^ 2 ≤ (x + (k : ℝ)) ^ j * (x + (k : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    calc 1 / ((x + (k : ℝ)) ^ j * (x + (k : ℝ)) ^ 2)
        ≤ 1 / (x ^ j * (x + (k : ℝ)) ^ 2) :=
          one_div_le_one_div_of_le (by positivity) hstep
      _ = (1 / x ^ j) * (1 / (x + (k : ℝ)) ^ 2) := by
          rw [one_div_mul_eq_div]
          field_simp
  have hsum1 : Summable (fun k : ℕ => 1 / (x + (k : ℝ)) ^ (j + 2)) :=
    summable_inv_pow_shift hx0 j
  have hsum2 : Summable (fun k : ℕ => (1 / x ^ j) * (1 / (x + (k : ℝ)) ^ 2)) :=
    (summable_inv_sq_shift hx0).mul_left _
  calc (∑' k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 2))
      ≤ ∑' k : ℕ, (1 / x ^ j) * (1 / (x + (k : ℝ)) ^ 2) :=
        hsum1.tsum_le_tsum hle hsum2
    _ = (1 / x ^ j) * ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ 2 := tsum_mul_left
    _ = (1 / x ^ j) * trigamma x := by rw [trigamma_eq_tsum hx0]
    _ ≤ (1 / x ^ j) * (1 / (x - 1)) := by
        have hpos : (0 : ℝ) < 1 / x ^ j := by positivity
        exact mul_le_mul_of_nonneg_left (trigamma_lt_inv_sub_one hx).le hpos.le

/-- **Decay of the polygamma functions**: for `x > 1`,
`|(log Γ)^{(j+2)}(x)| ≤ (j+1)!/(x^j (x−1))`. -/
theorem abs_polygamma_le (j : ℕ) {x : ℝ} (hx : 1 < x) :
    |deriv^[j + 2] logGamma x| ≤ (Nat.factorial (j + 1) : ℝ) * ((1 / x ^ j) * (1 / (x - 1))) := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [polygamma_series j hx0]
  have hnn : 0 ≤ ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 2) :=
    tsum_nonneg (fun k => by
      have : (0 : ℝ) < x + k := by positivity
      positivity)
  have hfac : (0 : ℝ) < (Nat.factorial (j + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hfac, abs_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left (tsum_inv_pow_shift_le hx j) hfac.le

/-- Every polygamma function of order `≥ 2` tends to `0` at infinity. -/
theorem tendsto_polygamma_atTop (j : ℕ) :
    Tendsto (fun x : ℝ => deriv^[j + 2] logGamma x) atTop (𝓝 0) := by
  have hbound : Tendsto (fun x : ℝ => (Nat.factorial (j + 1) : ℝ) * (1 / (x - 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
    have h2 : Tendsto (fun x : ℝ => 1 / (x - 1)) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero.comp h1
    simpa using h2.const_mul ((Nat.factorial (j + 1) : ℝ))
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have h := abs_polygamma_le j hx
  have hx1 : (1 : ℝ) ≤ x ^ j := one_le_pow₀ (by linarith)
  have hxpos : (0 : ℝ) < x ^ j := by positivity
  have hsub : (0 : ℝ) < x - 1 := by linarith
  have hstep : (1 / x ^ j) * (1 / (x - 1)) ≤ 1 / (x - 1) := by
    have : (1 : ℝ) / x ^ j ≤ 1 := by
      rw [div_le_one hxpos]; exact hx1
    nlinarith [one_div_pos.mpr hsub]
  have hfac : (0 : ℝ) ≤ (Nat.factorial (j + 1) : ℝ) := by positivity
  calc ‖deriv^[j + 2] logGamma x‖ = |deriv^[j + 2] logGamma x| := rfl
    _ ≤ (Nat.factorial (j + 1) : ℝ) * ((1 / x ^ j) * (1 / (x - 1))) := h
    _ ≤ (Nat.factorial (j + 1) : ℝ) * (1 / (x - 1)) :=
        mul_le_mul_of_nonneg_left hstep hfac

end SHSLib.Trigamma
