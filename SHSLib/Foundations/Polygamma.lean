/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The polygamma series at every order

Batches 144 and 145 proved

  `(log Γ)''(x)  =  ∑_{k ≥ 0} 1/(x+k)²`,
  `(log Γ)'''(x) = −2 ∑_{k ≥ 0} 1/(x+k)³`

by a defect argument run separately at each order.  This file replaces the
repetition by a single induction: once the series is known at one order `≥ 2`,
it may simply be *differentiated termwise*, because the differentiated series
is dominated, uniformly on `(a, ∞)` for every `a > 0`, by a convergent series.
The result is

  `(log Γ)^{(j+2)}(x) = (−1)^j (j+1)! ∑_{k ≥ 0} 1/(x+k)^{j+2}`
  (`polygamma_series`),

for every `j : ℕ` and every `x > 0`, equivalently
`(log Γ)^{(m)}(x) = (−1)^m (m−1)! ∑_{k ≥ 0} 1/(x+k)^m` for `m ≥ 2`
(`polygamma_series_of_two_le`).  Its consequences: the sign
`(−1)^m (log Γ)^{(m)} > 0` (`polygamma_sign`), and the values at `1`, which are
the zeta values `(log Γ)^{(m)}(1) = (−1)^m (m−1)! ζ(m)`
(`polygamma_one_eq_zeta`).
-/
import SHSLib.Foundations.Tetragamma

open Real Set Filter

namespace SHSLib.Trigamma

/-! ### Summability of the shifted `m`-th power series -/

/-- For `x > 0` the family `k ↦ 1/(x+k)^{j+2}` is summable. -/
theorem summable_inv_pow_shift {x : ℝ} (hx : 0 < x) (j : ℕ) :
    Summable (fun k : ℕ => 1 / (x + k) ^ (j + 2)) := by
  have hb : Summable (fun k : ℕ => (1 / x) ^ j * (1 / (x + (k : ℝ)) ^ 2)) :=
    (summable_inv_sq_shift hx).mul_left _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hb
  · have : (0 : ℝ) < x + k := by positivity
    positivity
  · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hxk : (0 : ℝ) < x + k := by positivity
    have hpow : x ^ j ≤ (x + (k : ℝ)) ^ j := by
      exact pow_le_pow_left₀ hx.le (by linarith) j
    have hfac : (x + (k : ℝ)) ^ (j + 2) = (x + (k : ℝ)) ^ j * (x + (k : ℝ)) ^ 2 := by
      rw [pow_add]
    rw [hfac]
    have hxj : (0 : ℝ) < x ^ j := by positivity
    have hstep : x ^ j * (x + (k : ℝ)) ^ 2 ≤ (x + (k : ℝ)) ^ j * (x + (k : ℝ)) ^ 2 := by
      have h2 : (0 : ℝ) ≤ (x + (k : ℝ)) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right hpow h2
    have hle : 1 / ((x + (k : ℝ)) ^ j * (x + (k : ℝ)) ^ 2)
        ≤ 1 / (x ^ j * (x + (k : ℝ)) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hstep
    calc 1 / ((x + (k : ℝ)) ^ j * (x + (k : ℝ)) ^ 2)
        ≤ 1 / (x ^ j * (x + (k : ℝ)) ^ 2) := hle
      _ = (1 / x) ^ j * (1 / (x + (k : ℝ)) ^ 2) := by
          rw [div_pow, one_pow]
          field_simp

/-! ### Termwise differentiation -/

/-- The derivative of a single term: `d/dz (z+k)^{-(j+2)} = −(j+2)(z+k)^{-(j+3)}`. -/
theorem hasDerivAt_inv_pow_term (j k : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => 1 / (w + (k : ℝ)) ^ (j + 2))
      (-((j : ℝ) + 2) / (z + (k : ℝ)) ^ (j + 3)) z := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hzk : (0 : ℝ) < z + (k : ℝ) := by positivity
  have h1 : HasDerivAt (fun w : ℝ => w + (k : ℝ)) 1 z := (hasDerivAt_id z).add_const _
  have h2 : HasDerivAt (fun w : ℝ => (w + (k : ℝ)) ^ (j + 2))
      ((j + 2 : ℕ) * (z + (k : ℝ)) ^ (j + 2 - 1) * 1) z := h1.pow (j + 2)
  have hne : (z + (k : ℝ)) ^ (j + 2) ≠ 0 := by positivity
  have h3 := h2.inv hne
  have hval : -((j + 2 : ℕ) * (z + (k : ℝ)) ^ (j + 2 - 1) * 1) / ((z + (k : ℝ)) ^ (j + 2)) ^ 2
      = -((j : ℝ) + 2) / (z + (k : ℝ)) ^ (j + 3) := by
    have hpow : ((z + (k : ℝ)) ^ (j + 2)) ^ 2 = (z + (k : ℝ)) ^ (j + 3) * (z + (k : ℝ)) ^ (j + 1) := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    rw [hpow]
    have hsimp : (j + 2 - 1 : ℕ) = j + 1 := by omega
    rw [hsimp]
    push_cast
    rw [mul_one]
    field_simp
  simpa [one_div, hval] using h3.congr_deriv hval

/-- Termwise differentiation of the shifted power series on `(a, ∞)`. -/
theorem hasDerivAt_tsum_inv_pow {a : ℝ} (ha : 0 < a) (j : ℕ) {y : ℝ} (hy : a < y) :
    HasDerivAt (fun z : ℝ => ∑' k : ℕ, 1 / (z + (k : ℝ)) ^ (j + 2))
      (-((j : ℝ) + 2) * ∑' k : ℕ, 1 / (y + (k : ℝ)) ^ (j + 3)) y := by
  have hderiv : ∀ (k : ℕ), ∀ z ∈ Ioi a,
      HasDerivAt (fun w : ℝ => 1 / (w + (k : ℝ)) ^ (j + 2))
        (-((j : ℝ) + 2) / (z + (k : ℝ)) ^ (j + 3)) z :=
    fun k z hz => hasDerivAt_inv_pow_term j k (lt_trans ha hz)
  have hbound : ∀ (k : ℕ), ∀ z ∈ Ioi a,
      ‖-((j : ℝ) + 2) / (z + (k : ℝ)) ^ (j + 3)‖
        ≤ ((j : ℝ) + 2) * (1 / (a + (k : ℝ)) ^ (j + 3)) := by
    intro k z hz
    have hz' : a < z := hz
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hak : (0 : ℝ) < a + (k : ℝ) := by positivity
    have hzk : (0 : ℝ) < z + (k : ℝ) := by linarith
    have hpow : (a + (k : ℝ)) ^ (j + 3) ≤ (z + (k : ℝ)) ^ (j + 3) :=
      pow_le_pow_left₀ hak.le (by linarith) _
    have hposz : (0 : ℝ) < (z + (k : ℝ)) ^ (j + 3) := by positivity
    rw [norm_div, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 2), abs_of_pos hposz]
    rw [mul_one_div, div_le_div_iff_of_pos_left (by positivity) hposz (by positivity)]
    exact hpow
  have husum : Summable (fun k : ℕ => ((j : ℝ) + 2) * (1 / (a + (k : ℝ)) ^ (j + 3))) := by
    have h := summable_inv_pow_shift ha (j + 1)
    have hcongr : (fun k : ℕ => 1 / (a + (k : ℝ)) ^ (j + 1 + 2))
        = fun k : ℕ => 1 / (a + (k : ℝ)) ^ (j + 3) := by
      funext k; norm_num [show j + 1 + 2 = j + 3 from by omega]
    rw [hcongr] at h
    exact h.mul_left _
  have hsum0 : Summable (fun k : ℕ => 1 / ((a + 1) + (k : ℝ)) ^ (j + 2)) :=
    summable_inv_pow_shift (by linarith : (0 : ℝ) < a + 1) j
  have h := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ => ((j : ℝ) + 2) * (1 / (a + (k : ℝ)) ^ (j + 3)))
    (g := fun k z => 1 / (z + (k : ℝ)) ^ (j + 2))
    (g' := fun k z => -((j : ℝ) + 2) / (z + (k : ℝ)) ^ (j + 3))
    husum isOpen_Ioi isPreconnected_Ioi hderiv hbound
    (mem_Ioi.mpr (by linarith : a < a + 1)) hsum0 (mem_Ioi.mpr hy)
  have hval : (∑' k : ℕ, -((j : ℝ) + 2) / (y + (k : ℝ)) ^ (j + 3))
      = -((j : ℝ) + 2) * ∑' k : ℕ, 1 / (y + (k : ℝ)) ^ (j + 3) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by rw [mul_one_div]
  rwa [hval] at h

/-! ### The iterated derivatives at the low orders -/

theorem iterate_deriv_two_logGamma (x : ℝ) : deriv^[2] logGamma x = trigamma x := by
  simp [Function.iterate_succ_apply', trigamma_def]

theorem iterate_deriv_three_logGamma (x : ℝ) : deriv^[3] logGamma x = tetragamma x := by
  have htri : trigamma = deriv (deriv logGamma) := rfl
  simp [Function.iterate_succ_apply', tetragamma_def, ← htri]

/-! ### The polygamma series -/

/-- **The polygamma series.**  For every `j : ℕ` and every `x > 0`,
`(log Γ)^{(j+2)}(x) = (−1)^j (j+1)! ∑_{k ≥ 0} 1/(x+k)^{j+2}`. -/
theorem polygamma_series (j : ℕ) {x : ℝ} (hx : 0 < x) :
    deriv^[j + 2] logGamma x
      = (-1) ^ j * (Nat.factorial (j + 1) : ℝ) * ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 2) := by
  induction j generalizing x with
  | zero =>
      have h2 : deriv^[0 + 2] logGamma x = deriv (deriv logGamma) x := by
        simp [Function.iterate_succ_apply']
      rw [h2, ← trigamma_def, trigamma_eq_tsum hx]
      norm_num
  | succ j ih =>
      have hstep : deriv^[j + 1 + 2] logGamma x = deriv (deriv^[j + 2] logGamma) x := by
        rw [show j + 1 + 2 = (j + 2) + 1 from by omega, Function.iterate_succ_apply']
      have hEq : (deriv^[j + 2] logGamma)
          =ᶠ[nhds x] fun y : ℝ =>
            (-1) ^ j * (Nat.factorial (j + 1) : ℝ) * ∑' k : ℕ, 1 / (y + (k : ℝ)) ^ (j + 2) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with y hy
        exact ih hy
      have hderiv : HasDerivAt
          (fun y : ℝ => (-1 : ℝ) ^ j * (Nat.factorial (j + 1) : ℝ) * ∑' k : ℕ, 1 / (y + (k : ℝ)) ^ (j + 2))
          ((-1 : ℝ) ^ j * (Nat.factorial (j + 1) : ℝ) *
            (-((j : ℝ) + 2) * ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 3))) x :=
        (hasDerivAt_tsum_inv_pow (a := x / 2) (by linarith) j (by linarith)).const_mul _
      rw [hstep, hEq.deriv_eq, hderiv.deriv]
      have hfac : (Nat.factorial (j + 1 + 1) : ℝ) = (Nat.factorial (j + 1) : ℝ) * ((j : ℝ) + 2) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [show j + 1 + 2 = j + 3 from by omega, hfac]
      ring

/-- The polygamma series in the usual indexing: for `m ≥ 2` and `x > 0`,
`(log Γ)^{(m)}(x) = (−1)^m (m−1)! ∑_{k ≥ 0} 1/(x+k)^m`. -/
theorem polygamma_series_of_two_le {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) :
    deriv^[m] logGamma x
      = (-1) ^ m * (Nat.factorial (m - 1) : ℝ) * ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have h := polygamma_series j hx
  have h1 : (-1 : ℝ) ^ (j + 2) = (-1 : ℝ) ^ j := by
    rw [pow_add]; norm_num
  have h2 : (j + 2 - 1 : ℕ) = j + 1 := by omega
  rw [h1, h2]
  exact h

/-- The sign of the polygamma functions: `(−1)^m (log Γ)^{(m)}(x) > 0` for
`m ≥ 2` and `x > 0`. -/
theorem polygamma_sign {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) :
    0 < (-1) ^ m * deriv^[m] logGamma x := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  rw [polygamma_series j hx]
  have hsum : 0 < ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 2) := by
    refine Summable.tsum_pos (summable_inv_pow_shift hx j) (fun k => ?_) 0 ?_
    · have : (0 : ℝ) < x + k := by positivity
      positivity
    · simp only [Nat.cast_zero, add_zero]
      positivity
  have hsq : (-1 : ℝ) ^ (j + 2) * ((-1) ^ j) = 1 := by
    rw [pow_add]
    norm_num [← pow_add, ← two_mul]
  have hfac : (0 : ℝ) < (Nat.factorial (j + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  calc (0 : ℝ) < (Nat.factorial (j + 1) : ℝ) * ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 2) := by positivity
    _ = (-1) ^ (j + 2) * ((-1) ^ j * (Nat.factorial (j + 1) : ℝ)
          * ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ (j + 2)) := by
        rw [← mul_assoc, ← mul_assoc, hsq]
        ring

/-- The polygamma values at `1` are the zeta values:
`(log Γ)^{(m)}(1) = (−1)^m (m−1)! ζ(m)` for `m ≥ 2`. -/
theorem polygamma_one_eq_zeta {m : ℕ} (hm : 2 ≤ m) :
    deriv^[m] logGamma 1
      = (-1) ^ m * (Nat.factorial (m - 1) : ℝ) * ∑' n : ℕ, 1 / (n : ℝ) ^ m := by
  have h := polygamma_series_of_two_le hm (x := 1) one_pos
  have hzeta : (∑' k : ℕ, 1 / ((1 : ℝ) + (k : ℝ)) ^ m) = ∑' n : ℕ, 1 / (n : ℝ) ^ m := by
    have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ m) :=
      Real.summable_one_div_nat_pow.mpr (by omega)
    rw [hs.tsum_eq_zero_add]
    have hzero : 1 / ((0 : ℕ) : ℝ) ^ m = 0 := by
      simp [zero_pow (by omega : m ≠ 0)]
    rw [hzero, zero_add]
    exact tsum_congr fun n => by push_cast; ring_nf
  rw [h, hzeta]

end SHSLib.Trigamma
