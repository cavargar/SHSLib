/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Γ` at the half-integers, and the ratio `Γ(n + ½)/Γ(n + 1)`

The closed form

  `Γ(n + ½) = (2n)! √π / (4ⁿ n!)`

follows from `Γ(½) = √π` by induction on `n`.  Dividing by `Γ(n+1) = n!` turns
it into

  `Γ(n + ½) / Γ(n + 1) = C(2n, n) √π / 4ⁿ`,

so the central binomial bracket of batch 158 gives, for every `n ≥ 1`, the
two-sided estimate

  `e^{−1/(7n)} / √n < Γ(n + ½)/Γ(n + 1) < 1/√n`,

and hence `√n · Γ(n + ½)/Γ(n + 1) → 1` with an explicit rate.
-/
import SHSLib.Foundations.StirlingCentralBinom

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### The closed form at half-integers -/

/-- **`Γ(n + ½) = (2n)! √π / (4ⁿ n!)`** for every natural `n`. -/
theorem gamma_nat_add_half (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2)
      = (Nat.factorial (2 * n) : ℝ) * Real.sqrt π / (4 ^ n * Nat.factorial n) := by
  induction n with
  | zero => simpa using Real.Gamma_one_half_eq
  | succ n ih =>
      have hne : ((n : ℝ) + 1 / 2) ≠ 0 := by positivity
      have hstep : Real.Gamma (((n : ℕ) : ℝ) + 1 / 2 + 1)
          = ((n : ℝ) + 1 / 2) * Real.Gamma ((n : ℝ) + 1 / 2) := Real.Gamma_add_one hne
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 := by push_cast; ring
      have hfac : Nat.factorial (2 * (n + 1))
          = (2 * n + 2) * ((2 * n + 1) * Nat.factorial (2 * n)) := by
        have h : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
        rw [h, Nat.factorial_succ, Nat.factorial_succ]
      have hfacR : (Nat.factorial (2 * (n + 1)) : ℝ)
          = (2 * (n : ℝ) + 2) * ((2 * (n : ℝ) + 1) * (Nat.factorial (2 * n) : ℝ)) := by
        rw [hfac]; push_cast; ring
      have hfacn : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
      rw [hcast, hstep, ih, hfacR, hfacn]
      field_simp
      ring

/-- `Γ(n + ½) / Γ(n + 1) = C(2n, n) √π / 4ⁿ`. -/
theorem gamma_half_ratio_eq (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma ((n : ℝ) + 1)
      = (Nat.centralBinom n : ℝ) * Real.sqrt π / 4 ^ n := by
  have hfacpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hGamma : Real.Gamma ((n : ℝ) + 1) = (Nat.factorial n : ℝ) := by
    exact_mod_cast Real.Gamma_nat_eq_factorial n
  have hchoose : (Nat.centralBinom n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)
      = (Nat.factorial (2 * n) : ℝ) := by
    have h : Nat.centralBinom n * Nat.factorial n * Nat.factorial n = Nat.factorial (2 * n) := by
      have h := Nat.choose_mul_factorial_mul_factorial
        (Nat.le_mul_of_pos_left n (by norm_num) : n ≤ 2 * n)
      simpa [Nat.centralBinom, two_mul, Nat.add_sub_cancel] using h
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  rw [gamma_nat_add_half n, hGamma, ← hchoose]
  field_simp

/-! ### The bracket and the limit -/

/-- **Two-sided bound on `Γ(n + ½)/Γ(n + 1)`**:
`e^{−1/(7n)}/√n < Γ(n + ½)/Γ(n + 1) < 1/√n` for every `n ≥ 1`. -/
theorem gamma_half_ratio_bracket {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(1 / (7 * (n : ℝ)))) / Real.sqrt (n : ℝ)
        < Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma ((n : ℝ) + 1) ∧
      Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma ((n : ℝ) + 1) < 1 / Real.sqrt (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsp : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hpow : (0 : ℝ) < 4 ^ n := by positivity
  have hsplit : Real.sqrt (π * n) = Real.sqrt π * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul Real.pi_pos.le _
  obtain ⟨h1, h2⟩ := centralBinom_lt_and_gt hn
  rw [hsplit] at h1 h2
  rw [gamma_half_ratio_eq n]
  constructor
  · rw [div_lt_div_iff₀ hsn hpow]
    have h1' := mul_lt_mul_of_pos_right h1 (mul_pos hsp hsn)
    have hsimp : 4 ^ n / (Real.sqrt π * Real.sqrt (n : ℝ)) * Real.exp (-(1 / (7 * (n : ℝ))))
        * (Real.sqrt π * Real.sqrt (n : ℝ))
        = Real.exp (-(1 / (7 * (n : ℝ)))) * 4 ^ n := by
      field_simp
    rw [hsimp] at h1'
    nlinarith [h1', hsn, hsp]
  · rw [div_lt_div_iff₀ hpow hsn]
    have h2' := mul_lt_mul_of_pos_right h2 (mul_pos hsp hsn)
    have hsimp : 4 ^ n / (Real.sqrt π * Real.sqrt (n : ℝ)) * (Real.sqrt π * Real.sqrt (n : ℝ))
        = 4 ^ n := by
      field_simp
    rw [hsimp] at h2'
    nlinarith [h2', hsn, hsp]

/-- **`√n · Γ(n + ½)/Γ(n + 1) → 1`.** -/
theorem tendsto_sqrt_mul_gamma_half_ratio :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)
      * (Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma ((n : ℝ) + 1))) atTop (𝓝 1) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(1 / (7 * (n : ℝ))))) atTop (𝓝 1) := by
    have hnat : Tendsto (fun n : ℕ => 7 * (n : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => 1 / (7 * (n : ℝ))) atTop (𝓝 0) := by
      have h := tendsto_inv_atTop_zero.comp hnat
      simpa [Function.comp_def, one_div] using h
    have hneg : Tendsto (fun n : ℕ => -(1 / (7 * (n : ℝ)))) atTop (𝓝 0) := by
      simpa using hinv.neg
    simpa using (Real.continuous_exp.tendsto 0).comp hneg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hexp tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    obtain ⟨h1, -⟩ := gamma_half_ratio_bracket hn
    have := mul_lt_mul_of_pos_left h1 hsn
    rw [show Real.sqrt (n : ℝ) * (Real.exp (-(1 / (7 * (n : ℝ)))) / Real.sqrt (n : ℝ))
      = Real.exp (-(1 / (7 * (n : ℝ)))) by field_simp] at this
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    obtain ⟨-, h2⟩ := gamma_half_ratio_bracket hn
    have := mul_lt_mul_of_pos_left h2 hsn
    rw [show Real.sqrt (n : ℝ) * (1 / Real.sqrt (n : ℝ)) = 1 by field_simp] at this
    linarith

end SHSLib.Trigamma
