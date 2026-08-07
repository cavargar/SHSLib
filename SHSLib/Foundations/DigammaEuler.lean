/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The digamma series in classical form: `ψ(x) = −γ + ∑_{k ≥ 0} (1/(k+1) − 1/(x+k))`

`SHSLib/Foundations/Digamma.lean` proves the digamma series in the `γ`-free
difference form `ψ(x) − ψ(1) = ∑_{k ≥ 0} (1/(k+1) − 1/(x+k))`.  The remaining
constant is identified here: Mathlib's `Real.hasDerivAt_Gamma_one` states
`Γ'(1) = −γ`, and `Γ(1) = 1`, so

  `ψ(1) = Γ'(1)/Γ(1) = −γ`  (`digamma_one`).

That turns every statement of the previous file into its classical form:

* `digamma_series` — `ψ(x) = −γ + ∑_{k ≥ 0} (1/(k+1) − 1/(x+k))` for `x > 0`,
  together with the summability of the series (`summable_digammaTerm`) and the
  corresponding `HasSum` statement (`hasSum_digammaTerm`);
* `digamma_nat_add_one_eq_harmonic` — `ψ(n+1) = −γ + H_n`, with `H_n` Mathlib's
  `harmonic n`;
* `digamma_two`, `digamma_half`, `digamma_nat_add_half` — the values
  `ψ(2) = 1 − γ`, `ψ(1/2) = −γ − 2 log 2` (from Legendre duplication), and
  `ψ(n + 1/2) = −γ − 2 log 2 + ∑_{k<n} 1/(k+1/2)`;
* `tsum_digammaTerm_half` — the resulting closed form
  `∑_{k ≥ 0} (1/(k+1) − 1/(k+1/2)) = −2 log 2`;
* `deriv_Gamma_eq` — `Γ'(x) = Γ(x) ψ(x)` on `(0, ∞)`.
-/
import SHSLib.Foundations.Digamma
import Mathlib.NumberTheory.Harmonic.GammaDeriv

open Real Set Filter

namespace SHSLib.Trigamma

/-! ### The value `ψ(1) = −γ` -/

/-- `Γ'(x) = Γ(x) ψ(x)` for `x > 0`. -/
theorem deriv_Gamma_eq {x : ℝ} (hx : 0 < x) :
    deriv Real.Gamma x = Real.Gamma x * digamma x := by
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hdiff : DifferentiableAt ℝ Real.Gamma x :=
    (contDiffAt_Gamma hx).differentiableAt (by simp)
  have h : HasDerivAt logGamma (deriv Real.Gamma x / Real.Gamma x) x := by
    simpa [logGamma, div_eq_inv_mul] using hdiff.hasDerivAt.log hpos.ne'
  rw [digamma_def, h.deriv]
  field_simp

/-- **`ψ(1) = −γ`**, the Euler–Mascheroni constant with a minus sign. -/
theorem digamma_one : digamma 1 = -Real.eulerMascheroniConstant := by
  have hG : Real.Gamma 1 = 1 := Real.Gamma_one
  have hd : HasDerivAt Real.Gamma (-Real.eulerMascheroniConstant) 1 := Real.hasDerivAt_Gamma_one
  have h : HasDerivAt logGamma ((-Real.eulerMascheroniConstant) / Real.Gamma 1) 1 := by
    simpa [logGamma, div_eq_inv_mul] using hd.log (by rw [hG]; norm_num)
  rw [digamma_def, h.deriv, hG, div_one]

/-! ### The classical digamma series -/

/-- **The digamma series.**  For every `x > 0`,
`ψ(x) = −γ + ∑_{k ≥ 0} (1/(k+1) − 1/(x+k))`. -/
theorem digamma_series {x : ℝ} (hx : 0 < x) :
    digamma x
      = -Real.eulerMascheroniConstant + ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / (x + k)) := by
  have h := digamma_sub_digamma_one hx
  rw [digamma_one] at h
  linarith

/-- The digamma series is summable: its `k`-th term is `(x−1)/((k+1)(x+k))`, of
size `O(1/k²)`. -/
theorem summable_digammaTerm {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / (x + k)) := by
  set c : ℝ := min x 1 with hc_def
  have hc : 0 < c := lt_min hx one_pos
  have hsq : Summable (fun k : ℕ => |x - 1| / c * (1 / ((1 : ℝ) + k) ^ 2)) :=
    (summable_inv_sq_shift one_pos).mul_left _
  refine hsq.of_norm_bounded ?_
  intro k
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < x + k := by positivity
  have hlow : c * ((k : ℝ) + 1) ≤ x + k := by
    rcases le_total x 1 with hx1 | hx1
    · have : c = x := by rw [hc_def, min_eq_left hx1]
      rw [this]
      nlinarith
    · have : c = 1 := by rw [hc_def, min_eq_right hx1]
      rw [this]; linarith
  have hval : 1 / ((k : ℝ) + 1) - 1 / (x + k) = (x - 1) / (((k : ℝ) + 1) * (x + k)) := by
    field_simp
    ring
  rw [hval, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < ((k:ℝ)+1) * (x+k))]
  rw [div_le_iff₀ (by positivity)]
  have hprod : c * ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * (x + k) := by
    have := mul_le_mul_of_nonneg_left hlow (le_of_lt h1)
    calc c * ((k : ℝ) + 1) ^ 2 = ((k : ℝ) + 1) * (c * ((k : ℝ) + 1)) := by ring
      _ ≤ ((k : ℝ) + 1) * (x + k) := this
  have hshift : ((1 : ℝ) + k) ^ 2 = ((k : ℝ) + 1) ^ 2 := by ring
  rw [hshift]
  have hnn : (0 : ℝ) ≤ |x - 1| / c * (1 / ((k : ℝ) + 1) ^ 2) := by positivity
  calc |x - 1|
      = |x - 1| / c * (1 / ((k : ℝ) + 1) ^ 2) * (c * ((k : ℝ) + 1) ^ 2) := by field_simp
    _ ≤ |x - 1| / c * (1 / ((k : ℝ) + 1) ^ 2) * (((k : ℝ) + 1) * (x + k)) :=
        mul_le_mul_of_nonneg_left hprod hnn

/-- The `HasSum` form of the digamma series. -/
theorem hasSum_digammaTerm {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / (x + k))
      (digamma x + Real.eulerMascheroniConstant) := by
  have h := (summable_digammaTerm hx).hasSum
  have he : (∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / (x + k)))
      = digamma x + Real.eulerMascheroniConstant := by
    rw [digamma_series hx]; ring
  rwa [he] at h

/-! ### Special values -/

/-- `ψ(2) = 1 − γ`. -/
theorem digamma_two : digamma 2 = 1 - Real.eulerMascheroniConstant := by
  have h := digamma_recurrence (x := 1) one_pos
  norm_num at h
  rw [h, digamma_one]
  ring

/-- `ψ(1/2) = −γ − 2 log 2`, from Legendre's duplication formula at `x = 1/2`. -/
theorem digamma_half :
    digamma (1 / 2) = -Real.eulerMascheroniConstant - 2 * Real.log 2 := by
  have h := duplication_deriv (x := 1 / 2) (by norm_num)
  norm_num at h
  have h1 : digamma (1 / 2) = deriv logGamma (1 / 2) := rfl
  have h2 : digamma 1 = deriv logGamma 1 := rfl
  rw [h1]
  rw [digamma_one] at h2
  norm_num at h ⊢
  linarith [h, h2]

/-- `ψ(n + 1/2) = −γ − 2 log 2 + ∑_{k<n} 1/(k+1/2)`. -/
theorem digamma_nat_add_half (n : ℕ) :
    digamma ((n : ℝ) + 1 / 2)
      = -Real.eulerMascheroniConstant - 2 * Real.log 2
        + ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1 / 2) := by
  induction n with
  | zero => simpa using digamma_half
  | succ n ih =>
      have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
      have h := digamma_recurrence hpos
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 := by push_cast; ring
      rw [hcast, h, ih, Finset.sum_range_succ]
      ring

/-- `ψ(n+1) = −γ + H_n`, with `H_n` the `n`-th harmonic number. -/
theorem digamma_nat_add_one_eq_harmonic (n : ℕ) :
    digamma ((n : ℝ) + 1) = -Real.eulerMascheroniConstant + (harmonic n : ℚ) := by
  have h := digamma_nat_add_one n
  rw [digamma_one] at h
  rw [h]
  congr 1
  rw [harmonic]
  push_cast
  simp [one_div]

/-! ### A closed form for the series at `1/2` -/

/-- `∑_{k ≥ 0} (1/(k+1) − 1/(k+1/2)) = −2 log 2`. -/
theorem tsum_digammaTerm_half :
    (∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / (1 / 2 + k))) = -(2 * Real.log 2) := by
  have h := digamma_series (x := 1 / 2) (by norm_num)
  rw [digamma_half] at h
  linarith

end SHSLib.Trigamma
