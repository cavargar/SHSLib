/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Beta distribution: density, normalisation and moments

Euler's integral of the first kind (batch 168) says that for `a, b > 0`

  `B(a,b) = ∫₀¹ t^{a−1}(1−t)^{b−1} dt`,

so `t ↦ t^{a−1}(1−t)^{b−1}/B(a,b)` is a probability density on `(0,1)`: the
**Beta density** `betaPDF a b`.  This module records

* nonnegativity of the density on `[0,1]`;
* the normalisation `∫₀¹ betaPDF a b = 1`;
* the raw moments in the general form
  `∫₀¹ t^s · betaPDF a b t dt = B(a+s, b)/B(a,b)` for every `s ≥ 0`;
* the shift `B(a+1, b) = B(a,b)·a/(a+b)`, which turns the moment formula into
  the classical closed forms

    mean `a/(a+b)`,  second moment `a(a+1)/((a+b)(a+b+1))`,
    variance `ab/((a+b)²(a+b+1))`,

  and, by induction on `k`, the general integer moment
  `E[X^k] = ∏_{i<k} (a+i)/(a+b+i)`.

The Beta law is the standard model for a division ratio in the cell-size
models of this library, where `X ∈ (0,1)` is the fraction of the mother cell
inherited by a daughter; the mean and variance computed here are exactly the
first two summary statistics used there.
-/
import SHSLib.Foundations.StirlingBetaIntegral

open Real Set Filter Topology MeasureTheory

namespace SHSLib.Trigamma

/-- The **Beta density** with shape parameters `a, b`:
`betaPDF a b t = t^{a−1}(1−t)^{b−1}/B(a,b)`.  It is a probability density on
`(0,1)`; outside `[0,1]` the formula is not used. -/
noncomputable def betaPDF (a b t : ℝ) : ℝ :=
  t ^ (a - 1) * (1 - t) ^ (b - 1) / betaFn a b

/-- The Beta density is nonnegative on `[0,1]`. -/
theorem betaPDF_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ betaPDF a b t := by
  have hB := betaFn_pos ha hb
  have h1 : 0 ≤ t ^ (a - 1) := Real.rpow_nonneg ht0 _
  have h2 : 0 ≤ (1 - t) ^ (b - 1) := Real.rpow_nonneg (by linarith) _
  exact div_nonneg (mul_nonneg h1 h2) hB.le

/-- **The general raw moment of the Beta density**: for `a, b > 0` and `s ≥ 0`,
`∫₀¹ t^s · betaPDF a b t dt = B(a+s, b)/B(a,b)`. -/
theorem integral_rpow_mul_betaPDF {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) :
    (∫ t in (0:ℝ)..1, t ^ s * betaPDF a b t) = betaFn (a + s) b / betaFn a b := by
  have has : 0 < a + s := by linarith
  have hshift : (∫ t in (0:ℝ)..1, t ^ s * (t ^ (a - 1) * (1 - t) ^ (b - 1)))
      = ∫ t in (0:ℝ)..1, t ^ (a + s - 1) * (1 - t) ^ (b - 1) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have htpos : 0 < t := ht.1
    rw [← mul_assoc, ← Real.rpow_add htpos]
    ring_nf
  calc (∫ t in (0:ℝ)..1, t ^ s * betaPDF a b t)
      = (∫ t in (0:ℝ)..1, t ^ s * (t ^ (a - 1) * (1 - t) ^ (b - 1))) / betaFn a b := by
        rw [← intervalIntegral.integral_div]
        exact intervalIntegral.integral_congr (fun t _ => by
          simp [betaPDF, mul_div_assoc])
    _ = (∫ t in (0:ℝ)..1, t ^ (a + s - 1) * (1 - t) ^ (b - 1)) / betaFn a b := by rw [hshift]
    _ = betaFn (a + s) b / betaFn a b := by rw [← betaFn_eq_integral has hb]

/-- **Normalisation**: the Beta density integrates to `1` over `(0,1)`. -/
theorem integral_betaPDF {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0:ℝ)..1, betaPDF a b t) = 1 := by
  have h := integral_rpow_mul_betaPDF ha hb (le_refl (0:ℝ))
  rw [add_zero, div_self (betaFn_pos ha hb).ne'] at h
  have hcong : (∫ t in (0:ℝ)..1, betaPDF a b t)
      = ∫ t in (0:ℝ)..1, t ^ (0:ℝ) * betaPDF a b t :=
    intervalIntegral.integral_congr (fun t _ => by rw [Real.rpow_zero, one_mul])
  rw [hcong, h]

/-- The shift in the **first** argument: `B(a+1, b) = B(a,b)·a/(a+b)`. -/
theorem betaFn_add_one_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaFn (a + 1) b = betaFn a b * (a / (a + b)) := by
  rw [betaFn_symm (a + 1) b, betaFn_add_one_right hb ha, betaFn_symm b a, add_comm b a]

/-- The ratio form of the shift: `B(a+1, b)/B(a,b) = a/(a+b)`. -/
theorem betaFn_add_one_left_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaFn (a + 1) b / betaFn a b = a / (a + b) := by
  rw [betaFn_add_one_left ha hb, mul_comm, mul_div_assoc, div_self (betaFn_pos ha hb).ne',
    mul_one]

/-- **The mean of the Beta distribution**: `E[X] = a/(a+b)`. -/
theorem betaPDF_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0:ℝ)..1, t * betaPDF a b t) = a / (a + b) := by
  have h := integral_rpow_mul_betaPDF ha hb (zero_le_one' ℝ)
  rw [betaFn_add_one_left_div ha hb] at h
  rw [← h]
  exact intervalIntegral.integral_congr (fun t _ => by rw [Real.rpow_one])

/-- **The second raw moment of the Beta distribution**:
`E[X²] = a(a+1)/((a+b)(a+b+1))`. -/
theorem betaPDF_second_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0:ℝ)..1, t ^ (2 : ℕ) * betaPDF a b t)
      = a * (a + 1) / ((a + b) * (a + b + 1)) := by
  have ha1 : (0:ℝ) < a + 1 := by linarith
  have hab : (0:ℝ) < a + b := by linarith
  have hab1 : (0:ℝ) < a + 1 + b := by linarith
  have hB : betaFn a b ≠ 0 := (betaFn_pos ha hb).ne'
  have hcong : (∫ t in (0:ℝ)..1, t ^ (2 : ℕ) * betaPDF a b t)
      = ∫ t in (0:ℝ)..1, t ^ (2 : ℝ) * betaPDF a b t := by
    refine (intervalIntegral.integral_congr (fun t _ => ?_)).symm
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hstep : betaFn (a + 2) b = betaFn a b * (a / (a + b)) * ((a + 1) / (a + 1 + b)) := by
    rw [show a + 2 = (a + 1) + 1 by ring, betaFn_add_one_left ha1 hb, betaFn_add_one_left ha hb]
  rw [hcong, integral_rpow_mul_betaPDF ha hb (by norm_num : (0:ℝ) ≤ 2), hstep]
  field_simp
  ring

/-- The iterated shift in the first argument, in ratio form:
`B(a+k, b)/B(a,b) = ∏_{i<k} (a+i)/(a+b+i)`. -/
theorem betaFn_add_nat_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    betaFn (a + k) b / betaFn a b = ∏ i ∈ Finset.range k, (a + i) / (a + b + i) := by
  induction k with
  | zero => simp [div_self (betaFn_pos ha hb).ne']
  | succ k ih =>
    have hak : (0:ℝ) < a + k := by positivity
    have hstep : betaFn (a + (k + 1 : ℕ)) b = betaFn (a + k) b * ((a + k) / (a + k + b)) := by
      rw [show a + ((k + 1 : ℕ) : ℝ) = (a + k) + 1 by push_cast; ring,
        betaFn_add_one_left hak hb]
    rw [hstep, Finset.prod_range_succ, ← ih, show a + k + b = a + b + k by ring]
    ring

/-- **The integer moments of the Beta distribution**:
`E[X^k] = ∏_{i<k} (a+i)/(a+b+i)`. -/
theorem betaPDF_moment_nat {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    (∫ t in (0:ℝ)..1, t ^ k * betaPDF a b t)
      = ∏ i ∈ Finset.range k, (a + i) / (a + b + i) := by
  have hcong : (∫ t in (0:ℝ)..1, t ^ k * betaPDF a b t)
      = ∫ t in (0:ℝ)..1, t ^ ((k : ℕ) : ℝ) * betaPDF a b t :=
    (intervalIntegral.integral_congr (fun t _ => by rw [Real.rpow_natCast])).symm
  rw [hcong, integral_rpow_mul_betaPDF ha hb (by positivity : (0:ℝ) ≤ (k : ℝ)),
    betaFn_add_nat_div ha hb k]

/-- **The variance of the Beta distribution**: `Var[X] = ab/((a+b)²(a+b+1))`. -/
theorem betaPDF_variance {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0:ℝ)..1, t ^ (2 : ℕ) * betaPDF a b t)
        - (∫ t in (0:ℝ)..1, t * betaPDF a b t) ^ 2
      = a * b / ((a + b) ^ 2 * (a + b + 1)) := by
  have hab : (0:ℝ) < a + b := by linarith
  have hab1 : (0:ℝ) < a + b + 1 := by linarith
  rw [betaPDF_second_moment ha hb, betaPDF_mean ha hb]
  field_simp
  ring

end SHSLib.Trigamma
