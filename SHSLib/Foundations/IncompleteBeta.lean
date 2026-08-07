/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The incomplete Beta function and the Beta cumulative distribution function

The **incomplete Beta function** is the partial Euler integral

  `B(x; a, b) = ∫₀ˣ t^{a−1}(1−t)^{b−1} dt`,

and its normalisation `I_x(a,b) = B(x; a, b)/B(a,b)` — the **regularised**
incomplete Beta function — is exactly the cumulative distribution function of
the Beta law of batch 171.

This module proves the basic facts:

* the Euler integrand is interval-integrable on `[0,1]` for `a, b > 0`
  (integrable at both endpoints, by splitting the interval at `½`);
* `I_0(a,b) = 0` and `I_1(a,b) = 1`;
* `I` is monotone in `x` and takes values in `[0,1]`;
* the complementation identity `B(x; a,b) + B(1−x; b,a) = B(a,b)`, i.e.
  `I_x(a,b) = 1 − I_{1−x}(b,a)`, obtained from the substitution `t ↦ 1 − t`;
* the median of the symmetric Beta law: `I_{1/2}(a,a) = ½`.
-/
import SHSLib.Foundations.BetaDistribution

open Real Set Filter Topology MeasureTheory

namespace SHSLib.Trigamma

/-- The Euler integrand `t^{a−1}(1−t)^{b−1}` of the Beta integral. -/
noncomputable def betaIntegrand (a b t : ℝ) : ℝ := t ^ (a - 1) * (1 - t) ^ (b - 1)

/-- On `[0, ½]` the factor `(1−t)^{b−1}` is continuous. -/
theorem continuousOn_one_sub_rpow_left {b : ℝ} :
    ContinuousOn (fun t : ℝ => (1 - t) ^ (b - 1)) (Set.uIcc (0:ℝ) (1/2)) := by
  refine ContinuousOn.rpow_const (by fun_prop) ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at ht
  exact Or.inl (by simp only [ne_eq, sub_eq_zero]; intro h; linarith [ht.2, h.symm])

/-- On `[½, 1]` the factor `t^{a−1}` is continuous. -/
theorem continuousOn_rpow_right {a : ℝ} :
    ContinuousOn (fun t : ℝ => t ^ (a - 1)) (Set.uIcc (1/2 : ℝ) 1) := by
  refine ContinuousOn.rpow_const (by fun_prop) ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
  exact Or.inl (by intro h; rw [h] at ht; linarith [ht.1])

/-- **Integrability of the Euler integrand** on `[0,1]` for `a, b > 0`. -/
theorem betaIntegrand_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (betaIntegrand a b) volume 0 1 := by
  have hleft : IntervalIntegrable (betaIntegrand a b) volume 0 (1/2) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < a - 1)).mul_continuousOn
      continuousOn_one_sub_rpow_left
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ (b - 1)) volume 0 (1/2) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < b - 1)
  have hsub : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (b - 1)) volume (1/2) 1 := by
    have := hbase.comp_sub_left 1
    norm_num at this
    exact this.symm
  have hright : IntervalIntegrable (betaIntegrand a b) volume (1/2) 1 := by
    have := hsub.continuousOn_mul (continuousOn_rpow_right (a := a))
    simpa [betaIntegrand, mul_comm] using this
  exact hleft.trans hright

/-- Integrability of the Euler integrand on any subinterval of `[0,1]`. -/
theorem betaIntegrand_intervalIntegrable_of_mem {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u v : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    IntervalIntegrable (betaIntegrand a b) volume u v := by
  refine (betaIntegrand_intervalIntegrable ha hb).mono_set ?_
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact Set.uIcc_subset_Icc ⟨hu, hu1⟩ ⟨hv, hv1⟩

/-- The **incomplete Beta function** `B(x; a, b) = ∫₀ˣ t^{a−1}(1−t)^{b−1} dt`. -/
noncomputable def incompleteBetaFn (a b x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, betaIntegrand a b t

/-- The **regularised incomplete Beta function** `I_x(a,b) = B(x;a,b)/B(a,b)`,
the cumulative distribution function of the Beta law with parameters `a, b`. -/
noncomputable def regBetaFn (a b x : ℝ) : ℝ := incompleteBetaFn a b x / betaFn a b

@[simp] theorem incompleteBetaFn_zero (a b : ℝ) : incompleteBetaFn a b 0 = 0 := by
  simp [incompleteBetaFn]

/-- At `x = 1` the incomplete Beta function is the complete one. -/
theorem incompleteBetaFn_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    incompleteBetaFn a b 1 = betaFn a b :=
  (betaFn_eq_integral ha hb).symm

@[simp] theorem regBetaFn_zero (a b : ℝ) : regBetaFn a b 0 = 0 := by simp [regBetaFn]

/-- `I_1(a,b) = 1`: the Beta density is normalised. -/
theorem regBetaFn_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : regBetaFn a b 1 = 1 := by
  rw [regBetaFn, incompleteBetaFn_one ha hb, div_self (betaFn_pos ha hb).ne']

/-- The incomplete Beta function is monotone on `[0,1]`. -/
theorem incompleteBetaFn_mono {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    incompleteBetaFn a b x ≤ incompleteBetaFn a b y := by
  have hx1 : x ≤ 1 := le_trans hxy hy
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hadd : incompleteBetaFn a b x + (∫ t in x..y, betaIntegrand a b t)
      = incompleteBetaFn a b y :=
    intervalIntegral.integral_add_adjacent_intervals
      (betaIntegrand_intervalIntegrable_of_mem ha hb le_rfl zero_le_one hx hx1)
      (betaIntegrand_intervalIntegrable_of_mem ha hb hx hx1 hy0 hy)
  have hnn : 0 ≤ ∫ t in x..y, betaIntegrand a b t := by
    refine intervalIntegral.integral_nonneg hxy ?_
    intro t ht
    have ht0 : 0 ≤ t := le_trans hx ht.1
    have ht1 : t ≤ 1 := le_trans ht.2 hy
    exact mul_nonneg (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg (by linarith) _)
  linarith

/-- The regularised incomplete Beta function is monotone on `[0,1]`. -/
theorem regBetaFn_mono {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    regBetaFn a b x ≤ regBetaFn a b y := by
  have hB := betaFn_pos ha hb
  unfold regBetaFn
  gcongr
  exact incompleteBetaFn_mono ha hb hx hxy hy

/-- `0 ≤ I_x(a,b) ≤ 1` for `x ∈ [0,1]`. -/
theorem regBetaFn_mem_Icc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : regBetaFn a b x ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · simpa using regBetaFn_mono ha hb (le_refl (0:ℝ)) hx hx1
  · simpa [regBetaFn_one ha hb] using regBetaFn_mono ha hb hx hx1 (le_refl (1:ℝ))

/-- **Complementation**: `B(x; a, b) + B(1−x; b, a) = B(a,b)`.  The substitution
`t ↦ 1 − t` turns the tail `∫ₓ¹ t^{a−1}(1−t)^{b−1}` into the head
`∫₀^{1−x} t^{b−1}(1−t)^{a−1}`. -/
theorem incompleteBetaFn_add_symm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    incompleteBetaFn a b x + incompleteBetaFn b a (1 - x) = betaFn a b := by
  have htail : (∫ t in x..1, betaIntegrand a b t) = incompleteBetaFn b a (1 - x) := by
    have hsub : (∫ t in x..1, betaIntegrand b a (1 - t))
        = ∫ t in (1 - 1)..(1 - x), betaIntegrand b a t :=
      intervalIntegral.integral_comp_sub_left (f := betaIntegrand b a) 1
    have hcongr : (∫ t in x..1, betaIntegrand a b t)
        = ∫ t in x..1, betaIntegrand b a (1 - t) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp [betaIntegrand, mul_comm]
    rw [hcongr, hsub]
    norm_num [incompleteBetaFn]
  have hadd : incompleteBetaFn a b x + (∫ t in x..1, betaIntegrand a b t)
      = incompleteBetaFn a b 1 :=
    intervalIntegral.integral_add_adjacent_intervals
      (betaIntegrand_intervalIntegrable_of_mem ha hb le_rfl zero_le_one hx hx1)
      (betaIntegrand_intervalIntegrable_of_mem ha hb hx hx1 zero_le_one le_rfl)
  rw [htail] at hadd
  rw [hadd, incompleteBetaFn_one ha hb]

/-- **The reflection formula for the Beta CDF**: `I_x(a,b) = 1 − I_{1−x}(b,a)`. -/
theorem regBetaFn_symm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    regBetaFn a b x = 1 - regBetaFn b a (1 - x) := by
  have hB : betaFn a b ≠ 0 := (betaFn_pos ha hb).ne'
  have hsymm : betaFn b a = betaFn a b := betaFn_symm b a
  have h := incompleteBetaFn_add_symm ha hb hx hx1
  rw [regBetaFn, regBetaFn, hsymm, eq_sub_iff_add_eq, ← add_div, h,
    div_self hB]

/-- **The median of the symmetric Beta law**: `I_{1/2}(a,a) = ½`. -/
theorem regBetaFn_half_self {a : ℝ} (ha : 0 < a) : regBetaFn a a (1/2) = 1/2 := by
  have h := regBetaFn_symm ha ha (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
  norm_num at h
  linarith

end SHSLib.Trigamma
