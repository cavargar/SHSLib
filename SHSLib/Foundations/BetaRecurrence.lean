/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The recurrence of the incomplete Beta function in its first parameter

Batch 176 proved the Beta–Binomial identity, which is the *integer* form of the
statement that `I_x(a+1,b)` differs from `I_x(a,b)` by a single explicit term.
This module proves the general real-parameter recurrence

  `I_x(a+1, b) = I_x(a, b) − x^a (1−x)^b / (a · B(a,b))`     for `a, b > 0`, `x ∈ [0,1]`,

equivalently, at the level of the unnormalised function,

  `a · B(x; a, b) − (a+b) · B(x; a+1, b) = x^a (1−x)^b`.

The proof is the fundamental theorem of calculus applied to
`F(t) = t^a (1−t)^b`.  Its derivative on `(0,x)` is
`a · t^{a−1}(1−t)^{b−1} − (a+b) · t^a(1−t)^{b−1}`, and `F` is continuous up to
the endpoint `0` because `a > 0` — even though the derivative itself blows up
there when `a < 1`.  The version of the fundamental theorem that only requires
a one-sided derivative on the open interval handles this.
-/
import SHSLib.Foundations.IncompleteBeta

open Real Set Filter Topology MeasureTheory

namespace SHSLib.Trigamma

/-- The antiderivative `F(t) = t^a (1−t)^b` used in the recurrence. -/
noncomputable def betaAntideriv (a b t : ℝ) : ℝ := t ^ a * (1 - t) ^ b

/-- For positive parameters `F` is continuous on all of `ℝ`; in particular at
the endpoint `0`, where the integrand of the recurrence may blow up. -/
theorem continuous_betaAntideriv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous (betaAntideriv a b) := by
  have h1 : Continuous fun t : ℝ => t ^ a :=
    continuous_iff_continuousAt.mpr fun t => Real.continuousAt_rpow_const t a (Or.inr ha.le)
  have h2 : Continuous fun t : ℝ => (1 - t) ^ b :=
    (continuous_iff_continuousAt.mpr fun t => Real.continuousAt_rpow_const t b (Or.inr hb.le)).comp
      (continuous_const.sub continuous_id)
  exact h1.mul h2

@[simp] theorem betaAntideriv_zero {a b : ℝ} (ha : 0 < a) : betaAntideriv a b 0 = 0 := by
  rw [betaAntideriv, Real.zero_rpow ha.ne', zero_mul]

/-- The derivative of `F(t) = t^a(1−t)^b` on the open interval, expressed
through the Euler integrands with parameters `(a,b)` and `(a+1,b)`. -/
theorem hasDerivAt_betaAntideriv {a b t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (betaAntideriv a b)
      (a * betaIntegrand a b t - (a + b) * betaIntegrand (a + 1) b t) t := by
  have hpos1 : (0:ℝ) < 1 - t := by linarith
  have h1 : HasDerivAt (fun s : ℝ => s ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
  have hinner : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h2' : HasDerivAt (fun s : ℝ => s ^ b) (b * (1 - t) ^ (b - 1)) (1 - t) :=
    Real.hasDerivAt_rpow_const (Or.inl hpos1.ne')
  have h2 : HasDerivAt (fun s : ℝ => (1 - s) ^ b) (b * (1 - t) ^ (b - 1) * (-1)) t :=
    HasDerivAt.comp t h2' hinner
  have h := h1.mul h2
  have e1 : t ^ (a - 1) * t = t ^ a := by
    nth_rewrite 2 [← Real.rpow_one t]
    rw [← Real.rpow_add ht0]
    norm_num
  have e2 : (1 - t) ^ (b - 1) * (1 - t) = (1 - t) ^ b := by
    nth_rewrite 2 [← Real.rpow_one (1 - t)]
    rw [← Real.rpow_add hpos1]
    norm_num
  refine (h.congr_deriv ?_)
  simp only [betaIntegrand, show a + 1 - 1 = a from by ring]
  rw [← e1, ← e2]
  ring

/-- **The unnormalised recurrence**:
`a·B(x;a,b) − (a+b)·B(x;a+1,b) = x^a (1−x)^b`. -/
theorem incompleteBetaFn_recurrence_aux {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    a * incompleteBetaFn a b x - (a + b) * incompleteBetaFn (a + 1) b x
      = x ^ a * (1 - x) ^ b := by
  have ha1 : (0:ℝ) < a + 1 := by linarith
  have hint1 : IntervalIntegrable (betaIntegrand a b) volume 0 x :=
    betaIntegrand_intervalIntegrable_of_mem ha hb le_rfl zero_le_one hx0 hx1
  have hint2 : IntervalIntegrable (betaIntegrand (a + 1) b) volume 0 x :=
    betaIntegrand_intervalIntegrable_of_mem ha1 hb le_rfl zero_le_one hx0 hx1
  have hint : IntervalIntegrable
      (fun t => a * betaIntegrand a b t - (a + b) * betaIntegrand (a + 1) b t) volume 0 x :=
    (hint1.const_mul a).sub (hint2.const_mul (a + b))
  have hcont : ContinuousOn (betaAntideriv a b) (Set.Icc 0 x) :=
    (continuous_betaAntideriv ha hb).continuousOn
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) x, HasDerivWithinAt (betaAntideriv a b)
      (a * betaIntegrand a b t - (a + b) * betaIntegrand (a + 1) b t) (Set.Ioi t) t := by
    intro t ht
    exact (hasDerivAt_betaAntideriv ht.1 (lt_of_lt_of_le ht.2 hx1)).hasDerivWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx0 hcont hderiv hint
  rw [intervalIntegral.integral_sub (hint1.const_mul a) (hint2.const_mul (a + b)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    betaAntideriv_zero ha, sub_zero] at hFTC
  simpa [incompleteBetaFn, betaAntideriv] using hFTC

/-- The recurrence for the incomplete Beta function itself. -/
theorem incompleteBetaFn_recurrence {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    incompleteBetaFn (a + 1) b x
      = (a * incompleteBetaFn a b x - x ^ a * (1 - x) ^ b) / (a + b) := by
  have hab : (0:ℝ) < a + b := by linarith
  rw [eq_div_iff hab.ne']
  linear_combination -incompleteBetaFn_recurrence_aux ha hb hx0 hx1

/-- **The recurrence of the regularised incomplete Beta function in its first
parameter**: `I_x(a+1,b) = I_x(a,b) − x^a(1−x)^b/(a·B(a,b))`. -/
theorem regBetaFn_recurrence {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regBetaFn (a + 1) b x
      = regBetaFn a b x - x ^ a * (1 - x) ^ b / (a * betaFn a b) := by
  have hab : (0:ℝ) < a + b := by linarith
  have hBpos := betaFn_pos ha hb
  simp only [regBetaFn]
  rw [incompleteBetaFn_recurrence ha hb hx0 hx1, betaFn_add_one_left ha hb]
  field_simp

end SHSLib.Trigamma
