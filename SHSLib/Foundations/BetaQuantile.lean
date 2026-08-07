/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regularity of the Beta CDF and the Beta quantile function

The regularised incomplete Beta function `I_x(a,b)` of batch 172 is shown here
to be a *bona fide* continuous, strictly increasing bijection of `[0,1]` onto
itself whose derivative is the Beta density of batch 171:

* `betaIntegrand a b` is continuous at every interior point of `(0,1)`;
* `x ↦ B(x; a, b)` is continuous on `[0,1]` and differentiable on `(0,1)` with
  derivative the Euler integrand (fundamental theorem of calculus), hence
  `I` is differentiable with derivative the Beta density `betaPDF a b`;
* `I` is strictly increasing on `[0,1]`, because the integrand is strictly
  positive on the open interval;
* consequently, for every level `p ∈ [0,1]` there is a **unique** `x ∈ [0,1]`
  with `I_x(a,b) = p` — the Beta quantile.  This is the object needed to
  generate Beta-distributed random variables by inverse transform, in the
  style of the clock-noise modules of `SHSLib/Core/`.
-/
import SHSLib.Foundations.IncompleteBeta

open Real Set Filter Topology MeasureTheory

namespace SHSLib.Trigamma

/-- The Euler integrand is continuous at every interior point of `(0,1)`. -/
theorem continuousAt_betaIntegrand {a b x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ContinuousAt (betaIntegrand a b) x := by
  have h1 : ContinuousAt (fun t : ℝ => t ^ (a - 1)) x :=
    ContinuousAt.rpow_const continuousAt_id (Or.inl hx0.ne')
  have h2 : ContinuousAt (fun t : ℝ => (1 - t) ^ (b - 1)) x := by
    refine ContinuousAt.rpow_const (by fun_prop) (Or.inl ?_)
    simp only [ne_eq, sub_eq_zero]
    intro h
    linarith [h.symm ▸ hx1]
  exact h1.mul h2

/-- The Euler integrand is continuous on the open interval `(0,1)`. -/
theorem continuousOn_betaIntegrand_Ioo {a b : ℝ} :
    ContinuousOn (betaIntegrand a b) (Set.Ioo (0:ℝ) 1) :=
  fun _ hx => (continuousAt_betaIntegrand hx.1 hx.2).continuousWithinAt

/-- **Fundamental theorem of calculus for the incomplete Beta function**: on the
open interval, `x ↦ B(x; a, b)` is differentiable with derivative the Euler
integrand. -/
theorem incompleteBetaFn_hasDerivAt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (incompleteBetaFn a b) (betaIntegrand a b x) x := by
  have hint : IntervalIntegrable (betaIntegrand a b) volume 0 x :=
    betaIntegrand_intervalIntegrable_of_mem ha hb le_rfl zero_le_one hx0.le hx1.le
  have hmeas : StronglyMeasurableAtFilter (betaIntegrand a b) (𝓝 x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo continuousOn_betaIntegrand_Ioo x
      ⟨hx0, hx1⟩
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas
    (continuousAt_betaIntegrand hx0 hx1)

/-- **The Beta CDF has the Beta density as its derivative** on `(0,1)`. -/
theorem regBetaFn_hasDerivAt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (regBetaFn a b) (betaPDF a b x) x := by
  have h := (incompleteBetaFn_hasDerivAt ha hb hx0 hx1).div_const (betaFn a b)
  simpa [regBetaFn, betaPDF, betaIntegrand] using h

/-- The incomplete Beta function is continuous on `[0,1]`. -/
theorem continuousOn_incompleteBetaFn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (incompleteBetaFn a b) (Set.Icc (0:ℝ) 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (betaIntegrand_intervalIntegrable ha hb) (a := 0) (by simp)
  rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h

/-- The Beta CDF is continuous on `[0,1]`. -/
theorem continuousOn_regBetaFn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (regBetaFn a b) (Set.Icc (0:ℝ) 1) :=
  (continuousOn_incompleteBetaFn ha hb).div_const _

/-- The Euler integrand is strictly positive on `(0,1)`. -/
theorem betaIntegrand_pos {a b t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < betaIntegrand a b t :=
  mul_pos (Real.rpow_pos_of_pos ht0 _) (Real.rpow_pos_of_pos (by linarith) _)

/-- The incomplete Beta function is **strictly** increasing on `[0,1]`. -/
theorem incompleteBetaFn_strictMonoOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (incompleteBetaFn a b) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hadd : incompleteBetaFn a b x + (∫ t in x..y, betaIntegrand a b t)
      = incompleteBetaFn a b y :=
    intervalIntegral.integral_add_adjacent_intervals
      (betaIntegrand_intervalIntegrable_of_mem ha hb le_rfl zero_le_one hx.1 hx.2)
      (betaIntegrand_intervalIntegrable_of_mem ha hb hx.1 hx.2 hy.1 hy.2)
  have hpos : 0 < ∫ t in x..y, betaIntegrand a b t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (betaIntegrand_intervalIntegrable_of_mem ha hb hx.1 hx.2 hy.1 hy.2) ?_ hxy
    intro t ht
    exact betaIntegrand_pos (lt_of_le_of_lt hx.1 ht.1) (lt_of_lt_of_le ht.2 hy.2)
  linarith

/-- The Beta CDF is **strictly** increasing on `[0,1]`. -/
theorem regBetaFn_strictMonoOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (regBetaFn a b) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hB := betaFn_pos ha hb
  unfold regBetaFn
  gcongr
  exact incompleteBetaFn_strictMonoOn ha hb hx hy hxy

/-- **The Beta quantile exists and is unique.** For every level `p ∈ [0,1]`
there is exactly one `x ∈ [0,1]` with `I_x(a,b) = p`. -/
theorem existsUnique_regBetaFn_eq {a b p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃! x : ℝ, x ∈ Set.Icc (0:ℝ) 1 ∧ regBetaFn a b x = p := by
  have hsub : Set.Icc (regBetaFn a b 0) (regBetaFn a b 1)
      ⊆ regBetaFn a b '' Set.Icc (0:ℝ) 1 :=
    intermediate_value_Icc (by norm_num) (continuousOn_regBetaFn ha hb)
  have hmem : p ∈ Set.Icc (regBetaFn a b 0) (regBetaFn a b 1) := by
    rw [regBetaFn_zero, regBetaFn_one ha hb]
    exact ⟨hp0, hp1⟩
  obtain ⟨x, hx, hxp⟩ := hsub hmem
  refine ⟨x, ⟨hx, hxp⟩, ?_⟩
  rintro y ⟨hy, hyp⟩
  exact (regBetaFn_strictMonoOn ha hb).injOn hy hx (by rw [hyp, hxp])

end SHSLib.Trigamma
