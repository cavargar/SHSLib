/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Global flow under a linear growth condition with time-varying coefficients

`SHSLib.Core.GlobalFlowLinearGrowth` constructs the flow of an SHS whose drift
obeys `‖f(q, x, t)‖ ≤ a + b‖x‖` with *constant* `a, b`.  Hespanha's Lemma 1 is
usually applied with coefficients that depend on time, `a(t)`, `b(t)`.  This
module carries the whole chain over to that setting:

* `gronwall_varying_rate_source` — Grönwall's inequality with both a
  time-varying rate and a time-varying source term;
* `ODEFlow.linearGrowthBoundVar` — the envelope
  `(‖x₀‖ + ∫_{t₀}^{t} a)·e^{∫_{t₀}^{t} b}`, with its monotonicity;
* `ODEFlow.norm_le_linearGrowthBoundVar` — the a priori bound for any continuous
  solution of the integral equation;
* `ODEFlow.exists_solution_horizon_of_linear_growth_var` and
  `ODEFlow.exists_global_solution_of_linear_growth_var` — existence on a finite
  horizon and globally;
* `SHS.exists_hasGlobalFlow_of_linear_growth_var` — Assumption 1 for an SHS with
  a time-varying linear growth bound.
-/
import SHSLib.Core.GlobalFlowLinearGrowth

open MeasureTheory Metric Set Topology Filter

open scoped NNReal

noncomputable section

/-- **Grönwall's inequality with a time-varying rate and source (integral
form).**  If `u` is continuous, `γ ≥ 0` and `c ≥ 0` are continuous, and

  `u t ≤ δ + ∫_a^t (γ(s)·u(s) + c(s)) ds`  for all `t ∈ [a, b]`,

then

  `u t ≤ (δ + ∫_a^t c)·exp(∫_a^t γ)`  for all `t ∈ [a, b]`.

This generalizes `gronwall_varying_rate`, where the source `c` is constant. -/
theorem gronwall_varying_rate_source
    {u gam cf : ℝ → ℝ} {a b delta : ℝ}
    (hu : Continuous u) (hgam : Continuous gam) (hgam0 : ∀ s, 0 ≤ gam s)
    (hcf : Continuous cf) (hcf0 : ∀ s, 0 ≤ cf s)
    (hint : ∀ t ∈ Set.Icc a b, u t ≤ delta + ∫ s in a..t, (gam s * u s + cf s)) :
    ∀ t ∈ Set.Icc a b,
      u t ≤ (delta + ∫ s in a..t, cf s) * Real.exp (∫ s in a..t, gam s) := by
  set F : ℝ → ℝ := fun s => gam s * u s + cf s with hF
  have hFc : Continuous F := by fun_prop
  set v : ℝ → ℝ := fun t => delta + ∫ s in a..t, F s with hv
  have hv_deriv : ∀ t, HasDerivAt v (F t) t := by
    intro t
    have := (intervalIntegral.integral_hasStrictDerivAt_right
      (hFc.intervalIntegrable a t) (hFc.stronglyMeasurableAtFilter _ _) hFc.continuousAt).hasDerivAt
    simpa [hv] using this.const_add delta
  set G : ℝ → ℝ := fun t => Real.exp (-∫ s in a..t, gam s) with hG
  have hG_deriv : ∀ t, HasDerivAt G (-gam t * G t) t := by
    intro t
    have h1 : HasDerivAt (fun t => ∫ s in a..t, gam s) (gam t) t :=
      (intervalIntegral.integral_hasStrictDerivAt_right (hgam.intervalIntegrable a t)
        (hgam.stronglyMeasurableAtFilter _ _) hgam.continuousAt).hasDerivAt
    simpa [hG, mul_comm] using h1.neg.exp
  have hC_deriv : ∀ t, HasDerivAt (fun t => delta + ∫ s in a..t, cf s) (cf t) t := by
    intro t
    have := (intervalIntegral.integral_hasStrictDerivAt_right
      (hcf.intervalIntegrable a t) (hcf.stronglyMeasurableAtFilter _ _) hcf.continuousAt).hasDerivAt
    simpa using this.const_add delta
  have hGpos : ∀ t, 0 < G t := fun t => Real.exp_pos _
  have hGle : ∀ t, a ≤ t → G t ≤ 1 := by
    intro t ht
    rw [hG]
    simp only [Real.exp_le_one_iff, neg_nonpos]
    rw [intervalIntegral.integral_of_le ht]
    exact setIntegral_nonneg measurableSet_Ioc fun s _ => hgam0 s
  set H : ℝ → ℝ := fun t => (delta + ∫ s in a..t, cf s) - G t * v t with hH
  have hH_deriv : ∀ t, HasDerivAt H (cf t - ((-gam t * G t) * v t + G t * F t)) t :=
    fun t => (hC_deriv t).sub ((hG_deriv t).mul (hv_deriv t))
  have hHmono : MonotoneOn H (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun t _ => ((hH_deriv t).continuousAt).continuousWithinAt
    · intro t _
      exact (hH_deriv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hH_deriv t).deriv]
      have hut : u t ≤ v t := hint t ⟨ht.1.le, ht.2.le⟩
      have h1 : cf t - ((-gam t * G t) * v t + G t * F t)
          = cf t * (1 - G t) + gam t * G t * (v t - u t) := by
        simp only [hF]; ring
      rw [h1]
      have hG1 := hGle t ht.1.le
      have h2 : 0 ≤ cf t * (1 - G t) := mul_nonneg (hcf0 t) (by linarith)
      have h3 : 0 ≤ gam t * G t * (v t - u t) :=
        mul_nonneg (mul_nonneg (hgam0 t) (hGpos t).le) (by linarith)
      linarith
  intro t ht
  have hHa : H a = 0 := by simp [hH, hG, hv]
  have h4 : 0 ≤ H t := by
    have := hHmono (Set.left_mem_Icc.2 (ht.1.trans ht.2)) ht ht.1
    linarith [hHa]
  have hut : u t ≤ v t := hint t ht
  have h5 : G t * v t ≤ delta + ∫ s in a..t, cf s := by
    simp only [hH] at h4; linarith
  have hGinv : (G t)⁻¹ = Real.exp (∫ s in a..t, gam s) := by
    rw [hG, ← Real.exp_neg]; ring_nf
  calc u t ≤ v t := hut
    _ = (G t)⁻¹ * (G t * v t) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hGpos t)), one_mul]
    _ ≤ (G t)⁻¹ * (delta + ∫ s in a..t, cf s) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = (delta + ∫ s in a..t, cf s) * Real.exp (∫ s in a..t, gam s) := by rw [hGinv]; ring

namespace ODEFlow

variable {n : ℕ}

/-- The growth envelope for time-varying coefficients:
`(‖x₀‖ + ∫_{t₀}^{t} a)·e^{∫_{t₀}^{t} b}`. -/
def linearGrowthBoundVar (av bv : ℝ → ℝ) (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  (‖x₀‖ + ∫ s in t₀..t, av s) * Real.exp (∫ s in t₀..t, bv s)

lemma intervalIntegral_nonneg_of_nonneg {g : ℝ → ℝ} (hg : ∀ s, 0 ≤ g s) {s t : ℝ}
    (hst : s ≤ t) : 0 ≤ ∫ r in s..t, g r :=
  intervalIntegral.integral_nonneg hst fun r _ => hg r

lemma linearGrowthBoundVar_nonneg {av bv : ℝ → ℝ} (hav : ∀ s, 0 ≤ av s)
    {t₀ : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : t₀ ≤ t) :
    0 ≤ linearGrowthBoundVar av bv t₀ x₀ t := by
  refine mul_nonneg ?_ (Real.exp_nonneg _)
  have := intervalIntegral_nonneg_of_nonneg hav ht
  linarith [norm_nonneg x₀]

lemma linearGrowthBoundVar_mono {av bv : ℝ → ℝ} (hav : ∀ s, 0 ≤ av s) (havc : Continuous av)
    (hbv : ∀ s, 0 ≤ bv s) (hbvc : Continuous bv)
    {t₀ : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {s t : ℝ} (hts : t₀ ≤ s) (hst : s ≤ t) :
    linearGrowthBoundVar av bv t₀ x₀ s ≤ linearGrowthBoundVar av bv t₀ x₀ t := by
  have hasplit : (∫ r in t₀..t, av r) = (∫ r in t₀..s, av r) + ∫ r in s..t, av r :=
    (intervalIntegral.integral_add_adjacent_intervals (havc.intervalIntegrable _ _)
      (havc.intervalIntegrable _ _)).symm
  have hbsplit : (∫ r in t₀..t, bv r) = (∫ r in t₀..s, bv r) + ∫ r in s..t, bv r :=
    (intervalIntegral.integral_add_adjacent_intervals (hbvc.intervalIntegrable _ _)
      (hbvc.intervalIntegrable _ _)).symm
  have ha2 : 0 ≤ ∫ r in s..t, av r := intervalIntegral_nonneg_of_nonneg hav hst
  have hb2 : 0 ≤ ∫ r in s..t, bv r := intervalIntegral_nonneg_of_nonneg hbv hst
  have ha1 : 0 ≤ ∫ r in t₀..s, av r := intervalIntegral_nonneg_of_nonneg hav hts
  refine mul_le_mul (by rw [hasplit]; linarith) (Real.exp_le_exp.mpr (by rw [hbsplit]; linarith))
    (Real.exp_nonneg _) ?_
  rw [hasplit]
  linarith [norm_nonneg x₀]

/-- **A priori bound with time-varying coefficients.**  Any continuous solution
of the integral equation whose drift obeys `‖g s y‖ ≤ a(s) + b(s)‖y‖` stays below
the envelope. -/
theorem norm_le_linearGrowthBoundVar
    {g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {av bv : ℝ → ℝ} (havc : Continuous av) (hav : ∀ s, 0 ≤ av s)
    (hbvc : Continuous bv) (hbv : ∀ s, 0 ≤ bv s)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => g p.1 p.2)
    (t₀ T : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) {u : ℝ → EuclideanSpace ℝ (Fin n)}
    (hu : Continuous u)
    (hueq : ∀ t ∈ Icc t₀ T, u t = x₀ + ∫ s in t₀..t, g s (u s))
    (hgrowth : ∀ s y, ‖g s y‖ ≤ av s + bv s * ‖y‖) :
    ∀ t ∈ Icc t₀ T, ‖u t‖ ≤ linearGrowthBoundVar av bv t₀ x₀ t := by
  have hgu : Continuous fun s => g s (u s) := continuous_comp_curve hcont hu
  have hint : ∀ t ∈ Icc t₀ T, ‖u t‖ ≤ ‖x₀‖ + ∫ s in t₀..t, (bv s * ‖u s‖ + av s) := by
    intro t ht
    have ht0 : t₀ ≤ t := ht.1
    have hstep : ‖∫ s in t₀..t, g s (u s)‖ ≤ ∫ s in t₀..t, (bv s * ‖u s‖ + av s) := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht0).trans ?_
      refine intervalIntegral.integral_mono_on ht0 ?_ ?_ fun s _ => ?_
      · exact hgu.norm.intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun s => bv s * ‖u s‖ + av s).intervalIntegrable _ _
      · have := hgrowth s (u s); linarith
    rw [hueq t ht]
    have := norm_add_le x₀ (∫ s in t₀..t, g s (u s))
    linarith
  intro t ht
  have key := gronwall_varying_rate_source (u := fun s => ‖u s‖) (gam := bv) (cf := av)
    (a := t₀) (b := T) (delta := ‖x₀‖)
    hu.norm hbvc hbv havc hav hint t ht
  simpa [linearGrowthBoundVar] using key

/-- Solvability on `[t₀, T]` for a drift that is Lipschitz on balls and of linear
growth with time-varying coefficients. -/
theorem exists_solution_horizon_of_linear_growth_var
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => f p.1 p.2)
    (hlip : LipschitzOnBalls f)
    {av bv : ℝ → ℝ} (havc : Continuous av) (hav : ∀ s, 0 ≤ av s)
    (hbvc : Continuous bv) (hbv : ∀ s, 0 ≤ bv s)
    (hgrowth : ∀ s y, ‖f s y‖ ≤ av s + bv s * ‖y‖)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (T : ℝ) (hT : t₀ ≤ T) :
    ∃ α : ℝ → EuclideanSpace ℝ (Fin n), Continuous α ∧ (∀ t ≤ t₀, α t = x₀) ∧
      ∀ t ∈ Icc t₀ T, α t = x₀ + ∫ s in t₀..t, f s (α s) := by
  set R : ℝ := linearGrowthBoundVar av bv t₀ x₀ T with hRdef
  have hR0 : 0 ≤ R := linearGrowthBoundVar_nonneg hav hT
  obtain ⟨K, hK⟩ := exists_lipschitzWith_truncation hlip R hR0
  set g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun t x => f t (clampBall R x) with hg
  have hgcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => g p.1 p.2 :=
    hcont.comp (continuous_fst.prodMk
      ((lipschitzWith_clampBall R).continuous.comp continuous_snd))
  obtain ⟨α, hαcont, hα0, hαeq⟩ := exists_global_solution g K hK hgcont t₀ x₀
  have hggrowth : ∀ s y, ‖g s y‖ ≤ av s + bv s * ‖y‖ := by
    intro s y
    refine le_trans (hgrowth s (clampBall R y)) ?_
    have := norm_clampBall_le R hR0 y
    nlinarith [hbv s]
  have hbound := norm_le_linearGrowthBoundVar havc hav hbvc hbv hgcont t₀ T x₀ hαcont
    (fun t ht => hαeq t ht.1) hggrowth
  refine ⟨α, hαcont, hα0, fun t ht => ?_⟩
  rw [hαeq t ht.1]
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hmem : s ∈ Icc t₀ T := ⟨hs.1, le_trans hs.2 ht.2⟩
  have hle : ‖α s‖ ≤ R :=
    le_trans (hbound s hmem) (linearGrowthBoundVar_mono hav havc hbv hbvc hmem.1 hmem.2)
  show f s (clampBall R (α s)) = f s (α s)
  rw [clampBall_eq_self hle]

/-- **Global existence under linear growth with time-varying coefficients.** -/
theorem exists_global_solution_of_linear_growth_var
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => f p.1 p.2)
    (hlip : LipschitzOnBalls f)
    {av bv : ℝ → ℝ} (havc : Continuous av) (hav : ∀ s, 0 ≤ av s)
    (hbvc : Continuous bv) (hbv : ∀ s, 0 ≤ bv s)
    (hgrowth : ∀ s y, ‖f s y‖ ≤ av s + bv s * ‖y‖)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ α : ℝ → EuclideanSpace ℝ (Fin n), Continuous α ∧ (∀ t ≤ t₀, α t = x₀) ∧
      (∀ t, t₀ ≤ t → α t = x₀ + ∫ s in t₀..t, f s (α s)) ∧
      (∀ t, t₀ ≤ t → ‖α t‖ ≤ linearGrowthBoundVar av bv t₀ x₀ t) := by
  classical
  choose sol hsolc hsol0 hsoleq using fun N : ℕ =>
    exists_solution_horizon_of_linear_growth_var f hcont hlip havc hav hbvc hbv hgrowth t₀ x₀
      (t₀ + N) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hcoh : ∀ (M N : ℕ) (t : ℝ), t₀ ≤ t → t ≤ t₀ + M → t ≤ t₀ + N →
      sol M t = sol N t := fun M N t ht hM hN =>
    locally_lipschitz_solution_unique f hcont hlip t₀ t x₀ (hsolc M) (hsolc N)
      (fun s hs => hsoleq M s ⟨hs.1, le_trans hs.2 hM⟩)
      (fun s hs => hsoleq N s ⟨hs.1, le_trans hs.2 hN⟩) ⟨ht, le_rfl⟩
  set idx : ℝ → ℕ := fun t => ⌈t - t₀⌉₊ with hidxdef
  have hidx : ∀ t, t ≤ t₀ + (idx t : ℝ) := by
    intro t
    have hceil := Nat.le_ceil (t - t₀)
    simp only [hidxdef]
    linarith
  set α : ℝ → EuclideanSpace ℝ (Fin n) := fun t => sol (idx t) t with hαdef
  have hagree : ∀ (N : ℕ) (t : ℝ), t ≤ t₀ + N → α t = sol N t := by
    intro N t ht
    by_cases htt : t ≤ t₀
    · show sol (idx t) t = sol N t
      rw [hsol0 (idx t) t htt, hsol0 N t htt]
    · push_neg at htt
      exact hcoh (idx t) N t htt.le (hidx t) ht
  have hbig : ∀ t : ℝ, ∃ N : ℕ, t < t₀ + N := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt (t - t₀)
    exact ⟨N, by linarith⟩
  have hcontα : Continuous α := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨N, hN⟩ := hbig t
    have heq : α =ᶠ[𝓝 t] sol N :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds hN) fun s hs => hagree N s (le_of_lt hs)
    exact ((hsolc N).continuousAt).congr heq.symm
  refine ⟨α, hcontα, fun t ht => hsol0 (idx t) t ht, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨N, hN⟩ := hbig t
    have hcongr : EqOn (fun s => f s (α s)) (fun s => f s (sol N s)) (uIcc t₀ t) := by
      intro s hs
      rw [uIcc_of_le ht] at hs
      show f s (α s) = f s (sol N s)
      rw [hagree N s (le_trans hs.2 hN.le)]
    rw [intervalIntegral.integral_congr hcongr, hagree N t hN.le]
    exact hsoleq N t ⟨ht, hN.le⟩
  · obtain ⟨N, hN⟩ := hbig t
    have hb2 := norm_le_linearGrowthBoundVar havc hav hbvc hbv hcont t₀ t x₀ (hsolc N)
      (fun s hs => hsoleq N s ⟨hs.1, le_trans hs.2 hN.le⟩) hgrowth t ⟨ht, le_rfl⟩
    rw [hagree N t hN.le]
    exact hb2

end ODEFlow

/-- **Existence of a global flow under linear growth with time-varying
coefficients.**  If the drift of `S` is jointly continuous, Lipschitz on bounded
sets and obeys `‖f(q, x, t)‖ ≤ a(t) + b(t)‖x‖` for continuous nonnegative `a`,
`b`, then `S` has a global flow with continuous trajectories obeying the envelope
`(‖x‖ + ∫_{t₀}^{t} a)·e^{∫_{t₀}^{t} b}`. -/
theorem SHS.exists_hasGlobalFlow_of_linear_growth_var
    {Q : Type*} {n m : ℕ} (S : SHS Q n m)
    (hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ∀ q, ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    {av bv : ℝ → ℝ} (havc : Continuous av) (hav : ∀ s, 0 ≤ av s)
    (hbvc : Continuous bv) (hbv : ∀ s, 0 ≤ bv s)
    (hgrowth : ∀ q x t, ‖S.f q x t‖ ≤ av t + bv t * ‖x‖) :
    ∃ hflow : S.HasGlobalFlow, (∀ t₀ q x, Continuous (hflow.flow t₀ q x)) ∧
      ∀ (q : Q) (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
        ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBoundVar av bv t₀ x t := by
  classical
  choose flow hflow_cont hflow_const hflow_eq hflow_bound using fun (t₀ : ℝ) (q : Q)
    (x : EuclideanSpace ℝ (Fin n)) =>
      ODEFlow.exists_global_solution_of_linear_growth_var (fun t y => S.f q y t) (hcont q)
        (hlip q) havc hav hbvc hbv (fun s y => hgrowth q y s) t₀ x
  refine ⟨{ flow := flow, flow_init := fun t₀ q₀ x₀ => hflow_const t₀ q₀ x₀ t₀ le_rfl,
            flow_ode := ?_ }, hflow_cont, fun q t₀ x t ht => hflow_bound t₀ q x t ht⟩
  intro t₀ q₀ x₀ t
  by_cases ht : t₀ ≤ t
  · rw [hflow_eq t₀ q₀ x₀ t ht, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht]
  · push_neg at ht
    rw [Set.Icc_eq_empty (by linarith)]
    simp [hflow_const t₀ q₀ x₀ t ht.le]

end
