/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Global existence of the flow under local Lipschitz continuity and linear growth

`SHSLib.Core.GlobalFlowExistence` constructs the flow of an SHS whose drift is
*globally* Lipschitz in the state.  Hespanha (2005) assumes less: Lemma 1 only
requires a **linear growth** bound `‖f(q, x, t)‖ ≤ a + b‖x‖` on the drift (plus
enough regularity for solutions to be unique), and shows that linear growth is
what rules out finite escape times.

This module proves global existence under exactly that combination: the drift is
Lipschitz **on bounded sets** (uniformly in time), jointly continuous, and of
linear growth.  The argument is the classical truncation argument:

* truncate the state coordinatewise to the box of half-width `R`
  (`ODEFlow.clampBall`, a `1`-Lipschitz retraction that fixes the ball of radius
  `R`), which makes the truncated drift globally Lipschitz;
* solve the truncated equation globally with
  `ODEFlow.exists_global_solution`;
* use Grönwall's inequality to show the solution obeys the a priori bound
  `‖α(t)‖ ≤ (‖x₀‖ + a(t − t₀))·e^{b(t−t₀)}`, which is *independent of `R`*, so
  for `R` at least the value of the bound at the horizon the truncation is
  inactive and `α` solves the original equation;
* glue the horizons together using uniqueness (again via truncation, since two
  solutions on a compact interval stay in a common ball).

## Main results

* `ODEFlow.exists_solution_horizon_of_linear_growth` — a solution on `[t₀, T]`.
* `ODEFlow.locally_lipschitz_solution_unique` — uniqueness on `[t₀, T]`.
* `ODEFlow.exists_global_solution_of_linear_growth` — a solution for all
  `t ≥ t₀`, together with the explicit growth envelope.
* `SHS.exists_hasGlobalFlow_of_linear_growth` — the corresponding statement for
  a stochastic hybrid system: `SHS.HasGlobalFlow` holds.
-/
import SHSLib.Core.GlobalFlowExistence

open MeasureTheory Metric Set Topology Filter

open scoped NNReal

noncomputable section

namespace ODEFlow

variable {n : ℕ}

/-! ## A Lipschitz retraction onto a box -/

/-- Coordinatewise truncation to `[-R, R]`: a `1`-Lipschitz map that fixes the
closed ball of radius `R` and has image inside the ball of radius `√n·R`. -/
def clampBall (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => max (-R) (min R (x.ofLp i)))

@[simp] lemma clampBall_apply (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (clampBall R x).ofLp i = max (-R) (min R (x.ofLp i)) := rfl

lemma real_clamp_lipschitz (R : ℝ) : LipschitzWith 1 (fun c : ℝ => max (-R) (min R c)) := by
  simpa [min_comm] using ((LipschitzWith.id (α := ℝ)).min_const R).const_max (-R)

lemma abs_clamp_sub_le (R a b : ℝ) :
    |max (-R) (min R a) - max (-R) (min R b)| ≤ |a - b| := by
  have h := (real_clamp_lipschitz R).dist_le_mul a b
  simpa [Real.dist_eq] using h

lemma lipschitzWith_clampBall (R : ℝ) : LipschitzWith 1 (clampBall (n := n) R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  simp only [NNReal.coe_one, one_mul]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h := abs_clamp_sub_le R (x.ofLp i) (y.ofLp i)
  simp only [clampBall_apply, Real.dist_eq]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

lemma norm_clampBall_le (R : ℝ) (hR : 0 ≤ R) (x : EuclideanSpace ℝ (Fin n)) :
    ‖clampBall R x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [clampBall_apply, Real.norm_eq_abs]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  rcases le_total 0 (x.ofLp i) with h | h
  · rw [abs_of_nonneg (le_max_of_le_right (le_min hR h)), abs_of_nonneg h]
    exact max_le (by linarith) (min_le_right _ _)
  · have hmin : min R (x.ofLp i) = x.ofLp i := min_eq_right (le_trans h hR)
    rw [hmin, abs_of_nonpos (max_le (by linarith) h), abs_of_nonpos h]
    have h2 : x.ofLp i ≤ max (-R) (x.ofLp i) := le_max_right _ _
    linarith

lemma clampBall_eq_self {R : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R) :
    clampBall R x = x := by
  ext i
  have hxi : |x.ofLp i| ≤ R := le_trans (by simpa using PiLp.norm_apply_le x i) hx
  simp [clampBall_apply, min_eq_right (abs_le.mp hxi).2, max_eq_right (abs_le.mp hxi).1]

lemma norm_clampBall_le_sqrt (R : ℝ) (hR : 0 ≤ R) (x : EuclideanSpace ℝ (Fin n)) :
    ‖clampBall R x‖ ≤ Real.sqrt n * R := by
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i : Fin n, ‖(clampBall R x).ofLp i‖ ^ 2) ≤ (n : ℝ) * R ^ 2 := by
    have hone : ∀ i : Fin n, ‖(clampBall R x).ofLp i‖ ^ 2 ≤ R ^ 2 := by
      intro i
      simp only [clampBall_apply, Real.norm_eq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    calc (∑ i : Fin n, ‖(clampBall R x).ofLp i‖ ^ 2) ≤ ∑ _i : Fin n, R ^ 2 :=
          Finset.sum_le_sum fun i _ => hone i
      _ = (n : ℝ) * R ^ 2 := by simp
  calc Real.sqrt (∑ i : Fin n, ‖(clampBall R x).ofLp i‖ ^ 2)
      ≤ Real.sqrt ((n : ℝ) * R ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * R := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hR]

/-! ## Truncated vector field -/

/-- Hypothesis: the drift is Lipschitz on every ball, with a constant that may
depend on the radius but not on time. -/
def LipschitzOnBalls (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ R : ℝ, ∃ K : ℝ≥0, ∀ t, LipschitzOnWith K (f t) (Metric.closedBall 0 R)

/-- The truncated drift `fᴿ(t, x) = f(t, clampBall R x)` is globally Lipschitz. -/
theorem exists_lipschitzWith_truncation
    {f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hlip : LipschitzOnBalls f) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ≥0, ∀ t, LipschitzWith K fun x => f t (clampBall R x) := by
  obtain ⟨K, hK⟩ := hlip (Real.sqrt n * R)
  refine ⟨K, fun t => LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hmem : ∀ z : EuclideanSpace ℝ (Fin n), clampBall R z ∈ Metric.closedBall 0 (Real.sqrt n * R) :=
    fun z => by simpa using norm_clampBall_le_sqrt R hR z
  refine le_trans ((hK t).dist_le_mul _ (hmem x) _ (hmem y)) ?_
  have hc := (lipschitzWith_clampBall (n := n) R).dist_le_mul x y
  have : dist (clampBall R x) (clampBall R y) ≤ dist x y := by simpa using hc
  exact mul_le_mul_of_nonneg_left this K.coe_nonneg

/-- The growth envelope of a linear-growth drift:
`(‖x₀‖ + a(t − t₀))·e^{b(t−t₀)}`. -/
def linearGrowthBound (a b t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  (‖x₀‖ + a * (t - t₀)) * Real.exp (b * (t - t₀))

lemma linearGrowthBound_nonneg {a b t₀ : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (ha : 0 ≤ a) (ht : t₀ ≤ t) : 0 ≤ linearGrowthBound a b t₀ x₀ t := by
  have h1 : 0 ≤ ‖x₀‖ + a * (t - t₀) := by
    have : 0 ≤ a * (t - t₀) := mul_nonneg ha (by linarith)
    linarith [norm_nonneg x₀]
  exact mul_nonneg h1 (Real.exp_nonneg _)

lemma linearGrowthBound_mono {a b t₀ : ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hts : t₀ ≤ s) (hst : s ≤ t) :
    linearGrowthBound a b t₀ x₀ s ≤ linearGrowthBound a b t₀ x₀ t := by
  have h1 : ‖x₀‖ + a * (s - t₀) ≤ ‖x₀‖ + a * (t - t₀) := by
    have : a * (s - t₀) ≤ a * (t - t₀) := by nlinarith
    linarith
  have h2 : Real.exp (b * (s - t₀)) ≤ Real.exp (b * (t - t₀)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h3 : 0 ≤ ‖x₀‖ + a * (s - t₀) := by
    have : 0 ≤ a * (s - t₀) := mul_nonneg ha (by linarith)
    linarith [norm_nonneg x₀]
  exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by linarith)

/-- **A priori bound.**  Any continuous solution of an integral equation whose
drift obeys `‖g s y‖ ≤ a + b‖y‖` stays below the growth envelope. -/
theorem norm_le_linearGrowthBound
    {g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => g p.1 p.2)
    (t₀ T : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) {u : ℝ → EuclideanSpace ℝ (Fin n)}
    (hu : Continuous u)
    (hueq : ∀ t ∈ Icc t₀ T, u t = x₀ + ∫ s in t₀..t, g s (u s))
    (hgrowth : ∀ s y, ‖g s y‖ ≤ a + b * ‖y‖) :
    ∀ t ∈ Icc t₀ T, ‖u t‖ ≤ linearGrowthBound a b t₀ x₀ t := by
  have hgu : Continuous fun s => g s (u s) := continuous_comp_curve hcont hu
  have hint : ∀ t ∈ Icc t₀ T, ‖u t‖ ≤ ‖x₀‖ + ∫ s in t₀..t, (b * ‖u s‖ + a) := by
    intro t ht
    have ht0 : t₀ ≤ t := ht.1
    have hstep : ‖∫ s in t₀..t, g s (u s)‖ ≤ ∫ s in t₀..t, (b * ‖u s‖ + a) := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht0).trans ?_
      refine intervalIntegral.integral_mono_on ht0 ?_ ?_ fun s _ => ?_
      · exact hgu.norm.intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun s => b * ‖u s‖ + a).intervalIntegrable _ _
      · have := hgrowth s (u s); linarith
    rw [hueq t ht]
    have := norm_add_le x₀ (∫ s in t₀..t, g s (u s))
    linarith
  intro t ht
  have key := gronwall_varying_rate (u := fun s => ‖u s‖) (gam := fun _ => b)
    (a := t₀) (b := T) (delta := ‖x₀‖) (c := a)
    hu.norm continuous_const (fun _ => hb) ha hint t ht
  simpa [linearGrowthBound, mul_comm] using key

/-! ## Existence on a finite horizon, uniqueness, and global existence -/

/-- Solvability of the integral equation on `[t₀, T]` for a drift that is
Lipschitz on balls and of linear growth. -/
theorem exists_solution_horizon_of_linear_growth
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => f p.1 p.2)
    (hlip : LipschitzOnBalls f)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgrowth : ∀ s y, ‖f s y‖ ≤ a + b * ‖y‖)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (T : ℝ) (hT : t₀ ≤ T) :
    ∃ α : ℝ → EuclideanSpace ℝ (Fin n), Continuous α ∧ (∀ t ≤ t₀, α t = x₀) ∧
      ∀ t ∈ Icc t₀ T, α t = x₀ + ∫ s in t₀..t, f s (α s) := by
  set R : ℝ := linearGrowthBound a b t₀ x₀ T with hRdef
  have hR0 : 0 ≤ R := linearGrowthBound_nonneg ha hT
  obtain ⟨K, hK⟩ := exists_lipschitzWith_truncation hlip R hR0
  set g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun t x => f t (clampBall R x) with hg
  have hgcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => g p.1 p.2 :=
    hcont.comp (continuous_fst.prodMk
      ((lipschitzWith_clampBall R).continuous.comp continuous_snd))
  obtain ⟨α, hαcont, hα0, hαeq⟩ := exists_global_solution g K hK hgcont t₀ x₀
  have hggrowth : ∀ s y, ‖g s y‖ ≤ a + b * ‖y‖ := by
    intro s y
    refine le_trans (hgrowth s (clampBall R y)) ?_
    have := norm_clampBall_le R hR0 y
    nlinarith
  have hbound := norm_le_linearGrowthBound a b ha hb hgcont t₀ T x₀ hαcont
    (fun t ht => hαeq t ht.1) hggrowth
  refine ⟨α, hαcont, hα0, fun t ht => ?_⟩
  rw [hαeq t ht.1]
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hmem : s ∈ Icc t₀ T := ⟨hs.1, le_trans hs.2 ht.2⟩
  have hle : ‖α s‖ ≤ R :=
    le_trans (hbound s hmem) (linearGrowthBound_mono ha hb hmem.1 hmem.2)
  show f s (clampBall R (α s)) = f s (α s)
  rw [clampBall_eq_self hle]

/-- **Uniqueness** on `[t₀, T]` for a drift that is Lipschitz on balls. -/
theorem locally_lipschitz_solution_unique
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => f p.1 p.2)
    (hlip : LipschitzOnBalls f)
    (t₀ T : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    {u v : ℝ → EuclideanSpace ℝ (Fin n)} (hu : Continuous u) (hv : Continuous v)
    (hueq : ∀ t ∈ Icc t₀ T, u t = x₀ + ∫ s in t₀..t, f s (u s))
    (hveq : ∀ t ∈ Icc t₀ T, v t = x₀ + ∫ s in t₀..t, f s (v s)) :
    EqOn u v (Icc t₀ T) := by
  by_cases hT : t₀ ≤ T
  · obtain ⟨s₁, hs₁, hmax⟩ := (isCompact_Icc (a := t₀) (b := T)).exists_isMaxOn
      ⟨t₀, left_mem_Icc.2 hT⟩ (f := fun s => max ‖u s‖ ‖v s‖)
      (by fun_prop : Continuous fun s => max ‖u s‖ ‖v s‖).continuousOn
    set R : ℝ := max ‖u s₁‖ ‖v s₁‖ with hRdef
    have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (le_max_left _ _)
    obtain ⟨K, hK⟩ := exists_lipschitzWith_truncation hlip R hR0
    set g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun t x => f t (clampBall R x) with hg
    have hgcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => g p.1 p.2 :=
      hcont.comp (continuous_fst.prodMk
        ((lipschitzWith_clampBall R).continuous.comp continuous_snd))
    have hbu : ∀ s ∈ Icc t₀ T, ‖u s‖ ≤ R := fun s hs =>
      le_trans (le_max_left _ _) (hmax hs)
    have hbv : ∀ s ∈ Icc t₀ T, ‖v s‖ ≤ R := fun s hs =>
      le_trans (le_max_right _ _) (hmax hs)
    have hueq' : ∀ t ∈ Icc t₀ T, u t = x₀ + ∫ s in t₀..t, g s (u s) := by
      intro t ht
      rw [hueq t ht]
      congr 1
      refine (intervalIntegral.integral_congr ?_).symm
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hmem : s ∈ Icc t₀ T := ⟨hs.1, le_trans hs.2 ht.2⟩
      show f s (clampBall R (u s)) = f s (u s)
      rw [clampBall_eq_self (hbu s hmem)]
    have hveq' : ∀ t ∈ Icc t₀ T, v t = x₀ + ∫ s in t₀..t, g s (v s) := by
      intro t ht
      rw [hveq t ht]
      congr 1
      refine (intervalIntegral.integral_congr ?_).symm
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hmem : s ∈ Icc t₀ T := ⟨hs.1, le_trans hs.2 ht.2⟩
      show f s (clampBall R (v s)) = f s (v s)
      rw [clampBall_eq_self (hbv s hmem)]
    exact integral_solution_unique g K hK hgcont t₀ T x₀ hu hv hueq' hveq'
  · intro t ht
    exact absurd (le_trans ht.1 ht.2) hT

/-- **Global existence under linear growth.** -/
theorem exists_global_solution_of_linear_growth
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => f p.1 p.2)
    (hlip : LipschitzOnBalls f)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgrowth : ∀ s y, ‖f s y‖ ≤ a + b * ‖y‖)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ α : ℝ → EuclideanSpace ℝ (Fin n), Continuous α ∧ (∀ t ≤ t₀, α t = x₀) ∧
      (∀ t, t₀ ≤ t → α t = x₀ + ∫ s in t₀..t, f s (α s)) ∧
      (∀ t, t₀ ≤ t → ‖α t‖ ≤ linearGrowthBound a b t₀ x₀ t) := by
  classical
  choose sol hsolc hsol0 hsoleq using fun N : ℕ =>
    exists_solution_horizon_of_linear_growth f hcont hlip a b ha hb hgrowth t₀ x₀
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
    have hb2 := norm_le_linearGrowthBound a b ha hb hcont t₀ t x₀ (hsolc N)
      (fun s hs => hsoleq N s ⟨hs.1, le_trans hs.2 hN.le⟩) hgrowth t ⟨ht, le_rfl⟩
    rw [hagree N t hN.le]
    exact hb2

end ODEFlow

/-- **Existence of a global flow under linear growth.**  If the drift of `S` is
jointly continuous, Lipschitz on bounded sets (uniformly in time) and of linear
growth `‖f(q, x, t)‖ ≤ a + b‖x‖` — the hypotheses of Hespanha (2005), Lemma 1 —
then `S` has a global flow, with continuous trajectories obeying the envelope
`(‖x‖ + a(t − t₀))·e^{b(t−t₀)}`. -/
theorem SHS.exists_hasGlobalFlow_of_linear_growth
    {Q : Type*} {n m : ℕ} (S : SHS Q n m)
    (hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ∀ q, ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgrowth : ∀ q x t, ‖S.f q x t‖ ≤ a + b * ‖x‖) :
    ∃ hflow : S.HasGlobalFlow, (∀ t₀ q x, Continuous (hflow.flow t₀ q x)) ∧
      ∀ (q : Q) (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
        ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound a b t₀ x t := by
  classical
  choose flow hflow_cont hflow_const hflow_eq hflow_bound using fun (t₀ : ℝ) (q : Q)
    (x : EuclideanSpace ℝ (Fin n)) =>
      ODEFlow.exists_global_solution_of_linear_growth (fun t y => S.f q y t) (hcont q)
        (hlip q) a b ha hb (fun s y => hgrowth q y s) t₀ x
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
