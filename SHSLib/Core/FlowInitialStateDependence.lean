/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dependence of the flow on the initial state

`SHSLib.Core.FlowRegularityLinearGrowth` bounds the distance between two
trajectories *provided both are already known to stay in a common ball*
(`SHS.HasGlobalFlow.norm_flow_sub_le_on_ball`).  Under the linear-growth
hypotheses of Hespanha (2005), Lemma 1, that proviso is automatic: the growth
envelope bounds *every* trajectory started in a bounded set of initial states,
uniformly on a compact time interval.  Combining the two gives genuine local
Lipschitz continuity of the initial-state map `x ↦ φ(t; t₀, q, x)`, hence its
continuity and measurability — the input needed by the Davis-layer
constructions, where the post-jump state is obtained by composing the flow with
a random initial condition.

## Main results

* `ODEFlow.linearGrowthBound_le_of_norm_le` — the envelope is bounded, uniformly
  over the initial states of a ball and over a compact time interval.
* `SHS.HasGlobalFlow.exists_lipschitz_initial_on_ball` — on a ball of initial
  states and a compact time interval the flow is Lipschitz in the initial state.
* `SHS.HasGlobalFlow.continuous_flow_initial` — `x ↦ φ(t; t₀, q, x)` is
  continuous for every `t ≥ t₀`.
* `SHS.HasGlobalFlow.measurable_flow_initial` — and therefore measurable.
* `SHS.HasGlobalFlow.continuousOn_flow_prod` — joint continuity in the initial
  state and the time.
* `SHS.exists_hasGlobalFlow_measurable_of_linear_growth` — existence of a global
  flow with all the regularity of `exists_hasGlobalFlow_regular_of_linear_growth`
  together with continuity and measurability in the initial state.
-/
import SHSLib.Core.FlowRegularityLinearGrowth

open MeasureTheory Metric Set Topology

open scoped NNReal

noncomputable section

namespace ODEFlow

variable {n : ℕ}

/-- The growth envelope, evaluated at any initial state of the ball of radius
`r` and any time of `[t₀, T]`, is bounded by `(r + a(T − t₀))·e^{b(T − t₀)}`. -/
lemma linearGrowthBound_le_of_norm_le {a b t₀ T r : ℝ} {x : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : ‖x‖ ≤ r) (ht₀ : t₀ ≤ t) (htT : t ≤ T) :
    linearGrowthBound a b t₀ x t ≤ (r + a * (T - t₀)) * Real.exp (b * (T - t₀)) := by
  have h1 : ‖x‖ + a * (t - t₀) ≤ r + a * (T - t₀) := by nlinarith
  have h2 : Real.exp (b * (t - t₀)) ≤ Real.exp (b * (T - t₀)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h3 : 0 ≤ ‖x‖ + a * (t - t₀) := by
    have : 0 ≤ a * (t - t₀) := mul_nonneg ha (by linarith)
    linarith [norm_nonneg x]
  exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by linarith)

end ODEFlow

section

variable {Q : Type*} {n m : ℕ} {S : SHS Q n m}

/-- **Lipschitz dependence on the initial state.**  Under the linear-growth
hypotheses, for a ball of initial states and a compact time interval there is a
single constant `C` with
`‖φ(t; t₀, q, x) − φ(t; t₀, q, y)‖ ≤ C‖x − y‖` for all `t ∈ [t₀, T]`. -/
theorem SHS.HasGlobalFlow.exists_lipschitz_initial_on_ball (hflow : S.HasGlobalFlow) (q : Q)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (hfc : ∀ (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)), Continuous (hflow.flow t₀ q x))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfb : ∀ (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
      ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound a b t₀ x t)
    (t₀ T r : ℝ) (hT : t₀ ≤ T) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r → ‖y‖ ≤ r →
      ∀ t ∈ Icc t₀ T,
        ‖hflow.flow t₀ q x t - hflow.flow t₀ q y t‖ ≤ C * ‖x - y‖ := by
  have hTt₀ : (0:ℝ) ≤ T - t₀ := by linarith
  set R : ℝ := (r + a * (T - t₀)) * Real.exp (b * (T - t₀)) with hRdef
  have hR : 0 ≤ R := by
    have : 0 ≤ r + a * (T - t₀) := by nlinarith
    exact mul_nonneg this (Real.exp_nonneg _)
  obtain ⟨K, hK0, hKb⟩ := hflow.norm_flow_sub_le_on_ball q hcont hlip R hR
  refine ⟨Real.exp (K * (T - t₀)), Real.exp_nonneg _, fun x y hx hy t ht => ?_⟩
  have hbound : ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ r →
      ∀ s ∈ Icc t₀ T, ‖hflow.flow t₀ q z s‖ ≤ R := by
    intro z hz s hs
    exact (hfb t₀ z s hs.1).trans
      (ODEFlow.linearGrowthBound_le_of_norm_le ha hb hz hs.1 hs.2)
  have hkey := hKb t₀ T x y (hfc t₀ x) (hfc t₀ y) (hbound x hx) (hbound y hy) t ht
  refine hkey.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by nlinarith [ht.1, ht.2])) (norm_nonneg _)

/-- The initial-state map of the flow is continuous. -/
theorem SHS.HasGlobalFlow.continuous_flow_initial (hflow : S.HasGlobalFlow) (q : Q)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (hfc : ∀ (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)), Continuous (hflow.flow t₀ q x))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfb : ∀ (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
      ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound a b t₀ x t)
    (t₀ t : ℝ) (ht : t₀ ≤ t) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => hflow.flow t₀ q x t := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨C, hC0, hC⟩ := hflow.exists_lipschitz_initial_on_ball q hcont hlip hfc ha hb hfb
    t₀ t (‖x₀‖ + 1) ht (by positivity)
  refine Metric.continuousAt_iff.mpr fun ε hε => ?_
  refine ⟨min 1 (ε / (C + 1)), lt_min one_pos (by positivity), fun {x} hx => ?_⟩
  have hx1 : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : dist x x₀ ≤ ε / (C + 1) := le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
  have hxr : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have := norm_sub_norm_le x x₀
    rw [dist_eq_norm] at hx1
    linarith
  have hbnd := hC x x₀ hxr (by linarith [norm_nonneg x₀]) t ⟨ht, le_rfl⟩
  rw [dist_eq_norm]
  rw [dist_eq_norm] at hx2
  have hlt : C * ‖x - x₀‖ < ε := by
    have h1 : C * ‖x - x₀‖ ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hx2 hC0
    have h2 : C * (ε / (C + 1)) < ε := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact lt_of_le_of_lt hbnd hlt

/-- The initial-state map of the flow is measurable. -/
theorem SHS.HasGlobalFlow.measurable_flow_initial (hflow : S.HasGlobalFlow) (q : Q)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (hfc : ∀ (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)), Continuous (hflow.flow t₀ q x))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfb : ∀ (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
      ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound a b t₀ x t)
    (t₀ t : ℝ) (ht : t₀ ≤ t) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => hflow.flow t₀ q x t :=
  (hflow.continuous_flow_initial q hcont hlip hfc ha hb hfb t₀ t ht).measurable

/-- **Joint continuity of the flow** in the initial state and the time. -/
theorem SHS.HasGlobalFlow.continuousOn_flow_prod (hflow : S.HasGlobalFlow) (q : Q)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (hfc : ∀ (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)), Continuous (hflow.flow t₀ q x))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfb : ∀ (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
      ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound a b t₀ x t)
    (t₀ : ℝ) :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ => hflow.flow t₀ q p.1 p.2)
      (Set.univ ×ˢ Set.Ici t₀) := by
  rintro ⟨x₀, t₁⟩ hp
  have ht₁ : t₀ ≤ t₁ := hp.2
  obtain ⟨C, hC0, hC⟩ := hflow.exists_lipschitz_initial_on_ball q hcont hlip hfc ha hb hfb
    t₀ (t₁ + 1) (‖x₀‖ + 1) (by linarith) (by positivity)
  refine Metric.continuousWithinAt_iff.mpr fun ε hε => ?_
  -- continuity of the trajectory started at `x₀` gives the time part
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ :=
    Metric.continuousAt_iff.mp ((hfc t₀ x₀).continuousAt (x := t₁)) (ε / 2) (by positivity)
  refine ⟨min (min 1 δ₁) (ε / (2 * (C + 1))), by positivity, ?_⟩
  rintro ⟨x, s⟩ hmem hdist
  have hs₀ : t₀ ≤ s := hmem.2
  rw [Prod.dist_eq] at hdist
  have hdx : dist x x₀ < min (min 1 δ₁) (ε / (2 * (C + 1))) :=
    lt_of_le_of_lt (le_max_left _ _) hdist
  have hds : dist s t₁ < min (min 1 δ₁) (ε / (2 * (C + 1))) :=
    lt_of_le_of_lt (le_max_right _ _) hdist
  have hx1 : dist x x₀ < 1 :=
    lt_of_lt_of_le hdx ((min_le_left _ _).trans (min_le_left _ _))
  have hx2 : dist x x₀ ≤ ε / (2 * (C + 1)) := (lt_of_lt_of_le hdx (min_le_right _ _)).le
  have hsδ : dist s t₁ < δ₁ :=
    lt_of_lt_of_le hds ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : dist s t₁ < 1 :=
    lt_of_lt_of_le hds ((min_le_left _ _).trans (min_le_left _ _))
  have hsT : s ≤ t₁ + 1 := by
    have := abs_lt.mp (by rwa [Real.dist_eq] at hs1)
    linarith [this.2]
  have hxr : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have := norm_sub_norm_le x x₀
    rw [dist_eq_norm] at hx1
    linarith
  have hstep1 := hC x x₀ hxr (by linarith [norm_nonneg x₀]) s ⟨hs₀, hsT⟩
  have hstep2 := hδ₁b hsδ
  have hsplit : dist (hflow.flow t₀ q x s) (hflow.flow t₀ q x₀ t₁) ≤
      dist (hflow.flow t₀ q x s) (hflow.flow t₀ q x₀ s)
        + dist (hflow.flow t₀ q x₀ s) (hflow.flow t₀ q x₀ t₁) := dist_triangle _ _ _
  have hfirst : dist (hflow.flow t₀ q x s) (hflow.flow t₀ q x₀ s) < ε / 2 := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt hstep1 ?_
    rw [dist_eq_norm] at hx2
    have h1 : C * ‖x - x₀‖ ≤ C * (ε / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hx2 hC0
    have h2 : C * (ε / (2 * (C + 1))) < ε / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  simp only []
  linarith [hsplit, hfirst, hstep2]

/-- **Existence of a global flow that is regular in the initial state.**  All the
conclusions of `SHS.exists_hasGlobalFlow_regular_of_linear_growth`, together with
continuity and measurability of `x ↦ φ(t; t₀, q, x)`. -/
theorem SHS.exists_hasGlobalFlow_measurable_of_linear_growth (S : SHS Q n m)
    (hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ∀ q, ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgrowth : ∀ q x t, ‖S.f q x t‖ ≤ a + b * ‖x‖) :
    ∃ hflow : S.HasGlobalFlow,
      (∀ t₀ q x, Continuous (hflow.flow t₀ q x)) ∧
      (∀ (q : Q) (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
        ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound a b t₀ x t) ∧
      (∀ (q : Q) (t₀ t : ℝ), t₀ ≤ t →
        Continuous fun x : EuclideanSpace ℝ (Fin n) => hflow.flow t₀ q x t) ∧
      (∀ (q : Q) (t₀ t : ℝ), t₀ ≤ t →
        Measurable fun x : EuclideanSpace ℝ (Fin n) => hflow.flow t₀ q x t) := by
  obtain ⟨hflow, hfc, hfb⟩ :=
    S.exists_hasGlobalFlow_of_linear_growth hcont hlip a b ha hb hgrowth
  have hcontin : ∀ (q : Q) (t₀ t : ℝ), t₀ ≤ t →
      Continuous fun x : EuclideanSpace ℝ (Fin n) => hflow.flow t₀ q x t := fun q t₀ t ht =>
    hflow.continuous_flow_initial q (hcont q) (hlip q) (fun s x => hfc s q x) ha hb
      (fun s x u hu => hfb q s x u hu) t₀ t ht
  exact ⟨hflow, hfc, hfb, hcontin, fun q t₀ t ht => (hcontin q t₀ t ht).measurable⟩

end

end
