/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regularity of the flow for drifts that are only locally Lipschitz

`SHSLib.Core.FlowRegularity` establishes, for a *globally* Lipschitz drift, that
the flow is unique, Lipschitz in the initial state and satisfies the restart
(cocycle) identity.  `SHSLib.Core.GlobalFlowLinearGrowth` constructs the flow
under the weaker hypotheses of Hespanha (2005), Lemma 1 — drift jointly
continuous, Lipschitz on bounded sets and of linear growth.  This module carries
the regularity theory over to that weaker setting.

The mechanism is always the same: on a compact time interval a continuous
trajectory is bounded, so the drift may be truncated to a ball on which it *is*
globally Lipschitz, and the results of the global theory apply.

## Main results

* `SHS.flow_eq_of_lipschitzOnBalls` — forward uniqueness of continuous solutions
  of the flow equation.
* `SHS.HasGlobalFlow.flow_eq_of_lipschitzOnBalls` — any two global flows with
  continuous trajectories coincide forward in time.
* `SHS.HasGlobalFlow.flow_restart_of_lipschitzOnBalls` — the restart (cocycle)
  identity `φ(t; s, q, φ(s; t₀, q, x)) = φ(t; t₀, q, x)`.
* `SHS.HasGlobalFlow.norm_flow_sub_le_on_ball` — Lipschitz dependence on the
  initial state, with a modulus governed by the Lipschitz constant of the drift
  on a ball containing both trajectories.
* `SHS.exists_hasGlobalFlow_regular_of_linear_growth` — a single statement
  combining existence, continuity, the growth envelope, uniqueness and the
  restart identity, with no regularity hypothesis left on the flow.
-/
import SHSLib.Core.GlobalFlowLinearGrowth
import SHSLib.Core.FlowRegularity

open MeasureTheory Metric Set Topology

open scoped NNReal

noncomputable section

section

variable {Q : Type*} {n m : ℕ} {S : SHS Q n m}

/-- **Forward uniqueness of the flow for a locally Lipschitz drift.**  Two
continuous solutions of the integral form of the flow equation with the same
initial value at `t₀` agree for all `t ≥ t₀`, provided the drift is jointly
continuous and Lipschitz on bounded sets. -/
theorem SHS.flow_eq_of_lipschitzOnBalls (S : SHS Q n m) (q₀ : Q)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q₀ p.2 p.1)
    (hlip : ODEFlow.LipschitzOnBalls fun t x => S.f q₀ x t)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    {y z : ℝ → EuclideanSpace ℝ (Fin n)} (hyc : Continuous y) (hzc : Continuous z)
    (hy : ∀ t, y t = x₀ + ∫ s in Set.Icc t₀ t, S.f q₀ (y s) s)
    (hz : ∀ t, z t = x₀ + ∫ s in Set.Icc t₀ t, S.f q₀ (z s) s)
    (t : ℝ) (ht : t₀ ≤ t) :
    y t = z t := by
  have hconv : ∀ (w : ℝ → EuclideanSpace ℝ (Fin n)),
      (∀ τ, w τ = x₀ + ∫ s in Set.Icc t₀ τ, S.f q₀ (w s) s) →
      ∀ τ ∈ Icc t₀ t, w τ = x₀ + ∫ s in t₀..τ, S.f q₀ (w s) s := by
    intro w hw τ hτ
    rw [hw τ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hτ.1]
  exact ODEFlow.locally_lipschitz_solution_unique (fun s v => S.f q₀ v s) hcont hlip
    t₀ t x₀ hyc hzc (hconv y hy) (hconv z hz) ⟨ht, le_rfl⟩

/-- Any two global flows of the same SHS with continuous trajectories agree
forward in time when the drift is jointly continuous and Lipschitz on bounded
sets: the flow map is determined by the SHS data. -/
theorem SHS.HasGlobalFlow.flow_eq_of_lipschitzOnBalls (h₁ h₂ : S.HasGlobalFlow) (q₀ : Q)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q₀ p.2 p.1)
    (hlip : ODEFlow.LipschitzOnBalls fun t x => S.f q₀ x t)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hc₁ : Continuous (h₁.flow t₀ q₀ x₀)) (hc₂ : Continuous (h₂.flow t₀ q₀ x₀))
    (t : ℝ) (ht : t₀ ≤ t) :
    h₁.flow t₀ q₀ x₀ t = h₂.flow t₀ q₀ x₀ t :=
  S.flow_eq_of_lipschitzOnBalls q₀ hcont hlip t₀ x₀ hc₁ hc₂
    (h₁.flow_ode t₀ q₀ x₀) (h₂.flow_ode t₀ q₀ x₀) t ht

/-- **Restart (cocycle) property for a locally Lipschitz drift.**  For
`t₀ ≤ s ≤ t`, restarting the flow at the intermediate time `s` from the state
reached then gives the same trajectory. -/
theorem SHS.HasGlobalFlow.flow_restart_of_lipschitzOnBalls (hflow : S.HasGlobalFlow) (q : Q)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (t₀ s t : ℝ) (hts : t₀ ≤ s) (hst : s ≤ t) (x : EuclideanSpace ℝ (Fin n))
    (hcx : Continuous (hflow.flow t₀ q x))
    (hcy : Continuous (hflow.flow s q (hflow.flow t₀ q x s))) :
    hflow.flow s q (hflow.flow t₀ q x s) t = hflow.flow t₀ q x t := by
  set xs := hflow.flow t₀ q x s with hxs
  -- the original trajectory, frozen before `s`, solves the flow equation started at `s`
  set z : ℝ → EuclideanSpace ℝ (Fin n) := fun τ => hflow.flow t₀ q x (max s τ) with hz
  have hzc : Continuous z := hcx.comp (continuous_const.max continuous_id)
  have hfx : Continuous fun r => S.f q (hflow.flow t₀ q x r) r :=
    hcont.comp (continuous_id.prodMk hcx)
  have hzeq : ∀ τ, z τ = xs + ∫ r in Set.Icc s τ, S.f q (z r) r := by
    intro τ
    by_cases hτ : s ≤ τ
    · have hcongr : Set.EqOn (fun r => S.f q (z r) r)
          (fun r => S.f q (hflow.flow t₀ q x r) r) (Set.uIcc s τ) := by
        intro r hr
        rw [Set.uIcc_of_le hτ] at hr
        show S.f q (hflow.flow t₀ q x (max s r)) r = _
        rw [max_eq_right hr.1]
      rw [hz]
      simp only [max_eq_right hτ]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hτ, intervalIntegral.integral_congr hcongr,
        hxs, hflow.flow_ode_interval t₀ q x hts,
        hflow.flow_ode_interval t₀ q x (le_trans hts hτ),
        ← intervalIntegral.integral_add_adjacent_intervals
          (a := t₀) (b := s) (c := τ) (hfx.intervalIntegrable _ _) (hfx.intervalIntegrable _ _)]
      abel
    · push_neg at hτ
      rw [Set.Icc_eq_empty (by linarith)]
      simp [hz, max_eq_left hτ.le, hxs]
  have hkey := S.flow_eq_of_lipschitzOnBalls q hcont hlip s xs hcy hzc
    (hflow.flow_ode s q xs) hzeq t hst
  rw [hkey, hz]
  simp [max_eq_right hst]

/-- **Lipschitz dependence on the initial state, localized.**  If both
trajectories stay in the ball of radius `R` on `[t₀, T]`, the distance between
them grows at most like `e^{K(t−t₀)}`, where `K` is a Lipschitz constant of the
drift on that ball. -/
theorem SHS.HasGlobalFlow.norm_flow_sub_le_on_ball (hflow : S.HasGlobalFlow) (q : Q)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t₀ T : ℝ) (x y : EuclideanSpace ℝ (Fin n)),
      Continuous (hflow.flow t₀ q x) → Continuous (hflow.flow t₀ q y) →
      (∀ s ∈ Icc t₀ T, ‖hflow.flow t₀ q x s‖ ≤ R) →
      (∀ s ∈ Icc t₀ T, ‖hflow.flow t₀ q y s‖ ≤ R) →
      ∀ t ∈ Icc t₀ T,
        ‖hflow.flow t₀ q x t - hflow.flow t₀ q y t‖ ≤ ‖x - y‖ * Real.exp (K * (t - t₀)) := by
  obtain ⟨K, hK⟩ := ODEFlow.exists_lipschitzWith_truncation hlip R hR
  refine ⟨K, K.coe_nonneg, fun t₀ T x y hcx hcy hbx hby t ht => ?_⟩
  -- work with the truncated drift, which agrees with `f` along both trajectories
  set g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun s v => S.f q (ODEFlow.clampBall R v) s with hg
  have hglip : ∀ (u v : EuclideanSpace ℝ (Fin n)) (s : ℝ), ‖g s u - g s v‖ ≤ K * ‖u - v‖ := by
    intro u v s
    have := (hK s).dist_le_mul u v
    simpa [hg, dist_eq_norm] using this
  have hgcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => g p.1 p.2 :=
    hcont.comp (continuous_fst.prodMk
      ((ODEFlow.lipschitzWith_clampBall R).continuous.comp continuous_snd))
  have heq : ∀ (w : ℝ → EuclideanSpace ℝ (Fin n)) (z₀ : EuclideanSpace ℝ (Fin n)),
      (∀ s ∈ Icc t₀ T, ‖w s‖ ≤ R) →
      (∀ τ, τ ∈ Icc t₀ T → w τ = z₀ + ∫ s in t₀..τ, S.f q (w s) s) →
      ∀ τ ∈ Icc t₀ T, w τ = z₀ + ∫ s in t₀..τ, g s (w s) := by
    intro w z₀ hb hw τ hτ
    rw [hw τ hτ]
    congr 1
    refine (intervalIntegral.integral_congr ?_).symm
    intro s hs
    rw [uIcc_of_le hτ.1] at hs
    show S.f q (ODEFlow.clampBall R (w s)) s = S.f q (w s) s
    rw [ODEFlow.clampBall_eq_self (hb s ⟨hs.1, le_trans hs.2 hτ.2⟩)]
  exact ODEFlow.dist_le_exp_of_integral_solutions g K K.coe_nonneg hglip hgcont t₀ T x y hcx hcy
    (heq _ x hbx fun τ hτ => hflow.flow_ode_interval t₀ q x hτ.1)
    (heq _ y hby fun τ hτ => hflow.flow_ode_interval t₀ q y hτ.1) t ht

/-- **Existence of a regular global flow under linear growth.**  For a drift
that is jointly continuous, Lipschitz on bounded sets and of linear growth, the
flow exists, has continuous trajectories, obeys the envelope
`(‖x‖ + a(t − t₀))·e^{b(t−t₀)}`, is the *unique* continuous solution of the flow
equation, and satisfies the restart (cocycle) identity. -/
theorem SHS.exists_hasGlobalFlow_regular_of_linear_growth (S : SHS Q n m)
    (hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (hlip : ∀ q, ODEFlow.LipschitzOnBalls fun t x => S.f q x t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgrowth : ∀ q x t, ‖S.f q x t‖ ≤ a + b * ‖x‖) :
    ∃ hflow : S.HasGlobalFlow,
      (∀ t₀ q x, Continuous (hflow.flow t₀ q x)) ∧
      (∀ (q : Q) (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
        ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound a b t₀ x t) ∧
      (∀ (h' : S.HasGlobalFlow), (∀ t₀ q x, Continuous (h'.flow t₀ q x)) →
        ∀ (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
          h'.flow t₀ q x t = hflow.flow t₀ q x t) ∧
      (∀ (q : Q) (t₀ s t : ℝ), t₀ ≤ s → s ≤ t → ∀ x : EuclideanSpace ℝ (Fin n),
        hflow.flow s q (hflow.flow t₀ q x s) t = hflow.flow t₀ q x t) := by
  obtain ⟨hflow, hfc, hfb⟩ :=
    S.exists_hasGlobalFlow_of_linear_growth hcont hlip a b ha hb hgrowth
  refine ⟨hflow, hfc, hfb, fun h' hc' t₀ q x t ht => ?_, fun q t₀ s t hts hst x => ?_⟩
  · exact h'.flow_eq_of_lipschitzOnBalls hflow q (hcont q) (hlip q) t₀ x
      (hc' t₀ q x) (hfc t₀ q x) t ht
  · exact hflow.flow_restart_of_lipschitzOnBalls q (hcont q) (hlip q) t₀ s t hts hst x
      (hfc t₀ q x) (hfc s q _)

end

end
