/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regularity of the flow of an SHS with a Lipschitz drift

`SHSLib.Core.GlobalFlowExistence` constructs the flow of the continuous dynamics
for a drift that is globally Lipschitz in the state, and
`SHSLib.Core.GronwallGrowthBound` shows it is unique forward in time.  This
module records the two structural properties of that flow which the hybrid
layer uses, both consequences of the same Grönwall inequality:

* **Lipschitz dependence on the initial state**
  `‖φ(t; t₀, q, x) − φ(t; t₀, q, y)‖ ≤ ‖x − y‖·e^{L(t−t₀)}`; in particular the
  flow is continuous, hence measurable, in the initial condition.
* **The restart (cocycle) property**
  `φ(t; s, q, φ(s; t₀, q, x)) = φ(t; t₀, q, x)` for `t₀ ≤ s ≤ t`, which is what
  licenses restarting a sample path after a jump.

Both are stated for an arbitrary `SHS.HasGlobalFlow` whose trajectories are
continuous, and then combined with the existence theorem into a single
statement, `SHS.exists_hasGlobalFlow_regular_of_lipschitz`, in which no
continuity hypothesis remains.
-/
import SHSLib.Core.GlobalFlowExistence

open MeasureTheory Metric Set Topology Filter

open scoped NNReal

noncomputable section

namespace ODEFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Grönwall dependence on the initial value.**  Two continuous solutions of
the integral equation with a drift that is `L`-Lipschitz in the state separate
at most exponentially fast:
`‖u t − v t‖ ≤ ‖x₀ − y₀‖·e^{L(t−t₀)}` on `[t₀, T]`. -/
theorem dist_le_exp_of_integral_solutions (f : ℝ → E → E) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y t, ‖f t x - f t y‖ ≤ L * ‖x - y‖)
    (hcont : Continuous fun p : ℝ × E => f p.1 p.2)
    (t₀ T : ℝ) (x₀ y₀ : E) {u v : ℝ → E} (hu : Continuous u) (hv : Continuous v)
    (hueq : ∀ t ∈ Icc t₀ T, u t = x₀ + ∫ s in t₀..t, f s (u s))
    (hveq : ∀ t ∈ Icc t₀ T, v t = y₀ + ∫ s in t₀..t, f s (v s)) :
    ∀ t ∈ Icc t₀ T, ‖u t - v t‖ ≤ ‖x₀ - y₀‖ * Real.exp (L * (t - t₀)) := by
  have hfu : Continuous fun s => f s (u s) := continuous_comp_curve hcont hu
  have hfv : Continuous fun s => f s (v s) := continuous_comp_curve hcont hv
  have hd_cont : Continuous fun s => ‖u s - v s‖ := (hu.sub hv).norm
  have hint : ∀ t ∈ Icc t₀ T,
      ‖u t - v t‖ ≤ ‖x₀ - y₀‖ + ∫ s in t₀..t, (L * ‖u s - v s‖ + 0) := by
    intro t ht
    have ht0 : t₀ ≤ t := ht.1
    have hdiff : u t - v t = (x₀ - y₀) + ∫ s in t₀..t, (f s (u s) - f s (v s)) := by
      rw [hueq t ht, hveq t ht, intervalIntegral.integral_sub
        (hfu.intervalIntegrable _ _) (hfv.intervalIntegrable _ _)]
      abel
    rw [hdiff]
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (intervalIntegral.norm_integral_le_integral_norm ht0).trans ?_
    refine intervalIntegral.integral_mono_on ht0 ?_ ?_ fun s _ => ?_
    · exact (hfu.sub hfv).norm.intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun s => L * ‖u s - v s‖ + 0).intervalIntegrable _ _
    · simpa using hlip (u s) (v s) s
  intro t ht
  have key := gronwall_varying_rate (u := fun s => ‖u s - v s‖) (gam := fun _ => L)
    (a := t₀) (b := T) (delta := ‖x₀ - y₀‖) (c := 0)
    hd_cont continuous_const (fun _ => hL) le_rfl hint t ht
  simpa [mul_comm] using key

end ODEFlow

section

variable {Q : Type*} {n m : ℕ} {S : SHS Q n m}

/-- Interval-integral form of the flow equation, valid for `t ≥ t₀` (for
`t < t₀` the set `[t₀, t]` is empty and the flow equation only says
`φ(t) = x`). -/
theorem SHS.HasGlobalFlow.flow_ode_interval (hflow : S.HasGlobalFlow)
    (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t₀ ≤ t) :
    hflow.flow t₀ q x t = x + ∫ s in t₀..t, S.f q (hflow.flow t₀ q x s) s := by
  rw [hflow.flow_ode t₀ q x t, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht]

/-- **Lipschitz dependence of the flow on the initial state.**  If the drift is
`L`-Lipschitz in the state then
`‖φ(t; t₀, q, x) − φ(t; t₀, q, y)‖ ≤ ‖x − y‖·e^{L(t−t₀)}` for `t ≥ t₀`. -/
theorem SHS.HasGlobalFlow.norm_flow_sub_le (hflow : S.HasGlobalFlow) (q : Q)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y t, ‖S.f q x t - S.f q y t‖ ≤ L * ‖x - y‖)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (t₀ : ℝ) (x y : EuclideanSpace ℝ (Fin n))
    (hcx : Continuous (hflow.flow t₀ q x)) (hcy : Continuous (hflow.flow t₀ q y))
    (t : ℝ) (ht : t₀ ≤ t) :
    ‖hflow.flow t₀ q x t - hflow.flow t₀ q y t‖ ≤ ‖x - y‖ * Real.exp (L * (t - t₀)) :=
  ODEFlow.dist_le_exp_of_integral_solutions (fun s z => S.f q z s) L hL hlip hcont
    t₀ t x y hcx hcy
    (fun _ hτ => hflow.flow_ode_interval t₀ q x hτ.1)
    (fun _ hτ => hflow.flow_ode_interval t₀ q y hτ.1)
    t ⟨ht, le_rfl⟩

/-- **Restart (cocycle) property of the flow.**  For `t₀ ≤ s ≤ t`, restarting
the flow at the intermediate time `s` from the state reached then gives the same
trajectory: `φ(t; s, q, φ(s; t₀, q, x)) = φ(t; t₀, q, x)`. -/
theorem SHS.HasGlobalFlow.flow_restart (hflow : S.HasGlobalFlow) (q : Q)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y t, ‖S.f q x t - S.f q y t‖ ≤ L * ‖x - y‖)
    (hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
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
    · have hmax : max s τ = τ := max_eq_right hτ
      have hcongr : Set.EqOn (fun r => S.f q (z r) r)
          (fun r => S.f q (hflow.flow t₀ q x r) r) (Set.uIcc s τ) := by
        intro r hr
        rw [Set.uIcc_of_le hτ] at hr
        show S.f q (hflow.flow t₀ q x (max s r)) r = _
        rw [max_eq_right hr.1]
      rw [hz]
      simp only [hmax]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hτ, intervalIntegral.integral_congr hcongr,
        hxs, hflow.flow_ode_interval t₀ q x hts,
        hflow.flow_ode_interval t₀ q x (le_trans hts hτ),
        ← intervalIntegral.integral_add_adjacent_intervals
          (a := t₀) (b := s) (c := τ) (hfx.intervalIntegrable _ _) (hfx.intervalIntegrable _ _)]
      abel
    · push_neg at hτ
      have hempty : Set.Icc s τ = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith)
      rw [hempty]
      simp [hz, max_eq_left hτ.le, hxs]
  have hzint : Continuous fun r => S.f q (z r) r := hcont.comp (continuous_id.prodMk hzc)
  have hyint : Continuous fun r => S.f q (hflow.flow s q xs r) r :=
    hcont.comp (continuous_id.prodMk hcy)
  have hkey := S.flow_eq_of_lipschitz q L hL hlip s xs _ z hyint hzint
    (hflow.flow_ode s q xs) hzeq t hst
  rw [hkey, hz]
  simp [max_eq_right hst]

/-- **Existence of a regular global flow.**  For a drift that is globally
`K`-Lipschitz in the state and jointly continuous in `(t, x)`, the flow
constructed in `SHSLib.Core.GlobalFlowExistence` has continuous trajectories, is
Lipschitz in the initial state with constant `e^{K(t−t₀)}`, and satisfies the
restart (cocycle) identity.  No continuity hypothesis is left in the
statement. -/
theorem SHS.exists_hasGlobalFlow_regular_of_lipschitz (S : SHS Q n m) (K : ℝ≥0)
    (hlip : ∀ q t, LipschitzWith K fun x => S.f q x t)
    (hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1) :
    ∃ hflow : S.HasGlobalFlow,
      (∀ t₀ q x, Continuous (hflow.flow t₀ q x)) ∧
      (∀ (q : Q) (t₀ : ℝ) (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
        ‖hflow.flow t₀ q x t - hflow.flow t₀ q y t‖
          ≤ ‖x - y‖ * Real.exp ((K : ℝ) * (t - t₀))) ∧
      (∀ (q : Q) (t₀ s t : ℝ) (x : EuclideanSpace ℝ (Fin n)), t₀ ≤ s → s ≤ t →
        hflow.flow s q (hflow.flow t₀ q x s) t = hflow.flow t₀ q x t) := by
  obtain ⟨hflow, hcontflow⟩ := S.exists_hasGlobalFlow_continuous_of_lipschitz K hlip hcont
  have hlip' : ∀ (q : Q) (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      ‖S.f q x t - S.f q y t‖ ≤ (K : ℝ) * ‖x - y‖ := by
    intro q x y t
    simpa [dist_eq_norm] using (hlip q t).dist_le_mul x y
  refine ⟨hflow, hcontflow, fun q t₀ x y t ht => ?_, fun q t₀ s t x hts hst => ?_⟩
  · exact hflow.norm_flow_sub_le q (K : ℝ) K.coe_nonneg (hlip' q) (hcont q) t₀ x y
      (hcontflow t₀ q x) (hcontflow t₀ q y) t ht
  · exact hflow.flow_restart q (K : ℝ) K.coe_nonneg (hlip' q) (hcont q) t₀ s t hts hst x
      (hcontflow t₀ q x) (hcontflow s q (hflow.flow t₀ q x s))

/-- **No finite escape, with an explicit continuous envelope.**  A drift that is
globally `K`-Lipschitz in the state and bounded by `c₀` at the origin obeys the
linear-growth condition of Hespanha (2005), Lemma 1, with rate `2K` and constant
`2c₀`.  Consequently the flow it generates exists globally and stays below the
continuous envelope `(‖x‖ + 2c₀(t − t₀))·e^{2K(t−t₀)}` — the content of
Assumption 2(ii) for this model class. -/
theorem SHS.exists_hasGlobalFlow_growth_bound_of_lipschitz (S : SHS Q n m) (K : ℝ≥0)
    (hlip : ∀ q t, LipschitzWith K fun x => S.f q x t)
    (hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1)
    (c₀ : ℝ) (hc₀ : 0 ≤ c₀) (hbdd : ∀ q t, ‖S.f q 0 t‖ ≤ c₀) :
    ∃ hflow : S.HasGlobalFlow, (∀ t₀ q x, Continuous (hflow.flow t₀ q x)) ∧
      ∀ (q : Q) (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
        ‖hflow.flow t₀ q x t‖
          ≤ (‖x‖ + 2 * c₀ * (t - t₀)) * Real.exp (2 * (K : ℝ) * (t - t₀)) := by
  obtain ⟨hflow, hcontflow⟩ := S.exists_hasGlobalFlow_continuous_of_lipschitz K hlip hcont
  refine ⟨hflow, hcontflow, fun q t₀ x t ht => ?_⟩
  have hgrowth : ∀ (y : EuclideanSpace ℝ (Fin n)) (s : ℝ),
      ‖S.f q y s‖ ≤ max (2 * (K : ℝ) * ‖y‖) (2 * c₀) := by
    intro y s
    have h1 : ‖S.f q y s - S.f q 0 s‖ ≤ (K : ℝ) * ‖y‖ := by
      simpa [dist_eq_norm] using (hlip q s).dist_le_mul y 0
    have h2 : ‖S.f q y s‖ ≤ (K : ℝ) * ‖y‖ + c₀ := by
      have h4 := norm_le_norm_add_norm_sub' (S.f q y s) (S.f q 0 s)
      have h3 := hbdd q s
      linarith
    rcases le_total c₀ ((K : ℝ) * ‖y‖) with hc | hc
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (by linarith)
  have hfcont : Continuous fun s => S.f q (hflow.flow t₀ q x s) s :=
    (hcont q).comp (continuous_id.prodMk (hcontflow t₀ q x))
  have key := S.flow_norm_le_growthEnvelope hflow (fun _ => 2 * (K : ℝ)) continuous_const
    (fun _ => by positivity) (2 * c₀) (by positivity) t₀ q x hgrowth hfcont t ht
  have hint : (∫ _r in Set.Icc t₀ t, 2 * (K : ℝ)) = 2 * (K : ℝ) * (t - t₀) := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc,
      max_eq_left (by linarith : (0 : ℝ) ≤ t - t₀)]
    simp [mul_comm]
  rw [SHS.growthEnvelope, hint] at key
  exact key

end

end
