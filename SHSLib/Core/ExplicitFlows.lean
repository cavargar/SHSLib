/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Explicit flows for the two simplest drifts

Assumption 1 of Hespanha (2005) — the existence of a global flow
(`SHS.HasGlobalFlow`) — is a hypothesis in most of the library.  For a model
whose drift is *constant* in the state, or a *scalar multiple of the state*, the
flow can be written down, so the assumption becomes a theorem.  Both cases occur
repeatedly among the example models (counting processes with no continuous
dynamics, constant-growth models, exponentially relaxing excitation variables).

This module packages the two constructions once and for all, together with the
regularity they need to be recognised as *the* flow:

* `SHS.constDriftFlow` / `SHS.hasGlobalFlow_of_drift_const` — for
  `f(q, x, t) = c q` the flow is `x + (t − t₀)⁺ · c q`;
* `SHS.linearDriftFlow` / `SHS.hasGlobalFlow_of_drift_linear` — for
  `f(q, x, t) = r q · x` the flow is `e^{r q (t − t₀)⁺} · x`;
* the drift hypotheses of the linear-growth theory (joint continuity, Lipschitz
  on balls, linear growth) for both; and
* the resulting uniqueness statements `SHS.flow_eq_constDriftFlow` and
  `SHS.flow_eq_linearDriftFlow`: any global flow with continuous trajectories is
  the explicit one.
-/
import SHSLib.Core.FlowRegularityLinearGrowth

open MeasureTheory Metric Set

open scoped NNReal

noncomputable section

section

variable {Q : Type*} {n m : ℕ} {S : SHS Q n m}

/-- The integral of a constant vector over `[t₀, t]`. -/
lemma integral_Icc_const_vec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (t₀ t : ℝ) (v : E) :
    (∫ _s in Set.Icc t₀ t, v) = max 0 (t - t₀) • v := by
  rw [MeasureTheory.setIntegral_const, Measure.real, Real.volume_Icc]
  rcases le_or_gt t₀ t with h | h
  · rw [max_eq_right (by linarith), ENNReal.toReal_ofReal (by linarith)]
  · rw [max_eq_left (by linarith), ENNReal.ofReal_eq_zero.2 (by linarith)]
    simp

/-! ## Constant drift -/

/-- The flow of a drift that does not depend on the state or the time:
`φ(t; t₀, q, x) = x + (t − t₀)⁺ · c q`. -/
def SHS.constDriftFlow (c : Q → EuclideanSpace ℝ (Fin n)) :
    ℝ → Q → EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) :=
  fun t₀ q x t => x + max 0 (t - t₀) • c q

theorem SHS.continuous_constDriftFlow (c : Q → EuclideanSpace ℝ (Fin n))
    (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (SHS.constDriftFlow c t₀ q x) := by
  unfold SHS.constDriftFlow
  fun_prop

/-- **Assumption 1 for a constant drift.** -/
def SHS.hasGlobalFlow_of_drift_const (S : SHS Q n m) (c : Q → EuclideanSpace ℝ (Fin n))
    (hf : ∀ q x t, S.f q x t = c q) : S.HasGlobalFlow where
  flow := SHS.constDriftFlow c
  flow_init := by intro t₀ q x; simp [SHS.constDriftFlow]
  flow_ode := by
    intro t₀ q x t
    simp only [SHS.constDriftFlow, hf]
    rw [integral_Icc_const_vec]

theorem SHS.constDrift_continuous (S : SHS Q n m) (c : Q → EuclideanSpace ℝ (Fin n))
    (hf : ∀ q x t, S.f q x t = c q) (q : Q) :
    Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1 := by
  simp only [hf]
  exact continuous_const

theorem SHS.constDrift_lipschitzOnBalls (S : SHS Q n m) (c : Q → EuclideanSpace ℝ (Fin n))
    (hf : ∀ q x t, S.f q x t = c q) (q : Q) :
    ODEFlow.LipschitzOnBalls fun t x => S.f q x t := by
  intro R
  refine ⟨0, fun t => LipschitzOnWith.of_dist_le_mul fun a _ b _ => ?_⟩
  simp [hf, dist_self]

theorem SHS.constDrift_growth (S : SHS Q n m) (c : Q → EuclideanSpace ℝ (Fin n))
    (hf : ∀ q x t, S.f q x t = c q) {a : ℝ} (hc : ∀ q, ‖c q‖ ≤ a)
    (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖S.f q x t‖ ≤ a + 0 * ‖x‖ := by
  rw [hf]
  simpa using hc q

/-- Any global flow of a constant-drift SHS with continuous trajectories is the
explicit one. -/
theorem SHS.flow_eq_constDriftFlow (S : SHS Q n m) (c : Q → EuclideanSpace ℝ (Fin n))
    (hf : ∀ q x t, S.f q x t = c q) (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q)
    (x : EuclideanSpace ℝ (Fin n)) (hc : Continuous (hflow.flow t₀ q x))
    (t : ℝ) (ht : t₀ ≤ t) :
    hflow.flow t₀ q x t = x + (t - t₀) • c q := by
  have hkey := hflow.flow_eq_of_lipschitzOnBalls (S.hasGlobalFlow_of_drift_const c hf) q
    (S.constDrift_continuous c hf q) (S.constDrift_lipschitzOnBalls c hf q) t₀ x hc
    (SHS.continuous_constDriftFlow c t₀ q x) t ht
  rw [hkey]
  show x + max 0 (t - t₀) • c q = _
  rw [max_eq_right (by linarith)]

/-! ## Drift proportional to the state -/

/-- The flow of a drift proportional to the state:
`φ(t; t₀, q, x) = e^{r q (t − t₀)⁺}·x`. -/
def SHS.linearDriftFlow (r : Q → ℝ) :
    ℝ → Q → EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) :=
  fun t₀ q x t => Real.exp (r q * max 0 (t - t₀)) • x

theorem SHS.continuous_linearDriftFlow (r : Q → ℝ) (t₀ : ℝ) (q : Q)
    (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (SHS.linearDriftFlow r t₀ q x) := by
  unfold SHS.linearDriftFlow
  fun_prop

/-- **Assumption 1 for a drift proportional to the state.** -/
def SHS.hasGlobalFlow_of_drift_linear (S : SHS Q n m) (r : Q → ℝ)
    (hf : ∀ q x t, S.f q x t = r q • x) : S.HasGlobalFlow where
  flow := SHS.linearDriftFlow r
  flow_init := by intro t₀ q x; simp [SHS.linearDriftFlow]
  flow_ode := by
    intro t₀ q x t
    by_cases ht : t₀ ≤ t
    · have hcongr : (∫ s in Set.Icc t₀ t, S.f q (SHS.linearDriftFlow r t₀ q x s) s)
          = ∫ s in Set.Icc t₀ t, (r q * Real.exp (r q * (s - t₀))) • x := by
        refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
        rw [hf]
        show r q • (Real.exp (r q * max 0 (s - t₀)) • x) = _
        rw [max_eq_right (by linarith [hs.1]), smul_smul]
      have hscalar : (∫ s in Set.Icc t₀ t, r q * Real.exp (r q * (s - t₀)))
          = Real.exp (r q * (t - t₀)) - 1 := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
        have hderiv : ∀ s ∈ Set.uIcc t₀ t,
            HasDerivAt (fun u => Real.exp (r q * (u - t₀)))
              (r q * Real.exp (r q * (s - t₀))) s := by
          intro s _
          have h1 : HasDerivAt (fun u : ℝ => r q * (u - t₀)) (r q) s := by
            simpa using ((hasDerivAt_id s).sub_const t₀).const_mul (r q)
          simpa [mul_comm] using h1.exp
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          ((by fun_prop : Continuous fun s : ℝ =>
            r q * Real.exp (r q * (s - t₀))).intervalIntegrable _ _)]
        simp
      rw [hcongr, integral_smul_const, hscalar, SHS.linearDriftFlow,
        max_eq_right (by linarith : (0:ℝ) ≤ t - t₀)]
      module
    · have hempty : Set.Icc t₀ t = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith [not_le.mp ht])
      rw [hempty]
      simp [SHS.linearDriftFlow, max_eq_left (by linarith [not_le.mp ht] : t - t₀ ≤ 0)]

theorem SHS.linearDrift_continuous (S : SHS Q n m) (r : Q → ℝ)
    (hf : ∀ q x t, S.f q x t = r q • x) (q : Q) :
    Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1 := by
  simp only [hf]
  exact continuous_snd.const_smul _

theorem SHS.linearDrift_lipschitzOnBalls (S : SHS Q n m) (r : Q → ℝ)
    (hf : ∀ q x t, S.f q x t = r q • x) (q : Q) :
    ODEFlow.LipschitzOnBalls fun t x => S.f q x t := by
  intro R
  refine ⟨Real.toNNReal |r q|, fun t => LipschitzOnWith.of_dist_le_mul fun u _ v _ => ?_⟩
  show ‖S.f q u t - S.f q v t‖ ≤ (Real.toNNReal |r q| : ℝ) * ‖u - v‖
  rw [hf, hf, ← smul_sub, norm_smul, Real.norm_eq_abs,
    Real.coe_toNNReal _ (abs_nonneg _)]

theorem SHS.linearDrift_growth (S : SHS Q n m) (r : Q → ℝ)
    (hf : ∀ q x t, S.f q x t = r q • x) {b : ℝ} (hr : ∀ q, |r q| ≤ b)
    (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖S.f q x t‖ ≤ 0 + b * ‖x‖ := by
  rw [hf, norm_smul, Real.norm_eq_abs, zero_add]
  exact mul_le_mul_of_nonneg_right (hr q) (norm_nonneg x)

/-- Any global flow of an SHS whose drift is proportional to the state, with
continuous trajectories, is the explicit exponential one. -/
theorem SHS.flow_eq_linearDriftFlow (S : SHS Q n m) (r : Q → ℝ)
    (hf : ∀ q x t, S.f q x t = r q • x) (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q)
    (x : EuclideanSpace ℝ (Fin n)) (hc : Continuous (hflow.flow t₀ q x))
    (t : ℝ) (ht : t₀ ≤ t) :
    hflow.flow t₀ q x t = Real.exp (r q * (t - t₀)) • x := by
  have hkey := hflow.flow_eq_of_lipschitzOnBalls (S.hasGlobalFlow_of_drift_linear r hf) q
    (S.linearDrift_continuous r hf q) (S.linearDrift_lipschitzOnBalls r hf q) t₀ x hc
    (SHS.continuous_linearDriftFlow r t₀ q x) t ht
  rw [hkey]
  show Real.exp (r q * max 0 (t - t₀)) • x = _
  rw [max_eq_right (by linarith)]

end

end
