/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharpness of the linear-growth envelope

`SHSLib.Core.GlobalFlowLinearGrowth` bounds every trajectory of a drift with
`‖f(q, x, t)‖ ≤ a + b‖x‖` by the envelope

  `linearGrowthBound a b t₀ x t = (‖x‖ + a(t − t₀))·e^{b(t−t₀)}`.

This module quantifies how much is lost in that estimate, using the explicit
flows of `SHSLib.Core.ExplicitFlows`:

* for a *radial* drift `f(q, x, t) = b·x` the envelope with `a = 0` is attained
  *exactly*, at every time and from every initial state
  (`SHS.norm_flow_eq_linearGrowthBound_of_drift_linear`);
* for a *constant* drift `f(q, x, t) = c q` the envelope with `b = 0` is
  attained exactly at the states that point along `c q`, and is strict
  otherwise (`SHS.norm_flow_constDrift_eq_iff_sameRay`,
  `SHS.norm_flow_constDrift_lt_of_not_sameRay`);
* whenever the exponential factor is switched on (`b > 0`) and the drift does
  not vanish, the envelope is strictly larger than the true norm
  (`SHS.norm_flow_constDrift_lt_linearGrowthBound`).
-/
import SHSLib.Core.ExplicitFlows

open Metric Set

noncomputable section

variable {Q : Type*} {n m : ℕ}

/-- **The envelope is attained by a radial drift.**  If `f(q, x, t) = b·x` then
every trajectory satisfies `‖φ(t)‖ = linearGrowthBound 0 b t₀ x t` exactly (the
sign of `b` is irrelevant for the identity; for `b ≥ 0` this is the envelope of
`SHS.exists_hasGlobalFlow_of_linear_growth` with `a = 0`). -/
theorem SHS.norm_flow_eq_linearGrowthBound_of_drift_linear (S : SHS Q n m) {b : ℝ}
    (hf : ∀ q x t, S.f q x t = b • x) (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q)
    (x : EuclideanSpace ℝ (Fin n)) (hc : Continuous (hflow.flow t₀ q x))
    (t : ℝ) (ht : t₀ ≤ t) :
    ‖hflow.flow t₀ q x t‖ = ODEFlow.linearGrowthBound 0 b t₀ x t := by
  rw [S.flow_eq_linearDriftFlow (fun _ => b) hf hflow t₀ q x hc t ht, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ODEFlow.linearGrowthBound]
  ring

/-- The trajectory of a constant drift, in a form ready for the triangle
inequality. -/
theorem SHS.flow_constDrift_norm (S : SHS Q n m) (c : Q → EuclideanSpace ℝ (Fin n))
    (hf : ∀ q x t, S.f q x t = c q) (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q)
    (x : EuclideanSpace ℝ (Fin n)) (hc : Continuous (hflow.flow t₀ q x))
    (t : ℝ) (ht : t₀ ≤ t) :
    ‖hflow.flow t₀ q x t‖ = ‖x + (t - t₀) • c q‖ := by
  rw [S.flow_eq_constDriftFlow c hf hflow t₀ q x hc t ht]

/-- **The envelope of a constant drift is attained exactly along the drift.**
With `a = ‖c q‖` and `b = 0` the bound `‖φ(t)‖ ≤ ‖x‖ + ‖c q‖(t − t₀)` is an
equality iff the initial state points along the drift. -/
theorem SHS.norm_flow_constDrift_eq_iff_sameRay (S : SHS Q n m)
    (c : Q → EuclideanSpace ℝ (Fin n)) (hf : ∀ q x t, S.f q x t = c q)
    (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (hc : Continuous (hflow.flow t₀ q x)) (t : ℝ) (ht : t₀ ≤ t) :
    ‖hflow.flow t₀ q x t‖ = ODEFlow.linearGrowthBound ‖c q‖ 0 t₀ x t
      ↔ SameRay ℝ x ((t - t₀) • c q) := by
  have hnorm : ‖(t - t₀) • c q‖ = ‖c q‖ * (t - t₀) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    ring
  rw [S.flow_constDrift_norm c hf hflow t₀ q x hc t ht, ODEFlow.linearGrowthBound,
    sameRay_iff_norm_add, hnorm]
  constructor
  · intro h; rw [h]; simp [mul_comm]
  · intro h; rw [h]; simp [mul_comm]

/-- A state that does not point along the drift stays strictly inside the
envelope. -/
theorem SHS.norm_flow_constDrift_lt_of_not_sameRay (S : SHS Q n m)
    (c : Q → EuclideanSpace ℝ (Fin n)) (hf : ∀ q x t, S.f q x t = c q)
    (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (hc : Continuous (hflow.flow t₀ q x)) (t : ℝ) (ht : t₀ ≤ t)
    (hray : ¬ SameRay ℝ x ((t - t₀) • c q)) :
    ‖hflow.flow t₀ q x t‖ < ODEFlow.linearGrowthBound ‖c q‖ 0 t₀ x t := by
  have hle : ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound ‖c q‖ 0 t₀ x t := by
    have hnorm : ‖(t - t₀) • c q‖ = ‖c q‖ * (t - t₀) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      ring
    rw [S.flow_constDrift_norm c hf hflow t₀ q x hc t ht, ODEFlow.linearGrowthBound]
    refine (norm_add_le _ _).trans ?_
    rw [hnorm]
    simp [mul_comm]
  refine lt_of_le_of_ne hle ?_
  intro heq
  exact hray ((S.norm_flow_constDrift_eq_iff_sameRay c hf hflow t₀ q x hc t ht).1 heq)

/-- **Strictness of the exponential factor.**  As soon as `b > 0`, the drift is
constant and nonzero and time has advanced, the envelope strictly overestimates
the trajectory. -/
theorem SHS.norm_flow_constDrift_lt_linearGrowthBound (S : SHS Q n m)
    (c : Q → EuclideanSpace ℝ (Fin n)) (hf : ∀ q x t, S.f q x t = c q)
    (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (hc : Continuous (hflow.flow t₀ q x)) {b : ℝ} (hb : 0 < b) (hcq : c q ≠ 0)
    (t : ℝ) (ht : t₀ < t) :
    ‖hflow.flow t₀ q x t‖ < ODEFlow.linearGrowthBound ‖c q‖ b t₀ x t := by
  have hcpos : 0 < ‖c q‖ := norm_pos_iff.2 hcq
  have hnorm : ‖(t - t₀) • c q‖ = ‖c q‖ * (t - t₀) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    ring
  have hle : ‖hflow.flow t₀ q x t‖ ≤ ‖x‖ + ‖c q‖ * (t - t₀) := by
    rw [S.flow_constDrift_norm c hf hflow t₀ q x hc t ht.le]
    refine (norm_add_le _ _).trans ?_
    rw [hnorm]
  have hpos : 0 < ‖x‖ + ‖c q‖ * (t - t₀) := by
    have : 0 < ‖c q‖ * (t - t₀) := mul_pos hcpos (by linarith)
    linarith [norm_nonneg x]
  have hexp : 1 < Real.exp (b * (t - t₀)) :=
    Real.one_lt_exp_iff.2 (mul_pos hb (by linarith))
  calc ‖hflow.flow t₀ q x t‖ ≤ ‖x‖ + ‖c q‖ * (t - t₀) := hle
    _ < (‖x‖ + ‖c q‖ * (t - t₀)) * Real.exp (b * (t - t₀)) := by
        nlinarith
    _ = ODEFlow.linearGrowthBound ‖c q‖ b t₀ x t := by
        rw [ODEFlow.linearGrowthBound]

end
