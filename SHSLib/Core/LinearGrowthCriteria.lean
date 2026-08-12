/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convenient criteria for the hypotheses of the linear-growth existence theorem

`SHS.exists_hasGlobalFlow_of_linear_growth` asks for a drift that is jointly
continuous, `ODEFlow.LipschitzOnBalls` and of linear growth.  Checking the
middle condition by hand for every model is tedious, so this module collects
sufficient conditions:

* a globally Lipschitz drift is Lipschitz on balls, and has linear growth as
  soon as `‖f(t, 0)‖` is bounded;
* a drift that is differentiable in the state with derivative bounded on each
  ball (uniformly in time) is Lipschitz on balls;
* an affine drift `f(t, x) = A x + v t` satisfies all three conditions, giving
  the ready-made corollary `SHS.exists_hasGlobalFlow_of_affine_drift`.
-/
import SHSLib.Core.GlobalFlowLinearGrowth

open Metric Set

open scoped NNReal

noncomputable section

namespace ODEFlow

variable {n : ℕ}

/-- A globally Lipschitz drift is Lipschitz on every ball. -/
theorem lipschitzOnBalls_of_lipschitzWith
    {f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    (h : ∀ t, LipschitzWith K (f t)) : LipschitzOnBalls f :=
  fun _ => ⟨K, fun t => (h t).lipschitzOnWith⟩

/-- A globally Lipschitz drift whose value at the origin is bounded has linear
growth. -/
theorem norm_le_of_lipschitzWith
    {f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0} {c : ℝ}
    (h : ∀ t, LipschitzWith K (f t)) (h0 : ∀ t, ‖f t 0‖ ≤ c) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ‖f t x‖ ≤ c + K * ‖x‖ := by
  have hd := (h t).dist_le_mul x 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero] at hd
  have := norm_sub_norm_le (f t x) (f t 0)
  have h0' := h0 t
  linarith

/-- A drift that is differentiable in the state, with derivative bounded on each
ball uniformly in time, is Lipschitz on balls. -/
theorem lipschitzOnBalls_of_fderiv_le
    {f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hdiff : ∀ t x, DifferentiableAt ℝ (f t) x)
    (hbound : ∀ R : ℝ, ∃ C : ℝ≥0, ∀ t, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      ‖fderiv ℝ (f t) x‖₊ ≤ C) :
    LipschitzOnBalls f := by
  intro R
  obtain ⟨C, hC⟩ := hbound R
  exact ⟨C, fun t => Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => hdiff t x) (hC t) (convex_closedBall 0 R)⟩

/-- An affine drift `f(t, x) = A x + v t` is Lipschitz on balls. -/
theorem lipschitzOnBalls_affine
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : ℝ → EuclideanSpace ℝ (Fin n)) :
    LipschitzOnBalls fun t x => A x + v t := by
  refine lipschitzOnBalls_of_lipschitzWith (K := ‖A‖₊) fun t => ?_
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub]
  exact A.le_opNorm _

/-- Linear growth for an affine drift. -/
theorem norm_affine_le
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : ℝ → EuclideanSpace ℝ (Fin n)) {a b : ℝ}
    (hA : ‖A‖ ≤ b) (hv : ∀ t, ‖v t‖ ≤ a) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖A x + v t‖ ≤ a + b * ‖x‖ := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖A x‖ ≤ b * ‖x‖ :=
    le_trans (A.le_opNorm x) (mul_le_mul_of_nonneg_right hA (norm_nonneg x))
  have h2 := hv t
  linarith

end ODEFlow

/-- **Global flow for an affine drift.**  If the drift of `S` is affine in the
state, `f(q, x, t) = A q x + v q t`, with the linear parts uniformly bounded by
`b`, the offsets uniformly bounded by `a` and continuous in time, then `S` has a
global flow with continuous trajectories obeying the envelope
`(‖x‖ + a(t − t₀))·e^{b(t−t₀)}`. -/
theorem SHS.exists_hasGlobalFlow_of_affine_drift
    {Q : Type*} {n m : ℕ} (S : SHS Q n m)
    (A : Q → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (v : Q → ℝ → EuclideanSpace ℝ (Fin n))
    (hf : ∀ q x t, S.f q x t = A q x + v q t)
    (hvc : ∀ q, Continuous (v q))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ q, ‖A q‖ ≤ b) (hv : ∀ q t, ‖v q t‖ ≤ a) :
    ∃ hflow : S.HasGlobalFlow, (∀ t₀ q x, Continuous (hflow.flow t₀ q x)) ∧
      ∀ (q : Q) (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), t₀ ≤ t →
        ‖hflow.flow t₀ q x t‖ ≤ ODEFlow.linearGrowthBound a b t₀ x t := by
  have hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1 := by
    intro q
    simp only [hf]
    exact ((A q).continuous.comp continuous_snd).add ((hvc q).comp continuous_fst)
  have hlip : ∀ q, ODEFlow.LipschitzOnBalls fun t x => S.f q x t := by
    intro q
    have := ODEFlow.lipschitzOnBalls_affine (A q) (v q)
    simpa [hf] using this
  exact S.exists_hasGlobalFlow_of_linear_growth hcont hlip a b ha hb
    (fun q x t => by rw [hf]; exact ODEFlow.norm_affine_le (A q) (v q) (hA q) (hv q) t x)

end
