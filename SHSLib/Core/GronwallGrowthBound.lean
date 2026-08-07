/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Time-varying Grönwall bound and Hespanha's Lemma 1 (Eq. 35)

Companion to `SHSLib.Core.Generator`.

`SHSLib.Core.Generator` proves `SHS.lemma1_linear_growth_bound`, the sample-path
growth bound of Hespanha (2005), Lemma 1, for a *constant* linear-growth rate
`K ≥ 0` (via Mathlib's `gronwallBound`).  The paper states the bound with a
*time-varying* rate `γ_f(t)`, in the form

  `‖x(t)‖ ≤ e^{∫_{t₀}^{t} γ_f(r) dr} · max{‖x₀‖, c_f/γ_f(t₀), c_φ}`  (Eq. 35),

which is false as literally formalized (see
`SHS.lemma1_linear_growth_bound_false` in `SHSLib.Core.Generator`: the term
`c_f/γ_f(t₀)` degenerates when `γ_f(t₀) = 0`).  This file supplies the robust,
true sum-form replacement with a time-varying rate,

  `‖x(t)‖ ≤ (‖x₀‖ + c_f·(t − t₀)) · e^{∫_{t₀}^{t} γ_f(r) dr}`,

together with the general real-analysis ingredient it rests on, a Grönwall
inequality with time-varying coefficient (`gronwall_varying_rate`), which is not
available in Mathlib (Mathlib's `gronwallBound` API assumes a constant rate).
-/
import SHSLib.Core.Generator

open MeasureTheory Topology Filter

noncomputable section

/-! ## A Grönwall inequality with time-varying rate

Mathlib's Grönwall API (`gronwallBound`, `norm_le_gronwallBound_of_norm_deriv_right_le`)
covers the constant-rate inequality `u' ≤ K·u + ε`.  The statement below is the
integral form with a *variable* rate `γ(s) ≥ 0`.
-/

/-- **Grönwall's inequality with a time-varying rate (integral form).**

If `u` is continuous, `γ ≥ 0` is continuous, `c ≥ 0`, and

  `u t ≤ δ + ∫_a^t (γ(s)·u(s) + c) ds`  for all `t ∈ [a, b]`,

then

  `u t ≤ (δ + c·(t − a))·exp(∫_a^t γ(s) ds)`  for all `t ∈ [a, b]`.

The proof compares `u` with `v t = δ + ∫_a^t (γ u + c)`, which satisfies
`v' = γ u + c ≤ γ v + c`, and shows that `t ↦ δ + c(t−a) − e^{−∫_a^t γ}·v t`
is monotone on `[a, b]` and vanishes at `a`. -/
theorem gronwall_varying_rate
    {u gam : ℝ → ℝ} {a b delta c : ℝ}
    (hu : Continuous u) (hgam : Continuous gam) (hgam0 : ∀ s, 0 ≤ gam s)
    (hc : 0 ≤ c)
    (hint : ∀ t ∈ Set.Icc a b, u t ≤ delta + ∫ s in a..t, (gam s * u s + c)) :
    ∀ t ∈ Set.Icc a b, u t ≤ (delta + c * (t - a)) * Real.exp (∫ s in a..t, gam s) := by
  set F : ℝ → ℝ := fun s => gam s * u s + c with hF
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
  have hGpos : ∀ t, 0 < G t := fun t => Real.exp_pos _
  have hGle : ∀ t, a ≤ t → G t ≤ 1 := by
    intro t ht
    rw [hG]
    simp only [Real.exp_le_one_iff, neg_nonpos]
    rw [intervalIntegral.integral_of_le ht]
    exact setIntegral_nonneg measurableSet_Ioc fun s _ => hgam0 s
  set H : ℝ → ℝ := fun t => delta + c * (t - a) - G t * v t with hH
  have hH_deriv : ∀ t, HasDerivAt H (c - ((-gam t * G t) * v t + G t * F t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => delta + c * (t - a)) c t := by
      simpa using (((hasDerivAt_id t).sub_const a).const_mul c).const_add delta
    exact h1.sub ((hG_deriv t).mul (hv_deriv t))
  have hHmono : MonotoneOn H (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact Continuous.continuousOn (by fun_prop)
    · intro t _
      exact (hH_deriv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hH_deriv t).deriv]
      have hut : u t ≤ v t := hint t ⟨ht.1.le, ht.2.le⟩
      have h1 : c - ((-gam t * G t) * v t + G t * F t)
          = c * (1 - G t) + gam t * G t * (v t - u t) := by
        simp only [hF]; ring
      rw [h1]
      have hG1 := hGle t ht.1.le
      have h2 : 0 ≤ c * (1 - G t) := mul_nonneg hc (by linarith)
      have h3 : 0 ≤ gam t * G t * (v t - u t) :=
        mul_nonneg (mul_nonneg (hgam0 t) (hGpos t).le) (by linarith)
      linarith
  intro t ht
  have hHa : H a = 0 := by simp [hH, hG, hv]
  have h4 : 0 ≤ H t := by
    have := hHmono (Set.left_mem_Icc.2 (ht.1.trans ht.2)) ht ht.1
    linarith [hHa]
  have hut : u t ≤ v t := hint t ht
  have h5 : G t * v t ≤ delta + c * (t - a) := by
    simp only [hH] at h4; linarith
  have hGinv : (G t)⁻¹ = Real.exp (∫ s in a..t, gam s) := by
    rw [hG, ← Real.exp_neg]; ring_nf
  calc u t ≤ v t := hut
    _ = (G t)⁻¹ * (G t * v t) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hGpos t)), one_mul]
    _ ≤ (G t)⁻¹ * (delta + c * (t - a)) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = (delta + c * (t - a)) * Real.exp (∫ s in a..t, gam s) := by rw [hGinv]; ring

/-! ## Continuity of primitives and of the flow -/

/-- The primitive `s ↦ ∫_{[a,s]} f` of a continuous function is continuous.
(For `s < a` the set `[a,s]` is empty, so the primitive is constant there.) -/
theorem continuous_setIntegral_Icc_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Continuous f) (a : ℝ) :
    Continuous fun s => ∫ r in Set.Icc a s, f r := by
  have hrw : (fun s => ∫ r in Set.Icc a s, f r)
      = fun s => if a ≤ s then ∫ r in a..s, f r else 0 := by
    refine funext fun s => ?_
    by_cases hs : a ≤ s
    · simp [hs, MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hs]
    · have hempty : Set.Icc a s = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith [not_le.mp hs])
      rw [hempty]
      simp [hs]
  rw [hrw]
  refine Continuous.if_le ?_ continuous_const continuous_const continuous_id ?_
  · exact intervalIntegral.continuous_primitive (fun _ _ => hf.intervalIntegrable _ _) a
  · intro s hs
    simp [← hs, intervalIntegral.integral_same]

/-- If the drift evaluated along the trajectory is continuous in time, then the
flow `t ↦ φ(t; t₀, q₀, x₀)` is continuous.  (Immediate from the integral form
`HasGlobalFlow.flow_ode` of the flow equation and the fundamental theorem of
calculus.) -/
theorem SHS.HasGlobalFlow.continuous_flow
    {Q : Type*} {n m : ℕ} {S : SHS Q n m} (hflow : S.HasGlobalFlow)
    (t₀ : ℝ) (q₀ : Q) (x₀ : EuclideanSpace ℝ (Fin n))
    (hf_cont : Continuous fun s => S.f q₀ (hflow.flow t₀ q₀ x₀ s) s) :
    Continuous (hflow.flow t₀ q₀ x₀) := by
  set f' : ℝ → EuclideanSpace ℝ (Fin n) := fun s => S.f q₀ (hflow.flow t₀ q₀ x₀ s) s with hf'
  have hg : hflow.flow t₀ q₀ x₀ = fun τ => x₀ + ∫ s in Set.Icc t₀ τ, f' s :=
    funext fun τ => hflow.flow_ode t₀ q₀ x₀ τ
  rw [hg]
  exact continuous_const.add (continuous_setIntegral_Icc_left hf_cont t₀)

/-! ## The Grönwall growth envelope -/

/-- The Grönwall growth envelope `(A + c_f·(s − t₀))·exp(∫_{t₀}^{s} γ_f)`:
the bound that Hespanha's Lemma 1 (Eq. 35) places on the sample paths, in its
robust sum form, for a trajectory started at time `t₀` from a state of norm at
most `A`. -/
def SHS.growthEnvelope (gamma_f : ℝ → ℝ) (c_f A t₀ s : ℝ) : ℝ :=
  (A + c_f * (s - t₀)) * Real.exp (∫ r in Set.Icc t₀ s, gamma_f r)

namespace SHS

variable {gamma_f : ℝ → ℝ} {c_f A t₀ : ℝ}

/-- The envelope dominates its own initial value `A` (for `s ≥ t₀`, `γ_f ≥ 0`,
`c_f ≥ 0`, `A ≥ 0`). -/
theorem le_growthEnvelope (hgamma_nonneg : ∀ t, 0 ≤ gamma_f t) (hc_f : 0 ≤ c_f)
    (hA : 0 ≤ A) {s : ℝ} (hs : t₀ ≤ s) :
    A ≤ growthEnvelope gamma_f c_f A t₀ s := by
  have hexp : 1 ≤ Real.exp (∫ r in Set.Icc t₀ s, gamma_f r) := by
    rw [Real.one_le_exp_iff]
    exact setIntegral_nonneg measurableSet_Icc fun r _ => hgamma_nonneg r
  have h1 : 0 ≤ c_f * (s - t₀) := mul_nonneg hc_f (by linarith)
  calc A = A * 1 := (mul_one A).symm
    _ ≤ (A + c_f * (s - t₀)) * Real.exp (∫ r in Set.Icc t₀ s, gamma_f r) := by
        apply mul_le_mul (by linarith) hexp zero_le_one (by linarith)

/-- The envelope is a continuous function of time — this is what makes the
sample-path bound an instance of “bounded by a continuous function”
(Assumption 2(ii) of Hespanha, 2005). -/
theorem continuous_growthEnvelope (hgamma_cont : Continuous gamma_f) :
    Continuous (growthEnvelope gamma_f c_f A t₀) := by
  unfold growthEnvelope
  exact (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).mul
    (Real.continuous_exp.comp (continuous_setIntegral_Icc_left hgamma_cont t₀))

/-- The envelope is nondecreasing in time on `[t₀, ∞)`. -/
theorem growthEnvelope_monotoneOn (hgamma_cont : Continuous gamma_f)
    (hgamma_nonneg : ∀ t, 0 ≤ gamma_f t) (hc_f : 0 ≤ c_f) (hA : 0 ≤ A) :
    MonotoneOn (growthEnvelope gamma_f c_f A t₀) (Set.Ici t₀) := by
  intro a ha b hb hab
  have hta : t₀ ≤ a := ha
  have hIcc : ∀ {x y : ℝ}, x ≤ y →
      ∫ r in Set.Icc x y, gamma_f r = ∫ r in x..y, gamma_f r := by
    intro x y hxy
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hxy]
  have hadd : (∫ r in Set.Icc t₀ a, gamma_f r) + (∫ r in Set.Icc a b, gamma_f r)
      = ∫ r in Set.Icc t₀ b, gamma_f r := by
    rw [hIcc hta, hIcc hab, hIcc (hta.trans hab)]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hgamma_cont.intervalIntegrable _ _) (hgamma_cont.intervalIntegrable _ _)
  have hmid : (0:ℝ) ≤ ∫ r in Set.Icc a b, gamma_f r :=
    setIntegral_nonneg measurableSet_Icc fun r _ => hgamma_nonneg r
  have hexp : Real.exp (∫ r in Set.Icc t₀ a, gamma_f r)
      ≤ Real.exp (∫ r in Set.Icc t₀ b, gamma_f r) := by
    apply Real.exp_le_exp.2
    linarith
  have hlin : A + c_f * (a - t₀) ≤ A + c_f * (b - t₀) := by nlinarith
  have hnn : (0:ℝ) ≤ A + c_f * (a - t₀) := by nlinarith
  exact mul_le_mul hlin hexp (Real.exp_pos _).le (by linarith)

/-- Composition property of the envelope: restarting the Grönwall estimate at an
intermediate time `a` from the value `growthEnvelope … a` never exceeds the
envelope at the later time `b`. -/
theorem growthEnvelope_restart (hgamma_cont : Continuous gamma_f)
    (hgamma_nonneg : ∀ t, 0 ≤ gamma_f t) (hc_f : 0 ≤ c_f)
    {a b : ℝ} (hta : t₀ ≤ a) (hab : a ≤ b) :
    (growthEnvelope gamma_f c_f A t₀ a + c_f * (b - a)) *
        Real.exp (∫ r in Set.Icc a b, gamma_f r)
      ≤ growthEnvelope gamma_f c_f A t₀ b := by
  have hIcc : ∀ {x y : ℝ}, x ≤ y →
      ∫ r in Set.Icc x y, gamma_f r = ∫ r in x..y, gamma_f r := by
    intro x y hxy
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hxy]
  have hadd : (∫ r in Set.Icc t₀ a, gamma_f r) + (∫ r in Set.Icc a b, gamma_f r)
      = ∫ r in Set.Icc t₀ b, gamma_f r := by
    rw [hIcc hta, hIcc hab, hIcc (hta.trans hab)]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hgamma_cont.intervalIntegrable _ _) (hgamma_cont.intervalIntegrable _ _)
  have h1 : 1 ≤ Real.exp (∫ r in Set.Icc t₀ a, gamma_f r) := by
    rw [Real.one_le_exp_iff]
    exact setIntegral_nonneg measurableSet_Icc fun r _ => hgamma_nonneg r
  have hcb : 0 ≤ c_f * (b - a) := mul_nonneg hc_f (by linarith)
  have hexp2 : 0 < Real.exp (∫ r in Set.Icc a b, gamma_f r) := Real.exp_pos _
  have hstep : growthEnvelope gamma_f c_f A t₀ a + c_f * (b - a)
      ≤ (A + c_f * (b - t₀)) * Real.exp (∫ r in Set.Icc t₀ a, gamma_f r) := by
    have : c_f * (b - a) ≤ c_f * (b - a) * Real.exp (∫ r in Set.Icc t₀ a, gamma_f r) := by
      nlinarith
    simp only [growthEnvelope]
    nlinarith [this]
  calc (growthEnvelope gamma_f c_f A t₀ a + c_f * (b - a)) *
        Real.exp (∫ r in Set.Icc a b, gamma_f r)
      ≤ ((A + c_f * (b - t₀)) * Real.exp (∫ r in Set.Icc t₀ a, gamma_f r)) *
          Real.exp (∫ r in Set.Icc a b, gamma_f r) :=
        mul_le_mul_of_nonneg_right hstep hexp2.le
    _ = growthEnvelope gamma_f c_f A t₀ b := by
        simp only [growthEnvelope]
        rw [mul_assoc, ← Real.exp_add, hadd]

end SHS

/-! ## Lemma 1 with a time-varying growth rate -/

/-- **The flow segment bound.**

If the drift obeys the linear-growth bound `‖f(q₀,x,t)‖ ≤ max (γ_f(t)·‖x‖) c_f`
with `γ_f ≥ 0` continuous and `c_f ≥ 0`, and the drift along the trajectory is
continuous in time, then for all `t ≥ t₀`

  `‖φ(t; t₀,q₀,x₀)‖ ≤ (‖x₀‖ + c_f·(t − t₀))·exp(∫_{t₀}^{t} γ_f(r) dr)`,

i.e. the flow stays below the Grönwall envelope started at `‖x₀‖`. -/
theorem SHS.flow_norm_le_growthEnvelope
    {Q : Type*} {n m : ℕ}
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (gamma_f : ℝ → ℝ) (hgamma_cont : Continuous gamma_f) (hgamma_nonneg : ∀ t, 0 ≤ gamma_f t)
    (c_f : ℝ) (hc_f : 0 ≤ c_f)
    (t₀ : ℝ) (q₀ : Q) (x₀ : EuclideanSpace ℝ (Fin n))
    (hf_growth : ∀ x t, ‖S.f q₀ x t‖ ≤ max (gamma_f t * ‖x‖) c_f)
    (hf_cont : Continuous fun s => S.f q₀ (hflow.flow t₀ q₀ x₀ s) s)
    (t : ℝ) (ht : t₀ ≤ t) :
    ‖hflow.flow t₀ q₀ x₀ t‖ ≤ SHS.growthEnvelope gamma_f c_f ‖x₀‖ t₀ t := by
  set g : ℝ → EuclideanSpace ℝ (Fin n) := hflow.flow t₀ q₀ x₀ with hgdef
  set f' : ℝ → EuclideanSpace ℝ (Fin n) := fun s => S.f q₀ (g s) s with hf'
  have hg_cont : Continuous g := hflow.continuous_flow _ _ _ hf_cont
  have hu_cont : Continuous fun s => ‖g s‖ := hg_cont.norm
  -- pointwise linear-growth bound along the trajectory
  have hbound : ∀ s, ‖f' s‖ ≤ gamma_f s * ‖g s‖ + c_f := by
    intro s
    refine (hf_growth (g s) s).trans (max_le ?_ ?_)
    · linarith
    · linarith [mul_nonneg (hgamma_nonneg s) (norm_nonneg (g s))]
  -- the integral inequality feeding Grönwall
  have hint : ∀ τ ∈ Set.Icc t₀ t,
      ‖g τ‖ ≤ ‖x₀‖ + ∫ s in t₀..τ, (gamma_f s * ‖g s‖ + c_f) := by
    intro τ hτ
    have hτ0 : t₀ ≤ τ := hτ.1
    have hflow_eq : g τ = x₀ + ∫ s in t₀..τ, f' s := by
      have hode := hflow.flow_ode t₀ q₀ x₀ τ
      rw [hgdef, hode, MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hτ0]
    have hstep : ‖∫ s in t₀..τ, f' s‖ ≤ ∫ s in t₀..τ, (gamma_f s * ‖g s‖ + c_f) := by
      refine (intervalIntegral.norm_integral_le_integral_norm hτ0).trans ?_
      refine intervalIntegral.integral_mono_on hτ0 ?_ ?_ fun s _ => hbound s
      · exact hf_cont.norm.intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun s => gamma_f s * ‖g s‖ + c_f).intervalIntegrable _ _
    rw [hflow_eq]
    have := norm_add_le x₀ (∫ s in t₀..τ, f' s)
    linarith
  have key := gronwall_varying_rate (u := fun s => ‖g s‖) (gam := gamma_f)
    (a := t₀) (b := t) (delta := ‖x₀‖) (c := c_f)
    hu_cont hgamma_cont hgamma_nonneg hc_f hint t ⟨ht, le_rfl⟩
  rw [SHS.growthEnvelope, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht]
  exact key

/-- **Lemma 1** (Hespanha, 2005, Eq. 35) — sum-form bound with a *time-varying*
rate, for the continuous flow started at the initial condition `z₀`.

  `‖x(t)‖ ≤ (‖x₀‖ + c_f·(t − t₀))·exp(∫_{t₀}^{t} γ_f(r) dr)`.

This is the robust replacement for the literal (false) formalization of Eq. 35;
see `SHS.lemma1_linear_growth_bound_false` in `SHSLib.Core.Generator`.  Only the
drift governs the continuous flow, so the reset bound `c_φ` of the paper enters
only in the hybrid (with-resets) version `SHS.hybrid_path_growth_bound`. -/
theorem SHS.lemma1_linear_growth_bound_varying_rate
    {Q : Type*} {n m : ℕ}
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (gamma_f : ℝ → ℝ) (hgamma_cont : Continuous gamma_f) (hgamma_nonneg : ∀ t, 0 ≤ gamma_f t)
    (c_f : ℝ) (hc_f : 0 ≤ c_f)
    (z₀ : SHS.InitialCondition Q n)
    (hf_growth : ∀ x t, ‖S.f z₀.q₀ x t‖ ≤ max (gamma_f t * ‖x‖) c_f)
    (hf_cont : Continuous fun s => S.f z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s)
    (t : ℝ) (ht : z₀.t₀ ≤ t) :
    ‖hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ t‖ ≤
      (‖z₀.x₀‖ + c_f * (t - z₀.t₀)) *
        Real.exp (∫ r in Set.Icc z₀.t₀ t, gamma_f r) :=
  S.flow_norm_le_growthEnvelope hflow gamma_f hgamma_cont hgamma_nonneg c_f hc_f
    z₀.t₀ z₀.q₀ z₀.x₀ hf_growth hf_cont t ht

/-! ## Lemma 1 for the full hybrid sample path

Between transitions the state follows the flow; at a transition time it is
mapped by one of the reset maps `φ_ℓ`.  Under the linear-growth bounds of
Hespanha's Lemma 1 on both the drift and the resets, the *whole* sample path
stays below a single Grönwall envelope started at `max ‖x₀‖ c_φ`.
-/

/-- **Lemma 1** (Hespanha, 2005, Eq. 35) for a hybrid sample path with
transitions.

Data: transition times `tau 0 = t₀ ≤ tau 1 ≤ tau 2 ≤ …`, post-transition modes
`qs k` and states `xs k`, where `xs (k+1)` is obtained from the flow value at
`tau (k+1)` by one of the reset maps (`hjump`).  Under the drift bound
`‖f(q,x,t)‖ ≤ max (γ_f(t)‖x‖) c_f` and the reset bound
`‖φ_ℓ(q,x,t)‖ ≤ max ‖x‖ c_φ`, every point of every segment obeys

  `‖x(s)‖ ≤ (max ‖x₀‖ c_φ + c_f·(s − t₀))·exp(∫_{t₀}^{s} γ_f(r) dr)`,

so the sample path is globally bounded by a continuous function of time
(Assumption 2(ii) of the paper). -/
theorem SHS.hybrid_path_growth_bound
    {Q : Type*} {n m : ℕ}
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (gamma_f : ℝ → ℝ) (hgamma_cont : Continuous gamma_f) (hgamma_nonneg : ∀ t, 0 ≤ gamma_f t)
    (c_f : ℝ) (hc_f : 0 ≤ c_f) (c_phi : ℝ)
    (hf_growth : ∀ q x t, ‖S.f q x t‖ ≤ max (gamma_f t * ‖x‖) c_f)
    (hphi_growth : ∀ l q x t, ‖S.phi_x l q x t‖ ≤ max ‖x‖ c_phi)
    (t₀ : ℝ) (tau : ℕ → ℝ) (htau0 : tau 0 = t₀) (htau_mono : ∀ k, tau k ≤ tau (k + 1))
    (qs : ℕ → Q) (xs : ℕ → EuclideanSpace ℝ (Fin n))
    (hf_cont : ∀ k, Continuous fun s => S.f (qs k) (hflow.flow (tau k) (qs k) (xs k) s) s)
    (hjump : ∀ k, ∃ l : Fin m, xs (k + 1) =
      S.phi_x l (qs k) (hflow.flow (tau k) (qs k) (xs k) (tau (k + 1))) (tau (k + 1)))
    (k : ℕ) (s : ℝ) (hs : tau k ≤ s) :
    ‖hflow.flow (tau k) (qs k) (xs k) s‖ ≤
      SHS.growthEnvelope gamma_f c_f (max ‖xs 0‖ c_phi) t₀ s := by
  set A : ℝ := max ‖xs 0‖ c_phi with hA
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (le_max_left _ _)
  have htau_ge : ∀ j : ℕ, t₀ ≤ tau j := by
    intro j
    induction j with
    | zero => exact le_of_eq htau0.symm
    | succ j ih => exact ih.trans (htau_mono j)
  -- main induction: the post-jump state at time `tau k` is below the envelope
  have hstate : ∀ j : ℕ, ‖xs j‖ ≤ SHS.growthEnvelope gamma_f c_f A t₀ (tau j) := by
    intro j
    induction j with
    | zero =>
      rw [htau0]
      exact le_trans (le_max_left _ _)
        (SHS.le_growthEnvelope hgamma_nonneg hc_f hA0 le_rfl)
    | succ j ih =>
      obtain ⟨l, hl⟩ := hjump j
      have hseg : ‖hflow.flow (tau j) (qs j) (xs j) (tau (j + 1))‖ ≤
          SHS.growthEnvelope gamma_f c_f ‖xs j‖ (tau j) (tau (j + 1)) :=
        S.flow_norm_le_growthEnvelope hflow gamma_f hgamma_cont hgamma_nonneg c_f hc_f
          (tau j) (qs j) (xs j) (fun x t => hf_growth _ x t) (hf_cont j) _ (htau_mono j)
      have hcomp : SHS.growthEnvelope gamma_f c_f ‖xs j‖ (tau j) (tau (j + 1)) ≤
          SHS.growthEnvelope gamma_f c_f A t₀ (tau (j + 1)) := by
        have := SHS.growthEnvelope_restart (gamma_f := gamma_f) (c_f := c_f) (A := A)
          (t₀ := t₀) hgamma_cont hgamma_nonneg hc_f (htau_ge j) (htau_mono j)
        refine le_trans ?_ this
        have hexp : (0:ℝ) < Real.exp (∫ r in Set.Icc (tau j) (tau (j + 1)), gamma_f r) :=
          Real.exp_pos _
        have h2 : ‖xs j‖ + c_f * (tau (j + 1) - tau j)
            ≤ SHS.growthEnvelope gamma_f c_f A t₀ (tau j) + c_f * (tau (j + 1) - tau j) := by
          linarith [ih]
        exact mul_le_mul_of_nonneg_right h2 hexp.le
      have hphi : ‖xs (j + 1)‖ ≤
          max ‖hflow.flow (tau j) (qs j) (xs j) (tau (j + 1))‖ c_phi := by
        rw [hl]; exact hphi_growth _ _ _ _
      refine hphi.trans (max_le (hseg.trans hcomp) ?_)
      exact le_trans (le_max_right ‖xs 0‖ c_phi)
        (SHS.le_growthEnvelope hgamma_nonneg hc_f hA0 (htau_ge (j + 1)))
  -- now bound the flow on the segment starting at `tau k`
  have hseg : ‖hflow.flow (tau k) (qs k) (xs k) s‖ ≤
      SHS.growthEnvelope gamma_f c_f ‖xs k‖ (tau k) s :=
    S.flow_norm_le_growthEnvelope hflow gamma_f hgamma_cont hgamma_nonneg c_f hc_f
      (tau k) (qs k) (xs k) (fun x t => hf_growth _ x t) (hf_cont k) s hs
  refine hseg.trans ?_
  have hrestart := SHS.growthEnvelope_restart (gamma_f := gamma_f) (c_f := c_f) (A := A)
    (t₀ := t₀) hgamma_cont hgamma_nonneg hc_f (htau_ge k) hs
  refine le_trans ?_ hrestart
  have hexp : (0:ℝ) < Real.exp (∫ r in Set.Icc (tau k) s, gamma_f r) := Real.exp_pos _
  have h2 : ‖xs k‖ + c_f * (s - tau k)
      ≤ SHS.growthEnvelope gamma_f c_f A t₀ (tau k) + c_f * (s - tau k) := by
    linarith [hstate k]
  exact mul_le_mul_of_nonneg_right h2 hexp.le

/-! ## Uniqueness of the flow under a Lipschitz drift

A second standard consequence of Grönwall's inequality: solutions of the flow
equation `x(t) = x₀ + ∫_{t₀}^{t} f(q₀, x(s), s) ds` are unique forward in time
when the drift is Lipschitz in the state.  In particular the flow map recorded
in `SHS.HasGlobalFlow` is determined by the SHS data.
-/

/-- **Forward uniqueness of the flow.**  If `f(q₀, ·, t)` is `L`-Lipschitz in the
state, then two continuous solutions of the integral form of the flow equation
with the same initial value at `t₀` agree for all `t ≥ t₀`. -/
theorem SHS.flow_eq_of_lipschitz
    {Q : Type*} {n m : ℕ} (S : SHS Q n m) (q₀ : Q)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y t, ‖S.f q₀ x t - S.f q₀ y t‖ ≤ L * ‖x - y‖)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (y z : ℝ → EuclideanSpace ℝ (Fin n))
    (hy_int : Continuous fun s => S.f q₀ (y s) s)
    (hz_int : Continuous fun s => S.f q₀ (z s) s)
    (hy : ∀ t, y t = x₀ + ∫ s in Set.Icc t₀ t, S.f q₀ (y s) s)
    (hz : ∀ t, z t = x₀ + ∫ s in Set.Icc t₀ t, S.f q₀ (z s) s)
    (t : ℝ) (ht : t₀ ≤ t) :
    y t = z t := by
  have hy_cont : Continuous y := by
    rw [funext hy]
    exact continuous_const.add (continuous_setIntegral_Icc_left hy_int t₀)
  have hz_cont : Continuous z := by
    rw [funext hz]
    exact continuous_const.add (continuous_setIntegral_Icc_left hz_int t₀)
  have hu_cont : Continuous fun s => ‖y s - z s‖ := (hy_cont.sub hz_cont).norm
  have hint : ∀ τ ∈ Set.Icc t₀ t,
      ‖y τ - z τ‖ ≤ 0 + ∫ s in t₀..τ, (L * ‖y s - z s‖ + 0) := by
    intro τ hτ
    have hτ0 : t₀ ≤ τ := hτ.1
    have hdiff : y τ - z τ = ∫ s in t₀..τ, (S.f q₀ (y s) s - S.f q₀ (z s) s) := by
      rw [hy τ, hz τ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hτ0, ← intervalIntegral.integral_of_le hτ0,
        intervalIntegral.integral_sub (hy_int.intervalIntegrable _ _)
          (hz_int.intervalIntegrable _ _)]
      abel
    rw [hdiff, zero_add]
    refine (intervalIntegral.norm_integral_le_integral_norm hτ0).trans ?_
    refine intervalIntegral.integral_mono_on hτ0 ?_ ?_ fun s _ => ?_
    · exact (hy_int.sub hz_int).norm.intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun s => L * ‖y s - z s‖ + 0).intervalIntegrable _ _
    · simpa using hlip (y s) (z s) s
  have key := gronwall_varying_rate (u := fun s => ‖y s - z s‖) (gam := fun _ => L)
    (a := t₀) (b := t) (delta := 0) (c := 0)
    hu_cont continuous_const (fun _ => hL) le_rfl hint t ⟨ht, le_rfl⟩
  have hzero : ‖y t - z t‖ = 0 := le_antisymm (by simpa using key) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Any two global flows of the same SHS agree forward in time when the drift is
Lipschitz in the state: the flow map is determined by the SHS data. -/
theorem SHS.HasGlobalFlow.flow_eq_of_lipschitz
    {Q : Type*} {n m : ℕ} {S : SHS Q n m} (h₁ h₂ : S.HasGlobalFlow) (q₀ : Q)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y t, ‖S.f q₀ x t - S.f q₀ y t‖ ≤ L * ‖x - y‖)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hcont₁ : Continuous fun s => S.f q₀ (h₁.flow t₀ q₀ x₀ s) s)
    (hcont₂ : Continuous fun s => S.f q₀ (h₂.flow t₀ q₀ x₀ s) s)
    (t : ℝ) (ht : t₀ ≤ t) :
    h₁.flow t₀ q₀ x₀ t = h₂.flow t₀ q₀ x₀ t :=
  S.flow_eq_of_lipschitz q₀ L hL hlip t₀ x₀ _ _ hcont₁ hcont₂
    (h₁.flow_ode t₀ q₀ x₀) (h₂.flow_ode t₀ q₀ x₀) t ht

end
