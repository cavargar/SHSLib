/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Global existence of the flow of an SHS with a Lipschitz drift

`SHSLib.Core.Basic` records the existence of a globally defined flow of the
continuous dynamics as a *hypothesis*, the structure `SHS.HasGlobalFlow`.
`SHSLib.Core.GronwallGrowthBound` shows that such a flow is unique forward in
time when the drift is Lipschitz in the state.

This module supplies the missing companion existence statement: if the drift
`f(q, ·, t)` is globally Lipschitz in the state with a constant independent of
`(q, t)`, and is jointly continuous in `(t, x)`, then a global flow *exists*, so
`SHS.HasGlobalFlow` becomes a theorem rather than an assumption for that model
class.

The construction is a Picard–Lindelöf argument iterated over a *uniform* time
step.  Mathlib's `IsPicardLindelof` gives a solution on a time interval whose
length is controlled by the size of a ball on which the drift is bounded; for a
globally Lipschitz drift the admissible step length `h` can be chosen once and
for all (`h ≤ 1/(2K)`), because enlarging the ball around the current state
enlarges the drift bound only linearly.  Solutions on consecutive steps are
glued, and Grönwall's inequality (`ODEFlow.integral_solution_unique`) shows that
the resulting family is coherent, so it assembles into a single solution defined
for all times.

## Main results

* `ODEFlow.exists_solution_step` — solvability of the integral equation on one
  step `[c, c + h]`, for any starting value.
* `ODEFlow.integral_solution_unique` — Grönwall uniqueness for the integral
  equation on `[t₀, T]`.
* `ODEFlow.exists_global_solution` — a solution of `x(t) = x₀ + ∫_{t₀}^{t} f`
  defined for all `t ≥ t₀` (and constant before `t₀`).
* `SHS.exists_hasGlobalFlow_of_lipschitz` — every SHS with a globally Lipschitz,
  jointly continuous drift has a global flow.
-/
import SHSLib.Core.GronwallGrowthBound
import Mathlib.Analysis.ODE.PicardLindelof

open MeasureTheory Metric Set Topology Filter

open scoped NNReal

noncomputable section

namespace ODEFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The integrand `s ↦ f s (u s)` of the Picard equation is continuous whenever
the curve `u` is. -/
theorem continuous_comp_curve {f : ℝ → E → E}
    (hcont : Continuous fun p : ℝ × E => f p.1 p.2) {u : ℝ → E} (hu : Continuous u) :
    Continuous fun s => f s (u s) :=
  hcont.comp (continuous_id.prodMk hu)

/-- **One Picard–Lindelöf step.**  If `f` is globally `K`-Lipschitz in the state
and jointly continuous, then for any starting time `c`, starting value `y` and
step `h` with `K·h ≤ 1/2`, the integral equation `γ t = y + ∫_c^t f s (γ s) ds`
has a continuous solution on `[c, c + h]` (extended to a globally continuous
curve that is constant, equal to `y`, before `c`). -/
theorem exists_solution_step (f : ℝ → E → E) (K : ℝ≥0)
    (hlip : ∀ t, LipschitzWith K (f t))
    (hcont : Continuous fun p : ℝ × E => f p.1 p.2)
    (c : ℝ) (y : E) (h : ℝ) (hh : 0 < h) (hKh : (K : ℝ) * h ≤ 1 / 2) :
    ∃ γ : ℝ → E, Continuous γ ∧ (∀ t ≤ c, γ t = y) ∧
      ∀ t ∈ Icc c (c + h), γ t = y + ∫ s in c..t, f s (γ s) := by
  have hch : c ≤ c + h := by linarith
  -- a bound for the drift at the starting value over the step
  obtain ⟨tm, htm, hmax⟩ := (isCompact_Icc (a := c) (b := c + h)).exists_isMaxOn
    ⟨c, left_mem_Icc.2 hch⟩ (f := fun t => ‖f t y‖)
    ((hcont.comp (continuous_id.prodMk continuous_const)).norm).continuousOn
  set M : ℝ := ‖f tm y‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  -- the radius of the ball on which the Picard–Lindelöf conditions are checked
  set R : ℝ := 2 * (M + 1) * h with hR
  have hR0 : 0 ≤ R := by positivity
  set L : ℝ := M + (K : ℝ) * R with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof f (⟨c, left_mem_Icc.2 hch⟩ : Icc c (c + h)) y
      ⟨R, hR0⟩ 0 ⟨L, hL0⟩ K := by
    constructor
    · exact fun t _ => (hlip t).lipschitzOnWith
    · exact fun x _ => (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro t ht x hx
      have h1 : ‖f t y‖ ≤ M := hmax ht
      have h2 : dist (f t x) (f t y) ≤ (K : ℝ) * dist x y := (hlip t).dist_le_mul x y
      have h3 : dist x y ≤ R := by simpa [dist_eq_norm] using hx
      have h0 : ‖f t x‖ ≤ ‖f t y‖ + ‖f t x - f t y‖ := by
        simpa using norm_le_norm_add_norm_sub' (f t x) (f t y)
      simp only [NNReal.coe_mk]
      have h4 : ‖f t x - f t y‖ ≤ (K : ℝ) * R := by
        rw [← dist_eq_norm]
        exact h2.trans (by nlinarith [K.coe_nonneg])
      linarith
    · simp only [NNReal.coe_mk, NNReal.coe_zero, sub_zero, add_sub_cancel_left, sub_self]
      rw [max_eq_left hh.le]
      nlinarith [K.coe_nonneg]
  obtain ⟨β, hβ0, hβ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (mem_closedBall_self (by simp))
  have hβcont : ContinuousOn β (Icc c (c + h)) := fun t ht => (hβ t ht).continuousWithinAt
  -- clamp the time to the step, so that the solution extends to a global curve
  set cl : ℝ → ℝ := fun t => max c (min t (c + h)) with hcl
  have hcl_cont : Continuous cl := by fun_prop
  have hcl_mem : ∀ t, cl t ∈ Icc c (c + h) := fun t =>
    ⟨le_max_left _ _, max_le hch (min_le_right _ _)⟩
  have hcl_eq : ∀ t ∈ Icc c (c + h), cl t = t := by
    intro t ht
    simp [hcl, min_eq_left ht.2, max_eq_right ht.1]
  refine ⟨fun t => β (cl t), hβcont.comp_continuous hcl_cont hcl_mem, ?_, ?_⟩
  · intro t ht
    have hct : cl t = c := by
      simp only [hcl]
      rw [min_eq_left (by linarith : t ≤ c + h), max_eq_left ht]
    show β (cl t) = y
    rw [hct, hβ0]
  · intro t ht
    have hsub : Icc c t ⊆ Icc c (c + h) := Icc_subset_Icc le_rfl ht.2
    have hcongr : EqOn (fun s => f s (β (cl s))) (fun s => f s (β s)) (uIcc c t) := by
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      simp [hcl_eq s (hsub hs)]
    have hint : IntervalIntegrable (fun s => f s (β s)) volume c t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact hcont.comp_continuousOn (continuousOn_id.prodMk (hβcont.mono hsub))
    have hftc : ∫ s in c..t, f s (β s) = β t - β c := by
      refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
        (hβcont.mono hsub) (fun x hx => ?_) hint
      have hx' : x ∈ Icc c (c + h) := hsub (Ioo_subset_Icc_self hx)
      have hnhds : Icc c (c + h) ∈ 𝓝 x := Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 ht.2)
      exact ((hβ x hx').hasDerivAt hnhds).hasDerivWithinAt
    show β (cl t) = y + _
    rw [intervalIntegral.integral_congr hcongr, hftc, hβ0, hcl_eq t ht]
    abel

omit [CompleteSpace E] in
/-- **Grönwall uniqueness for the integral equation.**  Two continuous solutions
of `u t = x₀ + ∫_{t₀}^{t} f s (u s) ds` on `[t₀, T]` coincide there. -/
theorem integral_solution_unique (f : ℝ → E → E) (K : ℝ≥0)
    (hlip : ∀ t, LipschitzWith K (f t))
    (hcont : Continuous fun p : ℝ × E => f p.1 p.2)
    (t₀ T : ℝ) (x₀ : E) {u v : ℝ → E} (hu : Continuous u) (hv : Continuous v)
    (hueq : ∀ t ∈ Icc t₀ T, u t = x₀ + ∫ s in t₀..t, f s (u s))
    (hveq : ∀ t ∈ Icc t₀ T, v t = x₀ + ∫ s in t₀..t, f s (v s)) :
    EqOn u v (Icc t₀ T) := by
  have hfu : Continuous fun s => f s (u s) := continuous_comp_curve hcont hu
  have hfv : Continuous fun s => f s (v s) := continuous_comp_curve hcont hv
  have hd_cont : Continuous fun s => ‖u s - v s‖ := (hu.sub hv).norm
  have hint : ∀ t ∈ Icc t₀ T,
      ‖u t - v t‖ ≤ 0 + ∫ s in t₀..t, ((K : ℝ) * ‖u s - v s‖ + 0) := by
    intro t ht
    have ht0 : t₀ ≤ t := ht.1
    have hdiff : u t - v t = ∫ s in t₀..t, (f s (u s) - f s (v s)) := by
      rw [hueq t ht, hveq t ht, intervalIntegral.integral_sub
        (hfu.intervalIntegrable _ _) (hfv.intervalIntegrable _ _)]
      abel
    rw [hdiff, zero_add]
    refine (intervalIntegral.norm_integral_le_integral_norm ht0).trans ?_
    refine intervalIntegral.integral_mono_on ht0 ?_ ?_ fun s _ => ?_
    · exact (hfu.sub hfv).norm.intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun s => (K : ℝ) * ‖u s - v s‖ + 0).intervalIntegrable _ _
    · simpa [dist_eq_norm] using (hlip s).dist_le_mul (u s) (v s)
  intro t ht
  have key := gronwall_varying_rate (u := fun s => ‖u s - v s‖) (gam := fun _ => (K : ℝ))
    (a := t₀) (b := T) (delta := 0) (c := 0)
    hd_cont continuous_const (fun _ => K.coe_nonneg) le_rfl hint t ht
  have hzero : ‖u t - v t‖ = 0 := le_antisymm (by simpa using key) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Solvability of the integral equation on `[t₀, t₀ + N·h]`, for every `N`,
obtained by gluing `N` Picard–Lindelöf steps. -/
theorem exists_solution_upTo (f : ℝ → E → E) (K : ℝ≥0)
    (hlip : ∀ t, LipschitzWith K (f t))
    (hcont : Continuous fun p : ℝ × E => f p.1 p.2)
    (t₀ : ℝ) (x₀ : E) (h : ℝ) (hh : 0 < h) (hKh : (K : ℝ) * h ≤ 1 / 2) (N : ℕ) :
    ∃ α : ℝ → E, Continuous α ∧ (∀ t ≤ t₀, α t = x₀) ∧
      ∀ t ∈ Icc t₀ (t₀ + N * h), α t = x₀ + ∫ s in t₀..t, f s (α s) := by
  classical
  induction N with
  | zero =>
      refine ⟨fun _ => x₀, continuous_const, fun t _ => rfl, ?_⟩
      intro t ht
      simp only [Nat.cast_zero, zero_mul, add_zero] at ht
      have hteq : t = t₀ := le_antisymm ht.2 ht.1
      simp [hteq]
  | succ N ih =>
      obtain ⟨α, hαc, hα0, hαeq⟩ := ih
      set c : ℝ := t₀ + N * h with hc
      have ht₀c : t₀ ≤ c := by
        have hnn : (0 : ℝ) ≤ N * h := by positivity
        simp only [hc]; linarith
      have hcmem : c ∈ Icc t₀ (t₀ + N * h) := ⟨ht₀c, le_rfl⟩
      obtain ⟨γ, hγc, hγ0, hγeq⟩ := exists_solution_step f K hlip hcont c (α c) h hh hKh
      set α' : ℝ → E := fun t => if t ≤ c then α t else γ t with hα'def
      have hap : ∀ t, α' t = if t ≤ c then α t else γ t := fun t => rfl
      have hα'cont : Continuous α' := by
        refine hαc.if_le hγc continuous_id continuous_const ?_
        intro x hx
        rw [show x = c from hx, hγ0 c le_rfl]
      have hfint : Continuous fun s => f s (α' s) := continuous_comp_curve hcont hα'cont
      refine ⟨α', hα'cont, ?_, ?_⟩
      · intro t ht
        rw [hap, if_pos (le_trans ht ht₀c)]
        exact hα0 t ht
      · intro t ht
        have hsucc : t₀ + (N + 1 : ℕ) * h = c + h := by push_cast [hc]; ring
        rw [hsucc] at ht
        by_cases htc : t ≤ c
        · rw [hap, if_pos htc]
          have hcongr : EqOn (fun s => f s (α' s)) (fun s => f s (α s)) (uIcc t₀ t) := by
            intro s hs
            rw [uIcc_of_le ht.1] at hs
            simp [hap, if_pos (le_trans hs.2 htc)]
          rw [intervalIntegral.integral_congr hcongr]
          exact hαeq t ⟨ht.1, htc⟩
        · push_neg at htc
          rw [hap, if_neg (not_le.2 htc)]
          have hsplit : (∫ s in t₀..t, f s (α' s))
              = (∫ s in t₀..c, f s (α' s)) + ∫ s in c..t, f s (α' s) :=
            (intervalIntegral.integral_add_adjacent_intervals
              (hfint.intervalIntegrable _ _) (hfint.intervalIntegrable _ _)).symm
          have hleft : (∫ s in t₀..c, f s (α' s)) = ∫ s in t₀..c, f s (α s) := by
            refine intervalIntegral.integral_congr ?_
            intro s hs
            rw [uIcc_of_le ht₀c] at hs
            simp [hap, if_pos hs.2]
          have hright : (∫ s in c..t, f s (α' s)) = ∫ s in c..t, f s (γ s) := by
            refine intervalIntegral.integral_congr ?_
            intro s hs
            rw [uIcc_of_le htc.le] at hs
            by_cases hsc : s ≤ c
            · have hsc' : s = c := le_antisymm hsc hs.1
              simp [hap, hsc', hγ0 c le_rfl]
            · simp [hap, if_neg hsc]
          have hαc_eq : α c = x₀ + ∫ s in t₀..c, f s (α s) := hαeq c hcmem
          have hγt := hγeq t ⟨htc.le, ht.2⟩
          rw [hsplit, hleft, hright, hγt, hαc_eq]
          abel

/-- **Global existence for a globally Lipschitz, jointly continuous drift.**
There is a continuous curve `α`, constant equal to `x₀` before `t₀`, that solves
the integral equation `α t = x₀ + ∫_{t₀}^{t} f s (α s) ds` for all `t ≥ t₀`. -/
theorem exists_global_solution (f : ℝ → E → E) (K : ℝ≥0)
    (hlip : ∀ t, LipschitzWith K (f t))
    (hcont : Continuous fun p : ℝ × E => f p.1 p.2)
    (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, Continuous α ∧ (∀ t ≤ t₀, α t = x₀) ∧
      ∀ t, t₀ ≤ t → α t = x₀ + ∫ s in t₀..t, f s (α s) := by
  classical
  set h : ℝ := (2 * ((K : ℝ) + 1))⁻¹ with hhdef
  have hKpos : (0 : ℝ) < 2 * ((K : ℝ) + 1) := by positivity
  have hh : 0 < h := by rw [hhdef]; positivity
  have hKh : (K : ℝ) * h ≤ 1 / 2 := by
    rw [hhdef, mul_inv_le_iff₀ hKpos]
    nlinarith [K.coe_nonneg]
  choose sol hsolc hsol0 hsoleq using
    exists_solution_upTo f K hlip hcont t₀ x₀ h hh hKh
  -- the solutions on the various horizons are coherent, by Grönwall uniqueness
  have hcoh : ∀ (M N : ℕ) (t : ℝ), t₀ ≤ t → t ≤ t₀ + M * h → t ≤ t₀ + N * h →
      sol M t = sol N t := fun M N t ht hM hN =>
    integral_solution_unique f K hlip hcont t₀ t x₀ (hsolc M) (hsolc N)
      (fun s hs => hsoleq M s ⟨hs.1, le_trans hs.2 hM⟩)
      (fun s hs => hsoleq N s ⟨hs.1, le_trans hs.2 hN⟩) ⟨ht, le_rfl⟩
  set idx : ℝ → ℕ := fun t => ⌈(t - t₀) / h⌉₊ with hidxdef
  have hidx : ∀ t, t ≤ t₀ + (idx t) * h := by
    intro t
    have h1 : (t - t₀) / h ≤ (idx t : ℝ) := Nat.le_ceil _
    have h2 := (div_le_iff₀ hh).mp h1
    linarith
  set α : ℝ → E := fun t => sol (idx t) t with hαdef
  have hagree : ∀ (N : ℕ) (t : ℝ), t ≤ t₀ + N * h → α t = sol N t := by
    intro N t ht
    by_cases htt : t ≤ t₀
    · show sol (idx t) t = sol N t
      rw [hsol0 (idx t) t htt, hsol0 N t htt]
    · push_neg at htt
      exact hcoh (idx t) N t htt.le (hidx t) ht
  have hbig : ∀ t : ℝ, ∃ N : ℕ, t < t₀ + N * h := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt ((t - t₀) / h)
    exact ⟨N, by nlinarith [(div_lt_iff₀ hh).mp hN]⟩
  have hcontα : Continuous α := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨N, hN⟩ := hbig t
    have heq : α =ᶠ[𝓝 t] sol N :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds hN) fun s hs => hagree N s (le_of_lt hs)
    exact ((hsolc N).continuousAt).congr heq.symm
  refine ⟨α, hcontα, fun t ht => hsol0 (idx t) t ht, fun t ht => ?_⟩
  obtain ⟨N, hN⟩ := hbig t
  have hcongr : EqOn (fun s => f s (α s)) (fun s => f s (sol N s)) (uIcc t₀ t) := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    show f s (α s) = f s (sol N s)
    rw [hagree N s (le_trans hs.2 hN.le)]
  rw [intervalIntegral.integral_congr hcongr, hagree N t hN.le]
  exact hsoleq N t ⟨ht, hN.le⟩

end ODEFlow

/-- **Existence of a (continuous) global flow for an SHS with a Lipschitz drift.**

If the drift of `S` is globally Lipschitz in the state, with a constant `K`
independent of the mode and of time, and is jointly continuous in `(t, x)` for
every mode, then `S` admits a global flow in the sense of `SHS.HasGlobalFlow`,
whose trajectories are moreover continuous in time.  Together with
`SHS.HasGlobalFlow.flow_eq_of_lipschitz` (uniqueness) this turns the standing
assumption `SHS.HasGlobalFlow` into a theorem for this model class. -/
theorem SHS.exists_hasGlobalFlow_continuous_of_lipschitz
    {Q : Type*} {n m : ℕ} (S : SHS Q n m) (K : ℝ≥0)
    (hlip : ∀ q t, LipschitzWith K fun x => S.f q x t)
    (hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1) :
    ∃ hflow : S.HasGlobalFlow, ∀ t₀ q₀ x₀, Continuous (hflow.flow t₀ q₀ x₀) := by
  classical
  choose flow hflow_cont hflow_const hflow_eq using fun (t₀ : ℝ) (q : Q)
    (x₀ : EuclideanSpace ℝ (Fin n)) =>
      ODEFlow.exists_global_solution (fun t x => S.f q x t) K (fun t => hlip q t)
        (hcont q) t₀ x₀
  refine ⟨{ flow := flow, flow_init := fun t₀ q₀ x₀ => hflow_const t₀ q₀ x₀ t₀ le_rfl,
            flow_ode := ?_ }, hflow_cont⟩
  intro t₀ q₀ x₀ t
  by_cases ht : t₀ ≤ t
  · rw [hflow_eq t₀ q₀ x₀ t ht, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht]
  · push_neg at ht
    rw [Set.Icc_eq_empty (by linarith)]
    simp [hflow_const t₀ q₀ x₀ t ht.le]

/-- **Existence of a global flow for an SHS with a Lipschitz drift.**  The
`Nonempty` form of `SHS.exists_hasGlobalFlow_continuous_of_lipschitz`. -/
theorem SHS.exists_hasGlobalFlow_of_lipschitz
    {Q : Type*} {n m : ℕ} (S : SHS Q n m) (K : ℝ≥0)
    (hlip : ∀ q t, LipschitzWith K fun x => S.f q x t)
    (hcont : ∀ q, Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => S.f q p.2 p.1) :
    Nonempty S.HasGlobalFlow :=
  ⟨(S.exists_hasGlobalFlow_continuous_of_lipschitz K hlip hcont).choose⟩

end
