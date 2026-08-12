/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The strong generator and Dynkin's formula

Formalization of the material around Proposition 6 (martingale property) of

  M.L. Bujorianu and J. Lygeros, "Toward a General Theory of Stochastic Hybrid
  Systems", LNCIS 337, Springer, 2006.

Section 4 of the paper introduces the *strong generator* `L` of the transition
semigroup `(P_t)` as the derivative of `P_t` at `t = 0`,

  `L f = lim_{t ↓ 0} (P_t f - f) / t`,

and states (Proposition 6) that for `f ∈ D(L)` the process

  `C_t^f = f(x_t) - f(x_0) - ∫_0^t L f (x_s) ds`                          (27)

is a `P_x`-martingale.  Here we work at the level of the semigroup, which is
where the analytic content of that statement lies:

* `HasStrongGenerator` formalizes membership `f ∈ D(L)` together with `L f`;
* `strongGenerator_unique` shows `L f` is well defined;
* `hasDerivWithinAt_semigroup` shows that `t ↦ P_t f (x)` is differentiable from
  the right with derivative `P_t (L f) (x)` (Kolmogorov's forward equation);
* `dynkin_formula` integrates this to `P_t f - f = ∫_0^t P_s (L f) ds`, which is
  exactly the statement that the process (27) has zero mean, i.e. the martingale
  property of Proposition 6 tested against the initial time.
-/
import SHSLib.Bujorianu2006.Resolvent

open MeasureTheory Set Filter Topology

noncomputable section

namespace Bujorianu2006

namespace TransitionSemigroup

variable {X : Type*} {S : TransitionSemigroup X}

/-- Membership `f ∈ D(L)` together with the value `L f`, in the pointwise sense:
`L f (x) = lim_{t ↓ 0} (P_t f (x) - f (x)) / t`. -/
def HasStrongGenerator (S : TransitionSemigroup X) (f Lf : X → ℝ) : Prop :=
  ∀ x, Tendsto (fun t : ℝ => (S.P t f x - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 (Lf x))

/-- The generator is well defined: two candidate values of `L f` agree. -/
theorem strongGenerator_unique {f g h : X → ℝ} (hg : S.HasStrongGenerator f g)
    (hh : S.HasStrongGenerator f h) : g = h := by
  funext x
  exact tendsto_nhds_unique (hg x) (hh x)

/-- The difference quotient of the semigroup at time `h`, transported by `P_t`,
is the difference quotient of `t ↦ P_t f (x)` at `t`. -/
theorem semigroup_slope (t h : ℝ) (ht : 0 ≤ t) (hh : 0 ≤ h) (f : X → ℝ) (x : X) :
    S.P t (fun y => (S.P h f y - f y) / h) x = (S.P (t + h) f x - S.P t f x) / h := by
  have h1 : (fun y => (S.P h f y - f y) / h)
      = fun y => h⁻¹ * ((fun z => S.P h f z) y - (fun z => f z) y) := by
    funext y; rw [div_eq_inv_mul]
  rw [h1, S.P_const_mul t h⁻¹ (fun y => (fun z => S.P h f z) y - (fun z => f z) y)]
  rw [S.P_sub t (fun z => S.P h f z) (fun z => f z)]
  simp only
  rw [S.P_add t h f x ht hh]
  simp [div_eq_inv_mul]

/-- **Kolmogorov's forward equation.** If `f ∈ D(L)` and `P_t` commutes with the
limit defining the generator, then `t ↦ P_t f (x)` has right derivative
`P_t (L f) (x)`. -/
theorem hasDerivWithinAt_semigroup {f Lf : X → ℝ} (t : ℝ) (ht : 0 ≤ t) (x : X)
    (hcomm : Tendsto (fun h : ℝ => S.P t (fun y => (S.P h f y - f y) / h) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (S.P t Lf x))) :
    HasDerivWithinAt (fun u => S.P u f x) (S.P t Lf x) (Ioi t) t := by
  have hsub : Tendsto (fun s : ℝ => s - t) (𝓝[>] t) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hlim : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (t - t)) := tendsto_id.sub_const t
      rw [sub_self] at hlim
      exact hlim.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using sub_pos.mpr (mem_Ioi.mp hs)
  have hcomp := hcomm.comp hsub
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ioi t \ {t} = Ioi t := by
    ext s; simp +contextual
  rw [hset]
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hlt : t < s := mem_Ioi.mp hs
  have hs' : 0 ≤ s - t := le_of_lt (sub_pos.mpr hlt)
  have hts : t + (s - t) = s := by ring
  show S.P t (fun y => (S.P (s - t) f y - f y) / (s - t)) x = slope (fun u => S.P u f x) t s
  rw [semigroup_slope t (s - t) ht hs' f x, hts, slope_def_field]

/-- **Dynkin's formula / zero mean of the process (27).** Integrating the forward
equation gives `P_t f (x) - f (x) = ∫_0^t P_s (L f) (x) ds`, i.e. the process
`C_t^f = f(x_t) - f(x_0) - ∫_0^t L f (x_s) ds` of Proposition 6 has zero
expectation under `P_x`. -/
theorem dynkin_formula {f Lf : X → ℝ} (t : ℝ) (ht : 0 ≤ t) (x : X)
    (hcont : ContinuousOn (fun u => S.P u f x) (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivWithinAt (fun u => S.P u f x) (S.P s Lf x) (Ioi s) s)
    (hint : IntervalIntegrable (fun s => S.P s Lf x) volume 0 t) :
    S.P t f x - f x = ∫ s in (0 : ℝ)..t, S.P s Lf x := by
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hcont hderiv hint
  rw [this, S.P_zero]

/-- The zero-mean statement in the exact form of `(27)`: with
`C_t^f = f(x_t) - f(x_0) - ∫_0^t L f (x_s) ds`, one has `E_x C_t^f = 0`. -/
theorem dynkinProcess_mean_zero {f Lf : X → ℝ} (t : ℝ) (ht : 0 ≤ t) (x : X)
    (hcont : ContinuousOn (fun u => S.P u f x) (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivWithinAt (fun u => S.P u f x) (S.P s Lf x) (Ioi s) s)
    (hint : IntervalIntegrable (fun s => S.P s Lf x) volume 0 t) :
    S.P t f x - f x - (∫ s in (0 : ℝ)..t, S.P s Lf x) = 0 := by
  rw [dynkin_formula t ht x hcont hderiv hint, sub_self]

end TransitionSemigroup

end Bujorianu2006

end
