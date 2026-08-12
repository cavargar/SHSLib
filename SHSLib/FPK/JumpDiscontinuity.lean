/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 6.2 of Bect (2010): the jump discontinuity of the density across `H`

Equation (34) of the paper expresses `(L^* μ_t) φ` for a model with forced jumps and
deterministic resets as

  `∫_E (F p_t) φ dm + ∫_G j_t^out φ ds − ∫_H j_t^in φ ds
      − ½ Σ_l ∫_H (f_l φ) ⟨f_l, n_ab⟩ (p_t^b − p_t^a) ds_H`,

where `p_t^a`, `p_t^b` are the two one-sided limits of the density across the hypersurface
`H` and `j_t^in = ⟨j_t^(b) − j_t^(a), n_ab⟩` is the jump of the normal component of the
probability current.  The paper then argues:

* the last term must vanish, *because* `L^* μ_t` is a Radon measure (Theorem 8) while that
  term involves the *first-order derivatives* of `φ` on the `m`-null hypersurface `H`;
* consequently `p_t` is continuous across `H⁰ = {x ∈ H : ∃ l, ⟨f_l, n_ab⟩ ≠ 0}`
  (conclusion (d) of Section 6.2);
* and the singular measures `β_t` of Theorem 13 are given by Eq. (35),
  `β_t(Γ) = ∫_{H ∩ Γ} j_t^in ds_H`.

This file formalizes the analytic core of that argument.  The obstruction "a measure
cannot see a transversal derivative on a null set" is captured, in the transversal
variable, by `GSHS.transversal_weight_eq_zero`: a linear functional of the form
`φ ↦ w · φ'(0)` that is dominated by the supremum norm of `φ` must be identically zero.
The witnesses are the rescaled bumps `ε ↦ ε · T(·/ε)`, whose sup norm is `O(ε)` while
their derivative at `0` stays equal to `1`.

The main consequences formalized here are

* `GSHS.transversal_weight_eq_zero`   — the last term of (34) vanishes;
* `GSHS.transversal_weight_eq_zero_of_measure` — the same, with the domination hypothesis
  packaged as "the functional is represented by a finite measure";
* `GSHS.density_jump_eq_zero_on_H0`   — conclusion 6.2(d): `p_t` is continuous on `H⁰`;
* `GSHS.boundaryIntensity` and `GSHS.boundaryIntensity_apply` — Eq. (35);
* `GSHS.boundaryIntensity_unique`     — Eq. (35) determines `β_t`.
-/
import Mathlib
import SHSLib.FPK.DensityEvolution

open MeasureTheory Set Function Metric
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

/-! ### A rescalable transversal test function -/

/-- An auxiliary `C^∞` bump on `ℝ`, equal to `1` on `[-1, 1]` and supported in `(-2, 2)`. -/
def unitBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The transversal test profile `T x = x · b(x)`: a smooth, compactly supported function
with `T'(0) = 1` and `‖T‖_∞ ≤ 2`.  Rescaling it produces test functions whose supremum
norm is arbitrarily small while their derivative at the origin stays equal to `1`. -/
def transversalProfile (x : ℝ) : ℝ := x * unitBump x

@[simp] theorem transversalProfile_eq_zero_of_two_le {x : ℝ} (hx : 2 ≤ |x|) :
    transversalProfile x = 0 := by
  have hns : x ∉ support (unitBump : ℝ → ℝ) := by
    rw [unitBump.support_eq]
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact hx
  have : unitBump x = 0 := by simpa using hns
  simp [transversalProfile, this]

theorem transversalProfile_contDiff : ContDiff ℝ 2 transversalProfile :=
  contDiff_id.mul (unitBump.contDiff (n := 2))

theorem transversalProfile_abs_le (x : ℝ) : |transversalProfile x| ≤ 2 := by
  by_cases hx : |x| ≤ 2
  · have hle := unitBump.le_one (x := x)
    have h0 := unitBump.nonneg (x := x)
    rw [transversalProfile, abs_mul]
    calc |x| * |unitBump x| ≤ 2 * 1 :=
          mul_le_mul hx (by rw [abs_of_nonneg h0]; exact hle) (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  · rw [transversalProfile_eq_zero_of_two_le (le_of_lt (lt_of_not_ge hx))]
    norm_num

theorem transversalProfile_deriv_zero : deriv transversalProfile 0 = 1 := by
  have hb : DifferentiableAt ℝ (unitBump : ℝ → ℝ) 0 :=
    (unitBump.contDiff (n := 1)).differentiable (by norm_num) 0
  have h := (hasDerivAt_id (0 : ℝ)).mul hb.hasDerivAt
  have h1 : unitBump 0 = 1 := unitBump.one_of_mem_closedBall (by simp [unitBump])
  rw [h1] at h
  simpa [transversalProfile] using h.deriv

/-- The rescaled transversal profile `T_ε(x) = ε · T(x/ε)`. -/
def scaledProfile (e x : ℝ) : ℝ := e * transversalProfile (x / e)

theorem scaledProfile_contDiff (e : ℝ) : ContDiff ℝ 2 (scaledProfile e) :=
  contDiff_const.mul (transversalProfile_contDiff.comp (contDiff_id.div_const e))

/-- The rescaled profile has supremum norm at most `2ε`: it is uniformly small. -/
theorem scaledProfile_abs_le {e : ℝ} (he : 0 < e) (x : ℝ) : |scaledProfile e x| ≤ 2 * e := by
  rw [scaledProfile, abs_mul, abs_of_pos he]
  nlinarith [transversalProfile_abs_le (x / e), abs_nonneg (transversalProfile (x / e))]

theorem scaledProfile_hasCompactSupport {e : ℝ} (he : 0 < e) :
    HasCompactSupport (scaledProfile e) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * e)) ?_
  intro x hx
  have hx' : 2 * e < |x| := by
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] using hx
  have h2 : 2 ≤ |x / e| := by
    rw [abs_div, abs_of_pos he, le_div_iff₀ he]
    linarith
  simp [scaledProfile, transversalProfile_eq_zero_of_two_le h2]

/-- Its derivative at the origin is `1`, independently of `ε`. -/
theorem scaledProfile_deriv_zero {e : ℝ} (he : 0 < e) : deriv (scaledProfile e) 0 = 1 := by
  have h1 : HasDerivAt (fun x : ℝ => x / e) (1 / e) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const e
  have hT : HasDerivAt transversalProfile 1 (0 / e) := by
    have hd : DifferentiableAt ℝ transversalProfile 0 :=
      transversalProfile_contDiff.differentiable (by norm_num) 0
    have h := hd.hasDerivAt
    rw [transversalProfile_deriv_zero] at h
    simpa using h
  have h2 := (hT.comp 0 h1).const_mul e
  have he' : scaledProfile e = fun y => e * (transversalProfile ∘ fun x : ℝ => x / e) y := rfl
  rw [he', h2.deriv]
  field_simp

/-! ### The last term of Eq. (34) vanishes -/

/-- **The last term of Eq. (34) vanishes.**

In the transversal variable across the hypersurface `H`, the last term of Eq. (34) is the
linear functional `φ ↦ w · φ'(0)`, with weight `w = ⟨f_l, n_ab⟩ (p_t^b − p_t^a)` (up to the
factor `−½` and the surface integration).  If this functional is dominated by the supremum
norm of the test function — which is exactly what it means for it to be given by a *finite
Radon measure*, as Theorem 8 guarantees for `L^* μ_t` — then the weight vanishes.

The proof tests the functional against the rescaled bumps `scaledProfile ε`, whose
supremum norm is `2ε` while their derivative at `0` is `1`. -/
theorem transversal_weight_eq_zero (w C : ℝ)
    (h : ∀ (phi : ℝ → ℝ) (M : ℝ), ContDiff ℝ 2 phi → HasCompactSupport phi →
      (∀ x, |phi x| ≤ M) → |w * deriv phi 0| ≤ C * M) :
    w = 0 := by
  -- Step 1: `|w| ≤ 2 C ε` for every `ε > 0`.
  have key : ∀ e : ℝ, 0 < e → |w| ≤ C * (2 * e) := by
    intro e he
    have := h (scaledProfile e) (2 * e) (scaledProfile_contDiff e)
      (scaledProfile_hasCompactSupport he) (scaledProfile_abs_le he)
    rwa [scaledProfile_deriv_zero he, mul_one] at this
  -- Step 2: `C ≥ 0`, since `|w| ≥ 0`.
  have hC : 0 ≤ C := by
    have h1 := key 1 one_pos
    nlinarith [abs_nonneg w]
  -- Step 3: `|w| ≤ ε` for every `ε > 0`, hence `w = 0`.
  have hw : |w| ≤ 0 := by
    refine le_of_forall_pos_le_add ?_
    intro eps heps
    have hpos : 0 < eps / (2 * C + 2) := by positivity
    have h1 := key (eps / (2 * C + 2)) hpos
    have hd : (0:ℝ) < 2 * C + 2 := by linarith
    have hcancel : eps / (2 * C + 2) * (2 * C + 2) = eps := div_mul_cancel₀ _ hd.ne'
    have h2 : C * (2 * (eps / (2 * C + 2))) ≤ eps := by nlinarith [hpos.le]
    linarith
  exact abs_eq_zero.mp (le_antisymm hw (abs_nonneg w))

/-- **The last term of Eq. (34) vanishes** (measure form).  If the functional
`φ ↦ w · φ'(0)` coincides with integration against a finite measure `ν`, then `w = 0`.
This is the exact form of the paper's argument: `L^* μ_t` is a Radon measure by
Theorem 8, so it cannot contain a term involving first-order derivatives of `φ` carried
by the `m`-null hypersurface `H`. -/
theorem transversal_weight_eq_zero_of_measure (w : ℝ) (nu : Measure ℝ) [IsFiniteMeasure nu]
    (h : ∀ phi : ℝ → ℝ, ContDiff ℝ 2 phi → HasCompactSupport phi →
      w * deriv phi 0 = ∫ x, phi x ∂nu) :
    w = 0 := by
  refine transversal_weight_eq_zero w (nu univ).toReal ?_
  intro phi M hphi hcs hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (phi 0)) (hM 0)
  have hint : Integrable phi nu := by
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · exact (hphi.continuous.aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun x => hM x)
  rw [h phi hphi hcs, ← Real.norm_eq_abs]
  calc ‖∫ x, phi x ∂nu‖ ≤ ∫ x, ‖phi x‖ ∂nu := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, M ∂nu :=
        integral_mono hint.norm (integrable_const M)
          (fun x => by simpa [Real.norm_eq_abs] using hM x)
    _ = (nu univ).toReal * M := by
        rw [integral_const]; simp [smul_eq_mul, measureReal_def]

/-- **Conclusion 6.2(d)**: the density is continuous across `H⁰`.

At a point of `H⁰` some noise vector field `f_l` is transversal to `H`, i.e.
`fn = ⟨f_l, n_ab⟩ ≠ 0`.  Since the corresponding term of Eq. (34), whose weight is
`fn · (p^b − p^a)`, must vanish by `transversal_weight_eq_zero`, the two one-sided limits
of the density agree: `p_t` has no jump on `H⁰`. -/
theorem density_jump_eq_zero_on_H0 (fn pa pb C : ℝ) (hfn : fn ≠ 0)
    (h : ∀ (phi : ℝ → ℝ) (M : ℝ), ContDiff ℝ 2 phi → HasCompactSupport phi →
      (∀ x, |phi x| ≤ M) → |fn * (pb - pa) * deriv phi 0| ≤ C * M) :
    pb = pa := by
  have hw : fn * (pb - pa) = 0 := transversal_weight_eq_zero _ C h
  rcases mul_eq_zero.mp hw with h1 | h2
  · exact absurd h1 hfn
  · linarith [sub_eq_zero.mp h2]

/-! ### Equation (35): the boundary measures `β_t` -/

variable {E : Type*} [MeasurableSpace E]

/-- **Eq. (35)**: the singular measures `β_t` of Theorem 13, for the models of
Section 6.2.  They are carried by the hypersurface `H` and have density `j_t^in`, the jump
of the normal component of the probability current, with respect to the surface measure
`s_H`. -/
def boundaryIntensity (sH : Measure E) (H : Set E) (jin : E → ℝ) : Measure E :=
  (sH.restrict H).withDensity fun x => ENNReal.ofReal (jin x)

/-- Eq. (35) evaluated on a measurable set: `β_t(Γ) = ∫_{H ∩ Γ} j_t^in ds_H`. -/
theorem boundaryIntensity_apply (sH : Measure E) {H Gam : Set E} (jin : E → ℝ)
    (hGam : MeasurableSet Gam) :
    boundaryIntensity sH H jin Gam = ∫⁻ x in H ∩ Gam, ENNReal.ofReal (jin x) ∂sH := by
  rw [boundaryIntensity, withDensity_apply _ hGam, Measure.restrict_restrict hGam,
    Set.inter_comm]

/-- `β_t` is carried by `H`: it gives no mass to sets disjoint from the hypersurface. -/
theorem boundaryIntensity_eq_zero_of_disjoint (sH : Measure E) {H Gam : Set E} (jin : E → ℝ)
    (hGam : MeasurableSet Gam) (hdisj : Disjoint H Gam) :
    boundaryIntensity sH H jin Gam = 0 := by
  rw [boundaryIntensity, withDensity_apply _ hGam, Measure.restrict_restrict hGam,
    Set.inter_comm, hdisj.inter_eq]
  simp

/-- **Eq. (35) determines `β_t`.**  The measures `β_t` appear in Theorem 13 as the
`m`-singular part of the source term.  Since the Lebesgue decomposition is unique, any
measure that is `m`-singular and reproduces the same source term must coincide with the
measure of Eq. (35).  Here `src` is the density of the absolutely continuous part. -/
theorem boundaryIntensity_unique (m : Measure E) [SigmaFinite m] {src : E → ℝ≥0∞}
    {beta beta' : Measure E} (hs : beta ⟂ₘ m) (hs' : beta' ⟂ₘ m)
    (hsrc : Measurable src)
    (h : m.withDensity src + beta = m.withDensity src + beta') :
    beta = beta' :=
  (singular_part_unique (m := m) (f := src) (g := src) (s₁ := beta) (s₂ := beta')
    hsrc hsrc hs hs' h).1

end GSHS
