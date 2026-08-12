/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 5.1 of Bect (2010): the surface measure and the boundary conditions (19)

Two ingredients of Section 5.1 are formalized here.

**The surface measure, Eq. (18).**  The surface measure `s` on `∂E` is defined mode by
mode,

  `s = Σ_{n_q ≥ 2} s_q + Σ_{n_q = 1} Σ_{x ∈ ∂E_q} δ_x`,                     (18)

i.e. as the sum over the modes of the individual surface measures, the one-dimensional
modes contributing counting measure on their (discrete) boundary.  Both pieces are
instances of `MeasureTheory.Measure.sum`, so `GSHS.hybridSurfaceMeasure` covers the whole
of Eq. (18); `GSHS.hybridSurfaceMeasure_of_dim_one` records that the contribution of a
one-dimensional mode is indeed counting measure on its boundary.

**The boundary conditions, Eq. (19).**  On the part `∂E \ G` of the boundary where the
process is allowed to live, the drift must satisfy `⟨f₀, n⟩ ≤ 0`: otherwise the
deterministic flow would leave the domain instantaneously.  This is formalized as
`GSHS.exits_immediately_of_outward_drift`: if the domain is `{y : ψ y ≤ 0}` near a
boundary point `x` (with `ψ x = 0`, so that `∇ψ` points outwards) and a curve through `x`
has velocity `v` with `⟨∇ψ, v⟩ > 0`, then the curve leaves the domain for all small
positive times.  Its contrapositive is `GSHS.inward_drift_of_stays_in_domain`, which is
exactly the necessity of the first condition in Eq. (19).
-/
import Mathlib

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSHS

/-! ### Eq. (18): the surface measure of a hybrid state space -/

variable {E : Type*} [MeasurableSpace E] {Q : Type*} [Countable Q] [MeasurableSpace Q]

/-- **Eq. (18)**: the surface measure on the boundary of a hybrid state space is the sum,
over the modes, of the surface measures of the individual mode boundaries.  Modes of
dimension `≥ 2` contribute their `(n_q − 1)`-dimensional surface measure; modes of
dimension `1` contribute counting measure on their finite boundary, which is again a sum
of Dirac masses and hence covered by the same formula. -/
def hybridSurfaceMeasure (sq : Q → Measure E) : Measure E := Measure.sum sq

omit [Countable Q] [MeasurableSpace Q] in
theorem hybridSurfaceMeasure_apply (sq : Q → Measure E) {A : Set E} (hA : MeasurableSet A) :
    hybridSurfaceMeasure sq A = ∑' q, sq q A :=
  Measure.sum_apply _ hA

omit [Countable Q] [MeasurableSpace Q] in
theorem lintegral_hybridSurfaceMeasure (sq : Q → Measure E) (f : E → ℝ≥0∞) :
    ∫⁻ x, f x ∂(hybridSurfaceMeasure sq) = ∑' q, ∫⁻ x, f x ∂(sq q) :=
  lintegral_sum_measure (f := f) (μ := sq)

/-- The one-dimensional part of Eq. (18): for a mode `q` with `n_q = 1` the boundary
`∂E_q` is a discrete set and its "surface measure" is `Σ_{x ∈ ∂E_q} δ_x`, that is,
counting measure on `∂E_q`. -/
theorem hybridSurfaceMeasure_of_dim_one (bdry : Finset E) {A : Set E}
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    (∑ x ∈ bdry, Measure.dirac x) A = (bdry.filter (· ∈ A)).card := by
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.dirac_apply' _ hA, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]

/-! ### Eq. (19): the boundary conditions on the vector fields -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Instantaneous exit** (justification of Eq. (19)).

Suppose the domain is contained in `{y : ψ y ≤ 0}` near a boundary point `x`, where `ψ`
is differentiable at `x` with `ψ x = 0` (so `∇ψ` is an outward conormal at `x`).  If a
curve `g` through `x` has velocity `v` with `⟨∇ψ, v⟩ > 0` — the drift pointing strictly
outwards — then `ψ (g t) > 0` for all sufficiently small `t > 0`, i.e. the curve leaves
the domain instantaneously. -/
theorem exits_immediately_of_outward_drift {psi : V → ℝ} {psi' : V →L[ℝ] ℝ} {x v : V}
    {g : ℝ → V} (hpsi : HasFDerivAt psi psi' x) (hx : psi x = 0)
    (hg : HasDerivAt g v 0) (hg0 : g 0 = x) (hout : 0 < psi' v) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < psi (g t) := by
  have hcomp : HasDerivAt (fun t => psi (g t)) (psi' v) 0 := by
    have h1 : HasFDerivAt psi psi' (g 0) := by rw [hg0]; exact hpsi
    simpa using h1.comp_hasDerivAt 0 hg
  have hslope : Tendsto (slope (fun t => psi (g t)) 0) (𝓝[≠] (0 : ℝ)) (𝓝 (psi' v)) :=
    hasDerivAt_iff_tendsto_slope.mp hcomp
  have hpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < slope (fun t => psi (g t)) 0 t :=
    hslope.eventually (eventually_gt_nhds hout)
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (fun t ht => ne_of_gt ht)
  filter_upwards [hsub hpos, self_mem_nhdsWithin] with t ht htpos
  have hs : slope (fun t => psi (g t)) 0 t = (psi (g t) - psi x) / t := by
    rw [slope_def_field]
    simp [hg0, sub_zero, div_eq_inv_mul, mul_comm]
  rw [hs, hx, sub_zero] at ht
  exact (div_pos_iff_of_pos_right htpos).mp ht

/-- **Eq. (19), first condition** (necessity).  If the deterministic flow starting from a
boundary point `x` stays in the domain `{y : ψ y ≤ 0}` for arbitrarily small positive
times, then the drift cannot point strictly outwards: `⟨f₀, n⟩ ≤ 0`. -/
theorem inward_drift_of_stays_in_domain {psi : V → ℝ} {psi' : V →L[ℝ] ℝ} {x v : V}
    {g : ℝ → V} (hpsi : HasFDerivAt psi psi' x) (hx : psi x = 0)
    (hg : HasDerivAt g v 0) (hg0 : g 0 = x)
    (hstay : ∃ᶠ t in 𝓝[>] (0 : ℝ), psi (g t) ≤ 0) :
    psi' v ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := exits_immediately_of_outward_drift hpsi hx hg hg0 hcon
  exact (hstay.and_eventually h).exists.elim fun t ht => absurd ht.1 (not_le.2 ht.2)

end GSHS
