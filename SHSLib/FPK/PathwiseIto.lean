/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eq. (3) of Bect (2010): the pathwise content of the generalized Itô formula

Section 2.2 states the *generalized Itô formula*

  `φ(X_t) − φ(X_0) = ∫₀ᵗ (Lφ)(X_s) ds + Σ_l ∫₀ᵗ (f_l φ)(X_s) dB_s^l
                       + Σ_{0 < τ_k ≤ t} (φ(X_{τ_k}) − φ(X_{τ_k}⁻))`.     (3)

Its stochastic-integral term is the Itô integral against the driving Wiener process of
Eq. (2); the remaining, purely *pathwise*, content of (3) is an exact accounting of the
increment of `φ(X)` along a piecewise-continuous trajectory: between consecutive jumps
the increment is the time integral of `Lφ` along the path, and at each jump time it is
the size of the jump of `φ(X)`.  Summing the two families of increments telescopes to
the total increment.

This file formalizes that pathwise identity, and hence the noise-free case (`r = 0`,
i.e. a piecewise-deterministic Markov process) of Eq. (3):

* `GSHS.telescope_pre_post` — the telescoping identity for a piecewise trajectory
  described by its pre-jump values `pre i = φ(X_{a_i}⁻)` and post-jump values
  `post i = φ(X_{a_i})`;
* `GSHS.pathwise_ito_noiseFree` — Eq. (3) with `r = 0`:
  `φ(X_t) − φ(X_0) = ∫₀ᵗ (Lφ)(X_s) ds + Σ_{0 < τ_k ≤ t} (φ(X_{τ_k}) − φ(X_{τ_k}⁻))`.

The convention is that `a 0 = 0` and `a n = t`, that the jump times are among the
`a i`, and that `post i = pre i` at an index which is not a jump time (so that the jump
sum over `Finset.range n` really only sees the genuine jumps in `(0; t]`; in particular
the term `i = 0` vanishes, since the process does not jump at time `0`).
-/
import Mathlib

open MeasureTheory intervalIntegral

noncomputable section

namespace GSHS

/-- Telescoping of a piecewise trajectory: the total increment `pre n − pre 0` is the
sum of the continuous increments `pre (i+1) − post i` over the pieces and of the jumps
`post i − pre i`. -/
theorem telescope_pre_post (pre post : ℕ → ℝ) (n : ℕ) :
    pre n - pre 0
      = (∑ i ∈ Finset.range n, (pre (i + 1) - post i))
        + ∑ i ∈ Finset.range n, (post i - pre i) := by
  rw [← Finset.sum_add_distrib]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring

/-- **Eq. (3) in the noise-free case.**  Let `0 = a 0 ≤ a 1 ≤ ⋯ ≤ a n = t` list the
jump times of the trajectory together with the endpoints, let `pre i = φ(X_{a_i}⁻)`,
`post i = φ(X_{a_i})` and let `Lphi s = (Lφ)(X_s)`.  If on each piece the increment of
`φ(X)` is the integral of `Lφ` along the path (which is what Eq. (2) gives in the
absence of noise), then

  `φ(X_t) − φ(X_0) = ∫₀ᵗ (Lφ)(X_s) ds + Σ_{0 < τ_k ≤ t} (φ(X_{τ_k}) − φ(X_{τ_k}⁻))`. -/
theorem pathwise_ito_noiseFree {Lphi : ℝ → ℝ} {a : ℕ → ℝ} {pre post : ℕ → ℝ} {n : ℕ}
    (hint : ∀ i < n, IntervalIntegrable Lphi volume (a i) (a (i + 1)))
    (hflow : ∀ i < n, ∫ s in (a i)..(a (i + 1)), Lphi s = pre (i + 1) - post i) :
    pre n - pre 0
      = (∫ s in (a 0)..(a n), Lphi s) + ∑ i ∈ Finset.range n, (post i - pre i) := by
  have hsum : ∑ i ∈ Finset.range n, (pre (i + 1) - post i)
      = ∫ s in (a 0)..(a n), Lphi s := by
    rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
    exact (Finset.sum_congr rfl fun i hi => (hflow i (Finset.mem_range.mp hi))).symm
  rw [telescope_pre_post pre post n, hsum]

/-! ## Eq. (2) without noise: the flow increment is the integral of `Lφ` -/

/-- **Eq. (2) with `f_l = 0` for `l ≥ 1`.**  Along a solution `Z` of the ordinary
differential equation `dZ/ds = f₀(Z_s)`, the increment of a differentiable test function
`φ` is the integral of `Lφ = ⟨f₀, ∇φ⟩` — the differential generator (4) in the absence
of noise — along the trajectory.  This discharges the hypothesis `hflow` of
`GSHS.pathwise_ito_noiseFree` on each inter-jump piece. -/
theorem flowIncrement_eq_integral_generator {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Z : ℝ → F} {f0 : F → F} {phi : F → ℝ} {u v : ℝ}
    (hZ : ∀ s ∈ Set.uIcc u v, HasDerivAt Z (f0 (Z s)) s)
    (hphi : ∀ x, DifferentiableAt ℝ phi x)
    (hint : IntervalIntegrable (fun s => fderiv ℝ phi (Z s) (f0 (Z s))) volume u v) :
    ∫ s in u..v, fderiv ℝ phi (Z s) (f0 (Z s)) = phi (Z v) - phi (Z u) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => phi (Z s))
    (fun s hs => ?_) hint
  exact ((hphi (Z s)).hasFDerivAt).comp_hasDerivAt s (hZ s hs)

end GSHS
