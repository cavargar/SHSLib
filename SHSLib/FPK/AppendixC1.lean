/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Appendix C.1 of Bect (2010): Eqs. (46) and (47), the computation of `L*μ_t`

The pointwise identities (44) and (45) of Appendix C.1,

  `(Lφ) p = j·∇φ + ½ Σ_l div((f_lφ) p f_l)`,     `j·∇φ = div(φ j) + φ F p`,

are formalized in `SHSLib.FPK.ProbabilityCurrent`.  Integrating their sum against the
volume measure and applying the divergence theorem (Theorem 21) to each divergence term
gives Eq. (46),

  `(L*μ_t)(φ) = ∫_E φ F p_t dm + ∫_{∂E} φ j_t^out ds
                  + ½ Σ_l ∫_{∂E} (f_lφ) p_t ⟨f_l, n⟩ ds`,

and, once the boundary condition of Proposition 11(b) has made the last term vanish,
Eq. (47),

  `(L*μ_t)(φ) = ∫_E φ F p_t dm + ∫_{∂E} φ j_t^out ds`,

which is the tested form of Eq. (48).  This file formalizes these two steps:

* `GSHS.eq46_lstar_pair` — Eq. (46), from the pointwise decomposition and the
  divergence theorem applied to each term;
* `GSHS.eq47_lstar_pair` — Eq. (47), when the noise boundary terms vanish;
* `GSHS.density_mul_normal_eq_zero_of_sq` — the elementary step of Appendix C.2 behind
  that vanishing: if `p Σ_l ⟨f_l,n⟩² = 0` then `p ⟨f_l,n⟩ = 0` for every `l`.
-/
import SHSLib.FPK.ProbabilityCurrent

open MeasureTheory Set

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E] {r : ℕ}

/-- **Eq. (46)** (Appendix C.1).  Suppose the integrand `(Lφ) p_t` decomposes pointwise
as `div(φ j) + φ F p + ½ Σ_l div((f_lφ) p f_l)` (Eqs. (44) and (45)) and that the
divergence theorem (Theorem 21) converts the integral over `E` of each divergence into
the corresponding boundary flux.  Then

  `∫_E (Lφ) p dm = ∫_E φ F p dm + ∫_{∂E} φ j^out ds + ½ Σ_l ∫_{∂E} (f_lφ) p ⟨f_l,n⟩ ds`. -/
theorem eq46_lstar_pair (m s : Measure E) {Lphip phiFp divPhiJ phiJout : E → ℝ}
    {divNoise noiseFlux : Fin r → E → ℝ}
    (hpoint : ∀ x, Lphip x = divPhiJ x + phiFp x + 2⁻¹ * ∑ l, divNoise l x)
    (hdivPhiJ : Integrable divPhiJ m) (hphiFp : Integrable phiFp m)
    (hdivNoise : ∀ l, Integrable (divNoise l) m)
    (hfluxJ : ∫ x, divPhiJ x ∂m = ∫ x, phiJout x ∂s)
    (hfluxN : ∀ l, ∫ x, divNoise l x ∂m = ∫ x, noiseFlux l x ∂s) :
    ∫ x, Lphip x ∂m
      = (∫ x, phiFp x ∂m) + (∫ x, phiJout x ∂s) + 2⁻¹ * ∑ l, ∫ x, noiseFlux l x ∂s := by
  have hsumInt : Integrable (fun x => ∑ l, divNoise l x) m :=
    integrable_finset_sum _ fun l _ => hdivNoise l
  have hcongr : ∫ x, Lphip x ∂m
      = ∫ x, (divPhiJ x + phiFp x + 2⁻¹ * ∑ l, divNoise l x) ∂m :=
    integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [hcongr,
    integral_add (f := fun x => divPhiJ x + phiFp x) (g := fun x => 2⁻¹ * ∑ l, divNoise l x)
      (hdivPhiJ.add hphiFp) (hsumInt.const_mul _),
    integral_add (f := divPhiJ) (g := phiFp) hdivPhiJ hphiFp, integral_const_mul,
    integral_finset_sum _ fun l _ => hdivNoise l, hfluxJ]
  have hN : ∑ l, ∫ x, divNoise l x ∂m = ∑ l, ∫ x, noiseFlux l x ∂s :=
    Finset.sum_congr rfl fun l _ => hfluxN l
  rw [hN]
  ring

/-- **Eq. (47)** (Appendix C.3): once the boundary condition of Proposition 11(b) makes
the noise boundary terms of Eq. (46) vanish, the adjoint is carried by the volume
density `F p` and the outward probability current,

  `(L*μ_t)(φ) = ∫_E φ F p dm + ∫_{∂E} φ j^out ds`. -/
theorem eq47_lstar_pair (m s : Measure E) {Lphip phiFp divPhiJ phiJout : E → ℝ}
    {divNoise noiseFlux : Fin r → E → ℝ}
    (hpoint : ∀ x, Lphip x = divPhiJ x + phiFp x + 2⁻¹ * ∑ l, divNoise l x)
    (hdivPhiJ : Integrable divPhiJ m) (hphiFp : Integrable phiFp m)
    (hdivNoise : ∀ l, Integrable (divNoise l) m)
    (hfluxJ : ∫ x, divPhiJ x ∂m = ∫ x, phiJout x ∂s)
    (hfluxN : ∀ l, ∫ x, divNoise l x ∂m = ∫ x, noiseFlux l x ∂s)
    (hvanish : ∀ l, ∫ x, noiseFlux l x ∂s = 0) :
    ∫ x, Lphip x ∂m = (∫ x, phiFp x ∂m) + ∫ x, phiJout x ∂s := by
  rw [eq46_lstar_pair m s hpoint hdivPhiJ hphiFp hdivNoise hfluxJ hfluxN]
  simp [hvanish]

omit [MeasurableSpace E] in
/-- The elementary step of Appendix C.2: at a boundary point where
`p Σ_l ⟨f_l, n⟩² = 0`, either the density vanishes or all the normal components do; in
either case `p ⟨f_l, n⟩ = 0` for every `l`.  This is what makes the last term of
Eq. (46) vanish. -/
theorem density_mul_normal_eq_zero_of_sq {p : E → ℝ} {w : Fin r → E → ℝ} {x : E}
    (h : p x * ∑ l, (w l x) ^ 2 = 0) (l : Fin r) : p x * w l x = 0 := by
  rcases mul_eq_zero.mp h with hp | hw
  · rw [hp, zero_mul]
  · have hzero : ∀ k ∈ Finset.univ, (w k x) ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _).mp hw
    have : w l x = 0 := by
      have := hzero l (Finset.mem_univ l)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    rw [this, mul_zero]

end GSHS
