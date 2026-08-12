/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Appendix B of Bect (2010): Eqs. (42) and (43)

In the direction "(b) and (c) ⟹ (a)" of Theorem 8, Eq. (13) is rewritten, for every
`φ ∈ C_c²(E)`, as

  `∬_{G × ]0;t]} φ (R^G(dx,ds) − (L^*μ_s)(dx) ds)
      = ∬_{E⁰ × ]0;t]} φ ((R^G K)(dx,ds) − ξ_s(dx) ds)`,      (42)

with `ξ_s = μ'_s − (L^*μ_s)(E⁰ ∩ ·) − r⁰(K − I)`.  Approximation extends (42) to
`φ = 1_Γ` with `Γ` a compact subset of the guard set `G`; for such a `Γ` the right-hand
side vanishes — it only sees the part of the state space outside `G` — which yields

  `R^G(Γ × ]0;t]) = ∫₀ᵗ (L^*μ_s)(Γ) ds`.                       (43)

Eq. (43) is the hypothesis `hR` from which `GSHS.theorem8_bc_imp_a` extracts the
positivity of `(L^*μ_t)(Γ)`, hence the existence of the mean jump intensity `r^G` of the
forced jumps.  This file supplies the two missing links:

* `GSHS.eq42_of_eq13` — the rearrangement of Eq. (13) into Eq. (42);
* `GSHS.source_eq_zero_on_guard` — the reset kernel maps into `E⁰`, so the source
  measure `R^G K` gives no mass to subsets of the guard set;
* `GSHS.eq42_rhs_eq_zero_of_subset_guard` — the right-hand side of (42) vanishes when
  `φ = 1_Γ` and `Γ ⊆ G`;
* `GSHS.eq43_of_eq42` — Eq. (43).
-/
import SHSLib.FPK.TotalVariationBounds

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E]

/-- **Eq. (42)** as a rearrangement of Eq. (13).  Writing the tested form of Eq. (13),

  `∫₀ᵗ μ'_s φ ds = ∫₀ᵗ (L^*μ_s)(1_G φ) ds + ∫₀ᵗ (L^*μ_s)(1_{E⁰} φ) ds
                     + ∫₀ᵗ r_s⁰(K−I)φ ds + (R^G K)(φ) − R^G(φ)`,

and setting `ξ = μ' − (L^*μ)(E⁰ ∩ ·) − r⁰(K−I)`, one obtains Eq. (42),

  `R^G(φ) − ∫₀ᵗ (L^*μ_s)(1_G φ) ds = (R^G K)(φ) − ∫₀ᵗ ξ_s φ ds`. -/
theorem eq42_of_eq13 {muPrime lstarG lstarE0 r0Jump RG RGK : ℝ}
    (h13 : muPrime = lstarG + lstarE0 + r0Jump + (RGK - RG)) :
    RG - lstarG = RGK - (muPrime - lstarE0 - r0Jump) := by linarith

/-- The reset kernel `K` is a kernel from `E` to `E⁰ = E \ G`: it never resets the state
into the guard set.  Consequently the source measure `R^G K` gives no mass to a set
contained in `G`. -/
theorem source_eq_zero_on_guard {RG : Measure E} {K : Kernel E E} {G Gam : Set E}
    (hGam : MeasurableSet Gam) (hsub : Gam ⊆ G) (hK : ∀ x, K x G = 0) :
    (K ∘ₘ RG) Gam = 0 := by
  have hx : ∀ x, K x Gam = 0 := fun x => measure_mono_null hsub (hK x)
  rw [Measure.bind_apply hGam (Kernel.aemeasurable _)]
  simp [hx]

/-- The right-hand side of Eq. (42) vanishes for `φ = 1_Γ` with `Γ ⊆ G`: both the source
measure `R^G K` and the measures `ξ_s` are carried by `E⁰`, which is disjoint from
`Γ`. -/
theorem eq42_rhs_eq_zero_of_subset_guard {RGK : Measure E} {xi : ℝ → Measure E}
    {G Gam : Set E} (hG : MeasurableSet G) (hsub : Gam ⊆ G)
    (hRGK : RGK Gᶜ = RGK univ) (hxi : ∀ s, xi s Gᶜ = xi s univ)
    (hRGKfin : RGK univ ≠ ⊤) (hxifin : ∀ s, xi s univ ≠ ⊤) (t : ℝ) :
    (RGK Gam).toReal - ∫ s in Set.Ioc (0 : ℝ) t, (xi s Gam).toReal = 0 := by
  have hzero : ∀ (nu : Measure E), nu Gᶜ = nu univ → nu univ ≠ ⊤ → nu Gam = 0 := by
    intro nu hnu hfin
    have hle : nu Gam ≤ nu G := measure_mono hsub
    have hsum : nu G + nu Gᶜ = nu univ := measure_add_measure_compl hG
    have hcfin : nu Gᶜ ≠ ⊤ := by rw [hnu]; exact hfin
    have hG0 : nu G = 0 := by
      have hstep : nu G + nu Gᶜ = 0 + nu Gᶜ := by rw [hsum, zero_add, hnu]
      exact (ENNReal.add_left_inj hcfin).mp hstep
    exact le_antisymm (hG0 ▸ hle) (zero_le _)
  have h1 : RGK Gam = 0 := hzero RGK hRGK hRGKfin
  have h2 : ∀ s, xi s Gam = 0 := fun s => hzero (xi s) (hxi s) (hxifin s)
  simp [h1, h2]

/-- **Eq. (43)**: for `Γ ⊆ G`, Eq. (42) tested against `1_Γ` reduces to
`R^G(Γ × ]0;t]) = ∫₀ᵗ (L^*μ_s)(Γ) ds`.  This is the hypothesis from which
`GSHS.theorem8_bc_imp_a` derives the positivity of `(L^*μ_t)(Γ)`. -/
theorem eq43_of_eq42 {RG lstarG rhs : ℝ} (heq42 : RG - lstarG = rhs) (hrhs : rhs = 0) :
    RG = lstarG := by
  rw [hrhs] at heq42
  linarith

end GSHS
