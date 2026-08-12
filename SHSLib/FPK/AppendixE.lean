/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Appendix E of Bect (2010): proof of Theorem 13

Under the assumptions of Theorem 13 the region `U` on which Eq. (48) is available is
`m`-conegligible and contains the whole boundary `∂E`.  Consequently the localized
identity (48) globalizes to

  `(L^* μ_t)(Γ ∩ U) = ∫_Γ F p_t dm + ∫_{∂E ∩ Γ} j_t^out ds`,      (51)

so that Eq. (22) collapses to `β_t(Γ) = −(L^* μ_t)(Γ ∩ H)` (the measures `β_t` are
carried by the singular set `H = E \ U`), the generalized FPK equation (14) becomes

  `μ'_t(Γ) = ∫_Γ F p_t dm + ∫_{∂E ∩ Γ} j_t^out ds + (L^* μ_t)(Γ ∩ H) + r_t(K − I)(Γ)`, (52)

and uniqueness of the Lebesgue–Radon–Nikodym decomposition with respect to `m` splits
(52) into the density equation (53) and the singular balance (54).

Formalized here:

* `GSHS.setIntegral_inter_of_ae_univ` — the elementary `m`-a.e. step behind (51);
* `GSHS.eq51_lstarMeasure_inter` — Eq. (51) for the measure `L^* μ_t` of Eq. (48);
* `GSHS.eq22_beta_eq_neg_lstar_inter` — `β_t(Γ) = −(L^* μ_t)(Γ ∩ H)`;
* `GSHS.beta_eq_zero_of_disjoint_singular` — hence `β_t` is carried by `H`;
* `GSHS.eq52_fpk_decomposition` — Eq. (52);
* `GSHS.eq53_eq54_lebesgue_split` — Eqs. (53) and (54), by uniqueness of the
  Lebesgue decomposition.
-/
import SHSLib.FPK.DensityEvolution
import SHSLib.FPK.ProbabilityCurrent

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E]

/-! ## Eq. (51): globalizing the localized form (48) of `L^* μ_t` -/

/-- If the complement of `U` is `m`-null then integrating over `Γ ∩ U` is the same as
integrating over `Γ`.  This is the step `m(E \ U) = 0` of Eq. (51). -/
theorem setIntegral_inter_of_ae_univ (m : Measure E) {U : Set E} (hU : m Uᶜ = 0)
    (f : E → ℝ) (Γ : Set E) : ∫ x in Γ ∩ U, f x ∂m = ∫ x in Γ, f x ∂m := by
  refine setIntegral_congr_set ?_
  refine (ae_eq_set).2 ⟨?_, ?_⟩
  · have : (Γ ∩ U) \ Γ = (∅ : Set E) := by
      ext x; simp +contextual
    rw [this]; simp
  · refine measure_mono_null (fun x hx => ?_) hU
    exact fun hxU => hx.2 ⟨hx.1, hxU⟩

/-- **Eq. (51)**.  When the region `U` on which Eq. (48) holds is `m`-conegligible and
contains the boundary, the measure `L^* μ_t` of Eq. (48) satisfies

  `(L^* μ_t)(Γ ∩ U) = ∫_Γ F p_t dm + ∫_{∂E ∩ Γ} j_t^out ds`,

i.e. restricting to `U` costs nothing. -/
theorem eq51_lstarMeasure_inter (m s : Measure E) {bdry U : Set E} {Fp jout : E → ℝ}
    (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    (hU : m Uᶜ = 0) (hUm : MeasurableSet U) (hbdry : bdry ⊆ U)
    {Γ : Set E} (hΓ : MeasurableSet Γ) :
    lstarMeasure m s bdry Fp jout (Γ ∩ U)
      = (∫ x in Γ, Fp x ∂m) + ∫ y in bdry ∩ Γ, jout y ∂s := by
  have hset : bdry ∩ (Γ ∩ U) = bdry ∩ Γ := by
    ext x
    constructor
    · rintro ⟨hb, hg, -⟩; exact ⟨hb, hg⟩
    · rintro ⟨hb, hg⟩; exact ⟨hb, hg, hbdry hb⟩
  rw [lstarMeasure_apply m s hFp hjout (hΓ.inter hUm),
    setIntegral_inter_of_ae_univ m hU Fp Γ, hset]

/-- **Eq. (51)** restated: on `U`, the abstract Radon measure `L^* μ_t` agrees with the
measure of Eq. (48). -/
theorem eq51_lstar_inter (m s : Measure E) {bdry U : Set E} {Fp jout : E → ℝ}
    (lstar : SignedMeasure E)
    (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    (hU : m Uᶜ = 0) (hUm : MeasurableSet U) (hbdry : bdry ⊆ U)
    {Γ : Set E} (hΓ : MeasurableSet Γ)
    (heq48 : lstar (Γ ∩ U) = lstarMeasure m s bdry Fp jout (Γ ∩ U)) :
    lstar (Γ ∩ U) = (∫ x in Γ, Fp x ∂m) + ∫ y in bdry ∩ Γ, jout y ∂s := by
  rw [heq48, eq51_lstarMeasure_inter m s hFp hjout hU hUm hbdry hΓ]

/-! ## Eq. (22) on `H`: the measures `β_t` are carried by the singular set -/

/-- Additivity of a signed measure along the splitting `Γ = (Γ ∩ U) ∪ (Γ ∩ H)`,
`H = Uᶜ`. -/
theorem signedMeasure_split (lstar : SignedMeasure E) {U Γ : Set E}
    (hUm : MeasurableSet U) (hΓ : MeasurableSet Γ) :
    lstar Γ = lstar (Γ ∩ U) + lstar (Γ ∩ Uᶜ) := by
  have hunion : Γ ∩ U ∪ Γ ∩ Uᶜ = Γ := by
    rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
  have hdisj : Disjoint (Γ ∩ U) (Γ ∩ Uᶜ) :=
    Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right
      disjoint_compl_right
  calc lstar Γ = lstar (Γ ∩ U ∪ Γ ∩ Uᶜ) := by rw [hunion]
    _ = lstar (Γ ∩ U) + lstar (Γ ∩ Uᶜ) :=
        MeasureTheory.VectorMeasure.of_union hdisj (hΓ.inter hUm)
          (hΓ.inter hUm.compl)

/-- **Eq. (22) in the setting of Theorem 13**: under Eq. (51), the defect measure `β_t`
of Eq. (22) is minus the restriction of `L^* μ_t` to the singular set `H = Uᶜ`,

  `β_t(Γ) = −(L^* μ_t)(Γ ∩ H)`. -/
theorem eq22_beta_eq_neg_lstar_inter (m s : Measure E) {bdry U : Set E} {Fp jout : E → ℝ}
    (lstar : SignedMeasure E)
    (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    (hU : m Uᶜ = 0) (hUm : MeasurableSet U) (hbdry : bdry ⊆ U)
    {Γ : Set E} (hΓ : MeasurableSet Γ)
    (heq48 : lstar (Γ ∩ U) = lstarMeasure m s bdry Fp jout (Γ ∩ U)) :
    betaMeasure m s bdry Fp jout lstar Γ = -lstar (Γ ∩ Uᶜ) := by
  rw [betaMeasure_apply m s lstar hFp hjout hΓ,
    signedMeasure_split lstar hUm hΓ,
    eq51_lstar_inter m s lstar hFp hjout hU hUm hbdry hΓ heq48]
  ring

/-- The measures `β_t` are *carried by* `H = Uᶜ`: they vanish on every measurable set
disjoint from `H`. -/
theorem beta_eq_zero_of_disjoint_singular (m s : Measure E) {bdry U : Set E}
    {Fp jout : E → ℝ} (lstar : SignedMeasure E)
    (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    (hU : m Uᶜ = 0) (hUm : MeasurableSet U) (hbdry : bdry ⊆ U)
    {Γ : Set E} (hΓ : MeasurableSet Γ) (hsub : Γ ⊆ U)
    (heq48 : lstar (Γ ∩ U) = lstarMeasure m s bdry Fp jout (Γ ∩ U)) :
    betaMeasure m s bdry Fp jout lstar Γ = 0 := by
  have hempty : Γ ∩ Uᶜ = (∅ : Set E) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
      not_and, not_not]
    exact fun hx => hsub hx
  rw [eq22_beta_eq_neg_lstar_inter m s lstar hFp hjout hU hUm hbdry hΓ heq48, hempty]
  simp

/-! ## Eq. (52): the decomposition of the generalized FPK equation -/

/-- **Eq. (52)**.  Substituting Eq. (51) into the generalized FPK equation (14),

  `μ'_t(Γ) = (L^* μ_t)(Γ) + (r_t K)(Γ) − r_t(Γ)`,

and splitting `L^* μ_t` along `Γ = (Γ ∩ U) ∪ (Γ ∩ H)` yields

  `μ'_t(Γ) = ∫_Γ F p_t dm + ∫_{∂E ∩ Γ} j_t^out ds + (L^* μ_t)(Γ ∩ H)
              + (r_t K)(Γ) − r_t(Γ)`. -/
theorem eq52_fpk_decomposition (m s : Measure E) {bdry U : Set E} {Fp jout : E → ℝ}
    (lstar : SignedMeasure E) {mu' rK r : ℝ}
    (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    (hU : m Uᶜ = 0) (hUm : MeasurableSet U) (hbdry : bdry ⊆ U)
    {Γ : Set E} (hΓ : MeasurableSet Γ)
    (heq48 : lstar (Γ ∩ U) = lstarMeasure m s bdry Fp jout (Γ ∩ U))
    (hfpk : mu' = lstar Γ + rK - r) :
    mu' = (∫ x in Γ, Fp x ∂m) + (∫ y in bdry ∩ Γ, jout y ∂s)
            + lstar (Γ ∩ Uᶜ) + (rK - r) := by
  rw [hfpk, signedMeasure_split lstar hUm hΓ,
    eq51_lstar_inter m s lstar hFp hjout hU hUm hbdry hΓ heq48]
  ring

/-! ## Eqs. (53) and (54): the Lebesgue–Radon–Nikodym split -/

/-- **Eqs. (53) and (54)**.  Write Eq. (52) as an equality of positive measures with the
negative terms moved to the opposite side: the left-hand side is
`(∂p/∂t + λ p_t) m + r_t^G` and the right-hand side is `(F p_t + d(r_tK)/dm) m` plus the
singular contributions (the boundary term, the term carried by `H` and `(r_tK)^⊥`).
Since `r_t^G` and the singular contributions are `m`-singular, uniqueness of the
Lebesgue–Radon–Nikodym decomposition (Theorem 23) gives the density equation (53),

  `∂p/∂t + λ p_t = F p_t + d(r_tK)/dm`   `m`-a.e.,

and the singular balance (54), `r_t^G = boundary + H-term + (r_tK)^⊥`. -/
theorem eq53_eq54_lebesgue_split (m : Measure E) [SigmaFinite m]
    {dpdt sink Fp src : E → ℝ≥0∞}
    (hlhs : Measurable fun x => dpdt x + sink x)
    (hrhs : Measurable fun x => Fp x + src x)
    {rG sing : Measure E} (hrG : rG ⟂ₘ m) (hsing : sing ⟂ₘ m)
    (heq52 : m.withDensity (fun x => dpdt x + sink x) + rG
      = m.withDensity (fun x => Fp x + src x) + sing) :
    (∀ᵐ x ∂m, dpdt x + sink x = Fp x + src x) ∧ rG = sing := by
  obtain ⟨hs, hd⟩ := singular_part_unique m hlhs hrhs hrG hsing heq52
  exact ⟨hd, hs⟩

end GSHS
