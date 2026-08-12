/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 5.3 and Appendix D of Bect (2010): from measures to densities

Theorem 13 turns the measure-valued FPK equation (14) into an evolution equation for the
probability density function,

  `∂p/∂t = F p_t + d(r_t K)/dm − λ p_t`,        (23)

valid on `E⁰ \ H`, together with statements about the `m`-singular part of the source
term `r_t K`.  The geometric ingredients of the proof (the divergence theorem on
manifolds with corners, hence the identification of the absolutely continuous part of
`L^* μ_t` with `F p_t` and of the boundary term with the outward probability current) are
not formalized here; they enter the statements below as hypotheses.  What is formalized
is the measure-theoretic core of the argument:

* `GSHS.theorem13_pdf_evolution` : the measure identity (14), tested on sets contained in
  the region where all the terms are absolutely continuous, forces the pointwise
  equation (23) to hold `m`-almost everywhere;
* `GSHS.singular_part_unique` : the decomposition of a measure into an `m`-absolutely
  continuous part and an `m`-singular part is unique, which is what identifies the
  singular part of `r_t K` with the measures `β_t` of Eq. (22);
* `GSHS.theorem23_lebesgue_radon_nikodym` : the Lebesgue–Radon–Nikodym theorem quoted as
  Theorem 23 in Appendix D, in the form used in the paper.
-/
import SHSLib.FPK.SpontaneousJumps

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E]

/-- **Theorem 13, Eq. (23)** (measure-theoretic core).  Let `dp` be the density of the
time derivative `μ'_t`, `Fp` the density of the absolutely continuous part of
`L^* μ_t`, `src` the density `d(r_t K)/dm` of the source term and `sink` the density
`λ p_t` of the sink term, all with respect to the reference measure `m` restricted to a
region `U` (in the paper, `U = E⁰ \ H`, where no singular contribution is present).  If
the generalized FPK equation (14) holds as an equality of measures on `U`, then the
evolution equation (23) holds `m`-almost everywhere on `U`. -/
theorem theorem13_pdf_evolution (m : Measure E) [SigmaFinite m] (U : Set E)
    {dp Fp src sink : E → ℝ}
    (hdp : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ →
      IntegrableOn dp s (m.restrict U))
    (hrhs : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ →
      IntegrableOn (fun x => Fp x + src x - sink x) s (m.restrict U))
    (hbal : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ →
      ∫ x in s, dp x ∂(m.restrict U)
        = ∫ x in s, (Fp x + src x - sink x) ∂(m.restrict U)) :
    dp =ᵐ[m.restrict U] fun x => Fp x + src x - sink x :=
  ae_eq_of_forall_setIntegral_eq_of_sigmaFinite hdp hrhs hbal

/-- **Uniqueness of the Lebesgue decomposition**, the tool that identifies the
`m`-singular part `(r_t K)^⊥` of the source term with the measures `β_t` of Eq. (22):
if a measure is written in two ways as an absolutely continuous part plus an
`m`-singular part, then both parts agree (the densities `m`-almost everywhere). -/
theorem singular_part_unique (m : Measure E) [SigmaFinite m] {f g : E → ℝ≥0∞}
    {s₁ s₂ : Measure E}
    (hf : Measurable f) (hg : Measurable g) (hs₁ : s₁ ⟂ₘ m) (hs₂ : s₂ ⟂ₘ m)
    (heq : m.withDensity f + s₁ = m.withDensity g + s₂) :
    s₁ = s₂ ∧ f =ᵐ[m] g := by
  set ν : Measure E := m.withDensity f + s₁ with hν
  have hν' : ν = s₁ + m.withDensity f := by rw [hν, add_comm]
  have heq' : ν = s₂ + m.withDensity g := by rw [heq, add_comm]
  have h₁ : s₁ = ν.singularPart m := Measure.eq_singularPart hf hs₁ hν'
  have h₂ : s₂ = ν.singularPart m := Measure.eq_singularPart hg hs₂ heq'
  have hd₁ : f =ᵐ[m] ν.rnDeriv m := Measure.eq_rnDeriv hf hs₁ hν'
  have hd₂ : g =ᵐ[m] ν.rnDeriv m := Measure.eq_rnDeriv hg hs₂ heq'
  exact ⟨h₁.trans h₂.symm, hd₁.trans hd₂.symm⟩

/-- **Theorem 23** (Lebesgue–Radon–Nikodym, Appendix D of Bect (2010)): a σ-finite
measure `ν₁` decomposes as an absolutely continuous part with respect to `ν₂`, with
density the Radon–Nikodym derivative, plus a `ν₂`-singular part; the decomposition is
unique, the density being unique up to `ν₂`-almost everywhere equality.  The
decomposition itself is Eq. (50) of the paper. -/
theorem theorem23_lebesgue_radon_nikodym (ν₁ ν₂ : Measure E) [SigmaFinite ν₁]
    [SigmaFinite ν₂] :
    (ν₁.singularPart ν₂) ⟂ₘ ν₂ ∧
      ν₁ = ν₂.withDensity (ν₁.rnDeriv ν₂) + ν₁.singularPart ν₂ ∧
      ∀ (f : E → ℝ≥0∞) (s : Measure E), Measurable f → s ⟂ₘ ν₂ →
        ν₁ = ν₂.withDensity f + s → s = ν₁.singularPart ν₂ ∧ f =ᵐ[ν₂] ν₁.rnDeriv ν₂ := by
  refine ⟨ν₁.mutuallySingular_singularPart ν₂, ?_, ?_⟩
  · rw [add_comm]
    exact (Measure.singularPart_add_rnDeriv ν₁ ν₂).symm
  · intro f s hf hs hadd
    have hadd' : ν₁ = s + ν₂.withDensity f := by rw [hadd, add_comm]
    exact ⟨Measure.eq_singularPart hf hs hadd', Measure.eq_rnDeriv hf hs hadd'⟩

/-! ## Corollary 15: the evolution equation for models with spontaneous jumps -/

/-- **Corollary 15, Eq. (26)** (Bect, 2010).  For a model with spontaneous jumps only
(`G = ∅`) whose reset kernel satisfies Assumption 14, with mean jump intensity
`r_t = λ μ_t` (Eq. (8)) and `μ_t = p_t m`, the generalized FPK equation in measure form,

  `μ'_t(Γ) = ∫_Γ F p_t dm + (r_t K)(Γ) − r_t(Γ)`,

turns into the evolution equation

  `∂p_t/∂t = F p_t + K*(λ p_t) − λ p_t`,   (26)

which holds `m`-almost everywhere.  The source density `K*(λ p_t)` is produced by
`corollary15_source_eq_withDensity`, i.e. by Assumption 14. -/
theorem corollary15_pdf_evolution (m : Measure E) [SigmaFinite m] {K Kstar : Kernel E E}
    (hdual : IsDualKernel m K Kstar) {lam p : E → ℝ≥0∞}
    (hlam : Measurable lam) (hp : Measurable p) {dp Fp : E → ℝ}
    (hsrc_meas : Measurable fun x => ∫⁻ y, lam y * p y ∂(Kstar x))
    (hsrc_lt_top : ∀ x, (∫⁻ y, lam y * p y ∂(Kstar x)) < ⊤)
    (hsink_lt_top : ∀ x, lam x * p x < ⊤)
    (hdp : ∀ s, MeasurableSet s → m s < ⊤ → IntegrableOn dp s m)
    (hFp : ∀ s, MeasurableSet s → m s < ⊤ → IntegrableOn Fp s m)
    (hsrc : ∀ s, MeasurableSet s → m s < ⊤ →
      IntegrableOn (fun x => (∫⁻ y, lam y * p y ∂(Kstar x)).toReal) s m)
    (hsink : ∀ s, MeasurableSet s → m s < ⊤ →
      IntegrableOn (fun x => (lam x * p x).toReal) s m)
    (hbal : ∀ s, MeasurableSet s → m s < ⊤ →
      ∫ x in s, dp x ∂m
        = (∫ x in s, Fp x ∂m)
          + ((K ∘ₘ (m.withDensity fun x => lam x * p x)) s).toReal
          - ((m.withDensity fun x => lam x * p x) s).toReal) :
    dp =ᵐ[m] fun x => Fp x + (∫⁻ y, lam y * p y ∂(Kstar x)).toReal - (lam x * p x).toReal := by
  have hsource := corollary15_source_eq_withDensity hdual hlam hp
  have hrhs : ∀ s, MeasurableSet s → m s < ⊤ → IntegrableOn
      (fun x => Fp x + (∫⁻ y, lam y * p y ∂(Kstar x)).toReal - (lam x * p x).toReal) s m :=
    fun s hs hfin => ((hFp s hs hfin).add (hsrc s hs hfin)).sub (hsink s hs hfin)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite hdp hrhs (fun s hs hfin => ?_)
  have hsrcval : ((K ∘ₘ (m.withDensity fun x => lam x * p x)) s).toReal
      = ∫ x in s, (∫⁻ y, lam y * p y ∂(Kstar x)).toReal ∂m := by
    rw [hsource, withDensity_apply _ hs,
      integral_toReal hsrc_meas.aemeasurable
        (Filter.Eventually.of_forall fun x => hsrc_lt_top x)]
  have hsinkval : ((m.withDensity fun x => lam x * p x) s).toReal
      = ∫ x in s, (lam x * p x).toReal ∂m := by
    rw [withDensity_apply _ hs,
      integral_toReal (hlam.mul hp).aemeasurable
        (Filter.Eventually.of_forall fun x => hsink_lt_top x)]
  have hsplit : ∫ x in s, (Fp x + (∫⁻ y, lam y * p y ∂(Kstar x)).toReal
        - (lam x * p x).toReal) ∂m
      = (∫ x in s, Fp x ∂m) + (∫ x in s, (∫⁻ y, lam y * p y ∂(Kstar x)).toReal ∂m)
        - ∫ x in s, (lam x * p x).toReal ∂m := by
    have e1 : ∫ x in s, (Fp x + (∫⁻ y, lam y * p y ∂(Kstar x)).toReal
          - (lam x * p x).toReal) ∂m
        = (∫ x in s, (Fp x + (∫⁻ y, lam y * p y ∂(Kstar x)).toReal) ∂m)
          - ∫ x in s, (lam x * p x).toReal ∂m :=
      integral_sub ((hFp s hs hfin).add (hsrc s hs hfin)) (hsink s hs hfin)
    have e2 : ∫ x in s, (Fp x + (∫⁻ y, lam y * p y ∂(Kstar x)).toReal) ∂m
        = (∫ x in s, Fp x ∂m) + ∫ x in s, (∫⁻ y, lam y * p y ∂(Kstar x)).toReal ∂m :=
      integral_add (hFp s hs hfin) (hsrc s hs hfin)
    rw [e1, e2]
  rw [hbal s hs hfin, hsrcval, hsinkval, hsplit]

/-! ## Theorem 13(c)(d): the conservation equations for the singular part -/

/-- **Theorem 13(c)**.  Eq. (54) of Appendix E reads

  `0 = ∫_{∂E ∩ Γ} j^out ds + (L^*μ_t)(Γ ∩ H) + (r_tK)^⊥(Γ) − r_t^G(Γ)`.

Tested on subsets of the interior hypersurface `H`, the boundary integral vanishes (`H`
does not meet `∂E`) and so does the mean intensity of forced jumps (which is carried by
the guard `G ⊆ ∂E`), leaving `(r_tK)^⊥ = β_t` on `H`, with `β_t(Γ) = −(L^*μ_t)(Γ ∩ H)`
the measures of Eq. (22).  Being the value of a positive measure, `β_t ≥ 0`. -/
theorem theorem13_singular_on_H (s : Measure E) (Lstar : Set E → ℝ)
    (rKsing rG : Measure E) {jout : E → ℝ} {H bdry : Set E}
    (hdisj : Disjoint H bdry)
    (hrG : ∀ Γ, MeasurableSet Γ → Γ ⊆ H → rG Γ = 0)
    (hbal : ∀ Γ, MeasurableSet Γ →
      (0 : ℝ) = (∫ y in bdry ∩ Γ, jout y ∂s) + Lstar (Γ ∩ H) + (rKsing Γ).toReal
        - (rG Γ).toReal) :
    ∀ Γ, MeasurableSet Γ → Γ ⊆ H →
      (rKsing Γ).toReal = -Lstar (Γ ∩ H) ∧ 0 ≤ -Lstar (Γ ∩ H) := by
  intro Γ hΓ hsub
  have hempty : bdry ∩ Γ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    exact (Set.disjoint_left.1 hdisj (hsub hx2)) hx1
  have hint : (∫ y in bdry ∩ Γ, jout y ∂s) = 0 := by rw [hempty]; simp
  have hzero : (rG Γ).toReal = 0 := by rw [hrG Γ hΓ hsub]; simp
  have h := hbal Γ hΓ
  rw [hint, hzero] at h
  have hval : (rKsing Γ).toReal = -Lstar (Γ ∩ H) := by linarith
  exact ⟨hval, hval ▸ ENNReal.toReal_nonneg⟩

/-- **Theorem 13(d)**.  Tested on subsets of `∂E \ G`, Eq. (54) loses the term supported
by `H` and the mean intensity of forced jumps (carried by `G`), so the singular part of
the source term is minus the outward flow of the probability current there,
`(r_tK)^⊥ = −∫ j^out ds ≥ 0`: the current points inwards on the part of the boundary
that is not a guard. -/
theorem theorem13_singular_off_guard (s : Measure E) (Lstar : Set E → ℝ)
    (rKsing rG : Measure E) {jout : E → ℝ} {H bdry G : Set E}
    (hdisj : Disjoint H bdry) (hLzero : Lstar ∅ = 0)
    (hrG : ∀ Γ, MeasurableSet Γ → Γ ⊆ bdry \ G → rG Γ = 0)
    (hbal : ∀ Γ, MeasurableSet Γ →
      (0 : ℝ) = (∫ y in bdry ∩ Γ, jout y ∂s) + Lstar (Γ ∩ H) + (rKsing Γ).toReal
        - (rG Γ).toReal) :
    ∀ Γ, MeasurableSet Γ → Γ ⊆ bdry \ G →
      (rKsing Γ).toReal = -∫ y in Γ, jout y ∂s ∧ (∫ y in Γ, jout y ∂s) ≤ 0 := by
  intro Γ hΓ hsub
  have hsubb : Γ ⊆ bdry := fun x hx => (hsub hx).1
  have hinter : bdry ∩ Γ = Γ := Set.inter_eq_right.2 hsubb
  have hHempty : Γ ∩ H = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    exact (Set.disjoint_left.1 hdisj hx2) (hsubb hx1)
  have hzero : (rG Γ).toReal = 0 := by rw [hrG Γ hΓ hsub]; simp
  have h := hbal Γ hΓ
  rw [hinter, hHempty, hLzero, hzero] at h
  have hval : (rKsing Γ).toReal = -∫ y in Γ, jout y ∂s := by linarith
  refine ⟨hval, ?_⟩
  have := ENNReal.toReal_nonneg (a := rKsing Γ)
  rw [hval] at this
  linarith

end GSHS
