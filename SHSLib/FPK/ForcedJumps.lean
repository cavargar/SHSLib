/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 6.2 of Bect (2010): a class of models with forced jumps

Assumption 19(a) of the paper describes a GSHS whose jumps are all *forced* (`λ = 0`) and
whose resets are *deterministic*: there is a map `Ψ : G → E⁰` with

  `K(x, ·) = δ_{Ψ(x)}`  for all `x ∈ G`.

Under Assumption 19(b)(c), `Ψ` is a `C¹`-diffeomorphism from the guard `G = ∂E` onto a
closed hypersurface `H = Ψ(G) ⊂ E⁰`, of zero volume measure.

This file formalizes the measure-theoretic consequences of that setup:

* `GSHS.source_deterministic_reset` — the source term `r_t K` is the pushforward
  `Ψ_* r_t` of the mean jump intensity;
* `GSHS.source_eq_zero_of_subset_range` and `GSHS.source_mutuallySingular` — the source
  term is carried by `H`, hence is purely `m`-singular when `m(H) = 0`; this is Bect's
  observation that the pdf cannot be smooth across `H`;
* `GSHS.forcedJump_pdf_evolution` — conclusion 6.2(a): away from `H` the usual
  Fokker–Planck equation `∂p_t/∂t = F p_t` holds, because both the source and the sink
  of the generalized FPK equation vanish there;
* `GSHS.current_conservation` — conclusion 6.2(b), Eq. (36): writing the mean intensity
  of forced jumps as `j_t^out · s` on `G` and the source term as `j_t^in · s_H` on `H`,
  the fact that the source is the pushforward of the sink by the reset map reads

  `j_t^out = d(s_H ∘ Ψ)/ds · (j_t^in ∘ Ψ)`,

  where `s_H ∘ Ψ` denotes the pullback of the surface measure of `H` by `Ψ`.

The reset map is modelled as a measurable equivalence `e : E ≃ᵐ E` (Assumption 19(c):
`Ψ` is a diffeomorphism from `G` onto `H`, and only its behaviour on `G` matters since
all measures involved are carried by `G`, resp. `H`).
-/
import SHSLib.FPK.DensityEvolution
import SHSLib.FPK.ProbabilityFlow

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E]

/-! ## The source term of a deterministic reset -/

/-- **Assumption 19(a)**: with a deterministic reset map `Ψ`, the reset kernel is
`K(x, ·) = δ_{Ψ(x)}` and the source term `r_t K` of the generalized FPK equation is the
pushforward of the mean jump intensity by the reset map. -/
theorem source_deterministic_reset (r : Measure E) {Psi : E → E} (hPsi : Measurable Psi) :
    (Kernel.deterministic Psi hPsi) ∘ₘ r = r.map Psi :=
  Measure.deterministic_comp_eq_map hPsi

/-- The source term `Ψ_* r_t` is carried by any measurable set containing the range of
the reset map — in the model of Section 6.2, by the hypersurface `H = Ψ(G)`. -/
theorem source_eq_zero_of_subset_range (r : Measure E) {Psi : E → E} (hPsi : Measurable Psi)
    {H : Set E} (hH : MeasurableSet H) (hrange : range Psi ⊆ H) :
    (r.map Psi) Hᶜ = 0 := by
  rw [Measure.map_apply hPsi hH.compl]
  convert measure_empty (μ := r)
  ext x
  simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
  exact hrange (mem_range_self x)

/-- Since `H = Ψ(G)` has zero volume measure, the source term `r_t K = Ψ_* r_t` is
purely singular with respect to `m`.  This is the reason why, in the models of
Section 6.2, the density `p_t` fails to be smooth across `H`. -/
theorem source_mutuallySingular (r : Measure E) {Psi : E → E} (hPsi : Measurable Psi)
    (m : Measure E) {H : Set E} (hH : MeasurableSet H) (hrange : range Psi ⊆ H)
    (hm : m H = 0) :
    (r.map Psi) ⟂ₘ m :=
  ⟨Hᶜ, hH.compl, source_eq_zero_of_subset_range r hPsi hH hrange, by simpa using hm⟩

/-- The density of a purely singular source term vanishes almost everywhere: there is no
absolutely continuous contribution of the forced jumps away from `H`. -/
theorem rnDeriv_source_ae_eq_zero (r : Measure E) {Psi : E → E} (hPsi : Measurable Psi)
    (m : Measure E) {H : Set E} (hH : MeasurableSet H) (hrange : range Psi ⊆ H)
    (hm : m H = 0) :
    (r.map Psi).rnDeriv m =ᵐ[m] 0 :=
  (source_mutuallySingular r hPsi m hH hrange hm).rnDeriv_ae_eq_zero

/-! ## Conclusion 6.2(a): the usual Fokker–Planck equation off `H` -/

/-- **Conclusion 6.2(a)**: for a model with forced jumps only (`λ = 0`) and deterministic
resets, the source term is carried by `H`, so both the source `d(r_tK)/dm` and the sink
`λ p_t` of Eq. (23) vanish on `U = E \ H`; hence the *usual* Fokker–Planck equation
`∂p_t/∂t = F p_t` holds `m`-almost everywhere on each component of `E⁰ \ H`. -/
theorem forcedJump_pdf_evolution (m : Measure E) [SigmaFinite m] (U : Set E)
    {dp Fp : E → ℝ}
    (hdp : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ → IntegrableOn dp s (m.restrict U))
    (hFp : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ → IntegrableOn Fp s (m.restrict U))
    (hbal : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ →
      ∫ x in s, dp x ∂(m.restrict U) = ∫ x in s, Fp x ∂(m.restrict U)) :
    dp =ᵐ[m.restrict U] Fp := by
  have h := theorem13_pdf_evolution (dp := dp) (Fp := Fp) (src := fun _ => 0)
    (sink := fun _ => 0) m U hdp (by simpa using hFp) (by simpa using hbal)
  simpa using h

/-! ## Conclusion 6.2(b), Eq. (36): conservation of the probability current -/

/-- Pushing a measure with a density forward by a measurable equivalence gives the
pushforward measure with the transported density. -/
theorem map_withDensity_measurableEquiv (e : E ≃ᵐ E) (mu : Measure E)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (mu.withDensity f).map e = (mu.map e).withDensity (f ∘ e.symm) := by
  ext A hA
  rw [MeasurableEquiv.map_apply, withDensity_apply _ hA, withDensity_apply _ (e.measurable hA),
    ← lintegral_indicator hA, ← lintegral_indicator (e.measurable hA),
    lintegral_map ((hf.comp e.symm.measurable).indicator hA) e.measurable]
  congr 1
  funext x
  by_cases hx : e x ∈ A <;> simp [hx]

/-- **Eq. (36)** (conclusion 6.2(b)): *conservation of the probability current through
the reset map*.

The mean intensity of forced jumps is `r_t^G = j_t^out · s` on the guard `G`, and the
source term `r_t K = Ψ_* r_t^G` is `β_t = j_t^in · s_H` on the hypersurface `H`
(Eq. (35)).  Writing `ν = s_H ∘ Ψ` for the pullback of the surface measure of `H` by the
reset map, and assuming `ν ≪ s`, the identity `Ψ_*(j_t^out · s) = j_t^in · s_H` is
equivalent to

  `j_t^out = d(s_H ∘ Ψ)/ds · (j_t^in ∘ Ψ)`   `s`-almost everywhere. -/
theorem current_conservation (e : E ≃ᵐ E) (s sH : Measure E) [SigmaFinite s]
    {jout jin : E → ℝ≥0∞} (hout : Measurable jout) (hin : Measurable jin)
    [(sH.map e.symm).HaveLebesgueDecomposition s]
    (hac : (sH.map e.symm) ≪ s)
    (hpush : (s.withDensity jout).map e = sH.withDensity jin) :
    jout =ᵐ[s] fun x => ((sH.map e.symm).rnDeriv s x) * jin (e x) := by
  set nu : Measure E := sH.map e.symm with hnu
  -- push both sides of `hpush` back through `e.symm`
  have h1 : ((s.withDensity jout).map e).map e.symm = s.withDensity jout := by
    rw [Measure.map_map e.symm.measurable e.measurable]
    simp
  have h2 : (sH.withDensity jin).map e.symm = nu.withDensity (jin ∘ e) := by
    have := map_withDensity_measurableEquiv e.symm sH hin
    simpa [hnu] using this
  have h3 : s.withDensity jout = nu.withDensity (jin ∘ e) := by
    rw [← h1, hpush, h2]
  -- replace `nu` by its density with respect to `s`
  have h4 : nu = s.withDensity (nu.rnDeriv s) := (Measure.withDensity_rnDeriv_eq nu s hac).symm
  have h5 : s.withDensity jout
      = s.withDensity (fun x => (nu.rnDeriv s x) * jin (e x)) := by
    rw [h3, show (fun x => (nu.rnDeriv s x) * jin (e x))
        = (nu.rnDeriv s) * (jin ∘ e) from rfl,
      withDensity_mul _ (Measure.measurable_rnDeriv nu s) (hin.comp e.measurable)]
    conv_lhs => rw [h4]
  exact (withDensity_eq_iff_of_sigmaFinite hout.aemeasurable
    (((Measure.measurable_rnDeriv nu s).mul (hin.comp e.measurable)).aemeasurable)).1 h5

end GSHS
