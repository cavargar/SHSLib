/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Appendix A of Bect (2010): the divergence theorem

Assumption 10 of the paper requires each domain `E_q` to be a `C²`-manifold with
corners, which is exactly what makes the divergence theorem (Theorem 21)

  `∫_E div(f) dm = ∫_{∂E} ⟨f, n⟩ ds`

available; this is the key tool used in Appendix C.1 to compute `L^* μ_t`.

This file provides the divergence theorem for the basic example of a manifold with
corners, a box `[a, b] ⊂ ℝⁿ⁺¹`, in the form used in the paper:

* `GSHS.boxFlux` — the boundary flux `∫_{∂E} ⟨f, n⟩ ds`, written face by face: the
  outward normal on the upper face in direction `i` is `+eᵢ` and on the lower face is
  `−eᵢ`, and the surface measure of each face is the `n`-dimensional Lebesgue measure;
* `GSHS.theorem21_divergence_box` — Theorem 21 for a box;
* `GSHS.hasPDerivAt_of_hasFDerivAt` and `GSHS.divergence_eq_sum_pDeriv` — the bridge to
  the partial-derivative calculus of `SHSLib.FPK.ProbabilityCurrent`: the divergence
  `Σᵢ ∂fⁱ/∂zⁱ` computed from partial derivatives agrees with the trace of the Fréchet
  derivative.
-/
import SHSLib.FPK.ProbabilityCurrent

open MeasureTheory Set

noncomputable section

namespace GSHS

variable {n : ℕ}

/-- The outward flux `∫_{∂E} ⟨F, n⟩ ds` of a vector field `F` through the boundary of the
box `[a, b] ⊂ ℝⁿ⁺¹`: on the upper face in direction `i` the outward normal is `+eᵢ`, on
the lower face it is `−eᵢ`, and the surface measure of a face is the `n`-dimensional
Lebesgue measure. -/
def boxFlux (a b : Fin (n + 1) → ℝ) (F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i)
    - ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i)

/-- **Theorem 21** (divergence theorem) for a box `[a, b] ⊂ ℝⁿ⁺¹`, the model case of a
`C²`-manifold with corners: the integral of the divergence of a `C¹` vector field over
the box equals the outward flux of the field through its boundary. -/
theorem theorem21_divergence_box (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (F' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (hcont : ContinuousOn F (Icc a b))
    (hderiv : ∀ x ∈ Set.univ.pi fun i => Ioo (a i) (b i), HasFDerivAt F (F' x) x)
    {divF : (Fin (n + 1) → ℝ) → ℝ}
    (hdivF : ∀ x, divF x = ∑ i, (F' x) (Pi.single i 1) i)
    (hint : IntegrableOn divF (Icc a b)) :
    ∫ x in Icc a b, divF x = boxFlux a b F := by
  have hint' : IntegrableOn (fun x => ∑ i, (F' x) (Pi.single i 1) i) (Icc a b) := by
    refine hint.congr ?_
    filter_upwards with x using (hdivF x)
  have h := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
    a b hab F F' ∅ Set.countable_empty hcont (by simpa using hderiv) hint'
  calc ∫ x in Icc a b, divF x = ∫ x in Icc a b, ∑ i, (F' x) (Pi.single i 1) i := by
        exact setIntegral_congr_fun measurableSet_Icc fun x _ => hdivF x
    _ = boxFlux a b F := h

/-- The partial derivatives of a Fréchet-differentiable vector field: `∂Fⁱ/∂zʲ` is the
`i`-th component of `F'` applied to the `j`-th coordinate direction. -/
theorem hasPDerivAt_of_hasFDerivAt {F : (Fin n → ℝ) → Fin n → ℝ}
    {F' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {x : Fin n → ℝ} (h : HasFDerivAt F F' x) (i j : Fin n) :
    HasPDerivAt (fun y => F y i) j x (F' (Pi.single j 1) i) := by
  have hup : HasDerivAt (fun t : ℝ => Function.update x j t) (Pi.single j 1) (x j) :=
    hasDerivAt_update x j (x j)
  have h' : HasFDerivAt F F' (Function.update x j (x j)) := by rwa [Function.update_eq_self]
  have hcomp : HasDerivAt (fun t : ℝ => F (Function.update x j t)) (F' (Pi.single j 1)) (x j) :=
    h'.comp_hasDerivAt (x j) hup
  have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
    |>.comp_hasDerivAt (x j) hcomp
  simpa using hproj

/-- The divergence computed from partial derivatives agrees with the trace of the
Fréchet derivative: `Σᵢ ∂Fⁱ/∂zⁱ = Σᵢ (F' eᵢ)ⁱ`. -/
theorem divergence_eq_sum_pDeriv {F : (Fin n → ℝ) → Fin n → ℝ}
    {F' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {x : Fin n → ℝ} {d : Fin n → ℝ}
    (h : HasFDerivAt F F' x) (hd : ∀ i, HasPDerivAt (fun y => F y i) i x (d i)) :
    ∑ i, d i = ∑ i, (F' (Pi.single i 1)) i :=
  Finset.sum_congr rfl fun i _ => (hd i).unique (hasPDerivAt_of_hasFDerivAt h i i)

end GSHS
