/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Appendix C.1 of Bect (2010) on a box: Eq. (46) proved from the divergence theorem

`SHSLib.FPK.ProbabilityCurrent` contains the pointwise differential identities of
Appendix C.1 — Eq. (44), Eq. (45) and `F p = −div(j)` — and
`SHSLib.FPK.DivergenceTheorem` contains Theorem 21 (the divergence theorem) for the
model case of a `C²`-manifold with corners, a box `[a, b] ⊂ ℝⁿ⁺¹`.

This file puts the two together and *proves* the computation of `L^* μ_t` of Eq. (46),

  `∫_E (Lφ) p dm = ∫_E φ F p dm + ∫_{∂E} ⟨φ j, n⟩ ds + ½ Σ_l ∫_{∂E} ⟨(f_l φ) p f_l, n⟩ ds`,

on a box, with the two boundary terms given by the face-by-face flux `GSHS.boxFlux` of
`SHSLib.FPK.DivergenceTheorem`.  Nothing about the identity is assumed: the hypotheses
are the differentiability data of the density `p`, of the vector fields `f₀`, `f_l` and
of the test function `φ` (the paper's Assumption 2 and the `C^{2,1}` smoothness of `p`),
plus the integrability of the three integrands.

Main results:

* `GSHS.generator_density_eq_divergence_sum` — the pointwise identity
  `(Lφ) p = div(φ j) + φ F p + ½ Σ_l div((f_l φ) p f_l)`, i.e. Eqs. (44)–(45) combined;
* `GSHS.appendixC1_eq46_box` — **Eq. (46)** on a box.
-/
import SHSLib.FPK.DivergenceTheorem

open MeasureTheory Set

noncomputable section

namespace GSHS

variable {n r : ℕ}

/-- **Eq. (16)**: the probability current `jⁱ = f₀ⁱ p − ½ Σ_j ∂(aⁱʲ p)/∂zʲ`, written in
terms of a family `gap y i j` of values of the partial derivatives `∂(aⁱʲ p)/∂zʲ`. -/
def currentField (f0 : (Fin n → ℝ) → Fin n → ℝ) (gap : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (p : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  f0 y i * p y - 2⁻¹ * ∑ j, gap y i j

/-- **Eq. (4)**: the value `(Lφ)(x) = Σ_i f₀ⁱ ∂φ/∂zⁱ + ½ Σ_{i,j} aⁱʲ ∂²φ/∂zⁱ∂zʲ` of the
differential generator of the diffusion at `x`, in terms of the gradient `gphi` and the
Hessian `ddphi` of the test function. -/
def generatorVal (f0 : (Fin n → ℝ) → Fin n → ℝ) (f : Fin r → (Fin n → ℝ) → Fin n → ℝ)
    (gphi : (Fin n → ℝ) → Fin n → ℝ) (ddphi : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, f0 x i * gphi x i + 2⁻¹ * ∑ i, ∑ j, diffusionMatrix f x i j * ddphi x i j

section

variable {f : Fin r → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
  {f0 : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
  {p phi : (Fin (n + 1) → ℝ) → ℝ}
  {dp : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
  {df : (Fin (n + 1) → ℝ) → Fin r → Fin (n + 1) → Fin (n + 1) → ℝ}
  {gphi : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
  {ddphi : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ}
  {gap : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ}
  {dfp : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
  {ddgap : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ}
  {V' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
  {W' : Fin r → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}

/-- **Eqs. (44) and (45) combined**: the pointwise identity

  `(Lφ) p = div(φ j) + φ F p + ½ Σ_l div((f_l φ) p f_l)`,

where the two divergences are computed as traces of the Fréchet derivatives `V'` of the
vector field `φ j` and `W' l` of the vector fields `(f_l φ) p f_l`, and `F p` is the
formal adjoint (21) evaluated through `GSHS.formalAdjointVal`.

The hypotheses are exactly the differentiability data of Appendix C.1: `dp`, `df`, `gphi`,
`ddphi` are the first partial derivatives of the density, of the noise vector fields and
of the test function together with its second derivatives; `gap x i j = ∂(aⁱʲ p)/∂zʲ(x)`,
`dfp x i = ∂(f₀ⁱ p)/∂zⁱ(x)` and `ddgap x i j = ∂²(aⁱʲ p)/∂zⁱ∂zʲ(x)`. -/
theorem generator_density_eq_divergence_sum
    (hp : ∀ x j, HasPDerivAt p j x (dp x j))
    (hf : ∀ x l k j, HasPDerivAt (fun y => f l y k) j x (df x l k j))
    (hphi : ∀ x i, HasPDerivAt phi i x (gphi x i))
    (hddphi : ∀ x i j, HasPDerivAt (fun y => gphi y i) j x (ddphi x i j))
    (hgap_def : ∀ x i j, HasPDerivAt (fun y => diffusionMatrix f y i j * p y) j x (gap x i j))
    (hfp : ∀ x i, HasPDerivAt (fun y => f0 y i * p y) i x (dfp x i))
    (hgap_deriv : ∀ x i j, HasPDerivAt (fun y => gap y i j) i x (ddgap x i j))
    (hV : ∀ x, HasFDerivAt (fun y i => phi y * currentField f0 gap p y i) (V' x) x)
    (hW : ∀ l x, HasFDerivAt (noiseField f gphi p l) (W' l x) x)
    (x : Fin (n + 1) → ℝ) :
    generatorVal f0 f gphi ddphi x * p x
      = (∑ i, (V' x (Pi.single i 1)) i) + phi x * formalAdjointVal (dfp x) (ddgap x)
        + 2⁻¹ * ∑ l, ∑ j, (W' l x (Pi.single j 1)) j := by
  -- the values `gap x i j` are the derivatives of the diffusion matrix times the density
  have hgapval : ∀ i j, gap x i j
      = (∑ l, (df x l i j * f l x j + f l x i * df x l j j)) * p x
        + diffusionMatrix f x i j * dp x j := fun i j =>
    (hgap_def x i j).unique (hasPDerivAt_diffusionMatrix_mul (hf x) (hp x) i j)
  -- Eq. (44)
  have hJx : ∀ i, currentField f0 gap p x i
      = f0 x i * p x - 2⁻¹ * ∑ j, ((∑ l, (df x l i j * f l x j + f l x i * df x l j j)) * p x
          + diffusionMatrix f x i j * dp x j) := by
    intro i
    simp only [currentField]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun j _ => hgapval i j
  have h44 := generator_mul_density_eq (f := f) (p := p) (x := x) (df := df x) (dp := dp x)
    (f0 := f0) (gphi := gphi) (ddphi := ddphi x) (Jx := currentField f0 gap p x) hJx
  -- `F p = −div(j)` and the derivatives of the current
  obtain ⟨hdJ, hsum⟩ := divergence_current_eq_neg_formalAdjoint (p := p) (x := x)
    (Jf := currentField f0 gap p) (gapf := gap) (f0 := f0) (dfp := dfp x) (ddgap := ddgap x)
    (fun _ _ => rfl) (hfp x) (hgap_deriv x)
  -- Eq. (45)
  have h45 := current_dot_grad_eq (x := x) (Jf := currentField f0 gap p) (phi := phi)
    (dphi := gphi x) (dJ := fun i => dfp x i - 2⁻¹ * ∑ j, ddgap x i j)
    (formalAdjointVal (dfp x) (ddgap x)) hsum
  -- the divergence of `φ j` is the trace of `V'`
  have hdivV : ∑ i, (gphi x i * currentField f0 gap p x i
        + phi x * (dfp x i - 2⁻¹ * ∑ j, ddgap x i j))
      = ∑ i, (V' x (Pi.single i 1)) i :=
    divergence_eq_sum_pDeriv (hV x) fun i => hasPDerivAt_mul_current (hphi x) hdJ i
  -- the divergence of `(f_l φ) p f_l` is the trace of `W' l`
  have hdivW : ∀ l, (∑ j, ((∑ i, (df x l i j * gphi x i + f l x i * ddphi x i j))
        * (p x * f l x j)
        + (∑ i, f l x i * gphi x i) * (dp x j * f l x j + p x * df x l j j)))
      = ∑ j, (W' l x (Pi.single j 1)) j := fun l =>
    divergence_eq_sum_pDeriv (hW l x) fun j =>
      hasPDerivAt_noiseField (hf x) (hp x) (hddphi x) l j
  calc generatorVal f0 f gphi ddphi x * p x
      = (∑ i, currentField f0 gap p x i * gphi x i)
        + 2⁻¹ * ∑ l, ∑ j, ((∑ i, (df x l i j * gphi x i + f l x i * ddphi x i j))
            * (p x * f l x j)
          + (∑ i, f l x i * gphi x i) * (dp x j * f l x j + p x * df x l j j)) := h44
    _ = ((∑ i, (gphi x i * currentField f0 gap p x i
            + phi x * (dfp x i - 2⁻¹ * ∑ j, ddgap x i j)))
          + phi x * formalAdjointVal (dfp x) (ddgap x))
        + 2⁻¹ * ∑ l, ∑ j, ((∑ i, (df x l i j * gphi x i + f l x i * ddphi x i j))
            * (p x * f l x j)
          + (∑ i, f l x i * gphi x i) * (dp x j * f l x j + p x * df x l j j)) := by
          rw [h45]
    _ = (∑ i, (V' x (Pi.single i 1)) i) + phi x * formalAdjointVal (dfp x) (ddgap x)
        + 2⁻¹ * ∑ l, ∑ j, (W' l x (Pi.single j 1)) j := by
          rw [hdivV, Finset.sum_congr rfl fun l _ => hdivW l]

/-- **Eq. (46)** (Appendix C.1) on a box `[a, b] ⊂ ℝⁿ⁺¹`, the model case of a
`C²`-manifold with corners (Assumption 10):

  `∫_E (Lφ) p dm = ∫_E φ F p dm + ∫_{∂E} ⟨φ j, n⟩ ds + ½ Σ_l ∫_{∂E} ⟨(f_l φ) p f_l, n⟩ ds`.

The two boundary integrals are the face-by-face outward fluxes `GSHS.boxFlux` of the
vector fields `φ j` (the probability current weighted by the test function) and
`(f_l φ) p f_l`.  The proof combines the pointwise identity
`GSHS.generator_density_eq_divergence_sum` (Eqs. (44)–(45)) with the divergence theorem
`GSHS.theorem21_divergence_box` (Theorem 21). -/
theorem appendixC1_eq46_box (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (hp : ∀ x j, HasPDerivAt p j x (dp x j))
    (hf : ∀ x l k j, HasPDerivAt (fun y => f l y k) j x (df x l k j))
    (hphi : ∀ x i, HasPDerivAt phi i x (gphi x i))
    (hddphi : ∀ x i j, HasPDerivAt (fun y => gphi y i) j x (ddphi x i j))
    (hgap_def : ∀ x i j, HasPDerivAt (fun y => diffusionMatrix f y i j * p y) j x (gap x i j))
    (hfp : ∀ x i, HasPDerivAt (fun y => f0 y i * p y) i x (dfp x i))
    (hgap_deriv : ∀ x i j, HasPDerivAt (fun y => gap y i j) i x (ddgap x i j))
    (hV : ∀ x, HasFDerivAt (fun y i => phi y * currentField f0 gap p y i) (V' x) x)
    (hW : ∀ l x, HasFDerivAt (noiseField f gphi p l) (W' l x) x)
    (hintV : IntegrableOn (fun x => ∑ i, (V' x (Pi.single i 1)) i) (Icc a b))
    (hintFp : IntegrableOn (fun x => phi x * formalAdjointVal (dfp x) (ddgap x)) (Icc a b))
    (hintW : ∀ l, IntegrableOn (fun x => ∑ j, (W' l x (Pi.single j 1)) j) (Icc a b)) :
    ∫ x in Icc a b, generatorVal f0 f gphi ddphi x * p x
      = (∫ x in Icc a b, phi x * formalAdjointVal (dfp x) (ddgap x))
        + boxFlux a b (fun y i => phi y * currentField f0 gap p y i)
        + 2⁻¹ * ∑ l, boxFlux a b (noiseField f gphi p l) := by
  classical
  -- the flux of `φ j` through the boundary of the box
  have hfluxV : ∫ x in Icc a b, (∑ i, (V' x (Pi.single i 1)) i)
      = boxFlux a b (fun y i => phi y * currentField f0 gap p y i) :=
    theorem21_divergence_box a b hab _ V'
      (fun x _ => ((hV x).differentiableAt.continuousAt).continuousWithinAt)
      (fun x _ => hV x) (fun _ => rfl) hintV
  -- the fluxes of the noise fields `(f_l φ) p f_l`
  have hfluxW : ∀ l, ∫ x in Icc a b, (∑ j, (W' l x (Pi.single j 1)) j)
      = boxFlux a b (noiseField f gphi p l) := fun l =>
    theorem21_divergence_box a b hab _ (W' l)
      (fun x _ => (((hW l x).differentiableAt).continuousAt).continuousWithinAt)
      (fun x _ => hW l x) (fun _ => rfl) (hintW l)
  have hsumW : IntegrableOn (fun x => ∑ l, ∑ j, (W' l x (Pi.single j 1)) j) (Icc a b) :=
    integrable_finset_sum _ fun l _ => hintW l
  have hpt : ∀ x ∈ Icc a b, generatorVal f0 f gphi ddphi x * p x
      = (∑ i, (V' x (Pi.single i 1)) i) + phi x * formalAdjointVal (dfp x) (ddgap x)
        + 2⁻¹ * ∑ l, ∑ j, (W' l x (Pi.single j 1)) j := fun x _ =>
    generator_density_eq_divergence_sum hp hf hphi hddphi hgap_def hfp hgap_deriv hV hW x
  have e1 : ∫ x in Icc a b, ((∑ i, (V' x (Pi.single i 1)) i
          + phi x * formalAdjointVal (dfp x) (ddgap x))
        + 2⁻¹ * ∑ l, ∑ j, (W' l x (Pi.single j 1)) j)
      = (∫ x in Icc a b, (∑ i, (V' x (Pi.single i 1)) i
            + phi x * formalAdjointVal (dfp x) (ddgap x)))
        + ∫ x in Icc a b, 2⁻¹ * ∑ l, ∑ j, (W' l x (Pi.single j 1)) j :=
    integral_add (hintV.add hintFp) (hsumW.const_mul _)
  have e2 : ∫ x in Icc a b, (∑ i, (V' x (Pi.single i 1)) i
          + phi x * formalAdjointVal (dfp x) (ddgap x))
      = (∫ x in Icc a b, ∑ i, (V' x (Pi.single i 1)) i)
        + ∫ x in Icc a b, phi x * formalAdjointVal (dfp x) (ddgap x) :=
    integral_add hintV hintFp
  have e3 : ∫ x in Icc a b, 2⁻¹ * ∑ l, ∑ j, (W' l x (Pi.single j 1)) j
      = 2⁻¹ * ∫ x in Icc a b, ∑ l, ∑ j, (W' l x (Pi.single j 1)) j :=
    integral_const_mul _ _
  have e4 : ∫ x in Icc a b, ∑ l, ∑ j, (W' l x (Pi.single j 1)) j
      = ∑ l, ∫ x in Icc a b, ∑ j, (W' l x (Pi.single j 1)) j :=
    integral_finset_sum _ fun l _ => hintW l
  rw [setIntegral_congr_fun measurableSet_Icc hpt, e1, e2, e3, e4, hfluxV,
    Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hfluxW l)]
  ring

/-- **Proposition 11(b) on a box**: the absorbing boundary condition makes the noise
boundary terms of Eq. (46) vanish.  On a box the outward normal of a face is `±eᵢ`, so
the normal component of the vector field `(f_l φ) p f_l` on the two faces orthogonal to
`eᵢ` is `(f_l φ) p f_lⁱ`; if `p f_lⁱ = 0` there — which is what Appendix C.2 establishes
— the whole flux vanishes. -/
theorem boxFlux_noiseField_eq_zero (a b : Fin (n + 1) → ℝ) (l : Fin r)
    (hbc : ∀ (i : Fin (n + 1)) (y : Fin n → ℝ),
      p (i.insertNth (a i) y) * f l (i.insertNth (a i) y) i = 0 ∧
        p (i.insertNth (b i) y) * f l (i.insertNth (b i) y) i = 0) :
    boxFlux a b (noiseField f gphi p l) = 0 := by
  have hzero : ∀ (i : Fin (n + 1)) (c : ℝ) (y : Fin n → ℝ),
      p (i.insertNth c y) * f l (i.insertNth c y) i = 0 →
      noiseField f gphi p l (i.insertNth c y) i = 0 := by
    intro i c y h
    have : noiseField f gphi p l (i.insertNth c y) i
        = (∑ k, f l (i.insertNth c y) k * gphi (i.insertNth c y) k)
          * (p (i.insertNth c y) * f l (i.insertNth c y) i) := by
      simp [noiseField, mul_assoc]
    rw [this, h, mul_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hb : ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      noiseField f gphi p l (i.insertNth (b i) y) i = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    exact hzero i (b i) y (hbc i y).2
  have ha : ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      noiseField f gphi p l (i.insertNth (a i) y) i = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    exact hzero i (a i) y (hbc i y).1
  rw [hb, ha, sub_zero]

/-- **Eq. (47)** (Appendix C.3) on a box: once the absorbing boundary condition of
Proposition 11(b) has removed the noise boundary terms, Eq. (46) becomes

  `∫_E (Lφ) p dm = ∫_E φ F p dm + ∫_{∂E} ⟨φ j, n⟩ ds`,

the tested form of Eq. (48). -/
theorem appendixC1_eq47_box (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (hp : ∀ x j, HasPDerivAt p j x (dp x j))
    (hf : ∀ x l k j, HasPDerivAt (fun y => f l y k) j x (df x l k j))
    (hphi : ∀ x i, HasPDerivAt phi i x (gphi x i))
    (hddphi : ∀ x i j, HasPDerivAt (fun y => gphi y i) j x (ddphi x i j))
    (hgap_def : ∀ x i j, HasPDerivAt (fun y => diffusionMatrix f y i j * p y) j x (gap x i j))
    (hfp : ∀ x i, HasPDerivAt (fun y => f0 y i * p y) i x (dfp x i))
    (hgap_deriv : ∀ x i j, HasPDerivAt (fun y => gap y i j) i x (ddgap x i j))
    (hV : ∀ x, HasFDerivAt (fun y i => phi y * currentField f0 gap p y i) (V' x) x)
    (hW : ∀ l x, HasFDerivAt (noiseField f gphi p l) (W' l x) x)
    (hintV : IntegrableOn (fun x => ∑ i, (V' x (Pi.single i 1)) i) (Icc a b))
    (hintFp : IntegrableOn (fun x => phi x * formalAdjointVal (dfp x) (ddgap x)) (Icc a b))
    (hintW : ∀ l, IntegrableOn (fun x => ∑ j, (W' l x (Pi.single j 1)) j) (Icc a b))
    (hbc : ∀ (l : Fin r) (i : Fin (n + 1)) (y : Fin n → ℝ),
      p (i.insertNth (a i) y) * f l (i.insertNth (a i) y) i = 0 ∧
        p (i.insertNth (b i) y) * f l (i.insertNth (b i) y) i = 0) :
    ∫ x in Icc a b, generatorVal f0 f gphi ddphi x * p x
      = (∫ x in Icc a b, phi x * formalAdjointVal (dfp x) (ddgap x))
        + boxFlux a b (fun y i => phi y * currentField f0 gap p y i) := by
  rw [appendixC1_eq46_box a b hab hp hf hphi hddphi hgap_def hfp hgap_deriv hV hW
    hintV hintFp hintW,
    Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) =>
      boxFlux_noiseField_eq_zero a b l (hbc l))]
  simp

end

end GSHS
