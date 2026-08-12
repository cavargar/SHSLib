/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 2.1 and Appendix A of Bect (2010): the hybrid state space

The state space of a GSHS is the disjoint union `E = ⋃_{q ∈ Q} {q} × E_q`, where `Q` is
a finite or countable set of modes and `E_q ⊆ ℝ^{n_q}`; the modes with `n_q = 0` are the
*purely discrete* ones and form `E^d`.  Here the state space is modelled by the sigma
type `GSHS.HybridSpace nq = Σ q : Q, (Fin (n q) → ℝ)`, together with a family
`dom : ∀ q, Set (Fin (n q) → ℝ)` of mode domains.

* `GSHS.hybridVolume` — the *volume measure* `m` of **Eq. (1)**,

    `m(Γ) = Σ_{n_q ≠ 0} m_q(Γ ∩ E_q) + Σ_{x ∈ E^d} δ_x(Γ)`,

  defined uniformly as the sum over the modes of the Lebesgue measure of the mode,
  restricted to `E_q` and pushed into `E`.  The two cases of Eq. (1) are *not* two
  separate definitions: for a purely discrete mode `n_q = 0` the space `ℝ^0` is a
  singleton and its Lebesgue measure is the Dirac mass at that point, which is the
  content of `GSHS.hybridVolume_discrete_mode`.  `GSHS.hybridVolume_apply`,
  `GSHS.lintegral_hybridVolume` and `GSHS.integral_hybridVolume` express `m` and its
  integrals mode by mode, and `GSHS.sigmaFinite_hybridVolume` shows that `m` is
  σ-finite whenever `Q` is countable (so that `m` may be used as the reference measure
  of the densities of Section 5).

* `GSHS.vectorFieldApply` — the action `g φ` of a vector field on a differentiable
  function, **Eq. (37)**; `GSHS.vectorFieldApply_of_discrete` is the second line of
  Eq. (37) (`g φ = 0` on `E^d`), which here is a theorem rather than a convention, and
  `GSHS.vectorFieldApply_eq_fderiv` identifies the coordinate expression with the
  derivative `dφ_q(z)·g(q,z)`.

* `GSHS.theorem21_divergence_hybrid` and `GSHS.theorem21_divergence_hybrid_flux` —
  **Theorem 21, Eq. (38)**: `∫_E div(f) dm = ∫_{∂E} ⟨f, n⟩ ds`.  The hybrid divergence
  theorem is exactly the sum over the modes of the divergence theorem in each mode
  (Assumption 10), the purely discrete modes contributing `0` to both sides.
  `GSHS.theorem21_divergence_hybrid_box` instantiates this with the divergence theorem
  on a box, `GSHS.theorem21_divergence_box`, giving an unconditional hybrid divergence
  theorem for a state space all of whose modes are boxes.
-/
import SHSLib.FPK.DivergenceTheorem
import SHSLib.FPK.BoundaryGeometry

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

variable {Q : Type*} (nq : Q → ℕ)

/-! ### Section 2.1: the hybrid state space and its volume measure -/

/-- The hybrid state space `E = ⋃_{q ∈ Q} {q} × E_q` of Section 2.1, as a type: a state
is a pair `(q, z)` consisting of a mode `q` and a continuous part `z ∈ ℝ^{n_q}`.  The
mode domains `E_q` enter through the volume measure `GSHS.hybridVolume`. -/
abbrev HybridSpace : Type _ := Σ q : Q, (Fin (nq q) → ℝ)

variable {nq}

/-- The injection of a mode into the hybrid state space is measurable. -/
theorem measurable_mk (q : Q) :
    Measurable (fun z : (Fin (nq q) → ℝ) => (⟨q, z⟩ : HybridSpace nq)) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  exact hs q

/-- The purely discrete part `E^d = ⋃_{n_q = 0} {q} × E_q` of the hybrid state space. -/
def discretePart (nq : Q → ℕ) : Set (HybridSpace nq) := {x | nq x.1 = 0}

variable (nq)

/-- **Eq. (1)**: the volume measure `m` of the hybrid state space, the sum over the modes
of the `n_q`-dimensional Lebesgue measure of `E_q`, viewed as a measure on `E`.  Modes
with `n_q = 0` contribute a Dirac mass (see `GSHS.hybridVolume_discrete_mode`), so this
single formula covers both terms of Eq. (1). -/
def hybridVolume (dom : ∀ q, Set (Fin (nq q) → ℝ)) : Measure (HybridSpace nq) :=
  Measure.sum fun q => (volume.restrict (dom q)).map (fun z => (⟨q, z⟩ : HybridSpace nq))

variable {nq}

/-- The value of the volume measure on a measurable set: the total volume of its mode
sections. -/
theorem hybridVolume_apply (dom : ∀ q, Set (Fin (nq q) → ℝ)) {A : Set (HybridSpace nq)}
    (hA : MeasurableSet A) :
    hybridVolume nq dom A
      = ∑' q, volume ((fun z => (⟨q, z⟩ : HybridSpace nq)) ⁻¹' A ∩ dom q) := by
  rw [hybridVolume, Measure.sum_apply _ hA]
  refine tsum_congr fun q => ?_
  rw [Measure.map_apply (measurable_mk q) hA, Measure.restrict_apply]
  exact (measurable_mk q) hA

/-- The second term of **Eq. (1)**: a purely discrete mode (`n_q = 0`) contributes the
Dirac mass at its unique point.  Indeed `ℝ^0` is a singleton whose Lebesgue measure is
the Dirac mass. -/
theorem hybridVolume_discrete_mode {dom : ∀ q, Set (Fin (nq q) → ℝ)} {q : Q}
    (hq : nq q = 0) (hdom : dom q = Set.univ) (z₀ : Fin (nq q) → ℝ) :
    (volume.restrict (dom q)).map (fun z => (⟨q, z⟩ : HybridSpace nq))
      = Measure.dirac (⟨q, z₀⟩ : HybridSpace nq) := by
  haveI : IsEmpty (Fin (nq q)) := by rw [hq]; infer_instance
  have hvol : (volume : Measure (Fin (nq q) → ℝ)) = Measure.dirac z₀ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => (volume : Measure ℝ)) z₀]
  rw [hdom, Measure.restrict_univ, hvol, Measure.map_dirac (measurable_mk q)]

/-- Integration in `ℝ≥0∞` against the volume measure, mode by mode. -/
theorem lintegral_hybridVolume (dom : ∀ q, Set (Fin (nq q) → ℝ))
    {f : HybridSpace nq → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(hybridVolume nq dom) = ∑' q, ∫⁻ z in dom q, f ⟨q, z⟩ := by
  rw [hybridVolume, lintegral_sum_measure]
  exact tsum_congr fun q => lintegral_map hf (measurable_mk q)

/-- Bochner integration against the volume measure, mode by mode. -/
theorem integral_hybridVolume (dom : ∀ q, Set (Fin (nq q) → ℝ)) {f : HybridSpace nq → ℝ}
    (hf : Integrable f (hybridVolume nq dom)) :
    ∫ x, f x ∂(hybridVolume nq dom) = ∑' q, ∫ z in dom q, f ⟨q, z⟩ := by
  rw [hybridVolume] at hf ⊢
  rw [integral_sum_measure hf]
  refine tsum_congr fun q => ?_
  have hmeas : AEStronglyMeasurable f
      ((volume.restrict (dom q)).map (fun z => (⟨q, z⟩ : HybridSpace nq))) :=
    (hf.mono_measure (Measure.le_sum _ q)).1
  exact integral_map (measurable_mk q).aemeasurable hmeas

/-- The volume measure of a hybrid state space with countably many modes is σ-finite; it
can therefore be used as the reference measure for the densities of Section 5. -/
theorem sigmaFinite_hybridVolume [Countable Q] (dom : ∀ q, Set (Fin (nq q) → ℝ)) :
    SigmaFinite (hybridVolume nq dom) := by
  refine Measure.sigmaFinite_of_countable (S := Set.range fun p : Q × ℕ =>
    (fun z => (⟨p.1, z⟩ : HybridSpace nq)) ''
      (spanningSets (volume.restrict (dom p.1)) p.2)) (Set.countable_range _) ?_ ?_
  · rintro s ⟨⟨q, k⟩, rfl⟩
    have hmeas : MeasurableSet
        ((fun z => (⟨q, z⟩ : HybridSpace nq)) '' (spanningSets (volume.restrict (dom q)) k)) := by
      rw [MeasurableSpace.measurableSet_iInf]
      intro q'
      show MeasurableSet ((fun z => (⟨q', z⟩ : HybridSpace nq)) ⁻¹' _)
      by_cases h : q' = q
      · subst h
        have : (fun z => (⟨q', z⟩ : HybridSpace nq)) ⁻¹'
            ((fun z => (⟨q', z⟩ : HybridSpace nq)) '' (spanningSets (volume.restrict (dom q')) k))
            = spanningSets (volume.restrict (dom q')) k := by
          ext z
          simp
        rw [this]
        exact measurableSet_spanningSets _ k
      · have : (fun z => (⟨q', z⟩ : HybridSpace nq)) ⁻¹'
            ((fun z => (⟨q, z⟩ : HybridSpace nq)) '' (spanningSets (volume.restrict (dom q)) k))
            = ∅ := by
          ext z
          simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
          rintro ⟨w, -, hw⟩
          exact h (congrArg Sigma.fst hw).symm
        rw [this]
        exact MeasurableSet.empty
    rw [hybridVolume_apply _ hmeas]
    have hzero : ∀ q' : Q, q' ≠ q →
        volume ((fun z => (⟨q', z⟩ : HybridSpace nq)) ⁻¹'
          ((fun z => (⟨q, z⟩ : HybridSpace nq)) '' (spanningSets (volume.restrict (dom q)) k))
          ∩ dom q') = 0 := by
      intro q' hq'
      have : (fun z => (⟨q', z⟩ : HybridSpace nq)) ⁻¹'
          ((fun z => (⟨q, z⟩ : HybridSpace nq)) '' (spanningSets (volume.restrict (dom q)) k))
          = ∅ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨w, -, hw⟩
        exact hq' (congrArg Sigma.fst hw).symm
      rw [this, Set.empty_inter, measure_empty]
    rw [tsum_eq_single q hzero]
    have hpre : (fun z => (⟨q, z⟩ : HybridSpace nq)) ⁻¹'
        ((fun z => (⟨q, z⟩ : HybridSpace nq)) '' (spanningSets (volume.restrict (dom q)) k))
        = spanningSets (volume.restrict (dom q)) k := by
      ext z; simp
    rw [hpre]
    have := measure_spanningSets_lt_top (volume.restrict (dom q)) k
    rwa [Measure.restrict_apply (measurableSet_spanningSets _ k)] at this
  · apply Set.eq_univ_of_forall
    rintro ⟨q, z⟩
    have hz : z ∈ ⋃ k, spanningSets (volume.restrict (dom q)) k := by
      rw [iUnion_spanningSets]; trivial
    obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hz
    exact ⟨_, ⟨(q, k), rfl⟩, ⟨z, hzk, rfl⟩⟩

/-! ### Appendix A: vector fields on the hybrid state space -/

variable (nq)

/-- **Eq. (37)**: the action `(g φ)(q, z) = Σ_i gⁱ(q,z) ∂φ/∂zⁱ(q,z)` of a vector field
`g` on a differentiable function `φ`, the partial derivatives of `φ` being given by the
family `dphi`.  On the purely discrete part `E^d` the sum is empty, so `g φ = 0` there,
which is exactly the second line of Eq. (37). -/
def vectorFieldApply (g : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ)
    (dphi : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ) (x : HybridSpace nq) : ℝ :=
  ∑ i, g x.1 x.2 i * dphi x.1 x.2 i

variable {nq}

/-- The second line of **Eq. (37)**: a vector field acts as `0` on the purely discrete
part of the state space. -/
theorem vectorFieldApply_of_discrete {g dphi : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ}
    {x : HybridSpace nq} (hx : x ∈ discretePart nq) :
    vectorFieldApply nq g dphi x = 0 := by
  haveI : IsEmpty (Fin (nq x.1)) := by rw [show nq x.1 = 0 from hx]; infer_instance
  simp [vectorFieldApply]

/-- The coordinate expression of **Eq. (37)** agrees with the intrinsic one: if `φ` is
differentiable in the continuous variable of mode `q`, with derivative `P`, then
`(g φ)(q, z) = P(g(q,z))`. -/
theorem vectorFieldApply_eq_fderiv {g : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ}
    {dphi : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ} {phi : HybridSpace nq → ℝ}
    {q : Q} {z : Fin (nq q) → ℝ} {P : (Fin (nq q) → ℝ) →L[ℝ] ℝ}
    (hphi : HasFDerivAt (fun w => phi (⟨q, w⟩ : HybridSpace nq)) P z)
    (hd : ∀ i, dphi q z i = P (Pi.single i 1)) :
    vectorFieldApply nq g dphi ⟨q, z⟩
      = fderiv ℝ (fun w => phi (⟨q, w⟩ : HybridSpace nq)) z (g q z) := by
  classical
  rw [hphi.fderiv]
  have hsum : g q z
      = ∑ i, g q z i • (Pi.single i (1 : ℝ) : Fin (nq q) → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc vectorFieldApply nq g dphi ⟨q, z⟩
      = ∑ i, g q z i * P (Pi.single i 1) := by
        simp [vectorFieldApply, hd]
    _ = P (∑ i, g q z i • (Pi.single i (1 : ℝ) : Fin (nq q) → ℝ)) := by
        rw [map_sum]
        simp [smul_eq_mul]
    _ = P (g q z) := by rw [← hsum]

/-- The divergence `div(f) = Σ_i ∂fⁱ/∂zⁱ` of a vector field on the hybrid state space,
computed from the family `pd` of diagonal partial derivatives `pd q z i = ∂fⁱ/∂zⁱ(q,z)`.
It vanishes on the purely discrete part. -/
def hybridDivergence (pd : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ) (x : HybridSpace nq) : ℝ :=
  ∑ i, pd x.1 x.2 i

theorem hybridDivergence_of_discrete {pd : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ}
    {x : HybridSpace nq} (hx : x ∈ discretePart nq) :
    hybridDivergence pd x = 0 := by
  haveI : IsEmpty (Fin (nq x.1)) := by rw [show nq x.1 = 0 from hx]; infer_instance
  simp [hybridDivergence]

/-! ### Theorem 21: the divergence theorem on a hybrid state space -/

/-- **Theorem 21, Eq. (38)** (mode-by-mode form).  If the divergence theorem holds in
each mode, with boundary flux `flux q`, then the integral of the divergence over the
whole hybrid state space is the total flux `Σ_q flux q`.  Purely discrete modes
contribute `0` to both sides. -/
theorem theorem21_divergence_hybrid (dom : ∀ q, Set (Fin (nq q) → ℝ))
    (pd : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ) (flux : Q → ℝ)
    (hint : Integrable (hybridDivergence pd) (hybridVolume nq dom))
    (hmode : ∀ q, ∫ z in dom q, ∑ i, pd q z i = flux q) :
    ∫ x, hybridDivergence pd x ∂(hybridVolume nq dom) = ∑' q, flux q := by
  rw [integral_hybridVolume dom hint]
  exact tsum_congr fun q => hmode q

/-- **Theorem 21, Eq. (38)**: `∫_E div(f) dm = ∫_{∂E} ⟨f, n⟩ ds`.  The surface measure
`s` of the boundary `∂E` is the sum, over the modes, of the surface measures `s_q` of
the individual boundaries `∂E_q` (Eq. (18)), and `fn = ⟨f, n⟩` is the outward normal
component of the field on `∂E`; the hypothesis `hmode` is the divergence theorem in each
mode, which holds under Assumption 10. -/
theorem theorem21_divergence_hybrid_flux (dom : ∀ q, Set (Fin (nq q) → ℝ))
    (pd : ∀ q, (Fin (nq q) → ℝ) → Fin (nq q) → ℝ)
    (sm : Q → Measure (HybridSpace nq)) (fn : HybridSpace nq → ℝ)
    (hint : Integrable (hybridDivergence pd) (hybridVolume nq dom))
    (hintS : Integrable fn (hybridSurfaceMeasure sm))
    (hmode : ∀ q, ∫ z in dom q, ∑ i, pd q z i = ∫ x, fn x ∂(sm q)) :
    ∫ x, hybridDivergence pd x ∂(hybridVolume nq dom)
      = ∫ x, fn x ∂(hybridSurfaceMeasure sm) := by
  rw [theorem21_divergence_hybrid dom pd _ hint hmode, hybridSurfaceMeasure]
  rw [hybridSurfaceMeasure] at hintS
  exact (integral_sum_measure hintS).symm

/-- **Theorem 21 for a hybrid state space whose modes are boxes.**  Each mode domain is
a box `[a_q, b_q] ⊂ ℝ^{k_q+1}`, a `C²`-manifold with corners (Assumption 10), and the
divergence theorem in each mode is `GSHS.theorem21_divergence_box`; the conclusion is
Eq. (38), the total boundary flux being the sum of the face fluxes of the boxes. -/
theorem theorem21_divergence_hybrid_box {kq : Q → ℕ}
    (a b : ∀ q, Fin (kq q + 1) → ℝ) (hab : ∀ q, a q ≤ b q)
    (F : ∀ q, (Fin (kq q + 1) → ℝ) → Fin (kq q + 1) → ℝ)
    (F' : ∀ q, (Fin (kq q + 1) → ℝ) → (Fin (kq q + 1) → ℝ) →L[ℝ] (Fin (kq q + 1) → ℝ))
    (pd : ∀ q, (Fin (kq q + 1) → ℝ) → Fin (kq q + 1) → ℝ)
    (hcont : ∀ q, ContinuousOn (F q) (Icc (a q) (b q)))
    (hderiv : ∀ q, ∀ x ∈ Set.univ.pi fun i => Ioo (a q i) (b q i), HasFDerivAt (F q) (F' q x) x)
    (hpd : ∀ q x i, pd q x i = (F' q x) (Pi.single i 1) i)
    (hintOn : ∀ q, IntegrableOn (fun z => ∑ i, pd q z i) (Icc (a q) (b q)))
    (hint : Integrable (hybridDivergence pd)
      (hybridVolume (fun q => kq q + 1) (fun q => Icc (a q) (b q)))) :
    ∫ x, hybridDivergence pd x ∂(hybridVolume (fun q => kq q + 1) (fun q => Icc (a q) (b q)))
      = ∑' q, boxFlux (a q) (b q) (F q) := by
  refine theorem21_divergence_hybrid _ pd _ hint fun q => ?_
  exact theorem21_divergence_box (a q) (b q) (hab q) (F q) (F' q) (hcont q) (hderiv q)
    (divF := fun z => ∑ i, pd q z i) (fun x => by simp [hpd q x]) (hintOn q)

end GSHS
