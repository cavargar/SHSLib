/-
# Linear schemes driven by i.i.d. Gaussian increments: exact moment recursions (Gardiner §10.1–§10.4)

All one-variable schemes of Ch. 10, applied to the linear SDEs `dx = -γx dt + σ dW`
(Ornstein–Uhlenbeck) and `dx = λx dt + μx dW` (linear multiplicative noise), are recursions of
the form

  `y_{n+1} = G(ΔWₙ) yₙ + H(ΔWₙ)`,   `G(z) = g₀ + g₁z + g₂z²`,   `H(z) = h₀ + h₁z`

(`Gardiner.SDE.LinStep`, `Gardiner.SDE.linScheme`), driven by i.i.d. increments
`ΔWₙ ~ N(0, τ)` on an arbitrary probability space.  We prove, with no further assumption, that
`yₙ` is independent of `ΔWₙ` (property iv) after (10.1.21)), square integrable, and that its first
two moments obey the exact recursions

  `⟨y_{n+1}⟩ = ⟨G⟩⟨yₙ⟩ + ⟨H⟩`,   `⟨y²_{n+1}⟩ = ⟨G²⟩⟨yₙ²⟩ + 2⟨GH⟩⟨yₙ⟩ + ⟨H²⟩`

with the Gaussian expectations `⟨G⟩ = g₀ + g₂τ`, `⟨G²⟩ = g₀² + (g₁² + 2g₀g₂)τ + 3g₂²τ²`,
`⟨GH⟩ = g₀h₀ + (g₁h₁ + g₂h₀)τ`, `⟨H⟩ = h₀`, `⟨H²⟩ = h₀² + h₁²τ`
(`Gardiner.SDE.linScheme_mean`, `Gardiner.SDE.linScheme_sq`).
-/
import SHSLib.Gardiner.SDE.GaussianMoments

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

noncomputable section

namespace Gardiner.SDE

/-- A one-step map `y ↦ G(z) y + H(z)` with `G` quadratic and `H` affine in the increment `z`. -/
structure LinStep where
  g0 : ℝ
  g1 : ℝ
  g2 : ℝ
  h0 : ℝ
  h1 : ℝ

namespace LinStep

/-- The multiplicative part `G(z)`. -/
def G (s : LinStep) (z : ℝ) : ℝ := s.g0 + s.g1 * z + s.g2 * z ^ 2
/-- The additive part `H(z)`. -/
def H (s : LinStep) (z : ℝ) : ℝ := s.h0 + s.h1 * z
/-- The one-step map. -/
def apply (s : LinStep) (y z : ℝ) : ℝ := s.G z * y + s.H z

/-- `⟨G⟩` for `z ~ N(0, τ)`. -/
def EG (s : LinStep) (τ : ℝ) : ℝ := s.g0 + s.g2 * τ
/-- `⟨H⟩`. -/
def EH (s : LinStep) : ℝ := s.h0
/-- `⟨G²⟩`. -/
def EG2 (s : LinStep) (τ : ℝ) : ℝ := s.g0 ^ 2 + (s.g1 ^ 2 + 2 * s.g0 * s.g2) * τ + 3 * s.g2 ^ 2 * τ ^ 2
/-- `⟨GH⟩`. -/
def EGH (s : LinStep) (τ : ℝ) : ℝ := s.g0 * s.h0 + (s.g1 * s.h1 + s.g2 * s.h0) * τ
/-- `⟨H²⟩`. -/
def EH2 (s : LinStep) (τ : ℝ) : ℝ := s.h0 ^ 2 + s.h1 ^ 2 * τ

lemma continuous_G (s : LinStep) : Continuous s.G := by unfold G; fun_prop
lemma continuous_H (s : LinStep) : Continuous s.H := by unfold H; fun_prop

lemma integral_G (s : LinStep) (τ : ℝ≥0) : ∫ z, s.G z ∂(gaussianReal 0 τ) = s.EG τ := by
  have := gauss_poly4 τ s.g0 s.g1 s.g2 0 0
  simp only [zero_mul, add_zero, mul_zero] at this
  simp only [G, EG]; rw [this]

lemma integral_H (s : LinStep) (τ : ℝ≥0) : ∫ z, s.H z ∂(gaussianReal 0 τ) = s.EH := by
  have := gauss_poly4 τ s.h0 s.h1 0 0 0
  simp only [zero_mul, add_zero, mul_zero] at this
  simp only [H, EH]; rw [this]

lemma integral_G2 (s : LinStep) (τ : ℝ≥0) :
    ∫ z, s.G z ^ 2 ∂(gaussianReal 0 τ) = s.EG2 τ := by
  have := gauss_poly4 τ (s.g0 ^ 2) (2 * s.g0 * s.g1) (s.g1 ^ 2 + 2 * s.g0 * s.g2)
    (2 * s.g1 * s.g2) (s.g2 ^ 2)
  simp only [G, EG2]
  rw [show (fun z : ℝ => (s.g0 + s.g1 * z + s.g2 * z ^ 2) ^ 2) = fun z => s.g0 ^ 2 +
    2 * s.g0 * s.g1 * z + (s.g1 ^ 2 + 2 * s.g0 * s.g2) * z ^ 2 + 2 * s.g1 * s.g2 * z ^ 3 +
    s.g2 ^ 2 * z ^ 4 by funext z; ring, this]

lemma integral_GH (s : LinStep) (τ : ℝ≥0) :
    ∫ z, s.G z * s.H z ∂(gaussianReal 0 τ) = s.EGH τ := by
  have := gauss_poly4 τ (s.g0 * s.h0) (s.g0 * s.h1 + s.g1 * s.h0) (s.g1 * s.h1 + s.g2 * s.h0)
    (s.g2 * s.h1) 0
  simp only [G, H, EGH]
  rw [show (fun z : ℝ => (s.g0 + s.g1 * z + s.g2 * z ^ 2) * (s.h0 + s.h1 * z)) = fun z =>
    s.g0 * s.h0 + (s.g0 * s.h1 + s.g1 * s.h0) * z + (s.g1 * s.h1 + s.g2 * s.h0) * z ^ 2 +
    s.g2 * s.h1 * z ^ 3 + 0 * z ^ 4 by funext z; ring, this]
  ring

lemma integral_H2 (s : LinStep) (τ : ℝ≥0) : ∫ z, s.H z ^ 2 ∂(gaussianReal 0 τ) = s.EH2 τ := by
  have := gauss_poly4 τ (s.h0 ^ 2) (2 * s.h0 * s.h1) (s.h1 ^ 2) 0 0
  simp only [H, EH2]
  rw [show (fun z : ℝ => (s.h0 + s.h1 * z) ^ 2) = fun z => s.h0 ^ 2 + 2 * s.h0 * s.h1 * z +
    s.h1 ^ 2 * z ^ 2 + 0 * z ^ 3 + 0 * z ^ 4 by funext z; ring, this]
  ring

/-- Polynomials of degree `≤ 4` in a Gaussian increment are integrable. -/
lemma integrable_poly4 (τ : ℝ≥0) (c₀ c₁ c₂ c₃ c₄ : ℝ) :
    Integrable (fun z : ℝ => c₀ + c₁ * z + c₂ * z ^ 2 + c₃ * z ^ 3 + c₄ * z ^ 4)
      (gaussianReal 0 τ) := by
  have i1 : Integrable (fun x : ℝ => c₁ * x) (gaussianReal 0 τ) := by
    simpa using (gauss_integrable_pow τ 1).const_mul c₁
  exact ((((integrable_const _).add i1).add ((gauss_integrable_pow τ 2).const_mul c₂)).add
    ((gauss_integrable_pow τ 3).const_mul c₃)).add ((gauss_integrable_pow τ 4).const_mul c₄)

lemma integrable_G (s : LinStep) (τ : ℝ≥0) : Integrable s.G (gaussianReal 0 τ) := by
  have := integrable_poly4 τ s.g0 s.g1 s.g2 0 0
  refine this.congr (Filter.Eventually.of_forall fun z => ?_); simp [G]

lemma integrable_H (s : LinStep) (τ : ℝ≥0) : Integrable s.H (gaussianReal 0 τ) := by
  have := integrable_poly4 τ s.h0 s.h1 0 0 0
  refine this.congr (Filter.Eventually.of_forall fun z => ?_); simp [H]

lemma integrable_G2 (s : LinStep) (τ : ℝ≥0) :
    Integrable (fun z => s.G z ^ 2) (gaussianReal 0 τ) := by
  have := integrable_poly4 τ (s.g0 ^ 2) (2 * s.g0 * s.g1) (s.g1 ^ 2 + 2 * s.g0 * s.g2)
    (2 * s.g1 * s.g2) (s.g2 ^ 2)
  refine this.congr (Filter.Eventually.of_forall fun z => ?_); simp only [G]; ring

lemma integrable_GH (s : LinStep) (τ : ℝ≥0) :
    Integrable (fun z => s.G z * s.H z) (gaussianReal 0 τ) := by
  have := integrable_poly4 τ (s.g0 * s.h0) (s.g0 * s.h1 + s.g1 * s.h0)
    (s.g1 * s.h1 + s.g2 * s.h0) (s.g2 * s.h1) 0
  refine this.congr (Filter.Eventually.of_forall fun z => ?_); simp only [G, H]; ring

lemma integrable_H2 (s : LinStep) (τ : ℝ≥0) :
    Integrable (fun z => s.H z ^ 2) (gaussianReal 0 τ) := by
  have := integrable_poly4 τ (s.h0 ^ 2) (2 * s.h0 * s.h1) (s.h1 ^ 2) 0 0
  refine this.congr (Filter.Eventually.of_forall fun z => ?_); simp only [H]; ring

end LinStep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Transport of integrals of functions of a `N(0, τ)` random variable. -/
lemma integral_comp_gauss {Z : Ω → ℝ} {τ : ℝ≥0} (hZ : Measurable Z)
    (hlaw : P.map Z = gaussianReal 0 τ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ ω, f (Z ω) ∂P = ∫ z, f z ∂(gaussianReal 0 τ) := by
  rw [← hlaw, integral_map hZ.aemeasurable hf.aestronglyMeasurable]

omit [IsProbabilityMeasure P] in
lemma integrable_comp_gauss {Z : Ω → ℝ} {τ : ℝ≥0} (hZ : Measurable Z)
    (hlaw : P.map Z = gaussianReal 0 τ) {f : ℝ → ℝ} (hf : Continuous f)
    (hi : Integrable f (gaussianReal 0 τ)) : Integrable (fun ω => f (Z ω)) P := by
  rw [← hlaw] at hi
  exact (integrable_map_measure hf.aestronglyMeasurable hZ.aemeasurable).mp hi

/-- **One step of a linear scheme**: if `Y` is square integrable and independent of the increment
`Z ~ N(0, τ)`, then `G(Z)Y + H(Z)` is square integrable with the stated first two moments. -/
theorem linStep_moments (s : LinStep) {τ : ℝ≥0} {Y Z : Ω → ℝ} (hY : Measurable Y)
    (hY2 : MemLp Y 2 P) (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 τ)
    (hind : IndepFun Y Z P) :
    MemLp (fun ω => s.apply (Y ω) (Z ω)) 2 P ∧
    ∫ ω, s.apply (Y ω) (Z ω) ∂P = s.EG τ * ∫ ω, Y ω ∂P + s.EH ∧
    ∫ ω, s.apply (Y ω) (Z ω) ^ 2 ∂P =
      s.EG2 τ * ∫ ω, Y ω ^ 2 ∂P + 2 * s.EGH τ * ∫ ω, Y ω ∂P + s.EH2 τ := by
  have hY1 : Integrable Y P := hY2.integrable one_le_two
  have hYsq : Integrable (fun ω => Y ω ^ 2) P := hY2.integrable_sq
  have hGc := s.continuous_G
  have hHc := s.continuous_H
  -- integrability of the functions of `Z`
  have iG := integrable_comp_gauss hZ hlaw hGc (s.integrable_G τ)
  have iH := integrable_comp_gauss hZ hlaw hHc (s.integrable_H τ)
  have iG2 := integrable_comp_gauss hZ hlaw (hGc.pow 2) (s.integrable_G2 τ)
  have iGH := integrable_comp_gauss (f := fun z => s.G z * s.H z) hZ hlaw (hGc.mul hHc)
    (s.integrable_GH τ)
  have iH2 := integrable_comp_gauss hZ hlaw (hHc.pow 2) (s.integrable_H2 τ)
  -- independence of the relevant functions
  have ind1 : IndepFun Y (fun ω => s.G (Z ω)) P := hind.comp measurable_id hGc.measurable
  have ind2 : IndepFun (fun ω => Y ω ^ 2) (fun ω => s.G (Z ω) ^ 2) P :=
    hind.comp (measurable_id.pow_const 2) (hGc.measurable.pow_const 2)
  have ind3 : IndepFun Y (fun ω => s.G (Z ω) * s.H (Z ω)) P :=
    hind.comp measurable_id (hGc.measurable.mul hHc.measurable)
  -- the product terms
  have p1 : Integrable (fun ω => s.G (Z ω) * Y ω) P := by
    have := ind1.integrable_mul hY1 iG
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp [mul_comm])
  have p2 : Integrable (fun ω => s.G (Z ω) ^ 2 * Y ω ^ 2) P := by
    have := ind2.integrable_mul hYsq iG2
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp [mul_comm])
  have p3 : Integrable (fun ω => s.G (Z ω) * s.H (Z ω) * Y ω) P := by
    have := ind3.integrable_mul hY1 iGH
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp [mul_comm])
  have e1 : ∫ ω, s.G (Z ω) * Y ω ∂P = s.EG τ * ∫ ω, Y ω ∂P := by
    have := ind1.integral_fun_mul_eq_mul_integral hY.aestronglyMeasurable
      (hGc.measurable.comp hZ).aestronglyMeasurable
    rw [show (fun ω => s.G (Z ω) * Y ω) = fun ω => Y ω * s.G (Z ω) by funext; ring, this,
      integral_comp_gauss hZ hlaw hGc, s.integral_G]
    ring
  have e2 : ∫ ω, s.G (Z ω) ^ 2 * Y ω ^ 2 ∂P = s.EG2 τ * ∫ ω, Y ω ^ 2 ∂P := by
    have := ind2.integral_fun_mul_eq_mul_integral (hY.pow_const 2).aestronglyMeasurable
      ((hGc.measurable.comp hZ).pow_const 2).aestronglyMeasurable
    rw [show (fun ω => s.G (Z ω) ^ 2 * Y ω ^ 2) = fun ω => Y ω ^ 2 * s.G (Z ω) ^ 2 by
      funext; ring, this, integral_comp_gauss hZ hlaw (hGc.pow 2), s.integral_G2]
    ring
  have e3 : ∫ ω, s.G (Z ω) * s.H (Z ω) * Y ω ∂P = s.EGH τ * ∫ ω, Y ω ∂P := by
    have := ind3.integral_fun_mul_eq_mul_integral hY.aestronglyMeasurable
      ((hGc.measurable.comp hZ).mul (hHc.measurable.comp hZ)).aestronglyMeasurable
    rw [show (fun ω => s.G (Z ω) * s.H (Z ω) * Y ω) = fun ω => Y ω * (s.G (Z ω) * s.H (Z ω)) by
      funext; ring, this, integral_comp_gauss (f := fun z => s.G z * s.H z) hZ hlaw (hGc.mul hHc),
      s.integral_GH]
    ring
  have hsq : (fun ω => s.apply (Y ω) (Z ω) ^ 2) = fun ω =>
      s.G (Z ω) ^ 2 * Y ω ^ 2 + 2 * (s.G (Z ω) * s.H (Z ω) * Y ω) + s.H (Z ω) ^ 2 := by
    funext ω; simp only [LinStep.apply]; ring
  have hint_sq : Integrable (fun ω => s.apply (Y ω) (Z ω) ^ 2) P := by
    rw [hsq]; exact (p2.add (p3.const_mul 2)).add iH2
  have hmeas : Measurable fun ω => s.apply (Y ω) (Z ω) := by
    simp only [LinStep.apply]
    exact ((hGc.measurable.comp hZ).mul hY).add (hHc.measurable.comp hZ)
  refine ⟨(memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hint_sq, ?_, ?_⟩
  · simp only [LinStep.apply]
    rw [integral_add p1 iH, e1, integral_comp_gauss hZ hlaw hHc, s.integral_H]
  · have p23 : Integrable (fun ω => s.G (Z ω) ^ 2 * Y ω ^ 2 +
        2 * (s.G (Z ω) * s.H (Z ω) * Y ω)) P := p2.add (p3.const_mul 2)
    rw [hsq, integral_add p23 iH2, integral_add p2 (p3.const_mul 2),
      integral_const_mul, e2, e3, integral_comp_gauss hZ hlaw (hHc.pow 2), s.integral_H2]
    ring

/-- The linear scheme `y_{n+1} = G(ΔWₙ) yₙ + H(ΔWₙ)`, `y₀ = c`. -/
def linScheme (s : LinStep) (c : ℝ) (ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => c
  | n + 1 => fun ω => s.apply (linScheme s c ξ n ω) (ξ n ω)

/-- The σ-algebra generated by the first `n` increments. -/
def pastSigma (ξ : ℕ → Ω → ℝ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Iio n, MeasurableSpace.comap (ξ i) inferInstance

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
lemma linScheme_measurable_past (s : LinStep) (c : ℝ) (ξ : ℕ → Ω → ℝ) (n : ℕ) :
    Measurable[pastSigma ξ n] (linScheme s c ξ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hmono : pastSigma ξ n ≤ pastSigma ξ (n + 1) := by
      refine iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ Set.Iio (n + 1)) =>
        MeasurableSpace.comap (ξ i) inferInstance) i ?_
      simp at hi ⊢; omega
    have hξ : Measurable[pastSigma ξ (n + 1)] (ξ n) := by
      refine Measurable.mono (comap_measurable (ξ n)) ?_ le_rfl
      exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iio (n + 1)) =>
        MeasurableSpace.comap (ξ i) inferInstance) n (by simp)
    have hy : Measurable[pastSigma ξ (n + 1)] (linScheme s c ξ n) := ih.mono hmono le_rfl
    show Measurable[pastSigma ξ (n + 1)] fun ω => s.apply (linScheme s c ξ n ω) (ξ n ω)
    simp only [LinStep.apply]
    exact ((s.continuous_G.measurable.comp hξ).mul hy).add (s.continuous_H.measurable.comp hξ)

omit [IsProbabilityMeasure P] in
/-- Property iv) after (10.1.21): `yₙ` is independent of the increment `ΔWₙ`. -/
theorem linScheme_indep (s : LinStep) (c : ℝ) {ξ : ℕ → Ω → ℝ} (hξm : ∀ n, Measurable (ξ n))
    (hind : iIndepFun ξ P) (n : ℕ) : IndepFun (linScheme s c ξ n) (ξ n) P := by
  have hI : iIndep (fun i => MeasurableSpace.comap (ξ i) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).mp hind
  have hdisj : Disjoint (Set.Iio n) {n} := by simp
  have h := indep_iSup_of_disjoint (fun i => (hξm i).comap_le) hI hdisj
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h
    (linScheme_measurable_past s c ξ n).comap_le) ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ ({n} : Set ℕ)) =>
    MeasurableSpace.comap (ξ i) inferInstance) n (by simp)

lemma linScheme_measurable (s : LinStep) (c : ℝ) {ξ : ℕ → Ω → ℝ} (hξm : ∀ n, Measurable (ξ n))
    (n : ℕ) : Measurable (linScheme s c ξ n) :=
  (linScheme_measurable_past s c ξ n).mono (iSup₂_le fun i _ => (hξm i).comap_le) le_rfl

/-- **Exact moment recursions** for a linear scheme driven by i.i.d. `N(0, τ)` increments. -/
theorem linScheme_moments (s : LinStep) (c : ℝ) {τ : ℝ≥0} {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (n : ℕ) :
    MemLp (linScheme s c ξ n) 2 P ∧
    ∫ ω, linScheme s c ξ (n + 1) ω ∂P = s.EG τ * ∫ ω, linScheme s c ξ n ω ∂P + s.EH ∧
    ∫ ω, linScheme s c ξ (n + 1) ω ^ 2 ∂P = s.EG2 τ * ∫ ω, linScheme s c ξ n ω ^ 2 ∂P +
      2 * s.EGH τ * ∫ ω, linScheme s c ξ n ω ∂P + s.EH2 τ := by
  have hL2 : ∀ n, MemLp (linScheme s c ξ n) 2 P := by
    intro n
    induction n with
    | zero => exact memLp_const c
    | succ n ih =>
      exact (linStep_moments s (linScheme_measurable s c hξm n) ih (hξm n) (hlaw n)
        (linScheme_indep s c hξm hind n)).1
  obtain ⟨-, h2, h3⟩ := linStep_moments s (linScheme_measurable s c hξm n) (hL2 n) (hξm n)
    (hlaw n) (linScheme_indep s c hξm hind n)
  exact ⟨hL2 n, h2, h3⟩

/-- Closed form of the mean when `⟨H⟩ = 0`: `⟨yₙ⟩ = c ⟨G⟩ⁿ`. -/
theorem linScheme_mean (s : LinStep) (c : ℝ) {τ : ℝ≥0} {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hH : s.h0 = 0) (n : ℕ) :
    ∫ ω, linScheme s c ξ n ω ∂P = c * s.EG τ ^ n := by
  induction n with
  | zero => simp [linScheme]
  | succ n ih =>
    rw [(linScheme_moments s c hξm hind hlaw n).2.1, ih, LinStep.EH, hH]; ring

/-- Closed form of the second moment for multiplicative schemes (`H ≡ 0`):
`⟨yₙ²⟩ = c² ⟨G²⟩ⁿ`. -/
theorem linScheme_sq (s : LinStep) (c : ℝ) {τ : ℝ≥0} {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hH0 : s.h0 = 0) (hH1 : s.h1 = 0) (n : ℕ) :
    ∫ ω, linScheme s c ξ n ω ^ 2 ∂P = c ^ 2 * s.EG2 τ ^ n := by
  induction n with
  | zero => simp [linScheme]
  | succ n ih =>
    rw [(linScheme_moments s c hξm hind hlaw n).2.2, ih]
    simp only [LinStep.EGH, LinStep.EH2, hH0, hH1]; ring

/-- Second moment for additive schemes with `g₁ = g₂ = h₀ = 0` (the Ornstein–Uhlenbeck case):
`⟨y²_{n+1}⟩ = g₀² ⟨yₙ²⟩ + h₁² τ`. -/
theorem linScheme_sq_additive (s : LinStep) (c : ℝ) {τ : ℝ≥0} {ξ : ℕ → Ω → ℝ}
    (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) (hg1 : s.g1 = 0) (hg2 : s.g2 = 0)
    (hh0 : s.h0 = 0) (n : ℕ) :
    ∫ ω, linScheme s c ξ (n + 1) ω ^ 2 ∂P =
      s.g0 ^ 2 * ∫ ω, linScheme s c ξ n ω ^ 2 ∂P + s.h1 ^ 2 * τ := by
  rw [(linScheme_moments s c hξm hind hlaw n).2.2]
  simp only [LinStep.EG2, LinStep.EGH, LinStep.EH2, hg1, hg2, hh0]; ring

end Gardiner.SDE
