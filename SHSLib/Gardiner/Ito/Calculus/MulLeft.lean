/-
# Pulling an initial random factor out of the Itô integral

If `Z` is bounded and measurable with respect to `𝓕 0` (for instance a random initial value
independent of the Wiener process), then `∫₀ᵀ Z G dW = Z ∫₀ᵀ G dW` almost surely
(`Gardiner.Ito.itoInt_mul_left`).  Gardiner uses this tacitly when solving linear equations with a
random initial condition `x(t₀)` independent of `W` (§4.4.2).
-/
import SHSLib.Gardiner.Ito.Calculus.Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {ι : Type*} [Fintype ι]

lemma memLp_mul_of_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} {Z f : α → ℝ} {C : ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hZb : ∀ a, |Z a| ≤ C) (hf : MemLp f 2 μ) :
    MemLp (fun a => Z a * f a) 2 μ :=
  hf.of_le_mul (c := C) (hZ.mul hf.aestronglyMeasurable) (Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hZb a) (abs_nonneg _))

/-- An elementary integrand multiplied by a bounded `𝓕 0`-measurable random variable. -/
def ElemIntegrand.mulLeft (Z : Ω → ℝ) (hZ : StronglyMeasurable[𝓕 0] Z) {C : ℝ}
    (hZb : ∀ ω, |Z ω| ≤ C) (H : ElemIntegrand 𝓕 P ι) : ElemIntegrand 𝓕 P ι where
  left := H.left
  right := H.right
  val i ω := Z ω * H.val i ω
  left_nonneg := H.left_nonneg
  left_le_right := H.left_le_right
  adapted i := (hZ.mono (𝓕.mono (H.left_nonneg i))).mul (H.adapted i)
  memLp i := memLp_mul_of_bdd (hZ.mono (𝓕.le 0)).aestronglyMeasurable hZb (H.memLp i)

lemma ElemIntegrand.process_mulLeft (Z : Ω → ℝ) (hZ : StronglyMeasurable[𝓕 0] Z) {C : ℝ}
    (hZb : ∀ ω, |Z ω| ≤ C) (H : ElemIntegrand 𝓕 P ι) :
    (H.mulLeft Z hZ hZb).process = fun s ω => Z ω * H.process s ω := by
  funext s ω; simp [ElemIntegrand.process, ElemIntegrand.mulLeft, Finset.mul_sum, mul_assoc]

lemma ElemIntegrand.integral_mulLeft (W : ℝ → Ω → ℝ) (Z : Ω → ℝ) (hZ : StronglyMeasurable[𝓕 0] Z)
    {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) (H : ElemIntegrand 𝓕 P ι) :
    (H.mulLeft Z hZ hZb).integral W = fun ω => Z ω * H.integral W ω := by
  funext ω; simp [ElemIntegrand.integral, ElemIntegrand.mulLeft, Finset.mul_sum, mul_assoc]

lemma integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {Z f : α → ℝ} {C : ℝ}
    (hZb : ∀ a, |Z a| ≤ C) (hf : MemLp f 2 μ) :
    ∫ a, (Z a * f a) ^ 2 ∂μ ≤ C ^ 2 * ∫ a, f a ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    (hf.integrable_sq.const_mul _) (Eventually.of_forall fun a => ?_)
  have h0 : 0 ≤ C := (abs_nonneg _).trans (hZb a)
  have : (Z a) ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZb a) 2
  calc (Z a * f a) ^ 2 = Z a ^ 2 * f a ^ 2 := by ring
    _ ≤ C ^ 2 * f a ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)

lemma isItoIntegrand_mul_left {T : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 0] Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    IsItoIntegrand 𝓕 P T (fun t ω => Z ω * G t ω) := by
  have hZm : Measurable Z := (hZ.mono (𝓕.le 0)).measurable
  refine ⟨(hZm.comp measurable_snd).mul hG.measurable, fun t ht htT =>
    (hZ.mono (𝓕.mono ht)).mul (hG.adapted t ht htT), ?_⟩
  exact memLp_mul_of_bdd (Z := fun p : ℝ × Ω => Z p.2) (hZm.comp measurable_snd).aestronglyMeasurable
    (fun p => hZb p.2) hG.memLp

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **Initial random factors can be taken out of the Itô integral**: for bounded `𝓕 0`-measurable
`Z`, `∫₀ᵀ Z G dW = Z ∫₀ᵀ G dW` almost surely. -/
theorem itoInt_mul_left {T : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 0] Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    itoInt W 𝓕 P T (fun t ω => Z ω * G t ω) =ᵐ[P] fun ω => Z ω * itoInt W 𝓕 P T G ω := by
  have := hW.isProbabilityMeasure
  have hZm : Measurable Z := (hZ.mono (𝓕.le 0)).measurable
  have hZG := isItoIntegrand_mul_left hG hZ hZb
  set H := fun k => (approxSeq 𝓕 P T G k).2 with hH
  have hHs : ∀ k, (H k).SupportedIn T := fun k => (approxSeq_spec hG k).1
  set K := fun k => (H k).mulLeft Z hZ hZb with hK
  have hKs : ∀ k, (K k).SupportedIn T := hHs
  have hconvH := approxSeq_tendsto_ts hW hG
  have hconvK : Tendsto (fun k => ∫ p, (Function.uncurry (K k).process p -
      Function.uncurry (fun t ω => Z ω * G t ω) p) ^ 2 ∂(tsMeasure P T)) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun k => ?_)
      (by simpa using hconvH.const_mul (C ^ 2))
    have hm : MemLp (fun p => Function.uncurry (H k).process p - Function.uncurry G p) 2
        (tsMeasure P T) := ((H k).memLp_process T).sub hG.memLp
    have e : (fun p => (Function.uncurry (K k).process p -
        Function.uncurry (fun t ω => Z ω * G t ω) p) ^ 2) =
        fun p => (Z p.2 * (Function.uncurry (H k).process p - Function.uncurry G p)) ^ 2 := by
      funext p
      simp only [hK, ElemIntegrand.process_mulLeft, Function.uncurry]
      ring
    rw [e]
    exact integral_mul_sq_le (Z := fun p : ℝ × Ω => Z p.2) (fun p => hZb p.2) hm
  have h1 := itoInt_tendsto hW hZG K hKs hconvK
  have h2 := itoInt_tendsto hW hG H hHs hconvH
  have hX : ∀ k, MemLp ((K k).integral W) 2 P := fun k => (K k).memLp_integral hW
  refine l2_ae_unique hX (memLp_itoInt hW hZG)
    (memLp_mul_of_bdd hZm.aestronglyMeasurable hZb (memLp_itoInt hW hG)) h1 ?_
  refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun k => ?_)
    (by simpa using h2.const_mul (C ^ 2))
  have e : (fun ω => ((K k).integral W ω - Z ω * itoInt W 𝓕 P T G ω) ^ 2) =
      fun ω => (Z ω * ((H k).integral W ω - itoInt W 𝓕 P T G ω)) ^ 2 := by
    funext ω
    simp only [hK, ElemIntegrand.integral_mulLeft]
    ring
  rw [e]
  exact integral_mul_sq_le hZb (((H k).memLp_integral hW).sub (memLp_itoInt hW hG))

end Gardiner.Ito
