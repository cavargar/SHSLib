/-
# Localising the Itô integral in time

For an Itô integrand `G` on `[0, T]` and `0 ≤ s ≤ t ≤ T`:

* `Gardiner.Ito.itoInt_cellInd`: `∫₀ᵀ 1_{(s,t]} G dW = ∫₀ᵗ G dW - ∫₀ˢ G dW` a.s.;
* `Gardiner.Ito.itoInt_mul_after`: if `G = 0` on `[0, s]` and `Z` is bounded and
  `𝓕 s`-measurable, then `∫₀ᵀ Z G dW = Z ∫₀ᵀ G dW` a.s.;
* `Gardiner.Ito.itoInt_mul_cellInd`: `∫₀ᵀ Z 1_{(s,t]} G dW = Z (∫₀ᵗ G dW - ∫₀ˢ G dW)` a.s.;
* `Gardiner.Ito.setIntegral_itoInt_incr_sq`: the conditional Itô isometry
  `E[1_A (∫ₛᵗ G dW)²] = E[1_A ∫ₛᵗ G² du]` for `A ∈ 𝓕 s`.

These are the ingredients for Itô's formula along a general Itô process
(`Gardiner.Ito.ItoGeneral`).
-/
import SHSLib.Gardiner.Ito.Calculus.MulLeft

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {ι : Type*} [Fintype ι]

/-- The indicator of `(s, ∞)` as a real function. -/
def afterInd (s : ℝ) (u : ℝ) : ℝ := (Set.Ioi s).indicator (fun _ => (1 : ℝ)) u

lemma afterInd_of_lt {s u : ℝ} (h : s < u) : afterInd s u = 1 := by
  simp [afterInd, Set.indicator_of_mem (show u ∈ Set.Ioi s from h)]

lemma afterInd_of_le {s u : ℝ} (h : u ≤ s) : afterInd s u = 0 := by
  simp [afterInd, Set.indicator_of_notMem (show u ∉ Set.Ioi s from not_lt.mpr h)]

lemma cellInd_max_max (a b s u : ℝ) :
    cellInd (max a s) (max b s) u = cellInd a b u * afterInd s u := by
  by_cases hsu : s < u
  · rw [afterInd_of_lt hsu, mul_one]
    by_cases h : u ∈ Set.Ioc a b
    · rw [cellInd_mem h, cellInd_mem ⟨max_lt h.1 hsu, h.2.trans (le_max_left _ _)⟩]
    · rw [cellInd_notMem h, cellInd_notMem]
      rintro ⟨h1, h2⟩
      exact h ⟨(le_max_left a s).trans_lt h1, by
        rcases le_total b s with hb | hb
        · rw [max_eq_right hb] at h2; linarith
        · rwa [max_eq_left hb] at h2⟩
  · push_neg at hsu
    rw [afterInd_of_le hsu, mul_zero, cellInd_notMem]
    rintro ⟨h1, -⟩
    exact absurd ((le_max_right a s).trans_lt h1) (not_lt.mpr hsu)

namespace ElemIntegrand

/-- The elementary integrand restricted to `(s, ∞)` and multiplied by a bounded `𝓕 s`-measurable
random variable `Z`. -/
def mulAfter (H : ElemIntegrand 𝓕 P ι) (s : ℝ) (Z : Ω → ℝ) (hZ : StronglyMeasurable[𝓕 s] Z)
    {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) : ElemIntegrand 𝓕 P ι where
  left i := max (H.left i) s
  right i := max (H.right i) s
  val i ω := Z ω * H.val i ω
  left_nonneg i := (H.left_nonneg i).trans (le_max_left _ _)
  left_le_right i := max_le_max_right s (H.left_le_right i)
  adapted i := (hZ.mono (𝓕.mono (le_max_right _ _))).mul
    ((H.adapted i).mono (𝓕.mono (le_max_left _ _)))
  memLp i := memLp_mul_of_bdd (hZ.mono (𝓕.le s)).aestronglyMeasurable hZb (H.memLp i)

lemma process_mulAfter (H : ElemIntegrand 𝓕 P ι) (s : ℝ) (Z : Ω → ℝ)
    (hZ : StronglyMeasurable[𝓕 s] Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) (u : ℝ) (ω : Ω) :
    (H.mulAfter s Z hZ hZb).process u ω = Z ω * (afterInd s u * H.process u ω) := by
  simp only [process, mulAfter, cellInd_max_max, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma integral_mulAfter (W : ℝ → Ω → ℝ) (H : ElemIntegrand 𝓕 P ι) (s : ℝ) (Z : Ω → ℝ)
    (hZ : StronglyMeasurable[𝓕 s] Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C)
    (hZ1 : StronglyMeasurable[𝓕 s] (fun _ : Ω => (1 : ℝ))) (hb1 : ∀ _ : Ω, |(1 : ℝ)| ≤ 1) :
    (H.mulAfter s Z hZ hZb).integral W =
      fun ω => Z ω * (H.mulAfter s (fun _ => 1) hZ1 hb1).integral W ω := by
  funext ω
  simp only [integral, mulAfter, Finset.mul_sum, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma mulAfter_supportedIn (H : ElemIntegrand 𝓕 P ι) {s T : ℝ} (hsT : s ≤ T) (Z : Ω → ℝ)
    (hZ : StronglyMeasurable[𝓕 s] Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) (hH : H.SupportedIn T) :
    (H.mulAfter s Z hZ hZb).SupportedIn T := fun i => max_le (hH i) hsT

end ElemIntegrand

lemma abs_afterInd_le (s u : ℝ) : |afterInd s u| ≤ 1 := by
  by_cases h : s < u
  · simp [afterInd_of_lt h]
  · simp [afterInd_of_le (not_lt.mp h)]

lemma measurable_afterInd (s : ℝ) : Measurable (afterInd s) :=
  measurable_const.indicator measurableSet_Ioi

lemma isItoIntegrand_det_mul {T : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G)
    {f : ℝ → ℝ} (hf : Measurable f) (hfb : ∀ u, |f u| ≤ 1) :
    IsItoIntegrand 𝓕 P T (fun u ω => f u * G u ω) := by
  refine ⟨(hf.comp measurable_fst).mul hG.measurable, fun t ht htT =>
    stronglyMeasurable_const.mul (hG.adapted t ht htT), ?_⟩
  exact memLp_mul_of_bdd (Z := fun p : ℝ × Ω => f p.1) (hf.comp measurable_fst).aestronglyMeasurable
    (fun p => hfb p.1) hG.memLp

lemma abs_cellInd_le (a b u : ℝ) : |cellInd a b u| ≤ 1 := by
  rw [abs_of_nonneg (cellInd_nonneg a b u)]; exact cellInd_le_one a b u

/-- Restricting the time–space measure: integrals of functions vanishing after time `t` over
`(0, T]` and over `(0, t]` agree. -/
lemma integral_tsMeasure_of_vanish [SFinite P] {t T : ℝ} (htT : t ≤ T) {f : ℝ × Ω → ℝ}
    (hf : ∀ p : ℝ × Ω, t < p.1 → f p = 0) :
    ∫ p, f p ∂(tsMeasure P T) = ∫ p, f p ∂(tsMeasure P t) := by
  have hset : MeasurableSet (Set.Iic t ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_Iic.prod MeasurableSet.univ
  have hres : (tsMeasure P T).restrict (Set.Iic t ×ˢ Set.univ) = tsMeasure P t := by
    unfold tsMeasure
    rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Iic]
    congr 2
    ext u; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h1.trans htT⟩
  rw [← hres, ← integral_indicator hset]
  congr 1
  funext p
  by_cases hp : p.1 ≤ t
  · rw [Set.indicator_of_mem (Set.mk_mem_prod (Set.mem_Iic.mpr hp) (Set.mem_univ _))]
  · rw [Set.indicator_of_notMem (fun h => hp (Set.mem_Iic.mp (Set.mem_prod.mp h).1)),
      hf p (not_le.mp hp)]

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **Truncation in time**: `∫₀ᵀ 1_{(0,t]} G dW = ∫₀ᵗ G dW` a.s. for `0 ≤ t ≤ T`. -/
theorem itoInt_cellInd_zero {T t : ℝ} (htT : t ≤ T) {G : ℝ → Ω → ℝ}
    (hG : IsItoIntegrand 𝓕 P T G) :
    itoInt W 𝓕 P T (fun u ω => cellInd 0 t u * G u ω) =ᵐ[P] itoInt W 𝓕 P t G := by
  have := hW.isProbabilityMeasure
  have hGt := hG.mono htT
  have hcG := isItoIntegrand_det_mul hG (measurable_cellInd 0 t) (abs_cellInd_le 0 t)
  set H := fun k => (approxSeq 𝓕 P t G k).2 with hH
  have hHs : ∀ k, (H k).SupportedIn t := fun k => (approxSeq_spec hGt k).1
  have hHsT : ∀ k, (H k).SupportedIn T := fun k i => (hHs k i).trans htT
  have hconv : Tendsto (fun k => ∫ p, (Function.uncurry (H k).process p -
      Function.uncurry (fun u ω => cellInd 0 t u * G u ω) p) ^ 2 ∂(tsMeasure P T)) atTop
      (𝓝 0) := by
    refine (approxSeq_tendsto_ts hW hGt).congr' (Eventually.of_forall fun k => ?_)
    dsimp only
    rw [integral_tsMeasure_of_vanish htT (f := fun p => (Function.uncurry (H k).process p -
      Function.uncurry (fun u ω => cellInd 0 t u * G u ω) p) ^ 2)]
    · refine integral_congr_ae ?_
      filter_upwards [ae_mem_Ioc_tsMeasure (P := P) t] with p hp
      simp only [Function.uncurry, cellInd_mem hp, one_mul]
      rfl
    · intro p hp
      simp only [Function.uncurry]
      rw [(H k).process_eq_zero_of_ge (hHs k) hp, cellInd_notMem (fun h => absurd h.2
        (not_le.mpr hp))]
      simp
  have h1 := itoInt_tendsto hW hcG H hHsT hconv
  have h2 := approxSeq_tendsto hW hGt
  exact l2_ae_unique (fun k => (H k).memLp_integral hW) (memLp_itoInt hW hcG)
    (memLp_itoInt hW hGt) h1 h2

/-- `∫₀ᵀ 1_{(s,t]} G dW = ∫₀ᵗ G dW - ∫₀ˢ G dW` a.s. for `0 ≤ s ≤ t ≤ T`. -/
theorem itoInt_cellInd {T s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) {G : ℝ → Ω → ℝ}
    (hG : IsItoIntegrand 𝓕 P T G) :
    itoInt W 𝓕 P T (fun u ω => cellInd s t u * G u ω) =ᵐ[P]
      fun ω => itoInt W 𝓕 P t G ω - itoInt W 𝓕 P s G ω := by
  have ht := isItoIntegrand_det_mul hG (measurable_cellInd 0 t) (abs_cellInd_le 0 t)
  have hs' := isItoIntegrand_det_mul hG (measurable_cellInd 0 s) (abs_cellInd_le 0 s)
  have e : (fun u ω => cellInd s t u * G u ω) =
      fun u ω => cellInd 0 t u * G u ω - cellInd 0 s u * G u ω := by
    funext u ω
    rw [← sub_mul]
    congr 1
    by_cases h1 : u ∈ Set.Ioc s t
    · rw [cellInd_mem h1, cellInd_mem ⟨hs.trans_lt h1.1, h1.2⟩,
        cellInd_notMem (fun h => absurd h.2 (not_le.mpr h1.1))]
      ring
    · by_cases h2 : u ∈ Set.Ioc 0 s
      · rw [cellInd_notMem h1, cellInd_mem h2, cellInd_mem ⟨h2.1, h2.2.trans hst⟩]; ring
      · rw [cellInd_notMem h1, cellInd_notMem h2, cellInd_notMem]
        · ring
        rintro ⟨a, b⟩
        by_cases hus : u ≤ s
        · exact h2 ⟨a, hus⟩
        · exact h1 ⟨not_le.mp hus, b⟩
  rw [e]
  filter_upwards [itoInt_sub hW ht hs', itoInt_cellInd_zero hW htT hG,
    itoInt_cellInd_zero hW (hst.trans htT) hG] with ω h1 h2 h3
  rw [h1, h2, h3]

/-- **Bounded `𝓕 s`-measurable factors come out of integrals over `(s, T]`**: if `G = 0` on
`[0, s]` and `Z` is bounded and `𝓕 s`-measurable, then `∫₀ᵀ Z G dW = Z ∫₀ᵀ G dW` a.s. -/
theorem itoInt_mul_after {T s : ℝ} (hsT : s ≤ T) {G : ℝ → Ω → ℝ}
    (hG : IsItoIntegrand 𝓕 P T G) (hGs : ∀ u ω, u ≤ s → G u ω = 0)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 s] Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    itoInt W 𝓕 P T (fun u ω => Z ω * G u ω) =ᵐ[P] fun ω => Z ω * itoInt W 𝓕 P T G ω := by
  have := hW.isProbabilityMeasure
  have hZm : Measurable Z := (hZ.mono (𝓕.le s)).measurable
  have hZG : IsItoIntegrand 𝓕 P T (fun u ω => Z ω * G u ω) := by
    refine ⟨(hZm.comp measurable_snd).mul hG.measurable, fun t ht htT => ?_, ?_⟩
    · by_cases hts : t ≤ s
      · have : (fun ω => Z ω * G t ω) = fun _ => 0 := funext fun ω => by rw [hGs t ω hts, mul_zero]
        rw [this]; exact stronglyMeasurable_const
      · exact (hZ.mono (𝓕.mono (not_le.mp hts).le)).mul (hG.adapted t ht htT)
    · exact memLp_mul_of_bdd (Z := fun p : ℝ × Ω => Z p.2)
        (hZm.comp measurable_snd).aestronglyMeasurable (fun p => hZb p.2) hG.memLp
  have hZ1 : StronglyMeasurable[𝓕 s] (fun _ : Ω => (1 : ℝ)) := stronglyMeasurable_const
  have hb1 : ∀ _ : Ω, |(1 : ℝ)| ≤ 1 := fun _ => by simp
  set H := fun k => (approxSeq 𝓕 P T G k).2 with hH
  have hHs : ∀ k, (H k).SupportedIn T := fun k => (approxSeq_spec hG k).1
  set K := fun k => (H k).mulAfter s Z hZ hZb with hK
  set K1 := fun k => (H k).mulAfter s (fun _ => 1) hZ1 hb1 with hK1
  have hKs : ∀ k, (K k).SupportedIn T := fun k =>
    (H k).mulAfter_supportedIn hsT Z hZ hZb (hHs k)
  have hK1s : ∀ k, (K1 k).SupportedIn T := fun k =>
    (H k).mulAfter_supportedIn hsT _ hZ1 hb1 (hHs k)
  have hconvH := approxSeq_tendsto_ts hW hG
  have hGeq : ∀ u ω, G u ω = afterInd s u * G u ω := fun u ω => by
    by_cases h : s < u
    · rw [afterInd_of_lt h, one_mul]
    · rw [hGs u ω (not_lt.mp h), mul_zero]
  have hbound : ∀ (Z' : Ω → ℝ) (hZ' : StronglyMeasurable[𝓕 s] Z') (C' : ℝ)
      (hZb' : ∀ ω, |Z' ω| ≤ C'), Tendsto (fun k => ∫ p, (Function.uncurry
        ((H k).mulAfter s Z' hZ' hZb').process p -
        Function.uncurry (fun u ω => Z' ω * G u ω) p) ^ 2 ∂(tsMeasure P T)) atTop (𝓝 0) := by
    intro Z' hZ' C' hZb'
    refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun k => ?_)
      (by simpa using hconvH.const_mul (C' ^ 2))
    have hm : MemLp (fun p => Function.uncurry (H k).process p - Function.uncurry G p) 2
        (tsMeasure P T) := ((H k).memLp_process T).sub hG.memLp
    have e : (fun p => (Function.uncurry ((H k).mulAfter s Z' hZ' hZb').process p -
        Function.uncurry (fun u ω => Z' ω * G u ω) p) ^ 2) =
        fun p => ((Z' p.2 * afterInd s p.1) *
          (Function.uncurry (H k).process p - Function.uncurry G p)) ^ 2 := by
      funext p
      simp only [ElemIntegrand.process_mulAfter, Function.uncurry]
      by_cases h : s < p.1
      · rw [afterInd_of_lt h]; ring
      · rw [afterInd_of_le (not_lt.mp h), hGs p.1 p.2 (not_lt.mp h)]; ring
    rw [e]
    refine integral_mul_sq_le (Z := fun p : ℝ × Ω => Z' p.2 * afterInd s p.1) (fun p => ?_) hm
    rw [abs_mul]
    have h1 := hZb' p.2
    have h0 : 0 ≤ C' := (abs_nonneg _).trans h1
    calc |Z' p.2| * |afterInd s p.1| ≤ C' * 1 :=
          mul_le_mul h1 (abs_afterInd_le s p.1) (abs_nonneg _) h0
      _ = C' := mul_one _
  have hG1 : IsItoIntegrand 𝓕 P T (fun u ω => (fun _ => (1 : ℝ)) ω * G u ω) := by
    simpa using hG
  have h1 := itoInt_tendsto hW hZG K hKs (hbound Z hZ C hZb)
  have h2 := itoInt_tendsto hW hG1 K1 hK1s (hbound _ hZ1 1 hb1)
  simp only [one_mul] at h2
  have hX : ∀ k, MemLp ((K k).integral W) 2 P := fun k => (K k).memLp_integral hW
  refine l2_ae_unique hX (memLp_itoInt hW hZG)
    (memLp_mul_of_bdd hZm.aestronglyMeasurable hZb (memLp_itoInt hW hG)) h1 ?_
  refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun k => ?_)
    (by simpa using h2.const_mul (C ^ 2))
  have e : (fun ω => ((K k).integral W ω - Z ω * itoInt W 𝓕 P T G ω) ^ 2) =
      fun ω => (Z ω * ((K1 k).integral W ω - itoInt W 𝓕 P T G ω)) ^ 2 := by
    funext ω
    simp only [hK, hK1, ElemIntegrand.integral_mulAfter W (H k) s Z hZ hZb hZ1 hb1]
    ring
  rw [e]
  exact integral_mul_sq_le hZb (((K1 k).memLp_integral hW).sub (memLp_itoInt hW hG))

/-- **Localised factorisation**: for `0 ≤ s ≤ t ≤ T` and a bounded `𝓕 s`-measurable `Z`,
`∫₀ᵀ Z 1_{(s,t]} G dW = Z (∫₀ᵗ G dW - ∫₀ˢ G dW)` a.s. -/
theorem itoInt_mul_cellInd {T s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 s] Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    itoInt W 𝓕 P T (fun u ω => Z ω * (cellInd s t u * G u ω)) =ᵐ[P]
      fun ω => Z ω * (itoInt W 𝓕 P t G ω - itoInt W 𝓕 P s G ω) := by
  have hcG := isItoIntegrand_det_mul hG (measurable_cellInd s t) (abs_cellInd_le s t)
  have h1 := itoInt_mul_after hW (hst.trans htT) hcG (fun u ω hu => by
    rw [cellInd_notMem (fun h => absurd h.1 (not_lt.mpr hu)), zero_mul]) hZ hZb
  filter_upwards [h1, itoInt_cellInd hW hs hst htT hG] with ω h1 h2
  rw [h1, h2]

/-- **Conditional Itô isometry**: for `A ∈ 𝓕 s` and `0 ≤ s ≤ t ≤ T`,
`E[1_A (∫₀ᵗ G dW - ∫₀ˢ G dW)²] = E[1_A ∫ₛᵗ G(u)² du]`. -/
theorem setIntegral_itoInt_incr_sq {T s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, (itoInt W 𝓕 P t G ω - itoInt W 𝓕 P s G ω) ^ 2 ∂P =
      ∫ ω in A, (∫ u : ℝ in Set.Ioc s t, G u ω ^ 2) ∂P := by
  have := hW.isProbabilityMeasure
  set Z : Ω → ℝ := A.indicator (fun _ => 1) with hZdef
  have hZ : StronglyMeasurable[𝓕 s] Z := stronglyMeasurable_const.indicator hA
  have hZb : ∀ ω, |Z ω| ≤ 1 := fun ω => by
    by_cases h : ω ∈ A
    · simp [hZdef, Set.indicator_of_mem h]
    · simp [hZdef, Set.indicator_of_notMem h]
  have hAm : MeasurableSet A := 𝓕.le s A hA
  have hcG := isItoIntegrand_det_mul hG (measurable_cellInd s t) (abs_cellInd_le s t)
  have hZG : IsItoIntegrand 𝓕 P T (fun u ω => Z ω * (cellInd s t u * G u ω)) := by
    have hZm : Measurable Z := (hZ.mono (𝓕.le s)).measurable
    refine ⟨(hZm.comp measurable_snd).mul hcG.measurable, fun u hu huT => ?_, ?_⟩
    · by_cases hus : u ≤ s
      · have : (fun ω => Z ω * (cellInd s t u * G u ω)) = fun _ => 0 := funext fun ω => by
          rw [cellInd_notMem (fun h => absurd h.1 (not_lt.mpr hus))]; ring
        rw [this]; exact stronglyMeasurable_const
      · exact (hZ.mono (𝓕.mono (not_le.mp hus).le)).mul (hcG.adapted u hu huT)
    · exact memLp_mul_of_bdd (Z := fun p : ℝ × Ω => Z p.2)
        (hZm.comp measurable_snd).aestronglyMeasurable (fun p => hZb p.2) hcG.memLp
  have hloc := itoInt_mul_cellInd hW hs hst htT hG hZ hZb
  have hsq := itoInt_sq hW hZG
  -- left side
  have hL : ∫ ω in A, (itoInt W 𝓕 P t G ω - itoInt W 𝓕 P s G ω) ^ 2 ∂P =
      ∫ ω, itoInt W 𝓕 P T (fun u ω => Z ω * (cellInd s t u * G u ω)) ω ^ 2 ∂P := by
    rw [← integral_indicator hAm]
    refine integral_congr_ae ?_
    filter_upwards [hloc] with ω hω
    rw [hω]
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h, hZdef]
    · simp [Set.indicator_of_notMem h, hZdef]
  rw [hL, hsq]
  -- right side: Fubini
  have hint : Integrable (fun p : ℝ × Ω => (Z p.2 * (cellInd s t p.1 * G p.1 p.2)) ^ 2)
      (tsMeasure P T) := hZG.memLp.integrable_sq
  have e1 : ∫ u in Set.Ioc 0 T, ∫ ω, (Z ω * (cellInd s t u * G u ω)) ^ 2 ∂P =
      ∫ ω : Ω, (∫ u : ℝ in Set.Ioc 0 T, (Z ω * (cellInd s t u * G u ω)) ^ 2) ∂P := by
    unfold tsMeasure at hint
    exact integral_integral_swap (f := fun u ω => (Z ω * (cellInd s t u * G u ω)) ^ 2) hint
  rw [e1, ← integral_indicator hAm]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases h : ω ∈ A
  · simp only [Set.indicator_of_mem h, hZdef, one_mul]
    rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext u
    by_cases hu : u ∈ Set.Ioc s t
    · have hu' : u ∈ Set.Ioc 0 T := ⟨hs.trans_lt hu.1, hu.2.trans htT⟩
      simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hu', cellInd_mem hu, one_mul]
    · simp only [Set.indicator_of_notMem hu]
      by_cases hu' : u ∈ Set.Ioc 0 T
      · simp [Set.indicator_of_mem hu', cellInd_notMem hu]
      · simp [Set.indicator_of_notMem hu']
  · simp [Set.indicator_of_notMem h, hZdef]

end Gardiner.Ito
