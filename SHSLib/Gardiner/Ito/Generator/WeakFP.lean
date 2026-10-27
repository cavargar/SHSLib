/-
# The weak Fokker–Planck equation for the law of an Itô diffusion (Gardiner (4.3.18)–(4.3.19))

Let `μ_t = P ∘ x(t)⁻¹` be the law of `x(t)`.  For a test function `φ ∈ C²_c` (`IsC2c φ`) and
jointly continuous coefficients `a`, `b` (with `b` bounded along the process):

* `weakFP_integrated`: `∫ φ dμ_t - ∫ φ dμ_0 = ∫₀ᵗ (∫ L φ(·, s) dμ_s) ds` (the form of
  `GSHS.FPKData.WeakDynkin` with zero jump term);
* `weakFP_hasDerivWithinAt` / `weakFP_hasDerivAt`: `d/dt ∫ φ dμ_t = ∫ L φ(·, t) dμ_t`
  (Gardiner (4.3.18)/(4.3.19)), as a derivative within `[0, T]` and, in `(0, T)`, as a two-sided
  derivative;
* `IsSDESol.weakFP_integrated`, `IsSDESol.weakFP_hasDerivWithinAt`, `IsSDESol.weakFP_hasDerivAt`:
  the same for solutions of Lipschitz SDEs on `[0, T]`.
-/
import SHSLib.Gardiner.Ito.Generator.SDE

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.Generator

open Gardiner.Ito Gardiner.Ito.StochDE

/-- **Test functions of class `C²_c`**: twice continuously differentiable with compact support. -/
structure IsC2c (φ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 φ
  hasCompactSupport : HasCompactSupport φ

/-- `L φ (y, t)` is jointly continuous for jointly continuous coefficients. -/
lemma continuous_itoGen {a b : ℝ → ℝ → ℝ} (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous fun p : ℝ × ℝ => itoGen a b φ p.1 p.2 := by
  unfold itoGen
  have ha' : Continuous fun p : ℝ × ℝ => a p.2 p.1 := ha.comp continuous_swap
  have hb' : Continuous fun p : ℝ × ℝ => b p.2 p.1 := hb.comp continuous_swap
  exact (ha'.mul ((contDiff_one_deriv hφ).continuous.comp continuous_snd)).add
    (((hb'.pow 2).div_const 2).mul ((continuous_deriv2_of_contDiff hφ).comp continuous_snd))

/-- `L φ` vanishes outside the support of `φ`. -/
lemma itoGen_eq_zero_of_notMem {a b : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {y : ℝ} (hy : y ∉ tsupport φ)
    (t : ℝ) : itoGen a b φ t y = 0 := by
  have h1 : deriv φ y = 0 := Function.notMem_support.mp fun h => hy (support_deriv_subset h)
  have h2 : deriv (deriv φ) y = 0 := Function.notMem_support.mp fun h =>
    hy (closure_minimal support_deriv_subset (isClosed_tsupport φ) (support_deriv_subset h))
  simp [itoGen, h1, h2]

/-- For `φ ∈ C²_c` and continuous coefficients, `L φ` is bounded on `[0, T] × ℝ`. -/
lemma exists_bound_itoGen {a b : ℝ → ℝ → ℝ} (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) {φ : ℝ → ℝ} (hφ : IsC2c φ) (T : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ Icc (0 : ℝ) T, ∀ y, |itoGen a b φ u y| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hφ.hasCompactSupport.isCompact).exists_bound_of_continuousOn
    (continuous_itoGen ha hb hφ.contDiff).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun u hu y => ?_⟩
  by_cases hy : y ∈ tsupport φ
  · have := hC (u, y) ⟨hu, hy⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [itoGen_eq_zero_of_notMem hy, abs_zero]; exact le_max_right _ _

/-- The law `μ_t = P ∘ x(t)⁻¹` of `x(t)`. -/
abbrev lawAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : ℝ → Ω → ℝ) (t : ℝ) :
    Measure ℝ :=
  P.map (x t)

lemma integral_lawAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : ℝ → Ω → ℝ} {t : ℝ}
    (hx : Measurable (x t)) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ y, g y ∂(lawAt P x t) = ∫ ω, g (x t ω) ∂P :=
  integral_map hx.aemeasurable hg.aestronglyMeasurable

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ}

lemma measurable_apply_of_isItoProcess {T : ℝ} {x a' b' : ℝ → Ω → ℝ}
    (hx : IsItoProcess W 𝓕 P T x a' b') (t : ℝ) : Measurable (x t) :=
  hx.measurable.comp (measurable_const.prodMk measurable_id)

lemma lawAt_clampProc {x : ℝ → Ω → ℝ} {T s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    lawAt P (clampProc x T) s = lawAt P x s := by
  simp only [lawAt, clampProc_eq hs]

variable (hW : IsFWiener W 𝓕 P)
include hW

section Diffusion

variable {T B : ℝ} {a b : ℝ → ℝ → ℝ} {x : ℝ → Ω → ℝ} {φ : ℝ → ℝ}

omit hW in
/-- The mean generator `m(s) = ∫ L φ(·, s) dμ_s = E L φ(x(s), s)`. -/
lemma integral_lawAt_itoGen (hx : IsItoDiffusion W 𝓕 P T a b x)
    (ha : Continuous (Function.uncurry a)) (hb : Continuous (Function.uncurry b))
    (hφ : IsC2c φ) (s : ℝ) :
    ∫ y, itoGen a b φ s y ∂(lawAt P x s) = ∫ ω, itoGen a b φ s (x s ω) ∂P :=
  integral_lawAt (measurable_apply_of_isItoProcess hx s)
    ((continuous_itoGen ha hb hφ.contDiff).comp (continuous_const.prodMk continuous_id))

/-- **The weak Fokker–Planck equation, integrated form** (`GSHS.FPKData.WeakDynkin` without
jumps): `∫ φ dμ_t - ∫ φ dμ_0 = ∫₀ᵗ (∫ L φ(·, s) dμ_s) ds` for `φ ∈ C²_c`, `0 ≤ t ≤ T`. -/
theorem weakFP_integrated (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) (hφ : IsC2c φ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ y, φ y ∂(lawAt P x t) - ∫ y, φ y ∂(lawAt P x 0) =
      ∫ s in (0 : ℝ)..t, ∫ y, itoGen a b φ s y ∂(lawAt P x s) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C0, C1, C2, hC0, hf⟩ := exists_c2BddDeriv_of_hasCompactSupport hφ.contDiff
    hφ.hasCompactSupport
  obtain ⟨C, hC, hCb⟩ := exists_bound_itoGen ha hb hφ T
  have hxm := measurable_apply_of_isItoProcess hx
  have hint : ∀ r, Integrable (fun ω => φ (x r ω)) P := fun r =>
    Integrable.of_bound (hf.continuous.measurable.comp (hxm r)).aestronglyMeasurable C0
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC0 _)
  have hd := dynkin_zero hW hx hB0 hB hf ht0 htT (hint 0) (hint t)
  rw [integral_lawAt (hxm t) hf.continuous, integral_lawAt (hxm 0) hf.continuous, hd,
    add_sub_cancel_left]
  simp_rw [integral_lawAt_itoGen hx ha hb hφ]
  have hLc := continuous_itoGen ha hb hφ.contDiff
  have hgm : Measurable (Function.uncurry fun u ω => itoGen a b φ u (x u ω)) :=
    hLc.measurable.comp (measurable_fst.prodMk hx.measurable)
  refine (intervalIntegral_integral_swap ?_).symm
  rw [uIoc_of_le ht0]
  refine Integrable.of_bound hgm.aestronglyMeasurable C ?_
  rw [Measure.restrict_prod_eq_prod_univ]
  refine (ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)).mpr
    (Eventually.of_forall fun p hp => ?_)
  rw [Real.norm_eq_abs]
  exact hCb p.1 ⟨hp.1.1.le, hp.1.2.trans htT⟩ _

/-- The mean generator `s ↦ ∫ L φ(·, s) dμ_s` is continuous on `[0, T]`. -/
lemma continuousOn_integral_itoGen (hx : IsItoDiffusion W 𝓕 P T a b x)
    (ha : Continuous (Function.uncurry a)) (hb : Continuous (Function.uncurry b))
    (hφ : IsC2c φ) :
    ContinuousOn (fun s => ∫ y, itoGen a b φ s y ∂(lawAt P x s)) (Icc 0 T) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC, hCb⟩ := exists_bound_itoGen ha hb hφ T
  have hLc := continuous_itoGen ha hb hφ.contDiff
  simp_rw [integral_lawAt_itoGen hx ha hb hφ]
  refine continuousOn_of_dominated (bound := fun _ => C) (fun s _ => ?_) (fun s hs => ?_)
    (integrable_const C) ?_
  · exact (hLc.measurable.comp (measurable_const.prodMk
      (measurable_apply_of_isItoProcess hx s))).aestronglyMeasurable
  · exact Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hCb s hs _
  · filter_upwards [hx.cont] with ω hω
    exact (hLc.comp (continuous_id.prodMk hω)).continuousOn

/-- **The weak Fokker–Planck equation** (Gardiner (4.3.18)–(4.3.19)):
`d/dt ∫ φ dμ_t = ∫ L φ(·, t) dμ_t` for `φ ∈ C²_c`, as a derivative within `[0, T]`. -/
theorem weakFP_hasDerivWithinAt (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) (hφ : IsC2c φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => ∫ y, φ y ∂(lawAt P x s))
      (∫ y, itoGen a b φ t y ∂(lawAt P x t)) (Icc 0 T) t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  set m : ℝ → ℝ := fun s => ∫ y, itoGen a b φ s y ∂(lawAt P x s) with hm
  have hmc : ContinuousOn m (Icc 0 T) := continuousOn_integral_itoGen hW hx ha hb hφ
  set m' : ℝ → ℝ := fun s => m (max 0 (min s T)) with hm'
  have hm'c : Continuous m' := hmc.comp_continuous (continuous_clamp T) (clamp_mem hT)
  have hG := ((hm'c.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt
    (s := Icc 0 T)).const_add (∫ y, φ y ∂(lawAt P x 0))
  have he : ∀ s ∈ Icc (0 : ℝ) T, ∫ y, φ y ∂(lawAt P x s) =
      (∫ y, φ y ∂(lawAt P x 0)) + ∫ u in (0 : ℝ)..s, m' u := by
    intro s hs
    have h := weakFP_integrated hW hx hB0 hB ha hb hφ hs.1 hs.2
    have : ∫ u in (0 : ℝ)..s, m' u = ∫ u in (0 : ℝ)..s, m u := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hs.1] at hu
      simp only [hm', clamp_eq ⟨hu.1, hu.2.trans hs.2⟩]
    rw [this]
    simp only [hm]
    linarith
  have hval : m' t = m t := by simp only [hm', clamp_eq ht]
  rw [hval] at hG
  exact hG.congr (fun s hs => he s hs) (he t ht)

/-- **The weak Fokker–Planck equation**, two-sided derivative at interior times `t ∈ (0, T)`. -/
theorem weakFP_hasDerivAt (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) (hφ : IsC2c φ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => ∫ y, φ y ∂(lawAt P x s)) (∫ y, itoGen a b φ t y ∂(lawAt P x t)) t :=
  (weakFP_hasDerivWithinAt hW hx hB0 hB ha hb hφ (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end Diffusion

namespace IsSDESol

variable {a b : ℝ → ℝ → ℝ} {T K B : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ} {φ : ℝ → ℝ}

/-- **Weak Fokker–Planck equation for SDE solutions, integrated form**:
`∫ φ dμ_t - ∫ φ dμ_0 = ∫₀ᵗ (∫ L φ(·, s) dμ_s) ds` for `φ ∈ C²_c`, `0 ≤ t ≤ T`. -/
theorem weakFP_integrated (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hc : SDECoeffs a b 0 T K)
    (ha : Continuous (Function.uncurry a)) (hb : Continuous (Function.uncurry b))
    (hB : ∀ y t, |b y t| ≤ B) (hφ : IsC2c φ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ y, φ y ∂(lawAt P x t) - ∫ y, φ y ∂(lawAt P x 0) =
      ∫ s in (0 : ℝ)..t, ∫ y, itoGen a b φ s y ∂(lawAt P x s) := by
  have hT : 0 ≤ T := ht0.trans htT
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  have h := Generator.weakFP_integrated hW (isItoDiffusion_clampProc hW hx hT hc ha hb hB) hB0
    (fun u _ ω => hB _ _) ha hb hφ ht0 htT
  rw [lawAt_clampProc ⟨ht0, htT⟩, lawAt_clampProc ⟨le_rfl, hT⟩] at h
  rw [h]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le ht0] at hu
  simp only [lawAt_clampProc ⟨hu.1, hu.2.trans htT⟩]

/-- **Weak Fokker–Planck equation for SDE solutions** (Gardiner (4.3.18)–(4.3.19)):
`d/dt ∫ φ dμ_t = ∫ L φ(·, t) dμ_t` within `[0, T]`, for `φ ∈ C²_c`. -/
theorem weakFP_hasDerivWithinAt (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hc : SDECoeffs a b 0 T K)
    (ha : Continuous (Function.uncurry a)) (hb : Continuous (Function.uncurry b))
    (hB : ∀ y t, |b y t| ≤ B) (hφ : IsC2c φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => ∫ y, φ y ∂(lawAt P x s))
      (∫ y, itoGen a b φ t y ∂(lawAt P x t)) (Icc 0 T) t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  have h := Generator.weakFP_hasDerivWithinAt hW (isItoDiffusion_clampProc hW hx hT hc ha hb hB)
    hB0 (fun u _ ω => hB _ _) ha hb hφ ht
  rw [lawAt_clampProc ht] at h
  exact h.congr (fun s hs => by simp only [lawAt_clampProc hs]) (by simp only [lawAt_clampProc ht])

/-- **Weak Fokker–Planck equation for SDE solutions**, two-sided derivative for `t ∈ (0, T)`. -/
theorem weakFP_hasDerivAt (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hc : SDECoeffs a b 0 T K)
    (ha : Continuous (Function.uncurry a)) (hb : Continuous (Function.uncurry b))
    (hB : ∀ y t, |b y t| ≤ B) (hφ : IsC2c φ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => ∫ y, φ y ∂(lawAt P x s)) (∫ y, itoGen a b φ t y ∂(lawAt P x t)) t :=
  (weakFP_hasDerivWithinAt hW hx hc ha hb hB hφ (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end IsSDESol

end Gardiner.Ito.Generator
