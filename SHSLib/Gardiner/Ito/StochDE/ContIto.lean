/-
# A continuous, adapted, jointly measurable version of the running Itô integral

For an Itô integrand `G` on `[0, T]`, `Gardiner.Ito.itoInt W 𝓕 P t G` is defined separately for each
`t` (as an element of `L²`).  This file constructs a process `I` with

* `(t, ω) ↦ I t ω` jointly measurable and `I t` `𝓕 t`-measurable for `t ≥ 0`;
* almost surely continuous paths on `[0, T]`;
* `I t = ∫₀ᵗ G dW` almost surely for every `t ∈ [0, T]`

(`exists_contItoVersion`, the canonical choice `contIto`), together with

* `IsContItoVersion.doob`: **Doob's `L²` inequality for the Itô integral**,
  `E[sup_{0 ≤ u ≤ t} |∫₀ᵘ G dW|²] ≤ 4 ∫₀ᵗ E[G²] ds`.

The construction approximates `G` by elementary integrands along a fast subsequence; Doob's
inequality for the differences of the elementary running integrals gives almost sure uniform
convergence on `[0, T]`.
-/
import SHSLib.Gardiner.Ito.StochDE.Version

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-! ### Generalities -/

/-- An almost sure limit and a mean-square limit agree almost surely. -/
lemma ae_eq_of_tendsto_ae_of_tendsto_sq {X : ℕ → Ω → ℝ} {Y Z : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hZ : AEMeasurable Z P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hl2 : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Z ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) : Y =ᵐ[P] Z := by
  have hmeas : ∀ n, AEMeasurable (fun ω => ‖X n ω - Z ω‖ₑ ^ 2) P := fun n =>
    (((hX n).sub hZ).enorm).pow_const 2
  have hfatou := lintegral_liminf_le' hmeas
  have hlim : ∀ᵐ ω ∂P, liminf (fun n => ‖X n ω - Z ω‖ₑ ^ 2) atTop = ‖Y ω - Z ω‖ₑ ^ 2 := by
    filter_upwards [hae] with ω hω
    exact (((ENNReal.continuous_pow 2).tendsto _).comp
      ((hω.sub_const (Z ω)).enorm)).liminf_eq
  rw [lintegral_congr_ae hlim, hl2.liminf_eq] at hfatou
  have h0 : ∫⁻ ω, ‖Y ω - Z ω‖ₑ ^ 2 ∂P = 0 := le_antisymm hfatou (zero_le _)
  have hYm : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae atTop hX hae
  rw [lintegral_eq_zero_iff' ((hYm.sub hZ).enorm.pow_const 2)] at h0
  filter_upwards [h0] with ω hω
  simpa [sub_eq_zero] using hω

/-- `D ≤ c D² + c⁻¹` in `ℝ≥0∞`. -/
lemma ennreal_le_mul_sq_add_inv (D c : ℝ≥0∞) : D ≤ c * D ^ 2 + c⁻¹ := by
  rcases eq_or_ne c ⊤ with rfl | hct
  · rcases eq_or_ne D 0 with rfl | hD
    · simp
    · rw [ENNReal.top_mul (pow_ne_zero 2 hD)]; exact le_top.trans le_self_add
  by_cases h : D ≤ c⁻¹
  · exact h.trans le_add_self
  · push_neg at h
    have h1 : 1 ≤ c * D := by
      rcases eq_or_ne c 0 with hc | hc
      · simp [hc] at h
      · calc 1 = c * c⁻¹ := (ENNReal.mul_inv_cancel hc (by
              exact hct)).symm
          _ ≤ c * D := mul_le_mul_right h.le c
    calc D = 1 * D := (one_mul D).symm
      _ ≤ (c * D) * D := mul_le_mul_left h1 D
      _ = c * D ^ 2 := by ring
      _ ≤ _ := le_self_add

/-! ### The regularised Wiener process and elementary running integrals -/

section Wiener

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

lemma measurable_regVer_W : Measurable fun p : ℝ × Ω => regVer W p.1 p.2 :=
  StochDE.measurable_regVer hW.measurable

lemma regVer_W_adapted {t : ℝ} (ht : 0 ≤ t) : StronglyMeasurable[𝓕 t] (regVer W t) :=
  StochDE.regVer_adapted hW.adapted ht

lemma ae_regVer_W_eq : ∀ᵐ ω ∂P, ∀ t, regVer W t ω = W t ω := by
  filter_upwards [hW.cont] with ω hω t
  exact regVer_eq hω.continuousAt

lemma ae_continuous_regVer_W : ∀ᵐ ω ∂P, Continuous fun t => regVer W t ω := by
  filter_upwards [hW.cont, ae_regVer_W_eq hW] with ω hc he
  simpa [he] using hc

variable {ι : Type*} [Fintype ι]

lemma measurable_running_regVer (H : ElemIntegrand 𝓕 P ι) :
    Measurable (Function.uncurry (H.running (regVer W))) := by
  have hŴ := measurable_regVer_W hW
  have hval : ∀ i, Measurable (H.val i) := fun i =>
    ((H.adapted i).mono (𝓕.le (H.left i))).measurable
  have e : Function.uncurry (H.running (regVer W)) = fun p : ℝ × Ω => ∑ i, H.val i p.2 *
      (regVer W (min (H.right i) p.1) p.2 - regVer W (min (H.left i) p.1) p.2) := by
    funext p; simp only [Function.uncurry, ElemIntegrand.running]
  rw [e]
  have hterm : ∀ i, Measurable fun p : ℝ × Ω => H.val i p.2 *
      (regVer W (min (H.right i) p.1) p.2 - regVer W (min (H.left i) p.1) p.2) := by
    intro i
    have h1 : Measurable fun p : ℝ × Ω => (min (H.right i) p.1, p.2) :=
      (measurable_const.min measurable_fst).prodMk measurable_snd
    have h2 : Measurable fun p : ℝ × Ω => (min (H.left i) p.1, p.2) :=
      (measurable_const.min measurable_fst).prodMk measurable_snd
    have h3 : Measurable fun p : ℝ × Ω => H.val i p.2 := (hval i).comp measurable_snd
    have h4 : Measurable fun p : ℝ × Ω => regVer W (min (H.right i) p.1) p.2 :=
      Measurable.comp (g := fun q : ℝ × Ω => regVer W q.1 q.2)
        (f := fun p : ℝ × Ω => (min (H.right i) p.1, p.2)) hŴ h1
    have h5 : Measurable fun p : ℝ × Ω => regVer W (min (H.left i) p.1) p.2 :=
      Measurable.comp (g := fun q : ℝ × Ω => regVer W q.1 q.2)
        (f := fun p : ℝ × Ω => (min (H.left i) p.1, p.2)) hŴ h2
    exact h3.mul (h4.sub h5)
  exact Finset.measurable_fun_sum _ fun i _ => hterm i

lemma running_regVer_adapted (H : ElemIntegrand 𝓕 P ι) {t : ℝ} (ht : 0 ≤ t) :
    StronglyMeasurable[𝓕 t] (H.running (regVer W) t) := by
  show StronglyMeasurable[𝓕 t] fun ω => ∑ i, H.val i ω *
    (regVer W (min (H.right i) t) ω - regVer W (min (H.left i) t) ω)
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  by_cases hlt : H.left i ≤ t
  · have hr0 : 0 ≤ min (H.right i) t := le_min ((H.left_nonneg i).trans (H.left_le_right i)) ht
    rw [min_eq_left hlt]
    exact ((H.adapted i).mono (𝓕.mono hlt)).mul
      (((regVer_W_adapted hW hr0).mono (𝓕.mono (min_le_right _ _))).sub
        ((regVer_W_adapted hW (H.left_nonneg i)).mono (𝓕.mono hlt)))
  · push_neg at hlt
    rw [min_eq_right hlt.le, min_eq_right (hlt.le.trans (H.left_le_right i))]
    simp only [sub_self, mul_zero]
    exact stronglyMeasurable_const

lemma ae_running_regVer_eq (H : ElemIntegrand 𝓕 P ι) :
    ∀ᵐ ω ∂P, ∀ t, H.running (regVer W) t ω = H.running W t ω := by
  filter_upwards [ae_regVer_W_eq hW] with ω hω t
  simp only [ElemIntegrand.running, hω]

lemma continuous_running_regVer (H : ElemIntegrand 𝓕 P ι) {ω : Ω}
    (hc : Continuous fun t => regVer W t ω) :
    Continuous fun t => H.running (regVer W) t ω := by
  show Continuous fun t => ∑ i, H.val i ω *
    (regVer W (min (H.right i) t) ω - regVer W (min (H.left i) t) ω)
  exact continuous_finset_sum _ fun i _ => continuous_const.mul
    ((hc.comp (continuous_const.min continuous_id)).sub
      (hc.comp (continuous_const.min continuous_id)))

end Wiener

/-! ### Uniform limits along summable increments -/

lemma limUnder_of_summable_incr {f : ℕ → ℝ → ℝ} {s : Set ℝ} (hf : ∀ j, ContinuousOn (f j) s)
    {u : ℕ → ℝ} (hu : Summable u) (hb : ∀ j, ∀ x ∈ s, |f (j + 1) x - f j x| ≤ u j) :
    ContinuousOn (fun x => limUnder atTop fun j => f j x) s ∧
      ∀ x ∈ s, Tendsto (fun j => f j x) atTop (𝓝 (limUnder atTop fun j => f j x)) := by
  set g : ℕ → ℝ → ℝ := fun j x => f (j + 1) x - f j x
  set L : ℝ → ℝ := fun x => f 0 x + ∑' j, g j x
  have hsum : ∀ x ∈ s, Summable fun j => g j x := fun x hx =>
    Summable.of_norm_bounded hu fun j => by
      rw [Real.norm_eq_abs]; exact hb j x hx
  have htend : ∀ x ∈ s, Tendsto (fun j => f j x) atTop (𝓝 (L x)) := by
    intro x hx
    have h1 := ((hsum x hx).hasSum.tendsto_sum_nat).const_add (f 0 x)
    refine h1.congr fun J => ?_
    simp only [g]
    rw [Finset.sum_range_sub (fun j => f j x)]
    ring
  have hlim : ∀ x ∈ s, (limUnder atTop fun j => f j x) = L x := fun x hx =>
    (htend x hx).limUnder_eq
  refine ⟨?_, fun x hx => (hlim x hx).symm ▸ htend x hx⟩
  have hLc : ContinuousOn L s :=
    (hf 0).add (continuousOn_tsum (fun j => (hf (j + 1)).sub (hf j)) hu
      fun j x hx => by rw [Real.norm_eq_abs]; exact hb j x hx)
  exact hLc.congr fun x hx => hlim x hx

lemma one_div_pow16_le (j : ℕ) : (1 : ℝ) / ((16 ^ j : ℕ) + 1 : ℝ) ≤ (1 / 16) ^ j := by
  rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
  push_cast; linarith

lemma tendsto_ofReal_one_div_pow16 :
    Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((16 ^ j : ℕ) + 1 : ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => (1 / ((16 ^ j : ℕ) + 1 : ℝ))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num))
      (fun j => by positivity) one_div_pow16_le
  simpa using (ENNReal.continuous_ofReal.tendsto 0).comp h

/-! ### The construction -/

/-- The `j`-th approximating running integral, along the subsequence `16 ^ j` of
`Gardiner.Ito.approxSeq`, computed with the regularised Wiener process. -/
def approxRun (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ)
    (G : ℝ → Ω → ℝ) (j : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (approxSeq 𝓕 P T G (16 ^ j)).2.running (regVer W) t ω

/-- **The continuous version of the running Itô integral** `t ↦ ∫₀ᵗ G dW` on `[0, T]`. -/
def itoCont (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ)
    (G : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun j => approxRun W 𝓕 P T G j t ω

/-- The properties of a continuous version of the running Itô integral on `[0, T]`. -/
structure IsContItoVersion (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ)
    (G : ℝ → Ω → ℝ) (I : ℝ → Ω → ℝ) : Prop where
  measurable : Measurable (Function.uncurry I)
  adapted : ∀ t, 0 ≤ t → StronglyMeasurable[𝓕 t] (I t)
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => I t ω) (Set.Icc 0 T)
  eq : ∀ t ∈ Set.Icc 0 T, I t =ᵐ[P] itoInt W 𝓕 P t G

section Construction

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) {T : ℝ} {G : ℝ → Ω → ℝ}
include hW

lemma measurable_approxRun (j : ℕ) : Measurable (Function.uncurry (approxRun W 𝓕 P T G j)) :=
  measurable_running_regVer hW _

lemma measurable_itoCont : Measurable (Function.uncurry (itoCont W 𝓕 P T G)) :=
  (StronglyMeasurable.limUnder (l := atTop)
    fun j => (measurable_approxRun hW (T := T) (G := G) j).stronglyMeasurable).measurable

lemma itoCont_adapted {t : ℝ} (ht : 0 ≤ t) : StronglyMeasurable[𝓕 t] (itoCont W 𝓕 P T G t) :=
  stronglyMeasurable_limUnder_nat fun j => running_regVer_adapted hW _ ht

/-- The mean-square distance between consecutive approximating elementary integrals. -/
lemma integral_sq_approx_diff_le (hG : IsItoIntegrand 𝓕 P T G) (j : ℕ) :
    ∫ ω, ((approxSeq 𝓕 P T G (16 ^ (j + 1))).2.integral W ω -
      (approxSeq 𝓕 P T G (16 ^ j)).2.integral W ω) ^ 2 ∂P ≤ 4 * (1 / 16) ^ j := by
  have := hW.isProbabilityMeasure
  set a := (approxSeq 𝓕 P T G (16 ^ (j + 1))).2.integral W
  set b := (approxSeq 𝓕 P T G (16 ^ j)).2.integral W
  set J := itoInt W 𝓕 P T G
  have ha := (approxSeq 𝓕 P T G (16 ^ (j + 1))).2.memLp_integral hW
  have hb := (approxSeq 𝓕 P T G (16 ^ j)).2.memLp_integral hW
  have hJ := memLp_itoInt hW hG
  have h1 : ∫ ω, (a ω - J ω) ^ 2 ∂P < 1 / ((16 ^ (j + 1) : ℕ) + 1 : ℝ) := by
    rw [itoInt_sub_sq hW hG _ (approxSeq_spec hG _).1]; exact (approxSeq_spec hG _).2
  have h2 : ∫ ω, (b ω - J ω) ^ 2 ∂P < 1 / ((16 ^ j : ℕ) + 1 : ℝ) := by
    rw [itoInt_sub_sq hW hG _ (approxSeq_spec hG _).1]; exact (approxSeq_spec hG _).2
  have hi1 : Integrable (fun ω => (a ω - J ω) ^ 2) P := (ha.sub hJ).integrable_sq
  have hi2 : Integrable (fun ω => (b ω - J ω) ^ 2) P := (hb.sub hJ).integrable_sq
  have hi3 : Integrable (fun ω => (a ω - b ω) ^ 2) P := (ha.sub hb).integrable_sq
  have h3 : ∫ ω, (a ω - b ω) ^ 2 ∂P ≤
      ∫ ω, (2 * (a ω - J ω) ^ 2 + 2 * (b ω - J ω) ^ 2) ∂P := by
    refine integral_mono hi3 ((hi1.const_mul 2).add (hi2.const_mul 2)) fun ω => ?_
    nlinarith [sq_nonneg (a ω + b ω - 2 * J ω)]
  rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
    integral_const_mul] at h3
  have h16 := one_div_pow16_le j
  have h16' : (1 : ℝ) / ((16 ^ (j + 1) : ℕ) + 1 : ℝ) ≤ (1 / 16) ^ j := by
    refine le_trans ?_ h16
    rw [one_div_le_one_div (by positivity) (by positivity)]
    push_cast; rw [pow_succ]; nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 16 by norm_num) (n := j)]
  linarith

/-- The dyadic supremum over `[0, T]` of the difference of consecutive approximations. -/
def approxDiffSup (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ)
    (G : ℝ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ≥0∞ :=
  dsup (fun t ω => approxRun W 𝓕 P T G (j + 1) t ω - approxRun W 𝓕 P T G j t ω) 0 T ω

omit hW in
lemma measurable_approxDiffSup' (hm : ∀ j, Measurable (Function.uncurry (approxRun W 𝓕 P T G j)))
    (j : ℕ) : Measurable (approxDiffSup W 𝓕 P T G j) :=
  measurable_dsup (fun u => (measurable_of_uncurry (hm (j + 1)) u).sub
    (measurable_of_uncurry (hm j) u)) 0 T

lemma measurable_approxDiffSup (j : ℕ) : Measurable (approxDiffSup W 𝓕 P T G j) :=
  measurable_approxDiffSup' (measurable_approxRun hW) j

lemma lintegral_approxDiffSup_sq_le (hG : IsItoIntegrand 𝓕 P T G) (hT : 0 ≤ T) (j : ℕ) :
    ∫⁻ ω, approxDiffSup W 𝓕 P T G j ω ^ 2 ∂P ≤ ENNReal.ofReal (16 * (1 / 16) ^ j) := by
  have := hW.isProbabilityMeasure
  set H1 := (approxSeq 𝓕 P T G (16 ^ (j + 1))).2
  set H0 := (approxSeq 𝓕 P T G (16 ^ j)).2
  set M : ℝ → Ω → ℝ := H1.running W - H0.running W
  have hM : Martingale M 𝓕 P :=
    (ElemIntegrand.martingale_running hW H1).sub (ElemIntegrand.martingale_running hW H0)
  have hMT : MemLp (M T) 2 P :=
    (ElemIntegrand.memLp_running hW H1 T).sub (ElemIntegrand.memLp_running hW H0 T)
  have hX : ∀ u ∈ Set.Icc 0 T, (fun ω => approxRun W 𝓕 P T G (j + 1) u ω -
      approxRun W 𝓕 P T G j u ω) =ᵐ[P] M u := by
    intro u _
    filter_upwards [ae_running_regVer_eq hW H1, ae_running_regVer_eq hW H0] with ω h1 h0
    simp only [approxRun, M, Pi.sub_apply]
    rw [h1, h0]
  have h := doob_L2_dsup hM hT hMT hX
  have hMT' : M T = H1.integral W - H0.integral W := by
    simp only [M, Pi.sub_apply]
    rw [ElemIntegrand.running_eq_integral W H1 (approxSeq_spec hG _).1,
      ElemIntegrand.running_eq_integral W H0 (approxSeq_spec hG _).1]
  rw [lintegral_enorm_sq_eq hMT, hMT'] at h
  refine h.trans ?_
  have h2 := integral_sq_approx_diff_le hW hG j
  calc 4 * ENNReal.ofReal (∫ ω, (H1.integral W - H0.integral W) ω ^ 2 ∂P)
      ≤ 4 * ENNReal.ofReal (4 * (1 / 16) ^ j) := by
        gcongr
        simpa using h2
    _ = ENNReal.ofReal (16 * (1 / 16) ^ j) := by
        rw [show (16 : ℝ) * (1 / 16) ^ j = 4 * (4 * (1 / 16) ^ j) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num

lemma lintegral_approxDiffSup_le (hG : IsItoIntegrand 𝓕 P T G) (hT : 0 ≤ T) (j : ℕ) :
    ∫⁻ ω, approxDiffSup W 𝓕 P T G j ω ∂P ≤ ENNReal.ofReal (17 * (1 / 4) ^ j) := by
  have := hW.isProbabilityMeasure
  set c : ℝ≥0∞ := ENNReal.ofReal (4 ^ j)
  have hm := measurable_approxDiffSup hW (T := T) (G := G) j
  calc ∫⁻ ω, approxDiffSup W 𝓕 P T G j ω ∂P
      ≤ ∫⁻ ω, (c * approxDiffSup W 𝓕 P T G j ω ^ 2 + c⁻¹) ∂P :=
        lintegral_mono fun ω => ennreal_le_mul_sq_add_inv _ _
    _ = c * ∫⁻ ω, approxDiffSup W 𝓕 P T G j ω ^ 2 ∂P + c⁻¹ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (hm.pow_const 2)]
        simp
    _ ≤ c * ENNReal.ofReal (16 * (1 / 16) ^ j) + c⁻¹ := by
        gcongr
        exact lintegral_approxDiffSup_sq_le hW hG hT j
    _ = ENNReal.ofReal (17 * (1 / 4) ^ j) := by
        simp only [c]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have h16 : (1 / 16 : ℝ) ^ j = (1 / 4) ^ j * (1 / 4) ^ j := by
          rw [← mul_pow]; norm_num
        have h4 : (4 : ℝ) ^ j * (1 / 4) ^ j = 1 := by rw [← mul_pow]; norm_num
        have h4' : ((4 : ℝ) ^ j)⁻¹ = (1 / 4) ^ j := by rw [one_div_pow, one_div]
        rw [h16, h4']
        linear_combination (16 * (1 / 4 : ℝ) ^ j) * h4

lemma ae_tsum_approxDiffSup_lt_top (hG : IsItoIntegrand 𝓕 P T G) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∑' j, approxDiffSup W 𝓕 P T G j ω < ⊤ := by
  have hm := measurable_approxDiffSup hW (T := T) (G := G)
  refine ae_lt_top (Measurable.ennreal_tsum hm) ?_
  rw [lintegral_tsum fun j => (hm j).aemeasurable]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j => lintegral_approxDiffSup_le hW hG hT j)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 17)]
  exact ENNReal.ofReal_ne_top

/-- The good set: the regularised Wiener path is continuous and the dyadic suprema of the
consecutive differences are summable.  On it, the approximations converge uniformly on `[0, T]`. -/
lemma itoCont_good (hT : 0 ≤ T) {ω : Ω} (hc : Continuous fun t => regVer W t ω)
    (hS : ∑' j, approxDiffSup W 𝓕 P T G j ω < ⊤) :
    ContinuousOn (fun t => itoCont W 𝓕 P T G t ω) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, Tendsto (fun j => approxRun W 𝓕 P T G j t ω) atTop
        (𝓝 (itoCont W 𝓕 P T G t ω)) := by
  have hfc : ∀ j, Continuous fun t => approxRun W 𝓕 P T G j t ω := fun j =>
    continuous_running_regVer hW _ hc
  have hne : ∀ j, approxDiffSup W 𝓕 P T G j ω ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top hS.ne (ENNReal.le_tsum j)
  refine limUnder_of_summable_incr (f := fun j t => approxRun W 𝓕 P T G j t ω)
    (fun j => (hfc j).continuousOn) (u := fun j => (approxDiffSup W 𝓕 P T G j ω).toReal)
    (ENNReal.summable_toReal hS.ne) fun j t ht => ?_
  have h1 : ‖approxRun W 𝓕 P T G (j + 1) t ω - approxRun W 𝓕 P T G j t ω‖ₑ ≤
      approxDiffSup W 𝓕 P T G j ω := by
    rw [approxDiffSup, dsup_eq_iSup hT ((hfc (j + 1)).sub (hfc j)).continuousOn]
    exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc 0 T) =>
      ‖approxRun W 𝓕 P T G (j + 1) u ω - approxRun W 𝓕 P T G j u ω‖ₑ) t ht
  have h2 := ENNReal.toReal_mono (hne j) h1
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] at h2

/-- **The continuous version of the running Itô integral.** -/
theorem isContItoVersion_itoCont (hG : IsItoIntegrand 𝓕 P T G) (hT : 0 ≤ T) :
    IsContItoVersion W 𝓕 P T G (itoCont W 𝓕 P T G) := by
  have := hW.isProbabilityMeasure
  have hgood : ∀ᵐ ω ∂P, (Continuous fun t => regVer W t ω) ∧
      ∑' j, approxDiffSup W 𝓕 P T G j ω < ⊤ := by
    filter_upwards [ae_continuous_regVer_W hW, ae_tsum_approxDiffSup_lt_top hW hG hT] with ω h1 h2
    exact ⟨h1, h2⟩
  refine ⟨measurable_itoCont hW, fun t ht => itoCont_adapted hW ht, ?_, fun t ht => ?_⟩
  · filter_upwards [hgood] with ω hω
    exact (itoCont_good hW hT hω.1 hω.2).1
  · have hGt := hG.mono ht.2
    set H := fun j : ℕ => (approxSeq 𝓕 P T G (16 ^ j)).2 with hH
    refine ae_eq_of_tendsto_ae_of_tendsto_sq (X := fun j => approxRun W 𝓕 P T G j t)
      (fun j => (measurable_of_uncurry (measurable_approxRun hW j) t).aemeasurable)
      (memLp_itoInt hW hGt).aestronglyMeasurable.aemeasurable ?_ ?_
    · filter_upwards [hgood] with ω hω
      exact (itoCont_good hW hT hω.1 hω.2).2 t ht
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_ofReal_one_div_pow16 (fun j => zero_le _) fun j => ?_
      have hae : (fun ω => approxRun W 𝓕 P T G j t ω) =ᵐ[P]
          ((H j).restrictTo t ht.1).integral W := by
        filter_upwards [ae_running_regVer_eq hW (H j)] with ω hω
        rw [ElemIntegrand.integral_restrictTo]
        exact hω t
      have hm : MemLp (((H j).restrictTo t ht.1).integral W - itoInt W 𝓕 P t G) 2 P :=
        (ElemIntegrand.memLp_integral hW _).sub (memLp_itoInt hW hGt)
      calc ∫⁻ ω, ‖approxRun W 𝓕 P T G j t ω - itoInt W 𝓕 P t G ω‖ₑ ^ 2 ∂P
          = ∫⁻ ω, ‖(((H j).restrictTo t ht.1).integral W - itoInt W 𝓕 P t G) ω‖ₑ ^ 2 ∂P := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae] with ω hω
            simp only [Pi.sub_apply, hω]
        _ = ENNReal.ofReal (∫ ω, (((H j).restrictTo t ht.1).integral W ω -
              itoInt W 𝓕 P t G ω) ^ 2 ∂P) := lintegral_enorm_sq_eq hm
        _ ≤ ENNReal.ofReal (1 / ((16 ^ j : ℕ) + 1 : ℝ)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [itoInt_sub_sq hW hGt _ ((H j).restrictTo_supportedIn ht.1)]
            refine ((H j).dist_restrictTo_le ht.1 ht.2 hG.memLp).trans ?_
            exact (approxSeq_spec hG _).2.le

/-- **Doob's `L²` maximal inequality for the Itô integral**:
`E[sup_{0 ≤ u ≤ t} |∫₀ᵘ G dW|²] ≤ 4 ∫₀ᵗ E[G(s)²] ds`, for any continuous version. -/
theorem IsContItoVersion.doob {I : ℝ → Ω → ℝ} (hI : IsContItoVersion W 𝓕 P T G I)
    (hG : IsItoIntegrand 𝓕 P T G) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∫⁻ ω, (⨆ u ∈ Set.Icc 0 t, ‖I u ω‖ₑ) ^ 2 ∂P ≤
      4 * ENNReal.ofReal (∫ s in Set.Ioc 0 t, ∫ ω, G s ω ^ 2 ∂P) := by
  have := hW.isProbabilityMeasure
  have hGt := hG.mono ht.2
  have hM := martingale_itoInt_min hW hGt
  have hMt : MemLp (itoInt W 𝓕 P (min t t) G) 2 P := by rw [min_self]; exact memLp_itoInt hW hGt
  have h := doob_L2_contin (X := I) hM ht.1 hMt (fun u hu => by
      have := hI.eq u ⟨hu.1, hu.2.trans ht.2⟩
      simpa [min_eq_left hu.2] using this)
    (by filter_upwards [hI.cont] with ω hω
        exact hω.mono (Set.Icc_subset_Icc_right ht.2))
  rwa [min_self, lintegral_enorm_sq_eq (memLp_itoInt hW hGt), itoInt_sq hW hGt] at h

end Construction

end Gardiner.Ito.StochDE
