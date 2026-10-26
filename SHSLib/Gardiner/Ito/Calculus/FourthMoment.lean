/-
# Fourth moments of Itô integrals of bounded integrands

For an Itô integrand `G` with `|G| ≤ K` which vanishes outside `(s, t]`,
`E[(∫₀ᵀ G dW)⁴] ≤ 3 K⁴ (t - s)²` (`Gardiner.Ito.itoInt_fourth_le`).

The bound is first proved for elementary integrands with non-overlapping, time-ordered pieces
(`Gardiner.Ito.IsFWiener.ordSum_fourth`), by the recursion
`E[(M + ξ ΔW)⁴] = E[M⁴] + 6 Δt E[M² ξ²] + 3 Δt² E[ξ⁴]`, and then passed to the limit along the
time-ordered approximations of the density theorem (`Gardiner.Ito.shiftElem`), clipped to
`(s, t]`, by Fatou's lemma.  It is the estimate behind the quadratic variation of a general Itô
integral (`Gardiner.Ito.QuadVar`).
-/
import SHSLib.Gardiner.Ito.Calculus.Localize
import SHSLib.Gardiner.Ito.Calculus.ItoFormula

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

/-- Third moment of `N(0, v)`. -/
theorem gaussReal_moment_three (v : ℝ≥0) : ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
  have h := gaussianReal_map_neg (μ := 0) (v := v)
  rw [neg_zero] at h
  have e1 : ∫ x, x ^ 3 ∂(gaussianReal 0 v) = ∫ x, (-x) ^ 3 ∂(gaussianReal 0 v) := by
    conv_lhs => rw [← h]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have e2 : ∫ x, (-x) ^ 3 ∂(gaussianReal 0 v) = -∫ x, x ^ 3 ∂(gaussianReal 0 v) := by
    rw [← integral_neg]; congr 1; funext x; ring
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- The elementary integral `Σ_{j < m} ξⱼ (W(rⱼ) - W(lⱼ))` of a sequence of pieces. -/
def ordSum (W : ℝ → Ω → ℝ) (ξ : ℕ → Ω → ℝ) (l r : ℕ → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range m, ξ j ω * (W (r j) ω - W (l j) ω)

omit mΩ in
lemma ordSum_succ (W : ℝ → Ω → ℝ) (ξ : ℕ → Ω → ℝ) (l r : ℕ → ℝ) (m : ℕ) (ω : Ω) :
    ordSum W ξ l r (m + 1) ω = ordSum W ξ l r m ω + ξ m ω * (W (r m) ω - W (l m) ω) := by
  simp [ordSum, Finset.sum_range_succ]


section Approx

variable [IsFiniteMeasure P] {T K : ℝ} {G : ℝ → Ω → ℝ}

/-- **Density, bounded case**, with the time-ordered approximant `shiftElem` made explicit. -/
lemma exists_shiftElem_approx (hG : IsItoIntegrand 𝓕 P T G) (hK0 : 0 ≤ K)
    (hK : ∀ t ω, |G t ω| ≤ K) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h s : ℝ) (hh : 0 < h) (hs : 0 < s),
      ∫ p, (Function.uncurry (shiftElem hG hK0 hK hT hh hs).process p - Function.uncurry G p) ^ 2
        ∂(tsMeasure P T) < ε := by
  obtain ⟨r, hr, hrΨ⟩ := Metric.tendsto_nhds_nhds.mp
    (tendsto_transErr hG.measurable hK0 hK hT (P := P)) (ε / 2) (by positivity)
  set h := r / 2 with hhdef
  have hh : 0 < h := by positivity
  set D : ℝ → ℝ := fun s => ∫ p, shiftErr T G h s p ∂(tsMeasure P T) with hD
  set Ψ : ℝ → ℝ := fun q => ∫ p, transErr T G q p ∂(tsMeasure P T) with hΨ
  have hDΨ : ∫ s in Set.Ioo 0 h, D s = ∫ q in Set.Ioo 0 h, Ψ q :=
    integral_shiftErr hG.measurable hK0 hK hh
  have hDi : IntegrableOn D (Set.Ioo 0 h) := by
    have hm : StronglyMeasurable (Function.uncurry (shiftErr T G h)) :=
      (measurable_shiftErr hG.measurable h).stronglyMeasurable
    refine Integrable.of_bound (hm.integral_prod_right (ν := tsMeasure P T)).aestronglyMeasurable
      ((2 * K) ^ 2 * (tsMeasure P T).real Set.univ) (Eventually.of_forall fun s => ?_)
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun p =>
      shiftErr_le hK0 hK h s p)
  have hΨi : IntegrableOn Ψ (Set.Ioo 0 h) := by
    have hm : StronglyMeasurable (Function.uncurry (transErr T G)) :=
      (measurable_transErr hG.measurable).stronglyMeasurable
    refine Integrable.of_bound (hm.integral_prod_right (ν := tsMeasure P T)).aestronglyMeasurable
      ((2 * K) ^ 2 * (tsMeasure P T).real Set.univ) (Eventually.of_forall fun q => ?_)
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun p =>
      transErr_le hK0 hK q p)
  have hvol : volume.real (Set.Ioo (0 : ℝ) h) = h := by
    simp [measureReal_def, Real.volume_Ioo, hh.le]
  have hΨle : ∫ q in Set.Ioo 0 h, Ψ q ≤ ∫ q in Set.Ioo 0 h, ε / 2 := by
    refine setIntegral_mono_on hΨi (integrableOn_const (by simp [Real.volume_Ioo]))
      measurableSet_Ioo fun q hq => ?_
    have hq' : dist q 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hq.1]; linarith [hq.2]
    have := hrΨ hq'
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  obtain ⟨s, hs, hDs⟩ : ∃ s ∈ Set.Ioo 0 h, D s < ε := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∫ s in Set.Ioo 0 h, ε ≤ ∫ s in Set.Ioo 0 h, D s :=
      setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioo])) hDi measurableSet_Ioo
        hcon
    rw [setIntegral_const, hvol, smul_eq_mul] at h1
    rw [setIntegral_const, hvol, smul_eq_mul] at hΨle
    nlinarith
  refine ⟨h, s, hh, hs.1, ?_⟩
  have : ∫ p, (Function.uncurry (shiftElem hG hK0 hK hT hh hs.1).process p -
      Function.uncurry G p) ^ 2 ∂(tsMeasure P T) = D s := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Ioc_tsMeasure T] with p hp
    simp only [Function.uncurry, shiftErr]
    rw [shiftElem_process hG hK0 hK hT hh hs.1 hs.2 hp,
      extIcc_of_mem (Set.Ioc_subset_Icc_self hp)]
  rw [this]; exact hDs

end Approx

/-- Clamping to `[a, b]`. -/
def clampI (a b x : ℝ) : ℝ := max a (min x b)

lemma clampI_mono (a b : ℝ) : Monotone (clampI a b) := fun _ _ h =>
  max_le_max le_rfl (min_le_min_right b h)

lemma le_clampI (a b x : ℝ) : a ≤ clampI a b x := le_max_left _ _

lemma clampI_le {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clampI a b x ≤ b :=
  max_le hab (min_le_right _ _)

lemma cellInd_clampI {a b L R : ℝ} (hL : L ≤ b) (u : ℝ) :
    cellInd (clampI a b L) (clampI a b R) u = cellInd L R u * cellInd a b u := by
  have hcl : clampI a b L = max a L := by rw [clampI, min_eq_left hL]
  rw [hcl]
  by_cases h1 : u ∈ Set.Ioc L R
  · by_cases h2 : u ∈ Set.Ioc a b
    · rw [cellInd_mem h1, cellInd_mem h2, cellInd_mem]
      · ring
      exact ⟨max_lt h2.1 h1.1, le_max_of_le_right (le_min h1.2 h2.2)⟩
    · rw [cellInd_notMem h2, mul_zero, cellInd_notMem]
      rintro ⟨h3, h4⟩
      apply h2
      refine ⟨(le_max_left a L).trans_lt h3, ?_⟩
      rcases le_max_iff.mp h4 with h5 | h5
      · exact absurd ((le_max_left a L).trans_lt h3) (not_lt.mpr h5)
      · exact h5.trans (min_le_right _ _)
  · rw [cellInd_notMem h1, zero_mul, cellInd_notMem]
    rintro ⟨h3, h4⟩
    apply h1
    refine ⟨(le_max_right a L).trans_lt h3, ?_⟩
    rcases le_max_iff.mp h4 with h5 | h5
    · exact absurd ((le_max_left a L).trans_lt h3) (not_lt.mpr h5)
    · exact h5.trans (min_le_left _ _)

namespace ElemIntegrand

/-- The elementary integrand with the pieces `ξⱼ 1_{(lⱼ, rⱼ]}`, `j < N`. -/
def ofSeq (N : ℕ) (l r : ℕ → ℝ) (ξ : ℕ → Ω → ℝ) (hl : ∀ j, 0 ≤ l j) (hlr : ∀ j, l j ≤ r j)
    (hξ : ∀ j, StronglyMeasurable[𝓕 (l j)] (ξ j)) (hξ2 : ∀ j, MemLp (ξ j) 2 P) :
    ElemIntegrand 𝓕 P (Fin N) where
  left j := l j
  right j := r j
  val j := ξ j
  left_nonneg j := hl j
  left_le_right j := hlr j
  adapted j := hξ j
  memLp j := hξ2 j

lemma integral_ofSeq (W : ℝ → Ω → ℝ) (N : ℕ) (l r : ℕ → ℝ) (ξ : ℕ → Ω → ℝ)
    (hl : ∀ j, 0 ≤ l j) (hlr : ∀ j, l j ≤ r j)
    (hξ : ∀ j, StronglyMeasurable[𝓕 (l j)] (ξ j)) (hξ2 : ∀ j, MemLp (ξ j) 2 P) :
    (ofSeq (P := P) N l r ξ hl hlr hξ hξ2).integral W = ordSum W ξ l r N := by
  funext ω
  simp only [integral, ofSeq, ordSum]
  exact Fin.sum_univ_eq_sum_range (fun j => ξ j ω * (W (r j) ω - W (l j) ω)) N

lemma process_ofSeq (N : ℕ) (l r : ℕ → ℝ) (ξ : ℕ → Ω → ℝ)
    (hl : ∀ j, 0 ≤ l j) (hlr : ∀ j, l j ≤ r j)
    (hξ : ∀ j, StronglyMeasurable[𝓕 (l j)] (ξ j)) (hξ2 : ∀ j, MemLp (ξ j) 2 P) (u : ℝ) (ω : Ω) :
    (ofSeq (P := P) N l r ξ hl hlr hξ hξ2).process u ω =
      ∑ j ∈ Finset.range N, ξ j ω * cellInd (l j) (r j) u := by
  simp only [process, ofSeq]
  exact Fin.sum_univ_eq_sum_range (fun j => ξ j ω * cellInd (l j) (r j) u) N

end ElemIntegrand

/-- **Fatou's lemma** for nonnegative real random variables converging almost surely. -/
lemma integrable_of_ae_tendsto_of_integral_le {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf0 : ∀ n ω, 0 ≤ f n ω) (hfi : ∀ n, Integrable (f n) P) (hgm : AEStronglyMeasurable g P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) {C : ℝ}
    (hC : ∀ n, ∫ ω, f n ω ∂P ≤ C) : Integrable g P ∧ ∫ ω, g ω ∂P ≤ C := by
  have hg0 : ∀ᵐ ω ∂P, 0 ≤ g ω := hlim.mono fun ω hω =>
    ge_of_tendsto' hω fun n => hf0 n ω
  have hC0 : 0 ≤ C := (integral_nonneg (hf0 0)).trans (hC 0)
  have hfat : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P ≤ ENNReal.ofReal C := by
    calc ∫⁻ ω, ENNReal.ofReal (g ω) ∂P
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂P := by
          refine lintegral_congr_ae (hlim.mono fun ω hω => ?_)
          exact ((ENNReal.continuous_ofReal.tendsto _).comp hω).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop :=
          lintegral_liminf_le' fun n => (hfi n).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal C := by
          refine liminf_le_of_le ⟨0, by simp⟩ fun x hx => ?_
          obtain ⟨n, hn⟩ := hx.exists
          refine hn.trans ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hf0 n))]
          exact ENNReal.ofReal_le_ofReal (hC n)
  have hint : Integrable g P := by
    refine ⟨hgm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hg0]
    exact hfat.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hg0 hgm]
  exact ENNReal.toReal_le_of_le_ofReal hC0 hfat

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

lemma IsFWiener.integral_incr_three {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W t ω - W s ω) ^ 3 ∂P = 0 := by
  rw [integral_comp_of_map_gauss (f := fun x => x ^ 3) (hW.measurable_incr s t)
    (hW.law_incr hs hst) (continuous_pow 3).measurable, gaussReal_moment_three]

/-- **Fourth moment of an ordered elementary integral**: if the pieces are time-ordered
(`lⱼ ≤ rⱼ ≤ lⱼ₊₁`), `ξⱼ` is `𝓕 lⱼ`-measurable and `|ξⱼ| ≤ K`, then
`E[M_m⁴] ≤ 3 (K² Σ_{j<m} (rⱼ - lⱼ))²` (and `E[M_m²] ≤ K² Σ_{j<m} (rⱼ - lⱼ)`). -/
theorem IsFWiener.ordSum_fourth {ξ : ℕ → Ω → ℝ} {l r : ℕ → ℝ} {K : ℝ}
    (hl0 : 0 ≤ l 0) (hlr : ∀ j, l j ≤ r j) (hrl : ∀ j, r j ≤ l (j + 1))
    (hξ : ∀ j, StronglyMeasurable[𝓕 (l j)] (ξ j)) (hξb : ∀ j ω, |ξ j ω| ≤ K) (m : ℕ) :
    StronglyMeasurable[𝓕 (l m)] (ordSum W ξ l r m) ∧
      Integrable (fun ω => ordSum W ξ l r m ω ^ 4) P ∧
      ∫ ω, ordSum W ξ l r m ω ^ 2 ∂P ≤ K ^ 2 * ∑ j ∈ Finset.range m, (r j - l j) ∧
      ∫ ω, ordSum W ξ l r m ω ^ 4 ∂P ≤ 3 * (K ^ 2 * ∑ j ∈ Finset.range m, (r j - l j)) ^ 2 := by
  have := hW.isProbabilityMeasure
  have hmono : Monotone l := monotone_nat_of_le_succ fun j => (hlr j).trans (hrl j)
  have hl : ∀ j, 0 ≤ l j := fun j => hl0.trans (hmono (Nat.zero_le j))
  have hK2 : ∀ j ω, ξ j ω ^ 2 ≤ K ^ 2 := fun j ω => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hξb j ω) 2
  have hK4 : ∀ j ω, ξ j ω ^ 4 ≤ K ^ 4 := fun j ω => by
    have := hK2 j ω
    calc ξ j ω ^ 4 = (ξ j ω ^ 2) ^ 2 := by ring
      _ ≤ (K ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) this 2
      _ = K ^ 4 := by ring
  have hξm : ∀ j, Measurable (ξ j) := fun j => ((hξ j).mono (𝓕.le _)).measurable
  induction m with
  | zero =>
    have h0 : ordSum W ξ l r 0 = fun _ => 0 := by funext ω; simp [ordSum]
    rw [h0]
    exact ⟨stronglyMeasurable_const, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨hMsm, hM4, hM2, hM4le⟩ := ih
    set M := ordSum W ξ l r m with hMdef
    set S := ∑ j ∈ Finset.range m, (r j - l j) with hS
    set d := r m - l m with hd
    have hd0 : 0 ≤ d := sub_nonneg.mpr (hlr m)
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hlr j)
    have hMm : Measurable M := (hMsm.mono (𝓕.le _)).measurable
    -- integrability of low powers from the fourth
    have hMpow : ∀ k ≤ 4, Integrable (fun ω => M ω ^ k) P := by
      intro k hk
      refine (hM4.add (integrable_const 1)).mono' (hMm.pow_const k).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_pow, Pi.add_apply]
      rcases le_total (|M ω|) 1 with h | h
      · have : |M ω| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) h
        have : 0 ≤ M ω ^ 4 := by positivity
        linarith
      · have : |M ω| ^ k ≤ |M ω| ^ 4 := pow_le_pow_right₀ h hk
        have e : |M ω| ^ 4 = M ω ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        linarith
    have hbdd : ∀ (k : ℕ) (n : ℕ), k ≤ 4 →
        Integrable (fun ω => M ω ^ k * ξ m ω ^ n) P := by
      intro k n hk
      refine ((hMpow k hk).norm.const_mul (|K| ^ n)).mono'
        ((hMm.pow_const k).mul ((hξm m).pow_const n)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((hξb m ω).trans (le_abs_self K)) n
    have hsmk : ∀ (k n : ℕ), StronglyMeasurable[𝓕 (l m)] (fun ω => M ω ^ k * ξ m ω ^ n) :=
      fun k n => (hMsm.pow k).mul ((hξ m).pow n)
    have hlm := hl m
    have hlrm := hlr m
    obtain ⟨i1, e1⟩ := hW.mul_incr_fun hlm hlrm (hsmk 3 1) (hbdd 3 1 (by norm_num))
      (g := fun x => x) measurable_id (hW.integrable_incr hlm hlrm)
    obtain ⟨i2, e2⟩ := hW.mul_incr_fun hlm hlrm (hsmk 2 2) (hbdd 2 2 (by norm_num))
      (g := fun x => x ^ 2) (continuous_pow 2).measurable (hW.integrable_incr_pow hlm hlrm 2)
    obtain ⟨i3, e3⟩ := hW.mul_incr_fun hlm hlrm (hsmk 1 3) (hbdd 1 3 (by norm_num))
      (g := fun x => x ^ 3) (continuous_pow 3).measurable (hW.integrable_incr_pow hlm hlrm 3)
    obtain ⟨i4, e4⟩ := hW.mul_incr_fun hlm hlrm (hsmk 0 4) (hbdd 0 4 (by norm_num))
      (g := fun x => x ^ 4) (continuous_pow 4).measurable (hW.integrable_incr_pow hlm hlrm 4)
    obtain ⟨j1, f1⟩ := hW.mul_incr_fun hlm hlrm (hsmk 1 1) (hbdd 1 1 (by norm_num))
      (g := fun x => x) measurable_id (hW.integrable_incr hlm hlrm)
    obtain ⟨j2, f2⟩ := hW.mul_incr_fun hlm hlrm (hsmk 0 2) (hbdd 0 2 (by norm_num))
      (g := fun x => x ^ 2) (continuous_pow 2).measurable (hW.integrable_incr_pow hlm hlrm 2)
    rw [hW.integral_incr hlm hlrm, mul_zero] at e1 f1
    rw [hW.integral_incr_sq hlm hlrm] at e2 f2
    rw [hW.integral_incr_three hlm hlrm, mul_zero] at e3
    rw [hW.integral_incr_four hlm hlrm] at e4
    have hsucc : ordSum W ξ l r (m + 1) = fun ω => M ω + ξ m ω * (W (r m) ω - W (l m) ω) := by
      funext ω; rw [ordSum_succ]
    -- expansions
    have ex4 : (fun ω => (M ω + ξ m ω * (W (r m) ω - W (l m) ω)) ^ 4) = fun ω =>
        M ω ^ 4 + 4 * (M ω ^ 3 * ξ m ω ^ 1 * (W (r m) ω - W (l m) ω)) + 6 * (M ω ^ 2 * ξ m ω ^ 2 * (W (r m) ω - W (l m) ω) ^ 2) +
          4 * (M ω ^ 1 * ξ m ω ^ 3 * (W (r m) ω - W (l m) ω) ^ 3) + M ω ^ 0 * ξ m ω ^ 4 * (W (r m) ω - W (l m) ω) ^ 4 := by
      funext ω; ring
    have ex2 : (fun ω => (M ω + ξ m ω * (W (r m) ω - W (l m) ω)) ^ 2) = fun ω =>
        M ω ^ 2 + 2 * (M ω ^ 1 * ξ m ω ^ 1 * (W (r m) ω - W (l m) ω)) + M ω ^ 0 * ξ m ω ^ 2 * (W (r m) ω - W (l m) ω) ^ 2 := by
      funext ω; ring
    have A1 : Integrable (fun ω => M ω ^ 4 + 4 * (M ω ^ 3 * ξ m ω ^ 1 *
        (W (r m) ω - W (l m) ω))) P := hM4.add (i1.const_mul 4)
    have A2 : Integrable (fun ω => M ω ^ 4 + 4 * (M ω ^ 3 * ξ m ω ^ 1 *
        (W (r m) ω - W (l m) ω)) + 6 * (M ω ^ 2 * ξ m ω ^ 2 * (W (r m) ω - W (l m) ω) ^ 2)) P :=
      A1.add (i2.const_mul 6)
    have A3 : Integrable (fun ω => M ω ^ 4 + 4 * (M ω ^ 3 * ξ m ω ^ 1 *
        (W (r m) ω - W (l m) ω)) + 6 * (M ω ^ 2 * ξ m ω ^ 2 * (W (r m) ω - W (l m) ω) ^ 2) +
        4 * (M ω ^ 1 * ξ m ω ^ 3 * (W (r m) ω - W (l m) ω) ^ 3)) P :=
      A2.add (i3.const_mul 4)
    have B1 : Integrable (fun ω => M ω ^ 2 + 2 * (M ω ^ 1 * ξ m ω ^ 1 *
        (W (r m) ω - W (l m) ω))) P := (hMpow 2 (by norm_num)).add (j1.const_mul 2)
    have I4 : Integrable (fun ω => (M ω + ξ m ω * (W (r m) ω - W (l m) ω)) ^ 4) P := by
      rw [ex4]; exact A3.add i4
    -- second moment
    have hint2 : ∫ ω, (M ω + ξ m ω * (W (r m) ω - W (l m) ω)) ^ 2 ∂P =
        ∫ ω, M ω ^ 2 ∂P + 2 * 0 + (∫ ω, M ω ^ 0 * ξ m ω ^ 2 ∂P) * d := by
      rw [ex2, integral_add B1 j2, integral_add (hMpow 2 (by norm_num)) (j1.const_mul 2),
        integral_const_mul]
      rw [f1, f2]
    have hEξ2 : ∫ ω, M ω ^ 0 * ξ m ω ^ 2 ∂P ≤ K ^ 2 := by
      have := integral_mono (hbdd 0 2 (by norm_num)) (integrable_const (K ^ 2))
        (fun ω => by simpa using hK2 m ω)
      simpa using this
    have hEM2ξ2 : ∫ ω, M ω ^ 2 * ξ m ω ^ 2 ∂P ≤ K ^ 2 * ∫ ω, M ω ^ 2 ∂P := by
      rw [← integral_const_mul]
      exact integral_mono (hbdd 2 2 (by norm_num)) ((hMpow 2 (by norm_num)).const_mul _)
        fun ω => by
          rw [mul_comm (K ^ 2)]
          exact mul_le_mul_of_nonneg_left (hK2 m ω) (sq_nonneg _)
    have hEξ4 : ∫ ω, M ω ^ 0 * ξ m ω ^ 4 ∂P ≤ K ^ 4 := by
      have := integral_mono (hbdd 0 4 (by norm_num)) (integrable_const (K ^ 4))
        (fun ω => by simpa using hK4 m ω)
      simpa using this
    have hint4 : ∫ ω, (M ω + ξ m ω * (W (r m) ω - W (l m) ω)) ^ 4 ∂P =
        ∫ ω, M ω ^ 4 ∂P + 4 * 0 + 6 * ((∫ ω, M ω ^ 2 * ξ m ω ^ 2 ∂P) * d) + 4 * 0 +
          (∫ ω, M ω ^ 0 * ξ m ω ^ 4 ∂P) * (3 * d ^ 2) := by
      rw [ex4, integral_add A3 i4, integral_add A2 (i3.const_mul 4),
        integral_add A1 (i2.const_mul 6), integral_add hM4 (i1.const_mul 4), integral_const_mul,
        integral_const_mul, integral_const_mul]
      rw [e1, e2, e3, e4]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsucc]
      have h1 : StronglyMeasurable[𝓕 (l (m + 1))] M := hMsm.mono (𝓕.mono (hmono (Nat.le_succ m)))
      have h2 : StronglyMeasurable[𝓕 (l (m + 1))] (ξ m) :=
        (hξ m).mono (𝓕.mono (hmono (Nat.le_succ m)))
      have h3 : StronglyMeasurable[𝓕 (l (m + 1))] (W (r m)) :=
        (hW.adapted _ (hlm.trans hlrm)).mono (𝓕.mono (hrl m))
      have h4 : StronglyMeasurable[𝓕 (l (m + 1))] (W (l m)) :=
        (hW.adapted _ hlm).mono (𝓕.mono (hmono (Nat.le_succ m)))
      exact h1.add (h2.mul (h3.sub h4))
    · rw [hsucc]; exact I4
    · rw [hsucc, hint2, Finset.sum_range_succ]
      have := mul_le_mul_of_nonneg_right hEξ2 hd0
      nlinarith
    · rw [hsucc, hint4, Finset.sum_range_succ]
      have a1 := mul_le_mul_of_nonneg_right hEM2ξ2 hd0
      have a2 := mul_le_mul_of_nonneg_right hEξ4 (by positivity : (0 : ℝ) ≤ 3 * d ^ 2)
      have a3 := mul_le_mul_of_nonneg_left hM2 (by positivity : (0 : ℝ) ≤ K ^ 2 * d)
      have hS' : K ^ 2 * S = K ^ 2 * ∑ j ∈ Finset.range m, (r j - l j) := rfl
      nlinarith

end Gardiner.Ito

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **Fourth moment of the Itô integral of a bounded integrand supported in `(a, b]`**:
`E[(∫₀ᵀ G dW)⁴] ≤ 3 (K² (b - a))²` if `|G| ≤ K` and `G = 0` outside `(a, b]`. -/
theorem itoInt_fourth_le {T K a b : ℝ} (hT : 0 < T) {G : ℝ → Ω → ℝ}
    (hG : IsItoIntegrand 𝓕 P T G) (hK0 : 0 ≤ K) (hK : ∀ u ω, |G u ω| ≤ K)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (hGv : ∀ u ω, u ∉ Set.Ioc a b → G u ω = 0) :
    Integrable (fun ω => itoInt W 𝓕 P T G ω ^ 4) P ∧
      ∫ ω, itoInt W 𝓕 P T G ω ^ 4 ∂P ≤ 3 * (K ^ 2 * (b - a)) ^ 2 := by
  have := hW.isProbabilityMeasure
  choose hk ck hhk hck hdist using fun k : ℕ =>
    exists_shiftElem_approx hG hK0 hK hT (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  set L : ℕ → ℕ → ℝ := fun k j => min (ck k + j * hk k) T with hLdef
  set R : ℕ → ℕ → ℝ := fun k j => min (ck k + (j + 1) * hk k) T with hRdef
  set X : ℕ → ℕ → Ω → ℝ := fun k j => extIcc T G (ck k + j * hk k) with hXdef
  set Lc : ℕ → ℕ → ℝ := fun k j => clampI a b (L k j) with hLcdef
  set Rc : ℕ → ℕ → ℝ := fun k j => clampI a b (R k j) with hRcdef
  set Xc : ℕ → ℕ → Ω → ℝ := fun k j => if L k j ≤ b then X k j else fun _ => 0 with hXcdef
  have hRL : ∀ k j, R k j = L k (j + 1) := by
    intro k j; simp only [hRdef, hLdef]; push_cast; ring_nf
  have hLc0 : ∀ k j, 0 ≤ Lc k j := fun k j => ha.trans (le_clampI _ _ _)
  have hLR : ∀ k j, L k j ≤ R k j := fun k j =>
    min_le_min_right _ (by nlinarith [hhk k])
  have hLRc : ∀ k j, Lc k j ≤ Rc k j := fun k j => clampI_mono a b (hLR k j)
  have hRLc : ∀ k j, Rc k j ≤ Lc k (j + 1) := fun k j => by
    simp only [hRcdef, hLcdef, hRL]; exact le_rfl
  have hXsm : ∀ k j, StronglyMeasurable[𝓕 (L k j)] (X k j) := by
    intro k j
    by_cases hj : ck k + j * hk k ≤ T
    · simp only [hLdef, hXdef, min_eq_left hj]; exact extIcc_adapted hG _
    · have : X k j = fun _ => 0 := funext fun ω => extIcc_of_notMem (fun hm => hj hm.2) ω
      rw [this]; exact stronglyMeasurable_const
  have hXcsm : ∀ k j, StronglyMeasurable[𝓕 (Lc k j)] (Xc k j) := by
    intro k j
    by_cases hj : L k j ≤ b
    · simp only [hXcdef, if_pos hj]
      refine (hXsm k j).mono (𝓕.mono ?_)
      simp only [hLcdef, clampI, min_eq_left hj]; exact le_max_right _ _
    · simp only [hXcdef, if_neg hj]; exact stronglyMeasurable_const
  have hXb : ∀ k j ω, |X k j ω| ≤ K := fun k j ω => abs_extIcc_le hK0 hK _ ω
  have hXcb : ∀ k j ω, |Xc k j ω| ≤ K := by
    intro k j ω
    by_cases hj : L k j ≤ b
    · simp only [hXcdef, if_pos hj]; exact hXb k j ω
    · simp only [hXcdef, if_neg hj, abs_zero]; exact hK0
  have hXc2 : ∀ k j, MemLp (Xc k j) 2 P := fun k j =>
    MemLp.of_bound ((hXcsm k j).mono (𝓕.le _)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hXcb k j ω)
  set N : ℕ → ℕ := fun k => ⌈T / hk k⌉₊ + 1 with hNdef
  set E := fun k => ElemIntegrand.ofSeq (P := P) (N k) (Lc k) (Rc k) (Xc k) (hLc0 k) (hLRc k)
    (hXcsm k) (hXc2 k) with hEdef
  have hEs : ∀ k, (E k).SupportedIn T := fun k j => (clampI_le hab _).trans hbT
  have hEproc : ∀ k u ω, (E k).process u ω =
      cellInd a b u * (shiftElem hG hK0 hK hT (hhk k) (hck k)).process u ω := by
    intro k u ω
    rw [hEdef, ElemIntegrand.process_ofSeq]
    simp only [ElemIntegrand.process, shiftElem]
    rw [Fin.sum_univ_eq_sum_range (fun j => extIcc T G (ck k + j * hk k) ω *
      cellInd (min (ck k + j * hk k) T) (min (ck k + (j + 1) * hk k) T) u), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : L k j ≤ b
    · simp only [hXcdef, if_pos hj, hLcdef, hRcdef]
      rw [cellInd_clampI hj]; simp only [hXdef, hLdef, hRdef]; ring
    · simp only [hXcdef, if_neg hj, zero_mul]
      by_cases hu : u ∈ Set.Ioc (L k j) (R k j)
      · rw [cellInd_notMem (show u ∉ Set.Ioc a b from fun h =>
          hj (hu.1.trans_le h.2).le)]; ring
      · rw [show cellInd (min (ck k + j * hk k) T) (min (ck k + (j + 1) * hk k) T) u = 0 from
          cellInd_notMem hu]; ring
  have hGeq : ∀ u ω, G u ω = cellInd a b u * G u ω := fun u ω => by
    by_cases hu : u ∈ Set.Ioc a b
    · rw [cellInd_mem hu, one_mul]
    · rw [hGv u ω hu, mul_zero]
  have hdistE : ∀ k, ∫ p, (Function.uncurry (E k).process p - Function.uncurry G p) ^ 2
      ∂(tsMeasure P T) < 1 / ((k : ℝ) + 1) := by
    intro k
    refine lt_of_le_of_lt ?_ (hdist k)
    refine integral_mono (((E k).memLp_process T).sub hG.memLp).integrable_sq
      (((shiftElem hG hK0 hK hT (hhk k) (hck k)).memLp_process T).sub hG.memLp).integrable_sq
      fun p => ?_
    simp only [Function.uncurry]
    rw [hEproc, hGeq p.1 p.2]
    have h1 := cellInd_nonneg a b p.1
    have h2 := cellInd_le_one a b p.1
    have e : (cellInd a b p.1 * (shiftElem hG hK0 hK hT (hhk k) (hck k)).process p.1 p.2 -
        cellInd a b p.1 * G p.1 p.2) ^ 2 = cellInd a b p.1 ^ 2 *
        ((shiftElem hG hK0 hK hT (hhk k) (hck k)).process p.1 p.2 - G p.1 p.2) ^ 2 := by ring
    have e2 : cellInd a b p.1 * G p.1 p.2 = G p.1 p.2 := (hGeq p.1 p.2).symm
    rw [e, e2]
    have : cellInd a b p.1 ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ((shiftElem hG hK0 hK hT (hhk k) (hck k)).process p.1 p.2 - G p.1 p.2)]
  have hconv := itoInt_tendsto hW hG E hEs
    (tendsto_of_lt_one_div (fun k => integral_nonneg fun _ => sq_nonneg _) hdistE)
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto_zero
    (Z := fun k ω => ((E k).integral W ω - itoInt W 𝓕 P T G ω) ^ 2)
    (fun k => (((E k).memLp_integral hW).sub (memLp_itoInt hW hG)).integrable_sq)
    (fun _ _ => sq_nonneg _) hconv
  have hIm : Measurable (itoInt W 𝓕 P T G) :=
    ((itoInt_stronglyMeasurable hW hG).mono (𝓕.le T)).measurable
  have hfour := fun k => hW.ordSum_fourth (hLc0 k 0) (hLRc k) (hRLc k) (hXcsm k) (hXcb k) (N k)
  refine integrable_of_ae_tendsto_of_integral_le
    (f := fun k ω => ordSum W (Xc (ns k)) (Lc (ns k)) (Rc (ns k)) (N (ns k)) ω ^ 4)
    (fun _ _ => by positivity) (fun k => (hfour (ns k)).2.1)
    (hIm.pow_const 4).aestronglyMeasurable ?_ (fun k => ?_)
  · filter_upwards [hae] with ω hω
    have h1 : Tendsto (fun k => (E (ns k)).integral W ω - itoInt W 𝓕 P T G ω) atTop (𝓝 0) :=
      tendsto_zero_of_sq_le (fun k => le_rfl) hω
    have h2 : Tendsto (fun k => (E (ns k)).integral W ω) atTop (𝓝 (itoInt W 𝓕 P T G ω)) := by
      simpa using h1.add_const (itoInt W 𝓕 P T G ω)
    have h3 := h2.pow 4
    refine h3.congr fun k => ?_
    simp only [hEdef, ElemIntegrand.integral_ofSeq]
  · refine (hfour (ns k)).2.2.2.trans ?_
    have hsum : ∑ j ∈ Finset.range (N (ns k)), (Rc (ns k) j - Lc (ns k) j) ≤ b - a := by
      calc ∑ j ∈ Finset.range (N (ns k)), (Rc (ns k) j - Lc (ns k) j)
          ≤ ∑ j ∈ Finset.range (N (ns k)), (Lc (ns k) (j + 1) - Lc (ns k) j) :=
            Finset.sum_le_sum fun j _ => by linarith [hRLc (ns k) j]
        _ = Lc (ns k) (N (ns k)) - Lc (ns k) 0 := Finset.sum_range_sub _ _
        _ ≤ b - a := by
            have := clampI_le hab (L (ns k) (N (ns k)))
            have := le_clampI a b (L (ns k) 0)
            simp only [hLcdef]; linarith
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range (N (ns k)), (Rc (ns k) j - Lc (ns k) j) :=
      Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hLRc _ j)
    have : K ^ 2 * ∑ j ∈ Finset.range (N (ns k)), (Rc (ns k) j - Lc (ns k) j) ≤ K ^ 2 * (b - a) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg K)
    have h0 : 0 ≤ K ^ 2 * ∑ j ∈ Finset.range (N (ns k)), (Rc (ns k) j - Lc (ns k) j) :=
      mul_nonneg (sq_nonneg K) hsum0
    nlinarith

end Gardiner.Ito
