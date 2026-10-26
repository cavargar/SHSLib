/-
# Quadratic variation of a general Itô integral

Let `b` be a bounded Itô integrand on `[0, T]`, `I(t) = ∫₀ᵗ b dW`, and `tᵢ` the uniform partition of
`[0, T]` into `n + 1` cells.  For bounded `𝓕 tᵢ`-measurable weights `Zᵢ`,

`E[(Σᵢ Zᵢ ((I(tᵢ₊₁) - I(tᵢ))² - ∫_{tᵢ}^{tᵢ₊₁} b² du))²] ≤ 8 C² B⁴ T² / (n + 1)`

(`Gardiner.Ito.qv_weighted_sq_le`), so the weighted quadratic variation of `I` is `∫ Z b² du` in
the limit.  This generalises `Gardiner.Ito.IsFWiener.integral_wqv_sq` (the case `b = 1`).  The
proof uses the conditional isometry (`Gardiner.Ito.setIntegral_itoInt_incr_sq`), which makes the
centred squared increments orthogonal, and the fourth-moment bound
(`Gardiner.Ito.itoInt_fourth_le`) for the diagonal.

We also show that `Σᵢ g(tᵢ) (I(tᵢ₊₁) - I(tᵢ)) → ∫₀ᵀ g b dW` in mean square for bounded, adapted `g`
with continuous paths (`Gardiner.Ito.sum_mul_incr_tendsto`).
-/
import SHSLib.Gardiner.Ito.Calculus.FourthMoment

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- `∫ₛᵗ b(u)² du` along a path. -/
def sqInt (b : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ := ∫ u in Set.Ioc s t, b u ω ^ 2

/-- The increment `∫₀ᵗ b dW - ∫₀ˢ b dW` of the running Itô integral. -/
def itoIncr (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (b : ℝ → Ω → ℝ) (s t : ℝ)
    (ω : Ω) : ℝ :=
  itoInt W 𝓕 P t b ω - itoInt W 𝓕 P s b ω

lemma measurable_sqInt {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b)) (s t : ℝ) :
    Measurable (sqInt b s t) := by
  have hf : StronglyMeasurable (fun p : Ω × ℝ => b p.2 p.1 ^ 2) :=
    ((hb.comp (measurable_snd.prodMk measurable_fst)).pow_const 2).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := volume.restrict (Set.Ioc s t))).measurable

omit mΩ in
lemma sqInt_nonneg (b : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : 0 ≤ sqInt b s t ω :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _

omit mΩ in
lemma sqInt_le {b : ℝ → Ω → ℝ} {T B s t : ℝ} (hB : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ ω, |b u ω| ≤ B)
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (ω : Ω) : sqInt b s t ω ≤ B ^ 2 * (t - s) := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc s t)
    (f := fun u => b u ω ^ 2) (C := B ^ 2) measure_Ioc_lt_top (fun u hu => by
      have h1 := hB u ⟨hs.trans hu.1.le, hu.2.trans htT⟩ ω
      have h2 : b u ω ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h2)
  have hvol : volume.real (Set.Ioc s t) = t - s := by
    simp [measureReal_def, Real.volume_Ioc, hst]
  rw [hvol, Real.norm_eq_abs] at h
  exact (le_abs_self (sqInt b s t ω)).trans h

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

section Bounded

variable {T B : ℝ} {b : ℝ → Ω → ℝ} (hb : IsItoIntegrand 𝓕 P T b) (hB0 : 0 ≤ B)
  (hB : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ ω, |b u ω| ≤ B)
include hb hB0 hB

omit hB0 hB in
lemma memLp_itoIncr {s t : ℝ} (hst : s ≤ t) (htT : t ≤ T) :
    MemLp (itoIncr W 𝓕 P b s t) 2 P := by
  have := hW.isProbabilityMeasure
  exact (memLp_itoInt hW (hb.mono htT)).sub (memLp_itoInt hW (hb.mono (hst.trans htT)))

/-- Fourth moment of an increment of the running Itô integral. -/
theorem itoIncr_fourth (hT : 0 < T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Integrable (fun ω => itoIncr W 𝓕 P b s t ω ^ 4) P ∧
      ∫ ω, itoIncr W 𝓕 P b s t ω ^ 4 ∂P ≤ 3 * (B ^ 2 * (t - s)) ^ 2 := by
  have hG := isItoIntegrand_det_mul hb (measurable_cellInd s t) (abs_cellInd_le s t)
  have hGb : ∀ u ω, |cellInd s t u * b u ω| ≤ B := fun u ω => by
    by_cases hu : u ∈ Set.Ioc s t
    · rw [cellInd_mem hu, one_mul]; exact hB u ⟨hs.trans hu.1.le, hu.2.trans htT⟩ ω
    · rw [cellInd_notMem hu, zero_mul, abs_zero]; exact hB0
  have hGv : ∀ u ω, u ∉ Set.Ioc s t → cellInd s t u * b u ω = 0 := fun u ω hu => by
    rw [cellInd_notMem hu, zero_mul]
  obtain ⟨h1, h2⟩ := itoInt_fourth_le hW hT hG hB0 hGb hs hst htT hGv
  have hae := itoInt_cellInd hW hs hst htT hb
  have hae4 : (fun ω => itoInt W 𝓕 P T (fun u ω => cellInd s t u * b u ω) ω ^ 4) =ᵐ[P]
      fun ω => itoIncr W 𝓕 P b s t ω ^ 4 := by
    filter_upwards [hae] with ω hω
    rw [hω]; rfl
  exact ⟨h1.congr hae4, by rwa [← integral_congr_ae hae4]⟩

/-- The centred squared increment `(I(t) - I(s))² - ∫ₛᵗ b²` is square integrable. -/
lemma memLp_itoIncr_sq_sub (hT : 0 < T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    MemLp (fun ω => itoIncr W 𝓕 P b s t ω ^ 2 - sqInt b s t ω) 2 P := by
  have := hW.isProbabilityMeasure
  obtain ⟨h4, -⟩ := itoIncr_fourth hW hb hB0 hB hT hs hst htT
  have hIm : AEStronglyMeasurable (itoIncr W 𝓕 P b s t) P :=
    (memLp_itoIncr hW hb hst htT).aestronglyMeasurable
  have h2 : MemLp (fun ω => itoIncr W 𝓕 P b s t ω ^ 2) 2 P := by
    refine (memLp_two_iff_integrable_sq (hIm.pow 2)).mpr ?_
    refine h4.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.pow_apply]; ring
  have h3 : MemLp (sqInt b s t) 2 P :=
    MemLp.of_bound (measurable_sqInt hb.measurable _ _).aestronglyMeasurable
      (B ^ 2 * (t - s)) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sqInt_nonneg b _ _ ω)]
        exact sqInt_le hB hs hst htT ω)
  exact h2.sub h3

omit hB0 in
/-- `E[(I(t) - I(s))² - ∫ₛᵗ b² | 𝓕 s] = 0`. -/
theorem condExp_itoIncr_sq_sub {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    P[fun ω => itoIncr W 𝓕 P b s t ω ^ 2 - sqInt b s t ω | 𝓕 s] =ᵐ[P] 0 := by
  have := hW.isProbabilityMeasure
  have hI := (memLp_itoIncr hW hb hst htT).integrable_sq
  have hβm := measurable_sqInt hb.measurable s t
  have hβi : Integrable (sqInt b s t) P :=
    Integrable.of_bound hβm.aestronglyMeasurable (B ^ 2 * (t - s))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sqInt_nonneg b s t ω)]
        exact sqInt_le hB hs hst htT ω)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hI.sub hβi)
    (fun _ _ _ => integrableOn_zero) (fun A hA _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  show _ = ∫ ω in A, (itoIncr W 𝓕 P b s t ω ^ 2 - sqInt b s t ω) ∂P
  rw [integral_sub hI.integrableOn hβi.integrableOn]
  have := setIntegral_itoInt_incr_sq hW hs hst htT hb hA
  simp only [integral_zero]
  unfold itoIncr sqInt
  rw [this, sub_self]

/-- **Weighted quadratic variation of the Itô integral**, quantitative form. -/
theorem qv_weighted_sq_le (hT : 0 < T) {C : ℝ} (n : ℕ) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ≤ n, StronglyMeasurable[𝓕 (gridPt T n i)] (Z i)) (hZb : ∀ i ≤ n, ∀ ω, |Z i ω| ≤ C)
    (hβ : ∀ i ≤ n, AEStronglyMeasurable[𝓕 (gridPt T n (i + 1))]
      (sqInt b (gridPt T n i) (gridPt T n (i + 1))) P) :
    ∫ ω, (∑ i ∈ Finset.range (n + 1), Z i ω * (itoIncr W 𝓕 P b (gridPt T n i)
      (gridPt T n (i + 1)) ω ^ 2 - sqInt b (gridPt T n i) (gridPt T n (i + 1)) ω)) ^ 2 ∂P ≤
      8 * C ^ 2 * B ^ 4 * T ^ 2 / (n + 1) := by
  have := hW.isProbabilityMeasure
  set t : ℕ → ℝ := fun i => gridPt T n i with ht
  set h := T / ((n : ℝ) + 1) with hh
  have hh0 : 0 ≤ h := by positivity
  have ht0 : ∀ i, 0 ≤ t i := fun i => gridPt_nonneg hT.le n i
  have htT : ∀ i ≤ n, t (i + 1) ≤ T := fun i hi => gridPt_le hT.le (by omega)
  have htsucc : ∀ i, t (i + 1) = t i + h := fun i => gridPt_succ T n i
  have htle : ∀ i, t i ≤ t (i + 1) := fun i => by rw [htsucc]; linarith
  have htmono : ∀ i j, i ≤ j → t i ≤ t j := fun i j hij => gridPt_mono hT.le n hij
  set D : ℕ → Ω → ℝ := fun i ω => itoIncr W 𝓕 P b (t i) (t (i + 1)) ω ^ 2 -
    sqInt b (t i) (t (i + 1)) ω with hD
  -- properties of the centred squared increments
  have hDm : ∀ i ≤ n, MemLp (D i) 2 P := by
    intro i hi
    obtain ⟨h4, -⟩ := itoIncr_fourth hW hb hB0 hB hT (ht0 i) (htle i) (htT i hi)
    have hIm : AEStronglyMeasurable (itoIncr W 𝓕 P b (t i) (t (i + 1))) P :=
      (memLp_itoIncr hW hb (htle i) (htT i hi)).aestronglyMeasurable
    have h2 : MemLp (fun ω => itoIncr W 𝓕 P b (t i) (t (i + 1)) ω ^ 2) 2 P := by
      refine (memLp_two_iff_integrable_sq (hIm.pow 2)).mpr ?_
      refine h4.congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.pow_apply]; ring
    have h3 : MemLp (sqInt b (t i) (t (i + 1))) 2 P :=
      MemLp.of_bound (measurable_sqInt hb.measurable _ _).aestronglyMeasurable
        (B ^ 2 * (t (i + 1) - t i)) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sqInt_nonneg b _ _ ω)]
          exact sqInt_le hB (ht0 i) (htle i) (htT i hi) ω)
    exact h2.sub h3
  have hDsq : ∀ i ≤ n, ∫ ω, D i ω ^ 2 ∂P ≤ 8 * B ^ 4 * h ^ 2 := by
    intro i hi
    obtain ⟨h4, h4le⟩ := itoIncr_fourth hW hb hB0 hB hT (ht0 i) (htle i) (htT i hi)
    have hd : t (i + 1) - t i = h := by rw [htsucc i]; ring
    have hβb : ∀ ω, sqInt b (t i) (t (i + 1)) ω ^ 2 ≤ (B ^ 2 * h) ^ 2 := fun ω => by
      have h1 := sqInt_le hB (ht0 i) (htle i) (htT i hi) ω
      rw [hd] at h1
      exact pow_le_pow_left₀ (sqInt_nonneg b _ _ ω) h1 2
    have hint : Integrable (fun ω => 2 * itoIncr W 𝓕 P b (t i) (t (i + 1)) ω ^ 4 +
        2 * (B ^ 2 * h) ^ 2) P := (h4.const_mul 2).add (integrable_const _)
    calc ∫ ω, D i ω ^ 2 ∂P ≤ ∫ ω, (2 * itoIncr W 𝓕 P b (t i) (t (i + 1)) ω ^ 4 +
          2 * (B ^ 2 * h) ^ 2) ∂P := by
          refine integral_mono (hDm i hi).integrable_sq hint fun ω => ?_
          have := hβb ω
          simp only [hD]
          nlinarith [sq_nonneg (itoIncr W 𝓕 P b (t i) (t (i + 1)) ω ^ 2 +
            sqInt b (t i) (t (i + 1)) ω)]
      _ = 2 * ∫ ω, itoIncr W 𝓕 P b (t i) (t (i + 1)) ω ^ 4 ∂P + 2 * (B ^ 2 * h) ^ 2 := by
          rw [integral_add (h4.const_mul 2) (integrable_const _), integral_const_mul,
            integral_const]
          simp
      _ ≤ 8 * B ^ 4 * h ^ 2 := by
          rw [hd] at h4le
          nlinarith
  -- the summands
  set Y : ℕ → Ω → ℝ := fun i ω => if i ≤ n then Z i ω * D i ω else 0 with hY
  have hZm : ∀ i ≤ n, Measurable (Z i) := fun i hi => ((hZ i hi).mono (𝓕.le _)).measurable
  have hYm : ∀ i, MemLp (Y i) 2 P := by
    intro i
    by_cases hi : i ≤ n
    · simp only [hY, if_pos hi]
      exact memLp_mul_of_bdd (hZm i hi).aestronglyMeasurable (hZb i hi) (hDm i hi)
    · simp only [hY, if_neg hi]; exact MemLp.zero
  -- `D i` is a.e. `𝓕 tᵢ₊₁`-measurable
  have hDae : ∀ i ≤ n, AEStronglyMeasurable[𝓕 (t (i + 1))] (D i) P := by
    intro i hi
    have h1 : StronglyMeasurable[𝓕 (t (i + 1))] (itoIncr W 𝓕 P b (t i) (t (i + 1))) :=
      (itoInt_stronglyMeasurable hW (hb.mono (htT i hi))).sub
        ((itoInt_stronglyMeasurable hW (hb.mono ((htle i).trans (htT i hi)))).mono
          (𝓕.mono (htle i)))
    exact (h1.pow 2).aestronglyMeasurable.sub (hβ i hi)
  have hcond : ∀ j ≤ n, P[D j | 𝓕 (t j)] =ᵐ[P] 0 := fun j hj =>
    condExp_itoIncr_sq_sub hW hb hB (ht0 j) (htle j) (htT j hj)
  have horth : ∀ i j, i < j → ∫ ω, Y i ω * Y j ω ∂P = 0 := by
    intro i j hij
    by_cases hj : j ≤ n
    · have hi : i ≤ n := by omega
      simp only [hY, if_pos hi, if_pos hj]
      set V : Ω → ℝ := fun ω => Z i ω * D i ω * Z j ω with hV
      have hVm : MemLp V 2 P := by
        have := memLp_mul_of_bdd (hZm i hi).aestronglyMeasurable (hZb i hi) (hDm i hi)
        have e : V = fun ω => Z j ω * (Z i ω * D i ω) := by funext ω; simp only [hV]; ring
        rw [e]
        exact memLp_mul_of_bdd (hZm j hj).aestronglyMeasurable (hZb j hj) this
      have hVae : AEStronglyMeasurable[𝓕 (t j)] V P := by
        have hle : t (i + 1) ≤ t j := htmono _ _ (by omega)
        exact (((hZ i hi).mono (𝓕.mono (htmono i j hij.le))).aestronglyMeasurable.mul
          ((hDae i hi).mono (𝓕.mono hle))).mul (hZ j hj).aestronglyMeasurable
      have hint : Integrable (V * D j) P := hVm.integrable_mul (hDm j hj)
      have e : (fun ω => Z i ω * D i ω * (Z j ω * D j ω)) = V * D j := by
        funext ω; simp only [hV, Pi.mul_apply]; ring
      rw [e, ← integral_condExp (𝓕.le (t j))]
      have h1 := condExp_mul_of_aestronglyMeasurable_left hVae hint
        ((hDm j hj).integrable one_le_two)
      rw [integral_congr_ae h1]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hcond j hj] with ω hω
      simp [hω]
    · simp [hY, if_neg hj]
  have hsum : (fun ω => ∑ i ∈ Finset.range (n + 1), Z i ω * (itoIncr W 𝓕 P b (gridPt T n i)
      (gridPt T n (i + 1)) ω ^ 2 - sqInt b (gridPt T n i) (gridPt T n (i + 1)) ω)) =
      fun ω => ∑ i ∈ Finset.range (n + 1), Y i ω := by
    funext ω
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ≤ n := by simp at hi; omega
    simp only [hY, if_pos this]
    rfl
  have hsum' : ∫ ω, (∑ i ∈ Finset.range (n + 1), Z i ω * (itoIncr W 𝓕 P b (gridPt T n i)
      (gridPt T n (i + 1)) ω ^ 2 - sqInt b (gridPt T n i) (gridPt T n (i + 1)) ω)) ^ 2 ∂P =
      ∫ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 ∂P := by
    congr 1; funext ω; rw [congrFun hsum ω]
  rw [hsum', integral_sq_sum_of_orth (n + 1) hYm horth]
  calc ∑ i ∈ Finset.range (n + 1), ∫ ω, Y i ω ^ 2 ∂P
      ≤ ∑ i ∈ Finset.range (n + 1), C ^ 2 * (8 * B ^ 4 * h ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := by simp at hi; omega
        simp only [hY, if_pos hi']
        refine (integral_mul_sq_le (hZb i hi') (hDm i hi')).trans ?_
        exact mul_le_mul_of_nonneg_left (hDsq i hi') (sq_nonneg C)
    _ = 8 * C ^ 2 * B ^ 4 * T ^ 2 / (n + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh]
        push_cast
        field_simp

end Bounded


omit hW in
/-- A bounded, jointly measurable, adapted multiplier preserves Itô integrands. -/
lemma isItoIntegrand_mul_bdd {T C : ℝ} {g b : ℝ → Ω → ℝ} (hb : IsItoIntegrand 𝓕 P T b)
    (hgm : Measurable (Function.uncurry g))
    (hgad : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (g t)) (hgb : ∀ t ω, |g t ω| ≤ C) :
    IsItoIntegrand 𝓕 P T (fun u ω => g u ω * b u ω) :=
  ⟨hgm.mul hb.measurable, fun t ht htT => (hgad t ht htT).mul (hb.adapted t ht htT),
    memLp_mul_of_bdd hgm.aestronglyMeasurable (fun p => hgb p.1 p.2) hb.memLp⟩

omit hW in
/-- `Z 1_{(s,t]} b` is an Itô integrand for bounded `𝓕 s`-measurable `Z`. -/
lemma isItoIntegrand_mul_cellInd {T s t C : ℝ} {b : ℝ → Ω → ℝ} (hb : IsItoIntegrand 𝓕 P T b)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 s] Z) (hZb : ∀ ω, |Z ω| ≤ C) :
    IsItoIntegrand 𝓕 P T (fun u ω => Z ω * (cellInd s t u * b u ω)) := by
  have hcG := isItoIntegrand_det_mul hb (measurable_cellInd s t) (abs_cellInd_le s t)
  have hZm : Measurable Z := (hZ.mono (𝓕.le s)).measurable
  refine ⟨(hZm.comp measurable_snd).mul hcG.measurable, fun u hu huT => ?_, ?_⟩
  · by_cases hus : u ≤ s
    · have : (fun ω => Z ω * (cellInd s t u * b u ω)) = fun _ => 0 := funext fun ω => by
        rw [cellInd_notMem (fun h => absurd h.1 (not_lt.mpr hus))]; ring
      rw [this]; exact stronglyMeasurable_const
    · exact (hZ.mono (𝓕.mono (not_le.mp hus).le)).mul (hcG.adapted u hu huT)
  · exact memLp_mul_of_bdd (Z := fun p : ℝ × Ω => Z p.2)
      (hZm.comp measurable_snd).aestronglyMeasurable (fun p => hZb p.2) hcG.memLp

omit hW in
lemma isItoIntegrand_finset_sum {T : ℝ} {ι : Type*} (s : Finset ι) (Gs : ι → ℝ → Ω → ℝ)
    (h : ∀ i ∈ s, IsItoIntegrand 𝓕 P T (Gs i)) :
    IsItoIntegrand 𝓕 P T (fun u ω => ∑ i ∈ s, Gs i u ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨measurable_const, fun _ _ _ => stronglyMeasurable_const, MemLp.zero'⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Linearity over finite sums.** -/
theorem itoInt_finset_sum {T : ℝ} {ι : Type*} (s : Finset ι) (Gs : ι → ℝ → Ω → ℝ)
    (h : ∀ i ∈ s, IsItoIntegrand 𝓕 P T (Gs i)) :
    itoInt W 𝓕 P T (fun u ω => ∑ i ∈ s, Gs i u ω) =ᵐ[P]
      fun ω => ∑ i ∈ s, itoInt W 𝓕 P T (Gs i) ω := by
  have := hW.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : IsItoIntegrand 𝓕 P T (fun _ _ => (0 : ℝ)) :=
      ⟨measurable_const, fun _ _ _ => stronglyMeasurable_const, MemLp.zero'⟩
    have hsq := itoInt_sq hW h0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero] at hsq
    exact ae_eq_zero_of_integral_sq (memLp_itoInt hW h0) hsq
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsItoIntegrand 𝓕 P T (Gs i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    filter_upwards [itoInt_add hW (h a (Finset.mem_insert_self a s))
      (isItoIntegrand_finset_sum s Gs hs), ih hs] with ω h1 h2
    rw [h1, h2]

/-- **Riemann sums against the increments of an Itô integral**: for a bounded, adapted `g` with
continuous paths, `Σᵢ g(tᵢ) (∫₀^{tᵢ₊₁} b dW - ∫₀^{tᵢ} b dW) → ∫₀ᵀ g b dW` in mean square. -/
theorem sum_mul_incr_tendsto {T C : ℝ} (hT : 0 < T) {b g : ℝ → Ω → ℝ}
    (hb : IsItoIntegrand 𝓕 P T b) (hgm : Measurable (Function.uncurry g))
    (hgad : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (g t)) (hgb : ∀ t ω, |g t ω| ≤ C)
    (hgc : ∀ᵐ ω ∂P, Continuous fun t => g t ω) :
    Tendsto (fun n : ℕ => ∫ ω, (∑ i ∈ Finset.range (n + 1), g (gridPt T n i) ω *
      itoIncr W 𝓕 P b (gridPt T n i) (gridPt T n (i + 1)) ω -
      itoInt W 𝓕 P T (fun u ω => g u ω * b u ω) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  have hne : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at h1
    exact zero_ne_one h1
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgb 0 (Classical.arbitrary _))
  have hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (g t) 2 P := fun t _ _ =>
    MemLp.of_bound (hgm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb t ω)
  set R := fun n => riemElem (P := P) hT.le hgad hL2 n with hR
  have hRb : ∀ n u ω, |(R n).process u ω| ≤ C := by
    intro n u ω
    by_cases hu0 : u ≤ 0
    · rw [(R n).process_eq_zero_of_le hu0, abs_zero]; exact hC0
    by_cases huT : T < u
    · rw [(R n).process_eq_zero_of_ge (riemElem_supportedIn hT.le hgad hL2 n) huT, abs_zero]
      exact hC0
    · rw [riemElem_process hgad hL2 hT n ⟨not_le.mp hu0, not_lt.mp huT⟩ ω]; exact hgb _ ω
  set H : ℕ → ℝ → Ω → ℝ := fun n u ω => (R n).process u ω * b u ω with hH
  have hHi : ∀ n, IsItoIntegrand 𝓕 P T (H n) := fun n =>
    isItoIntegrand_mul_bdd hb (R n).measurable_process
      (fun t _ _ => (R n).process_adapted t) (hRb n)
  have hgbi := isItoIntegrand_mul_bdd hb hgm hgad hgb
  -- Step 1: the Riemann sum is the Itô integral of `H n`
  have step1 : ∀ n, (fun ω => ∑ i ∈ Finset.range (n + 1), g (gridPt T n i) ω *
      itoIncr W 𝓕 P b (gridPt T n i) (gridPt T n (i + 1)) ω) =ᵐ[P] itoInt W 𝓕 P T (H n) := by
    intro n
    set Gs : Fin (n + 1) → ℝ → Ω → ℝ := fun i u ω => g (gridPt T n i) ω *
      (cellInd (gridPt T n i) (gridPt T n (i + 1)) u * b u ω) with hGs
    have hGsi : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), IsItoIntegrand 𝓕 P T (Gs i) :=
      fun i _ => isItoIntegrand_mul_cellInd hb
        (hgad _ (gridPt_nonneg hT.le n i) (gridPt_le hT.le (by omega))) (hgb _)
    have eH : H n = fun u ω => ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), Gs i u ω := by
      funext u ω
      simp only [hH, hR, hGs, ElemIntegrand.process, riemElem, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hloc : ∀ i : Fin (n + 1), itoInt W 𝓕 P T (Gs i) =ᵐ[P] fun ω => g (gridPt T n i) ω *
        itoIncr W 𝓕 P b (gridPt T n i) (gridPt T n (i + 1)) ω := fun i =>
      itoInt_mul_cellInd hW (gridPt_nonneg hT.le n i) (gridPt_mono hT.le n (Nat.le_succ _))
        (gridPt_le hT.le (by omega)) hb
        (hgad _ (gridPt_nonneg hT.le n i) (gridPt_le hT.le (by omega))) (hgb _)
    rw [eH]
    filter_upwards [itoInt_finset_sum hW Finset.univ Gs hGsi, ae_all_iff.mpr hloc] with ω h1 h2
    rw [h1]
    simp_rw [h2]
    exact (Fin.sum_univ_eq_sum_range (fun i => g (gridPt T n i) ω *
      itoIncr W 𝓕 P b (gridPt T n i) (gridPt T n (i + 1)) ω) (n + 1)).symm
  -- Step 2: isometry and dominated convergence
  have step2 : ∀ n, ∫ ω, (itoInt W 𝓕 P T (H n) ω -
      itoInt W 𝓕 P T (fun u ω => g u ω * b u ω) ω) ^ 2 ∂P =
      ∫ p, (Function.uncurry (H n) p - Function.uncurry (fun u ω => g u ω * b u ω) p) ^ 2
        ∂(tsMeasure P T) := by
    intro n
    have hd := (hHi n).sub hgbi
    rw [show (∫ p, (Function.uncurry (H n) p - Function.uncurry (fun u ω => g u ω * b u ω) p) ^ 2
      ∂(tsMeasure P T)) = ∫ p, Function.uncurry (fun t ω => H n t ω - g t ω * b t ω) p ^ 2
      ∂(tsMeasure P T) from rfl, integral_sq_tsMeasure hd.memLp, ← itoInt_sq hW hd]
    refine integral_congr_ae ?_
    filter_upwards [itoInt_sub hW (hHi n) hgbi] with ω hω
    rw [hω]
  have hconv : Tendsto (fun n => ∫ p, (Function.uncurry (H n) p -
      Function.uncurry (fun u ω => g u ω * b u ω) p) ^ 2 ∂(tsMeasure P T)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := tsMeasure P T)
      (F := fun n p => (Function.uncurry (H n) p -
        Function.uncurry (fun u ω => g u ω * b u ω) p) ^ 2) (f := fun _ => 0)
      (fun p => (2 * C) ^ 2 * Function.uncurry b p ^ 2)
      (fun n => (((hHi n).measurable.sub hgbi.measurable).pow_const 2).aestronglyMeasurable)
      (hb.memLp.integrable_sq.const_mul _)
      (fun n => Eventually.of_forall fun p => by
        simp only [Function.uncurry, hH]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have e : ((R n).process p.1 p.2 * b p.1 p.2 - g p.1 p.2 * b p.1 p.2) ^ 2 =
            ((R n).process p.1 p.2 - g p.1 p.2) ^ 2 * b p.1 p.2 ^ 2 := by ring
        rw [e]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h1 := hRb n p.1 p.2
        have h2 := hgb p.1 p.2
        have : |(R n).process p.1 p.2 - g p.1 p.2| ≤ 2 * C := by
          calc _ ≤ |(R n).process p.1 p.2| + |g p.1 p.2| := abs_sub _ _
            _ ≤ 2 * C := by linarith
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2)
      (by
        filter_upwards [ae_mem_Ioc_tsMeasure (P := P) T,
          Measure.quasiMeasurePreserving_snd.ae hgc] with p hp hpc
        simp only [Function.uncurry, hH]
        have hcl : ∀ n : ℕ, (R n).process p.1 p.2 = g (cellLeft (T / (n + 1)) 0 p.1) p.2 :=
          fun n => riemElem_process hgad hL2 hT n hp p.2
        simp_rw [hcl]
        have hlim : Tendsto (fun n : ℕ => cellLeft (T / (n + 1)) 0 p.1) atTop (𝓝 p.1) := by
          have hh : Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop
              (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => p.1 - T / (n + 1))
            (h := fun _ => p.1) (by simpa using (tendsto_const_nhds (x := p.1)).sub hh)
            tendsto_const_nhds (fun n => ?_) (fun n => ?_)
          · have := (cellLeft_zero_mem (by positivity : (0 : ℝ) < T / (n + 1)) hp.1).2.2
            simp only; linarith
          · exact (cellLeft_zero_mem (by positivity : (0 : ℝ) < T / (n + 1)) hp.1).2.1.le
        have hg := ((hpc.tendsto p.1).comp hlim)
        have := ((hg.mul_const (b p.1 p.2)).sub_const (g p.1 p.2 * b p.1 p.2)).pow 2
        simpa using this)
    simpa using h
  refine (hconv.congr fun n => (step2 n).symm).congr fun n => ?_
  refine integral_congr_ae ?_
  filter_upwards [step1 n] with ω hω
  rw [← hω]

end Gardiner.Ito
