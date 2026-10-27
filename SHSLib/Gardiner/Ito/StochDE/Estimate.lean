/-
# The basic `L²` estimates for Itô processes with state-dependent coefficients

* `isItoIntegrand_drive`: for a jointly measurable adapted process `x` with
  `∫_{t₀}^T E x(s)² ds < ∞`, `s ↦ 1_{s > t₀} b(x(s), s)` is an Itô integrand on `[0, T]`;
* `sup_sq_le`: if `Y(u) = ζ + ∫_{t₀}^u A ds + ∫_{t₀}^u B dW` for every `u ∈ [t₀, T]` and `Y` has
  continuous paths, then
  `E sup_{t₀ ≤ u ≤ t} |Y(u)|² ≤ 3 E ζ² + 3 (t - t₀) ∫_{t₀}^t E A² ds + 12 ∫_{t₀}^t E B² ds`.
  The factor `12 = 3 · 4` comes from Doob's inequality for the Itô integral.
-/
import SHSLib.Gardiner.Ito.StochDE.Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- `∫_{(t₀, t]} E[A(s)²] ds` as an element of `ℝ≥0∞`. -/
def tsSq (P : Measure Ω) (A : ℝ → Ω → ℝ) (t₀ t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Set.Ioc t₀ t, ∫⁻ ω, ‖A s ω‖ₑ ^ 2 ∂P

/-- `E[sup_{t₀ ≤ u ≤ t} |Y(u)|²]` as an element of `ℝ≥0∞`. -/
def supSq (P : Measure Ω) (Y : ℝ → Ω → ℝ) (t₀ t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (⨆ u ∈ Set.Icc t₀ t, ‖Y u ω‖ₑ) ^ 2 ∂P

lemma supSq_mono_right {Y : ℝ → Ω → ℝ} {t₀ s t : ℝ} (hst : s ≤ t) :
    supSq P Y t₀ s ≤ supSq P Y t₀ t := by
  refine lintegral_mono fun ω => pow_le_pow_left' ?_ 2
  exact biSup_mono fun u hu => ⟨hu.1, hu.2.trans hst⟩

lemma enorm_le_iSup_Icc {Y : ℝ → Ω → ℝ} {t₀ t s : ℝ} (hs : s ∈ Set.Icc t₀ t) (ω : Ω) :
    ‖Y s ω‖ₑ ≤ ⨆ u ∈ Set.Icc t₀ t, ‖Y u ω‖ₑ :=
  le_iSup₂ (f := fun u (_ : u ∈ Set.Icc t₀ t) => ‖Y u ω‖ₑ) s hs

/-- `∫_{t₀}^t E Y(s)² ds ≤ ∫_{t₀}^t E sup_{t₀ ≤ u ≤ s} |Y(u)|² ds`. -/
lemma tsSq_le_lintegral_supSq (Y : ℝ → Ω → ℝ) (t₀ t : ℝ) :
    tsSq P Y t₀ t ≤ ∫⁻ s in Set.Ioc t₀ t, supSq P Y t₀ s := by
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  exact lintegral_mono fun ω => pow_le_pow_left' (enorm_le_iSup_Icc ⟨hs.1.le, le_rfl⟩ ω) 2

/-! ### Pointwise bounds for the coefficients -/

section Coeff

variable {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} (hc : SDECoeffs a b t₀ T K)
include hc

lemma drive_of_le {x : ℝ → Ω → ℝ} {s : ℝ} (hs : s ≤ t₀) (ω : Ω) : drive t₀ b x s ω = 0 := by
  simp [drive, afterInd_of_le hs]

lemma drive_of_lt {x : ℝ → Ω → ℝ} {s : ℝ} (hs : t₀ < s) (ω : Ω) :
    drive t₀ b x s ω = b (x s ω) s := by
  simp [drive, afterInd_of_lt hs]

lemma enorm_a_sq_le {s : ℝ} (hs : s ∈ Set.Icc t₀ T) (y : ℝ) :
    ‖a y s‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * (1 + ‖y‖ₑ ^ 2) := by
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hc.sq_a_le hs y)

lemma enorm_b_sq_le {s : ℝ} (hs : s ∈ Set.Icc t₀ T) (y : ℝ) :
    ‖b y s‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * (1 + ‖y‖ₑ ^ 2) := by
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hc.sq_b_le hs y)

lemma enorm_a_sub_sq_le {s : ℝ} (hs : s ∈ Set.Icc t₀ T) (y z : ℝ) :
    ‖a y s - a z s‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ‖y - z‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hc.lip_a hs y z
  have h0 : 0 ≤ |a y s - a z s| := abs_nonneg _
  rw [← sq_abs (a y s - a z s), ← sq_abs (y - z), ← mul_pow]
  exact pow_le_pow_left₀ h0 h 2

lemma enorm_b_sub_sq_le {s : ℝ} (hs : s ∈ Set.Icc t₀ T) (y z : ℝ) :
    ‖b y s - b z s‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ‖y - z‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hc.lip_b hs y z
  have h0 : 0 ≤ |b y s - b z s| := abs_nonneg _
  rw [← sq_abs (b y s - b z s), ← sq_abs (y - z), ← mul_pow]
  exact pow_le_pow_left₀ h0 h 2

lemma enorm_drive_sq_le {x : ℝ → Ω → ℝ} {s : ℝ} (hs : s ≤ T) (ω : Ω) :
    ‖drive t₀ b x s ω‖ₑ ^ 2 ≤
      (Set.Ioc t₀ T).indicator (fun s => ENNReal.ofReal (K ^ 2) * (1 + ‖x s ω‖ₑ ^ 2)) s := by
  by_cases h : t₀ < s
  · rw [drive_of_lt hc h, Set.indicator_of_mem (show s ∈ Set.Ioc t₀ T from ⟨h, hs⟩)]
    exact enorm_b_sq_le hc ⟨h.le, hs⟩ _
  · push_neg at h
    simp [drive_of_le hc h]

lemma enorm_drive_sub_sq_le {x y : ℝ → Ω → ℝ} {s : ℝ} (hs : s ≤ T) (ω : Ω) :
    ‖drive t₀ b x s ω - drive t₀ b y s ω‖ₑ ^ 2 ≤
      (Set.Ioc t₀ T).indicator (fun s => ENNReal.ofReal (K ^ 2) * ‖x s ω - y s ω‖ₑ ^ 2) s := by
  by_cases h : t₀ < s
  · rw [drive_of_lt hc h, drive_of_lt hc h, Set.indicator_of_mem (show s ∈ Set.Ioc t₀ T from ⟨h, hs⟩)]
    exact enorm_b_sub_sq_le hc ⟨h.le, hs⟩ _ _
  · push_neg at h
    simp [drive_of_le hc h]

end Coeff

/-! ### The noise integrand -/

lemma memLp_two_of_lintegral_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (h : ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ < ⊤) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq hf]
  refine ⟨hf.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa [enorm_pow] using h

lemma measurable_drive {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} (hc : SDECoeffs a b t₀ T K)
    {x : ℝ → Ω → ℝ} (hxm : Measurable (Function.uncurry x)) :
    Measurable (Function.uncurry (drive t₀ b x)) := by
  have h1 : Measurable fun p : ℝ × Ω => afterInd t₀ p.1 :=
    (measurable_afterInd t₀).comp measurable_fst
  have h2 : Measurable fun p : ℝ × Ω => (x p.1 p.2, p.1) := hxm.prodMk measurable_fst
  have h3 : Measurable fun p : ℝ × Ω => b (x p.1 p.2) p.1 :=
    Measurable.comp (g := Function.uncurry b) (f := fun p : ℝ × Ω => (x p.1 p.2, p.1))
      hc.measurable_b h2
  exact h1.mul h3

lemma drive_adapted {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} (hc : SDECoeffs a b t₀ T K)
    {x : ℝ → Ω → ℝ} (hxa : ∀ t ∈ Set.Icc t₀ T, StronglyMeasurable[𝓕 t] (x t)) {t : ℝ}
    (htT : t ≤ T) : StronglyMeasurable[𝓕 t] (drive t₀ b x t) := by
  by_cases h : t₀ < t
  · have e : drive t₀ b x t = fun ω => b (x t ω) t := funext fun ω => drive_of_lt hc h ω
    rw [e]
    have hx : Measurable[𝓕 t] (x t) := (hxa t ⟨h.le, htT⟩).measurable
    have h2 : Measurable[𝓕 t] fun ω => (x t ω, t) := hx.prodMk measurable_const
    exact (Measurable.comp (g := Function.uncurry b) hc.measurable_b h2).stronglyMeasurable
  · push_neg at h
    have e : drive t₀ b x t = fun _ => 0 := funext fun ω => drive_of_le hc h ω
    rw [e]; exact stronglyMeasurable_const

/-- `∫_{(0,T]} ∫ |1_{s>t₀} b(x(s), s)|² ≤ K² ∫_{(t₀,T]} ∫ (1 + |x(s)|²)`. -/
lemma lintegral_tsMeasure_drive_le [IsFiniteMeasure P] {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ}
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) {x : ℝ → Ω → ℝ}
    (hxm : Measurable (Function.uncurry x)) :
    ∫⁻ p, ‖Function.uncurry (drive t₀ b x) p‖ₑ ^ 2 ∂(tsMeasure P T) ≤
      ENNReal.ofReal (K ^ 2) * ∫⁻ s in Set.Ioc t₀ T, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P := by
  have hdm := measurable_drive hc hxm
  unfold tsMeasure
  rw [lintegral_prod _ (hdm.enorm.pow_const 2).aemeasurable]
  have hF : Measurable fun s => ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P :=
    (measurable_const.add (hxm.enorm.pow_const 2)).lintegral_prod_right'
  calc ∫⁻ s in Set.Ioc 0 T, ∫⁻ ω, ‖Function.uncurry (drive t₀ b x) (s, ω)‖ₑ ^ 2 ∂P
      ≤ ∫⁻ s in Set.Ioc 0 T, (Set.Ioc t₀ T).indicator
          (fun s => ENNReal.ofReal (K ^ 2) * ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P) s := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        by_cases h : t₀ < s
        · have hm : Measurable fun ω => 1 + ‖x s ω‖ₑ ^ 2 :=
            measurable_const.add ((measurable_of_uncurry hxm s).enorm.pow_const 2)
          rw [Set.indicator_of_mem (show s ∈ Set.Ioc t₀ T from ⟨h, hs.2⟩),
            ← lintegral_const_mul _ hm]
          refine lintegral_mono fun ω => ?_
          have := enorm_drive_sq_le hc (x := x) hs.2 ω
          rwa [Set.indicator_of_mem (show s ∈ Set.Ioc t₀ T from ⟨h, hs.2⟩)] at this
        · push_neg at h
          simp [Function.uncurry, drive_of_le hc h]
    _ ≤ ∫⁻ s, (Set.Ioc t₀ T).indicator
          (fun s => ENNReal.ofReal (K ^ 2) * ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P) s :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (K ^ 2) * ∫⁻ s in Set.Ioc t₀ T, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P := by
        rw [lintegral_indicator measurableSet_Ioc, lintegral_const_mul _ hF]

lemma lintegral_one_add_lt_top [IsFiniteMeasure P] {x : ℝ → Ω → ℝ}
    (hxm : Measurable (Function.uncurry x)) {t₀ T : ℝ}
    (hsq : ∫⁻ s in Set.Ioc t₀ T, ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P < ⊤) :
    ∫⁻ s in Set.Ioc t₀ T, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P < ⊤ := by
  have hx2 : ∀ s, Measurable fun ω => ‖x s ω‖ₑ ^ 2 := fun s =>
    ((measurable_of_uncurry hxm s).enorm.pow_const 2)
  have e : ∀ s, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P = P Set.univ + ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P := fun s => by
    rw [lintegral_add_left measurable_const]; simp
  simp_rw [e]
  rw [lintegral_add_left measurable_const]
  refine ENNReal.add_lt_top.mpr ⟨?_, hsq⟩
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
    Real.volume_Ioc]
  exact ENNReal.mul_lt_top (measure_lt_top P _) ENNReal.ofReal_lt_top

/-- **The noise integrand of (4.3.4) is an Itô integrand.** -/
theorem isItoIntegrand_drive [IsFiniteMeasure P] {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ}
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) {x : ℝ → Ω → ℝ}
    (hxm : Measurable (Function.uncurry x))
    (hxa : ∀ t ∈ Set.Icc t₀ T, StronglyMeasurable[𝓕 t] (x t))
    (hsq : ∫⁻ s in Set.Ioc t₀ T, ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P < ⊤) :
    IsItoIntegrand 𝓕 P T (drive t₀ b x) where
  measurable := measurable_drive hc hxm
  adapted t _ htT := drive_adapted hc hxa htT
  memLp := by
    refine memLp_two_of_lintegral_lt_top (measurable_drive hc hxm).aestronglyMeasurable ?_
    refine (lintegral_tsMeasure_drive_le hc ht₀ hxm).trans_lt ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_one_add_lt_top hxm hsq)

/-! ### The basic estimate -/

/-- `∫_{(0,t]} E B² ≤ ∫_{(t₀,t]} E B²` for an integrand vanishing on `(0, t₀]` (as `ℝ≥0∞`). -/
lemma ofReal_integral_sq_le_tsSq {B : ℝ → Ω → ℝ} {t₀ t : ℝ} (ht₀ : 0 ≤ t₀)
    (hB0 : ∀ s ω, s ≤ t₀ → B s ω = 0) :
    ENNReal.ofReal (∫ s in Set.Ioc 0 t, ∫ ω, B s ω ^ 2 ∂P) ≤ tsSq P B t₀ t := by
  refine (ofReal_integral_le_lintegral_enorm _).trans ?_
  have h1 : ∀ s, ‖∫ ω, B s ω ^ 2 ∂P‖ₑ ≤ ∫⁻ ω, ‖B s ω‖ₑ ^ 2 ∂P := fun s =>
    (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp [enorm_pow]))
  refine (lintegral_mono fun s => h1 s).trans ?_
  refine (lintegral_mono_set (Set.Ioc_subset_Ioc_union_Ioc (b := t₀))).trans ?_
  refine (lintegral_union_le _ _ _).trans ?_
  have h0 : ∫⁻ s in Set.Ioc 0 t₀, ∫⁻ ω, ‖B s ω‖ₑ ^ 2 ∂P = 0 :=
    setLIntegral_eq_zero measurableSet_Ioc fun s hs => by simp [hB0 s _ hs.2]
  rw [h0, zero_add]
  rfl

/-- **The basic `L²` estimate.** If `Y(u) = ζ + ∫_{t₀}^u A ds + ∫_{t₀}^u B dW` almost surely for
each `u ∈ [t₀, T]` and `Y` has almost surely continuous paths, then for `t ∈ [t₀, T]`
`E sup_{t₀ ≤ u ≤ t} |Y(u)|² ≤ 3 E ζ² + 3 (t - t₀) ∫_{t₀}^t E A² + 12 ∫_{t₀}^t E B²`. -/
theorem sup_sq_le {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) {Y A B : ℝ → Ω → ℝ} {ζ : Ω → ℝ}
    {t₀ T t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t ∈ Set.Icc t₀ T)
    (hB : IsItoIntegrand 𝓕 P T B) (hB0 : ∀ s ω, s ≤ t₀ → B s ω = 0)
    (hA : Measurable (Function.uncurry A)) (hζ : AEMeasurable ζ P)
    (hYc : ∀ᵐ ω ∂P, ContinuousOn (fun u => Y u ω) (Set.Icc t₀ T))
    (hY : ∀ u ∈ Set.Icc t₀ T, Y u =ᵐ[P] fun ω =>
      ζ ω + (∫ s in t₀..u, A s ω) + itoInt W 𝓕 P u B ω) :
    supSq P Y t₀ t ≤ 3 * ∫⁻ ω, ‖ζ ω‖ₑ ^ 2 ∂P + 3 * ENNReal.ofReal (t - t₀) * tsSq P A t₀ t +
      12 * tsSq P B t₀ t := by
  have := hW.isProbabilityMeasure
  have hT : 0 ≤ T := ht₀.trans (ht.1.trans ht.2)
  set I := itoCont W 𝓕 P T B
  have hI := isContItoVersion_itoCont hW hB hT
  have hgrid : ∀ᵐ ω ∂P, ∀ n (k : Fin (2 ^ n + 1)), Y (gridPt t₀ t n k) ω =
      ζ ω + (∫ s in t₀..gridPt t₀ t n k, A s ω) + I (gridPt t₀ t n k) ω := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k
    have hg := gridPt_mem ht.1 (n := n) (k := k) (Nat.lt_succ_iff.mp k.isLt)
    have hgT : gridPt t₀ t n k ∈ Set.Icc t₀ T := ⟨hg.1, hg.2.trans ht.2⟩
    filter_upwards [hY _ hgT, hI.eq _ ⟨ht₀.trans hg.1, hgT.2⟩] with ω h1 h2
    rw [h1]; simp only [I, h2]
  set Aint : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Ioc t₀ t, ‖A s ω‖ₑ
  set Isup : Ω → ℝ≥0∞ := fun ω => ⨆ u ∈ Set.Icc 0 t, ‖I u ω‖ₑ
  have hpt : ∀ᵐ ω ∂P, (⨆ u ∈ Set.Icc t₀ t, ‖Y u ω‖ₑ) ≤ ‖ζ ω‖ₑ + Aint ω + Isup ω := by
    filter_upwards [hYc, hgrid] with ω hc hg
    rw [← dsup_eq_iSup ht.1 (hc.mono (Set.Icc_subset_Icc_right ht.2))]
    refine iSup_le fun n => iSup_le fun k => ?_
    have hmem := gridPt_mem ht.1 (Nat.lt_succ_iff.mp k.isLt)
    rw [hg n k]
    refine (enorm_add_le _ _).trans ?_
    refine add_le_add ?_ ?_
    · refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [intervalIntegral.integral_of_le hmem.1]
      exact (enorm_integral_le_lintegral_enorm _).trans
        (lintegral_mono_set (Set.Ioc_subset_Ioc_right hmem.2))
    · exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc 0 t) => ‖I u ω‖ₑ) _
        ⟨ht₀.trans hmem.1, hmem.2⟩
  have hAs : Measurable fun q : Ω × ℝ => ‖A q.2 q.1‖ₑ :=
    (Measurable.comp (g := Function.uncurry A) (f := fun q : Ω × ℝ => (q.2, q.1)) hA
      measurable_swap).enorm
  have hAm : Measurable Aint := hAs.lintegral_prod_right'
  have hζ2 : AEMeasurable (fun ω => 3 * ‖ζ ω‖ₑ ^ 2) P := (hζ.enorm.pow_const 2).const_mul 3
  have hA2 : Measurable fun ω => 3 * Aint ω ^ 2 := (hAm.pow_const 2).const_mul 3
  -- the drift term
  have hAterm : ∫⁻ ω, Aint ω ^ 2 ∂P ≤ ENNReal.ofReal (t - t₀) * tsSq P A t₀ t := by
    calc ∫⁻ ω, Aint ω ^ 2 ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (t - t₀) * (∫⁻ s in Set.Ioc t₀ t, ‖A s ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have := lintegral_sq_le_mul (μ := (volume : Measure ℝ).restrict (Set.Ioc t₀ t))
            (f := fun s => ‖A s ω‖ₑ)
            ((hAs.comp (measurable_const.prodMk measurable_id)).aemeasurable)
          simpa [Real.volume_Ioc] using this
      _ = ENNReal.ofReal (t - t₀) * tsSq P A t₀ t := by
          rw [lintegral_const_mul _ ((hAs.pow_const 2).lintegral_prod_right')]
          congr 1
          exact lintegral_lintegral_swap ((hAs.pow_const 2).aemeasurable)
  -- the noise term
  have hIterm : ∫⁻ ω, Isup ω ^ 2 ∂P ≤ 4 * tsSq P B t₀ t := by
    refine (hI.doob hW hB ⟨ht₀.trans ht.1, ht.2⟩).trans ?_
    gcongr
    exact ofReal_integral_sq_le_tsSq ht₀ hB0
  calc supSq P Y t₀ t ≤ ∫⁻ ω, (‖ζ ω‖ₑ + Aint ω + Isup ω) ^ 2 ∂P :=
        lintegral_mono_ae (hpt.mono fun ω h => pow_le_pow_left' h 2)
    _ ≤ ∫⁻ ω, (3 * ‖ζ ω‖ₑ ^ 2 + 3 * Aint ω ^ 2 + 3 * Isup ω ^ 2) ∂P :=
        lintegral_mono fun ω => ennreal_add3_sq_le _ _ _
    _ = 3 * ∫⁻ ω, ‖ζ ω‖ₑ ^ 2 ∂P + 3 * ∫⁻ ω, Aint ω ^ 2 ∂P + 3 * ∫⁻ ω, Isup ω ^ 2 ∂P := by
        rw [lintegral_add_left' (hζ2.add hA2.aemeasurable), lintegral_add_left' hζ2,
          lintegral_const_mul'' _ (hζ.enorm.pow_const 2), lintegral_const_mul _ (hAm.pow_const 2),
          lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 3 * ∫⁻ ω, ‖ζ ω‖ₑ ^ 2 ∂P + 3 * (ENNReal.ofReal (t - t₀) * tsSq P A t₀ t) +
          3 * (4 * tsSq P B t₀ t) := by gcongr
    _ = _ := by ring

end Gardiner.Ito.StochDE
