/-
# Uniqueness, moment bound and continuous dependence for Itô SDEs

Gardiner §4.3.1, (4.3.10)–(4.3.11).  For solutions of (4.3.4) on `[t₀, T]` (`IsSDESol`):

* `IsSDESol.supSq_le_const`: **moment bound** `E sup_{t₀ ≤ t ≤ T} |x(t)|² ≤ C (1 + E ξ²)` with
  `C = sdeMomentConst K (T - t₀)` depending only on `K` and `T - t₀`;
* `IsSDESol.supSq_sub_le`: **mean-square continuous dependence on the initial value**,
  `E sup_{t₀ ≤ t ≤ T} |x(t) - y(t)|² ≤ 3 e^{L (T - t₀)} E |ξ - η|²`, `L = (3 (T - t₀) + 12) K²`;
* `IsSDESol.unique`: **uniqueness up to indistinguishability**.
-/
import SHSLib.Gardiner.Ito.StochDE.Estimate

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- The Lipschitz/Gronwall rate `L = (3 (T - t₀) + 12) K²` of the basic estimate. -/
def sdeRate (K d : ℝ) : ℝ := (3 * d + 12) * K ^ 2

lemma sdeRate_nonneg {K d : ℝ} (hd : 0 ≤ d) : 0 ≤ sdeRate K d := by
  unfold sdeRate; positivity

/-- The constant of the moment bound: `C(K, d) = (3 + L d) e^{L d}` with `L = sdeRate K d`. -/
def sdeMomentConst (K d : ℝ) : ℝ := (3 + sdeRate K d * d) * Real.exp (sdeRate K d * d)

/-! ### Measurability helpers -/

lemma aemeasurable_iSup_Icc {Y : ℝ → Ω → ℝ} (hY : ∀ u, Measurable (Y u)) {t₀ t : ℝ}
    (ht : t₀ ≤ t) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun u => Y u ω) (Set.Icc t₀ t)) :
    AEMeasurable (fun ω => ⨆ u ∈ Set.Icc t₀ t, ‖Y u ω‖ₑ) P := by
  refine (measurable_dsup hY t₀ t).aemeasurable.congr ?_
  filter_upwards [hc] with ω hω
  exact dsup_eq_iSup ht hω

lemma measurable_comp_coeff {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F))
    {x : ℝ → Ω → ℝ} (hxm : Measurable (Function.uncurry x)) :
    Measurable (Function.uncurry fun s ω => F (x s ω) s) := by
  have h2 : Measurable fun p : ℝ × Ω => (x p.1 p.2, p.1) := hxm.prodMk measurable_fst
  exact Measurable.comp (g := Function.uncurry F) (f := fun p : ℝ × Ω => (x p.1 p.2, p.1)) hF h2

/-! ### Bounds on `tsSq` -/

section Coeff

variable {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} (hc : SDECoeffs a b t₀ T K)
include hc

lemma tsSq_a_le {x : ℝ → Ω → ℝ} {t : ℝ} (ht : t ≤ T) :
    tsSq P (fun s ω => a (x s ω) s) t₀ t ≤
      ENNReal.ofReal (K ^ 2) * ∫⁻ s in Set.Ioc t₀ t, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P := by
  unfold tsSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun ω => enorm_a_sq_le hc ⟨hs.1.le, hs.2.trans ht⟩ _

lemma tsSq_drive_le {x : ℝ → Ω → ℝ} {t : ℝ} (ht : t ≤ T) :
    tsSq P (drive t₀ b x) t₀ t ≤
      ENNReal.ofReal (K ^ 2) * ∫⁻ s in Set.Ioc t₀ t, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P := by
  unfold tsSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  have := enorm_drive_sq_le hc (x := x) (hs.2.trans ht) ω
  rwa [Set.indicator_of_mem (show s ∈ Set.Ioc t₀ T from ⟨hs.1, hs.2.trans ht⟩)] at this

lemma tsSq_a_sub_le {x y : ℝ → Ω → ℝ} {t : ℝ} (ht : t ≤ T) :
    tsSq P (fun s ω => a (x s ω) s - a (y s ω) s) t₀ t ≤
      ENNReal.ofReal (K ^ 2) * tsSq P (fun s ω => x s ω - y s ω) t₀ t := by
  unfold tsSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun ω => enorm_a_sub_sq_le hc ⟨hs.1.le, hs.2.trans ht⟩ _ _

lemma tsSq_drive_sub_le {x y : ℝ → Ω → ℝ} {t : ℝ} (ht : t ≤ T) :
    tsSq P (fun s ω => drive t₀ b x s ω - drive t₀ b y s ω) t₀ t ≤
      ENNReal.ofReal (K ^ 2) * tsSq P (fun s ω => x s ω - y s ω) t₀ t := by
  unfold tsSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  have := enorm_drive_sub_sq_le hc (x := x) (y := y) (hs.2.trans ht) ω
  rwa [Set.indicator_of_mem (show s ∈ Set.Ioc t₀ T from ⟨hs.1, hs.2.trans ht⟩)] at this

end Coeff

lemma lintegral_one_add_le_supSq [IsProbabilityMeasure P] (x : ℝ → Ω → ℝ) {t₀ t : ℝ}
    (ht : t₀ ≤ t) (hxm : Measurable (Function.uncurry x)) :
    ∫⁻ s in Set.Ioc t₀ t, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P ≤
      ENNReal.ofReal (t - t₀) + ∫⁻ s in Set.Ioc t₀ t, supSq P x t₀ s := by
  have e : ∀ s, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P = 1 + ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P := fun s => by
    rw [lintegral_add_left measurable_const]; simp
  simp_rw [e]
  have hm : Measurable fun s => ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P :=
    (hxm.enorm.pow_const 2).lintegral_prod_right'
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
    Real.volume_Ioc, one_mul]
  exact add_le_add le_rfl (tsSq_le_lintegral_supSq (P := P) x t₀ t)

/-- **The basic estimate for a difference.**  If `Yᵢ(u) = ζᵢ + ∫_{t₀}^u Aᵢ ds + ∫_{t₀}^u Bᵢ dW`
(`i = 1, 2`), then `E sup_{t₀ ≤ u ≤ t} |Y₁(u) - Y₂(u)|²` is at most
`3 E |ζ₁ - ζ₂|² + 3 (t - t₀) ∫_{t₀}^t E |A₁ - A₂|² + 12 ∫_{t₀}^t E |B₁ - B₂|²`. -/
theorem sup_sq_sub_le {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) {Y₁ Y₂ A₁ A₂ B₁ B₂ : ℝ → Ω → ℝ}
    {ζ₁ ζ₂ : Ω → ℝ} {t₀ T t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t ∈ Set.Icc t₀ T)
    (hB₁ : IsItoIntegrand 𝓕 P T B₁) (hB₂ : IsItoIntegrand 𝓕 P T B₂)
    (hB₁0 : ∀ s ω, s ≤ t₀ → B₁ s ω = 0) (hB₂0 : ∀ s ω, s ≤ t₀ → B₂ s ω = 0)
    (hA₁ : Measurable (Function.uncurry A₁)) (hA₂ : Measurable (Function.uncurry A₂))
    (hA₁i : ∀ᵐ ω ∂P, IntegrableOn (fun s => A₁ s ω) (Set.Icc t₀ T))
    (hA₂i : ∀ᵐ ω ∂P, IntegrableOn (fun s => A₂ s ω) (Set.Icc t₀ T))
    (hζ₁ : AEMeasurable ζ₁ P) (hζ₂ : AEMeasurable ζ₂ P)
    (hY₁c : ∀ᵐ ω ∂P, ContinuousOn (fun u => Y₁ u ω) (Set.Icc t₀ T))
    (hY₂c : ∀ᵐ ω ∂P, ContinuousOn (fun u => Y₂ u ω) (Set.Icc t₀ T))
    (hY₁ : ∀ u ∈ Set.Icc t₀ T, Y₁ u =ᵐ[P] fun ω =>
      ζ₁ ω + (∫ s in t₀..u, A₁ s ω) + itoInt W 𝓕 P u B₁ ω)
    (hY₂ : ∀ u ∈ Set.Icc t₀ T, Y₂ u =ᵐ[P] fun ω =>
      ζ₂ ω + (∫ s in t₀..u, A₂ s ω) + itoInt W 𝓕 P u B₂ ω) :
    supSq P (fun s ω => Y₁ s ω - Y₂ s ω) t₀ t ≤ 3 * ∫⁻ ω, ‖ζ₁ ω - ζ₂ ω‖ₑ ^ 2 ∂P +
      3 * ENNReal.ofReal (t - t₀) * tsSq P (fun s ω => A₁ s ω - A₂ s ω) t₀ t +
      12 * tsSq P (fun s ω => B₁ s ω - B₂ s ω) t₀ t := by
  have := hW.isProbabilityMeasure
  refine sup_sq_le hW ht₀ ht (hB₁.sub hB₂) (fun s ω hs => by simp [hB₁0 s ω hs, hB₂0 s ω hs])
    (hA₁.sub hA₂) (hζ₁.sub hζ₂) ((hY₁c.and hY₂c).mono fun ω hω => hω.1.sub hω.2) ?_
  intro u hu
  have hu0 : 0 ≤ u := ht₀.trans hu.1
  filter_upwards [hY₁ u hu, hY₂ u hu, itoInt_sub hW (hB₁.mono hu.2) (hB₂.mono hu.2), hA₁i, hA₂i]
    with ω h1 h2 h3 h4 h5
  have hsub : Set.uIcc t₀ u ⊆ Set.Icc t₀ T := by
    rw [Set.uIcc_of_le hu.1]; exact Set.Icc_subset_Icc_right hu.2
  rw [h1, h2, h3, intervalIntegral.integral_sub ((h4.mono_set hsub).intervalIntegrable)
    ((h5.mono_set hsub).intervalIntegrable)]
  ring

/-! ### Solutions -/

namespace IsSDESol

variable {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ}

lemma isItoIntegrand [IsFiniteMeasure P] (hx : IsSDESol W 𝓕 P a b t₀ T ξ x)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) : IsItoIntegrand 𝓕 P T (drive t₀ b x) :=
  isItoIntegrand_drive hc ht₀ hx.measurable hx.adapted hx.sq_int

/-- The basic estimate along a solution. -/
lemma supSq_le_aux (hW : IsFWiener W 𝓕 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (hξ : AEMeasurable ξ P) :
    ∀ t ∈ Set.Icc t₀ T, supSq P x t₀ t ≤ 3 * ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P +
      ENNReal.ofReal (sdeRate K (T - t₀)) * ∫⁻ s in Set.Ioc t₀ t, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P := by
  intro t ht
  have := hW.isProbabilityMeasure
  have h := sup_sq_le hW (A := fun s ω => a (x s ω) s) ht₀ ht (hx.isItoIntegrand hc ht₀)
    (fun s ω hs => drive_of_le hc hs ω) (measurable_comp_coeff hc.measurable_a hx.measurable)
    hξ hx.cont hx.eq
  refine h.trans ?_
  rw [add_assoc]
  gcongr ?_ + ?_
  set X := ∫⁻ s in Set.Ioc t₀ t, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P
  have hd : 0 ≤ T - t₀ := sub_nonneg.mpr (ht.1.trans ht.2)
  calc 3 * ENNReal.ofReal (t - t₀) * tsSq P (fun s ω => a (x s ω) s) t₀ t +
        12 * tsSq P (drive t₀ b x) t₀ t
      ≤ 3 * ENNReal.ofReal (T - t₀) * (ENNReal.ofReal (K ^ 2) * X) +
          12 * (ENNReal.ofReal (K ^ 2) * X) := by
        gcongr
        · linarith [ht.2]
        · exact tsSq_a_le hc ht.2
        · exact tsSq_drive_le hc ht.2
    _ = ENNReal.ofReal (sdeRate K (T - t₀)) * X := by
        rw [sdeRate, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity)
          (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num
        ring

/-- A solution has a finite second moment of its supremum. -/
lemma supSq_lt_top (hW : IsFWiener W 𝓕 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (hξ : MemLp ξ 2 P) :
    supSq P x t₀ T < ⊤ := by
  have := hW.isProbabilityMeasure
  refine (hx.supSq_le_aux hW hc ht₀ hξ.aestronglyMeasurable.aemeasurable T
    ⟨htT, le_rfl⟩).trans_lt ?_
  refine ENNReal.add_lt_top.mpr ⟨?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lintegral_one_add_lt_top hx.measurable hx.sq_int)⟩
  rw [lintegral_enorm_sq_eq hξ]
  exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

/-- **The moment bound** `E sup_{t₀ ≤ t ≤ T} |x(t)|² ≤ C (1 + E ξ²)`, with
`C = sdeMomentConst K (T - t₀)` depending only on `K` and `T - t₀`. -/
theorem supSq_le_const (hW : IsFWiener W 𝓕 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (hξ : MemLp ξ 2 P) :
    supSq P x t₀ T ≤ ENNReal.ofReal (sdeMomentConst K (T - t₀)) * (1 + ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P) := by
  have := hW.isProbabilityMeasure
  set L := sdeRate K (T - t₀)
  have hd : 0 ≤ T - t₀ := sub_nonneg.mpr htT
  have hL : 0 ≤ L := sdeRate_nonneg hd
  set α := 3 * ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P + ENNReal.ofReal L * ENNReal.ofReal (T - t₀)
  have hg := gronwall_ennreal (ψ := fun t => supSq P x t₀ t) (α := α) hL
    (fun s _ t _ hst => supSq_mono_right hst) (hx.supSq_lt_top hW hc ht₀ htT hξ).ne
    (fun t ht => by
      refine (hx.supSq_le_aux hW hc ht₀ hξ.aestronglyMeasurable.aemeasurable t ht).trans ?_
      have h1 := lintegral_one_add_le_supSq (P := P) x ht.1 hx.measurable
      calc 3 * ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P + ENNReal.ofReal L *
            ∫⁻ s in Set.Ioc t₀ t, ∫⁻ ω, (1 + ‖x s ω‖ₑ ^ 2) ∂P
          ≤ 3 * ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P + ENNReal.ofReal L *
            (ENNReal.ofReal (T - t₀) + ∫⁻ s in Set.Ioc t₀ t, supSq P x t₀ s) := by
            gcongr
            refine h1.trans ?_
            gcongr
            linarith [ht.2]
        _ = α + ENNReal.ofReal L * ∫⁻ s in Set.Ioc t₀ t, supSq P x t₀ s := by
            simp only [α]; ring)
    T ⟨htT, le_rfl⟩
  refine hg.trans ?_
  simp only [α, sdeMomentConst]
  rw [lintegral_enorm_sq_eq hξ, ← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_ofNat 3,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (integral_nonneg fun _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hE : 0 ≤ ∫ ω, ξ ω ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hexp : 0 < Real.exp (L * (T - t₀)) := Real.exp_pos _
  have hLd : 0 ≤ L * (T - t₀) := mul_nonneg hL hd
  have key : 3 * ∫ ω, ξ ω ^ 2 ∂P + L * (T - t₀) ≤
      (3 + L * (T - t₀)) * (1 + ∫ ω, ξ ω ^ 2 ∂P) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right key hexp.le]

/-- The basic estimate for the difference of two solutions. -/
lemma supSq_sub_le_aux {y : ℝ → Ω → ℝ} {η : Ω → ℝ} (hW : IsFWiener W 𝓕 P)
    (hx : IsSDESol W 𝓕 P a b t₀ T ξ x) (hy : IsSDESol W 𝓕 P a b t₀ T η y)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (hξ : AEMeasurable ξ P) (hη : AEMeasurable η P) :
    ∀ t ∈ Set.Icc t₀ T, supSq P (fun s ω => x s ω - y s ω) t₀ t ≤
      3 * ∫⁻ ω, ‖ξ ω - η ω‖ₑ ^ 2 ∂P + ENNReal.ofReal (sdeRate K (T - t₀)) *
        ∫⁻ s in Set.Ioc t₀ t, supSq P (fun s ω => x s ω - y s ω) t₀ s := by
  intro t ht
  have := hW.isProbabilityMeasure
  have hd : 0 ≤ T - t₀ := sub_nonneg.mpr (ht.1.trans ht.2)
  have h := sup_sq_sub_le hW (A₁ := fun s ω => a (x s ω) s) (A₂ := fun s ω => a (y s ω) s)
    ht₀ ht (hx.isItoIntegrand hc ht₀) (hy.isItoIntegrand hc ht₀)
    (fun s ω hs => drive_of_le hc hs ω) (fun s ω hs => drive_of_le hc hs ω)
    (measurable_comp_coeff hc.measurable_a hx.measurable)
    (measurable_comp_coeff hc.measurable_a hy.measurable)
    (hx.cont.mono fun ω hω => hc.driftCoeff.integrableOn hx.measurable hω)
    (hy.cont.mono fun ω hω => hc.driftCoeff.integrableOn hy.measurable hω)
    hξ hη hx.cont hy.cont hx.eq hy.eq
  refine h.trans ?_
  rw [add_assoc]
  gcongr ?_ + ?_
  set X := ∫⁻ s in Set.Ioc t₀ t, supSq P (fun s ω => x s ω - y s ω) t₀ s
  have hX : tsSq P (fun s ω => x s ω - y s ω) t₀ t ≤ X := tsSq_le_lintegral_supSq _ t₀ t
  calc 3 * ENNReal.ofReal (t - t₀) *
        tsSq P (fun s ω => a (x s ω) s - a (y s ω) s) t₀ t +
        12 * tsSq P (fun s ω => drive t₀ b x s ω - drive t₀ b y s ω) t₀ t
      ≤ 3 * ENNReal.ofReal (T - t₀) * (ENNReal.ofReal (K ^ 2) * X) +
          12 * (ENNReal.ofReal (K ^ 2) * X) := by
        gcongr
        · linarith [ht.2]
        · exact (tsSq_a_sub_le hc ht.2).trans (by gcongr)
        · exact (tsSq_drive_sub_le hc ht.2).trans (by gcongr)
    _ = ENNReal.ofReal (sdeRate K (T - t₀)) * X := by
        rw [sdeRate, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity)
          (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num
        ring

lemma supSq_sub_le_two {x y : ℝ → Ω → ℝ} {t₀ t : ℝ} (ht : t₀ ≤ t)
    (hxm : Measurable (Function.uncurry x))
    (hxc : ∀ᵐ ω ∂P, ContinuousOn (fun u => x u ω) (Set.Icc t₀ t)) :
    supSq P (fun s ω => x s ω - y s ω) t₀ t ≤ 2 * supSq P x t₀ t + 2 * supSq P y t₀ t := by
  unfold supSq
  rw [← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul' _ _ (by norm_num),
    ← lintegral_add_left' (((aemeasurable_iSup_Icc (measurable_of_uncurry hxm) ht hxc).pow_const
      2).const_mul 2)]
  refine lintegral_mono fun ω => ?_
  refine (pow_le_pow_left' ?_ 2).trans (ennreal_add_sq_le _ _)
  refine iSup₂_le fun u hu => ?_
  exact (enorm_sub_le).trans (add_le_add (enorm_le_iSup_Icc hu ω) (enorm_le_iSup_Icc hu ω))

/-- **Mean-square continuous dependence on the initial value**:
`E sup_{t₀ ≤ t ≤ T} |x(t) - y(t)|² ≤ 3 e^{L (T - t₀)} E |ξ - η|²`, `L = sdeRate K (T - t₀)`. -/
theorem supSq_sub_le {y : ℝ → Ω → ℝ} {η : Ω → ℝ} (hW : IsFWiener W 𝓕 P)
    (hx : IsSDESol W 𝓕 P a b t₀ T ξ x) (hy : IsSDESol W 𝓕 P a b t₀ T η y)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (hξ : MemLp ξ 2 P)
    (hη : MemLp η 2 P) :
    supSq P (fun s ω => x s ω - y s ω) t₀ T ≤
      (3 * ∫⁻ ω, ‖ξ ω - η ω‖ₑ ^ 2 ∂P) *
        ENNReal.ofReal (Real.exp (sdeRate K (T - t₀) * (T - t₀))) := by
  have hfin : supSq P (fun s ω => x s ω - y s ω) t₀ T ≠ ⊤ :=
    ((supSq_sub_le_two htT hx.measurable hx.cont).trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (by norm_num) (hx.supSq_lt_top hW hc ht₀ htT hξ),
       ENNReal.mul_lt_top (by norm_num) (hy.supSq_lt_top hW hc ht₀ htT hη)⟩)).ne
  exact gronwall_ennreal (ψ := fun t => supSq P (fun s ω => x s ω - y s ω) t₀ t)
    (sdeRate_nonneg (sub_nonneg.mpr htT)) (fun s _ t _ hst => supSq_mono_right hst) hfin
    (hx.supSq_sub_le_aux hW hy hc ht₀ hξ.aestronglyMeasurable.aemeasurable
      hη.aestronglyMeasurable.aemeasurable) T ⟨htT, le_rfl⟩

/-- **Uniqueness up to indistinguishability**: two solutions with the same initial value agree,
almost surely, at all times of `[t₀, T]`. -/
theorem unique {y : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
    (hx : IsSDESol W 𝓕 P a b t₀ T ξ x) (hy : IsSDESol W 𝓕 P a b t₀ T ξ y)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (hξ : MemLp ξ 2 P) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc t₀ T, x t ω = y t ω := by
  have h := hx.supSq_sub_le hW hy hc ht₀ htT hξ hξ
  simp only [sub_self, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    lintegral_zero, mul_zero, zero_mul, nonpos_iff_eq_zero] at h
  have hm : AEMeasurable (fun ω => (⨆ u ∈ Set.Icc t₀ T, ‖x u ω - y u ω‖ₑ) ^ 2) P :=
    (aemeasurable_iSup_Icc (Y := fun s ω => x s ω - y s ω)
      (fun u => (measurable_of_uncurry hx.measurable u).sub (measurable_of_uncurry hy.measurable u))
      htT ((hx.cont.and hy.cont).mono fun ω hω => hω.1.sub hω.2)).pow_const 2
  rw [supSq, lintegral_eq_zero_iff' hm] at h
  filter_upwards [h] with ω hω t ht
  simp only [Pi.zero_apply, pow_eq_zero_iff (n := 2) (by norm_num)] at hω
  have := (enorm_le_iSup_Icc (Y := fun s ω => x s ω - y s ω) ht ω).trans_eq hω
  simpa [sub_eq_zero] using this

end IsSDESol

end Gardiner.Ito.StochDE
