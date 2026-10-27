/-
# Increments of the running Itô integral

Auxiliary facts about the running Itô integral `t ↦ ∫₀ᵗ G dW` (`Gardiner.Ito.itoInt`):

* `integral_itoInt_mul_itoInt`: `E[M_r M_s] = E[M_r²]` for `r ≤ s` (orthogonality of increments);
* `integral_itoInt_sub_sq`: **the increment isometry**
  `E (∫_r^s G dW)² = E (M_s - M_r)² = ∫_r^s E G² dt`;
* `itoInt_process_eq_running`: for an elementary integrand, the running Itô integral is the
  elementary running sum.
-/
import SHSLib.Gardiner.Ito.StochDE.Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) {T : ℝ} {G : ℝ → Ω → ℝ}
include hW

/-- Orthogonality of increments: `E[M_r M_s] = E[M_r²]` for `r ≤ s ≤ T`. -/
lemma integral_itoInt_mul_itoInt {r s : ℝ} (hrs : r ≤ s) (hsT : s ≤ T)
    (hG : IsItoIntegrand 𝓕 P T G) :
    ∫ ω, itoInt W 𝓕 P r G ω * itoInt W 𝓕 P s G ω ∂P = ∫ ω, itoInt W 𝓕 P r G ω ^ 2 ∂P := by
  have := hW.isProbabilityMeasure
  have hs := memLp_itoInt hW (hG.mono hsT)
  have hr := memLp_itoInt hW (hG.mono (hrs.trans hsT))
  have hmr := itoInt_stronglyMeasurable hW (W := W) (hG.mono (hrs.trans hsT))
  calc ∫ ω, itoInt W 𝓕 P r G ω * itoInt W 𝓕 P s G ω ∂P
      = ∫ ω, (P[itoInt W 𝓕 P r G * itoInt W 𝓕 P s G | 𝓕 r]) ω ∂P :=
        (integral_condExp (𝓕.le r)).symm
    _ = ∫ ω, (itoInt W 𝓕 P r G * P[itoInt W 𝓕 P s G | 𝓕 r]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hmr (hr.integrable_mul hs)
          (hs.integrable one_le_two))
    _ = ∫ ω, itoInt W 𝓕 P r G ω ^ 2 ∂P :=
        integral_congr_ae ((condExp_itoInt hW hrs (hG.mono hsT)).mono fun ω h => by
          simp only [Pi.mul_apply, h, sq])

/-- `t ↦ E G(t)²` is integrable on `(0, T]` for an Itô integrand. -/
lemma integrableOn_integral_sq (hG : IsItoIntegrand 𝓕 P T G) :
    IntegrableOn (fun u => ∫ ω, G u ω ^ 2 ∂P) (Set.Ioc 0 T) := by
  have := hW.isProbabilityMeasure
  exact hG.memLp.integrable_sq.integral_prod_left

/-- **The increment isometry**: `E (M_s - M_r)² = ∫_r^s E G² dt` for `0 ≤ r ≤ s ≤ T`. -/
theorem integral_itoInt_sub_sq {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hsT : s ≤ T)
    (hG : IsItoIntegrand 𝓕 P T G) :
    ∫ ω, (itoInt W 𝓕 P s G ω - itoInt W 𝓕 P r G ω) ^ 2 ∂P =
      ∫ u in Set.Ioc r s, ∫ ω, G u ω ^ 2 ∂P := by
  have := hW.isProbabilityMeasure
  have hs := memLp_itoInt hW (hG.mono hsT)
  have hr := memLp_itoInt hW (hG.mono (hrs.trans hsT))
  have e : (fun ω => (itoInt W 𝓕 P s G ω - itoInt W 𝓕 P r G ω) ^ 2) = fun ω =>
      itoInt W 𝓕 P s G ω ^ 2 - 2 * (itoInt W 𝓕 P r G ω * itoInt W 𝓕 P s G ω) +
        itoInt W 𝓕 P r G ω ^ 2 := by funext ω; ring
  have i1 : Integrable (fun ω => itoInt W 𝓕 P s G ω ^ 2) P := hs.integrable_sq
  have i2 : Integrable (fun ω => 2 * (itoInt W 𝓕 P r G ω * itoInt W 𝓕 P s G ω)) P :=
    (hr.integrable_mul hs).const_mul 2
  have i3 : Integrable (fun ω => itoInt W 𝓕 P r G ω ^ 2) P := hr.integrable_sq
  rw [e, integral_add (f := fun ω => itoInt W 𝓕 P s G ω ^ 2 -
      2 * (itoInt W 𝓕 P r G ω * itoInt W 𝓕 P s G ω)) (i1.sub i2) i3,
    integral_sub i1 i2, integral_const_mul,
    integral_itoInt_mul_itoInt hW hrs hsT hG, itoInt_sq hW (hG.mono hsT),
    itoInt_sq hW (hG.mono (hrs.trans hsT))]
  have hI := (integrableOn_integral_sq hW hG)
  have hU : Set.Ioc 0 s = Set.Ioc 0 r ∪ Set.Ioc r s := (Set.Ioc_union_Ioc_eq_Ioc hr0 hrs).symm
  rw [hU, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hI.mono_set (Set.Ioc_subset_Ioc_right (hrs.trans hsT)))
    (hI.mono_set (Set.Ioc_subset_Ioc hr0 hsT))]
  ring

/-- The increment isometry as an inequality in `ℝ≥0∞`. -/
theorem lintegral_itoInt_sub_sq_le {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hsT : s ≤ T)
    (hG : IsItoIntegrand 𝓕 P T G) :
    ∫⁻ ω, ‖itoInt W 𝓕 P s G ω - itoInt W 𝓕 P r G ω‖ₑ ^ 2 ∂P ≤
      ∫⁻ u in Set.Ioc r s, ∫⁻ ω, ‖G u ω‖ₑ ^ 2 ∂P := by
  have := hW.isProbabilityMeasure
  have hs := memLp_itoInt hW (hG.mono hsT)
  have hr := memLp_itoInt hW (hG.mono (hrs.trans hsT))
  have h := lintegral_enorm_sq_eq (hs.sub hr)
  simp only [Pi.sub_apply] at h
  rw [h, integral_itoInt_sub_sq hW hr0 hrs hsT hG]
  refine (ofReal_integral_le_lintegral_enorm _).trans ?_
  refine lintegral_mono fun u => ?_
  exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp [enorm_pow]))

/-- For an elementary integrand supported in `(0, T]`, the running Itô integral at `u ≤ T` is the
elementary running sum `Σᵢ φᵢ (W(bᵢ ∧ u) - W(aᵢ ∧ u))`. -/
theorem itoInt_process_eq_running {ι : Type} [Fintype ι] (H : ElemIntegrand 𝓕 P ι)
    (hH : H.SupportedIn T) {u : ℝ} (huT : u ≤ T) :
    itoInt W 𝓕 P u H.process =ᵐ[P] H.running W u := by
  have := hW.isProbabilityMeasure
  calc itoInt W 𝓕 P u H.process =ᵐ[P] P[itoInt W 𝓕 P T H.process | 𝓕 u] :=
        (condExp_itoInt hW huT (H.isItoIntegrand T)).symm
    _ =ᵐ[P] P[H.integral W | 𝓕 u] := condExp_congr_ae (itoInt_elem hW H hH)
    _ = P[H.running W T | 𝓕 u] := by rw [H.running_eq_integral W hH]
    _ =ᵐ[P] H.running W u := (H.martingale_running hW).2 u T huT

/-- Two integrands that agree on `(0, t] × Ω` have the same Itô integral at time `t`. -/
lemma itoInt_congr_of_eq_on {t : ℝ} {G H : ℝ → Ω → ℝ}
    (hG : IsItoIntegrand 𝓕 P t G) (hH : IsItoIntegrand 𝓕 P t H)
    (h : ∀ s ∈ Set.Ioc 0 t, ∀ ω, G s ω = H s ω) :
    itoInt W 𝓕 P t G =ᵐ[P] itoInt W 𝓕 P t H := by
  have := hW.isProbabilityMeasure
  refine itoInt_congr hW hG hH ?_
  unfold tsMeasure
  refine (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hG.measurable hH.measurable)).mpr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact Eventually.of_forall fun ω => h s hs ω

omit hW in
lemma abs_one_sub_afterInd_le (s u : ℝ) : |1 - afterInd s u| ≤ 1 := by
  rcases lt_or_ge s u with h | h
  · rw [afterInd_of_lt h]; simp
  · rw [afterInd_of_le h]; simp

/-- **Additivity of the running Itô integral**: for `0 ≤ s ≤ u ≤ T`,
`∫₀ᵘ 1_{v > s} G dW = ∫₀ᵘ G dW - ∫₀ˢ G dW`, i.e. `∫_s^u G dW` is the Itô integral of the integrand
restricted to `(s, u]`. -/
theorem itoInt_afterInd {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (huT : u ≤ T)
    (hG : IsItoIntegrand 𝓕 P T G) :
    itoInt W 𝓕 P u (fun v ω => afterInd s v * G v ω) =ᵐ[P]
      fun ω => itoInt W 𝓕 P u G ω - itoInt W 𝓕 P s G ω := by
  have := hW.isProbabilityMeasure
  set H : ℝ → Ω → ℝ := fun v ω => (1 - afterInd s v) * G v ω
  have hH : IsItoIntegrand 𝓕 P T H :=
    isItoIntegrand_det_mul hG (measurable_const.sub (measurable_afterInd s))
      (abs_one_sub_afterInd_le s)
  have h1 : itoInt W 𝓕 P s G =ᵐ[P] itoInt W 𝓕 P s H :=
    itoInt_congr_of_eq_on hW (hG.mono (hsu.trans huT)) (hH.mono (hsu.trans huT))
      (fun v hv ω => by simp [H, afterInd_of_le hv.2])
  have h2 : itoInt W 𝓕 P u H =ᵐ[P] itoInt W 𝓕 P s H := by
    have hsq := integral_itoInt_sub_sq hW hs hsu huT hH
    have h0 : ∫ v in Set.Ioc s u, ∫ ω, H v ω ^ 2 ∂P = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun v hv => by simp [H, afterInd_of_lt hv.1]
    rw [h0] at hsq
    have := ae_eq_zero_of_integral_sq ((memLp_itoInt hW (hH.mono huT)).sub
      (memLp_itoInt hW (hH.mono (hsu.trans huT)))) hsq
    filter_upwards [this] with ω hω
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hω
    exact hω
  have e : (fun v ω => afterInd s v * G v ω) = fun v ω => G v ω - H v ω := by
    funext v ω; simp only [H]; ring
  rw [e]
  filter_upwards [itoInt_sub hW (hG.mono huT) (hH.mono huT), h1, h2] with ω e1 e2 e3
  rw [e1, e3, e2]

end Gardiner.Ito.StochDE
