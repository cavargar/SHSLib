import SHSLib.Core.DavisConditionalHoldingDensityRandomWindow

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Truncating a profile at an age horizon: the core transfer

The conditional laws of a segment bound the hazard average of a profile by a
constant that bounds the profile *everywhere*.  Only ages inside the age window
ever enter such an average, so a bound below an age horizon should suffice.

This module makes that precise by truncating the age: `Φ̃(z, r) = Φ(z, r ⊓ T)`
agrees with `Φ` below the horizon `T`, inherits its continuity, joint
measurability and Lipschitz constant, and is bounded everywhere as soon as `Φ`
is bounded below the horizon.  Because a hazard window integral over a window
lying below the horizon is the same for `Φ` and for `Φ̃`, every bound proved for
globally bounded profiles transfers to profiles bounded only below the horizon:
the window estimates, and both forms — deterministic and history-measurable
window length — of the density form of the conditional holding-time law.

The module sits directly above the density form of the conditional holding-time
law so that the segment laws downstream can consume the horizon-localized
statements.  The quantitative consequences for the centered reset profile,
which need the linear growth of its compensator, live further down in
`DavisProfileTruncation`.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A sharper bound on the hazard average of a bounded profile: it is at most
the bound times the mass the window carries. -/
theorem abs_davisHazardWindowIntegral_le_mul_survivor_sub
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (Phi : DavisState Q n → ℝ → ℝ) (hPhicont : ∀ z, Continuous (Phi z))
    (K : ℝ) (hK : ∀ z r, |Phi z r| ≤ K)
    (z : DavisState Q n) (u T : ℝ≥0) :
    |davisHazardWindowIntegral S hflow Phi z u T| ≤
      K * (davisSegmentSurvivor S hflow z u -
        davisSegmentSurvivor S hflow z (u + T)) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK z 0)
  have hdens_cont : Continuous (davisSegmentHazardDensity S hflow z) :=
    continuous_davisSegmentHazardDensity S hflow hcont z
  have hdens_nonneg : ∀ s : ℝ, 0 ≤ davisSegmentHazardDensity S hflow z s := by
    intro s
    unfold davisSegmentHazardDensity
    exact mul_nonneg (totalIntensity_nonneg S _) (Real.exp_nonneg _)
  have hmass := integral_Icc_davisSegmentHazardDensity S hflow hcont z u (u + T)
    le_self_add
  unfold davisHazardWindowIntegral
  calc |∫ s in Set.Icc (u : ℝ) ((u + T : ℝ≥0) : ℝ),
          davisSegmentHazardDensity S hflow z s * Phi z s|
      ≤ ∫ s in Set.Icc (u : ℝ) ((u + T : ℝ≥0) : ℝ),
          |davisSegmentHazardDensity S hflow z s * Phi z s| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Icc (u : ℝ) ((u + T : ℝ≥0) : ℝ)))
            (f := fun s => davisSegmentHazardDensity S hflow z s * Phi z s)
    _ ≤ ∫ s in Set.Icc (u : ℝ) ((u + T : ℝ≥0) : ℝ),
          K * davisSegmentHazardDensity S hflow z s := by
        refine setIntegral_mono_on
          (((hdens_cont.mul (hPhicont z)).continuousOn.integrableOn_compact
            isCompact_Icc).abs)
          ((continuous_const.mul hdens_cont).continuousOn.integrableOn_compact
            isCompact_Icc) measurableSet_Icc ?_
        intro s _
        rw [abs_mul, abs_of_nonneg (hdens_nonneg s), mul_comm]
        exact mul_le_mul_of_nonneg_right (hK z s) (hdens_nonneg s)
    _ = K * (davisSegmentSurvivor S hflow z u -
          davisSegmentSurvivor S hflow z (u + T)) := by
        rw [integral_const_mul, hmass]

/-! ## The truncated profile -/


/-- A profile with its age truncated at the horizon `Tmax`. -/
def davisTruncatedProfile (Phi : DavisState Q n → ℝ → ℝ) (Tmax : ℝ) :
    DavisState Q n → ℝ → ℝ :=
  fun z r => Phi z (min r Tmax)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Below the horizon the truncated profile is the original one. -/
theorem davisTruncatedProfile_eq_of_le (Phi : DavisState Q n → ℝ → ℝ)
    {Tmax : ℝ} (z : DavisState Q n) {r : ℝ} (hr : r ≤ Tmax) :
    davisTruncatedProfile Phi Tmax z r = Phi z r := by
  rw [davisTruncatedProfile, min_eq_left hr]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Truncation preserves continuity in the age. -/
theorem continuous_davisTruncatedProfile {Phi : DavisState Q n → ℝ → ℝ}
    (hPhicont : ∀ z, Continuous (Phi z)) (Tmax : ℝ) (z : DavisState Q n) :
    Continuous (davisTruncatedProfile Phi Tmax z) :=
  (hPhicont z).comp (continuous_id.min continuous_const)

omit [MeasurableSingletonClass Q] in
/-- Truncation preserves joint measurability. -/
theorem measurable_davisTruncatedProfile {Phi : DavisState Q n → ℝ → ℝ}
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ => Phi p.1 p.2)
    (Tmax : ℝ) :
    Measurable fun p : DavisState Q n × ℝ =>
      davisTruncatedProfile Phi Tmax p.1 p.2 :=
  hPhimeas.comp (measurable_fst.prodMk (measurable_snd.min measurable_const))

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A profile bounded below the horizon has a globally bounded truncation. -/
theorem abs_davisTruncatedProfile_le {Phi : DavisState Q n → ℝ → ℝ} {Tmax K : ℝ}
    (hK : ∀ z r, r ≤ Tmax → |Phi z r| ≤ K) (z : DavisState Q n) (r : ℝ) :
    |davisTruncatedProfile Phi Tmax z r| ≤ K :=
  hK z (min r Tmax) (min_le_right _ _)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Truncation preserves a Lipschitz bound in the age. -/
theorem abs_davisTruncatedProfile_sub_le {Phi : DavisState Q n → ℝ → ℝ}
    {Tmax L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z r r', |Phi z r - Phi z r'| ≤ L * |r - r'|)
    (z : DavisState Q n) (r r' : ℝ) :
    |davisTruncatedProfile Phi Tmax z r -
      davisTruncatedProfile Phi Tmax z r'| ≤ L * |r - r'| := by
  refine le_trans (hlip z (min r Tmax) (min r' Tmax)) ?_
  refine mul_le_mul_of_nonneg_left ?_ hL
  have h := abs_min_sub_min_le_max (a := r) (b := Tmax) (c := r') (d := Tmax)
  simpa using h

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A hazard window integral over a window lying below the horizon does not see
the truncation. -/
theorem davisHazardWindowIntegral_davisTruncatedProfile
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (Phi : DavisState Q n → ℝ → ℝ)
    {Tmax : ℝ} (z : DavisState Q n) (u T : ℝ≥0)
    (hTmax : ((u + T : ℝ≥0) : ℝ) ≤ Tmax) :
    davisHazardWindowIntegral S hflow (davisTruncatedProfile Phi Tmax) z u T =
      davisHazardWindowIntegral S hflow Phi z u T := by
  unfold davisHazardWindowIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [davisTruncatedProfile_eq_of_le Phi z (le_trans hs.2 hTmax)]

/-- **The window bound from a profile bounded below the horizon.** -/
theorem abs_davisHazardWindowIntegral_le_of_age_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (Phi : DavisState Q n → ℝ → ℝ) (hPhicont : ∀ z, Continuous (Phi z))
    {Tmax K : ℝ} (hK : ∀ z r, r ≤ Tmax → |Phi z r| ≤ K)
    (z : DavisState Q n) (u T : ℝ≥0)
    (hTmax : ((u + T : ℝ≥0) : ℝ) ≤ Tmax) :
    |davisHazardWindowIntegral S hflow Phi z u T| ≤ K := by
  rw [← davisHazardWindowIntegral_davisTruncatedProfile S hflow Phi z u T hTmax]
  exact abs_davisHazardWindowIntegral_le S hflow hcont _
    (continuous_davisTruncatedProfile hPhicont Tmax) K
    (abs_davisTruncatedProfile_le hK) z u T

/-- The sharper window bound, weighted by the mass the window carries, from a
profile bounded below the horizon. -/
theorem abs_davisHazardWindowIntegral_le_mul_survivor_sub_of_age_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (Phi : DavisState Q n → ℝ → ℝ) (hPhicont : ∀ z, Continuous (Phi z))
    {Tmax K : ℝ} (hK : ∀ z r, r ≤ Tmax → |Phi z r| ≤ K)
    (z : DavisState Q n) (u T : ℝ≥0)
    (hTmax : ((u + T : ℝ≥0) : ℝ) ≤ Tmax) :
    |davisHazardWindowIntegral S hflow Phi z u T| ≤
      K * (davisSegmentSurvivor S hflow z u -
        davisSegmentSurvivor S hflow z (u + T)) := by
  rw [← davisHazardWindowIntegral_davisTruncatedProfile S hflow Phi z u T hTmax]
  exact abs_davisHazardWindowIntegral_le_mul_survivor_sub S hflow hcont _
    (continuous_davisTruncatedProfile hPhicont Tmax) K
    (abs_davisTruncatedProfile_le hK) z u T

/-! ## The density form of the holding-time law below an age horizon -/

/-- **The density form of the holding-time law from a horizon bound.**  Same
identity as the global version, with the profile bounded only at ages below a
horizon that covers the age window. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_holdingTime_density_of_age_le
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (Phi : DavisState Q n → ℝ → ℝ)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ => Phi p.1 p.2)
    (hPhicont : ∀ z, Continuous (Phi z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |Phi z r - Phi z r'| ≤ L * |r - r'|)
    (Rmax K : ℝ) (hK : ∀ z r, r ≤ Rmax → |Phi z r| ≤ K)
    (k : ℕ) (u : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (T : ℝ≥0)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hage : ∀ ω ∈ A, ((u ω + T : ℝ≥0) : ℝ) ≤ Rmax) :
    ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + T},
        Phi ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
          ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ∂P =
      ∫ ω in A, davisHazardWindowIntegral S hflow Phi
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState) (u ω) T ∂P := by
  classical
  have hm : ((ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k :
      MeasurableSpace Ω)) ≤ mΩ :=
    (ξ.preJumpHistoryFiltration S hflow hf hr hξ initial).le k
  have hAm : MeasurableSet A := hm _ hA
  have hum : Measurable u := hu.mono hm le_rfl
  have hhm : Measurable (ξ.holdingTime k) := hξ.holdingTime k
  have hWm : MeasurableSet {ω | u ω < ξ.holdingTime k ω ∧
      ξ.holdingTime k ω ≤ u ω + T} := by
    have hWeq : {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + T} =
        {ω | u ω < ξ.holdingTime k ω} \ {ω | u ω + T < ξ.holdingTime k ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
    exact hWeq ▸ (measurableSet_lt hum hhm).diff
      (measurableSet_lt (hum.add measurable_const) hhm)
  have hglobal := hlaw.setIntegral_holdingTime_density hcont hsurv
    (davisTruncatedProfile Phi Rmax)
    (measurable_davisTruncatedProfile hPhimeas Rmax)
    (continuous_davisTruncatedProfile hPhicont Rmax) L hL
    (abs_davisTruncatedProfile_sub_le hL hlip) K
    (abs_davisTruncatedProfile_le hK) k u hu T A hA
  have hLHS : ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + T},
      davisTruncatedProfile Phi Rmax
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
        ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ∂P =
      ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + T},
      Phi ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
        ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ∂P := by
    refine setIntegral_congr_fun (hAm.inter hWm) fun ω hω => ?_
    have hle : ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ≤ Rmax := by
      refine le_trans ?_ (hage ω hω.1)
      exact_mod_cast hω.2.2
    exact davisTruncatedProfile_eq_of_le Phi _ hle
  have hRHS : ∫ ω in A, davisHazardWindowIntegral S hflow
        (davisTruncatedProfile Phi Rmax)
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState) (u ω) T ∂P =
      ∫ ω in A, davisHazardWindowIntegral S hflow Phi
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState) (u ω) T ∂P := by
    refine setIntegral_congr_fun hAm fun ω hω => ?_
    exact davisHazardWindowIntegral_davisTruncatedProfile S hflow Phi _ (u ω) T
      (hage ω hω)
  rw [hLHS, hRHS] at hglobal
  exact hglobal

/-- **The density form at a history-measurable window length, from a horizon
bound.** -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_holdingTime_density_randomWindow_of_age_le
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (Phi : DavisState Q n → ℝ → ℝ)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ => Phi p.1 p.2)
    (hPhicont : ∀ z, Continuous (Phi z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |Phi z r - Phi z r'| ≤ L * |r - r'|)
    (Rmax K : ℝ) (hK : ∀ z r, r ≤ Rmax → |Phi z r| ≤ K)
    (k : ℕ) (u V : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (hV : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] V)
    (Vmax : ℝ≥0) (hVle : ∀ ω, V ω ≤ Vmax)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hage : ∀ ω ∈ A, ((u ω + V ω : ℝ≥0) : ℝ) ≤ Rmax) :
    ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + V ω},
        Phi ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
          ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ∂P =
      ∫ ω in A, davisHazardWindowIntegral S hflow Phi
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
          (u ω) (V ω) ∂P := by
  classical
  have hm : ((ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k :
      MeasurableSpace Ω)) ≤ mΩ :=
    (ξ.preJumpHistoryFiltration S hflow hf hr hξ initial).le k
  have hAm : MeasurableSet A := hm _ hA
  have hum : Measurable u := hu.mono hm le_rfl
  have hVm : Measurable V := hV.mono hm le_rfl
  have hhm : Measurable (ξ.holdingTime k) := hξ.holdingTime k
  have hWm : MeasurableSet {ω | u ω < ξ.holdingTime k ω ∧
      ξ.holdingTime k ω ≤ u ω + V ω} := by
    have hWeq : {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + V ω} =
        {ω | u ω < ξ.holdingTime k ω} \ {ω | u ω + V ω < ξ.holdingTime k ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
    exact hWeq ▸ (measurableSet_lt hum hhm).diff
      (measurableSet_lt (hum.add hVm) hhm)
  have hglobal := hlaw.setIntegral_holdingTime_density_randomWindow hcont hsurv
    (davisTruncatedProfile Phi Rmax)
    (measurable_davisTruncatedProfile hPhimeas Rmax)
    (continuous_davisTruncatedProfile hPhicont Rmax) L hL
    (abs_davisTruncatedProfile_sub_le hL hlip) K
    (abs_davisTruncatedProfile_le hK) k u V hu hV Vmax hVle A hA
  have hLHS : ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + V ω},
      davisTruncatedProfile Phi Rmax
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
        ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ∂P =
      ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + V ω},
      Phi ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
        ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ∂P := by
    refine setIntegral_congr_fun (hAm.inter hWm) fun ω hω => ?_
    have hle : ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ≤ Rmax := by
      refine le_trans ?_ (hage ω hω.1)
      exact_mod_cast hω.2.2
    exact davisTruncatedProfile_eq_of_le Phi _ hle
  have hRHS : ∫ ω in A, davisHazardWindowIntegral S hflow
        (davisTruncatedProfile Phi Rmax)
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
          (u ω) (V ω) ∂P =
      ∫ ω in A, davisHazardWindowIntegral S hflow Phi
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
          (u ω) (V ω) ∂P := by
    refine setIntegral_congr_fun hAm fun ω hω => ?_
    exact davisHazardWindowIntegral_davisTruncatedProfile S hflow Phi _ (u ω)
      (V ω) (hage ω hω)
  rw [hLHS, hRHS] at hglobal
  exact hglobal

end SHS
