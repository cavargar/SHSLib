import SHSLib.Core.DavisSegmentHazardRiemann
import SHSLib.Core.DavisConditionalHoldingWindow

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The density form of the conditional holding-time law

The window law evaluates the mean of a history-measurable weight over the event
that the holding time of the running segment falls in an age window.  The
conditional law of the *completed* part of the one-segment contribution needs
more: the weight there is the realized value of a profile *at the realized
holding time*, so the window law must be upgraded to a statement about the
conditional **density** of the holding time,

`∫_{A ∩ {u < h_k ≤ u+T}} Φ(h_k) = ∫_A ∫_u^{u+T} haz(s) · Φ(s) ds`.

The proof refines the window into `M` cells of mesh `δ = T/M`.  On each cell the
window law replaces the realized value of the profile by its value at the left
endpoint of the cell, at a cost of at most `L·δ` — the profile is Lipschitz —
and the resulting step-function sum is exactly the Riemann sum of the previous
module, which is within `L·δ` of the hazard average.  Both errors vanish as the
mesh is refined, so the two sides agree.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The hazard average over an age window -/

/-- The hazard average of a profile over the age window `[u, u+T]`. -/
def davisHazardWindowIntegral (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (Phi : DavisState Q n → ℝ → ℝ) (z : DavisState Q n) (u T : ℝ≥0) : ℝ :=
  ∫ s in Set.Icc (u : ℝ) ((u + T : ℝ≥0) : ℝ),
    davisSegmentHazardDensity S hflow z s * Phi z s

/-- The uniform grid of mesh `T/M` spanning the window `[u, u+T]` ends at
`u+T`. -/
theorem davisHazardGridPoint_div (u T : ℝ≥0) {M : ℕ} (hM : M ≠ 0) :
    davisHazardGridPoint u (T / (M : ℝ≥0)) M = u + T := by
  unfold davisHazardGridPoint
  have hM' : ((M : ℝ≥0)) ≠ 0 := Nat.cast_ne_zero.mpr hM
  rw [mul_div_cancel₀ _ hM']

/-- **The Riemann estimate on the window grid.**  The hazard average over the
window differs from the Riemann sum of mesh `T/M` by at most `L·T/M`. -/
theorem abs_davisHazardWindowIntegral_sub_riemannSum_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (Phi : DavisState Q n → ℝ → ℝ) (hPhicont : ∀ z, Continuous (Phi z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |Phi z r - Phi z r'| ≤ L * |r - r'|)
    (z : DavisState Q n) (u T : ℝ≥0) {M : ℕ} (hM : M ≠ 0) :
    |davisHazardWindowIntegral S hflow Phi z u T -
        davisHazardRiemannSum S hflow z (Phi z) u (T / (M : ℝ≥0)) M| ≤
      L * ((T : ℝ) / (M : ℝ)) := by
  have h := abs_integral_Icc_hazardDensity_mul_sub_riemannSum_le' S hflow hcont
    z (Phi z) (hPhicont z) L hL (hlip z) u (T / (M : ℝ≥0)) M
  rw [davisHazardGridPoint_div u T hM] at h
  have hcast : ((T / (M : ℝ≥0) : ℝ≥0) : ℝ) = (T : ℝ) / (M : ℝ) := by
    push_cast
    ring
  rw [hcast] at h
  exact h

/-- The hazard average of a bounded profile is bounded by the same constant. -/
theorem abs_davisHazardWindowIntegral_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (Phi : DavisState Q n → ℝ → ℝ) (hPhicont : ∀ z, Continuous (Phi z))
    (K : ℝ) (hK : ∀ z r, |Phi z r| ≤ K)
    (z : DavisState Q n) (u T : ℝ≥0) :
    |davisHazardWindowIntegral S hflow Phi z u T| ≤ K := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK z 0)
  have hdens_cont : Continuous (davisSegmentHazardDensity S hflow z) :=
    continuous_davisSegmentHazardDensity S hflow hcont z
  have hdens_nonneg : ∀ s : ℝ, 0 ≤ davisSegmentHazardDensity S hflow z s := by
    intro s
    unfold davisSegmentHazardDensity
    exact mul_nonneg (totalIntensity_nonneg S _) (Real.exp_nonneg _)
  have hle : u ≤ u + T := le_self_add
  have hmass := integral_Icc_davisSegmentHazardDensity S hflow hcont z u (u + T)
    hle
  have hmass_le : davisSegmentSurvivor S hflow z u -
      davisSegmentSurvivor S hflow z (u + T) ≤ 1 := by
    have h2 := davisSegmentSurvivor_le_one S hflow z u
    have h3 := davisSegmentSurvivor_pos S hflow z (u + T)
    linarith
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
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left hmass_le hK0
    _ = K := mul_one K

/-! ## Measurability of the hazard average -/

omit [MeasurableSingletonClass Q] in
/-- The hazard density is jointly measurable in the state and the age. -/
theorem measurable_davisSegmentHazardDensity_uncurry
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    [S.IntensitiesMeasurable]
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2) :
    Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentHazardDensity S hflow p.1 p.2 := by
  have hflowmeas : Measurable fun p : DavisState Q n × ℝ =>
      davisFlow S hflow p.2.toNNReal p.1 :=
    hf.measurable_joint.comp
      ((measurable_snd.real_toNNReal).prodMk measurable_fst)
  have htot : Measurable fun z : DavisState Q n => S.totalIntensity z := by
    unfold totalIntensity
    exact Finset.measurable_sum _ fun i _ => IntensitiesMeasurable.measurable i
  have h1 : Measurable fun p : DavisState Q n × ℝ =>
      S.totalIntensity (davisFlow S hflow p.2.toNNReal p.1) :=
    htot.comp hflowmeas
  have h2 : Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentSurvivor S hflow p.1 p.2.toNNReal :=
    hsurv.comp (measurable_fst.prodMk measurable_snd.real_toNNReal)
  exact h1.mul h2

omit [MeasurableSingletonClass Q] in
/-- The hazard average over a window is jointly measurable in the state and the
starting age. -/
theorem measurable_davisHazardWindowIntegral
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    [S.IntensitiesMeasurable]
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (Phi : DavisState Q n → ℝ → ℝ)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ => Phi p.1 p.2)
    (T : ℝ≥0) :
    Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisHazardWindowIntegral S hflow Phi p.1 p.2 T := by
  classical
  set f : (DavisState Q n × ℝ≥0) × ℝ → ℝ := fun p =>
    Set.indicator (Set.Icc ((p.1.2 : ℝ)) ((p.1.2 + T : ℝ≥0) : ℝ))
      (fun s => davisSegmentHazardDensity S hflow p.1.1 s * Phi p.1.1 s) p.2
    with hfdef
  have hsetm : MeasurableSet {p : (DavisState Q n × ℝ≥0) × ℝ |
      ((p.1.2 : ℝ)) ≤ p.2 ∧ p.2 ≤ ((p.1.2 + T : ℝ≥0) : ℝ)} := by
    have hm1 : Measurable fun p : (DavisState Q n × ℝ≥0) × ℝ =>
        ((p.1.2 : ℝ)) :=
      measurable_coe_nnreal_real.comp (measurable_fst.snd)
    have hm2 : Measurable fun p : (DavisState Q n × ℝ≥0) × ℝ =>
        (((p.1.2 + T : ℝ≥0)) : ℝ) :=
      measurable_coe_nnreal_real.comp ((measurable_fst.snd).add measurable_const)
    exact (measurableSet_le hm1 measurable_snd).inter
      (measurableSet_le measurable_snd hm2)
  have hgm : Measurable fun p : (DavisState Q n × ℝ≥0) × ℝ =>
      davisSegmentHazardDensity S hflow p.1.1 p.2 * Phi p.1.1 p.2 :=
    ((measurable_davisSegmentHazardDensity_uncurry S hflow hf hsurv).comp
        ((measurable_fst.fst).prodMk measurable_snd)).mul
      (hPhimeas.comp ((measurable_fst.fst).prodMk measurable_snd))
  have hfm : Measurable f := by
    have : f = fun p => if ((p.1.2 : ℝ)) ≤ p.2 ∧ p.2 ≤ ((p.1.2 + T : ℝ≥0) : ℝ)
        then davisSegmentHazardDensity S hflow p.1.1 p.2 * Phi p.1.1 p.2
        else 0 := by
      funext p
      by_cases hp : ((p.1.2 : ℝ)) ≤ p.2 ∧ p.2 ≤ ((p.1.2 + T : ℝ≥0) : ℝ)
      · rw [if_pos hp, hfdef]
        exact Set.indicator_of_mem (Set.mem_Icc.mpr hp) _
      · rw [if_neg hp, hfdef]
        exact Set.indicator_of_notMem (fun hmem => hp (Set.mem_Icc.mp hmem)) _
    rw [this]
    exact Measurable.ite hsetm hgm measurable_const
  have hint : ∀ p : DavisState Q n × ℝ≥0,
      davisHazardWindowIntegral S hflow Phi p.1 p.2 T = ∫ s : ℝ, f (p, s) := by
    intro p
    rw [davisHazardWindowIntegral, ← MeasureTheory.integral_indicator
      measurableSet_Icc]
  simp only [hint]
  exact (hfm.stronglyMeasurable.integral_prod_right').measurable

/-! ## The pathwise cell decomposition -/

/-- Off the window, every cell contribution vanishes. -/
theorem davisHazardCellSum_eq_zero (u delta : ℝ≥0) (M : ℕ) (h : ℝ≥0)
    (c : ℕ → ℝ)
    (hh : ¬ (u < h ∧ h ≤ davisHazardGridPoint u delta M)) :
    ∑ i ∈ Finset.range M,
      (if davisHazardGridPoint u delta i < h ∧
          h ≤ davisHazardGridPoint u delta (i + 1) then c i else 0) = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases hcell : davisHazardGridPoint u delta i < h ∧
      h ≤ davisHazardGridPoint u delta (i + 1)
  · exact absurd ⟨lt_of_le_of_lt (by
        simpa using davisHazardGridPoint_mono u delta (Nat.zero_le i)) hcell.1,
      le_trans hcell.2 (davisHazardGridPoint_mono u delta
        (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))⟩ hh
  · rw [if_neg hcell]

/-- **The cell estimate.**  On the window, the value of a Lipschitz profile at
a point differs from the value at the left endpoint of the cell containing that
point by at most the Lipschitz constant times the mesh. -/
theorem abs_sub_davisHazardCellSum_le (phi : ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ r r' : ℝ, |phi r - phi r'| ≤ L * |r - r'|)
    (u delta : ℝ≥0) (M : ℕ) (h : ℝ≥0)
    (hh : u < h ∧ h ≤ davisHazardGridPoint u delta M) :
    |phi (h : ℝ) - ∑ i ∈ Finset.range M,
        (if davisHazardGridPoint u delta i < h ∧
            h ≤ davisHazardGridPoint u delta (i + 1)
          then phi ((davisHazardGridPoint u delta i : ℝ≥0) : ℝ) else 0)| ≤
      L * (delta : ℝ) := by
  induction M with
  | zero =>
    exact absurd (lt_of_lt_of_le hh.1 (by simpa using hh.2)) (lt_irrefl _)
  | succ M ih =>
    rw [Finset.sum_range_succ]
    by_cases hle : h ≤ davisHazardGridPoint u delta M
    · have hlast : ¬ (davisHazardGridPoint u delta M < h ∧
          h ≤ davisHazardGridPoint u delta (M + 1)) := fun hc =>
        absurd hle (not_le.2 hc.1)
      rw [if_neg hlast, add_zero]
      exact ih ⟨hh.1, hle⟩
    · have hgt : davisHazardGridPoint u delta M < h := not_le.1 hle
      have hzero := davisHazardCellSum_eq_zero u delta M h
        (fun i => phi ((davisHazardGridPoint u delta i : ℝ≥0) : ℝ))
        (fun hc => hle hc.2)
      rw [hzero, if_pos ⟨hgt, hh.2⟩, zero_add]
      have hdist : |(h : ℝ) -
          ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ)| ≤ (delta : ℝ) := by
        have h1 : ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ) ≤ (h : ℝ) := by
          exact_mod_cast hgt.le
        have h2 : (h : ℝ) ≤
            ((davisHazardGridPoint u delta (M + 1) : ℝ≥0) : ℝ) := by
          exact_mod_cast hh.2
        rw [abs_of_nonneg (by linarith)]
        have h3 := davisHazardGridPoint_succ_sub u delta M
        linarith
      calc |phi (h : ℝ) -
            phi ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ)|
          ≤ L * |(h : ℝ) -
              ((davisHazardGridPoint u delta M : ℝ≥0) : ℝ)| := hlip _ _
        _ ≤ L * (delta : ℝ) := mul_le_mul_of_nonneg_left hdist hL

/-! ## A uniform estimate for set integrals -/

/-- Two set integrals whose integrands differ by at most a constant differ by
at most that constant times the mass of the set. -/
theorem abs_setIntegral_sub_le_of_forall {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f g : Ω → ℝ) (A : Set Ω)
    (hAm : MeasurableSet A) (hf : IntegrableOn f A P) (hg : IntegrableOn g A P)
    (c : ℝ) (hc : ∀ ω, |f ω - g ω| ≤ c) :
    |∫ ω in A, f ω ∂P - ∫ ω in A, g ω ∂P| ≤ c * (P A).toReal := by
  rw [← integral_sub hf hg]
  calc |∫ ω in A, (f ω - g ω) ∂P| ≤ ∫ ω in A, |f ω - g ω| ∂P := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (μ := P.restrict A) (f := fun ω => f ω - g ω)
    _ ≤ ∫ _ω in A, c ∂P :=
        setIntegral_mono_on (hf.sub hg).abs
          ((integrable_const c).integrableOn)
          hAm (fun ω _ => hc ω)
    _ = c * (P A).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
        rfl

/-! ## The density form of the conditional holding-time law -/

/-- **The density form of the conditional holding-time law.**  On a history
event, the mean of a Lipschitz profile evaluated at the realized holding time,
restricted to the event that the holding time falls in the age window
`(u, u+T]`, is the mean of the hazard average of the profile over that
window. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_holdingTime_density
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
    (K : ℝ) (hK : ∀ z r, |Phi z r| ≤ K)
    (k : ℕ) (u : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (T : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + T},
        Phi ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
          ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ∂P =
      ∫ ω in A, davisHazardWindowIntegral S hflow Phi
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState) (u ω) T ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  have hm : (F k : MeasurableSpace Ω) ≤ mΩ := F.le k
  have hAm : MeasurableSet A := hm _ hA
  set z : Ω → DavisState Q n :=
    fun ω => (davisPreJumpHistory S hflow ξ initial k ω).currentState with hz
  have hzF : Measurable[F k] z :=
    (DavisPreJumpHistory.measurable_currentState k).comp
      (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial k)
  have hzm : Measurable z := hzF.mono hm le_rfl
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK initial 0)
  set h : Ω → ℝ≥0 := ξ.holdingTime k with hhdef
  have hhm : Measurable h := hξ.holdingTime k
  set W : Set Ω := {ω | u ω < h ω ∧ h ω ≤ u ω + T} with hW
  have hum : Measurable u := hu.mono hm le_rfl
  have hWeq : W = {ω | u ω < h ω} \ {ω | u ω + T < h ω} := by
    ext ω
    simp only [hW, Set.mem_setOf_eq, Set.mem_diff, not_lt]
  have hWm : MeasurableSet W :=
    hWeq ▸ (measurableSet_lt hum hhm).diff
      (measurableSet_lt (hum.add measurable_const) hhm)
  -- the two sides
  set lhs : ℝ := ∫ ω in A ∩ W, Phi (z ω) ((h ω : ℝ≥0) : ℝ) ∂P with hlhs
  set rhs : ℝ := ∫ ω in A, davisHazardWindowIntegral S hflow Phi (z ω) (u ω) T ∂P
    with hrhs
  -- integrability of the two integrands
  have hlhsfun : Measurable fun ω => Phi (z ω) ((h ω : ℝ≥0) : ℝ) :=
    hPhimeas.comp (hzm.prodMk (measurable_coe_nnreal_real.comp hhm))
  have hwinfun : Measurable fun ω =>
      davisHazardWindowIntegral S hflow Phi (z ω) (u ω) T :=
    (measurable_davisHazardWindowIntegral S hflow hf hsurv Phi hPhimeas T).comp
      (hzm.prodMk (hu.mono hm le_rfl))
  have hboundint : ∀ (f : Ω → ℝ), Measurable f → ∀ (c : ℝ), (∀ ω, |f ω| ≤ c) →
      ∀ B : Set Ω, IntegrableOn f B P := by
    intro f hfm c hfc B
    refine Integrable.integrableOn ?_
    refine (integrable_const (max c 0)).mono' hfm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact le_trans (hfc ω) (le_max_left c 0)
  -- the indicator form of the left-hand side
  have hlhs_ind : lhs = ∫ ω in A,
      W.indicator (fun ω => Phi (z ω) ((h ω : ℝ≥0) : ℝ)) ω ∂P := by
    rw [hlhs, MeasureTheory.setIntegral_indicator hWm]
  -- the estimate at mesh `T/M`
  have key : ∀ M : ℕ, M ≠ 0 →
      |lhs - rhs| ≤ 2 * (L * ((T : ℝ) / (M : ℝ))) * (P A).toReal := by
    intro M hM
    set delta : ℝ≥0 := T / (M : ℝ≥0) with hdelta
    have hdeltacast : (delta : ℝ) = (T : ℝ) / (M : ℝ) := by
      rw [hdelta]; push_cast; ring
    have hLd : 0 ≤ L * (delta : ℝ) := mul_nonneg hL delta.coe_nonneg
    set pt : ℕ → Ω → ℝ≥0 :=
      fun i ω => davisHazardGridPoint (u ω) delta i with hpt
    have hptF : ∀ i, Measurable[F k] (pt i) := by
      intro i
      show Measurable[F k] fun ω => u ω + (i : ℝ≥0) * delta
      exact hu.add measurable_const
    have hptM : ∀ ω, pt M ω = u ω + T := fun ω =>
      davisHazardGridPoint_div (u ω) T hM
    -- the step function
    set psi : Ω → ℝ := fun ω => ∑ i ∈ Finset.range M,
      (if pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
        then Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) else 0) with hpsi
    have hcellm : ∀ i, MeasurableSet {ω | pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω} := by
      intro i
      have hEq : {ω | pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω} =
          {ω | pt i ω < h ω} \ {ω | pt (i + 1) ω < h ω} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
      exact hEq ▸ (measurableSet_lt ((hptF i).mono hm le_rfl) hhm).diff
        (measurableSet_lt ((hptF (i + 1)).mono hm le_rfl) hhm)
    have hwF : ∀ i, Measurable[F k] fun ω => Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) :=
      fun i => hPhimeas.comp
        (hzF.prodMk (measurable_coe_nnreal_real.comp (hptF i)))
    have hwm : ∀ i, Measurable fun ω => Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) :=
      fun i => (hwF i).mono hm le_rfl
    have hpsim : Measurable psi := by
      rw [hpsi]
      refine Finset.measurable_sum _ fun i _ => ?_
      exact Measurable.ite (hcellm i) (hwm i) measurable_const
    -- Step 1: the left-hand side is within `L·δ` of the mean of `psi`
    have hstep1pt : ∀ ω,
        |W.indicator (fun ω => Phi (z ω) ((h ω : ℝ≥0) : ℝ)) ω - psi ω| ≤
          L * (delta : ℝ) := by
      intro ω
      have hpsiω : psi ω = ∑ i ∈ Finset.range M,
          (if davisHazardGridPoint (u ω) delta i < h ω ∧
              h ω ≤ davisHazardGridPoint (u ω) delta (i + 1)
            then Phi (z ω)
              ((davisHazardGridPoint (u ω) delta i : ℝ≥0) : ℝ) else 0) := by
        simp only [hpsi, hpt]
      by_cases hωW : ω ∈ W
      · rw [Set.indicator_of_mem hωW, hpsiω]
        refine abs_sub_davisHazardCellSum_le (Phi (z ω)) L hL (hlip (z ω))
          (u ω) delta M (h ω) ?_
        refine ⟨hωW.1, ?_⟩
        rw [show davisHazardGridPoint (u ω) delta M = pt M ω from rfl, hptM ω]
        exact hωW.2
      · rw [Set.indicator_of_notMem hωW, hpsiω]
        have hnot : ¬ (u ω < h ω ∧
            h ω ≤ davisHazardGridPoint (u ω) delta M) := by
          intro hc
          exact hωW ⟨hc.1, by rw [← hptM ω]; exact hc.2⟩
        rw [davisHazardCellSum_eq_zero (u ω) delta M (h ω)
          (fun i => Phi (z ω) ((davisHazardGridPoint (u ω) delta i : ℝ≥0) : ℝ))
          hnot]
        simpa using hLd
    have hstep1 : |lhs - ∫ ω in A, psi ω ∂P| ≤
        L * (delta : ℝ) * (P A).toReal := by
      rw [hlhs_ind]
      refine abs_setIntegral_sub_le_of_forall P _ _ A hAm ?_ ?_ _ hstep1pt
      · exact hboundint _ (hlhsfun.indicator hWm) K (fun ω => by
          by_cases hωW : ω ∈ W
          · rw [Set.indicator_of_mem hωW]; exact hK _ _
          · rw [Set.indicator_of_notMem hωW, abs_zero]; exact hK0) A
      · refine hboundint _ hpsim ((M : ℝ) * K) (fun ω => ?_) A
        rw [hpsi]
        calc |∑ i ∈ Finset.range M,
              (if pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
                then Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) else 0)|
            ≤ ∑ i ∈ Finset.range M,
              |(if pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
                then Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) else 0)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ Finset.range M, K := by
              refine Finset.sum_le_sum fun i _ => ?_
              by_cases hc : pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
              · rw [if_pos hc]; exact hK _ _
              · rw [if_neg hc, abs_zero]; exact hK0
          _ = (M : ℝ) * K := by rw [Finset.sum_const, Finset.card_range,
                nsmul_eq_mul]
    -- Step 2: the mean of `psi` is the mean of the Riemann sum
    have hstep2 : ∫ ω in A, psi ω ∂P =
        ∫ ω in A, davisHazardRiemannSum S hflow (z ω) (Phi (z ω)) (u ω) delta M
          ∂P := by
      have hsum1 : ∫ ω in A, psi ω ∂P =
          ∑ i ∈ Finset.range M, ∫ ω in A,
            (if pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
              then Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) else 0) ∂P := by
        rw [hpsi, integral_finset_sum]
        intro i _
        refine hboundint _ (Measurable.ite (hcellm i) (hwm i) measurable_const)
          K (fun ω => ?_) A
        by_cases hc : pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
        · rw [if_pos hc]; exact hK _ _
        · rw [if_neg hc, abs_zero]; exact hK0
      have hcell : ∀ i,
          ∫ ω in A, (if pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
              then Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) else 0) ∂P =
            ∫ ω in A, Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) *
              (davisSegmentSurvivor S hflow (z ω) (pt i ω) -
                davisSegmentSurvivor S hflow (z ω) (pt (i + 1) ω)) ∂P := by
        intro i
        have hind : ∫ ω in A, (if pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
              then Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) else 0) ∂P =
            ∫ ω in A ∩ {ω | pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω},
              Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) ∂P := by
          rw [← MeasureTheory.setIntegral_indicator (hcellm i)]
          refine setIntegral_congr_fun hAm fun ω _ => ?_
          by_cases hc : pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω
          · rw [if_pos hc, Set.indicator_of_mem
              (show ω ∈ {ω | pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω} from hc)]
          · rw [if_neg hc, Set.indicator_of_notMem
              (show ω ∉ {ω | pt i ω < h ω ∧ h ω ≤ pt (i + 1) ω} from hc)]
        rw [hind]
        exact hlaw.setIntegral_holdingTime_window_weighted hcont hsurv k
          (pt i) (pt (i + 1)) (hptF i) (hptF (i + 1))
          (fun ω => davisHazardGridPoint_mono (u ω) delta (Nat.le_succ i))
          A hA (fun ω => Phi (z ω) ((pt i ω : ℝ≥0) : ℝ)) (hwF i) K
          (fun ω => hK _ _)
      rw [hsum1]
      simp_rw [hcell]
      rw [← integral_finset_sum]
      · rfl
      · intro i _
        refine hboundint _ ((hwm i).mul (((hsurv.comp
            (hzm.prodMk ((hptF i).mono hm le_rfl))).sub
              (hsurv.comp (hzm.prodMk ((hptF (i + 1)).mono hm le_rfl))))))
          (K * 1) (fun ω => ?_) A
        rw [abs_mul]
        have h1 : |davisSegmentSurvivor S hflow (z ω) (pt i ω) -
            davisSegmentSurvivor S hflow (z ω) (pt (i + 1) ω)| ≤ 1 := by
          have ha := davisSegmentSurvivor_pos S hflow (z ω) (pt i ω)
          have hb := davisSegmentSurvivor_le_one S hflow (z ω) (pt i ω)
          have hc := davisSegmentSurvivor_pos S hflow (z ω) (pt (i + 1) ω)
          have hd := davisSegmentSurvivor_le_one S hflow (z ω) (pt (i + 1) ω)
          rw [abs_le]
          constructor <;> linarith
        exact mul_le_mul (hK _ _) h1 (abs_nonneg _) hK0
    -- Step 3: the Riemann sum is within `L·δ` of the hazard average
    have hstep3 : |(∫ ω in A, davisHazardRiemannSum S hflow (z ω) (Phi (z ω))
          (u ω) delta M ∂P) - rhs| ≤ L * (delta : ℝ) * (P A).toReal := by
      have hRm : Measurable fun ω =>
          davisHazardRiemannSum S hflow (z ω) (Phi (z ω)) (u ω) delta M := by
        rw [show (fun ω => davisHazardRiemannSum S hflow (z ω) (Phi (z ω))
            (u ω) delta M) = fun ω => ∑ i ∈ Finset.range M,
              Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) *
                (davisSegmentSurvivor S hflow (z ω) (pt i ω) -
                  davisSegmentSurvivor S hflow (z ω) (pt (i + 1) ω)) from rfl]
        refine Finset.measurable_sum _ fun i _ => ?_
        exact (hwm i).mul (((hsurv.comp
          (hzm.prodMk ((hptF i).mono hm le_rfl))).sub
            (hsurv.comp (hzm.prodMk ((hptF (i + 1)).mono hm le_rfl)))))
      have hRbound : ∀ ω, |davisHazardRiemannSum S hflow (z ω) (Phi (z ω))
          (u ω) delta M| ≤ (M : ℝ) * K := by
        intro ω
        calc |davisHazardRiemannSum S hflow (z ω) (Phi (z ω)) (u ω) delta M|
            ≤ ∑ i ∈ Finset.range M,
              |Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) *
                (davisSegmentSurvivor S hflow (z ω) (pt i ω) -
                  davisSegmentSurvivor S hflow (z ω) (pt (i + 1) ω))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ Finset.range M, K := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              have h1 : |davisSegmentSurvivor S hflow (z ω) (pt i ω) -
                  davisSegmentSurvivor S hflow (z ω) (pt (i + 1) ω)| ≤ 1 := by
                have ha := davisSegmentSurvivor_pos S hflow (z ω) (pt i ω)
                have hb := davisSegmentSurvivor_le_one S hflow (z ω) (pt i ω)
                have hc := davisSegmentSurvivor_pos S hflow (z ω)
                  (pt (i + 1) ω)
                have hd := davisSegmentSurvivor_le_one S hflow (z ω)
                  (pt (i + 1) ω)
                rw [abs_le]
                constructor <;> linarith
              calc |Phi (z ω) ((pt i ω : ℝ≥0) : ℝ)| * _
                  ≤ K * 1 := mul_le_mul (hK _ _) h1 (abs_nonneg _) hK0
                _ = K := mul_one K
          _ = (M : ℝ) * K := by rw [Finset.sum_const, Finset.card_range,
                nsmul_eq_mul]
      rw [hrhs]
      refine abs_setIntegral_sub_le_of_forall P _ _ A hAm
        (hboundint _ hRm ((M : ℝ) * K) hRbound A)
        (hboundint _ hwinfun K (fun ω => abs_davisHazardWindowIntegral_le S
          hflow hcont Phi hPhicont K hK (z ω) (u ω) T) A) _ ?_
      intro ω
      have h2 := abs_davisHazardWindowIntegral_sub_riemannSum_le S hflow hcont
        Phi hPhicont L hL hlip (z ω) (u ω) T hM
      rw [abs_sub_comm] at h2
      rw [hdeltacast]
      exact h2
    -- combine
    have hcomb : |lhs - rhs| ≤ L * (delta : ℝ) * (P A).toReal +
        L * (delta : ℝ) * (P A).toReal := by
      have htri : |lhs - rhs| ≤ |lhs - ∫ ω in A, psi ω ∂P| +
          |(∫ ω in A, psi ω ∂P) - rhs| := by
        calc |lhs - rhs| = |(lhs - ∫ ω in A, psi ω ∂P) +
              ((∫ ω in A, psi ω ∂P) - rhs)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      refine le_trans htri (add_le_add hstep1 ?_)
      rw [hstep2]
      exact hstep3
    calc |lhs - rhs| ≤ L * (delta : ℝ) * (P A).toReal +
          L * (delta : ℝ) * (P A).toReal := hcomb
      _ = 2 * (L * ((T : ℝ) / (M : ℝ))) * (P A).toReal := by
          rw [hdeltacast]; ring
  -- pass to the limit in the mesh
  by_contra hne
  have hD : 0 < |lhs - rhs| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set C : ℝ := (P A).toReal with hC
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  obtain ⟨M, hMgt⟩ := exists_nat_gt ((2 * L * (T : ℝ) * C) / |lhs - rhs|)
  have hM1 : max M 1 ≠ 0 := by positivity
  have hMreal : (0 : ℝ) < ((max M 1 : ℕ) : ℝ) := by
    have : 0 < max M 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right M 1)
    exact_mod_cast this
  have hkey := key (max M 1) hM1
  have hMge : ((M : ℕ) : ℝ) ≤ ((max M 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left M 1
  have hbig : (2 * L * (T : ℝ) * C) / |lhs - rhs| < ((max M 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le hMgt hMge
  have hlt : 2 * L * (T : ℝ) * C < |lhs - rhs| * ((max M 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hD] at hbig
    linarith
  have hle : |lhs - rhs| * ((max M 1 : ℕ) : ℝ) ≤ 2 * L * (T : ℝ) * C := by
    have h1 : |lhs - rhs| ≤ 2 * (L * ((T : ℝ) / ((max M 1 : ℕ) : ℝ))) * C :=
      hkey
    have h2 : 2 * (L * ((T : ℝ) / ((max M 1 : ℕ) : ℝ))) * C =
        (2 * L * (T : ℝ) * C) / ((max M 1 : ℕ) : ℝ) := by
      field_simp
    rw [h2] at h1
    rw [← le_div_iff₀ hMreal]
    exact h1
  linarith

end SHS
