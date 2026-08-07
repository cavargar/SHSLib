import SHSLib.Core.DavisConditionalHoldingDensity

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The density law at a history-measurable window length

The density form of the conditional holding-time law integrates a Lipschitz
profile of the realized holding time over an age window `(u, u+T]` whose
*length* `T` is a constant.  For the contribution of a segment observed at the
random time at which it starts, the window length is itself random: it is the
age `t − T_N` the segment has reached, a quantity known once the history before
jump `N` is known.

This module removes the restriction.  The proof is the one of the constant-length
case, with the uniform grid of the window replaced by the grid whose cell
endpoints

`u(ω) + i · V(ω)/M`,   `i = 0, …, M`,

are themselves history-measurable random variables.  Every ingredient survives
the change:

* the window law of the conditional holding time already accepts random
  thresholds, so each cell is evaluated exactly as before;
* the Riemann estimate and the cell estimate are deterministic statements about
  one state and one window, so they may be applied at each sample point with
  that point's own window length;
* the error committed on a cell is `L · V(ω)/M ≤ L · Tmax/M`, uniformly in `ω`,
  as soon as the window length is bounded by `Tmax` — which it is, the window
  being contained in the observation horizon.

Letting the mesh go to zero then identifies the mean of the profile at the
realized holding time on the random window with the mean of the hazard average
over that window.

The module also records the joint measurability of the hazard average in all
three of its arguments — state, starting age and window length — which the
constant-length development only needed for the first two.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Joint measurability in state, starting age and window length -/

omit [MeasurableSingletonClass Q] in
/-- The hazard average over a window is jointly measurable in the state, the
starting age and the length of the window. -/
theorem measurable_davisHazardWindowIntegral_triple
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    [S.IntensitiesMeasurable]
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (Phi : DavisState Q n → ℝ → ℝ)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ => Phi p.1 p.2) :
    Measurable fun p : (DavisState Q n × ℝ≥0) × ℝ≥0 =>
      davisHazardWindowIntegral S hflow Phi p.1.1 p.1.2 p.2 := by
  classical
  set f : ((DavisState Q n × ℝ≥0) × ℝ≥0) × ℝ → ℝ := fun p =>
    Set.indicator (Set.Icc ((p.1.1.2 : ℝ)) ((p.1.1.2 + p.1.2 : ℝ≥0) : ℝ))
      (fun s => davisSegmentHazardDensity S hflow p.1.1.1 s * Phi p.1.1.1 s) p.2
    with hfdef
  have hsetm : MeasurableSet {p : ((DavisState Q n × ℝ≥0) × ℝ≥0) × ℝ |
      ((p.1.1.2 : ℝ)) ≤ p.2 ∧ p.2 ≤ ((p.1.1.2 + p.1.2 : ℝ≥0) : ℝ)} := by
    have hm1 : Measurable fun p : ((DavisState Q n × ℝ≥0) × ℝ≥0) × ℝ =>
        ((p.1.1.2 : ℝ)) :=
      measurable_coe_nnreal_real.comp (measurable_fst.fst.snd)
    have hm2 : Measurable fun p : ((DavisState Q n × ℝ≥0) × ℝ≥0) × ℝ =>
        (((p.1.1.2 + p.1.2 : ℝ≥0)) : ℝ) :=
      measurable_coe_nnreal_real.comp
        ((measurable_fst.fst.snd).add (measurable_fst.snd))
    exact (measurableSet_le hm1 measurable_snd).inter
      (measurableSet_le measurable_snd hm2)
  have hgm : Measurable fun p : ((DavisState Q n × ℝ≥0) × ℝ≥0) × ℝ =>
      davisSegmentHazardDensity S hflow p.1.1.1 p.2 * Phi p.1.1.1 p.2 :=
    ((measurable_davisSegmentHazardDensity_uncurry S hflow hf hsurv).comp
        ((measurable_fst.fst.fst).prodMk measurable_snd)).mul
      (hPhimeas.comp ((measurable_fst.fst.fst).prodMk measurable_snd))
  have hfm : Measurable f := by
    have hif : f = fun p => if ((p.1.1.2 : ℝ)) ≤ p.2 ∧
        p.2 ≤ ((p.1.1.2 + p.1.2 : ℝ≥0) : ℝ)
        then davisSegmentHazardDensity S hflow p.1.1.1 p.2 * Phi p.1.1.1 p.2
        else 0 := by
      funext p
      by_cases hp : ((p.1.1.2 : ℝ)) ≤ p.2 ∧ p.2 ≤ ((p.1.1.2 + p.1.2 : ℝ≥0) : ℝ)
      · rw [if_pos hp, hfdef]
        exact Set.indicator_of_mem (Set.mem_Icc.mpr hp) _
      · rw [if_neg hp, hfdef]
        exact Set.indicator_of_notMem (fun hmem => hp (Set.mem_Icc.mp hmem)) _
    rw [hif]
    exact Measurable.ite hsetm hgm measurable_const
  have hint : ∀ p : (DavisState Q n × ℝ≥0) × ℝ≥0,
      davisHazardWindowIntegral S hflow Phi p.1.1 p.1.2 p.2 = ∫ s : ℝ, f (p, s) := by
    intro p
    rw [davisHazardWindowIntegral, ← MeasureTheory.integral_indicator
      measurableSet_Icc]
  simp only [hint]
  exact (hfm.stronglyMeasurable.integral_prod_right').measurable

/-! ## The density law on a random window -/

set_option maxHeartbeats 4000000 in
/-- **The density form of the conditional holding-time law on a random
window.**  On a history event, the mean of a Lipschitz profile evaluated at the
realized holding time, restricted to the event that the holding time falls in
the age window `(u, u+V]` of history-measurable start and bounded
history-measurable length, is the mean of the hazard average of the profile
over that window. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_holdingTime_density_randomWindow
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
    (k : ℕ) (u V : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (hV : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] V)
    (Tmax : ℝ≥0) (hVle : ∀ ω, V ω ≤ Tmax)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    ∫ ω in A ∩ {ω | u ω < ξ.holdingTime k ω ∧
        ξ.holdingTime k ω ≤ u ω + V ω},
        Phi ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
          ((ξ.holdingTime k ω : ℝ≥0) : ℝ) ∂P =
      ∫ ω in A, davisHazardWindowIntegral S hflow Phi
        ((davisPreJumpHistory S hflow ξ initial k ω).currentState)
          (u ω) (V ω) ∂P := by
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
  set W : Set Ω := {ω | u ω < h ω ∧ h ω ≤ u ω + V ω} with hW
  have hum : Measurable u := hu.mono hm le_rfl
  have hVm : Measurable V := hV.mono hm le_rfl
  have hWeq : W = {ω | u ω < h ω} \ {ω | u ω + V ω < h ω} := by
    ext ω
    simp only [hW, Set.mem_setOf_eq, Set.mem_diff, not_lt]
  have hWm : MeasurableSet W :=
    hWeq ▸ (measurableSet_lt hum hhm).diff
      (measurableSet_lt (hum.add hVm) hhm)
  -- the two sides
  set lhs : ℝ := ∫ ω in A ∩ W, Phi (z ω) ((h ω : ℝ≥0) : ℝ) ∂P with hlhs
  set rhs : ℝ :=
    ∫ ω in A, davisHazardWindowIntegral S hflow Phi (z ω) (u ω) (V ω) ∂P
    with hrhs
  -- integrability of the two integrands
  have hlhsfun : Measurable fun ω => Phi (z ω) ((h ω : ℝ≥0) : ℝ) :=
    hPhimeas.comp (hzm.prodMk (measurable_coe_nnreal_real.comp hhm))
  have hwinfun : Measurable fun ω =>
      davisHazardWindowIntegral S hflow Phi (z ω) (u ω) (V ω) :=
    (measurable_davisHazardWindowIntegral_triple S hflow hf hsurv Phi
      hPhimeas).comp ((hzm.prodMk hum).prodMk hVm)
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
  -- the estimate at mesh `Tmax/M`
  have key : ∀ M : ℕ, M ≠ 0 →
      |lhs - rhs| ≤ 2 * (L * ((Tmax : ℝ) / (M : ℝ))) * (P A).toReal := by
    intro M hM
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      have : 0 < M := Nat.pos_of_ne_zero hM
      exact_mod_cast this
    set delta : Ω → ℝ≥0 := fun ω => V ω / (M : ℝ≥0) with hdelta
    have hdeltaF : Measurable[F k] delta := hV.div measurable_const
    have hdeltacast : ∀ ω, (delta ω : ℝ) = (V ω : ℝ) / (M : ℝ) := by
      intro ω
      rw [hdelta]; push_cast; ring
    have hdeltale : ∀ ω, (delta ω : ℝ) ≤ (Tmax : ℝ) / (M : ℝ) := by
      intro ω
      rw [hdeltacast ω]
      have hVc : (V ω : ℝ) ≤ (Tmax : ℝ) := by exact_mod_cast hVle ω
      gcongr
    have hLd : 0 ≤ L * ((Tmax : ℝ) / (M : ℝ)) :=
      mul_nonneg hL (div_nonneg Tmax.coe_nonneg hMpos.le)
    set pt : ℕ → Ω → ℝ≥0 :=
      fun i ω => davisHazardGridPoint (u ω) (delta ω) i with hpt
    have hptF : ∀ i, Measurable[F k] (pt i) := by
      intro i
      show Measurable[F k] fun ω => u ω + (i : ℝ≥0) * delta ω
      exact hu.add (measurable_const.mul hdeltaF)
    have hptM : ∀ ω, pt M ω = u ω + V ω := fun ω =>
      davisHazardGridPoint_div (u ω) (V ω) hM
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
    -- Step 1: the left-hand side is within `L·Tmax/M` of the mean of `psi`
    have hstep1pt : ∀ ω,
        |W.indicator (fun ω => Phi (z ω) ((h ω : ℝ≥0) : ℝ)) ω - psi ω| ≤
          L * ((Tmax : ℝ) / (M : ℝ)) := by
      intro ω
      have hpsiω : psi ω = ∑ i ∈ Finset.range M,
          (if davisHazardGridPoint (u ω) (delta ω) i < h ω ∧
              h ω ≤ davisHazardGridPoint (u ω) (delta ω) (i + 1)
            then Phi (z ω)
              ((davisHazardGridPoint (u ω) (delta ω) i : ℝ≥0) : ℝ) else 0) := by
        simp only [hpsi, hpt]
      have hstep : L * (delta ω : ℝ) ≤ L * ((Tmax : ℝ) / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (hdeltale ω) hL
      by_cases hωW : ω ∈ W
      · rw [Set.indicator_of_mem hωW, hpsiω]
        refine le_trans (abs_sub_davisHazardCellSum_le (Phi (z ω)) L hL
          (hlip (z ω)) (u ω) (delta ω) M (h ω) ?_) hstep
        refine ⟨hωW.1, ?_⟩
        rw [show davisHazardGridPoint (u ω) (delta ω) M = pt M ω from rfl,
          hptM ω]
        exact hωW.2
      · rw [Set.indicator_of_notMem hωW, hpsiω]
        have hnot : ¬ (u ω < h ω ∧
            h ω ≤ davisHazardGridPoint (u ω) (delta ω) M) := by
          intro hc
          exact hωW ⟨hc.1, by rw [← hptM ω]; exact hc.2⟩
        rw [davisHazardCellSum_eq_zero (u ω) (delta ω) M (h ω)
          (fun i => Phi (z ω)
            ((davisHazardGridPoint (u ω) (delta ω) i : ℝ≥0) : ℝ)) hnot]
        simpa using hLd
    have hstep1 : |lhs - ∫ ω in A, psi ω ∂P| ≤
        L * ((Tmax : ℝ) / (M : ℝ)) * (P A).toReal := by
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
        ∫ ω in A, davisHazardRiemannSum S hflow (z ω) (Phi (z ω)) (u ω)
          (delta ω) M ∂P := by
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
          (fun ω => davisHazardGridPoint_mono (u ω) (delta ω) (Nat.le_succ i))
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
    -- Step 3: the Riemann sum is within `L·Tmax/M` of the hazard average
    have hstep3 : |(∫ ω in A, davisHazardRiemannSum S hflow (z ω) (Phi (z ω))
          (u ω) (delta ω) M ∂P) - rhs| ≤
        L * ((Tmax : ℝ) / (M : ℝ)) * (P A).toReal := by
      have hRm : Measurable fun ω =>
          davisHazardRiemannSum S hflow (z ω) (Phi (z ω)) (u ω) (delta ω) M := by
        rw [show (fun ω => davisHazardRiemannSum S hflow (z ω) (Phi (z ω))
            (u ω) (delta ω) M) = fun ω => ∑ i ∈ Finset.range M,
              Phi (z ω) ((pt i ω : ℝ≥0) : ℝ) *
                (davisSegmentSurvivor S hflow (z ω) (pt i ω) -
                  davisSegmentSurvivor S hflow (z ω) (pt (i + 1) ω)) from rfl]
        refine Finset.measurable_sum _ fun i _ => ?_
        exact (hwm i).mul (((hsurv.comp
          (hzm.prodMk ((hptF i).mono hm le_rfl))).sub
            (hsurv.comp (hzm.prodMk ((hptF (i + 1)).mono hm le_rfl)))))
      have hRbound : ∀ ω, |davisHazardRiemannSum S hflow (z ω) (Phi (z ω))
          (u ω) (delta ω) M| ≤ (M : ℝ) * K := by
        intro ω
        calc |davisHazardRiemannSum S hflow (z ω) (Phi (z ω)) (u ω)
              (delta ω) M|
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
          hflow hcont Phi hPhicont K hK (z ω) (u ω) (V ω)) A) _ ?_
      intro ω
      have h2 := abs_davisHazardWindowIntegral_sub_riemannSum_le S hflow hcont
        Phi hPhicont L hL hlip (z ω) (u ω) (V ω) hM
      rw [abs_sub_comm] at h2
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (hdeltale ω) hL)
      rw [hdeltacast ω]
      exact h2
    -- combine
    have hcomb : |lhs - rhs| ≤ L * ((Tmax : ℝ) / (M : ℝ)) * (P A).toReal +
        L * ((Tmax : ℝ) / (M : ℝ)) * (P A).toReal := by
      have htri : |lhs - rhs| ≤ |lhs - ∫ ω in A, psi ω ∂P| +
          |(∫ ω in A, psi ω ∂P) - rhs| := by
        calc |lhs - rhs| = |(lhs - ∫ ω in A, psi ω ∂P) +
              ((∫ ω in A, psi ω ∂P) - rhs)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      refine le_trans htri (add_le_add hstep1 ?_)
      rw [hstep2]
      exact hstep3
    calc |lhs - rhs| ≤ L * ((Tmax : ℝ) / (M : ℝ)) * (P A).toReal +
          L * ((Tmax : ℝ) / (M : ℝ)) * (P A).toReal := hcomb
      _ = 2 * (L * ((Tmax : ℝ) / (M : ℝ))) * (P A).toReal := by ring
  -- pass to the limit in the mesh
  by_contra hne
  have hD : 0 < |lhs - rhs| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set C : ℝ := (P A).toReal with hC
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  obtain ⟨M, hMgt⟩ := exists_nat_gt ((2 * L * (Tmax : ℝ) * C) / |lhs - rhs|)
  have hM1 : max M 1 ≠ 0 := by positivity
  have hMreal : (0 : ℝ) < ((max M 1 : ℕ) : ℝ) := by
    have : 0 < max M 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right M 1)
    exact_mod_cast this
  have hkey := key (max M 1) hM1
  have hMge : ((M : ℕ) : ℝ) ≤ ((max M 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left M 1
  have hbig : (2 * L * (Tmax : ℝ) * C) / |lhs - rhs| < ((max M 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le hMgt hMge
  have hlt : 2 * L * (Tmax : ℝ) * C < |lhs - rhs| * ((max M 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hD] at hbig
    linarith
  have hle : |lhs - rhs| * ((max M 1 : ℕ) : ℝ) ≤ 2 * L * (Tmax : ℝ) * C := by
    have h1 : |lhs - rhs| ≤ 2 * (L * ((Tmax : ℝ) / ((max M 1 : ℕ) : ℝ))) * C :=
      hkey
    have h2 : 2 * (L * ((Tmax : ℝ) / ((max M 1 : ℕ) : ℝ))) * C =
        (2 * L * (Tmax : ℝ) * C) / ((max M 1 : ℕ) : ℝ) := by
      field_simp
    rw [h2] at h1
    rw [← le_div_iff₀ hMreal]
    exact h1
  linarith

end SHS
