import SHSLib.Core.DavisConditionalHoldingWindow
import SHSLib.Core.DavisConditionalChannelIntegral
import SHSLib.Core.DavisOneStepLaw

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The weighted channel identity and the conditional mean of a reset

The conditional channel law states that, given the history and the newly
revealed holding time, the mark of the next jump is drawn from the normalized
intensity weights at the pre-jump state.  It is phrased as an identity between
the measure of an event and an integral of the normalized weight, and has
already been upgraded to test functions of the mark *alone*.

The conditional law of the *completed* part of the one-segment contribution
needs its weighted form, in which the value attached to a mark may itself
depend on the pre-channel information:

`∫_{E ∩ {mark_k = ℓ}} w = ∫_E w · p_ℓ(z⁻_k)`,

together with the consequence obtained by summing over the marks: on every
pre-channel event, the realized increment of a bounded test function across the
reset has the same mean as the *normalized expected* reset increment at the
pre-jump state,

`∫_E w · (g(reset_{mark_k}(z⁻_k)) − g(z⁻_k)) = ∫_E w · E[Δg](z⁻_k)`.

This is the channel half of the completed-part conditional law; the holding
time half is the window law of the previous module.

The passage from sets to weights is the same measure-theoretic argument as for
the survivor identity: the restriction of `P` to the mark event and `P`
weighted by the normalized channel weight agree on the pre-channel σ-algebra,
hence integrate every pre-channel measurable function identically.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The pre-jump state is the history state flowed for the realized holding
time. -/
theorem davisStateBeforeJump_eq_stateBeforeNextJump
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n) (k : ℕ) (ω : Ω) :
    davisStateBeforeJump S hflow ξ initial k ω =
      (davisPreJumpHistory S hflow ξ initial k ω).stateBeforeNextJump S hflow
        (ξ.holdingTime k ω) := rfl

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Normalized channel weights are at most one. -/
theorem davisChannelProbability_le_one (S : SHS Q n m)
    (z : DavisState Q n) (ℓ : Fin m) :
    davisChannelProbability S z ℓ ≤ 1 := by
  unfold davisChannelProbability
  rcases eq_or_lt_of_le (totalIntensity_nonneg S z) with hz | hz
  · rw [← hz, div_zero]; norm_num
  · rw [div_le_one hz, totalIntensity]
    exact Finset.single_le_sum
      (fun i _ => S.intensity_nonneg i z.1 z.2.1 z.2.2) (Finset.mem_univ ℓ)

/-- The normalized channel weight at the pre-jump state is measurable before
the mark is sampled. -/
theorem DavisJumpNoise.measurable_channelProbability_preChannel
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) [S.IntensitiesMeasurable]
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) (ℓ : Fin m) :
    Measurable[ξ.preChannelSpace S hflow initial k]
      (fun ω => davisChannelProbability S
        (davisStateBeforeJump S hflow ξ initial k ω) ℓ) := by
  have hz := ξ.stateBeforeJump_measurable_preChannel S hflow hf initial k
  have hp : Measurable fun z : DavisState Q n =>
      davisChannelProbability S z ℓ := by
    unfold davisChannelProbability
    exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
      (Finset.measurable_sum _ fun i _ => IntensitiesMeasurable.measurable i)
  exact hp.comp hz

/-! ## The weighted channel identity -/

/-- **The weighted channel identity, nonnegative form.**  For a pre-channel
measurable nonnegative weight, integrating the weight over the part of a
pre-channel event on which the next mark is `ℓ` is the same as integrating the
weight against the normalized channel weight over the whole event. -/
theorem DavisJumpNoise.ConditionalChannelLaw.lintegral_channel_weighted
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (ℓ : Fin m) (E : Set Ω)
    (hE : MeasurableSet[ξ.preChannelSpace S hflow initial k] E)
    (w : Ω → ℝ≥0∞)
    (hw : Measurable[ξ.preChannelSpace S hflow initial k] w) :
    ∫⁻ ω in E ∩ {ω | ξ.channel k ω = ℓ}, w ω ∂P =
      ∫⁻ ω in E, w ω * ENNReal.ofReal
        (davisChannelProbability S
          (davisStateBeforeJump S hflow ξ initial k ω) ℓ) ∂P := by
  classical
  have hm : ξ.preChannelSpace S hflow initial k ≤ mΩ := hξ.preChannelSpace_le S hflow hf hr initial k
  set ρ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (davisChannelProbability S (davisStateBeforeJump S hflow ξ initial k ω) ℓ)
    with hρ
  have hρmeas : Measurable ρ :=
    ((ξ.measurable_channelProbability_preChannel S hflow hf initial k
      ℓ).mono hm le_rfl).ennreal_ofReal
  have hEm : MeasurableSet E := hm _ hE
  have hagree : ∀ B, MeasurableSet[ξ.preChannelSpace S hflow initial k] B →
      (P.restrict {ω | ξ.channel k ω = ℓ}) B = (P.withDensity ρ) B := by
    intro B hB
    rw [Measure.restrict_apply (hm _ hB), withDensity_apply ρ (hm _ hB)]
    exact hlaw.channel_identity k ℓ B hB
  have hind : Measurable[ξ.preChannelSpace S hflow initial k] (E.indicator w) := hw.indicator (s := E) hE
  have hkey := lintegral_eq_of_measure_eq_of_le hm
    (P.restrict {ω | ξ.channel k ω = ℓ}) (P.withDensity ρ) hagree
    (E.indicator w) hind
  rw [lintegral_indicator hEm, Measure.restrict_restrict hEm] at hkey
  rw [lintegral_withDensity_eq_lintegral_mul _ hρmeas
    (hind.mono hm le_rfl)] at hkey
  rw [hkey, ← lintegral_indicator hEm]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ E
  · simp [Set.indicator_of_mem hω, hρ, mul_comm]
  · simp [Set.indicator_of_notMem hω]

/-- **The signed weighted channel identity.**  For a bounded pre-channel
measurable real weight, the mean of the weight over the part of a pre-channel
event on which the next mark is `ℓ` is the mean of the weight against the
normalized channel weight. -/
theorem DavisJumpNoise.ConditionalChannelLaw.setIntegral_channel_weighted
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (ℓ : Fin m) (E : Set Ω)
    (hE : MeasurableSet[ξ.preChannelSpace S hflow initial k] E)
    (w : Ω → ℝ)
    (hw : Measurable[ξ.preChannelSpace S hflow initial k] w)
    (C : ℝ) (hwC : ∀ ω, |w ω| ≤ C) :
    ∫ ω in E ∩ {ω | ξ.channel k ω = ℓ}, w ω ∂P =
      ∫ ω in E, w ω * davisChannelProbability S
        (davisStateBeforeJump S hflow ξ initial k ω) ℓ ∂P := by
  classical
  have hm : ξ.preChannelSpace S hflow initial k ≤ mΩ := hξ.preChannelSpace_le S hflow hf hr initial k
  set Sset : Set Ω := {ω | ξ.channel k ω = ℓ} with hSset
  set p : Ω → ℝ := fun ω => davisChannelProbability S
    (davisStateBeforeJump S hflow ξ initial k ω) ℓ with hp
  have hSm : MeasurableSet Sset := hξ.channel k (measurableSet_singleton ℓ)
  have hEm : MeasurableSet E := hm _ hE
  have hwm : Measurable w := hw.mono hm le_rfl
  have hpmeas : Measurable p :=
    (ξ.measurable_channelProbability_preChannel S hflow hf initial k
      ℓ).mono hm le_rfl
  have hp0 : ∀ ω, 0 ≤ p ω := fun ω => davisChannelProbability_nonneg S _ ℓ
  have hp1 : ∀ ω, p ω ≤ 1 := fun ω => davisChannelProbability_le_one S _ ℓ
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right C 0
  have hwC' : ∀ ω, |w ω| ≤ C' := fun ω => le_trans (hwC ω) (le_max_left C 0)
  -- pointwise algebra for the indicator
  have hpt : ∀ (f : Ω → ℝ) (ω : Ω), ENNReal.ofReal (Sset.indicator f ω) =
      Sset.indicator (fun ω => ENNReal.ofReal (f ω)) ω := by
    intro f ω
    by_cases hω : ω ∈ Sset
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hmul : ∀ (f : Ω → ℝ) (ω : Ω),
      ENNReal.ofReal (f ω * p ω) =
        ENNReal.ofReal (f ω) * ENNReal.ofReal (p ω) := by
    intro f ω
    rcases le_or_gt 0 (f ω) with hpos | hneg
    · exact ENNReal.ofReal_mul hpos
    · have h1 : f ω * p ω ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg.le (hp0 ω)
      rw [ENNReal.ofReal_eq_zero.2 h1, ENNReal.ofReal_eq_zero.2 hneg.le,
        zero_mul]
  have hpart : ∀ (f : Ω → ℝ), Measurable[ξ.preChannelSpace S hflow initial k] f →
      ∫⁻ ω in E, ENNReal.ofReal (Sset.indicator f ω) ∂P =
        ∫⁻ ω in E, ENNReal.ofReal (f ω * p ω) ∂P := by
    intro f hfG
    have h1 : ∫⁻ ω in E, ENNReal.ofReal (Sset.indicator f ω) ∂P =
        ∫⁻ ω in E ∩ Sset, ENNReal.ofReal (f ω) ∂P := by
      rw [show (fun ω => ENNReal.ofReal (Sset.indicator f ω)) =
        Sset.indicator (fun ω => ENNReal.ofReal (f ω)) from funext (hpt f)]
      rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
        Set.inter_comm]
    rw [h1, hlaw.lintegral_channel_weighted hf hr hξ k ℓ E hE
      (fun ω => ENNReal.ofReal (f ω)) hfG.ennreal_ofReal]
    exact lintegral_congr fun ω => (hmul f ω).symm
  -- integrability of both sides
  have hbound : ∀ ω, |Sset.indicator w ω| ≤ C' := by
    intro ω
    by_cases hω : ω ∈ Sset
    · rw [Set.indicator_of_mem hω]; exact hwC' ω
    · rw [Set.indicator_of_notMem hω, abs_zero]; exact hC0
  have hintL : IntegrableOn (fun ω => Sset.indicator w ω) E P := by
    refine Integrable.integrableOn ?_
    refine Integrable.mono' (integrable_const C')
      (hwm.indicator hSm).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hbound ω
  have hintR : IntegrableOn (fun ω => w ω * p ω) E P := by
    refine Integrable.integrableOn ?_
    refine Integrable.mono' (integrable_const C')
      (hwm.mul hpmeas).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 ω)]
    calc |w ω| * p ω ≤ |w ω| * 1 :=
          mul_le_mul_of_nonneg_left (hp1 ω) (abs_nonneg _)
      _ = |w ω| := mul_one _
      _ ≤ C' := hwC' ω
  have hLHS : ∫ ω in E ∩ Sset, w ω ∂P = ∫ ω in E, Sset.indicator w ω ∂P :=
    (MeasureTheory.setIntegral_indicator hSm).symm
  rw [hLHS]
  refine integral_eq_of_lintegral_pos_neg_eq _ _ E hintL hintR ?_ ?_
  · exact hpart w hw
  · have hneg := hpart (fun ω => -w ω) hw.neg
    have h1 : (fun ω => -(Sset.indicator w ω)) =
        Sset.indicator (fun ω => -w ω) := by
      funext ω
      by_cases hω : ω ∈ Sset
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    calc ∫⁻ ω in E, ENNReal.ofReal (-(Sset.indicator w ω)) ∂P
        = ∫⁻ ω in E, ENNReal.ofReal (Sset.indicator (fun ω => -w ω) ω) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [show -(Sset.indicator w ω) = Sset.indicator (fun ω => -w ω) ω from
            congrFun h1 ω]
      _ = ∫⁻ ω in E, ENNReal.ofReal (-w ω * p ω) ∂P := hneg
      _ = ∫⁻ ω in E, ENNReal.ofReal (-(w ω * p ω)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [neg_mul]

/-! ## The conditional mean of a realized reset -/

/-- **The conditional mean of a realized reset.**  On every pre-channel event,
a bounded pre-channel measurable weight times the realized increment of a
bounded test function across the reset has the same mean as the same weight
times the normalized expected reset increment at the pre-jump state. -/
theorem DavisJumpNoise.ConditionalChannelLaw.setIntegral_realizedResetIncrement_weighted
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (g : DavisState Q n → ℝ) (hg : Measurable g)
    (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (k : ℕ) (E : Set Ω)
    (hE : MeasurableSet[ξ.preChannelSpace S hflow initial k] E)
    (w : Ω → ℝ)
    (hw : Measurable[ξ.preChannelSpace S hflow initial k] w)
    (C : ℝ) (hwC : ∀ ω, |w ω| ≤ C) :
    ∫ ω in E, w ω *
        davisRealizedResetIncrement S hflow ξ initial g k ω ∂P =
      ∫ ω in E, w ω * davisExpectedResetIncrement S g
        (davisStateBeforeJump S hflow ξ initial k ω) ∂P := by
  classical
  have hm : ξ.preChannelSpace S hflow initial k ≤ mΩ := hξ.preChannelSpace_le S hflow hf hr initial k
  set zb : Ω → DavisState Q n := davisStateBeforeJump S hflow ξ initial k
    with hzb
  have hzbG : Measurable[ξ.preChannelSpace S hflow initial k] zb :=
    ξ.stateBeforeJump_measurable_preChannel S hflow hf initial k
  have hzbm : Measurable zb := hzbG.mono hm le_rfl
  have hEm : MeasurableSet E := hm _ hE
  have hwm : Measurable w := hw.mono hm le_rfl
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right C 0
  have hwC' : ∀ ω, |w ω| ≤ C' := fun ω => le_trans (hwC ω) (le_max_left C 0)
  -- the value attached to the mark `ℓ`
  set d : Fin m → Ω → ℝ := fun ℓ ω => g (S.resetDavisState ℓ (zb ω)) - g (zb ω)
    with hd
  have hdG : ∀ ℓ, Measurable[ξ.preChannelSpace S hflow initial k] (d ℓ) := fun ℓ =>
    ((hg.comp (hr.reset_measurable ℓ)).comp hzbG).sub (hg.comp hzbG)
  have hdC : ∀ ℓ ω, |d ℓ ω| ≤ 2 * Cg := by
    intro ℓ ω
    calc |d ℓ ω| ≤ |g (S.resetDavisState ℓ (zb ω))| + |g (zb ω)| :=
          abs_sub _ _
      _ ≤ Cg + Cg := add_le_add (hgC _) (hgC _)
      _ = 2 * Cg := by ring
  have hdm : ∀ ℓ, Measurable (d ℓ) := fun ℓ => (hdG ℓ).mono hm le_rfl
  set p : Fin m → Ω → ℝ := fun ℓ ω => davisChannelProbability S (zb ω) ℓ
    with hpdef
  have hpm : ∀ ℓ, Measurable (p ℓ) := fun ℓ =>
    (ξ.measurable_channelProbability_preChannel S hflow hf initial k
      ℓ).mono hm le_rfl
  -- integrability facts
  have hintbound : ∀ (f : Ω → ℝ), Measurable f → ∀ K : ℝ, (∀ ω, |f ω| ≤ K) →
      IntegrableOn f E P := by
    intro f hfm K hfK
    refine Integrable.integrableOn ?_
    refine Integrable.mono' (integrable_const (max K 0))
      hfm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact le_trans (hfK ω) (le_max_left K 0)
  -- decompose the realized increment along the mark
  have hsplit : ∀ ω, w ω * davisRealizedResetIncrement S hflow ξ initial g k ω =
      ∑ ℓ : Fin m, ({ω' | ξ.channel k ω' = ℓ}.indicator (fun ω' =>
        w ω' * d ℓ ω')) ω := by
    intro ω
    rw [Finset.sum_eq_single (ξ.channel k ω)]
    · rw [Set.indicator_of_mem (by simp)]
      rfl
    · intro b _ hb
      refine Set.indicator_of_notMem ?_ _
      simpa [Set.mem_setOf_eq] using fun h => hb h.symm
    · intro h
      exact absurd (Finset.mem_univ (ξ.channel k ω)) h
  have hLHS : ∫ ω in E, w ω *
      davisRealizedResetIncrement S hflow ξ initial g k ω ∂P =
      ∑ ℓ : Fin m, ∫ ω in E ∩ {ω | ξ.channel k ω = ℓ}, w ω * d ℓ ω ∂P := by
    rw [setIntegral_congr_fun hEm (fun ω _ => hsplit ω)]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [MeasureTheory.setIntegral_indicator
        (show MeasurableSet {ω' | ξ.channel k ω' = ℓ} from
          hξ.channel k (measurableSet_singleton ℓ))]
    · intro ℓ _
      refine Integrable.indicator ?_
        (show MeasurableSet {ω' | ξ.channel k ω' = ℓ} from
          hξ.channel k (measurableSet_singleton ℓ))
      exact hintbound (fun ω => w ω * d ℓ ω) (hwm.mul (hdm ℓ))
        (C' * (2 * Cg + 1)) (fun ω => by
          rw [abs_mul]
          have h2 : (0:ℝ) ≤ 2 * Cg := le_trans (abs_nonneg _) (hdC ℓ ω)
          exact mul_le_mul (hwC' ω) (le_trans (hdC ℓ ω) (by linarith))
            (abs_nonneg _) hC0)
  rw [hLHS]
  have hstep : ∀ ℓ : Fin m,
      ∫ ω in E ∩ {ω | ξ.channel k ω = ℓ}, w ω * d ℓ ω ∂P =
        ∫ ω in E, (w ω * d ℓ ω) * p ℓ ω ∂P := by
    intro ℓ
    refine hlaw.setIntegral_channel_weighted hf hr hξ k ℓ E hE
      (fun ω => w ω * d ℓ ω) (hw.mul (hdG ℓ)) (C' * (2 * Cg + 1)) ?_
    intro ω
    rw [abs_mul]
    have h2 : (0:ℝ) ≤ 2 * Cg := le_trans (abs_nonneg _) (hdC ℓ ω)
    exact mul_le_mul (hwC' ω) (le_trans (hdC ℓ ω) (by linarith))
      (abs_nonneg _) hC0
  simp_rw [hstep]
  rw [← integral_finset_sum]
  · refine setIntegral_congr_fun hEm fun ω _ => ?_
    rw [davisExpectedResetIncrement, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => by rw [hpdef, hd]; ring
  · intro ℓ _
    refine hintbound (fun ω => (w ω * d ℓ ω) * p ℓ ω)
      ((hwm.mul (hdm ℓ)).mul (hpm ℓ)) (C' * (2 * Cg + 1) * 1) ?_
    intro ω
    rw [abs_mul]
    have h2 : (0:ℝ) ≤ 2 * Cg := le_trans (abs_nonneg _) (hdC ℓ ω)
    have hwd : |w ω * d ℓ ω| ≤ C' * (2 * Cg + 1) := by
      rw [abs_mul]
      exact mul_le_mul (hwC' ω) (le_trans (hdC ℓ ω) (by linarith))
        (abs_nonneg _) hC0
    have hp1 : |p ℓ ω| ≤ 1 := by
      rw [abs_of_nonneg (davisChannelProbability_nonneg S _ ℓ)]
      exact davisChannelProbability_le_one S _ ℓ
    exact mul_le_mul hwd hp1 (abs_nonneg _)
      (le_trans (abs_nonneg _) hwd)

end SHS
