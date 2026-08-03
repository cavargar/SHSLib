import SHSLib.Core.DavisConditionalChannelIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Conditional expectations of finite channel marks

This module converts the event-integral conditional channel law into Mathlib's
conditional-expectation interface.  The singleton-indicator formula is the
basic bridge needed to center reset increments whose coefficients are
measurable before the channel is sampled.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The conditional expectation of a channel singleton indicator is its
normalized channel probability evaluated at the pre-jump state. -/
theorem DavisJumpNoise.ConditionalChannelLaw.condExp_channel_indicator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (ℓ : Fin m) :
    P[(fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) |
        ξ.preChannelSpace S hflow initial k] =ᵐ[P]
      fun ω => davisChannelProbability S
        (davisStateBeforeJump S hflow ξ initial k ω) ℓ := by
  symm; apply ae_eq_condExp_of_forall_setIntegral_eq
  · exact hξ.preChannelSpace_le S hflow hf hr initial k
  · -- hf: Integrable indicator function
    have eq_fun : (fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) =
        Set.indicator {ω | ξ.channel k ω = ℓ} (fun _ => 1) := by
      ext ω; simp [Set.indicator]
    rw [eq_fun]
    exact Integrable.indicator (integrable_const 1) (hξ.channel k (measurableSet_singleton ℓ))
  · -- hg_int_finite: Integrability of channel probability on finite measure sets
    intro s hs _
    have h_meas_state : Measurable (S.davisStateBeforeJump hflow ξ initial k) :=
      DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
    have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
      simp_rw [davisChannelProbability]
      exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
        (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
    have h_bound : ∀ ω, ‖S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ‖ ≤ 1 := by
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (davisChannelProbability_nonneg S _ ℓ)]
      unfold davisChannelProbability
      apply div_le_one_of_le₀
      · let z := S.davisStateBeforeJump hflow ξ initial k ω
        rw [totalIntensity]
        exact Finset.single_le_sum (f := fun ℓ => S.intensity ℓ z.1 z.2.1 z.2.2)
          (fun ℓ _ => S.intensity_nonneg ℓ z.1 z.2.1 z.2.2) (Finset.mem_univ ℓ)
      · exact totalIntensity_nonneg S (S.davisStateBeforeJump hflow ξ initial k ω)
    have hint : Integrable (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ) P := by
      apply Integrable.mono' (integrable_const 1)
      · exact (h_meas_prob.comp h_meas_state).aestronglyMeasurable
      · filter_upwards with x
        exact h_bound x
    exact hint.integrableOn
  · -- hg_eq: Integral equality
    intro s hs hP
    -- Use lintegral_channel_indicator to get lintegral equality
    have lint_eq := DavisJumpNoise.ConditionalChannelLaw.lintegral_channel_indicator hξ hlaw k ℓ s hs
    -- Convert lintegral equality to integral equality for nonnegative functions
    -- Convert integrals to lintegrals using integral_eq_lintegral_of_nonneg_ae
    have rhs_eq : ENNReal.toReal (∫⁻ x in s, ENNReal.ofReal (if ξ.channel k x = ℓ then (1 : ℝ) else 0) ∂P) =
        ∫ x in s, (if ξ.channel k x = ℓ then (1 : ℝ) else 0) ∂P := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
      · filter_upwards with x; split_ifs <;> norm_num
      · refine Measurable.aestronglyMeasurable ?_
        exact Measurable.ite (hξ.channel k (measurableSet_singleton ℓ)) measurable_const measurable_const
    have h_meas_state : Measurable (S.davisStateBeforeJump hflow ξ initial k) :=
      DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
    have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
      simp_rw [davisChannelProbability]
      exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
        (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
    have h_ae_meas : AEStronglyMeasurable (fun x => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ) P :=
      (h_meas_prob.comp h_meas_state).aestronglyMeasurable
    have lhs_eq : ENNReal.toReal (∫⁻ x in s, ENNReal.ofReal (S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ) ∂P) =
        ∫ x in s, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ ∂P := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
      · filter_upwards with x; exact davisChannelProbability_nonneg S _ ℓ
      · exact h_ae_meas.restrict
    -- Now use lint_eq to connect the two sides
    have indicator_eq : ∀ ω, ({ω' | ξ.channel k ω' = ℓ}.indicator (fun _ => (1 : ℝ≥0∞))) ω =
        ENNReal.ofReal (if ξ.channel k ω = ℓ then (1 : ℝ) else 0) := by
      intro ω
      by_cases h : ξ.channel k ω = ℓ <;> simp [h, Set.indicator]
    rw [← lhs_eq, ← rhs_eq]
    -- Now goal is: (∫⁻ ofReal(channel_prob)).toReal = (∫⁻ ofReal(if ...)).toReal
    -- Use lint_eq and indicator_eq
    rw [← funext indicator_eq]
    rw [lint_eq]
  · -- hgm: AEStronglyMeasurable
    have h_meas_state_pre : Measurable[ξ.preChannelSpace S hflow initial k]
        (S.davisStateBeforeJump hflow ξ initial k) :=
      DavisJumpNoise.stateBeforeJump_measurable_preChannel S hflow hf ξ initial k
    have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
      simp_rw [davisChannelProbability]
      exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
        (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
    have h_comp : Measurable[ξ.preChannelSpace S hflow initial k]
        (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ) :=
      h_meas_prob.comp h_meas_state_pre
    exact h_comp.aestronglyMeasurable

/-- The conditional expectation of any real-valued test of the finite channel
mark is the corresponding normalized finite-channel average. -/
theorem DavisJumpNoise.ConditionalChannelLaw.condExp_channel_test
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (v : Fin m → ℝ) :
    P[(fun ω => v (ξ.channel k ω)) |
        ξ.preChannelSpace S hflow initial k] =ᵐ[P]
      fun ω => ∑ ℓ : Fin m, davisChannelProbability S
        (davisStateBeforeJump S hflow ξ initial k ω) ℓ * v ℓ := by
  -- Rewrite v(channel k) as a sum of indicators
  have h_eq : ∀ ω, v (ξ.channel k ω) = ∑ ℓ : Fin m, (if ξ.channel k ω = ℓ then v ℓ else 0) := by
    intro ω
    rw [Finset.sum_eq_single (ξ.channel k ω)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- Rewrite using h_eq
  simp_rw [funext h_eq]
  apply (ae_eq_condExp_of_forall_setIntegral_eq ?hm ?hint ?hint' ?hint'' ?hg).symm
  · exact hξ.preChannelSpace_le S hflow hf hr initial k
  · -- Integrability of the sum of indicators
    apply Integrable.mono' (integrable_const (∑ ℓ : Fin m, |v ℓ|))
    · have : Measurable (fun x => ∑ ℓ : Fin m, if ξ.channel k x = ℓ then v ℓ else 0) := by
        apply Finset.measurable_sum
        intro ℓ _
        exact Measurable.ite (hξ.channel k (measurableSet_singleton ℓ)) measurable_const measurable_const
      exact this.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs]
      calc |∑ ℓ : Fin m, if ξ.channel k ω = ℓ then v ℓ else 0|
          ≤ ∑ ℓ : Fin m, |if ξ.channel k ω = ℓ then v ℓ else 0| := by
            exact Finset.abs_sum_le_sum_abs _ _
        _ = ∑ ℓ : Fin m, |v ℓ| * |if ξ.channel k ω = ℓ then (1 : ℝ) else 0| := by
            congr 1; ext ℓ; split_ifs <;> simp
        _ ≤ ∑ ℓ : Fin m, |v ℓ| * 1 := by
            apply Finset.sum_le_sum; intro ℓ _
            gcongr
            split_ifs <;> norm_num
        _ = ∑ ℓ : Fin m, |v ℓ| := by simp
  · -- Integrability on sets for RHS
    intro s _ _
    apply Integrable.integrableOn
    have h_meas_state : Measurable (S.davisStateBeforeJump hflow ξ initial k) :=
      DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
    have h_meas_prob : ∀ ℓ, Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
      intro ℓ
      simp_rw [davisChannelProbability]
      exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
        (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
    have h_meas_term : ∀ ℓ ∈ Finset.univ, Measurable (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ) := by
      intro ℓ _
      exact (h_meas_prob ℓ).comp h_meas_state |>.mul_const _
    have h_aestronglyMeasurable : AEStronglyMeasurable (fun ω => ∑ ℓ : Fin m, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ) P :=
      Measurable.aestronglyMeasurable (Finset.measurable_sum _ h_meas_term)
    apply Integrable.mono' (integrable_const (∑ ℓ : Fin m, |v ℓ|)) h_aestronglyMeasurable
    filter_upwards with ω
    simp only [Real.norm_eq_abs]
    calc |∑ ℓ : Fin m, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ|
        ≤ ∑ ℓ : Fin m, |S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ℓ : Fin m, |S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ| * |v ℓ| := by
          congr 1; ext ℓ; rw [abs_mul]
      _ ≤ ∑ ℓ : Fin m, 1 * |v ℓ| := by
          apply Finset.sum_le_sum; intro ℓ _
          gcongr
          rw [abs_of_nonneg (davisChannelProbability_nonneg S _ ℓ)]
          by_cases hz : S.totalIntensity (S.davisStateBeforeJump hflow ξ initial k ω) = 0
          · rw [davisChannelProbability]
            simp [hz]
          · have := Finset.single_le_sum (f := fun ℓ => davisChannelProbability S (S.davisStateBeforeJump hflow ξ initial k ω) ℓ)
              (fun ℓ _ => davisChannelProbability_nonneg S _ ℓ) (Finset.mem_univ ℓ)
            rwa [sum_davisChannelProbability S _ hz] at this
      _ = ∑ ℓ : Fin m, |v ℓ| := by simp
  · -- Integral equality
    intro s hs hP
    -- Use linearity of integral to split the sums
    have h_int_lhs : IntegrableOn (fun ω => ∑ ℓ : Fin m, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ) s P := by
      apply Integrable.integrableOn
      have h_meas_state : Measurable (S.davisStateBeforeJump hflow ξ initial k) :=
        DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
      have h_meas_prob : ∀ ℓ, Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
        intro ℓ
        simp_rw [davisChannelProbability]
        exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
          (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
      have h_meas_term : ∀ ℓ ∈ Finset.univ, Measurable (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ) := by
        intro ℓ _
        exact (h_meas_prob ℓ).comp h_meas_state |>.mul_const _
      have h_aestronglyMeasurable : AEStronglyMeasurable (fun ω => ∑ ℓ : Fin m, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ) P :=
        Measurable.aestronglyMeasurable (Finset.measurable_sum _ h_meas_term)
      apply Integrable.mono' (integrable_const (∑ ℓ : Fin m, |v ℓ|)) h_aestronglyMeasurable
      filter_upwards with ω
      simp only [Real.norm_eq_abs]
      calc |∑ ℓ : Fin m, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ|
          ≤ ∑ ℓ : Fin m, |S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ ℓ : Fin m, |S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ| * |v ℓ| := by
            congr 1; ext ℓ; rw [abs_mul]
        _ ≤ ∑ ℓ : Fin m, 1 * |v ℓ| := by
            apply Finset.sum_le_sum; intro ℓ _
            gcongr
            rw [abs_of_nonneg (davisChannelProbability_nonneg S _ ℓ)]
            by_cases hz : S.totalIntensity (S.davisStateBeforeJump hflow ξ initial k ω) = 0
            · simp [davisChannelProbability, hz]
            · have := Finset.single_le_sum (f := fun ℓ => davisChannelProbability S (S.davisStateBeforeJump hflow ξ initial k ω) ℓ)
                (fun ℓ _ => davisChannelProbability_nonneg S _ ℓ) (Finset.mem_univ ℓ)
              rwa [sum_davisChannelProbability S _ hz] at this
        _ = ∑ ℓ : Fin m, |v ℓ| := by simp
    have h_int_rhs : IntegrableOn (fun ω => ∑ ℓ : Fin m, if ξ.channel k ω = ℓ then v ℓ else 0) s P := by
      apply Integrable.integrableOn
      have : Measurable (fun x => ∑ ℓ : Fin m, if ξ.channel k x = ℓ then v ℓ else 0) := by
        apply Finset.measurable_sum
        intro ℓ _
        exact Measurable.ite (hξ.channel k (measurableSet_singleton ℓ)) measurable_const measurable_const
      have h_aestronglyMeasurable : AEStronglyMeasurable (fun ω => ∑ ℓ : Fin m, if ξ.channel k ω = ℓ then v ℓ else 0) P :=
        this.aestronglyMeasurable
      apply Integrable.mono' (integrable_const (∑ ℓ : Fin m, |v ℓ|)) h_aestronglyMeasurable
      filter_upwards with ω
      simp only [Real.norm_eq_abs]
      calc |∑ ℓ : Fin m, if ξ.channel k ω = ℓ then v ℓ else 0|
          ≤ ∑ ℓ : Fin m, |if ξ.channel k ω = ℓ then v ℓ else 0| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ ℓ : Fin m, |v ℓ| * |if ξ.channel k ω = ℓ then (1 : ℝ) else 0| := by
            congr 1; ext ℓ; split_ifs <;> simp
        _ ≤ ∑ ℓ : Fin m, |v ℓ| * 1 := by
            apply Finset.sum_le_sum; intro ℓ _
            gcongr
            split_ifs <;> norm_num
        _ = ∑ ℓ : Fin m, |v ℓ| := by simp
    rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin m)) (fun ℓ _ => by
        apply Integrable.integrableOn
        apply Integrable.mul_const
        have h_meas_state : Measurable (S.davisStateBeforeJump hflow ξ initial k) :=
          DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
        have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
          simp_rw [davisChannelProbability]
          exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
            (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
        have h_ae_meas : AEStronglyMeasurable (fun x => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ) P :=
          (h_meas_prob.comp h_meas_state).aestronglyMeasurable
        apply Integrable.mono' (integrable_const 1) h_ae_meas
        filter_upwards with ω
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (davisChannelProbability_nonneg S _ ℓ)]
        by_cases hz : S.totalIntensity (S.davisStateBeforeJump hflow ξ initial k ω) = 0
        · simp [davisChannelProbability, hz]
        · have := Finset.single_le_sum (f := fun ℓ => davisChannelProbability S (S.davisStateBeforeJump hflow ξ initial k ω) ℓ)
            (fun ℓ _ => davisChannelProbability_nonneg S _ ℓ) (Finset.mem_univ ℓ)
          rwa [sum_davisChannelProbability S _ hz] at this),
        MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin m)) (fun ℓ _ => by
        apply Integrable.integrableOn
        have eq_fun : (fun x => if ξ.channel k x = ℓ then v ℓ else 0) =
            Set.indicator {x | ξ.channel k x = ℓ} (fun _ => v ℓ) := by
          ext x; simp [Set.indicator]
        rw [eq_fun]
        exact Integrable.indicator (integrable_const (v ℓ)) (hξ.channel k (measurableSet_singleton ℓ)))]
    congr 1
    ext ℓ
    -- For each ℓ, show the integrals are equal
    by_cases hv0 : v ℓ = 0
    · simp [hv0]
    · -- Use lintegral_channel_indicator
      have lint_eq := DavisJumpNoise.ConditionalChannelLaw.lintegral_channel_indicator hξ hlaw k ℓ s hs
      have h_meas_state : Measurable (S.davisStateBeforeJump hflow ξ initial k) :=
        DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
      have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
        simp_rw [davisChannelProbability]
        exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
          (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
      have h_ae_meas : AEStronglyMeasurable (fun x => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ) P :=
        (h_meas_prob.comp h_meas_state).aestronglyMeasurable
      have lhs_eq : ∫ (x : Ω) in s, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ ∂P =
          ∫ (x : Ω) in s, (if ξ.channel k x = ℓ then (1 : ℝ) else 0) ∂P := by
        have rhs_eq : ENNReal.toReal (∫⁻ x in s, ENNReal.ofReal (if ξ.channel k x = ℓ then (1 : ℝ) else 0) ∂P) =
            ∫ x in s, (if ξ.channel k x = ℓ then (1 : ℝ) else 0) ∂P := by
          rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
          · filter_upwards with x; split_ifs <;> norm_num
          · refine Measurable.aestronglyMeasurable ?_
            exact Measurable.ite (hξ.channel k (measurableSet_singleton ℓ)) measurable_const measurable_const
        have lhs_eq : ENNReal.toReal (∫⁻ x in s, ENNReal.ofReal (S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ) ∂P) =
            ∫ x in s, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ ∂P := by
          rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
          · filter_upwards with x; exact davisChannelProbability_nonneg S _ ℓ
          · exact h_ae_meas.restrict
        rw [← lhs_eq, ← rhs_eq]
        have indicator_eq : ∀ ω, ({ω' | ξ.channel k ω' = ℓ}.indicator (fun _ => (1 : ℝ≥0∞))) ω =
            ENNReal.ofReal (if ξ.channel k ω = ℓ then (1 : ℝ) else 0) := by
          intro ω
          by_cases h : ξ.channel k ω = ℓ <;> simp [h, Set.indicator]
        rw [← funext indicator_eq]
        rw [lint_eq]
      have h1 : ∫ (a : Ω) in s, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k a) ℓ * v ℓ ∂P =
          (∫ (a : Ω) in s, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k a) ℓ ∂P) * v ℓ :=
        integral_mul_const _ _
      have h2 : ∫ (a : Ω) in s, if ξ.channel k a = ℓ then v ℓ else 0 ∂P =
          (∫ (a : Ω) in s, if ξ.channel k a = ℓ then (1 : ℝ) else 0 ∂P) * v ℓ := by
        have : (fun a => if ξ.channel k a = ℓ then v ℓ else 0) = (fun a => (if ξ.channel k a = ℓ then (1 : ℝ) else 0) * v ℓ) := by
          ext x; split_ifs <;> ring
        rw [this, integral_mul_const]
      rw [h1, h2, lhs_eq]
  · -- AEStronglyMeasurable for RHS
    have h_meas_state : Measurable[ξ.preChannelSpace S hflow initial k]
        (S.davisStateBeforeJump hflow ξ initial k) :=
      DavisJumpNoise.stateBeforeJump_measurable_preChannel S hflow hf ξ initial k
    have h_meas_prob : ∀ ℓ, Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
      intro ℓ
      simp_rw [davisChannelProbability]
      exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
        (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
    have h_meas_term : ∀ ℓ ∈ Finset.univ,
        Measurable[ξ.preChannelSpace S hflow initial k] (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ) := by
      intro ℓ _
      exact (h_meas_prob ℓ).comp h_meas_state |>.mul_const _
    exact (Finset.measurable_sum _ h_meas_term).aestronglyMeasurable

end SHS
