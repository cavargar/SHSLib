import SHSLib.Core.DavisConditionalChannelExpectation
import SHSLib.Core.DavisFiniteCompensatorBounds
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Conditional expectations of reset increments

This module extends the finite-channel conditional expectation formula from
fixed channel tests to channel tests whose coefficients are measurable before
the channel is sampled.  It then specializes the result to reset increments
and their centered versions.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Conditional finite-channel averaging with coefficients that may depend on
information already present in the pre-channel measurable space. -/
theorem DavisJumpNoise.ConditionalChannelLaw.condExp_channel_dependent_test
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (v : Ω → Fin m → ℝ)
    (hvmeas : ∀ ℓ, Measurable[ξ.preChannelSpace S hflow initial k]
      (fun ω => v ω ℓ))
    (C : ℝ) (hvbound : ∀ ω ℓ, |v ω ℓ| ≤ C) :
    P[(fun ω => v ω (ξ.channel k ω)) |
        ξ.preChannelSpace S hflow initial k] =ᵐ[P]
      fun ω => ∑ ℓ : Fin m, davisChannelProbability S
        (davisStateBeforeJump S hflow ξ initial k ω) ℓ * v ω ℓ := by
  -- Rewrite v(channel k) as a sum over indicators
  have h_eq : ∀ ω, v ω (ξ.channel k ω) = ∑ ℓ : Fin m, (if ξ.channel k ω = ℓ then v ω ℓ else 0) := by
    intro ω
    rw [Finset.sum_eq_single (ξ.channel k ω)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp_rw [funext h_eq]
  apply (ae_eq_condExp_of_forall_setIntegral_eq ?hm ?hint ?hint' ?hint'' ?hg).symm
  · exact hξ.preChannelSpace_le S hflow hf hr initial k
  · -- Integrability of LHS
    apply Integrable.mono' (integrable_const (m * C))
    · -- Measurability
      have : Measurable (fun x => ∑ ℓ : Fin m, if ξ.channel k x = ℓ then v x ℓ else 0) := by
        apply Finset.measurable_sum _ fun ℓ _ => ?_
        refine Measurable.ite (hξ.channel k (measurableSet_singleton ℓ)) ?_ measurable_const
        refine Measurable.mono (hvmeas ℓ) (hξ.preChannelSpace_le S hflow hf hr initial k) ?_
        exact le_refl _
      exact this.aestronglyMeasurable
    · -- Bound
      filter_upwards with ω
      simp only [Real.norm_eq_abs]
      calc |∑ ℓ : Fin m, if ξ.channel k ω = ℓ then v ω ℓ else 0|
          ≤ ∑ ℓ : Fin m, |if ξ.channel k ω = ℓ then v ω ℓ else 0| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ ℓ : Fin m, |v ω ℓ| * |if ξ.channel k ω = ℓ then (1 : ℝ) else 0| := by
            congr 1; ext ℓ; split_ifs <;> simp
        _ ≤ ∑ ℓ : Fin m, |v ω ℓ| * 1 := by
            apply Finset.sum_le_sum; intro ℓ _
            gcongr
            split_ifs <;> norm_num
        _ = ∑ ℓ : Fin m, |v ω ℓ| := by simp
        _ ≤ ∑ _ : Fin m, C := by apply Finset.sum_le_sum; intro ℓ _; exact hvbound ω ℓ
        _ = m * C := by simp
  · -- Integrability of RHS
    intro s hs hP
    apply Integrable.integrableOn
    apply Integrable.mono' (integrable_const (m * C))
    · -- Measurability
      have h_meas_state_pre : Measurable[ξ.preChannelSpace S hflow initial k]
          (S.davisStateBeforeJump hflow ξ initial k) :=
        DavisJumpNoise.stateBeforeJump_measurable_preChannel S hflow hf ξ initial k
      have h_meas_prob : ∀ ℓ, Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
        intro ℓ
        simp_rw [davisChannelProbability]
        exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
          (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
      have h_meas_term : ∀ ℓ ∈ Finset.univ,
          Measurable[ξ.preChannelSpace S hflow initial k] (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ω ℓ) := by
        intro ℓ _
        apply Measurable.mul
        · exact (h_meas_prob ℓ).comp h_meas_state_pre
        · exact hvmeas ℓ
      have h_meas_sum := Finset.measurable_sum _ h_meas_term
      have h_meas_sum_mΩ : Measurable (fun ω => ∑ ℓ : Fin m, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ω ℓ) :=
        Measurable.mono h_meas_sum (hξ.preChannelSpace_le S hflow hf hr initial k) (le_refl _)
      exact h_meas_sum_mΩ.aestronglyMeasurable
    · -- Bound
      filter_upwards with ω
      simp only [Real.norm_eq_abs]
      calc |∑ ℓ : Fin m, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ω ℓ|
          ≤ ∑ ℓ : Fin m, |S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ω ℓ| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ ℓ : Fin m, |S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ| * |v ω ℓ| := by
            congr 1; ext ℓ; rw [abs_mul]
        _ ≤ ∑ ℓ : Fin m, 1 * |v ω ℓ| := by
            apply Finset.sum_le_sum; intro ℓ _
            gcongr
            rw [abs_of_nonneg (davisChannelProbability_nonneg S _ ℓ)]
            by_cases hz : S.totalIntensity (S.davisStateBeforeJump hflow ξ initial k ω) = 0
            · rw [davisChannelProbability]
              simp [hz]
            · have := Finset.single_le_sum (f := fun ℓ => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ)
                (fun ℓ _ => davisChannelProbability_nonneg S _ ℓ) (Finset.mem_univ ℓ)
              rwa [sum_davisChannelProbability S _ hz] at this
        _ = ∑ ℓ : Fin m, |v ω ℓ| := by simp
        _ ≤ ∑ _ : Fin m, C := by apply Finset.sum_le_sum; intro ℓ _; exact hvbound ω ℓ
        _ = m * C := by simp
  · -- Integral equality
    intro s hs hP
    -- Integrability of each term on RHS (indicator * v)
    have h_rhs_int : ∀ i ∈ Finset.univ, Integrable (fun x => if ξ.channel k x = i then v x i else 0) (P.restrict s) := by
      intro i _
      have heq : (fun x => if ξ.channel k x = i then v x i else 0) =
          Set.indicator {x | ξ.channel k x = i} (fun x => v x i) := by
        ext x; simp [Set.indicator]
      rw [heq]
      apply Integrable.indicator
      · -- v(·, i) is integrable (bounded)
        apply Integrable.mono' (integrable_const C)
        · exact Measurable.aestronglyMeasurable ((hvmeas i).mono (hξ.preChannelSpace_le S hflow hf hr initial k) (le_refl _))
        · filter_upwards with x; exact hvbound x i
      · have := hξ.channel k (measurableSet_singleton i)
        exact this
    -- Integrability of each term on LHS (prob * v)
    have h_lhs_int : ∀ i ∈ Finset.univ, Integrable (fun x => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) i * v x i) (P.restrict s) := by
      intro i _
      apply Integrable.mono' (integrable_const C)
      · -- Measurability
        have h_meas_state_pre : Measurable[ξ.preChannelSpace S hflow initial k]
            (S.davisStateBeforeJump hflow ξ initial k) :=
          DavisJumpNoise.stateBeforeJump_measurable_preChannel S hflow hf ξ initial k
        have h_meas_prob : ∀ ℓ, Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
          intro ℓ
          simp_rw [davisChannelProbability]
          exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
            (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
        have h_meas_term : Measurable[ξ.preChannelSpace S hflow initial k] (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) i * v ω i) := by
          apply Measurable.mul
          · exact (h_meas_prob i).comp h_meas_state_pre
          · exact hvmeas i
        exact Measurable.aestronglyMeasurable ((h_meas_term.mono (hξ.preChannelSpace_le S hflow hf hr initial k) (le_refl _)))
      · -- Bound
        filter_upwards with x
        simp only [Real.norm_eq_abs]
        calc |S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) i * v x i|
            = |S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) i| * |v x i| := abs_mul _ _
          _ ≤ 1 * |v x i| := by
              gcongr
              rw [abs_of_nonneg (davisChannelProbability_nonneg S _ i)]
              by_cases hz : S.totalIntensity (S.davisStateBeforeJump hflow ξ initial k x) = 0
              · rw [davisChannelProbability]
                simp [hz]
              · have := Finset.single_le_sum (f := fun ℓ => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k x) ℓ)
                  (fun ℓ _ => davisChannelProbability_nonneg S _ ℓ) (Finset.mem_univ i)
                rwa [sum_davisChannelProbability S _ hz] at this
          _ = |v x i| := by simp
          _ ≤ C := hvbound x i
    rw [MeasureTheory.integral_finset_sum Finset.univ h_rhs_int, MeasureTheory.integral_finset_sum Finset.univ h_lhs_int]
    apply Finset.sum_congr rfl
    intro ℓ _
    -- Now need: ∫ prob * v(·, ℓ) = ∫ I(channel = ℓ) * v(·, ℓ)
    -- Rewrite RHS using indicator
    have rhs_eq : (fun x => if ξ.channel k x = ℓ then v x ℓ else 0) =
        Set.indicator {x | ξ.channel k x = ℓ} (fun x => v x ℓ) := by
      ext x; simp [Set.indicator]
    rw [rhs_eq]
    -- Use the pull-out property: for G-measurable g, ∫ prob * g = ∫ I * g
    -- condExp_channel_indicator says E[I(channel=ℓ) | G] = prob
    have h_cond := DavisJumpNoise.ConditionalChannelLaw.condExp_channel_indicator hf hr hξ hlaw k ℓ
    -- We have: prob = E[I(channel=ℓ) | G] a.e.
    -- Need: ∫_s prob * v = ∫_s I(channel=ℓ) * v
    -- Rewrite prob using h_cond
    have h_prob_eq : (fun a => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k a) ℓ) =ᵐ[P]
        MeasureTheory.condExp (ξ.preChannelSpace S hflow initial k) P
          (fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) := h_cond.symm
    -- Rewrite LHS using h_prob_eq
    have h_lhs_rw : ∫ a in s, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k a) ℓ * v a ℓ ∂P =
        ∫ a in s, MeasureTheory.condExp (ξ.preChannelSpace S hflow initial k) P
          (fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) a * v a ℓ ∂P := by
      apply MeasureTheory.integral_congr_ae
      have h_prob_eq_restrict : (fun a => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k a) ℓ) =ᵐ[P.restrict s]
          MeasureTheory.condExp (ξ.preChannelSpace S hflow initial k) P
            (fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) :=
        h_prob_eq.restrict
      filter_upwards [h_prob_eq_restrict] with x hx
      rw [hx]
    rw [h_lhs_rw]
    -- Pull-out: E[I|G] * v = E[v * I | G] when v is G-measurable
    -- Use integral_condExp: ∫ E[X|G] = ∫ X
    -- And pull-out: E[I|G] * v = E[v*I | G] when v is G-measurable
    -- First, show the pull-out
    have v_meas : Measurable[ξ.preChannelSpace S hflow initial k] (fun ω => v ω ℓ) := hvmeas ℓ
    have I_int : Integrable (fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) P := by
      have heq : (fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) =
          Set.indicator {ω | ξ.channel k ω = ℓ} (fun _ => (1 : ℝ)) := by
        ext ω; simp [Set.indicator]
      rw [heq]
      apply Integrable.indicator (integrable_const 1)
      exact hξ.channel k (measurableSet_singleton ℓ)
    -- Use pull-out: E[I|G] * v = E[v * I | G] when v is G-measurable
    -- Then use: ∫ E[v*I | G] over s = ∫ v*I over s (defining property of condExp)
    -- First, v * I is integrable
    have vI_int : Integrable (fun ω => v ω ℓ * (if ξ.channel k ω = ℓ then (1 : ℝ) else 0)) P := by
      apply Integrable.mono' (integrable_const C)
      · exact (v_meas.mono (hξ.preChannelSpace_le S hflow hf hr initial k) (le_refl _)).aestronglyMeasurable.mul
          (Measurable.aestronglyMeasurable (Measurable.ite (hξ.channel k (measurableSet_singleton ℓ)) 
            measurable_const measurable_const))
      · filter_upwards with ω
        simp only [Real.norm_eq_abs]
        split_ifs <;> simp
        · exact hvbound ω ℓ
        · -- 0 ≤ C since |v| ≤ C and |v| ≥ 0
          exact le_trans (abs_nonneg _) (hvbound ω ℓ)
    have vI_int' : Integrable (fun ω => (if ξ.channel k ω = ℓ then (1 : ℝ) else 0) * v ω ℓ) P := by
      apply Integrable.mono' (integrable_const C)
      · exact (Measurable.aestronglyMeasurable (Measurable.ite (hξ.channel k (measurableSet_singleton ℓ)) 
            measurable_const measurable_const)).mul
          (v_meas.mono (hξ.preChannelSpace_le S hflow hf hr initial k) (le_refl _)).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Real.norm_eq_abs]
        split_ifs <;> simp
        · exact hvbound ω ℓ
        · -- 0 ≤ C since |v| ≤ C and |v| ≥ 0
          exact le_trans (abs_nonneg _) (hvbound ω ℓ)
    -- Use pull-out: E[I|G] * v = E[v * I | G] when v is G-measurable
    -- Then use: ∫ E[v*I | G] over s = ∫ v*I over s (defining property of condExp)
    -- Use setIntegral_condExp
    have h_set_int := MeasureTheory.setIntegral_condExp
      (hm := hξ.preChannelSpace_le S hflow hf hr initial k) vI_int hs
    -- Goal: ∫ E[I|G] * v = ∫ v * I
    -- Use pull-out: condExp(G) * v = condExp(v * I) when v is G-measurable
    -- Pull-out says: v * E[I|G] = E[v * I | G] when v is G-measurable
    have pull_out : ∀ᵐ a ∂P,
        MeasureTheory.condExp (ξ.preChannelSpace S hflow initial k) P (fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) a * v a ℓ =
        MeasureTheory.condExp (ξ.preChannelSpace S hflow initial k) P (fun ω => v ω ℓ * (if ξ.channel k ω = ℓ then (1 : ℝ) else 0)) a := by
      have hp := condExp_mul_of_stronglyMeasurable_right v_meas.stronglyMeasurable vI_int' I_int
      filter_upwards [hp] with a ha
      simp only [Pi.mul_apply] at ha
      simp [mul_comm] at ha ⊢
      convert ha.symm using 2
      funext x; simp [Pi.mul_apply]
    have lhs_eq : ∫ a in s, MeasureTheory.condExp (ξ.preChannelSpace S hflow initial k) P (fun ω => if ξ.channel k ω = ℓ then (1 : ℝ) else 0) a * v a ℓ ∂P =
        ∫ a in s, MeasureTheory.condExp (ξ.preChannelSpace S hflow initial k) P (fun ω => v ω ℓ * (if ξ.channel k ω = ℓ then (1 : ℝ) else 0)) a ∂P := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_of_ae pull_out] with a ha
      rw [ha]
    rw [lhs_eq]
    rw [h_set_int]
    simp only [← rhs_eq]
    congr 1; ext x; split_ifs <;> ring
  · -- AEStronglyMeasurable for RHS
    have h_meas_state : Measurable (S.davisStateBeforeJump hflow ξ initial k) :=
      DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
    have h_meas_prob : ∀ ℓ, Measurable (fun z : DavisState Q n => S.davisChannelProbability z ℓ) := by
      intro ℓ
      simp_rw [davisChannelProbability]
      exact Measurable.div (IntensitiesMeasurable.measurable ℓ)
        (Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j)
    have h_meas_term : ∀ ℓ ∈ Finset.univ,
        Measurable[ξ.preChannelSpace S hflow initial k] (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ω ℓ) := by
      intro ℓ _
      apply Measurable.mul
      · have h_meas_state_pre : Measurable[ξ.preChannelSpace S hflow initial k]
            (S.davisStateBeforeJump hflow ξ initial k) :=
          DavisJumpNoise.stateBeforeJump_measurable_preChannel S hflow hf ξ initial k
        exact (h_meas_prob ℓ).comp h_meas_state_pre
      · exact hvmeas ℓ
    exact Measurable.aestronglyMeasurable (Finset.measurable_sum _ h_meas_term)

/-- Given the pre-channel information, the conditional expectation of the
realized reset increment is its normalized expected reset increment. -/
theorem DavisJumpNoise.ConditionalChannelLaw.condExp_realizedResetIncrement
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (g : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C) (k : ℕ) :
    P[davisRealizedResetIncrement S hflow ξ initial g k |
        ξ.preChannelSpace S hflow initial k] =ᵐ[P]
      fun ω => davisExpectedResetIncrement S g
        (davisStateBeforeJump S hflow ξ initial k ω) := by
  -- Let z(ω) = davisStateBeforeJump ... ω
  let z := fun ω => S.davisStateBeforeJump hflow ξ initial k ω
  -- Define v(ω, ℓ) = g(resetDavisState ℓ (z ω)) - g(z ω)
  let v := fun ω ℓ => g (S.resetDavisState ℓ (z ω)) - g (z ω)
  -- Rewrite davisRealizedResetIncrement using the indicator sum
  have h_eq : ∀ ω, davisRealizedResetIncrement S hflow ξ initial g k ω =
      ∑ ℓ : Fin m, (if ξ.channel k ω = ℓ then v ω ℓ else 0) := by
    intro ω
    simp only [davisRealizedResetIncrement]
    rw [Finset.sum_eq_single (ξ.channel k ω)]
    · simp [z, v]
    · intro b _ hb
      simp [hb.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp_rw [funext h_eq]
  -- v is bounded by 2C
  have hvbound : ∀ ω ℓ, |v ω ℓ| ≤ 2 * C := by
    intro ω ℓ
    simp only [v]
    calc |g (S.resetDavisState ℓ (z ω)) - g (z ω)|
        ≤ |g (S.resetDavisState ℓ (z ω))| + |g (z ω)| := abs_sub _ _
      _ ≤ C + C := by linarith [hg (S.resetDavisState ℓ (z ω)), hg (z ω)]
      _ = 2 * C := by ring
  -- v is pre-channel measurable
  have hvmeas : ∀ ℓ, Measurable[ξ.preChannelSpace S hflow initial k] (fun ω => v ω ℓ) := by
    intro ℓ
    simp only [v]
    apply Measurable.sub
    · apply Measurable.comp hgmeas
      apply Measurable.comp (hr.reset_measurable ℓ)
      exact DavisJumpNoise.stateBeforeJump_measurable_preChannel S hflow hf ξ initial k
    · apply Measurable.comp hgmeas
      exact DavisJumpNoise.stateBeforeJump_measurable_preChannel S hflow hf ξ initial k
  -- Apply condExp_channel_dependent_test
  have h_result := DavisJumpNoise.ConditionalChannelLaw.condExp_channel_dependent_test
    hf hr hξ hlaw k v hvmeas (2 * C) hvbound
  -- Now show the RHS equals davisExpectedResetIncrement
  have h_rhs : ∀ ω, ∑ ℓ : Fin m, S.davisChannelProbability (z ω) ℓ * v ω ℓ =
      davisExpectedResetIncrement S g (z ω) := by
    intro ω
    simp only [davisExpectedResetIncrement, v]
  have h_final : (fun ω => ∑ ℓ : Fin m, S.davisChannelProbability (z ω) ℓ * v ω ℓ) =ᵐ[P]
      fun ω => davisExpectedResetIncrement S g (z ω) := by
    exact MeasureTheory.ae_of_all P h_rhs
  -- Also need to show the sum form equals v(channel) form
  have h_sum_eq : ∀ ω, ∑ ℓ : Fin m, (if ξ.channel k ω = ℓ then v ω ℓ else 0) = v ω (ξ.channel k ω) := by
    intro ω
    rw [Finset.sum_eq_single (ξ.channel k ω)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h_lhs : (fun x => ∑ ℓ : Fin m, if ξ.channel k x = ℓ then v x ℓ else 0) =ᵐ[P]
      fun ω => v ω (ξ.channel k ω) := by
    exact MeasureTheory.ae_of_all P h_sum_eq
  have h_lhs_cond : P[fun x => ∑ ℓ : Fin m, if ξ.channel k x = ℓ then v x ℓ else 0 | ξ.preChannelSpace S hflow initial k] =ᶠ[ae P]
      P[fun ω => v ω (ξ.channel k ω) | ξ.preChannelSpace S hflow initial k] := MeasureTheory.condExp_congr_ae h_lhs
  exact h_lhs_cond.trans (h_result.trans h_final.symm)

/-- Every centered reset increment has conditional expectation zero before its
channel mark is sampled. -/
theorem DavisJumpNoise.ConditionalChannelLaw.condExp_centeredResetIncrement
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (g : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C) (k : ℕ) :
    P[davisCenteredResetIncrement S hflow ξ initial g k |
        ξ.preChannelSpace S hflow initial k] =ᵐ[P]
      (0 : Ω → ℝ) := by
  -- Write centered increment as difference
  have h_diff : ∀ ω, davisCenteredResetIncrement S hflow ξ initial g k ω =
      davisRealizedResetIncrement S hflow ξ initial g k ω -
      davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω) := by
    intro ω; rfl
  simp_rw [funext h_diff]
  -- Measurability of realized increment
  have h_real_meas : Measurable (fun ω => davisRealizedResetIncrement S hflow ξ initial g k ω) :=
    hξ.realizedResetIncrement S hflow hf hr initial g hgmeas k
  -- Measurability of expected increment (ambient)
  have h_meas_exp : Measurable (fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω)) :=
    (measurable_davisExpectedResetIncrement S hr g hgmeas).comp
      (DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k)
  -- Measurability of expected increment (pre-channel)
  have h_meas_exp_pre : Measurable[ξ.preChannelSpace S hflow initial k]
      (fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω)) :=
    DavisJumpNoise.expectedResetIncrement_measurable_preChannel S hflow hf hr ξ initial g hgmeas k
  -- Integrability of realized increment
  have h_int_real : Integrable (fun ω => davisRealizedResetIncrement S hflow ξ initial g k ω) P := by
    apply Integrable.mono' (integrable_const (2 * C))
    · exact h_real_meas.aestronglyMeasurable
    · filter_upwards with ω; exact abs_davisRealizedResetIncrement_le S hflow ξ initial g C hg k ω
  -- Integrability of expected increment
  have h_int_exp : Integrable (fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω)) P := by
    apply Integrable.mono' (integrable_const (2 * C))
    · exact h_meas_exp.aestronglyMeasurable
    · filter_upwards with ω; exact abs_davisExpectedResetIncrement_le_all S g _ C hg
  -- Use linearity of conditional expectation
  have h_sub := MeasureTheory.condExp_sub h_int_real h_int_exp (m := ξ.preChannelSpace S hflow initial k)
  refine h_sub.trans ?_
  -- Apply condExp_realizedResetIncrement
  have h_real_cond := condExp_realizedResetIncrement hf hr hξ hlaw g hgmeas C hg k
  -- The expected increment is pre-channel measurable, so E[expected | G] = expected
  have h_exp_cond : P[fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω) |
      ξ.preChannelSpace S hflow initial k] =
      fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω) :=
    MeasureTheory.condExp_of_stronglyMeasurable (hξ.preChannelSpace_le S hflow hf hr initial k)
      h_meas_exp_pre.stronglyMeasurable h_int_exp
  have h_diff_cond : (P[fun ω => davisRealizedResetIncrement S hflow ξ initial g k ω | ξ.preChannelSpace S hflow initial k] -
      P[fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω) |
        ξ.preChannelSpace S hflow initial k]) =ᵐ[P]
      (fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω)) -
        (fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω)) := by
    rw [h_exp_cond]
    filter_upwards [h_real_cond] with ω hω
    show (P[fun ω => davisRealizedResetIncrement S hflow ξ initial g k ω | ξ.preChannelSpace S hflow initial k] -
        fun ω => davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω)) ω = _
    simp only [Pi.sub_apply]
    rw [hω]
  exact h_diff_cond.trans (by simp : _ =ᵐ[P] (0 : Ω → ℝ))

end SHS
