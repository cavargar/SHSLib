import SHSLib.Core.DavisFiniteCompensatorBounds

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Integral consequences of the conditional channel law

This module upgrades the event-level conditional law of a finite channel mark
to identities for finite-valued test functions.  This is the measure-theoretic
bridge needed before centering reset increments whose coefficients depend on
the pre-channel history.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A function of a finite channel mark is the finite sum of its values times
singleton indicators. -/
theorem channel_value_eq_sum_indicators
    {Ω : Type*} (c : Ω → Fin m) (v : Fin m → ℝ) (ω : Ω) :
    v (c ω) = ∑ ℓ : Fin m, ({ω' | c ω' = ℓ}.indicator (fun _ => v ℓ)) ω := by
  rw [Finset.sum_eq_single (c ω)]
  · simp [Set.indicator]
  · intro b _ hb
    simp [Set.indicator, hb.symm]
  · intro h
    exact absurd (Finset.mem_univ (c ω)) h

/-- An `ENNReal`-valued function of a finite channel mark decomposes into
singleton indicators. -/
theorem channel_ennreal_eq_sum_indicators
    {Ω : Type*} (c : Ω → Fin m) (v : Fin m → ℝ≥0∞) (ω : Ω) :
    v (c ω) = ∑ ℓ : Fin m, ({ω' | c ω' = ℓ}.indicator (fun _ => v ℓ)) ω := by
  rw [Finset.sum_eq_single (c ω)]
  · simp [Set.indicator]
  · intro b _ hb
    simp [Set.indicator, hb.symm]
  · intro h
    exact absurd (Finset.mem_univ (c ω)) h

/-- Measurable jump noise makes the pre-channel information a subspace of the
ambient measurable space. -/
theorem DavisJumpNoise.MeasurableNoise.preChannelSpace_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k : ℕ) :
    ξ.preChannelSpace S hflow initial k ≤ mΩ := by
  rw [DavisJumpNoise.preChannelSpace]
  exact MeasurableSpace.comap_le_iff_le_map.mpr (Measurable.prodMk (hξ.preJumpHistory S hflow hf hr initial k) (hξ.holdingTime k))

/-- The event-level conditional channel law is exactly the lintegral identity
for a singleton indicator. -/
theorem DavisJumpNoise.ConditionalChannelLaw.lintegral_channel_indicator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (ℓ : Fin m) (A : Set Ω)
    (hA : MeasurableSet[ξ.preChannelSpace S hflow initial k] A) :
    ∫⁻ ω in A, ({ω' | ξ.channel k ω' = ℓ}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂P =
      ∫⁻ ω in A, ENNReal.ofReal (davisChannelProbability S
        (davisStateBeforeJump S hflow ξ initial k ω) ℓ) ∂P := by
  -- The indicator function {set}.indicator (fun _ => 1) equals 1 on the set and 0 outside
  -- So the lintegral over A equals P (A ∩ {ω | ξ.channel k ω = ℓ})
  have h_indicator : ∀ ω, ({ω' | ξ.channel k ω' = ℓ}.indicator (fun _ => (1 : ℝ≥0∞))) ω =
    if ξ.channel k ω = ℓ then 1 else 0 := by
    intro ω
    simp [Set.indicator, Set.mem_setOf_eq]
  simp_rw [h_indicator]
  -- The lintegral of an indicator equals the measure of the set
  have lhs_eq : ∫⁻ ω in A, (if ξ.channel k ω = ℓ then 1 else 0 : ℝ≥0∞) ∂P = P (A ∩ {ω | ξ.channel k ω = ℓ}) := by
    have meas_set : MeasurableSet {ω | ξ.channel k ω = ℓ} := by
      have := hξ.channel k
      exact this (measurableSet_singleton ℓ)
    have : (fun ω => (if ξ.channel k ω = ℓ then 1 else 0 : ℝ≥0∞)) =
        Set.indicator {ω | ξ.channel k ω = ℓ} (fun _ => 1) := by
      ext ω; simp [Set.indicator]
    rw [this, setLIntegral_indicator meas_set]
    simp [Set.inter_comm]
  rw [lhs_eq]
  -- Apply the conditional channel law
  rw [hlaw.channel_identity k ℓ A hA]
  rfl

/-- Event-level conditional channel probabilities determine integrals of every
nonnegative finite-valued channel test function. -/
theorem DavisJumpNoise.ConditionalChannelLaw.lintegral_channel_test
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (A : Set Ω)
    (hA : MeasurableSet[ξ.preChannelSpace S hflow initial k] A)
    (v : Fin m → ℝ≥0∞) :
    ∫⁻ ω in A, v (ξ.channel k ω) ∂P =
      ∫⁻ ω in A, ∑ ℓ : Fin m,
        ENNReal.ofReal (davisChannelProbability S
          (davisStateBeforeJump S hflow ξ initial k ω) ℓ) * v ℓ ∂P := by
  -- Expand v (ξ.channel k ω) using channel_ennreal_eq_sum_indicators
  have h_expand : ∀ ω, v (ξ.channel k ω) = ∑ ℓ : Fin m,
      ({ω' | ξ.channel k ω' = ℓ}.indicator (fun _ => v ℓ)) ω :=
    channel_ennreal_eq_sum_indicators (ξ.channel k) v
  simp_rw [h_expand]
  -- Use lintegral_finset_sum to pull lintegral inside
  -- Measurability of indicator
  have meas_indicator : ∀ i : Fin m, MeasurableSet {ω | ξ.channel k ω = i} := fun i =>
    hξ.channel k (measurableSet_singleton i)
  have meas_f : ∀ i : Fin m, Measurable (fun ω => ({ω' | ξ.channel k ω' = i}.indicator (fun _ => v i)) ω) :=
    fun i => Measurable.indicator (measurable_const) (meas_indicator i)
  rw [MeasureTheory.lintegral_finset_sum (f := fun i : Fin m => fun ω => ({ω' | ξ.channel k ω' = i}.indicator (fun _ => v i)) ω) (s := Finset.univ) (by simp [meas_f])]
  -- Rewrite RHS to move lintegral inside
  have meas_ofReal : ∀ i : Fin m, Measurable (fun ω => ENNReal.ofReal (davisChannelProbability S (davisStateBeforeJump S hflow ξ initial k ω) i)) := by
    intro i
    have h_meas_state : Measurable (davisStateBeforeJump S hflow ξ initial k) :=
      DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
    have h_meas_total : Measurable (fun z : DavisState Q n => S.totalIntensity z) :=
      Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j
    have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z i) := by
      unfold davisChannelProbability
      exact Measurable.div (IntensitiesMeasurable.measurable i) h_meas_total
    exact Measurable.ennreal_ofReal (h_meas_prob.comp h_meas_state)
  have meas_rhs : ∀ i : Fin m, Measurable (fun ω => ENNReal.ofReal (davisChannelProbability S (davisStateBeforeJump S hflow ξ initial k ω) i) * v i) := by
    intro i
    apply Measurable.mul_const
    apply Measurable.ennreal_ofReal
    have h_meas_state : Measurable (davisStateBeforeJump S hflow ξ initial k) :=
      DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
    have h_meas_total : Measurable (fun z : DavisState Q n => S.totalIntensity z) :=
      Finset.measurable_sum _ fun j _ => IntensitiesMeasurable.measurable j
    have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z i) := by
      unfold davisChannelProbability
      exact Measurable.div (IntensitiesMeasurable.measurable i) h_meas_total
    exact h_meas_prob.comp h_meas_state
  rw [MeasureTheory.lintegral_finset_sum (f := fun ℓ : Fin m => fun ω => ENNReal.ofReal (davisChannelProbability S (davisStateBeforeJump S hflow ξ initial k ω) ℓ) * v ℓ) (s := Finset.univ) (by simp [meas_rhs])]
  · refine Finset.sum_congr rfl ?_
    intro i _
    -- Apply lintegral_channel_indicator and factor out v i
    -- Rewrite indicator (fun _ => v i) = v i * indicator 1
    have h_eq : ∀ ω, ({ω' | ξ.channel k ω' = i}.indicator (fun _ => v i)) ω = v i * ({ω' | ξ.channel k ω' = i}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
      intro ω
      simp [Set.indicator]
    -- Use lintegral_channel_indicator to show ∫⁻ indicator 1 = ∫⁻ ofReal(prob)
    have lint_eq := lintegral_channel_indicator hξ hlaw k i A hA
    -- Rewrite indicator (fun _ => v i) = v i * indicator 1
    simp_rw [h_eq]
    -- Now factor out v i from both sides
    have meas_ind : Measurable ({ω' | ξ.channel k ω' = i}.indicator fun x => (1 : ℝ≥0∞)) :=
      Measurable.indicator measurable_const (meas_indicator i)
    have lhs_eq : ∫⁻ ω in A, v i * ({ω' | ξ.channel k ω' = i}.indicator (fun x => 1)) ω ∂P =
        v i * ∫⁻ ω in A, ({ω' | ξ.channel k ω' = i}.indicator (fun x => 1)) ω ∂P := by
      rw [MeasureTheory.lintegral_const_mul (f := fun ω => ({ω' | ξ.channel k ω' = i}.indicator (fun x => 1)) ω) (r := v i) meas_ind]
    have rhs_eq : ∫⁻ ω in A, ENNReal.ofReal (S.davisChannelProbability (davisStateBeforeJump S hflow ξ initial k ω) i) * v i ∂P =
        v i * ∫⁻ ω in A, ENNReal.ofReal (S.davisChannelProbability (davisStateBeforeJump S hflow ξ initial k ω) i) ∂P := by
      have : ∀ ω, ENNReal.ofReal (S.davisChannelProbability (davisStateBeforeJump S hflow ξ initial k ω) i) * v i = v i * ENNReal.ofReal (S.davisChannelProbability (davisStateBeforeJump S hflow ξ initial k ω) i) := fun ω => mul_comm _ _
      simp_rw [this]
      rw [MeasureTheory.lintegral_const_mul (f := fun ω => ENNReal.ofReal (S.davisChannelProbability (davisStateBeforeJump S hflow ξ initial k ω) i)) (r := v i) (meas_ofReal i)]
    rw [lhs_eq, rhs_eq, lint_eq]

/-- On a finite measure space, the preceding identity specializes to bounded
real-valued tests of the channel mark. -/
theorem DavisJumpNoise.ConditionalChannelLaw.integral_channel_test
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (k : ℕ) (A : Set Ω)
    (hA : MeasurableSet[ξ.preChannelSpace S hflow initial k] A)
    (v : Fin m → ℝ) :
    ∫ ω in A, v (ξ.channel k ω) ∂P =
      ∫ ω in A, ∑ ℓ : Fin m,
        davisChannelProbability S
          (davisStateBeforeJump S hflow ξ initial k ω) ℓ * v ℓ ∂P := by
  -- Expand v (ξ.channel k ω) using channel_value_eq_sum_indicators
  have h_expand : ∀ ω, v (ξ.channel k ω) = ∑ ℓ : Fin m,
      ({ω' | ξ.channel k ω' = ℓ}.indicator (fun _ => v ℓ)) ω :=
    channel_value_eq_sum_indicators (ξ.channel k) v
  simp_rw [h_expand]
  -- Convert set integrals to restricted measure integrals
  show ∫ ω, ∑ ℓ, ({ω' | ξ.channel k ω' = ℓ}.indicator fun x => v ℓ) ω ∂(P.restrict A) =
       ∫ ω, ∑ ℓ, S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) ℓ * v ℓ ∂(P.restrict A)
  -- Need to show integrability for the LHS
  have h_integrable_lhs : ∀ i ∈ Finset.univ, Integrable (fun ω => ({ω' | ξ.channel k ω' = i}.indicator fun x => v i) ω) (P.restrict A) := by
    intro i _
    apply Integrable.indicator
    · exact integrable_const (v i)
    · have : MeasurableSet {ω' | ξ.channel k ω' = i} := by
        have hch := hξ.channel k
        exact hch (measurableSet_singleton i)
      exact this
  rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin m)) h_integrable_lhs]
  -- Push integral inside sum on RHS
  have h_integrable_rhs : ∀ i ∈ Finset.univ, Integrable (fun ω => S.davisChannelProbability (S.davisStateBeforeJump hflow ξ initial k ω) i * v i) (P.restrict A) := by
    intro i _
    apply Integrable.mul_const
    refine Integrable.mono' (MeasureTheory.integrable_const 1) ?_ ?_
    · have h_meas_state : Measurable (davisStateBeforeJump S hflow ξ initial k) :=
        DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
      have h_meas_total : Measurable (fun z : DavisState Q n => S.totalIntensity z) := by
        exact Finset.measurable_sum _ fun i _ => IntensitiesMeasurable.measurable i
      have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z i) := by
        unfold davisChannelProbability
        exact Measurable.div (IntensitiesMeasurable.measurable i) h_meas_total
      exact (h_meas_prob.comp h_meas_state).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs]
      have h_nonneg := davisChannelProbability_nonneg S (S.davisStateBeforeJump hflow ξ initial k ω) i
      by_cases hz : S.totalIntensity (S.davisStateBeforeJump hflow ξ initial k ω) ≠ 0
      · have h_sum := sum_davisChannelProbability S (S.davisStateBeforeJump hflow ξ initial k ω) hz
        have h_le_one : davisChannelProbability S (S.davisStateBeforeJump hflow ξ initial k ω) i ≤ 1 := by
          calc davisChannelProbability S (S.davisStateBeforeJump hflow ξ initial k ω) i
              ≤ ∑ ℓ : Fin m, davisChannelProbability S (S.davisStateBeforeJump hflow ξ initial k ω) ℓ := by
                exact Finset.single_le_sum (fun ℓ _ => davisChannelProbability_nonneg _ _ ℓ) (Finset.mem_univ i)
            _ = 1 := h_sum
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · have hz' : S.totalIntensity (S.davisStateBeforeJump hflow ξ initial k ω) = 0 := not_not.mp hz
        simp [hz', davisChannelProbability]
  rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin m)) h_integrable_rhs]
  congr 1
  ext i
  -- For each i, show that the two integrals are equal
  -- LHS: ∫ a in A, indicator({ξ.channel k = i}) (v i) ∂P = v i * P(A ∩ {ξ.channel k = i})
  -- RHS: ∫ a in A, davisChannelProbability ... i * v i ∂P = v i * ∫ a in A, davisChannelProbability ... i ∂P
  rw [MeasureTheory.integral_mul_const]
  -- LHS simplifies using indicator integral
  have meas_set : MeasurableSet {ω | ξ.channel k ω = i} := hξ.channel k (measurableSet_singleton i)
  have lhs_simp : ∫ (a : Ω) in A, ({ω' | ξ.channel k ω' = i}.indicator fun x => v i) a ∂P =
      v i * (P (A ∩ {ω | ξ.channel k ω = i})).toReal := by
    rw [setIntegral_indicator meas_set]
    simp [mul_comm]
    left
    rfl
  rw [lhs_simp]
  rw [mul_comm]
  congr 1
  -- Need: (P (A ∩ {ξ.channel k = i})).toReal = ∫ a in A, davisChannelProbability ... i ∂P
  -- Use lintegral_channel_indicator
  have lint_eq := lintegral_channel_indicator hξ hlaw k i A hA
  -- lint_eq says: ∫⁻ ω in A, indicator({ξ.channel k = i}) 1 ∂P = ∫⁻ ω in A, ofReal (davisChannelProbability ...) i ∂P
  -- The LHS is P(A ∩ {ξ.channel k = i})
  rw [setLIntegral_indicator meas_set] at lint_eq
  simp at lint_eq
  -- Now lint_eq : P ({ω | ξ.channel k ω = i} ∩ A) = ∫⁻ ω in A, ofReal (davisChannelProbability ...) i ∂P
  rw [Set.inter_comm] at lint_eq
  -- Convert real integral to lintegral
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · rw [← lint_eq]
  · filter_upwards with ω
    exact davisChannelProbability_nonneg S _ i
  · -- AEStronglyMeasurable
    have h_meas_state : Measurable (davisStateBeforeJump S hflow ξ initial k) :=
        DavisJumpNoise.MeasurableNoise.stateBeforeJump S hflow hf hr hξ initial k
    have h_meas_total : Measurable (fun z : DavisState Q n => S.totalIntensity z) := by
        exact Finset.measurable_sum _ fun i _ => IntensitiesMeasurable.measurable i
    have h_meas_prob : Measurable (fun z : DavisState Q n => S.davisChannelProbability z i) := by
        unfold davisChannelProbability
        exact Measurable.div (IntensitiesMeasurable.measurable i) h_meas_total
    exact (h_meas_prob.comp h_meas_state).aestronglyMeasurable



end SHS
