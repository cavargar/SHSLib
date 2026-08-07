import SHSLib.Core.DavisResetOccupationRegular
import SHSLib.Core.DavisOneSegmentTruncatedCompensation

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The conditional holding-time law at a history-measurable threshold

The conditional holding-time law states the survivor identity

`P (A ∩ {u < h_k}) = ∫⁻ A, Sur_k(u)`

for every event `A` of the pre-jump history at index `k` and every
*deterministic* threshold `u`.  Discharging the conditional step of the
one-segment martingale needs the same identity for a *random* threshold: the
age `s − T_k` of the active segment at an observation time `s` is not
deterministic, it is a function of the history at index `k`.

This module proves the survivor identity for an arbitrary threshold that is
measurable with respect to the pre-jump history at index `k`.

* For a threshold with countable range the identity follows from the
  deterministic one by splitting the conditioning event along the level sets
  of the threshold, which are again history events.
* A general history-measurable threshold is approximated from above by its
  dyadic upper roundings, which are countably valued, decrease to it, and are
  again history measurable.  The events `{u_j < h_k}` then increase to
  `{u < h_k}`, so the left-hand sides converge; the survivor factors converge
  by continuity of the survivor factor in the duration, so the right-hand
  sides converge by dominated convergence.

The specialization to the age of the segment active at a fixed elapsed time is
recorded at the end: it is the conditional probability that segment `k`, known
to have started at `T_k ≤ s`, is still running at `s`.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Continuity of the survivor factor in the duration -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Under continuity of the total intensity along the flow, the integrated
hazard is continuous in the elapsed duration. -/
theorem continuous_davisIntegratedHazard
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow) (z : DavisState Q n) :
    Continuous fun u : ℝ≥0 => davisIntegratedHazard S hflow z u := by
  have heq : (fun u : ℝ≥0 => davisIntegratedHazard S hflow z u) =
      fun u : ℝ≥0 => ∫ s in (0)..(u : ℝ),
        S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
    funext u
    unfold davisIntegratedHazard
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    erw [← intervalIntegral.integral_of_le u.2]
    rfl
  rw [heq]
  have hprim : Continuous fun b : ℝ => ∫ s in (0)..b,
      S.totalIntensity (davisFlow S hflow s.toNNReal z) :=
    intervalIntegral.continuous_primitive (fun a b => (hcont z).intervalIntegrable a b) 0
  exact hprim.comp NNReal.continuous_coe

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The survivor factor of a deterministic segment is continuous in the
elapsed duration. -/
theorem continuous_davisSegmentSurvivor
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow) (z : DavisState Q n) :
    Continuous fun u : ℝ≥0 => davisSegmentSurvivor S hflow z u := by
  unfold davisSegmentSurvivor
  exact (continuous_davisIntegratedHazard S hflow hcont z).neg.rexp

/-! ## Dyadic upper roundings on `ℝ≥0` -/

/-- The dyadic upper rounding of a nonnegative real at scale `2⁻ʲ`. -/
def nnrealDyadicUpper (j : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  ((⌊x * 2 ^ j⌋₊ + 1 : ℕ) : ℝ≥0) / 2 ^ j

theorem lt_nnrealDyadicUpper (j : ℕ) (x : ℝ≥0) : x < nnrealDyadicUpper j x := by
  unfold nnrealDyadicUpper
  rw [lt_div_iff₀ (by positivity)]
  push_cast
  exact Nat.lt_floor_add_one (x * 2 ^ j)

theorem nnrealDyadicUpper_le (j : ℕ) (x : ℝ≥0) :
    nnrealDyadicUpper j x ≤ x + (2 ^ j)⁻¹ := by
  unfold nnrealDyadicUpper
  rw [div_le_iff₀ (by positivity)]
  have h : (⌊x * 2 ^ j⌋₊ : ℝ≥0) ≤ x * 2 ^ j := Nat.floor_le (by positivity)
  push_cast
  calc (⌊x * 2 ^ j⌋₊ : ℝ≥0) + 1 ≤ x * 2 ^ j + 1 := by gcongr
    _ = (x + (2 ^ j)⁻¹) * 2 ^ j := by field_simp

theorem nnrealDyadicUpper_succ_le (j : ℕ) (x : ℝ≥0) :
    nnrealDyadicUpper (j + 1) x ≤ nnrealDyadicUpper j x := by
  unfold nnrealDyadicUpper
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ⌊x * 2 ^ (j + 1)⌋₊ ≤ 2 * ⌊x * 2 ^ j⌋₊ + 1 := by
    have hlt : (x : ℝ≥0) * 2 ^ (j + 1) < ((2 * ⌊x * 2 ^ j⌋₊ + 2 : ℕ) : ℝ≥0) := by
      have h := Nat.lt_floor_add_one (x * 2 ^ j)
      push_cast
      calc x * 2 ^ (j + 1) = (x * 2 ^ j) * 2 := by ring
        _ < ((⌊x * 2 ^ j⌋₊ : ℝ≥0) + 1) * 2 := by gcongr
        _ = 2 * ⌊x * 2 ^ j⌋₊ + 2 := by ring
    have h2 : ⌊x * 2 ^ (j + 1)⌋₊ < 2 * ⌊x * 2 ^ j⌋₊ + 2 := (Nat.floor_lt (zero_le _)).2 hlt
    omega
  have h3 : ((⌊x * 2 ^ (j + 1)⌋₊ : ℝ≥0) + 1) ≤ 2 * (⌊x * 2 ^ j⌋₊ : ℝ≥0) + 2 := by
    have h4 : ((⌊x * 2 ^ (j + 1)⌋₊ : ℕ) : ℝ≥0) ≤ ((2 * ⌊x * 2 ^ j⌋₊ + 1 : ℕ) : ℝ≥0) := by
      exact_mod_cast h1
    push_cast at h4
    calc (⌊x * 2 ^ (j + 1)⌋₊ : ℝ≥0) + 1 ≤ (2 * (⌊x * 2 ^ j⌋₊ : ℝ≥0) + 1) + 1 := by gcongr
      _ = 2 * (⌊x * 2 ^ j⌋₊ : ℝ≥0) + 2 := by ring
  push_cast
  calc ((⌊x * 2 ^ (j + 1)⌋₊ : ℝ≥0) + 1) * 2 ^ j
      ≤ (2 * (⌊x * 2 ^ j⌋₊ : ℝ≥0) + 2) * 2 ^ j := by gcongr
    _ = ((⌊x * 2 ^ j⌋₊ : ℝ≥0) + 1) * 2 ^ (j + 1) := by ring

theorem tendsto_nnrealDyadicUpper (x : ℝ≥0) :
    Filter.Tendsto (fun j => nnrealDyadicUpper j x) Filter.atTop (nhds x) := by
  have htop : Filter.Tendsto (fun j : ℕ => x + ((2 : ℝ≥0) ^ j)⁻¹)
      Filter.atTop (nhds (x + 0)) := by
    refine Filter.Tendsto.const_add x ?_
    simpa [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) (by norm_num) (by norm_num))
  rw [add_zero] at htop
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
    (fun j => (lt_nnrealDyadicUpper j x).le) (fun j => nnrealDyadicUpper_le j x)

theorem measurable_nnrealDyadicUpper (j : ℕ) : Measurable (nnrealDyadicUpper j) := by
  unfold nnrealDyadicUpper
  fun_prop

theorem countable_range_nnrealDyadicUpper (j : ℕ) :
    (Set.range (nnrealDyadicUpper j)).Countable := by
  refine Set.Countable.mono (s₁ := Set.range (nnrealDyadicUpper j))
    (s₂ := Set.range fun i : ℕ => ((i : ℝ≥0) / 2 ^ j)) ?_ (Set.countable_range _)
  rintro _ ⟨x, rfl⟩
  exact ⟨⌊x * 2 ^ j⌋₊ + 1, by simp [nnrealDyadicUpper]⟩

/-! ## The survivor identity at a countably valued threshold -/

/-- The conditional holding-time law for a countably valued threshold that is
measurable with respect to the pre-jump history. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.measure_lt_holdingTime_of_countableRange
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (u : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (hcount : (Set.range u).Countable)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    P (A ∩ {ω | u ω < ξ.holdingTime k ω}) =
      ∫⁻ ω in A, ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u ω)) ∂P := by
  classical
  set B : ℝ≥0 → Set Ω := fun c => A ∩ {ω | u ω = c} with hB
  have hBH : ∀ c, MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (B c) := fun c => hA.inter (hu (measurableSet_singleton c))
  have hBm : ∀ c, MeasurableSet (B c) := fun c =>
    (ξ.preJumpHistoryFiltration S hflow hf hr hξ initial).le k _ (hBH c)
  have hdisjB : ∀ c c' : ℝ≥0, c ≠ c' → Disjoint (B c) (B c') := by
    intro c c' hcc'
    rw [Set.disjoint_left]
    rintro ω ⟨-, hω⟩ ⟨-, hω'⟩
    exact hcc' (hω ▸ hω')
  have hAeq : A = ⋃ c ∈ Set.range u, B c := by
    ext ω
    simp only [hB, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun hω => ⟨u ω, ⟨ω, rfl⟩, hω, rfl⟩, fun ⟨_, _, hω, _⟩ => hω⟩
  have hCeq : A ∩ {ω | u ω < ξ.holdingTime k ω} =
      ⋃ c ∈ Set.range u, (B c ∩ {ω | c < ξ.holdingTime k ω}) := by
    ext ω
    simp only [hB, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨hωA, hωlt⟩
      exact ⟨u ω, ⟨ω, rfl⟩, ⟨hωA, rfl⟩, hωlt⟩
    · rintro ⟨c, -, ⟨hωA, hωc⟩, hωlt⟩
      exact ⟨hωA, by rw [hωc]; exact hωlt⟩
  have hdisj : (Set.range u).PairwiseDisjoint
      fun c => B c ∩ {ω | c < ξ.holdingTime k ω} := by
    intro c _ c' _ hcc'
    exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hdisjB c c' hcc')
  have hdisj' : (Set.range u).PairwiseDisjoint B := fun c _ c' _ hcc' => hdisjB c c' hcc'
  rw [hCeq, measure_biUnion hcount hdisj
    (fun c _ => (hBm c).inter (measurableSet_lt measurable_const (hξ.holdingTime k)))]
  conv_rhs => rw [hAeq]
  rw [lintegral_biUnion hcount (fun c _ => hBm c) hdisj']
  refine tsum_congr fun c => ?_
  rw [hlaw.survivor_identity k (c : ℝ≥0) (B c) (hBH c)]
  refine setLIntegral_congr_fun (hBm c) ?_
  intro ω hω
  have h2 : u ω = (c : ℝ≥0) := hω.2
  simp only [h2]

/-! ## The survivor identity at an arbitrary history-measurable threshold -/

/-- **The conditional holding-time law at a history-measurable threshold.**
The survivor identity of the conditional holding-time law holds for every
threshold measurable with respect to the pre-jump history at the same index,
not only for deterministic ones. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.measure_lt_holdingTime_of_historyMeasurable
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (k : ℕ) (u : Ω → ℝ≥0)
    (hu : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] u)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    P (A ∩ {ω | u ω < ξ.holdingTime k ω}) =
      ∫⁻ ω in A, ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u ω)) ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  -- the dyadic upper approximations of the threshold
  set v : ℕ → Ω → ℝ≥0 := fun j ω => nnrealDyadicUpper j (u ω) with hv
  have hvH : ∀ j, Measurable[F k] (v j) := fun j =>
    (measurable_nnrealDyadicUpper j).comp hu
  have hvcount : ∀ j, (Set.range (v j)).Countable := by
    intro j
    refine Set.Countable.mono ?_ (countable_range_nnrealDyadicUpper j)
    rintro _ ⟨ω, rfl⟩
    exact ⟨u ω, rfl⟩
  have hAm : MeasurableSet A := (F.le k) _ hA
  have hstep : ∀ j, P (A ∩ {ω | v j ω < ξ.holdingTime k ω}) =
      ∫⁻ ω in A, ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
          (v j ω)) ∂P :=
    fun j => hlaw.measure_lt_holdingTime_of_countableRange k (v j) (hvH j)
      (hvcount j) A hA
  -- the left-hand sides increase to the left-hand side of the claim
  set C : ℕ → Set Ω := fun j => A ∩ {ω | v j ω < ξ.holdingTime k ω} with hC
  have hCmono : Monotone C := by
    refine monotone_nat_of_le_succ fun j => ?_
    intro ω hω
    exact ⟨hω.1, lt_of_le_of_lt (nnrealDyadicUpper_succ_le j (u ω)) hω.2⟩
  have hCunion : ⋃ j, C j = A ∩ {ω | u ω < ξ.holdingTime k ω} := by
    ext ω
    simp only [hC, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hωA, hωlt⟩
      exact ⟨hωA, lt_of_le_of_lt (le_of_lt (lt_nnrealDyadicUpper j (u ω))) hωlt⟩
    · rintro ⟨hωA, hωlt⟩
      obtain ⟨j, hj⟩ := (Filter.Tendsto.eventually_lt_const hωlt
        (tendsto_nnrealDyadicUpper (u ω))).exists
      exact ⟨j, hωA, hj⟩
  have hCmeas : ∀ j, MeasurableSet (C j) := fun j =>
    hAm.inter (measurableSet_lt (((hvH j).mono (F.le k) le_rfl)) (hξ.holdingTime k))
  have hLHS : Filter.Tendsto (fun j => P (C j)) Filter.atTop
      (nhds (P (A ∩ {ω | u ω < ξ.holdingTime k ω}))) := by
    rw [← hCunion]
    exact tendsto_measure_iUnion_atTop hCmono
  -- the right-hand sides converge by dominated convergence
  have hHmeas : Measurable fun ω =>
      (davisPreJumpHistory S hflow ξ initial k ω).currentState :=
    (DavisPreJumpHistory.measurable_currentState k).comp
      (hξ.preJumpHistory S hflow hf hr initial k)
  have hfmeas : ∀ j, Measurable fun ω => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (v j ω)) := by
    intro j
    exact (hsurv.comp (hHmeas.prodMk ((hvH j).mono (F.le k) le_rfl))).ennreal_ofReal
  have hbound : ∀ j, ∀ᵐ ω ∂(P.restrict A), ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (v j ω)) ≤ 1 := by
    intro j
    filter_upwards with ω
    have h := DavisPreJumpHistory.nextSurvivor_mem_Ioc S hflow
      (davisPreJumpHistory S hflow ξ initial k ω) (v j ω)
    exact ENNReal.ofReal_le_one.2 h.2
  have hconv : ∀ᵐ ω ∂(P.restrict A), Filter.Tendsto (fun j => ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (v j ω)))
      Filter.atTop (nhds (ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u ω)))) := by
    filter_upwards with ω
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    exact ((continuous_davisSegmentSurvivor S hflow hcont
      (davisPreJumpHistory S hflow ξ initial k ω).currentState).tendsto
        (u ω)).comp (tendsto_nnrealDyadicUpper (u ω))
  have hRHS : Filter.Tendsto (fun j => ∫⁻ ω in A, ENNReal.ofReal
      ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (v j ω)) ∂P)
      Filter.atTop (nhds (∫⁻ ω in A, ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u ω)) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
      (fun j => hfmeas j) hbound ?_ hconv
    simp
  refine tendsto_nhds_unique (hLHS.congr fun j => hstep j) hRHS

/-! ## The age of the active segment as a threshold -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Cumulative jump times are finite sums of holding times. -/
theorem DavisJumpNoise.jumpTime_eq_sum_range {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (k : ℕ) (ω : Ω) :
    ξ.jumpTime k ω = ∑ i ∈ Finset.range k, ξ.holdingTime i ω := by
  induction k with
  | zero => simp
  | succ k ih => rw [DavisJumpNoise.jumpTime_succ, ih, Finset.sum_range_succ]

omit [MeasurableSingletonClass Q] in
/-- Each holding-time coordinate of a finite history is measurable. -/
theorem DavisPreJumpHistory.measurable_holdingTime (k : ℕ) (i : Fin k) :
    Measurable fun H : DavisPreJumpHistory Q n m k => H.holdingTime i := by
  have hencode : Measurable fun H : DavisPreJumpHistory Q n m k =>
      (H.holdingTime, H.channel, H.stateAfterJump) := by
    rw [measurable_iff_comap_le]
    rfl
  exact (measurable_pi_apply i).comp hencode.fst

/-- The `k`-th cumulative jump time is measurable with respect to the pre-jump
history at index `k`. -/
theorem DavisJumpNoise.measurable_jumpTime_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k : ℕ) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (ξ.jumpTime k) := by
  have hH := ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial k
  have heq : ξ.jumpTime k = fun ω => ∑ i : Fin k,
      (davisPreJumpHistory S hflow ξ initial k ω).holdingTime i := by
    funext ω
    rw [ξ.jumpTime_eq_sum_range k ω, Finset.sum_range fun i => ξ.holdingTime i ω]
    rfl
  rw [heq]
  exact Finset.measurable_sum _ fun i _ =>
    (DavisPreJumpHistory.measurable_holdingTime k i).comp hH

/-- **Conditional survival of the active segment.**  On a history event at
index `k`, the conditional probability that segment `k` — which started at the
cumulative jump time `T_k` — is still running at elapsed time `s` is the
survivor factor evaluated at the age `s − T_k`. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.measure_segment_active
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (k : ℕ) (s : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    P (A ∩ {ω | s - ξ.jumpTime k ω < ξ.holdingTime k ω}) =
      ∫⁻ ω in A, ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow
          (s - ξ.jumpTime k ω)) ∂P :=
  hlaw.measure_lt_holdingTime_of_historyMeasurable hcont hsurv k
    (fun ω => s - ξ.jumpTime k ω)
    (measurable_const.sub
      (ξ.measurable_jumpTime_preJumpHistory S hflow hf hr hξ initial k))
    A hA

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- On the event that segment `k` has started, being still active at elapsed
time `s` is exactly the age at `s` being below the holding time. -/
theorem davisSegmentActive_iff_age_lt_holdingTime {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (k : ℕ) (s : ℝ≥0) (ω : Ω)
    (hstart : ξ.jumpTime k ω ≤ s) :
    (¬ ξ.jumpTime (k + 1) ω ≤ s) ↔ s - ξ.jumpTime k ω < ξ.holdingTime k ω := by
  rw [DavisJumpNoise.jumpTime_succ, not_le, tsub_lt_iff_right hstart,
    add_comm (ξ.holdingTime k ω) (ξ.jumpTime k ω)]

end SHS
