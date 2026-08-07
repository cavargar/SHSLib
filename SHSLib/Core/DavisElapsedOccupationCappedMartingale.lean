import SHSLib.Core.DavisElapsedBoundedRegime

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The deterministic-cap increment law as a capped martingale property

The concrete martingale, generator, and Dynkin statements assembled so far all
take the deterministic-cap increment law as their remaining structural input.
That law is stated as an eventwise centering property of two-time increments.

This module identifies it with a standard object: the law holds exactly when
every deterministic jump-capped occupation-centered approximation is itself a
martingale for the given filtration.  One direction is immediate from the
set-integral characterisation of martingales; the converse uses observability
and an integrable elapsed occupation envelope to supply adaptedness and
integrability, and then the conditional-expectation form of the law.

The module also records the elementary pathwise structure of the capped
increments: they are additive in time, vanish on degenerate intervals, and
vanish outright once the cap has already been exhausted before the initial
time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Pathwise structure of capped increments -/

/-- The active segment index is monotone in elapsed time. -/
theorem DavisJumpNoise.activeSegmentIndex_mono {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive) {s t : ℝ≥0} (hst : s ≤ t)
    (ω : Ω) :
    ξ.activeSegmentIndex hne s ω ≤ ξ.activeSegmentIndex hne t ω :=
  (ξ.jumpTime_le_iff_le_activeSegmentIndex hne _ t ω).mp
    ((ξ.jumpTime_activeSegmentIndex_le hne s ω).trans hst)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A capped increment over a degenerate interval vanishes. -/
theorem davisStoppedElapsedOccupationCenteredResetIncrement_self
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s : ℝ≥0) (ω : Ω) :
    davisStoppedElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g N s s ω = 0 :=
  sub_self _

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Capped increments are additive along consecutive time intervals. -/
theorem davisStoppedElapsedOccupationCenteredResetIncrement_add
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s t u : ℝ≥0) (ω : Ω) :
    davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t ω +
      davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N t u ω =
      davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s u ω := by
  unfold davisStoppedElapsedOccupationCenteredResetIncrement
  ring

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Once the jump cap has been exhausted before the initial time, the capped
approximation no longer moves. -/
theorem davisStoppedElapsedOccupationCenteredResetIncrement_eq_zero_of_cap_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω)
    (hN : N ≤ ξ.activeSegmentIndex hne s ω) :
    davisStoppedElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g N s t ω = 0 := by
  -- Since s ≤ t, the active segment index is monotone
  have h_monotone : ξ.activeSegmentIndex hne s ω ≤ ξ.activeSegmentIndex hne t ω :=
    DavisJumpNoise.activeSegmentIndex_mono ξ hne hst ω
  -- So N ≤ activeSegmentIndex at time t as well
  have hN_t : N ≤ ξ.activeSegmentIndex hne t ω := Nat.le_trans hN h_monotone
  -- At both times, min N k = N and the compensation term is 0
  have hmin_s : min N (ξ.activeSegmentIndex hne s ω) = N := Nat.min_eq_left hN
  have hmin_t : min N (ξ.activeSegmentIndex hne t ω) = N := Nat.min_eq_left hN_t
  -- Unfold the increment definition
  unfold davisStoppedElapsedOccupationCenteredResetIncrement
  -- Show the realized sums are equal
  have hreal_s : davisFiniteRealizedResetSum S hflow ξ initial g
      (min N (ξ.activeSegmentIndex hne s ω)) ω =
      davisFiniteRealizedResetSum S hflow ξ initial g N ω := by
    rw [hmin_s]
  have hreal_t : davisFiniteRealizedResetSum S hflow ξ initial g
      (min N (ξ.activeSegmentIndex hne t ω)) ω =
      davisFiniteRealizedResetSum S hflow ξ initial g N ω := by
    rw [hmin_t]
  -- Show the stopped elapsed reset occupations are equal (both reduce to davisFiniteResetOccupation)
  have hocc_s : davisStoppedElapsedResetOccupation S hflow ξ hne initial g N s ω =
      davisFiniteResetOccupation S hflow g ξ initial N ω := by
    unfold davisStoppedElapsedResetOccupation
    have hk_s : ξ.activeSegmentIndex hne s ω ≥ N := hN
    simp [hk_s]
  have hocc_t : davisStoppedElapsedResetOccupation S hflow ξ hne initial g N t ω =
      davisFiniteResetOccupation S hflow g ξ initial N ω := by
    unfold davisStoppedElapsedResetOccupation
    have hk_t : ξ.activeSegmentIndex hne t ω ≥ N := hN_t
    simp [hk_t]
  -- Now both centered reset sums are equal
  have hsum_s : davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N s ω =
      davisFiniteRealizedResetSum S hflow ξ initial g N ω -
      davisFiniteResetOccupation S hflow g ξ initial N ω := by
    unfold davisStoppedElapsedOccupationCenteredResetSum
    rw [hmin_s, hocc_s]
  have hsum_t : davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t ω =
      davisFiniteRealizedResetSum S hflow ξ initial g N ω -
      davisFiniteResetOccupation S hflow g ξ initial N ω := by
    unfold davisStoppedElapsedOccupationCenteredResetSum
    rw [hmin_t, hocc_t]
  -- The increment is zero
  rw [hsum_t, hsum_s, sub_self]

/-! ## From capped martingales to the increment law -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- If every deterministic jump-capped approximation is a martingale, then the
deterministic-cap increment law holds. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.of_capped_martingale
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hmart : ∀ N, Martingale
      (fun t => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) filtration P) :
    DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g := by
  have mart := hmart
  refine ⟨?_, ?_⟩
  -- integrable
  · intro N s t
    exact integrable_davisStoppedElapsedOccupationCenteredResetIncrement
      S hflow P ξ hne initial g N s t
      (mart N |>.integrable s) (mart N |>.integrable t)
  -- centered_on_earlier_events
  · intro N s t hst A hA hAfin
    have hs_int := (mart N).integrable s
    have ht_int := (mart N).integrable t
    have hs_intA : Integrable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N s) (P.restrict A) := hs_int.integrableOn
    have ht_intA : Integrable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t) (P.restrict A) := ht_int.integrableOn
    -- For a martingale, ∫ A Sum t = ∫ A Sum s for A ∈ filtration s
    have heq : ∫ ω in A, davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω ∂P =
      ∫ ω in A, davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s ω ∂P := by
      have hm : ↑(filtration s) ≤ mΩ := filtration.le s
      haveI : SigmaFinite (P.trim hm) := by infer_instance
      haveI : ↑(filtration s) ≤ mΩ := hm
      have hcondExp : P[davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N t | filtration s] =ᵐ[P]
        (fun ω => davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N s ω) := (mart N).2 s t hst
      have h1 : ∫ ω in A, P[davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N t | filtration s] ω ∂P =
        ∫ ω in A, davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N t ω ∂P := setIntegral_condExp hm ht_int hA
      have h2 : ∫ ω in A, P[davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N t | filtration s] ω ∂P =
        ∫ ω in A, davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N s ω ∂P := by
        apply MeasureTheory.setIntegral_congr_ae (hm A hA)
        filter_upwards [hcondExp] with x hx _ using hx
      rw [← h1, h2]
    unfold davisStoppedElapsedOccupationCenteredResetIncrement
    rw [integral_sub ht_intA hs_intA, heq, sub_self]

/-! ## From the increment law to capped martingales -/

omit [MeasurableSingletonClass Q] in
/-- Under observability and an integrable elapsed occupation envelope, every
deterministic jump-capped approximation is integrable at every time. -/
theorem DavisElapsedOccupationObservable.integrable_stopped
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P)
    (N : ℕ) (t : ℝ≥0) :
    Integrable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t) P := by
  apply integrable_davisStoppedElapsedOccupationCenteredResetSum_of_envelope
    S hflow P ξ hne initial g N t _ (henv t)
  have h : Measurable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t) := by
    have hmeas := hobs.measurable_stopped N t
    exact Measurable.mono hmeas (filtration.le t) (by trivial)
  exact h.aestronglyMeasurable

omit [MeasurableSingletonClass Q] in
/-- Conversely, the deterministic-cap increment law, together with
observability and integrable elapsed occupation envelopes, makes every
deterministic jump-capped approximation a martingale. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.capped_martingale
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g)
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P)
    (N : ℕ) :
    Martingale
      (fun t => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) filtration P := by
  have hadapted : StronglyAdapted filtration
      (fun t => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) :=
    fun t => (hobs.measurable_stopped N t).stronglyMeasurable
  refine ⟨hadapted, ?_⟩
  intro s t hst
  have hint : Integrable
      (davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t) P := hlaw.integrable N s t
  have hcond : P[davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t | filtration s] =ᵐ[P] (0 : Ω → ℝ) := by
    haveI : SigmaFinite (P.trim (filtration.le s)) := (isFiniteMeasure_trim _).toSigmaFinite
    apply condExp_davisStoppedElapsedOccupationCenteredResetIncrement_eq_zero
      S hflow P filtration ξ hne initial g N s t (filtration.le s) hint
    · exact fun A hA hAfin => hlaw.centered_on_earlier_events N s t hst A hA hAfin
  -- The increment equals X_t - X_s
  have heq : davisStoppedElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g N s t =
      (fun ω => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω -
        davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s ω) := rfl
  -- Use that E[X_t - X_s | F_s] = 0 implies E[X_t | F_s] = X_s
  have hcond' := hcond
  rw [heq] at hcond'
  -- E[X_s | F_s] = X_s since X_s is F_s-measurable
  have hs_meas : StronglyMeasurable[filtration s]
      (fun ω => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s ω) := hadapted s
  have hs_int : Integrable
      (fun ω => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s ω) P := hobs.integrable_stopped henv N s
  have hself : P[davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s | filtration s] =ᵐ[P]
      (fun ω => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s ω) := by
    have := condExp_of_stronglyMeasurable (filtration.le s) hs_meas hs_int
    exact Filter.EventuallyEq.of_eq this
  -- First show integrability of X_t
  have ht_int : Integrable
      (fun ω => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω) P := hobs.integrable_stopped henv N t
  -- Use linearity: E[X_t - X_s | F_s] = E[X_t | F_s] - E[X_s | F_s]
  have hsub := condExp_sub ht_int hs_int
  specialize hsub (filtration s : MeasurableSpace Ω)
  filter_upwards [hcond', hself, hsub] with ω h1 h2 h3
  simp only [Pi.sub_apply, Pi.zero_apply] at h1 h3
  -- h1: E[increment | s] ω = 0
  -- h2: E[X_s | s] ω = X_s ω
  -- h3: E[increment | s] ω = E[X_t | s] ω - E[X_s | s] ω
  -- So: 0 = E[X_t | s] ω - X_s ω
  have h1' : P[(fun ω => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω) - (fun ω => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N s ω) | (filtration s : MeasurableSpace Ω)] ω = 0 := h1
  rw [h3] at h1'
  rw [h2] at h1'
  linarith

omit [MeasurableSingletonClass Q] in
/-- The deterministic-cap increment law is exactly the statement that every
deterministic jump-capped approximation is a martingale. -/
theorem DavisElapsedOccupationObservable.incrementLaw_iff_capped_martingale
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} {hne : ξ.NonExplosive}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    DavisStoppedElapsedOccupationIncrementLaw
        S hflow P filtration ξ hne initial g ↔
      ∀ N, Martingale
        (fun t => davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N t) filtration P :=
  ⟨fun hlaw N => hlaw.capped_martingale hobs henv N,
    fun hmart => DavisStoppedElapsedOccupationIncrementLaw.of_capped_martingale
      S hflow P filtration ξ hne initial g hmart⟩

/-! ## Concrete consequences -/

/-- Bounded-regime martingale property with the structural input replaced by
the capped martingale property. -/
theorem martingale_davisElapsedOccupationCenteredResetProcess_of_capped_martingale
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (C : ℝ) (hC : 0 ≤ C) (hgC : ∀ z, |g z| ≤ C)
    (L : ℝ) (hL : ∀ z, S.totalIntensity z ≤ L)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive}
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (initial : DavisState Q n) (hg : Measurable g)
    (hmart : ∀ N, Martingale
      (fun t => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) ξ.fullFiltration P) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_bounded_regime
    Q _ _ n m S hflow hf hr g hreg hcont C hC hgC L hL Ω _ P _ ξ hξ hne
    d hdpos hd initial hg
    (DavisStoppedElapsedOccupationIncrementLaw.of_capped_martingale
      S hflow P ξ.fullFiltration ξ hne initial g hmart)

end SHS
