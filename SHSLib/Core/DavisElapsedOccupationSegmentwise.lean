import SHSLib.Core.DavisElapsedOccupationCappedMartingale

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Segmentwise decomposition of the capped martingale property

The deterministic-cap increment law was identified with the statement that
every deterministic jump-capped occupation-centered approximation is a
martingale.  Those approximations differ from one cap to the next by the
contribution of a single flow segment, so the whole family is generated,
segment by segment, by the increments carried by the individual segments.

This module isolates that single-segment contribution, computes it pathwise
(a realized reset centered by its sampled occupation compensator on completed
segments, minus the partial occupation compensator on the active segment, and
zero on segments not yet reached), proves that the capped approximations
telescope into finite sums of segment contributions, and deduces that the
capped martingale property — hence, by the previous module, the
deterministic-cap increment law itself — holds exactly when every single
segment contribution is a martingale.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The contribution of the flow segment with index `N` to the
occupation-centered approximation at elapsed time `t`: a fully realized and
compensated reset on a completed segment, minus the partial occupation
compensator on the currently active segment, and zero on segments that have
not been reached yet. -/
def davisElapsedOccupationSegmentContribution (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if N < ξ.activeSegmentIndex hne t ω then
    davisRealizedResetIncrement S hflow ξ initial g N ω -
      davisSampledResetOccupationCompensator S hflow g ξ initial N ω
  else if N = ξ.activeSegmentIndex hne t ω then
    -davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial N ω)
      (t - ξ.jumpTime N ω)
  else 0

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The approximation with a zero jump cap vanishes identically. -/
theorem davisStoppedElapsedOccupationCenteredResetSum_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g 0 t ω = 0 := by
  unfold davisStoppedElapsedOccupationCenteredResetSum
  simp [davisFiniteRealizedResetSum, davisStoppedElapsedResetOccupation,
    davisFiniteResetOccupation]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Raising the deterministic jump cap by one adds exactly the contribution of
the corresponding flow segment. -/
theorem davisStoppedElapsedOccupationCenteredResetSum_succ_sub
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g (N + 1) t ω -
      davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω =
      davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N t ω := by
  unfold davisStoppedElapsedOccupationCenteredResetSum
  unfold davisElapsedOccupationSegmentContribution
  unfold davisStoppedElapsedResetOccupation
  set k := ξ.activeSegmentIndex hne t ω with hk
  by_cases hNk : N < k
  · -- Case N < k
    have hNk' : N < ξ.activeSegmentIndex hne t ω := hNk
    have hmin1 : min N k = N := Nat.min_eq_left (Nat.le_of_lt hNk)
    have hmin2 : min (N + 1) k = N + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hNk)
    have hklt_N : ¬(k < N) := not_lt.mpr (Nat.le_of_lt hNk)
    have hklt_N1 : ¬(k < N + 1) := not_lt.mpr (Nat.succ_le_of_lt hNk)
    simp only [hk] at hmin1 hmin2 hklt_N hklt_N1
    rw [hk.symm] at hmin1 hmin2 hklt_N hklt_N1
    simp [hmin1, hklt_N1, hklt_N, hNk]
    unfold davisFiniteRealizedResetSum davisFiniteResetOccupation
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    unfold davisSampledResetOccupationCompensator
    ring
  · by_cases hNk' : N = k
    · -- Case N = k
      simp [hNk']
    · -- Case N > k
      -- N > k means k < N, so min N k = k and min (N+1) k = k
      have hle : k < N := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hNk) (Ne.symm hNk')
      have hmin1 : min N k = k := Nat.min_eq_right (Nat.le_of_lt hle)
      have hmin2 : min (N + 1) k = k := Nat.min_eq_right (Nat.le_of_lt (Nat.lt_succ_of_lt hle))
      have hklt_N : k < N + 1 := Nat.lt_succ_of_lt hle
      have hklt_N' : k < N := hle
      simp [hmin1, hmin2, hklt_N, hklt_N', hNk, hNk']

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Every deterministic jump-capped approximation is the finite sum of the
contributions of the segments below the cap. -/
theorem davisStoppedElapsedOccupationCenteredResetSum_eq_sum_segmentContribution
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω =
      ∑ i ∈ Finset.range N,
        davisElapsedOccupationSegmentContribution
          S hflow ξ hne initial g i t ω := by
  induction N with
  | zero =>
    simp [davisStoppedElapsedOccupationCenteredResetSum_zero
      S hflow ξ hne initial g t ω]
  | succ N ih =>
    have h := davisStoppedElapsedOccupationCenteredResetSum_succ_sub
      S hflow ξ hne initial g N t ω
    rw [Finset.sum_range_succ]
    linarith

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- On a segment already completed at the initial time, the contribution no
longer depends on the elapsed time. -/
theorem davisElapsedOccupationSegmentContribution_eq_of_lt
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω)
    (hN : N < ξ.activeSegmentIndex hne t ω) :
    davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N t ω =
      davisRealizedResetIncrement S hflow ξ initial g N ω -
        davisSampledResetOccupationCompensator S hflow g ξ initial N ω := by
  simp [davisElapsedOccupationSegmentContribution, hN]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A segment that has not been reached carries no contribution. -/
theorem davisElapsedOccupationSegmentContribution_eq_zero_of_lt
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω)
    (hN : ξ.activeSegmentIndex hne t ω < N) :
    davisElapsedOccupationSegmentContribution
      S hflow ξ hne initial g N t ω = 0 := by
  simp [davisElapsedOccupationSegmentContribution]
  split_ifs with h1 h2 <;> try omega
  linarith [hN]

/-! ## The capped martingale property, segment by segment -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- If every single-segment contribution is a martingale, then so is every
deterministic jump-capped approximation. -/
theorem martingale_davisStoppedElapsedOccupationCenteredResetSum_of_segments
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hseg : ∀ i, Martingale
      (fun t => davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g i t) filtration P)
    (N : ℕ) :
    Martingale
      (fun t => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) filtration P := by
  have heq : (fun t => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) =
      (fun t => ∑ i ∈ Finset.range N,
        davisElapsedOccupationSegmentContribution
          S hflow ξ hne initial g i t) := by
    ext t ω
    simp only [Finset.sum_apply]
    exact davisStoppedElapsedOccupationCenteredResetSum_eq_sum_segmentContribution
      S hflow ξ hne initial g N t ω
  have sum_martingale : ∀ K, Martingale
      (fun t => ∑ i ∈ Finset.range K,
        davisElapsedOccupationSegmentContribution
          S hflow ξ hne initial g i t) filtration P := by
    intro K
    induction K with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      refine ⟨fun _ => stronglyMeasurable_const, ?_⟩
      intro s t hst
      simp
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      exact ih.add (hseg k)
  rw [heq]
  exact sum_martingale N

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Conversely, each single-segment contribution is the difference of two
consecutive capped approximations, hence a martingale whenever they are. -/
theorem martingale_davisElapsedOccupationSegmentContribution_of_capped
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hmart : ∀ N, Martingale
      (fun t => davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) filtration P)
    (N : ℕ) :
    Martingale
      (fun t => davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N t) filtration P := by
  have heq : (fun t => davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g N t) =
      (fun t => davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g (N + 1) t -
        davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N t) := by
    funext t ω
    exact (davisStoppedElapsedOccupationCenteredResetSum_succ_sub
      S hflow ξ hne initial g N t ω).symm
  rw [heq]
  exact (hmart (N + 1)).sub (hmart N)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The capped martingale property is exactly the segmentwise martingale
property. -/
theorem martingale_capped_iff_martingale_segmentContribution
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) :
    (∀ N, Martingale
        (fun t => davisStoppedElapsedOccupationCenteredResetSum
          S hflow ξ hne initial g N t) filtration P) ↔
      ∀ N, Martingale
        (fun t => davisElapsedOccupationSegmentContribution
          S hflow ξ hne initial g N t) filtration P :=
  ⟨fun hmart N => martingale_davisElapsedOccupationSegmentContribution_of_capped
      S hflow P filtration ξ hne initial g hmart N,
    fun hseg N => martingale_davisStoppedElapsedOccupationCenteredResetSum_of_segments
      S hflow P filtration ξ hne initial g hseg N⟩

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Segmentwise martingales give the deterministic-cap increment law. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.of_segment_martingales
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hseg : ∀ i, Martingale
      (fun t => davisElapsedOccupationSegmentContribution
        S hflow ξ hne initial g i t) filtration P) :
    DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g :=
  DavisStoppedElapsedOccupationIncrementLaw.of_capped_martingale
    S hflow P filtration ξ hne initial g
    (martingale_davisStoppedElapsedOccupationCenteredResetSum_of_segments
      S hflow P filtration ξ hne initial g hseg)

omit [MeasurableSingletonClass Q] in
/-- Under observability and an integrable elapsed occupation envelope, the
deterministic-cap increment law is exactly the segmentwise martingale
property. -/
theorem DavisElapsedOccupationObservable.incrementLaw_iff_segment_martingales
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
        (fun t => davisElapsedOccupationSegmentContribution
          S hflow ξ hne initial g N t) filtration P :=
  (hobs.incrementLaw_iff_capped_martingale henv).trans
    (martingale_capped_iff_martingale_segmentContribution
      S hflow P filtration ξ hne initial g)

end SHS
