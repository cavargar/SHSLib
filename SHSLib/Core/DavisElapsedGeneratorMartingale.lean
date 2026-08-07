import SHSLib.Core.DavisElapsedOccupationMartingale

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Generator bridge for the elapsed occupation martingale

The occupation-compensated test-function process is, pathwise, exactly the
elapsed occupation-centered reset process.  This module records that process
form of the bridge and transfers the martingale property proved in the
previous module across it.  A final corollary shows that the compensated
generator process has zero mean at every time, which is the Dynkin-type
identity used by the generator theorems.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The test-function increment compensated by occupied flow and reset
densities, viewed as a time-indexed process. -/
def davisElapsedCompensatedGeneratorProcess (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (a g : DavisState Q n → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω =>
    g (davisJumpPath S hflow ξ hne initial t ω) - g initial -
      davisElapsedOccupationCompensator S hflow ξ hne initial a g t ω

/-- Process form of the generator bridge: the compensated generator process
coincides with the elapsed occupation-centered reset process. -/
theorem davisElapsedCompensatedGeneratorProcess_eq_occupationCenteredProcess
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (a g : DavisState Q n → ℝ)
    (hga : DavisFlowIntegralIdentity S hflow g a) :
    davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g =
      davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g := by
  funext t ω
  exact davis_compensatedProcess_eq_elapsedOccupationCenteredResetSum
    S hflow ξ hne initial g a hga t ω

/-- Transfer of the martingale property across the generator bridge. -/
theorem martingale_davisElapsedCompensatedGeneratorProcess
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (a g : DavisState Q n → ℝ)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (hmart : Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) filtration P) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        S hflow ξ hne initial a g) filtration P := by
  rw [davisElapsedCompensatedGeneratorProcess_eq_occupationCenteredProcess
    S hflow ξ hne initial a g hga]
  exact hmart

/-- Concrete generator bridge: observability, reset-occupation regularity with
integrable elapsed envelopes, the deterministic-cap increment law, and the
flow fundamental-theorem identity make the compensated generator process a
martingale. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_compensatedGenerator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {a g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {filtration : Filtration ℝ≥0 mΩ}
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (hobs : DavisElapsedOccupationObservable
      S hflow filtration ξ hne initial g)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P filtration ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        S hflow ξ hne initial a g) filtration P :=
  martingale_davisElapsedCompensatedGeneratorProcess
    S hflow P filtration ξ hne initial a g hga
    (@DavisStoppedElapsedOccupationIncrementLaw.martingale
      Q _ _ n m S hflow hf hr g hreg Ω _ P _ filtration ξ hξ hne initial hg
      hobs hlaw henv)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- With positive holding times, elapsed time zero lies in the initial
segment. -/
theorem DavisJumpNoise.activeSegmentIndex_zero {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (hpos : ξ.PositiveHoldingTimes) (ω : Ω) :
    ξ.activeSegmentIndex hne 0 ω = 0 := by
  have hex : ∃ j, (0 : ℝ≥0) < ξ.jumpTime j ω := ⟨1, by simpa using hpos 0 ω⟩
  have hfind : Nat.find hex = 1 := (Nat.find_eq_iff hex).2 ⟨by
    simpa using hpos 0 ω, by
      intro j hj
      have : j = 0 := by omega
      simp [this]⟩
  unfold DavisJumpNoise.activeSegmentIndex
  rw [show Nat.find _ = 1 from hfind]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The elapsed occupation-centered reset process starts at zero. -/
theorem davisElapsedOccupationCenteredResetProcess_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) (ω : Ω) :
    davisElapsedOccupationCenteredResetProcess
      S hflow ξ hne initial g 0 ω = 0 := by
  have hk := ξ.activeSegmentIndex_zero hne hpos ω
  simp [davisElapsedOccupationCenteredResetProcess,
    davisElapsedOccupationCenteredResetSum, davisElapsedRealizedResetSum,
    davisElapsedResetOccupation, hk, davisFiniteRealizedResetSum,
    davisFiniteResetOccupation, davisSegmentResetOccupationCompensator,
    Set.Icc_self]

/-- Dynkin-type identity: a compensated generator process that is a martingale
has zero mean at every elapsed time. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (filtration : Filtration ℝ≥0 mΩ)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) (a g : DavisState Q n → ℝ)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (hmart : Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) filtration P)
    (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 := by
  rw [davisElapsedCompensatedGeneratorProcess_eq_occupationCenteredProcess
    S hflow ξ hne initial a g hga]
  -- Use martingale property: ∫ M_t = ∫ M_0
  have hcond : ∀ᵐ ω ∂P, P[fun ω' => S.davisElapsedOccupationCenteredResetProcess hflow ξ hne initial g t ω' | filtration 0] ω =
                              S.davisElapsedOccupationCenteredResetProcess hflow ξ hne initial g 0 ω :=
    hmart.condExp_ae_eq (zero_le t)
  calc ∫ ω, S.davisElapsedOccupationCenteredResetProcess hflow ξ hne initial g t ω ∂P
      = ∫ ω, P[fun ω' => S.davisElapsedOccupationCenteredResetProcess hflow ξ hne initial g t ω' | filtration 0] ω ∂P := by
        rw [MeasureTheory.integral_condExp]
    _ = ∫ ω, S.davisElapsedOccupationCenteredResetProcess hflow ξ hne initial g 0 ω ∂P := by
        exact MeasureTheory.integral_congr_ae hcond
    _ = 0 := by
      simp [davisElapsedOccupationCenteredResetProcess_zero S hflow ξ hne hpos initial g]

end SHS
