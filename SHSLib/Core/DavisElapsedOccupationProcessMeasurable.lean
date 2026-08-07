import SHSLib.Core.DavisElapsedOccupationIncrementCentering
import SHSLib.Core.DavisElapsedOccupationEnvelopeMeasurable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Measurability and full-filtration adaptedness

The elapsed occupation-centered reset process is the pointwise eventual limit
of its deterministic jump-capped approximations.  This gives ambient
measurability at every fixed time.  Consequently the process is adapted to
the full-information filtration.

Adaptedness to the smaller natural state-path filtration requires an
additional observability statement: the state path alone need not reveal a
reset that leaves the observed state unchanged.  The full-filtration result
therefore records the unconditional conclusion available from the current
regularity interfaces without adding an unjustified observability hypothesis.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The full elapsed occupation-centered reset sum is measurable at every
fixed time. -/
theorem DavisResetOccupationRegular.measurable_elapsedOccupationCenteredResetSum
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g) (t : ℝ≥0) :
    Measurable (davisElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t) := by
  refine measurable_of_tendsto_metrizable (fun N => @DavisResetOccupationRegular.measurable_stoppedElapsedOccupationCenteredResetSum
      Q _ _ n m S hflow hf hr g hreg Ω _ ξ hξ hne initial hg N t) ?_
  exact tendsto_pi_nhds.mpr (fun ω => tendsto_davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t ω)

/-- The elapsed occupation-centered reset process is adapted to the
full-information filtration. -/
theorem DavisResetOccupationRegular.elapsedOccupationCenteredResetProcess_adapted_full
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g) :
    Adapted ξ.fullFiltration
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) := by
  intro t
  have hlim : ∀ ω, Filter.Tendsto (fun N =>
      davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t ω) Filter.atTop
      (nhds (davisElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g t ω)) :=
    fun ω => tendsto_davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g t ω
  exact measurable_of_tendsto_metrizable
    (fun N => @hreg.measurable_stoppedElapsedOccupationCenteredResetSum
      Q _ _ n m S hflow hf hr g _ _ ξ hξ hne initial hg N t)
    (tendsto_pi_nhds.mpr hlim)

/-- Every fixed two-time increment of the elapsed occupation-centered reset
process is measurable. -/
theorem DavisResetOccupationRegular.measurable_elapsedOccupationCenteredResetIncrement
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (hg : Measurable g) (s t : ℝ≥0) :
    Measurable (davisElapsedOccupationCenteredResetIncrement
      S hflow ξ hne initial g s t) := by
  unfold davisElapsedOccupationCenteredResetIncrement
  unfold davisElapsedOccupationCenteredResetProcess
  exact (@hreg.measurable_elapsedOccupationCenteredResetSum
    Q _ _ n m S hflow hf hr g Ω _ ξ hξ hne initial hg t).sub
      (@hreg.measurable_elapsedOccupationCenteredResetSum
        Q _ _ n m S hflow hf hr g Ω _ ξ hξ hne initial hg s)

end SHS
