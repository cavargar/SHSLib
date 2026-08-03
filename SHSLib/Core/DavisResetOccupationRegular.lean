import SHSLib.Core.DavisConditionalHoldingSignedApproximation
import SHSLib.Core.DavisResetOccupationBridge
import SHSLib.Core.DavisFiniteCompensatorMeasurable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Regularity interface for reset occupation along Davis segments

The basic SHS structure does not by itself provide the joint parameter
measurability needed to integrate a stopped, history-dependent occupation
density.  This module records that extra analytic input explicitly and derives
the corresponding finite-history and ambient-sample measurability facts.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Analytic regularity required for the reset occupation density of a test
function along deterministic Davis flow segments.

The fields separate the three facts used by the conditional endpoint bridge:
joint measurability of the raw density, integrability on every bounded segment,
and joint measurability of the stopped integral and survivor factor. -/
structure DavisResetOccupationRegular (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ) : Prop where
  density_measurable : Measurable (fun p : DavisState Q n × ℝ =>
    davisSegmentResetOccupationDensity S hflow g p.1 p.2)
  density_integrableOn : ∀ z u, IntegrableOn
    (davisSegmentResetOccupationDensity S hflow g z)
    (Set.Icc (0 : ℝ) (u : ℝ))
  stoppedCompensator_measurable : Measurable (fun p : DavisState Q n × ℝ≥0 =>
    davisSegmentResetOccupationCompensator S hflow g p.1 p.2)
  survivor_measurable : Measurable (fun p : DavisState Q n × ℝ≥0 =>
    davisSegmentSurvivor S hflow p.1 p.2)

/-- The reset occupation compensator on the `k`-th segment, stopped at its
sampled holding time. -/
def davisSampledResetOccupationCompensator (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) (ω : Ω) : ℝ :=
  davisSegmentResetOccupationCompensator S hflow g
    (davisPreJumpHistory S hflow ξ initial k ω).currentState
    (ξ.holdingTime k ω)

/-- At a fixed elapsed time, the reset occupation density is a measurable
function of finite pre-jump history. -/
theorem DavisResetOccupationRegular.measurable_history_density
    {S : SHS Q n m} {hflow : S.HasGlobalFlow} {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g) (k : ℕ) (s : ℝ) :
    Measurable (fun H : DavisPreJumpHistory Q n m k =>
      davisSegmentResetOccupationDensity S hflow g H.currentState s) := by
  exact hreg.density_measurable.comp
    ((DavisPreJumpHistory.measurable_currentState k).prodMk measurable_const)

/-- At a fixed stopping duration, the stopped reset occupation compensator is
measurable as a function of finite pre-jump history. -/
theorem DavisResetOccupationRegular.measurable_history_stoppedCompensator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow} {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g) (k : ℕ) (u : ℝ≥0) :
    Measurable (fun H : DavisPreJumpHistory Q n m k =>
      davisSegmentResetOccupationCompensator S hflow g H.currentState u) := by
  exact hreg.stoppedCompensator_measurable.comp
    ((DavisPreJumpHistory.measurable_currentState k).prodMk measurable_const)

/-- The survivor factor at a fixed duration is measurable as a function of
finite pre-jump history. -/
theorem DavisResetOccupationRegular.measurable_history_survivor
    {S : SHS Q n m} {hflow : S.HasGlobalFlow} {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g) (k : ℕ) (u : ℝ≥0) :
    Measurable (fun H : DavisPreJumpHistory Q n m k =>
      H.nextSurvivor S hflow u) := by
  exact hreg.survivor_measurable.comp
    ((DavisPreJumpHistory.measurable_currentState k).prodMk measurable_const)

/-- Under measurable jump noise, the sampled stopped occupation compensator
is measurable in the ambient sample space.  It is generally not measurable in
the pre-jump filtration because it depends on the newly sampled holding time. -/
theorem DavisResetOccupationRegular.measurable_sampled_stoppedCompensator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k : ℕ) :
    Measurable (davisSampledResetOccupationCompensator
      S hflow g ξ initial k) := by
  unfold davisSampledResetOccupationCompensator
  have hp : Measurable (fun ω =>
      ((davisPreJumpHistory S hflow ξ initial k ω).currentState,
        ξ.holdingTime k ω)) :=
    ((DavisPreJumpHistory.measurable_currentState k).comp
      (hξ.preJumpHistory S hflow hf hr initial k)).prodMk (hξ.holdingTime k)
  simpa only [Function.comp_apply] using
    hreg.stoppedCompensator_measurable.comp hp

/-- Pulling the fixed-time density back through the random pre-jump history
makes it measurable in the corresponding history filtration. -/
theorem DavisResetOccupationRegular.measurable_preJump_density
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    (k : ℕ) (s : ℝ) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (fun ω => davisSegmentResetOccupationDensity S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState s) := by
  exact (hreg.measurable_history_density k s).comp
    (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial k)

/-- Pulling the fixed-duration stopped compensator back through the random
history makes it measurable in the corresponding history filtration. -/
theorem DavisResetOccupationRegular.measurable_preJump_stoppedCompensator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    (k : ℕ) (u : ℝ≥0) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (fun ω => davisSegmentResetOccupationCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState u) := by
  exact (hreg.measurable_history_stoppedCompensator k u).comp
    (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial k)

/-- The regularity interface supplies the survivor measurability hypothesis
used by the conditional holding-time threshold theorems. -/
theorem DavisResetOccupationRegular.measurable_preJump_survivor
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    (k : ℕ) (u : ℝ≥0) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (fun ω => (davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor
        S hflow u) := by
  exact (hreg.measurable_history_survivor k u).comp
    (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial k)

end SHS
