import SHSLib.Core.DavisMartingale

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Observable jump times for the natural Davis filtration

This module isolates a concrete sufficient condition under which the exogenous
cumulative jump times can be recovered from observations of the assembled state
path.  This is the missing distinction between the full-information filtration
and the natural path filtration: measurability of the noise coordinates alone
does not make hidden resets observable from the state process.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A strong, directly usable observability condition: at every elapsed time,
a measurable function of the current augmented state reports how many sampled
jump times have occurred.  It is sufficient for stopping-time results.  Models
whose state records a jump counter, or whose mode graph cannot revisit a mode,
can establish this condition directly. -/
structure DavisJumpNoise.CurrentStateJumpCountObservable
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) where
  jumpCount : ℝ≥0 → DavisState Q n → ℕ
  jumpCount_measurable : ∀ t, Measurable (jumpCount t)
  occurred_iff : ∀ k t ω,
    ξ.jumpTime k ω ≤ t ↔
      k ≤ jumpCount t (davisJumpPath S hflow ξ hne initial t ω)

/-- Under current-state jump-count observability, every cumulative jump time is
a stopping time for the natural path filtration. -/
theorem DavisJumpNoise.CurrentStateJumpCountObservable.jumpTime_isStoppingTime_natural
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n)
    (hobs : ξ.CurrentStateJumpCountObservable S hflow hne initial)
    (k : ℕ) :
    IsStoppingTime (ξ.naturalPathFiltration S hflow hf hr hξ hne initial)
      (fun ω => ((ξ.jumpTime k ω : ℝ≥0) : ℝ≥0∞)) := by
  intro t
  have hpath := hξ.jumpPath_adapted_natural S hflow hf hr hne initial t
  have hcount : Measurable[
      ξ.naturalPathFiltration S hflow hf hr hξ hne initial t]
      (fun ω => hobs.jumpCount t (davisJumpPath S hflow ξ hne initial t ω)) :=
    (hobs.jumpCount_measurable t).comp hpath
  have hset : MeasurableSet[
      ξ.naturalPathFiltration S hflow hf hr hξ hne initial t]
      {ω | k ≤ hobs.jumpCount t (davisJumpPath S hflow ξ hne initial t ω)} :=
    measurableSet_Ici.preimage hcount
  change MeasurableSet[
    ξ.naturalPathFiltration S hflow hf hr hξ hne initial t]
    {ω | ((ξ.jumpTime k ω : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  rw [show {ω | ((ξ.jumpTime k ω : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
      {ω | k ≤ hobs.jumpCount t
        (davisJumpPath S hflow ξ hne initial t ω)} from by
    ext ω
    simp only [Set.mem_setOf_eq, ENNReal.coe_le_coe]
    exact hobs.occurred_iff k t ω]
  exact hset

/-- Pathwise non-explosion also gives divergence of the cumulative jump times
when they are viewed in `ℝ≥0∞`, the codomain used by stopping times. -/
theorem DavisJumpNoise.jumpTime_tendsto_ennreal
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive) (ω : Ω) :
    Filter.Tendsto (fun k => ((ξ.jumpTime k ω : ℝ≥0) : ℝ≥0∞))
      Filter.atTop (nhds ⊤) := by
  exact ENNReal.tendsto_coe_nhds_top.mpr (hne ω)

/-- No sequence of finite `ℝ≥0`-valued times can tend to `Filter.atTop` after
coercion to `ℝ≥0∞`: that filter eventually requires the value to be `⊤`.
Consequently localization data for finite stopping times must use `nhds ⊤`,
not `Filter.atTop`, as its convergence filter. -/
theorem no_nnreal_coe_tendsto_ennreal_atTop (σ : ℕ → ℝ≥0) :
    ¬ Filter.Tendsto (fun k => (σ k : ℝ≥0∞))
      Filter.atTop Filter.atTop := by
  intro h
  have htop : ∀ᶠ k in Filter.atTop, (⊤ : ℝ≥0∞) ≤ (σ k : ℝ≥0∞) :=
    Filter.tendsto_atTop.mp h ⊤
  rcases htop.exists with ⟨k, hk⟩
  have : (σ k : ℝ≥0∞) = ⊤ := top_unique hk
  exact ENNReal.coe_ne_top this

/-- The localization fields common to Davis's local-martingale constructions,
separated from the later compensated-jump identity. -/
structure DavisLocalizationData
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne) where
  sigma : ℕ → R.Omega → ℝ≥0
  sigma_stopping : ∀ k, IsStoppingTime R.filtration
    (fun ω => (sigma k ω : ℝ≥0∞))
  sigma_tendsto : ∀ᵐ ω ∂ R.P,
    Filter.Tendsto (fun k => (sigma k ω : ℝ≥0∞))
      Filter.atTop (nhds ⊤)

/-- Observable, non-explosive jump noise supplies canonical localization data
for its natural-filtration realization: use the cumulative jump times. -/
def DavisLocalizationData.ofJumpNoiseNaturalFiltration
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n)
    (hobs : ξ.CurrentStateJumpCountObservable S hflow hne initial) :
    DavisLocalizationData S hflow hf hr hli hnePDP
      (DavisProcessRealization.ofJumpNoiseNaturalFiltration S hflow hf hr hli
        hnePDP P ξ hξ hne hpos initial) where
  sigma := ξ.jumpTime
  sigma_stopping := fun k =>
    hobs.jumpTime_isStoppingTime_natural S hflow hf hr hξ hne initial k
  sigma_tendsto := Filter.Eventually.of_forall fun ω =>
    ξ.jumpTime_tendsto_ennreal hne ω

end SHS
