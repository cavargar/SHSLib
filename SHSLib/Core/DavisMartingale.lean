import SHSLib.Core.DavisConstruction

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Martingales for the concrete SHS Davis process

This file isolates the process-level data of a realization of the concrete PDP.
Unlike the local-characteristic package, a realization includes a probability
space, an adapted coordinate process, and the compensated jump-measure result.
The latter is the primitive probabilistic theorem used in Davis's proof; the
extended-generator martingale is derived from it below rather than assumed.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A process realization of the standard time-augmented Davis PDP, carrying
exactly the path/filtration facts used in the proof of Davis 26.14. -/
structure DavisProcessRealization (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr) where
  Omega : Type*
  mOmega : MeasurableSpace Omega
  P : Measure Omega
  probability : IsProbabilityMeasure P
  filtration : Filtration ℝ≥0 mOmega
  sigmaFiniteFiltration : SigmaFiniteFiltration P filtration
  process : ℝ≥0 → Omega → DavisState Q n
  initial : DavisState Q n
  process_zero : ∀ᵐ ω ∂ P, process 0 ω = initial
  /-- The clock coordinate converts Davis elapsed time to SHS absolute time. -/
  clock_eq : ∀ u ω, (process u ω).2.2 = initial.2.2 + (u : ℝ)

attribute [instance] DavisProcessRealization.mOmega
attribute [instance] DavisProcessRealization.probability
attribute [instance] DavisProcessRealization.sigmaFiniteFiltration

/-- Package the assembled recursive jump path as a Davis process realization.
The probability law and filtration remain parameters at this stage; sampling
laws and adaptedness can subsequently be proved for a concrete noise model.
Positive holding times give the initial-state field, while pathwise
non-explosion gives a total process and the clock identity. -/
def DavisProcessRealization.ofJumpNoise
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [hP : IsProbabilityMeasure P]
    (filtration : Filtration ℝ≥0 mΩ)
    [hfiltration : SigmaFiniteFiltration P filtration]
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (hpos : ξ.PositiveHoldingTimes) (initial : DavisState Q n) :
    DavisProcessRealization S hflow hf hr hli hnePDP where
  Omega := Ω
  mOmega := mΩ
  P := P
  probability := hP
  filtration := filtration
  sigmaFiniteFiltration := hfiltration
  process := davisJumpPath S hflow ξ hne initial
  initial := initial
  process_zero := Filter.Eventually.of_forall
    (davisJumpPath_zero S hflow ξ hne hpos initial)
  clock_eq := davisJumpPath_clock S hflow ξ hne initial

/-- The realization constructed from jump noise uses the assembled recursive
path definitionally. -/
@[simp] theorem DavisProcessRealization.ofJumpNoise_process
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (filtration : Filtration ℝ≥0 mΩ)
    [SigmaFiniteFiltration P filtration]
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (hpos : ξ.PositiveHoldingTimes) (initial : DavisState Q n)
    (t : ℝ≥0) (ω : Ω) :
    (DavisProcessRealization.ofJumpNoise S hflow hf hr hli hnePDP P
      filtration ξ hne hpos initial).process t ω =
      davisJumpPath S hflow ξ hne initial t ω := rfl

/-! ## A canonical full-information filtration

The natural filtration of the noise is the eventual target for the canonical
construction.  The constant full measurable-space filtration is a useful first
concrete realization: it is automatically sigma-finite under a probability
measure, makes every measurable noise time a stopping time, and makes the
assembled path adapted.  This removes the previously external filtration
parameter without asserting the stronger natural-filtration result.
-/

/-- The constant filtration carrying all measurable information at every
elapsed time. -/
def DavisJumpNoise.fullFiltration {m : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω) : Filtration ℝ≥0 mΩ :=
  Filtration.const ℝ≥0 mΩ le_rfl

/-- Every cumulative jump time is a stopping time for the full-information
filtration. -/
theorem DavisJumpNoise.MeasurableNoise.jumpTime_isStoppingTime_full
    {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (k : ℕ) :
    IsStoppingTime ξ.fullFiltration
      (fun ω => ((ξ.jumpTime k ω : ℝ≥0) : ℝ≥0∞)) := by
  intro t
  change MeasurableSet[mΩ]
    {ω | ((ξ.jumpTime k ω : ℝ≥0) : ℝ≥0∞) ≤ t}
  exact measurableSet_Iic.preimage ((hξ.jumpTime k).coe_nnreal_ennreal)

/-- The assembled recursive path is adapted to the full-information
filtration. -/
theorem DavisJumpNoise.MeasurableNoise.jumpPath_adapted_full
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) :
    Adapted ξ.fullFiltration (davisJumpPath S hflow ξ hne initial) := by
  intro t
  exact hξ.jumpPath S hflow hf hr hne initial t

/-- Package measurable, non-explosive positive jump noise using its canonical
full-information filtration.  Unlike `ofJumpNoise`, this constructor has no
filtration argument. -/
def DavisProcessRealization.ofJumpNoiseFullFiltration
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) :
    DavisProcessRealization S hflow hf hr hli hnePDP :=
  DavisProcessRealization.ofJumpNoise S hflow hf hr hli hnePDP P
    ξ.fullFiltration ξ hne hpos initial

/-- The full-filtration realization uses the assembled jump path. -/
@[simp] theorem DavisProcessRealization.ofJumpNoiseFullFiltration_process
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    (DavisProcessRealization.ofJumpNoiseFullFiltration S hflow hf hr hli
      hnePDP P ξ hξ hne hpos initial).process t ω =
      davisJumpPath S hflow ξ hne initial t ω := rfl

/-- The full-filtration realization's assembled path is adapted. -/
theorem DavisProcessRealization.ofJumpNoiseFullFiltration_adapted
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) :
    Adapted
      (DavisProcessRealization.ofJumpNoiseFullFiltration S hflow hf hr hli
        hnePDP P ξ hξ hne hpos initial).filtration
      (DavisProcessRealization.ofJumpNoiseFullFiltration S hflow hf hr hli
        hnePDP P ξ hξ hne hpos initial).process := by
  change Adapted ξ.fullFiltration (davisJumpPath S hflow ξ hne initial)
  exact hξ.jumpPath_adapted_full S hflow hf hr hne initial

/-! ## Natural filtration of the assembled path

Unlike the full-information filtration, this filtration reveals only the
assembled state path up to the current elapsed time.  It is defined directly
as the supremum of the pullback measurable spaces of the coordinate maps, so
it does not require an auxiliary topology on the augmented state space.
-/

/-- The natural filtration generated by the assembled Davis jump path. -/
def DavisJumpNoise.naturalPathFiltration
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) : Filtration ℝ≥0 mΩ where
  seq i := ⨆ j ≤ i, MeasurableSpace.comap
    (davisJumpPath S hflow ξ hne initial j) inferInstance
  mono' i j hij := biSup_mono fun _ hki => hki.trans hij
  le' i := by
    refine iSup₂_le fun j _ => ?_
    exact measurable_iff_comap_le.mp
      (hξ.jumpPath S hflow hf hr hne initial j)

/-- The assembled path is adapted to its natural path filtration. -/
theorem DavisJumpNoise.MeasurableNoise.jumpPath_adapted_natural
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) :
    Adapted (ξ.naturalPathFiltration S hflow hf hr hξ hne initial)
      (davisJumpPath S hflow ξ hne initial) := by
  intro i
  apply measurable_iff_comap_le.mpr
  exact le_iSup₂_of_le i le_rfl le_rfl

/-- The natural path filtration is contained in the full-information
filtration. -/
theorem DavisJumpNoise.naturalPathFiltration_le_fullFiltration
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) :
    ξ.naturalPathFiltration S hflow hf hr hξ hne initial ≤
      ξ.fullFiltration := by
  intro i
  exact (ξ.naturalPathFiltration S hflow hf hr hξ hne initial).le i

/-- Package measurable, non-explosive positive jump noise using the natural
filtration generated by its assembled state path. -/
def DavisProcessRealization.ofJumpNoiseNaturalFiltration
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) :
    DavisProcessRealization S hflow hf hr hli hnePDP :=
  DavisProcessRealization.ofJumpNoise S hflow hf hr hli hnePDP P
    (ξ.naturalPathFiltration S hflow hf hr hξ hne initial)
    ξ hne hpos initial

/-- The natural-filtration realization uses the assembled jump path. -/
@[simp] theorem DavisProcessRealization.ofJumpNoiseNaturalFiltration_process
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    (DavisProcessRealization.ofJumpNoiseNaturalFiltration S hflow hf hr hli
      hnePDP P ξ hξ hne hpos initial).process t ω =
      davisJumpPath S hflow ξ hne initial t ω := rfl

/-- The natural-filtration realization's assembled path is adapted. -/
theorem DavisProcessRealization.ofJumpNoiseNaturalFiltration_adapted
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hnePDP : DavisNonExplosive S hflow hf hr)
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : DavisJumpNoise m Ω) (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) :
    Adapted
      (DavisProcessRealization.ofJumpNoiseNaturalFiltration S hflow hf hr hli
        hnePDP P ξ hξ hne hpos initial).filtration
      (DavisProcessRealization.ofJumpNoiseNaturalFiltration S hflow hf hr hli
        hnePDP P ξ hξ hne hpos initial).process := by
  change Adapted
    (ξ.naturalPathFiltration S hflow hf hr hξ hne initial)
    (davisJumpPath S hflow ξ hne initial)
  exact hξ.jumpPath_adapted_natural S hflow hf hr hne initial

/-- Regularity assumptions on a lifted test function needed to invoke the
Davis extended-generator and localization theorems for a realization. -/
structure DavisTestFunctionRegular
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (ψ : TestFunction Q n) : Prop where
  measurable : Measurable ψ.toDavisFunction
  flow_regular : Davis.InExtGenDomain_AbsCont
    (toDavisPDPStandard S hflow hf hr hli hne).toPDP ψ.toDavisFunction
  bounded : ∃ C : ℝ, ∀ z, |ψ.toDavisFunction z| ≤ C

/-- Process-level hypotheses supplied by the canonical jump-time construction.
They are the deterministic telescoping identity and compensated jump-measure
martingale in Davis's proof, not the desired generator martingale itself. -/
structure DavisCompensatorData
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (ψ : TestFunction Q n) where
  sigma : ℕ → R.Omega → ℝ≥0
  sigma_stopping : ∀ k, IsStoppingTime R.filtration
    (fun ω => (sigma k ω : ℝ≥0∞))
  sigma_tendsto : ∀ᵐ ω ∂ R.P,
    Filter.Tendsto (fun k => (sigma k ω : ℝ≥0∞)) Filter.atTop (nhds ⊤)
  jumpCompensated : ℝ≥0 → R.Omega → ℝ
  decomposition : ∀ (k : ℕ) (t : ℝ≥0) (ω : R.Omega),
    ψ.toDavisFunction (R.process (min t (sigma k ω)) ω) -
      ψ.toDavisFunction (R.process 0 ω) -
      (∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(sigma k ω)),
        Davis.pdpGenerator
          (toDavisPDPStandard S hflow hf hr hli hne).toPDP
          (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω)) =
      jumpCompensated (min t (sigma k ω)) ω
  jump_martingale : ∀ k, Martingale
    (fun t ω => jumpCompensated (min t (sigma k ω)) ω) R.filtration R.P

/-- Integrability/localization data promoting Davis's local martingale to a
true martingale.  Conditions (15)--(16), or bounded-rate localization, are the
standard ways to establish these fields. -/
structure DavisTrueMartingaleData
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (ψ : TestFunction Q n) where
  /-- Condition (15): finite expected cumulative total intensity. -/
  finite_transitions : ∀ t, Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
    S.totalIntensity (R.process u.toNNReal ω)) R.P
  /-- Condition (16): finite expected intensity-weighted absolute jumps. -/
  finite_jumps : ∀ t, Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
    ∑ ℓ : Fin m, |ψ.toDavisFunction (S.resetDavisState ℓ (R.process u.toNNReal ω)) -
      ψ.toDavisFunction (R.process u.toNNReal ω)| *
      S.intensity ℓ (R.process u.toNNReal ω).1
        (R.process u.toNNReal ω).2.1 (R.process u.toNNReal ω).2.2) R.P
  endpoint_integrable : ∀ t, Integrable (fun ω => ψ.toDavisFunction (R.process t ω)) R.P
  generator_integrable : ∀ t, Integrable (fun ω =>
    ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
      S.extendedGenerator ψ (R.process u.toNNReal ω).1
        (R.process u.toNNReal ω).2.1 (R.process u.toNNReal ω).2.2) R.P
  adapted : Adapted R.filtration (fun t ω =>
    ψ.toDavisFunction (R.process t ω) - ψ.toDavisFunction (R.process 0 ω) -
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        Davis.pdpGenerator
          (toDavisPDPStandard S hflow hf hr hli hne).toPDP
          (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω))
  envelope : R.Omega → ℝ
  envelope_integrable : Integrable envelope R.P
  dominated : ∀ t ω, |ψ.toDavisFunction (R.process t ω) -
    ψ.toDavisFunction (R.process 0 ω) -
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        Davis.pdpGenerator
          (toDavisPDPStandard S hflow hf hr hli hne).toPDP
          (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω)| ≤
    envelope ω

/-
Integrability of the compensated generator process is derived from endpoint
and generator integrability, rather than requested as duplicate input.
-/
theorem DavisTrueMartingaleData.compensated_integrable
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (ψ : TestFunction Q n) (hψ : Measurable ψ.toDavisFunction)
    (htm : DavisTrueMartingaleData S hflow hf hr hli hne R ψ) (t : ℝ≥0) :
    Integrable (fun ω =>
      ψ.toDavisFunction (R.process t ω) - ψ.toDavisFunction (R.process 0 ω) -
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          Davis.pdpGenerator
            (toDavisPDPStandard S hflow hf hr hli hne).toPDP
            (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω)) R.P := by
  refine' MeasureTheory.Integrable.sub _ _;
  · exact MeasureTheory.Integrable.sub ( htm.endpoint_integrable t ) ( by exact MeasureTheory.integrable_const _ |> MeasureTheory.Integrable.congr <| by filter_upwards [ R.process_zero ] with ω hω; aesop );
  · convert htm.generator_integrable t using 1;
    ext ω;
    convert rfl using 3;
    convert ( toDavisPDP_compatible S hflow hf hr ).pdpGenerator_eq_extendedGenerator ψ hψ _ |> Eq.symm using 1

/-
Davis 26.14 followed by the true-martingale promotion, specialized to the
concrete PDP constructed from the SHS.
-/
theorem toDavisPDPStandard_compensated_martingale
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (ψ : TestFunction Q n)
    (hψ : DavisTestFunctionRegular S hflow hf hr hli hne R ψ)
    (hc : DavisCompensatorData S hflow hf hr hli hne R ψ)
    (htm : DavisTrueMartingaleData S hflow hf hr hli hne R ψ) :
    Martingale (fun t ω =>
      ψ.toDavisFunction (R.process t ω) - ψ.toDavisFunction (R.process 0 ω) -
        ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          Davis.pdpGenerator
            (toDavisPDPStandard S hflow hf hr hli hne).toPDP
            (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω))
      R.filtration R.P := by
  obtain ⟨ σ, hσ_st, hσ_top, Jc, hdecomp, hjump_mart ⟩ := hc;
  have := @Davis.pdp_generator_bounded_true_martingale;
  apply this (S.toDavisPDPStandard hflow hf hr hli hne) hψ.bounded hψ.measurable R.process R.filtration (S.flowGenerator ψ) (fun t ω => ψ.toDavisFunction (R.process t ω) - ψ.toDavisFunction (R.process 0 ω) - ∫ u in Set.Icc (0 : ℝ) (t : ℝ), Davis.pdpGenerator (S.toDavisPDPStandard hflow hf hr hli hne).toPDP (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω)) (fun t ω => rfl) htm.adapted (htm.compensated_integrable S hflow hf hr hli hne R ψ hψ.measurable) σ hσ_st hσ_top (fun k => by
    convert hjump_mart k using 1;
    grind) htm.envelope htm.envelope_integrable htm.dominated


end SHS
namespace SHS

/-- The coordinate processes of a Davis realization, displaying the augmented
SHS state `Zᵤ = (qᵤ,xᵤ,tᵤ)`. -/
def DavisProcessRealization.qProc
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
    {hne : DavisNonExplosive S hflow hf hr}
    (R : DavisProcessRealization S hflow hf hr hli hne) :=
  fun u ω => (R.process u ω).1

def DavisProcessRealization.xProc
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
    {hne : DavisNonExplosive S hflow hf hr}
    (R : DavisProcessRealization S hflow hf hr hli hne) :=
  fun u ω => (R.process u ω).2.1

def DavisProcessRealization.timeProc
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
    {hne : DavisNonExplosive S hflow hf hr}
    (R : DavisProcessRealization S hflow hf hr hli hne) :=
  fun u ω => (R.process u ω).2.2

/-- The discrete SHS coordinate process indexed by absolute SHS time.
Times before the realization's initial clock are clamped to elapsed time zero by
`Real.toNNReal`; on the intervals used below, the elapsed time is nonnegative. -/
def DavisProcessRealization.qProcAbsolute
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
    {hne : DavisNonExplosive S hflow hf hr}
    (R : DavisProcessRealization S hflow hf hr hli hne) :=
  fun s ω => R.qProc (s - R.initial.2.2).toNNReal ω

/-- The continuous SHS coordinate process indexed by absolute SHS time. -/
def DavisProcessRealization.xProcAbsolute
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
    {hne : DavisNonExplosive S hflow hf hr}
    (R : DavisProcessRealization S hflow hf hr hli hne) :=
  fun s ω => R.xProc (s - R.initial.2.2).toNNReal ω

/-- Translation from Davis elapsed-time integration to the SHS absolute-time
convention.  This is the change of variables `s = t₀ + u`. -/
theorem integral_Icc_elapsed_to_absolute (f : ℝ → ℝ) (t₀ t : ℝ) (ht : 0 ≤ t) :
    (∫ u in Set.Icc (0 : ℝ) t, f u) =
      ∫ s in Set.Icc t₀ (t₀ + t), f (s - t₀) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le ht,
      ← intervalIntegral.integral_of_le (by linarith : t₀ ≤ t₀ + t)]
  rw [intervalIntegral.integral_comp_sub_right]
  norm_num

@[simp] theorem DavisProcessRealization.process_eq_coordinates
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
    {hne : DavisNonExplosive S hflow hf hr}
    (R : DavisProcessRealization S hflow hf hr hli hne) (u) (ω) :
    R.process u ω = (R.qProc u ω, R.xProc u ω, R.timeProc u ω) := rfl

/-
Hespanha's Theorem 2 obtained from the concrete time-augmented Davis PDP.
There is no compensated-process martingale hypothesis: it is derived above
from the deterministic-flow and jump-compensator construction and its stated
integrability/localization assumptions.  Davis elapsed time is `u : ℝ≥0`;
the third coordinate of `R.process u` is the SHS absolute time.
-/
theorem theorem2_PDP_generator
    {Q : Type*} [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    {n m : ℕ} (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (ψ : TestFunction Q n)
    (hψ : DavisTestFunctionRegular S hflow hf hr hli hne R ψ)
    (hc : DavisCompensatorData S hflow hf hr hli hne R ψ)
    (htm : DavisTrueMartingaleData S hflow hf hr hli hne R ψ)
    (t : ℝ≥0) :
    ∫ ω, ψ.toFun (R.qProc t ω) (R.xProc t ω) (R.timeProc t ω) ∂ R.P =
      ψ.toDavisFunction R.initial +
      ∫ ω, (∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        S.extendedGenerator ψ (R.qProc u.toNNReal ω)
          (R.xProc u.toNNReal ω) (R.timeProc u.toNNReal ω)) ∂ R.P := by
  have h_integrable : ∀ t, Integrable (fun ω => ψ.toDavisFunction (R.process t ω) - ψ.toDavisFunction (R.process 0 ω) - ∫ u in Set.Icc (0 : ℝ) (t : ℝ), Davis.pdpGenerator (toDavisPDPStandard S hflow hf hr hli hne).toPDP (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω)) R.P := by
    exact htm.compensated_integrable S hflow hf hr hli hne R ψ hψ.measurable;
  have h_integrable : ∀ t, ∫ ω, (ψ.toDavisFunction (R.process t ω) - ψ.toDavisFunction (R.process 0 ω) - ∫ u in Set.Icc (0 : ℝ) (t : ℝ), Davis.pdpGenerator (toDavisPDPStandard S hflow hf hr hli hne).toPDP (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω)) ∂ R.P = 0 := by
    intro t
    have h_martingale : Martingale (fun t ω => ψ.toDavisFunction (R.process t ω) - ψ.toDavisFunction (R.process 0 ω) - ∫ u in Set.Icc (0 : ℝ) (t : ℝ), Davis.pdpGenerator (toDavisPDPStandard S hflow hf hr hli hne).toPDP (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω)) R.filtration R.P := by
      apply toDavisPDPStandard_compensated_martingale S hflow hf hr hli hne R ψ hψ hc htm;
    have := h_martingale.2 0 t ( by norm_num );
    convert integral_congr_ae this using 1;
    · rw [ MeasureTheory.integral_condExp ];
    · simp +decide [ MeasureTheory.integral_zero ];
  have h_integrable : ∫ ω, ψ.toDavisFunction (R.process t ω) ∂ R.P = ψ.toDavisFunction R.initial + ∫ ω, ∫ u in Set.Icc (0 : ℝ) (t : ℝ), Davis.pdpGenerator (toDavisPDPStandard S hflow hf hr hli hne).toPDP (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω) ∂ volume ∂ R.P := by
    have h_integrable : ∫ ω, ψ.toDavisFunction (R.process t ω) ∂ R.P - ∫ ω, ψ.toDavisFunction (R.process 0 ω) ∂ R.P - ∫ ω, ∫ u in Set.Icc (0 : ℝ) (t : ℝ), Davis.pdpGenerator (toDavisPDPStandard S hflow hf hr hli hne).toPDP (S.flowGenerator ψ) ψ.toDavisFunction (R.process u.toNNReal ω) ∂ volume ∂ R.P = 0 := by
      rw [ ← MeasureTheory.integral_sub, ← MeasureTheory.integral_sub ];
      · exact h_integrable t;
      · exact htm.endpoint_integrable t |> fun h => h.sub ( htm.endpoint_integrable 0 );
      · convert htm.generator_integrable t using 1;
        ext ω; congr; ext u; exact (by
        exact toDavisPDP_compatible S hflow hf hr |>.pdpGenerator_eq_extendedGenerator ψ hψ.measurable _);
      · exact htm.endpoint_integrable t;
      · convert htm.endpoint_integrable 0 using 1;
    rw [ show ∫ ω, ψ.toDavisFunction ( R.process 0 ω ) ∂ R.P = ψ.toDavisFunction R.initial from ?_ ] at h_integrable ; linarith!;
    rw [ MeasureTheory.integral_congr_ae ( R.process_zero.mono fun ω hω => by rw [ hω ] ) ] ; norm_num;
  convert h_integrable using 4;
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u hu => by rw [ toDavisPDPStandard_compatible S hflow hf hr hli hne |>.pdpGenerator_eq_extendedGenerator ψ hψ.measurable ] ; rfl;

/-
Hespanha's generator formula in absolute SHS time.  The realization starts
at `z₀`, its `qProcAbsolute` and `xProcAbsolute` are the SHS coordinate
processes, and the clock equation converts Davis elapsed time to absolute time.
-/
theorem theorem2_PDP_generator_absolute
    {Q : Type*} [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    {n m : ℕ} (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (ψ : TestFunction Q n)
    (hψ : DavisTestFunctionRegular S hflow hf hr hli hne R ψ)
    (hc : DavisCompensatorData S hflow hf hr hli hne R ψ)
    (htm : DavisTrueMartingaleData S hflow hf hr hli hne R ψ)
    (z₀ : InitialCondition Q n) (hinitial : R.initial = z₀.toDavisState)
    (t : ℝ≥0) :
    ∫ ω, ψ.toFun (R.qProcAbsolute (z₀.t₀ + (t : ℝ)) ω)
        (R.xProcAbsolute (z₀.t₀ + (t : ℝ)) ω) (z₀.t₀ + (t : ℝ)) ∂ R.P =
      ψ.toFun z₀.q₀ z₀.x₀ z₀.t₀ +
      ∫ ω, (∫ s in Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ)),
        S.extendedGenerator ψ (R.qProcAbsolute s ω)
          (R.xProcAbsolute s ω) s) ∂ R.P := by
  have := @theorem2_PDP_generator Q;
  convert this S hflow hf hr hli hne R ψ hψ hc htm t using 2;
  · simp +decide [ R.clock_eq, DavisProcessRealization.qProcAbsolute, DavisProcessRealization.xProcAbsolute ];
    simp +decide [ hinitial, InitialCondition.toDavisState ];
    exact funext fun ω => by rw [ show R.timeProc t ω = z₀.t₀ + t from by simpa [ hinitial ] using R.clock_eq t ω ] ;
  · exact hinitial.symm ▸ rfl;
  · refine' MeasureTheory.integral_congr_ae _;
    filter_upwards [ R.process_zero ] with ω hω;
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    rw [ ← MeasureTheory.integral_add_right_eq_self _ z₀.t₀ ] ; congr ; ext x ; split_ifs <;> simp_all +decide [ DavisProcessRealization.qProcAbsolute, DavisProcessRealization.xProcAbsolute ] ;
    · rw [ show R.timeProc x.toNNReal ω = z₀.t₀ + x from ?_ ];
      · simp +decide [ add_comm, InitialCondition.toDavisState ];
      · convert R.clock_eq x.toNNReal ω using 1;
        simp +decide [ hinitial, Real.toNNReal_of_nonneg ( by linarith : 0 ≤ x ) ];
        exact Real.ext_cauchy rfl;
    · linarith!;
    · linarith

end SHS