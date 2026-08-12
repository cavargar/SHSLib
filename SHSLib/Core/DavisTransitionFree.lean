import SHSLib.Core.FlowDynkin
import SHSLib.Core.Generator

open MeasureTheory MeasurableSpace Topology Filter
open scoped ENNReal NNReal

noncomputable section

/-! # The transition-free SHS as a Davis process: Theorem 1 without assumptions

`SHS.theorem1_generator_formula` derives Hespanha's Eq. (8) from a bundle of
Davis-level data (a process realization, a compensator package and
true-martingale data).  Nothing so far shows those bundles to be *inhabited*,
so the formula could in principle be vacuous.

This module removes that doubt in the transition-free case `m = 0`, where the
sample path is the deterministic flow.  Every Davis hypothesis bundle is
constructed explicitly on the one-point probability space, and Eq. (8) is then
obtained from `theorem1_generator_formula` — and independently checked against
the deterministic Dynkin identity of `SHSLib.Core.FlowDynkin`.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n : ℕ}

/-! ## Basic consequences of `m = 0` -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
@[simp] theorem totalIntensity_of_transition_free (S : SHS Q n 0)
    (z : DavisState Q n) : S.totalIntensity z = 0 := by
  simp [SHS.totalIntensity]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
@[simp] theorem davisJumpRate_of_transition_free (S : SHS Q n 0)
    (z : DavisState Q n) : davisJumpRate S z = 0 := by
  simp [davisJumpRate]

/-- With no transition channels, measurability of the intensities is vacuous. -/
instance intensitiesMeasurable_of_transition_free (S : SHS Q n 0) :
    S.IntensitiesMeasurable := ⟨fun ℓ => ℓ.elim0⟩

omit [MeasurableSingletonClass Q] in
/-- With no transition channels, the reset regularity conditions are vacuous. -/
theorem davisResetRegular_of_transition_free (S : SHS Q n 0) :
    DavisResetRegular S := ⟨fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0⟩

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A transition-free system has zero (hence bounded) Davis jump rate. -/
theorem davisBoundedRate_of_transition_free (S : SHS Q n 0) :
    DavisBoundedRate S := ⟨0, fun z => by simp⟩

/-- Local integrability of the (vanishing) jump rate. -/
theorem davisLocallyIntegrable_of_transition_free (S : SHS Q n 0)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow) :
    DavisLocallyIntegrable S hflow :=
  davisLocallyIntegrable_of_boundedRate S hflow hf
    (davisBoundedRate_of_transition_free S)

/-- Non-explosion of a transition-free system. -/
theorem davisNonExplosive_of_transition_free (S : SHS Q n 0)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow) :
    DavisNonExplosive S hflow hf (davisResetRegular_of_transition_free S) :=
  davisNonExplosive_of_boundedRate S hflow hf
    (davisResetRegular_of_transition_free S)
    (davisBoundedRate_of_transition_free S)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- For `m = 0` the extended generator is the flow (drift) generator. -/
theorem extendedGenerator_eq_flowGenerator (S : SHS Q n 0)
    (ψ : TestFunction Q n) (z : DavisState Q n) :
    S.extendedGenerator ψ z.1 z.2.1 z.2.2 = S.flowGenerator ψ z := by
  simp [SHS.extendedGenerator, SHS.flowGenerator]

/-- For `m = 0` the Davis generator of the constructed PDP is the flow
generator: the jump term carries the vanishing rate as a factor. -/
theorem pdpGenerator_of_transition_free (S : SHS Q n 0)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    (ψ : TestFunction Q n) (z : DavisState Q n) :
    Davis.pdpGenerator (toDavisPDP S hflow hf
        (davisResetRegular_of_transition_free S))
      (S.flowGenerator ψ) ψ.toDavisFunction z = S.flowGenerator ψ z := by
  simp [Davis.pdpGenerator, toDavisPDP]


/-! ## The deterministic realization on the one-point space -/

/-- The one-point probability space carrying the deterministic path of a
transition-free SHS. -/
def detRealization (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (initial : DavisState Q n) :
    DavisProcessRealization S hflow hf (davisResetRegular_of_transition_free S)
      (davisLocallyIntegrable_of_transition_free S hflow hf)
      (davisNonExplosive_of_transition_free S hflow hf) where
  Omega := Unit
  mOmega := inferInstance
  P := Measure.dirac ()
  probability := inferInstance
  filtration := Filtration.const ℝ≥0 (inferInstance : MeasurableSpace Unit) le_rfl
  sigmaFiniteFiltration := inferInstance
  process := fun u _ => davisFlow S hflow u initial
  initial := initial
  process_zero := Filter.Eventually.of_forall (fun _ => by
    simp [davisFlow, hflow.flow_init])
  clock_eq := fun _ _ => rfl

@[simp] theorem detRealization_process (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (initial : DavisState Q n) (u : ℝ≥0)
    (ω : (detRealization S hflow hf initial).Omega) :
    (detRealization S hflow hf initial).process u ω =
      davisFlow S hflow u initial := rfl

@[simp] theorem detRealization_initial (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (initial : DavisState Q n) :
    (detRealization S hflow hf initial).initial = initial := rfl


/-! ## Standing regularity for the deterministic construction -/

/-- Regularity of a transition-free system together with a test function: the
recorded partial derivatives are genuine, and both the drift and the flow
generator are continuous along every trajectory.  The test function is also
bounded and measurable, as required by Davis's domain conditions. -/
structure TransitionFreeRegular (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (ψ : TestFunction Q n) : Prop where
  partials : ψ.HasPartials
  drift_cont : ∀ q x t₀ t₁,
    ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s) (Set.Icc t₀ t₁)
  gen_cont : ∀ q x t₀ t₁,
    ContinuousOn (fun s => S.flowGenerator ψ (q, hflow.flow t₀ q x s, s))
      (Set.Icc t₀ t₁)
  measurable : Measurable ψ.toDavisFunction
  bounded : ∃ C : ℝ, ∀ z, |ψ.toDavisFunction z| ≤ C

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- **The deterministic Dynkin identity in Davis elapsed time.**  Along the
augmented flow of a transition-free SHS the compensated test function vanishes
identically. -/
theorem flowGenerator_integral_elapsed {m : ℕ} (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (ψ : TestFunction Q n) (hψ : ψ.HasPartials)
    (hdrift : ∀ q x t₀ t₁,
      ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s) (Set.Icc t₀ t₁))
    (hgen : ∀ q x t₀ t₁,
      ContinuousOn (fun s => S.flowGenerator ψ (q, hflow.flow t₀ q x s, s))
        (Set.Icc t₀ t₁))
    (z : DavisState Q n) {T : ℝ} (hT : 0 ≤ T) :
    (∫ u in Set.Icc (0 : ℝ) T,
        S.flowGenerator ψ (davisFlow S hflow u.toNNReal z)) =
      ψ.toDavisFunction (davisFlow S hflow T.toNNReal z) - ψ.toDavisFunction z := by
  obtain ⟨q, x, t₀⟩ := z
  set F : ℝ → ℝ := fun s => S.flowGenerator ψ (q, hflow.flow t₀ q x s, s) with hF
  -- rewrite the elapsed-time integrand
  have hstep1 : (∫ u in Set.Icc (0 : ℝ) T,
      S.flowGenerator ψ (davisFlow S hflow u.toNNReal (q, x, t₀))) =
      ∫ u in Set.Icc (0 : ℝ) T, F (t₀ + u) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    have : (u.toNNReal : ℝ) = u := Real.coe_toNNReal u hu.1
    simp [davisFlow, hF, this]
  -- change variables to absolute time
  have hstep2 : (∫ u in Set.Icc (0 : ℝ) T, F (t₀ + u)) =
      ∫ s in Set.Icc t₀ (t₀ + T), F s := by
    rw [integral_Icc_elapsed_to_absolute (fun u => F (t₀ + u)) t₀ T hT]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro s _
    simp
  -- Newton–Leibniz along the flow
  have hcont := hdrift q x t₀ (t₀ + T)
  have hgenint : IntervalIntegrable F volume t₀ (t₀ + T) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by linarith : t₀ ≤ t₀ + T)]
    exact hgen q x t₀ (t₀ + T)
  have hdynkin := flow_dynkin_identity S hflow ψ hψ t₀ (t₀ + T)
    (by linarith) q x hcont hgenint
  have hstep3 : (∫ s in Set.Icc t₀ (t₀ + T), F s) = ∫ s in t₀..(t₀ + T), F s := by
    rw [intervalIntegral.integral_of_le (by linarith : t₀ ≤ t₀ + T),
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hTc : (T.toNNReal : ℝ) = T := Real.coe_toNNReal T hT
  rw [hstep1, hstep2, hstep3]
  simp only [hF]
  rw [← hdynkin]
  simp [TestFunction.toDavisFunction, davisFlow, hTc]


/-! ## Continuity of the test function along the augmented flow -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The lifted test function is continuous along every augmented trajectory. -/
theorem continuous_testFun_along_davisFlow {m : ℕ} (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (ψ : TestFunction Q n) (hψ : ψ.HasPartials)
    (hdrift : ∀ q x t₀ t₁,
      ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s) (Set.Icc t₀ t₁))
    (z : DavisState Q n) :
    Continuous (fun t : ℝ =>
      ψ.toDavisFunction (davisFlow S hflow t.toNNReal z)) := by
  obtain ⟨q, x, t₀⟩ := z
  have hclock : Continuous (fun t : ℝ => t₀ + (t.toNNReal : ℝ)) := by
    simp only [Real.coe_toNNReal']
    fun_prop
  have hmaps : ∀ t : ℝ, t₀ + (t.toNNReal : ℝ) ∈ Set.Ici t₀ := by
    intro t
    simp
  have hpath : ContinuousOn (fun s => ψ.toFun q (hflow.flow t₀ q x s) s)
      (Set.Ici t₀) := by
    have hflowcont := hflow.continuousOn_flow_Ici S t₀ q x
      (fun t₁ => hdrift q x t₀ t₁)
    exact (hψ.continuous q).comp_continuousOn
      (hflowcont.prodMk continuousOn_id)
  have := hpath.comp_continuous hclock hmaps
  simpa [TestFunction.toDavisFunction, davisFlow, Function.comp] using this

/-! ## The Davis data bundles of the deterministic realization -/

/-- The lifted test function satisfies Davis's domain regularity along the
deterministic realization. -/
theorem detTestFunctionRegular (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (ψ : TestFunction Q n)
    (hreg : TransitionFreeRegular S hflow ψ) (initial : DavisState Q n) :
    DavisTestFunctionRegular S hflow hf (davisResetRegular_of_transition_free S)
      (davisLocallyIntegrable_of_transition_free S hflow hf)
      (davisNonExplosive_of_transition_free S hflow hf)
      (detRealization S hflow hf initial) ψ where
  measurable := hreg.measurable
  flow_regular := fun z =>
    (continuous_testFun_along_davisFlow S hflow ψ hreg.partials
      hreg.drift_cont z).locallyIntegrable
  bounded := hreg.bounded

/-- Every function on the one-point space is integrable for the Dirac measure. -/
theorem integrable_unit (g : Unit → ℝ) : Integrable g (Measure.dirac ()) := by
  refine (integrable_const (g ())).congr ?_
  filter_upwards with u
  cases u
  rfl

/-- **The compensator data of the deterministic realization.**  There are no
jumps, so the localizing sequence can be taken deterministic, the compensated
jump process vanishes identically, and the pathwise decomposition is the
deterministic Dynkin identity. -/
def detCompensatorData (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (ψ : TestFunction Q n)
    (hreg : TransitionFreeRegular S hflow ψ) (initial : DavisState Q n) :
    DavisCompensatorData S hflow hf (davisResetRegular_of_transition_free S)
      (davisLocallyIntegrable_of_transition_free S hflow hf)
      (davisNonExplosive_of_transition_free S hflow hf)
      (detRealization S hflow hf initial) ψ where
  sigma := fun k _ => (k : ℝ≥0)
  sigma_stopping := fun k => isStoppingTime_const _ _
  sigma_tendsto := Filter.Eventually.of_forall (fun _ => by
    simpa using ENNReal.tendsto_nat_nhds_top)
  jumpCompensated := fun _ _ => 0
  decomposition := by
    intro k t ω
    have hT : (0 : ℝ) ≤ ((min t (k : ℝ≥0) : ℝ≥0) : ℝ) := (min t (k : ℝ≥0)).coe_nonneg
    have hgen : ∀ z : DavisState Q n,
        Davis.pdpGenerator (toDavisPDPStandard S hflow hf
            (davisResetRegular_of_transition_free S)
            (davisLocallyIntegrable_of_transition_free S hflow hf)
            (davisNonExplosive_of_transition_free S hflow hf)).toPDP
          (S.flowGenerator ψ) ψ.toDavisFunction z = S.flowGenerator ψ z :=
      fun z => pdpGenerator_of_transition_free S hflow hf ψ z
    simp only [detRealization_process, hgen]
    have hkey := flowGenerator_integral_elapsed S hflow ψ hreg.partials
      hreg.drift_cont hreg.gen_cont initial hT
    have hzero : davisFlow S hflow 0 initial = initial := by
      simp [davisFlow, hflow.flow_init]
    rw [hzero]
    have hcoe : (((min t (k : ℝ≥0) : ℝ≥0) : ℝ)).toNNReal = min t (k : ℝ≥0) :=
      Real.toNNReal_coe
    rw [hcoe] at hkey
    rw [← NNReal.coe_min, hkey]
    ring
  jump_martingale := fun k => by
    simpa using martingale_zero (Ω := Unit) ℝ
      (detRealization S hflow hf initial).filtration
      (detRealization S hflow hf initial).P


/-- Every function on the one-point space is measurable. -/
theorem measurable_unit {m : MeasurableSpace Unit} (g : Unit → ℝ) :
    Measurable[m] g := by
  have hg : g = fun _ => g () := funext fun u => by cases u; rfl
  rw [hg]
  exact measurable_const

/-- **The true-martingale data of the deterministic realization.**  Conditions
(15)–(16) are vacuous (no transitions), all integrals live on a one-point
space, and the compensated process vanishes, so the envelope can be taken to be
zero. -/
def detTrueMartingaleData (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (ψ : TestFunction Q n)
    (hreg : TransitionFreeRegular S hflow ψ) (initial : DavisState Q n) :
    DavisTrueMartingaleData S hflow hf (davisResetRegular_of_transition_free S)
      (davisLocallyIntegrable_of_transition_free S hflow hf)
      (davisNonExplosive_of_transition_free S hflow hf)
      (detRealization S hflow hf initial) ψ where
  finite_transitions := fun t => integrable_unit _
  finite_jumps := fun t => integrable_unit _
  endpoint_integrable := fun t => integrable_unit _
  generator_integrable := fun t => integrable_unit _
  adapted := fun t => measurable_unit _
  envelope := fun _ => 0
  envelope_integrable := integrable_unit _
  dominated := by
    intro t ω
    have hT : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
    have hgen : ∀ z : DavisState Q n,
        Davis.pdpGenerator (toDavisPDPStandard S hflow hf
            (davisResetRegular_of_transition_free S)
            (davisLocallyIntegrable_of_transition_free S hflow hf)
            (davisNonExplosive_of_transition_free S hflow hf)).toPDP
          (S.flowGenerator ψ) ψ.toDavisFunction z = S.flowGenerator ψ z :=
      fun z => pdpGenerator_of_transition_free S hflow hf ψ z
    simp only [detRealization_process, hgen]
    have hkey := flowGenerator_integral_elapsed S hflow ψ hreg.partials
      hreg.drift_cont hreg.gen_cont initial hT
    have hzero : davisFlow S hflow 0 initial = initial := by
      simp [davisFlow, hflow.flow_init]
    rw [Real.toNNReal_coe] at hkey
    rw [hzero, hkey]
    simp


/-! ## Eq. (8) for a transition-free system: the trajectory-local version

The route through `theorem1_generator_formula` below needs the test function to
be bounded and measurable and needs continuity along *every* trajectory,
because those are the hypotheses Davis's martingale machinery asks for.  For a
transition-free system none of that is really necessary: the identity is the
deterministic Dynkin identity, and only the single trajectory issued from the
initial condition is involved.  The following statement records that stronger
form. -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- **Hespanha's Eq. (8) for a transition-free SHS, assuming regularity only
along the trajectory under consideration.**

Compared with `SHS.eq8_transition_free` this drops the boundedness and
measurability of the test function altogether and localizes the two continuity
hypotheses to the time interval `[t₀, t₀ + t]` of the trajectory issued from
`z₀`. -/
theorem eq8_transition_free_of_trajectory (S : SHS Q n 0)
    (hflow : S.HasGlobalFlow) (ψ : TestFunction Q n) (hψ : ψ.HasPartials)
    (z₀ : InitialCondition Q n) (t : ℝ≥0)
    (hdrift : ContinuousOn (fun s => S.f z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s)
      (Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ))))
    (hgen : ContinuousOn
      (fun s => S.extendedGenerator ψ z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s)
      (Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ)))) :
    ψ.toFun z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ (z₀.t₀ + (t : ℝ)))
        (z₀.t₀ + (t : ℝ)) =
      ψ.toFun z₀.q₀ z₀.x₀ z₀.t₀ +
        ∫ s in Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ)),
          S.extendedGenerator ψ z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s := by
  have hle : z₀.t₀ ≤ z₀.t₀ + (t : ℝ) := by
    have : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
    linarith
  have hEq : ∀ s : ℝ,
      S.extendedGenerator ψ z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s =
        S.flowGenerator ψ (z₀.q₀, hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s, s) :=
    fun s => extendedGenerator_eq_flowGenerator S ψ
      (z₀.q₀, hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s, s)
  have hgen' : ContinuousOn
      (fun s => S.flowGenerator ψ (z₀.q₀, hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s, s))
      (Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ))) := by
    simpa [hEq] using hgen
  have hint : IntervalIntegrable
      (fun s => S.flowGenerator ψ (z₀.q₀, hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s, s))
      volume z₀.t₀ (z₀.t₀ + (t : ℝ)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le hle]
  have hdyn := flow_dynkin_identity S hflow ψ hψ z₀.t₀ (z₀.t₀ + (t : ℝ)) hle
    z₀.q₀ z₀.x₀ hdrift hint
  have hIcc : (∫ s in Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ)),
      S.extendedGenerator ψ z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s) =
      ∫ s in z₀.t₀..(z₀.t₀ + (t : ℝ)),
        S.flowGenerator ψ (z₀.q₀, hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s, s) := by
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun s _ => hEq s)
  rw [hIcc, ← hdyn]
  ring


/-! ## Hespanha's Eq. (8) for a transition-free system, with no assumed data -/

@[simp] theorem detRealization_P (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (initial : DavisState Q n) :
    (detRealization S hflow hf initial).P = Measure.dirac () := rfl

/-- Integration against the deterministic realization is evaluation at the
single sample point. -/
theorem integral_detRealization (S : SHS Q n 0) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (initial : DavisState Q n)
    (g : (detRealization S hflow hf initial).Omega → ℝ) :
    ∫ ω, g ω ∂(detRealization S hflow hf initial).P = g () := by
  show ∫ ω, g ω ∂(Measure.dirac ()) = g ()
  simp

@[simp] theorem detRealization_qProcAbsolute (S : SHS Q n 0)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    (initial : DavisState Q n) (s : ℝ)
    (ω : (detRealization S hflow hf initial).Omega) :
    (detRealization S hflow hf initial).qProcAbsolute s ω = initial.1 := rfl

theorem detRealization_xProcAbsolute (S : SHS Q n 0)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    (initial : DavisState Q n) {s : ℝ} (hs : initial.2.2 ≤ s)
    (ω : (detRealization S hflow hf initial).Omega) :
    (detRealization S hflow hf initial).xProcAbsolute s ω =
      hflow.flow initial.2.2 initial.1 initial.2.1 s := by
  have hsub : ((s - initial.2.2).toNNReal : ℝ) = s - initial.2.2 :=
    Real.coe_toNNReal _ (by linarith)
  simp only [DavisProcessRealization.xProcAbsolute,
    DavisProcessRealization.xProc, detRealization_process, detRealization_initial,
    davisFlow, hsub]
  ring_nf

/-- **Hespanha's Eq. (8) for a transition-free SHS.**  The Davis data required
by `SHS.theorem1_generator_formula` is *constructed* here rather than assumed,
so the identity holds outright: for every `C¹` bounded test function whose
drift and generator are continuous along trajectories,

`ψ(q₀, φ(t₀+t), t₀+t) = ψ(q₀, x₀, t₀) + ∫_{t₀}^{t₀+t} (Lψ)(q₀, φ(s), s) ds`.

In particular the hypothesis bundles of Theorem 1 are inhabited, so that
theorem is not vacuous. -/
theorem eq8_transition_free {Q : Type*} [Fintype Q] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] {n : ℕ}
    (S : SHS Q n 0) (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    (ψ : TestFunction Q n) (hreg : TransitionFreeRegular S hflow ψ)
    (z₀ : InitialCondition Q n) (t : ℝ≥0) :
    ψ.toFun z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ (z₀.t₀ + (t : ℝ)))
        (z₀.t₀ + (t : ℝ)) =
      ψ.toFun z₀.q₀ z₀.x₀ z₀.t₀ +
        ∫ s in Set.Icc z₀.t₀ (z₀.t₀ + (t : ℝ)),
          S.extendedGenerator ψ z₀.q₀ (hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s) s := by
  have h := theorem1_generator_formula S hflow hf
    (davisResetRegular_of_transition_free S)
    (hli := davisLocallyIntegrable_of_transition_free S hflow hf)
    (hne := davisNonExplosive_of_transition_free S hflow hf)
    (detRealization S hflow hf z₀.toDavisState) ψ
    (detTestFunctionRegular S hflow hf ψ hreg z₀.toDavisState)
    (detCompensatorData S hflow hf ψ hreg z₀.toDavisState)
    (detTrueMartingaleData S hflow hf ψ hreg z₀.toDavisState)
    z₀ rfl t
  have hx : ∀ {s : ℝ}, z₀.t₀ ≤ s →
      (detRealization S hflow hf (z₀.q₀, z₀.x₀, z₀.t₀)).xProcAbsolute s () =
        hflow.flow z₀.t₀ z₀.q₀ z₀.x₀ s := by
    intro s hs
    exact detRealization_xProcAbsolute S hflow hf (z₀.q₀, z₀.x₀, z₀.t₀) hs ()
  have hle : z₀.t₀ ≤ z₀.t₀ + (t : ℝ) := by
    have : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
    linarith
  rw [integral_detRealization, integral_detRealization] at h
  simp only [detRealization_qProcAbsolute, InitialCondition.toDavisState] at h
  rw [hx hle] at h
  rw [h]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro s hs
  exact congrArg (fun y => S.extendedGenerator ψ z₀.q₀ y s) (hx hs.1)

end SHS
