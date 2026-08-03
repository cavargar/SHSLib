import SHSLib.Core.DavisBridge

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-!
# Concrete Davis PDP associated with an SHS

This module constructs the homogeneous time-augmented PDP of an SHS.  The
extra hypotheses below isolate exactly the regularity facts not contained in
`SHS.HasGlobalFlow`: measurable flow and its composition law, measurable
resets, exclusion of genuine self resets, and a measurable non-self fallback
used only where the total jump intensity is zero.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The time-augmented deterministic flow. -/
def davisFlow (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (u : ℝ≥0) (z : DavisState Q n) : DavisState Q n :=
  (z.1, hflow.flow z.2.2 z.1 z.2.1 (z.2.2 + (u : ℝ)),
    z.2.2 + (u : ℝ))

/-- Measurability and the cocycle law required of the augmented flow. -/
structure DavisFlowRegular (S : SHS Q n m) (hflow : S.HasGlobalFlow) : Prop where
  measurable : ∀ u : ℝ≥0, Measurable (davisFlow S hflow u)
  /-- Joint measurability is needed to integrate rates along flow trajectories. -/
  measurable_joint : Measurable (fun p : ℝ≥0 × DavisState Q n =>
    davisFlow S hflow p.1 p.2)
  add : ∀ s t : ℝ≥0, ∀ z, davisFlow S hflow (s + t) z =
    davisFlow S hflow s (davisFlow S hflow t z)

/-- Regularity of the original non-autonomous global flow, in a form that is
convenient for constructing the time-augmented Davis flow.  The restart law
says that restarting a trajectory at any intermediate absolute time gives the
same future trajectory. -/
structure DavisGlobalFlowRegular (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) : Prop where
  measurable_flow : Measurable (fun p : ℝ × Q × EuclideanSpace ℝ (Fin n) × ℝ =>
    hflow.flow p.1 p.2.1 p.2.2.1 p.2.2.2)
  restart : ∀ (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (t u : ℝ),
    hflow.flow t₀ q x (t + u) =
      hflow.flow t q (hflow.flow t₀ q x t) (t + u)

/-- Joint measurability and the restart law of a concrete non-autonomous flow
supply all regularity fields required by its time augmentation. -/
theorem davisFlowRegular_of_globalFlowRegular (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hreg : DavisGlobalFlowRegular S hflow) :
    DavisFlowRegular S hflow := by
  refine ⟨?measurable, ?measurable_joint, ?add⟩
  case measurable =>
    intro u
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact measurable_fst
    · -- hflow.flow a.2.2 a.1 a.2.1 (a.2.2 + u)
      convert hreg.measurable_flow.comp (by fun_prop : Measurable (fun a : DavisState Q n => (a.2.2, a.1, a.2.1, a.2.2 + ↑u))) using 1
    · exact measurable_snd.snd.add measurable_const
  case measurable_joint =>
    simp [davisFlow]
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact measurable_snd.fst
    · convert hreg.measurable_flow.comp (by fun_prop : Measurable (fun p : ℝ≥0 × DavisState Q n => (p.2.2.2, p.2.1, p.2.2.1, p.2.2.2 + p.1))) using 1
    · exact Measurable.add measurable_snd.snd.snd (by fun_prop : Measurable fun p : ℝ≥0 × DavisState Q n => ENNReal.toReal p.1)
  case add =>
    intro s t z
    simp [davisFlow]
    -- restart: hflow.flow t₀ q x (t + u) = hflow.flow t q (hflow.flow t₀ q x t) (t + u)
    -- We want: flow z.2.2 q x (z.2.2 + s + t) = flow (z.2.2 + t) q (flow z.2.2 q x (z.2.2 + t)) (z.2.2 + t + s)
    -- Set t₀ = z.2.2, elapsed = t, u = s, so t + u = t + s in restart args
    have h := hreg.restart (z.2.2) z.1 z.2.1 (z.2.2 + ↑t) (↑s)
    have heq : z.2.2 + (↑s + ↑t) = z.2.2 + ↑t + ↑s := by ring
    constructor
    · rw [heq]
      exact h
    · ring

/-- A directly usable constructor when the measurable-flow and restart facts
are available separately. -/
theorem davisFlowRegular_of_measurable_restart (S : SHS Q n m)
    (hflow : S.HasGlobalFlow)
    (hmeas : Measurable (fun p : ℝ × Q × EuclideanSpace ℝ (Fin n) × ℝ =>
      hflow.flow p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hrestart : ∀ (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
      (t u : ℝ),
      hflow.flow t₀ q x (t + u) =
        hflow.flow t q (hflow.flow t₀ q x t) (t + u)) :
    DavisFlowRegular S hflow := by
  exact davisFlowRegular_of_globalFlowRegular S hflow
    ⟨hmeas, hrestart⟩

/-- Canonical non-self destination used by the reset kernel only when the total
intensity is zero.  Advancing the otherwise irrelevant clock avoids imposing
an existence assumption on the state space. -/
def zeroIntensityFallback (z : DavisState Q n) : DavisState Q n :=
  (z.1, z.2.1, z.2.2 + 1)

@[simp] theorem zeroIntensityFallback_ne (z : DavisState Q n) :
    zeroIntensityFallback z ≠ z := by
  intro h
  have ht : z.2.2 + 1 = z.2.2 := congrArg (fun y => y.2.2) h
  linarith

/-- Measurable-reset assumptions. Active reset channels must genuinely change
state.  The zero-rate fallback is canonical and has no effect on the weighted
jump compensator. -/
structure DavisResetRegular (S : SHS Q n m) : Prop where
  reset_measurable : ∀ ℓ : Fin m, Measurable (S.resetDavisState ℓ)
  active_reset_ne : ∀ ℓ z,
    0 < S.intensity ℓ z.1 z.2.1 z.2.2 → S.resetDavisState ℓ z ≠ z

/-- The nonnegative Davis jump rate obtained by summing marked SHS rates. -/
def davisJumpRate (S : SHS Q n m) (z : DavisState Q n) : ℝ≥0 :=
  Real.toNNReal (S.totalIntensity z)

/-- The normalized finite marked-reset probability measure.  At zero total
intensity it is the Dirac mass at the designated non-self fallback. -/
def markedResetMeasure (S : SHS Q n m)
    (z : DavisState Q n) : Measure (DavisState Q n) :=
  if S.totalIntensity z = 0 then
    Measure.dirac (zeroIntensityFallback z)
  else
    ∑ ℓ : Fin m,
      ENNReal.ofReal (S.intensity ℓ z.1 z.2.1 z.2.2 / S.totalIntensity z) •
        Measure.dirac (S.resetDavisState ℓ z)

/-
The finite marked-reset kernel.
-/
def markedResetKernel (S : SHS Q n m) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] : Kernel (DavisState Q n) (DavisState Q n) := by
  refine Kernel.mk (markedResetMeasure S) ?_
  have h_measurable : Measurable (fun z : DavisState Q n => S.totalIntensity z) := by
    exact Finset.measurable_sum _ fun i _ => IntensitiesMeasurable.measurable i
  intro s hs;
  unfold SHS.markedResetMeasure;
  have h_measurable : ∀ ℓ, Measurable (fun z : DavisState Q n => ENNReal.ofReal (S.intensity ℓ z.1 z.2.1 z.2.2 / S.totalIntensity z) • Measure.dirac (S.resetDavisState ℓ z)) := by
    intro ℓ;
    have h_measurable : Measurable (fun z : DavisState Q n => ENNReal.ofReal (S.intensity ℓ z.1 z.2.1 z.2.2 / S.totalIntensity z)) := by
      exact Measurable.ennreal_ofReal ( Measurable.div ( by exact ‹S.IntensitiesMeasurable›.measurable ℓ ) h_measurable );
    apply_rules [ MeasureTheory.Measure.measurable_of_measurable_coe, measurable_const ];
    intro s hs; by_cases h : MeasurableSet s <;> simp_all +decide [ MeasureTheory.Measure.dirac_apply ] ;
    exact Measurable.mul h_measurable ( Measurable.indicator measurable_const ( hr.reset_measurable ℓ h ) );
  convert MeasurableSet.union ( MeasurableSet.inter ( show MeasurableSet { z : DavisState Q n | S.totalIntensity z = 0 } from measurableSet_eq_fun ( by assumption ) measurable_const ) ( show MeasurableSet ( ( fun z => Measure.dirac ( zeroIntensityFallback z ) ) ⁻¹' s ) from ?_ ) ) ( MeasurableSet.inter ( show MeasurableSet { z : DavisState Q n | S.totalIntensity z ≠ 0 } from measurableSet_eq_fun ( by assumption ) measurable_const |> MeasurableSet.compl ) ( show MeasurableSet ( ( fun z => ∑ ℓ, ENNReal.ofReal ( S.intensity ℓ z.1 z.2.1 z.2.2 / S.totalIntensity z ) • Measure.dirac ( S.resetDavisState ℓ z ) ) ⁻¹' s ) from ?_ ) ) using 1;
  · ext; aesop;
  · convert hs.preimage ( show Measurable ( fun z => Measure.dirac ( zeroIntensityFallback z ) ) from ?_ ) using 1;
    exact MeasureTheory.Measure.measurable_dirac.comp (by fun_prop)
  · exact hs.preimage ( Finset.measurable_sum _ fun _ _ => h_measurable _ )

/-- The finite marked-reset measure depends measurably on its pre-jump state. -/
theorem markedResetMeasure_measurable (S : SHS Q n m)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable] :
    Measurable (markedResetMeasure S) :=
  (markedResetKernel S hr).measurable

/-- The marked-reset kernel is Markov. -/
theorem markedResetKernel_isMarkov (S : SHS Q n m)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable] :
    IsMarkovKernel (markedResetKernel S hr) := by
  constructor;
  intro z
  by_cases h : S.totalIntensity z = 0;
  · simp [h, markedResetKernel];
    constructor ; simp +decide [ h, markedResetMeasure ];
  · constructor;
    have h_sum : ∑ ℓ : Fin m, S.intensity ℓ z.1 z.2.1 z.2.2 / S.totalIntensity z = 1 := by
      rw [ ← Finset.sum_div, div_eq_iff h ] ; simp +decide [ SHS.totalIntensity ];
    convert congr_arg ENNReal.ofReal h_sum using 1;
    · unfold SHS.markedResetKernel;
      unfold SHS.markedResetMeasure; simp +decide [ h ] ;
      rw [ ENNReal.ofReal_sum_of_nonneg fun _ _ => div_nonneg ( show 0 ≤ S.intensity _ _ _ _ from _ ) ( show 0 ≤ S.totalIntensity _ from _ ) ];
      · exact fun _ _ => S.intensity_nonneg _ _ _ _;
      · exact fun _ _ => totalIntensity_nonneg S z;
    · norm_num

/-- The marked-reset kernel has no self jumps, including at zero intensity. -/
theorem markedResetKernel_no_self_jump (S : SHS Q n m)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (z : DavisState Q n) : markedResetKernel S hr z {z} = 0 := by
  unfold SHS.markedResetKernel;
  unfold SHS.markedResetMeasure;
  by_cases h : S.totalIntensity z = 0 <;> simp +decide [ h, zeroIntensityFallback_ne ];
  intro ℓ; by_cases hℓ : 0 < S.intensity ℓ z.1 z.2.1 z.2.2 <;> simp_all +decide [ div_nonpos_iff ] ;
  · exact Or.inr ( hr.active_reset_ne ℓ z hℓ );
  · exact Or.inl <| Or.inr <| totalIntensity_nonneg S z

/-- Weighted finite-kernel integral identity. Weighting avoids any dependence
on the zero-rate fallback. -/
theorem markedResetKernel_weighted_integral (S : SHS Q n m)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (g : DavisState Q n → ℝ) (z : DavisState Q n) :
    (davisJumpRate S z : ℝ) * (∫ y, g y ∂(markedResetKernel S hr z)) =
      ∑ ℓ : Fin m, g (S.resetDavisState ℓ z) *
        S.intensity ℓ z.1 z.2.1 z.2.2 := by
  unfold markedResetKernel;
  unfold davisJumpRate markedResetMeasure; by_cases h : S.totalIntensity z = 0 <;> simp +decide [h]
  · exact Eq.symm ( Finset.sum_eq_zero fun i _ => by rw [ show S.intensity i z.1 z.2.1 z.2.2 = 0 from le_antisymm ( by exact le_trans ( Finset.single_le_sum ( fun a _ => S.intensity_nonneg a z.1 z.2.1 z.2.2 ) ( Finset.mem_univ i ) ) h.le ) ( S.intensity_nonneg i z.1 z.2.1 z.2.2 ) ] ; ring );
  · rw [ max_eq_left ( totalIntensity_nonneg S z ), MeasureTheory.integral_finset_sum_measure ];
    · simp +decide [mul_comm, Finset.mul_sum _ _ _,
        MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
      exact Finset.sum_congr rfl fun _ _ => by rw [ ENNReal.toReal_ofReal ( div_nonneg ( S.intensity_nonneg _ _ _ _ ) ( totalIntensity_nonneg S z ) ), mul_left_comm, mul_div_cancel₀ _ h ] ;
    · intro i _; apply_rules [ MeasureTheory.Integrable.smul_measure, MeasureTheory.integrable_dirac ] ;
      · exact ENNReal.coe_lt_top;
      · exact ENNReal.ofReal_ne_top

/-- The concrete time-augmented Davis PDP associated with an SHS. -/
def toDavisPDP (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] : Davis.PDP (DavisState Q n) where
  flow := davisFlow S hflow
  flow_zero := by
    intro z
    simp [davisFlow, hflow.flow_init]
  flow_add := hf.add
  flow_measurable := hf.measurable
  jumpRate := davisJumpRate S
  jumpRate_measurable := by
    exact Measurable.ennreal_toNNReal ( Measurable.ennreal_ofReal ( Finset.measurable_sum _ fun i _ => ‹S.IntensitiesMeasurable›.measurable i ) )
  transitionMeasure := markedResetKernel S hr
  transitionMeasure_markov := markedResetKernel_isMarkov S hr
  no_self_jump := markedResetKernel_no_self_jump S hr

/-- Local integrability required to strengthen the concrete PDP to a standard
Davis PDP. -/
structure DavisLocallyIntegrable (S : SHS Q n m) (hflow : S.HasGlobalFlow) : Prop where
  jumpRate : ∀ z : DavisState Q n, ∃ eps : ℝ, 0 < eps ∧
    IntervalIntegrable
      (fun s => (davisJumpRate S (davisFlow S hflow s.toNNReal z) : ℝ)) volume 0 eps

/-- Non-explosion assumption, stated directly for the constructed PDP. -/
def DavisNonExplosive (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] : Prop :=
  Davis.PDPNonExplosive (toDavisPDP S hflow hf hr)

/-- A uniform bound on the total jump rate of the time-augmented SHS. -/
def DavisBoundedRate (S : SHS Q n m) : Prop :=
  ∃ c : ℝ≥0, ∀ z : DavisState Q n, davisJumpRate S z ≤ c

/-- Per-channel real bounds imply a uniform bound on the total Davis jump rate. -/
theorem davisBoundedRate_of_channel_bounds (S : SHS Q n m)
    (c : Fin m → ℝ≥0)
    (hc : ∀ ℓ (z : DavisState Q n), S.intensity ℓ z.1 z.2.1 z.2.2 ≤ c ℓ) :
    DavisBoundedRate S := by
  use ∑ ℓ, c ℓ
  intro z
  unfold davisJumpRate
  simp only [Real.toNNReal_le_iff_le_coe]
  calc S.totalIntensity z
      = ∑ ℓ : Fin m, S.intensity ℓ z.1 z.2.1 z.2.2 := rfl
    _ ≤ ∑ ℓ : Fin m, (c ℓ : ℝ) := by
        apply Finset.sum_le_sum
        intro ℓ _
        exact hc ℓ z
    _ = (∑ ℓ, c ℓ : ℝ≥0) := by simp

/-- The real-valued Davis rate along each augmented flow trajectory is
measurable in elapsed time. -/
lemma davisJumpRate_comp_flow_measurable (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    [S.IntensitiesMeasurable] (z : DavisState Q n) :
    Measurable (fun s : ℝ =>
      (davisJumpRate S (davisFlow S hflow s.toNNReal z) : ℝ)) := by
  have hflow_meas : Measurable (fun s : ℝ =>
      davisFlow S hflow s.toNNReal z) :=
    hf.measurable_joint.comp
      (measurable_real_toNNReal.prodMk measurable_const)
  have hrate_meas : Measurable (davisJumpRate S) := by
    exact Measurable.ennreal_toNNReal (Measurable.ennreal_ofReal
      (Finset.measurable_sum _ fun i _ => ‹S.IntensitiesMeasurable›.measurable i))
  exact (hrate_meas.comp hflow_meas).coe_nnreal_real

/-- A measurable uniformly bounded jump rate is locally integrable along the
augmented flow. -/
theorem davisLocallyIntegrable_of_boundedRate (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    [S.IntensitiesMeasurable] (hb : DavisBoundedRate S) :
    DavisLocallyIntegrable S hflow := by
  rcases hb with ⟨c, hc⟩
  constructor
  intro z
  refine ⟨1, by norm_num, ?_⟩
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ne_of_lt (measure_Ioc_lt_top (μ := volume) (a := (0 : ℝ)) (b := 1))
  · exact (davisJumpRate_comp_flow_measurable S hflow hf z).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast hc (davisFlow S hflow s.toNNReal z)

/-- A uniform rate bound discharges the Davis non-explosion condition for the
time-augmented construction, whose state space has no active boundary. -/
theorem davisNonExplosive_of_boundedRate (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (hb : DavisBoundedRate S) :
    DavisNonExplosive S hflow hf hr := by
  apply Davis.nonexplosive_of_bounded_rate_no_boundary
  exact hb

/-- Package the concrete PDP under Davis's standard hypotheses. -/
def toDavisPDPStandard (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr) :
    Davis.PDPStandard (DavisState Q n) where
  toPDP := toDavisPDP S hflow hf hr
  jumpRate_locally_integrable := hli.jumpRate
  nonExplosive := hne

/-- A uniformly bounded concrete SHS rate directly yields a standard Davis
PDP, with local integrability and non-explosion derived automatically. -/
def toDavisPDPStandardOfBoundedRate (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (hb : DavisBoundedRate S) : Davis.PDPStandard (DavisState Q n) :=
  toDavisPDPStandard S hflow hf hr
    (davisLocallyIntegrable_of_boundedRate S hflow hf hb)
    (davisNonExplosive_of_boundedRate S hflow hf hr hb)

/-- Package a concrete SHS directly from regularity of its original global
flow, measurable non-self resets, and finite per-channel rate bounds. -/
def toDavisPDPStandardOfChannelBounds (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hflowReg : DavisGlobalFlowRegular S hflow)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (c : Fin m → ℝ≥0)
    (hc : ∀ ℓ (z : DavisState Q n),
      S.intensity ℓ z.1 z.2.1 z.2.2 ≤ c ℓ) :
    Davis.PDPStandard (DavisState Q n) :=
  toDavisPDPStandardOfBoundedRate S hflow
    (davisFlowRegular_of_globalFlowRegular S hflow hflowReg) hr
    (davisBoundedRate_of_channel_bounds S c hc)

/-- The concrete PDP realizes exactly the SHS local characteristics. -/
theorem toDavisPDP_compatible (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] :
    DavisCompatible S hflow (toDavisPDP S hflow hf hr) := by
  constructor
  · intro u z
    rfl
  · exact fun z => Real.coe_toNNReal _ ( totalIntensity_nonneg S z );
  · intro g hg z
    have := markedResetKernel_weighted_integral S hr g z
    simp [toDavisPDP, davisJumpRate, totalIntensity] at this ⊢;
    simp_all +decide [ sub_mul, Finset.sum_sub_distrib ];
    rw [ max_eq_left ( Finset.sum_nonneg fun _ _ => S.intensity_nonneg _ _ _ _ ), ← Finset.mul_sum _ _ _, mul_comm ]

/-- Compatibility for the underlying PDP of the standard package. -/
theorem toDavisPDPStandard_compatible (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr) :
    DavisCompatible S hflow (toDavisPDPStandard S hflow hf hr hli hne).toPDP := by
  exact toDavisPDP_compatible S hflow hf hr

/-- The high-level channel-bound constructor retains the exact SHS local
characteristics in its underlying Davis PDP. -/
theorem toDavisPDPStandardOfChannelBounds_compatible (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hflowReg : DavisGlobalFlowRegular S hflow)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    (c : Fin m → ℝ≥0)
    (hc : ∀ ℓ (z : DavisState Q n),
      S.intensity ℓ z.1 z.2.1 z.2.2 ≤ c ℓ) :
    DavisCompatible S hflow
      (toDavisPDPStandardOfChannelBounds S hflow hflowReg hr c hc).toPDP := by
  exact toDavisPDP_compatible S hflow
    (davisFlowRegular_of_globalFlowRegular S hflow hflowReg) hr

/-- A convenient constructor when every reset is measurable and globally
non-self.  This is stronger than necessary—the library only requires
non-selfness on positive-rate channels—but is often the simplest condition for
concrete deterministic reset families. -/
theorem davisResetRegular_of_ne (S : SHS Q n m)
    (hmeas : ∀ ℓ : Fin m, Measurable (S.resetDavisState ℓ))
    (hne : ∀ ℓ z, S.resetDavisState ℓ z ≠ z) :
    DavisResetRegular S := by
  refine ⟨hmeas, fun ℓ z hint => hne ℓ z⟩

/-- A reset that changes the discrete mode on every active channel is regular,
provided its full augmented-state map is measurable. -/
theorem davisResetRegular_of_mode_change (S : SHS Q n m)
    (hmeas : ∀ ℓ : Fin m, Measurable (S.resetDavisState ℓ))
    (hmode : ∀ ℓ q x t,
      0 < S.intensity ℓ q x t → S.phi_q ℓ q x t ≠ q) :
    DavisResetRegular S := by
  refine ⟨hmeas, fun ℓ z hint => ?_⟩
  simp only [resetDavisState]
  intro heq
  have : S.phi_q ℓ z.1 z.2.1 z.2.2 = z.1 := congr_arg Prod.fst heq
  exact hmode ℓ z.1 z.2.1 z.2.2 hint this

/-- A reset that changes the continuous state on every active channel is
regular, provided its full augmented-state map is measurable. -/
theorem davisResetRegular_of_continuous_change (S : SHS Q n m)
    (hmeas : ∀ ℓ : Fin m, Measurable (S.resetDavisState ℓ))
    (hstate : ∀ ℓ q x t,
      0 < S.intensity ℓ q x t → S.phi_x ℓ q x t ≠ x) :
    DavisResetRegular S := by
  constructor
  · exact hmeas
  · intro ℓ z hint
    specialize hstate ℓ z.1 z.2.1 z.2.2 hint
    simp only [resetDavisState]
    intro heq
    have : (S.phi_q ℓ z.1 z.2.1 z.2.2, S.phi_x ℓ z.1 z.2.1 z.2.2, z.2.2).2.1 = z.2.1 := congr_arg Prod.fst (congr_arg Prod.snd heq)
    simp at this
    exact hstate this

/-- Componentwise measurability of the two reset coordinates implies
measurability of the time-augmented reset map. -/
theorem resetDavisState_measurable (S : SHS Q n m) (ℓ : Fin m)
    (hq : Measurable (fun z : DavisState Q n =>
      S.phi_q ℓ z.1 z.2.1 z.2.2))
    (hx : Measurable (fun z : DavisState Q n =>
      S.phi_x ℓ z.1 z.2.1 z.2.2)) :
    Measurable (S.resetDavisState ℓ) := by
  simp only [resetDavisState]
  exact Measurable.prodMk hq (Measurable.prodMk hx measurable_snd.snd)

/-- Model-facing reset constructor: componentwise measurable reset coordinates
plus an active discrete-mode change suffice for `DavisResetRegular`. -/
theorem davisResetRegular_of_measurable_mode_change (S : SHS Q n m)
    (hq : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_q ℓ z.1 z.2.1 z.2.2))
    (hx : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_x ℓ z.1 z.2.1 z.2.2))
    (hmode : ∀ ℓ q x t,
      0 < S.intensity ℓ q x t → S.phi_q ℓ q x t ≠ q) :
    DavisResetRegular S := by
  refine ⟨?reset_measurable, ?active_reset_ne⟩
  case reset_measurable =>
    intro ℓ
    simp only [resetDavisState]
    exact Measurable.prodMk (hq ℓ) (Measurable.prodMk (hx ℓ) measurable_snd.snd)
  case active_reset_ne =>
    intro ℓ z hint
    simp only [resetDavisState]
    intro h
    have := hmode ℓ z.1 z.2.1 z.2.2 hint
    exact this (congrArg Prod.fst h)

/-- Model-facing reset constructor: componentwise measurable reset coordinates
plus an active continuous-state change suffice for `DavisResetRegular`. -/
theorem davisResetRegular_of_measurable_continuous_change (S : SHS Q n m)
    (hq : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_q ℓ z.1 z.2.1 z.2.2))
    (hx : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_x ℓ z.1 z.2.1 z.2.2))
    (hstate : ∀ ℓ q x t,
      0 < S.intensity ℓ q x t → S.phi_x ℓ q x t ≠ x) :
    DavisResetRegular S := by
  constructor
  · exact fun ℓ => resetDavisState_measurable S ℓ (hq ℓ) (hx ℓ)
  · intro ℓ z hint
    specialize hstate ℓ z.1 z.2.1 z.2.2 hint
    simp only [resetDavisState]
    intro heq
    have : (S.phi_q ℓ z.1 z.2.1 z.2.2, S.phi_x ℓ z.1 z.2.1 z.2.2, z.2.2).2.1 = z.2.1 := congr_arg Prod.fst (congr_arg Prod.snd heq)
    simp at this
    exact hstate this

/-- Model-facing reset constructor allowing each active transition to change
either coordinate.  Unlike the mode-only and continuous-state-only variants,
the coordinate that changes may depend on the channel and pre-jump state. -/
theorem davisResetRegular_of_measurable_coordinate_change (S : SHS Q n m)
    (hq : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_q ℓ z.1 z.2.1 z.2.2))
    (hx : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_x ℓ z.1 z.2.1 z.2.2))
    (hchange : ∀ ℓ q x t,
      0 < S.intensity ℓ q x t →
        S.phi_q ℓ q x t ≠ q ∨ S.phi_x ℓ q x t ≠ x) :
    DavisResetRegular S := by
  refine ⟨fun ℓ => ?_, fun ℓ z hint => ?_⟩
  · exact resetDavisState_measurable S ℓ (hq ℓ) (hx ℓ)
  · by_contra heq
    have hq_eq : S.phi_q ℓ z.1 z.2.1 z.2.2 = z.1 :=
      congrArg Prod.fst heq
    have hx_eq : S.phi_x ℓ z.1 z.2.1 z.2.2 = z.2.1 :=
      congrArg (fun p => p.2.1) heq
    exact (hchange ℓ z.1 z.2.1 z.2.2 hint).elim
      (fun h => h hq_eq) (fun h => h hx_eq)

/-- An equivalent convenient interface for models with possible identity
resets: every identity reset must have zero rate. -/
theorem davisResetRegular_of_measurable_self_inactive (S : SHS Q n m)
    (hq : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_q ℓ z.1 z.2.1 z.2.2))
    (hx : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_x ℓ z.1 z.2.1 z.2.2))
    (hinactive : ∀ ℓ (z : DavisState Q n),
      S.resetDavisState ℓ z = z →
        S.intensity ℓ z.1 z.2.1 z.2.2 = 0) :
    DavisResetRegular S := by
  constructor
  · exact fun ℓ => resetDavisState_measurable S ℓ (hq ℓ) (hx ℓ)
  · intro ℓ z hint
    exact fun heq => ne_of_gt hint (hinactive ℓ z heq)

/-- End-to-end constructor for the common bounded-rate case.  Componentwise
measurability, an active change in at least one reset coordinate, measurable
intensities, global-flow regularity, and channel bounds are enough to produce a
standard Davis PDP. -/
def toDavisPDPStandardOfMeasurableCoordinateChange (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hflowReg : DavisGlobalFlowRegular S hflow)
    [S.IntensitiesMeasurable]
    (hq : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_q ℓ z.1 z.2.1 z.2.2))
    (hx : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_x ℓ z.1 z.2.1 z.2.2))
    (hchange : ∀ ℓ q x t,
      0 < S.intensity ℓ q x t →
        S.phi_q ℓ q x t ≠ q ∨ S.phi_x ℓ q x t ≠ x)
    (c : Fin m → ℝ≥0)
    (hc : ∀ ℓ (z : DavisState Q n),
      S.intensity ℓ z.1 z.2.1 z.2.2 ≤ c ℓ) :
    Davis.PDPStandard (DavisState Q n) :=
  toDavisPDPStandardOfChannelBounds S hflow hflowReg
    (davisResetRegular_of_measurable_coordinate_change S hq hx hchange) c hc

/-- The end-to-end coordinate-change constructor preserves exactly the original
SHS flow, total rate, and weighted reset compensator. -/
theorem toDavisPDPStandardOfMeasurableCoordinateChange_compatible
    (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hflowReg : DavisGlobalFlowRegular S hflow)
    [S.IntensitiesMeasurable]
    (hq : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_q ℓ z.1 z.2.1 z.2.2))
    (hx : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_x ℓ z.1 z.2.1 z.2.2))
    (hchange : ∀ ℓ q x t,
      0 < S.intensity ℓ q x t →
        S.phi_q ℓ q x t ≠ q ∨ S.phi_x ℓ q x t ≠ x)
    (c : Fin m → ℝ≥0)
    (hc : ∀ ℓ (z : DavisState Q n),
      S.intensity ℓ z.1 z.2.1 z.2.2 ≤ c ℓ) :
    DavisCompatible S hflow
      (toDavisPDPStandardOfMeasurableCoordinateChange S hflow hflowReg
        hq hx hchange c hc).toPDP := by
  exact toDavisPDPStandardOfChannelBounds_compatible S hflow hflowReg
    (davisResetRegular_of_measurable_coordinate_change S hq hx hchange) c hc


/-! ## Pathwise jump-time recursion

The following definitions isolate the deterministic recursion underlying the
canonical Davis construction.  Probability laws for the holding times and
marks can be added separately; all clock and flow bookkeeping is already
forced by this pathwise layer. -/

/-- Exogenous holding times and channel marks used by the pathwise jump
recursion.  In a probabilistic construction these are sampled from the
integrated hazard and normalized marked-reset kernel, respectively. -/
structure DavisJumpNoise (m : ℕ) (Ω : Type*) where
  holdingTime : ℕ → Ω → ℝ≥0
  channel : ℕ → Ω → Fin m

/-- Cumulative elapsed jump time: `jumpTime k` is the sum of the first `k`
holding times. -/
def DavisJumpNoise.jumpTime {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) : ℕ → Ω → ℝ≥0
  | 0, _ => 0
  | k + 1, ω => ξ.jumpTime k ω + ξ.holdingTime k ω

@[simp] theorem DavisJumpNoise.jumpTime_zero {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (ω : Ω) : ξ.jumpTime 0 ω = 0 := rfl

@[simp] theorem DavisJumpNoise.jumpTime_succ {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (k : ℕ) (ω : Ω) :
    ξ.jumpTime (k + 1) ω = ξ.jumpTime k ω + ξ.holdingTime k ω := rfl

/-- The post-jump chain generated by deterministic flow for the sampled
holding time followed by the sampled SHS reset channel. -/
def davisStateAfterJump (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n) :
    ℕ → Ω → DavisState Q n
  | 0, _ => initial
  | k + 1, ω =>
      S.resetDavisState (ξ.channel k ω)
        (davisFlow S hflow (ξ.holdingTime k ω)
          (davisStateAfterJump S hflow ξ initial k ω))

/-- State immediately before the `k`-th reset. -/
def davisStateBeforeJump (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) (ω : Ω) : DavisState Q n :=
  davisFlow S hflow (ξ.holdingTime k ω)
    (davisStateAfterJump S hflow ξ initial k ω)

@[simp] theorem davisStateAfterJump_zero (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (ω : Ω) :
    davisStateAfterJump S hflow ξ initial 0 ω = initial := rfl

@[simp] theorem davisStateAfterJump_succ (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (k : ℕ) (ω : Ω) :
    davisStateAfterJump S hflow ξ initial (k + 1) ω =
      S.resetDavisState (ξ.channel k ω)
        (davisStateBeforeJump S hflow ξ initial k ω) := rfl

/-- Jump times are monotone along every noise realization. -/
theorem DavisJumpNoise.jumpTime_mono {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (ω : Ω) :
    Monotone (fun k => ξ.jumpTime k ω) := by
  intro k l hkl
  induction hkl with
  | refl => rfl
  | step _ ih =>
      simp only [jumpTime_succ]
      exact le_add_of_le_of_nonneg ih (zero_le _)

/-- The absolute clock of the post-jump state is the initial clock plus the
cumulative elapsed jump time.  This is the key invariant needed to turn the
homogeneous Davis process back into an absolute-time SHS process. -/
theorem davisStateAfterJump_clock (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (k : ℕ) (ω : Ω) :
    (davisStateAfterJump S hflow ξ initial k ω).2.2 =
      initial.2.2 + (ξ.jumpTime k ω : ℝ) := by
  induction k with
  | zero => simp [davisStateAfterJump, DavisJumpNoise.jumpTime]
  | succ k ih =>
    simp [davisStateAfterJump, davisFlow, resetDavisState, ih,
      DavisJumpNoise.jumpTime_succ]
    ring

/-- The pre-jump state's clock is the initial clock plus the next cumulative
jump time. -/
theorem davisStateBeforeJump_clock (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (k : ℕ) (ω : Ω) :
    (davisStateBeforeJump S hflow ξ initial k ω).2.2 =
      initial.2.2 + (ξ.jumpTime (k + 1) ω : ℝ) := by
  conv_lhs => rw [davisStateBeforeJump, davisFlow]
  simp [davisStateAfterJump_clock]
  ring


/-- The `k`-th deterministic segment, clamped at its sampled holding time.  At
`u = 0` it is the `k`-th post-jump state; once `u` reaches the holding time it
is the corresponding pre-jump state. -/
def davisJumpSegment (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) (u : ℝ≥0) (ω : Ω) : DavisState Q n :=
  davisFlow S hflow (min u (ξ.holdingTime k ω))
    (davisStateAfterJump S hflow ξ initial k ω)

@[simp] theorem davisJumpSegment_zero (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (k : ℕ) (ω : Ω) :
    davisJumpSegment S hflow ξ initial k 0 ω =
      davisStateAfterJump S hflow ξ initial k ω := by
  simp [davisJumpSegment, davisFlow, hflow.flow_init]

@[simp] theorem davisJumpSegment_holdingTime (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (k : ℕ) (ω : Ω) :
    davisJumpSegment S hflow ξ initial k (ξ.holdingTime k ω) ω =
      davisStateBeforeJump S hflow ξ initial k ω := by
  simp [davisJumpSegment, davisStateBeforeJump]

/-- Clock invariant inside a clamped deterministic segment. -/
theorem davisJumpSegment_clock (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (k : ℕ) (u : ℝ≥0) (ω : Ω) :
    (davisJumpSegment S hflow ξ initial k u ω).2.2 =
      initial.2.2 +
        ((ξ.jumpTime k ω : ℝ) + (min u (ξ.holdingTime k ω) : ℝ)) := by
  rw [davisJumpSegment, davisFlow]
  rw [davisStateAfterJump_clock]
  simp only [NNReal.coe_min]
  ring

/-! ## Active segment and assembled path

A pathwise non-explosion assumption makes the cumulative jump times tend to
infinity.  It therefore selects a least inter-jump segment containing every
finite elapsed time.  This section assembles the segment recursion above into
a total path, without yet imposing probability laws on the noise. -/

/-- Pathwise non-explosion of abstract jump noise: cumulative elapsed jump
times eventually exceed every finite elapsed time. -/
def DavisJumpNoise.NonExplosive {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) : Prop :=
  ∀ ω, Filter.Tendsto (fun k => ξ.jumpTime k ω) Filter.atTop Filter.atTop

/-- The least segment whose right endpoint lies strictly after `t`.  Using a
strict right endpoint gives a right-continuous convention at jump times: when
`t` equals a cumulative jump time, the selected segment is the post-jump one. -/
noncomputable def DavisJumpNoise.activeSegmentIndex {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (t : ℝ≥0) (ω : Ω) : ℕ :=
  Nat.find (by
    have hev := (hne ω).eventually (Filter.eventually_gt_atTop t)
    rcases hev.exists with ⟨j, hj⟩
    exact ⟨j, hj⟩) - 1

/-- The selected segment begins no later than the requested elapsed time. -/
theorem DavisJumpNoise.jumpTime_activeSegmentIndex_le {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (t : ℝ≥0) (ω : Ω) :
    ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω ≤ t := by
  have hex : ∃ j, t < ξ.jumpTime j ω := by
    have hev := (hne ω).eventually (Filter.eventually_gt_atTop t)
    rcases hev.exists with ⟨j, hj⟩
    exact ⟨j, hj⟩
  have hneg0 : ¬ (t < ξ.jumpTime 0 ω) := by simp
  have hpos : 0 < Nat.find hex := by rwa [Nat.find_pos]
  have hlt : ξ.activeSegmentIndex hne t ω < Nat.find hex := by
    simp [DavisJumpNoise.activeSegmentIndex, hpos]
  exact le_of_not_gt (Nat.find_min hex hlt)

/-- The requested elapsed time lies strictly before the selected segment's
right endpoint. -/
theorem DavisJumpNoise.lt_jumpTime_activeSegmentIndex_succ
    {m : ℕ} {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (hne : ξ.NonExplosive) (t : ℝ≥0) (ω : Ω) :
    t < ξ.jumpTime (ξ.activeSegmentIndex hne t ω + 1) ω := by
  unfold DavisJumpNoise.activeSegmentIndex
  set k := Nat.find (show ∃ j, t < ξ.jumpTime j ω from by
    have hev := (hne ω).eventually (Filter.eventually_gt_atTop t)
    exact hev.exists) with hk
  have hp_k : t < ξ.jumpTime k ω := Nat.find_spec (by
    have hev := (hne ω).eventually (Filter.eventually_gt_atTop t)
    exact hev.exists)
  -- k ≥ 1 because jumpTime 0 = 0 and t ≥ 0
  have hk_pos : k ≥ 1 := by
    by_contra hk_zero
    have : k = 0 := Nat.eq_zero_of_not_pos hk_zero
    simp [this, jumpTime_zero] at hp_k
  simp [Nat.sub_add_cancel hk_pos]
  exact hp_k

/-- Time elapsed inside the active segment is bounded by its holding time. -/
theorem DavisJumpNoise.activeSegmentElapsed_le_holdingTime
    {m : ℕ} {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (hne : ξ.NonExplosive) (t : ℝ≥0) (ω : Ω) :
    t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω ≤
      ξ.holdingTime (ξ.activeSegmentIndex hne t ω) ω := by
  have hlt := ξ.lt_jumpTime_activeSegmentIndex_succ hne t ω
  rw [DavisJumpNoise.jumpTime_succ] at hlt
  rw [tsub_le_iff_right]
  simpa [add_comm] using hlt.le

/-- Total path assembled from the recursively generated deterministic
segments.  At a jump time this chooses the post-jump endpoint of the next
segment. -/
noncomputable def davisJumpPath (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) : DavisState Q n :=
  let k := ξ.activeSegmentIndex hne t ω
  davisJumpSegment S hflow ξ initial k (t - ξ.jumpTime k ω) ω

/-- Every holding time is strictly positive.  This excludes cascades of
instantaneous resets, and in particular ensures that elapsed time zero belongs
to the initial segment. -/
def DavisJumpNoise.PositiveHoldingTimes {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) : Prop :=
  ∀ k ω, 0 < ξ.holdingTime k ω

/-- With positive holding times, the assembled path starts at the supplied
augmented state. -/
@[simp] theorem davisJumpPath_zero (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (hne : ξ.NonExplosive) (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) (ω : Ω) :
    davisJumpPath S hflow ξ hne initial 0 ω = initial := by
  have hex : ∃ j, (0 : ℝ≥0) < ξ.jumpTime j ω := by
    exact ⟨1, by simpa using hpos 0 ω⟩
  have hfind : Nat.find hex = 1 := (Nat.find_eq_iff hex).2 ⟨by
    simpa using hpos 0 ω, by
      intro j hj
      have : j = 0 := by omega
      simp [this]⟩
  have hindex : ξ.activeSegmentIndex hne 0 ω = 0 := by
    unfold DavisJumpNoise.activeSegmentIndex
    rw [show Nat.find _ = 1 from hfind]
  simp [davisJumpPath, hindex]

/-- The augmented clock of the assembled path is exactly initial absolute time
plus elapsed Davis time. -/
theorem davisJumpPath_clock (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (hne : ξ.NonExplosive) (initial : DavisState Q n)
    (t : ℝ≥0) (ω : Ω) :
    (davisJumpPath S hflow ξ hne initial t ω).2.2 =
      initial.2.2 + (t : ℝ) := by
  rw [davisJumpPath, davisJumpSegment_clock]
  have hle := ξ.jumpTime_activeSegmentIndex_le hne t ω
  rw [min_eq_left]
  · rw [NNReal.coe_sub hle]
    ring
  · exact_mod_cast ξ.activeSegmentElapsed_le_holdingTime hne t ω

/-! ## Measurability of the finite recursion

The pathwise recursion becomes usable as a stochastic process once its noise
coordinates are measurable.  The results in this section deliberately concern
a fixed finite jump index (and, for the assembled path, a fixed elapsed time),
so they do not require any independence or distributional assumptions.
-/

/-- Coordinatewise measurability of holding times and channel marks. -/
structure DavisJumpNoise.MeasurableNoise {m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω) : Prop where
  holdingTime : ∀ k, Measurable (ξ.holdingTime k)
  channel : ∀ k, Measurable (ξ.channel k)

/-- Every finite cumulative jump time is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.jumpTime
    {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) (k : ℕ) :
    Measurable (ξ.jumpTime k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    show Measurable fun ω => ξ.jumpTime k ω + ξ.holdingTime k ω
    exact Measurable.add ih (hξ.holdingTime k)

/-- Every finite post-jump state in the recursive chain is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.stateAfterJump
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k : ℕ) :
    Measurable (davisStateAfterJump S hflow ξ initial k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    show Measurable (fun ω => S.resetDavisState (ξ.channel k ω) (davisFlow S hflow (ξ.holdingTime k ω) (davisStateAfterJump S hflow ξ initial k ω)))
    have h1 : Measurable (fun ω => (ξ.holdingTime k ω, davisStateAfterJump S hflow ξ initial k ω)) :=
      Measurable.prodMk (hξ.holdingTime k) ih
    have h2 : Measurable (fun ω => (ξ.channel k ω, (ξ.holdingTime k ω, davisStateAfterJump S hflow ξ initial k ω))) :=
      Measurable.prodMk (hξ.channel k) h1
    have hflow_meas : Measurable (fun p : ℝ≥0 × DavisState Q n => davisFlow S hflow p.1 p.2) := hf.measurable_joint
    have hF : ∀ ℓ : Fin m, Measurable (fun p : ℝ≥0 × DavisState Q n => S.resetDavisState ℓ (davisFlow S hflow p.1 p.2)) :=
      fun ℓ => (hr.reset_measurable ℓ).comp hflow_meas
    have hF_meas : Measurable (fun (x : Fin m × ℝ≥0 × DavisState Q n) => S.resetDavisState x.1 (davisFlow S hflow x.2.1 x.2.2)) := by
      intro s hs
      have : (fun x : Fin m × ℝ≥0 × DavisState Q n => S.resetDavisState x.1 (davisFlow S hflow x.2.1 x.2.2)) ⁻¹' s = 
             ⋃ ℓ : Fin m, {x : Fin m × ℝ≥0 × DavisState Q n | x.1 = ℓ} ∩ 
                          (fun x : Fin m × ℝ≥0 × DavisState Q n => S.resetDavisState x.1 (davisFlow S hflow x.2.1 x.2.2)) ⁻¹' s := by
        ext x; simp
      rw [this]
      apply MeasurableSet.iUnion
      intro ℓ
      set t := (fun p : ℝ≥0 × DavisState Q n => S.resetDavisState ℓ (davisFlow S hflow p.1 p.2)) ⁻¹' s with ht_def
      have hset : {x : Fin m × ℝ≥0 × DavisState Q n | x.1 = ℓ} ∩ 
              (fun x : Fin m × ℝ≥0 × DavisState Q n => S.resetDavisState x.1 (davisFlow S hflow x.2.1 x.2.2)) ⁻¹' s = 
              {ℓ} ×ˢ t := by
        ext ⟨a, b⟩
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
        constructor <;> intro h <;> rcases h with ⟨ha, hb⟩ <;> simp_all
      rw [hset]
      exact MeasurableSet.prod (measurableSet_singleton ℓ) (hF ℓ hs)
    exact hF_meas.comp h2

/-- Every finite pre-jump state is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.stateBeforeJump
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k : ℕ) :
    Measurable (davisStateBeforeJump S hflow ξ initial k) := by
  exact hf.measurable_joint.comp
    ((hξ.holdingTime k).prodMk
      (hξ.stateAfterJump S hflow hf hr initial k))

/-- A finite clamped inter-jump segment is measurable in the noise sample. -/
theorem DavisJumpNoise.MeasurableNoise.jumpSegment
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k : ℕ) (u : ℝ≥0) :
    Measurable (fun ω => davisJumpSegment S hflow ξ initial k u ω) := by
  change Measurable (fun ω => davisFlow S hflow
    (min u (ξ.holdingTime k ω))
    (davisStateAfterJump S hflow ξ initial k ω))
  exact hf.measurable_joint.comp
    ((measurable_const.min (hξ.holdingTime k)).prodMk
      (hξ.stateAfterJump S hflow hf hr initial k))

/-- At each fixed elapsed time, the active segment index is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.activeSegmentIndex
    {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (hne : ξ.NonExplosive) (t : ℝ≥0) :
    Measurable (fun ω => ξ.activeSegmentIndex hne t ω) := by
  -- First prove jumpTime k is measurable for all k
  have hjumpTime : ∀ k, Measurable (ξ.jumpTime k) := by
    intro k
    induction k with
    | zero => exact measurable_const
    | succ k ih =>
        have : ξ.jumpTime (k + 1) = fun ω => ξ.jumpTime k ω + ξ.holdingTime k ω := by
          ext ω; rfl
        rw [this]; exact ih.add (hξ.holdingTime k)
  -- activeSegmentIndex ω = n iff jumpTime n ω ≤ t < jumpTime (n+1) ω
  -- We show the preimage of each singleton is measurable
  have key : ∀ n : ℕ, MeasurableSet {ω | ξ.activeSegmentIndex hne t ω = n} := by
    intro n
    -- {ω | activeSegmentIndex ω = n} = {ω | jumpTime n ω ≤ t} ∩ {ω | t < jumpTime (n+1) ω}
    have heq : {ω | ξ.activeSegmentIndex hne t ω = n} =
        {ω | ξ.jumpTime n ω ≤ t} ∩ {ω | t < ξ.jumpTime (n + 1) ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hidx
        exact ⟨by rw [← hidx]; exact ξ.jumpTime_activeSegmentIndex_le hne t ω,
               by rw [← hidx]; exact ξ.lt_jumpTime_activeSegmentIndex_succ hne t ω⟩
      · intro ⟨hle, hlt⟩
        -- We have jumpTime n ω ≤ t < jumpTime (n+1) ω
        -- Need to show activeSegmentIndex ω = n
        -- i.e., Nat.find hex - 1 = n, i.e., Nat.find hex = n + 1
        apply Nat.sub_eq_of_eq_add
        exact (Nat.find_eq_iff _).2 ⟨hlt, fun j hj => fun h =>
          not_lt.mpr (le_trans (ξ.jumpTime_mono ω (Nat.le_of_lt_succ hj)) hle) h⟩
    rw [heq]
    apply MeasurableSet.inter
    · change MeasurableSet (ξ.jumpTime n ⁻¹' {x | x ≤ t})
      exact measurableSet_Iic.preimage (hjumpTime n)
    · change MeasurableSet (ξ.jumpTime (n + 1) ⁻¹' {x | t < x})
      exact measurableSet_Ioi.preimage (hjumpTime (n + 1))
  intro s hs
  -- s⁻¹' (fun ω => f ω) = ⋃_{n ∈ s} {ω | f ω = n}
  have heq : (fun ω => ξ.activeSegmentIndex hne t ω) ⁻¹' s =
      ⋃ n ∈ s, {ω | ξ.activeSegmentIndex hne t ω = n} := by
    ext ω
    simp [Set.mem_preimage, Set.mem_iUnion]
  rw [heq]
  refine MeasurableSet.iUnion (fun n : ℕ => ?_)
  by_cases h : n ∈ s <;> simp_all

/-- At each fixed elapsed time, the assembled jump path is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.jumpPath
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) :
    Measurable (fun ω => davisJumpPath S hflow ξ hne initial t ω) := by
  let index : Ω → ℕ := fun ω => ξ.activeSegmentIndex hne t ω
  have hindex : Measurable index := hξ.activeSegmentIndex hne t
  have hbranch : ∀ k, Measurable (fun ω =>
      davisJumpSegment S hflow ξ initial k (t - ξ.jumpTime k ω) ω) := by
    intro k
    change Measurable (fun ω => davisFlow S hflow
      (min (t - ξ.jumpTime k ω) (ξ.holdingTime k ω))
      (davisStateAfterJump S hflow ξ initial k ω))
    exact hf.measurable_joint.comp
      (((measurable_const.sub (hξ.jumpTime k)).min (hξ.holdingTime k)).prodMk
        (hξ.stateAfterJump S hflow hf hr initial k))
  have hp : ∀ k, MeasurableSet {ω | index ω = k} := fun k =>
    measurableSet_eq_fun hindex measurable_const
  have hex : ∀ ω, ∃ k, index ω = k := fun ω => ⟨index ω, rfl⟩
  have hfind := Measurable.find hbranch hp hex
  convert hfind using 1
  funext ω
  have hleast : Nat.find (hex ω) = index ω := by
    exact (Nat.find_eq_iff (hex ω)).2 ⟨rfl, by
      intro j hj h
      subst h
      exact (Nat.lt_irrefl _ hj).elim⟩
  rw [hleast]
  rfl

end SHS
