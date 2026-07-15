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
  add : ∀ s t : ℝ≥0, ∀ z, davisFlow S hflow (s + t) z =
    davisFlow S hflow s (davisFlow S hflow t z)

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

/-- Package the concrete PDP under Davis's standard hypotheses. -/
def toDavisPDPStandard (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr) :
    Davis.PDPStandard (DavisState Q n) where
  toPDP := toDavisPDP S hflow hf hr
  jumpRate_locally_integrable := hli.jumpRate
  nonExplosive := hne

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

end SHS