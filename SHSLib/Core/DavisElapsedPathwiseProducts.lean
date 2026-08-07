import SHSLib.Core.DavisElapsedPathwiseTestBound

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Discharging the product hypotheses of the path-level regime

Replacing the uniform bound on the test function by a random path-level bound
left two integrability hypotheses on products: the random test bound times the
completed-jump count, and the random test bound times the accumulated hazard.

This module gives usable sufficient conditions for them.  A uniform bound is
the special case of a constant path-level bound, and then the products reduce
to the one-factor hypotheses of the earlier regimes.  More generally a
deterministically bounded random test bound suffices, and — the genuinely more
general criterion — square integrability of the three factors does, by
Cauchy–Schwarz.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A uniform bound on the test function is a constant path-level bound. -/
theorem DavisPathwiseTestBound.of_uniform
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (C : ℝ) (hgC : ∀ z, |g z| ≤ C) :
    DavisPathwiseTestBound S hflow ξ initial g (fun _ => C) :=
  fun _ _ _ => ⟨hgC _, fun _ => hgC _⟩

/-! ## Constant and bounded test bounds -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- For a deterministically bounded random test bound, the two product
hypotheses follow from integrability of the completed-jump count and of the
accumulated hazard alone. -/
theorem integrable_mul_of_bounded_pathwise_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (G : Ω → ℝ) (K : ℝ)
    (hGmeas : AEStronglyMeasurable G P) (hGK : ∀ ω, |G ω| ≤ K)
    (hcount : ∀ t, Integrable
      (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P) :
    (∀ t, Integrable (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P) ∧
      ∀ t, Integrable (fun ω => G ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have := (hcount t).const_mul K
    apply this.mono'
    · exact (hGmeas.mul (hcount t).aestronglyMeasurable)
    · filter_upwards with ω
      have h1 : |G ω| ≤ K := hGK ω
      have h2 : 0 ≤ (ξ.activeSegmentIndex hne t ω : ℝ) := Nat.cast_nonneg _
      calc |G ω * (ξ.activeSegmentIndex hne t ω : ℝ)|
          = |G ω| * |(ξ.activeSegmentIndex hne t ω : ℝ)| := abs_mul _ _
        _ = |G ω| * (ξ.activeSegmentIndex hne t ω : ℝ) := by rw [abs_of_nonneg h2]
        _ ≤ K * (ξ.activeSegmentIndex hne t ω : ℝ) := by gcongr
  · have := (hhazard t).const_mul K
    apply this.mono'
    · exact (hGmeas.mul ((hhazard t).aestronglyMeasurable))
    · filter_upwards with ω
      have h2 : 0 ≤ S.davisElapsedAccumulatedHazard hflow ξ hne initial t ω := by
        exact (davisElapsedAccumulatedHazard_nonneg S hflow ξ hne initial t ω)
      calc ‖G ω * S.davisElapsedAccumulatedHazard hflow ξ hne initial t ω‖
          = |G ω| * |S.davisElapsedAccumulatedHazard hflow ξ hne initial t ω| := by rw [Real.norm_eq_abs, abs_mul]
        _ = |G ω| * S.davisElapsedAccumulatedHazard hflow ξ hne initial t ω := by rw [abs_of_nonneg h2]
        _ ≤ K * S.davisElapsedAccumulatedHazard hflow ξ hne initial t ω := by gcongr; exact hGK ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- For a constant path-level bound the products are integrable exactly when
the completed-jump count and the accumulated hazard are. -/
theorem integrable_mul_of_const_pathwise_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (C : ℝ)
    (hcount : ∀ t, Integrable
      (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P)
    (hhazard : ∀ t, Integrable
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) P) :
    (∀ t, Integrable
        (fun ω => (fun _ : Ω => C) ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P) ∧
      ∀ t, Integrable (fun ω => (fun _ : Ω => C) ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P :=
  ⟨fun t => (hcount t).const_mul C, fun t => (hhazard t).const_mul C⟩

/-! ## Square integrability -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Cauchy–Schwarz form: square integrability of the random test bound, of the
completed-jump count, and of the accumulated hazard gives the two product
hypotheses. -/
theorem integrable_mul_of_memLp_two_pathwise_bound
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (G : Ω → ℝ)
    (hG2 : MemLp G 2 P)
    (hcount2 : ∀ t, MemLp (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) 2 P)
    (hhazard2 : ∀ t, MemLp
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) 2 P) :
    (∀ t, Integrable (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) P) ∧
      ∀ t, Integrable (fun ω => G ω *
        davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) P := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hpqr : ENNReal.HolderTriple 2 2 1 := ⟨by
      calc (2 : ENNReal)⁻¹ + 2⁻¹ = (2 : ENNReal)⁻¹ * 2 := by ring
        _ = 1 := by rw [mul_comm, ← div_eq_mul_inv, ENNReal.div_self] <;> norm_num
        _ = 1⁻¹ := by rw [inv_one]⟩
    have h : MemLp (fun ω => G ω * (ξ.activeSegmentIndex hne t ω : ℝ)) 1 P :=
      MemLp.mul (p := 2) (q := 2) (r := 1) (hpqr := hpqr) (hcount2 t) hG2
    exact MeasureTheory.memLp_one_iff_integrable.mp h
  · have hpqr : ENNReal.HolderTriple 2 2 1 := ⟨by
      calc (2 : ENNReal)⁻¹ + 2⁻¹ = (2 : ENNReal)⁻¹ * 2 := by ring
        _ = 1 := by rw [mul_comm, ← div_eq_mul_inv, ENNReal.div_self] <;> norm_num
        _ = 1⁻¹ := by rw [inv_one]⟩
    have h : MemLp (fun ω => G ω * davisElapsedAccumulatedHazard S hflow ξ hne initial t ω) 1 P :=
      MemLp.mul (p := 2) (q := 2) (r := 1) (hpqr := hpqr) (hhazard2 t) hG2
    exact MeasureTheory.memLp_one_iff_integrable.mp h
/-! ## The resulting martingale statements -/

/-- Martingale property for a square-integrable path-level test bound. -/
theorem DavisStoppedElapsedOccupationIncrementLaw.martingale_of_pathwise_bound_memLp
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    {hne : ξ.NonExplosive} (initial : DavisState Q n) (hg : Measurable g)
    (G : Ω → ℝ) (hG : DavisPathwiseTestBound S hflow ξ initial g G)
    (hG2 : MemLp G 2 P)
    (hcount2 : ∀ t, MemLp (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) 2 P)
    (hhazard2 : ∀ t, MemLp
      (davisElapsedAccumulatedHazard S hflow ξ hne initial t) 2 P)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw
      S hflow P ξ.fullFiltration ξ hne initial g) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess
        S hflow ξ hne initial g) ξ.fullFiltration P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale_of_pathwise_bound
    Q _ _ n m S hflow hf hr g hreg hcont Ω _ P _ ξ hξ hne initial hg G hG
    (integrable_mul_of_memLp_two_pathwise_bound
      S hflow P ξ hne initial G hG2 hcount2 hhazard2).1
    (integrable_mul_of_memLp_two_pathwise_bound
      S hflow P ξ hne initial G hG2 hcount2 hhazard2).2 hlaw

end SHS
