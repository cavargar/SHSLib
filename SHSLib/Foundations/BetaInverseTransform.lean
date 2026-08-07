/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The inverse-transform theorem for the Beta law

If `U` is uniform on `[0,1]` then `Q(U)` has the Beta law, where `Q` is the
Beta quantile function of batch 174.  This module proves that as an identity of
measures on `ℝ`:

  `Measure.map (betaQuantile a b) (volume.restrict (Icc 0 1)) = betaMeasure a b`.

The two ingredients are batch 175's adjunction `Q(p) ≤ x ↔ p ≤ I_x(a,b)`, which
computes the preimage `Q⁻¹(-∞, x] ∩ [0,1] = [0, I_x(a,b)]`, and batch 177's CDF
identity `betaMeasure a b (Iic x) = ofReal (I_x(a,b))`.  Two finite Borel
measures on `ℝ` that agree on every `Iic x` are equal, so the two computations
suffice.

Along the way the module records the junk values of the quantile outside
`[0,1]` and the resulting global measurability of `betaQuantile a b`.
-/
import SHSLib.Foundations.BetaMeasure

open Real Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SHSLib.Trigamma

/-- Outside `[0,1]` the quantile takes its junk value `0`. -/
theorem betaQuantile_eq_zero_of_notMem {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {p : ℝ}
    (hp : p ∉ Set.Icc (0:ℝ) 1) : betaQuantile a b p = 0 := by
  classical
  have hnex : ¬ ∃ x, x ∈ Set.Icc (0:ℝ) 1 ∧ regBetaFn a b x = p := by
    rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    exact hp (regBetaFn_mem_Icc ha hb hx0 hx1)
  simp only [betaQuantile, dif_neg hnex]

/-- The quantile precomposed with the clamp `p ↦ max 0 (min 1 p)`; this is a
globally continuous function agreeing with the quantile on `[0,1]`. -/
noncomputable def betaQuantileClamp (a b p : ℝ) : ℝ :=
  betaQuantile a b (max 0 (min 1 p))

theorem continuous_betaQuantileClamp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous (betaQuantileClamp a b) := by
  have hmaps : ∀ p : ℝ, max 0 (min 1 p) ∈ Set.Icc (0:ℝ) 1 := by
    intro p
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (min_le_left _ _)
  exact (continuousOn_betaQuantile ha hb).comp_continuous
    (continuous_const.max (continuous_const.min continuous_id)) hmaps

theorem betaQuantileClamp_eq_of_mem {a b p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    betaQuantileClamp a b p = betaQuantile a b p := by
  obtain ⟨hp0, hp1⟩ := hp
  rw [betaQuantileClamp, min_eq_right hp1, max_eq_right hp0]

/-- The quantile function is Borel measurable on all of `ℝ`. -/
theorem measurable_betaQuantile {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Measurable (betaQuantile a b) := by
  classical
  have hpw : betaQuantile a b
      = Set.piecewise (Set.Icc (0:ℝ) 1) (betaQuantileClamp a b) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ Set.Icc (0:ℝ) 1
    · rw [Set.piecewise_eq_of_mem _ _ _ hp, betaQuantileClamp_eq_of_mem hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp, betaQuantile_eq_zero_of_notMem ha hb hp]
  rw [hpw]
  exact Measurable.piecewise measurableSet_Icc
    (continuous_betaQuantileClamp ha hb).measurable measurable_const

/-- **The preimage computation.**  For `x ∈ [0,1]`, the uniform points `p` with
`Q(p) ≤ x` are exactly `[0, I_x(a,b)]`. -/
theorem preimage_betaQuantile_Iic_inter {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    betaQuantile a b ⁻¹' Set.Iic x ∩ Set.Icc (0:ℝ) 1
      = Set.Icc (0:ℝ) (regBetaFn a b x) := by
  obtain ⟨hI0, hI1⟩ := regBetaFn_mem_Icc ha hb hx0 hx1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Icc]
  constructor
  · rintro ⟨hQ, hp0, hp1⟩
    exact ⟨hp0, (betaQuantile_le_iff ha hb hp0 hp1 hx0 hx1).mp hQ⟩
  · rintro ⟨hp0, hp⟩
    have hp1 : p ≤ 1 := hp.trans hI1
    exact ⟨(betaQuantile_le_iff ha hb hp0 hp1 hx0 hx1).mpr hp, hp0, hp1⟩

/-- Below `0` no uniform point is mapped into `(-∞, x]`. -/
theorem preimage_betaQuantile_Iic_inter_of_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : x < 0) :
    betaQuantile a b ⁻¹' Set.Iic x ∩ Set.Icc (0:ℝ) 1 = ∅ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Icc,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro hQ hp0 hp1
  exact absurd ((betaQuantile_mem_Icc ha hb hp0 hp1).1.trans hQ) (not_le.mpr hx)

/-- Above `1` every uniform point is mapped into `(-∞, x]`. -/
theorem preimage_betaQuantile_Iic_inter_of_one_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : 1 ≤ x) :
    betaQuantile a b ⁻¹' Set.Iic x ∩ Set.Icc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := by
  refine Set.inter_eq_right.mpr ?_
  rintro p ⟨hp0, hp1⟩
  exact ((betaQuantile_mem_Icc ha hb hp0 hp1).2).trans hx

/-- **The inverse-transform theorem**: the pushforward of the uniform law on
`[0,1]` under the Beta quantile function is the Beta law. -/
theorem map_betaQuantile_uniform {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Measure.map (betaQuantile a b) (volume.restrict (Set.Icc (0:ℝ) 1)) = betaMeasure a b := by
  have hQmeas := measurable_betaQuantile ha hb
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  refine MeasureTheory.Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hQmeas measurableSet_Iic,
    Measure.restrict_apply (hQmeas measurableSet_Iic)]
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [preimage_betaQuantile_Iic_inter_of_neg ha hb hx, betaMeasure_Iic_of_nonpos a b hx.le]
    simp
  · subst hx
    rw [preimage_betaQuantile_Iic_inter ha hb le_rfl zero_le_one,
      betaMeasure_Iic ha hb le_rfl zero_le_one, Real.volume_Icc, sub_zero]
  · rcases le_or_gt x 1 with hx1 | hx1
    · rw [preimage_betaQuantile_Iic_inter ha hb hx.le hx1,
        betaMeasure_Iic ha hb hx.le hx1, Real.volume_Icc, sub_zero]
    · rw [preimage_betaQuantile_Iic_inter_of_one_lt ha hb hx1.le,
        betaMeasure_Iic_of_one_le ha hb hx1.le, Real.volume_Icc]
      simp

end SHSLib.Trigamma
