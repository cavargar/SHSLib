/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The law of a uniform order statistic is the Beta law

Batch 187 computed the distribution *function* of the `(j+1)`-st order
statistic of `n = j+m+1` independent uniforms on `[0,1]`: it is the regularised
incomplete Beta function `I_x(j+1, m+1)`.  This module upgrades that to an
identity of measures,

  `Measure.map (order statistic) (unifPi n) = betaMeasure (j+1) (m+1)`,

by checking the two remaining ranges of the argument — below `0` the order
statistic is almost surely larger, above `1` it is almost surely smaller — and
appealing to the fact that a finite Borel measure on `ℝ` is determined by its
values on the half-lines `(-∞, a]`.
-/
import SHSLib.Foundations.UniformOrderStatistic

open MeasureTheory Set ENNReal

namespace SHSLib.Trigamma

/-! ### One-dimensional marginals of the product measure -/

theorem unifPi_coord_Iic (n : ℕ) (x : ℝ) (i : Fin n) :
    unifPi n {w : Fin n → ℝ | w i ≤ x} = unifIcc (Set.Iic x) := by
  have hset : {w : Fin n → ℝ | w i ≤ x}
      = Set.univ.pi (fun k => if k = i then Set.Iic x else Set.univ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h k
      by_cases hk : k = i
      · subst hk; simpa using h
      · simp [hk]
    · intro h
      have := h i
      simpa using this
  rw [hset, unifPi, Measure.pi_pi]
  simp only [apply_ite unifIcc, measure_univ, Finset.prod_ite_eq' Finset.univ i]
  simp

theorem unifPi_coord_Ioi (n : ℕ) (x : ℝ) (i : Fin n) :
    unifPi n {w : Fin n → ℝ | x < w i} = unifIcc (Set.Ioi x) := by
  have hset : {w : Fin n → ℝ | x < w i}
      = Set.univ.pi (fun k => if k = i then Set.Ioi x else Set.univ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h k
      by_cases hk : k = i
      · subst hk; simpa using h
      · simp [hk]
    · intro h
      have := h i
      simpa using this
  rw [hset, unifPi, Measure.pi_pi]
  simp only [apply_ite unifIcc, measure_univ, Finset.prod_ite_eq' Finset.univ i]
  simp

/-! ### Measurability of the order statistic -/

theorem orderStat_preimage_Iic (n : ℕ) (x : ℝ) (j : Fin n) :
    (fun w : Fin n → ℝ => orderStat n w j) ⁻¹' (Set.Iic x)
      = (belowCount n x) ⁻¹' {i : Fin (n + 1) | (j : ℕ) + 1 ≤ (i : ℕ)} := by
  ext w
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, belowCount]
  exact orderStat_le_iff n x w j

theorem measurableSet_orderStat_le (n : ℕ) (x : ℝ) (j : Fin n) :
    MeasurableSet ((fun w : Fin n → ℝ => orderStat n w j) ⁻¹' (Set.Iic x)) := by
  rw [orderStat_preimage_Iic]
  exact (measurable_belowCount n x) MeasurableSet.of_discrete

theorem measurable_orderStat (n : ℕ) (j : Fin n) :
    Measurable (fun w : Fin n → ℝ => orderStat n w j) :=
  measurable_of_Iic (fun x => measurableSet_orderStat_le n x j)

/-! ### The two degenerate ranges -/

/-- Below `0` the order statistic almost surely fails to be small. -/
theorem measure_orderStat_le_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) (j : Fin n) :
    unifPi n {w : Fin n → ℝ | orderStat n w j ≤ x} = 0 := by
  have hsub : {w : Fin n → ℝ | orderStat n w j ≤ x}
      ⊆ ⋃ i : Fin n, {w : Fin n → ℝ | w i ≤ x} := by
    intro w hw
    have hcard : (j : ℕ) + 1 ≤ (belowSet n x w).card := (orderStat_le_iff n x w j).mp hw
    have hne : (belowSet n x w).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hne
    exact Set.mem_iUnion.mpr ⟨i, mem_belowSet.mp hi⟩
  have hzero : ∀ i : Fin n, unifPi n {w : Fin n → ℝ | w i ≤ x} = 0 := by
    intro i
    rw [unifPi_coord_Iic, unifIcc_Iic (by linarith), ENNReal.ofReal_eq_zero]
    exact hx
  refine le_antisymm ?_ (zero_le _)
  calc unifPi n {w : Fin n → ℝ | orderStat n w j ≤ x}
      ≤ unifPi n (⋃ i : Fin n, {w : Fin n → ℝ | w i ≤ x}) := measure_mono hsub
    _ ≤ ∑' i : Fin n, unifPi n {w : Fin n → ℝ | w i ≤ x} := measure_iUnion_le _
    _ = 0 := by simp [hzero]

/-- Above `1` the order statistic is almost surely small. -/
theorem measure_orderStat_le_of_one_le (n : ℕ) {x : ℝ} (hx : 1 ≤ x) (j : Fin n) :
    unifPi n {w : Fin n → ℝ | orderStat n w j ≤ x} = 1 := by
  have hsub : {w : Fin n → ℝ | orderStat n w j ≤ x}ᶜ
      ⊆ ⋃ i : Fin n, {w : Fin n → ℝ | x < w i} := by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hw
    have hcard : ¬ ((j : ℕ) + 1 ≤ (belowSet n x w).card) := fun h =>
      hw ((orderStat_le_iff n x w j).mpr h)
    have hlt : (belowSet n x w).card < n := by
      have := j.isLt
      omega
    have hne : belowSet n x w ≠ Finset.univ := by
      intro hcon
      rw [hcon] at hlt
      simp at hlt
    obtain ⟨i, hi⟩ : ∃ i, i ∉ belowSet n x w := by
      by_contra hcon
      push_neg at hcon
      exact hne (Finset.eq_univ_iff_forall.mpr hcon)
    exact Set.mem_iUnion.mpr ⟨i, not_le.mp (fun hc => hi (mem_belowSet.mpr hc))⟩
  have hzero : ∀ i : Fin n, unifPi n {w : Fin n → ℝ | x < w i} = 0 := by
    intro i
    rw [unifPi_coord_Ioi, unifIcc_Ioi (by linarith), ENNReal.ofReal_eq_zero]
    linarith
  have hcompl : unifPi n {w : Fin n → ℝ | orderStat n w j ≤ x}ᶜ = 0 := by
    refine le_antisymm ?_ (zero_le _)
    calc unifPi n {w : Fin n → ℝ | orderStat n w j ≤ x}ᶜ
        ≤ unifPi n (⋃ i : Fin n, {w : Fin n → ℝ | x < w i}) := measure_mono hsub
      _ ≤ ∑' i : Fin n, unifPi n {w : Fin n → ℝ | x < w i} := measure_iUnion_le _
      _ = 0 := by simp [hzero]
  have hmeas : MeasurableSet {w : Fin n → ℝ | orderStat n w j ≤ x} :=
    measurableSet_orderStat_le n x j
  have hadd := measure_add_measure_compl (μ := unifPi n) hmeas
  rw [hcompl, add_zero, measure_univ] at hadd
  exact hadd

/-! ### The law -/

/-- **The `(j+1)`-st order statistic of `n = j+m+1` independent uniforms has the
`Beta(j+1, m+1)` law.** -/
theorem map_orderStat (j m : ℕ) :
    (unifPi (j + m + 1)).map
        (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w ⟨j, by omega⟩)
      = betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1) := by
  set jj : Fin (j + m + 1) := ⟨j, by omega⟩ with hjjdef
  have hmeas : Measurable (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w jj) :=
    measurable_orderStat _ jj
  haveI : IsProbabilityMeasure (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    isProbabilityMeasure_betaMeasure (by positivity) (by positivity)
  refine (Measure.ext_of_Iic (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) _ (fun a => ?_)).symm
  rw [Measure.map_apply hmeas measurableSet_Iic]
  have hpre : (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w jj) ⁻¹' Set.Iic a
      = {w : Fin (j + m + 1) → ℝ | orderStat (j + m + 1) w jj ≤ a} := rfl
  rw [hpre]
  rcases le_or_gt a 0 with ha | ha
  · rw [measure_orderStat_le_of_nonpos _ ha jj, betaMeasure_Iic_of_nonpos _ _ ha]
  · rcases le_or_gt a 1 with ha1 | ha1
    · rw [measure_orderStat_le (j := j) (m := m) ha.le ha1 jj rfl,
        betaMeasure_Iic (by positivity) (by positivity) ha.le ha1]
    · rw [measure_orderStat_le_of_one_le _ ha1.le jj,
        betaMeasure_Iic_of_one_le (by positivity) (by positivity) ha1.le]

end SHSLib.Trigamma
