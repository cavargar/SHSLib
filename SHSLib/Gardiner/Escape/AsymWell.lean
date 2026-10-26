/-
# A concrete asymmetric quartic double well

`U(x) = x⁴/4 - x³/3 - x²`, `U'(x) = x(x + 1)(x - 2)`: minima `a = -1` (`U = -5/12`,
`U'' = 3`) and `c = 2` (`U = -8/3`, `U'' = 6`), barrier top `b = 0` (`U = 0`, `U'' = -2`).
The left well is the upper one, so the population results of §9.1–9.2 are non-trivial.

`Gardiner.Escape.awHyp` verifies `TwoWellHyp` (radius `1/4`, cubic constant `2`, separation
`1/100`), and every theorem of `DoubleWell.lean` and `Splitting.lean` is applied to it.
-/
import SHSLib.Gardiner.Escape.Splitting

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-- The asymmetric quartic double well `U(x) = x⁴/4 - x³/3 - x²`. -/
def awU (x : ℝ) : ℝ := x ^ 4 / 4 - x ^ 3 / 3 - x ^ 2

lemma awU_cont : Continuous awU := by unfold awU; fun_prop

lemma awU_vals : awU (-1) = -5 / 12 ∧ awU 0 = 0 ∧ awU 2 = -8 / 3 ∧ awU (-1 / 2) = -37 / 192 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold awU; norm_num)

lemma awU_integrable : Integrable (fun z => exp (-awU z)) := by
  have hg : Integrable (fun z : ℝ => exp 8 * exp (-(1 / 2) * z ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  refine hg.mono' (Continuous.aestronglyMeasurable (by have := awU_cont; fun_prop))
    (Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.mpr
  unfold awU
  nlinarith [sq_nonneg (z ^ 2 / 2 - z / 3 - 2), sq_nonneg (z - 2), sq_nonneg z, sq_nonneg (z + 1)]

/-- `TwoWellHyp` for the asymmetric quartic: `a = -1`, `b = 0`, `c = 2`, `k_a = 3`, `k_b = 2`,
`k_c = 6`. -/
def awHyp : TwoWellHyp awU (-1) 0 2 where
  r := 1 / 4
  ka := 3
  kb := 2
  kc := 6
  M := 2
  η := 1 / 100
  cont := awU_cont
  hr := by norm_num
  hka := by norm_num
  hkb := by norm_num
  hkc := by norm_num
  hM := by norm_num
  hMra := by norm_num
  hMrb := by norm_num
  hMrc := by norm_num
  hη := by norm_num
  taylor_a := by
    intro s hs
    have e : awU (-1 + s) - awU (-1) - 3 / 2 * s ^ 2 = s ^ 3 * (s / 4 - 4 / 3) := by
      unfold awU; ring
    rw [e, abs_mul, abs_pow]
    have h1 : |s / 4 - 4 / 3| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
    nlinarith [pow_nonneg (abs_nonneg s) 3]
  taylor_b := by
    intro s hs
    have e : awU 0 - awU (0 + s) - 2 / 2 * s ^ 2 = s ^ 3 * (1 / 3 - s / 4) := by
      unfold awU; ring
    rw [e, abs_mul, abs_pow]
    have h1 : |1 / 3 - s / 4| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
    nlinarith [pow_nonneg (abs_nonneg s) 3]
  taylor_c := by
    intro s hs
    have e : awU (2 + s) - awU 2 - 6 / 2 * s ^ 2 = s ^ 3 * (5 / 3 + s / 4) := by
      unfold awU; ring
    rw [e, abs_mul, abs_pow]
    have h1 : |5 / 3 + s / 4| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
    nlinarith [pow_nonneg (abs_nonneg s) 3]
  sep_ab := by norm_num
  sep_bc := by norm_num
  well_a := by
    intro z hz h
    have e : awU z - awU (-1) = (z + 1) ^ 2 * (3 * z ^ 2 - 10 * z + 5) / 12 := by
      unfold awU; ring
    have h2 : 1 / 16 ≤ (z + 1) ^ 2 := by
      have := sq_abs (z - -1); nlinarith [abs_nonneg (z - -1)]
    have h3 : 5 ≤ 3 * z ^ 2 - 10 * z + 5 := by nlinarith
    nlinarith
  well_c := by
    intro z hz h
    have e : awU z - awU 2 = (z - 2) ^ 2 * (3 * z ^ 2 + 8 * z + 8) / 12 := by
      unfold awU; ring
    have h2 : 1 / 16 ≤ (z - 2) ^ 2 := by
      have := sq_abs (z - 2); nlinarith [abs_nonneg (z - 2)]
    have h3 : 8 ≤ 3 * z ^ 2 + 8 * z + 8 := by nlinarith
    nlinarith
  barrier := by
    intro z hz h
    have e : awU 0 - awU z = z ^ 2 * (12 + 4 * z - 3 * z ^ 2) / 12 := by
      unfold awU; ring
    rw [sub_zero] at h
    have h2 : 1 / 16 ≤ z ^ 2 := by have := sq_abs z; nlinarith [abs_nonneg z]
    have h3 : 5 ≤ 12 + 4 * z - 3 * z ^ 2 := by nlinarith [hz.1, hz.2]
    nlinarith
  integrable := awU_integrable

/-- **(9.1.6) for the asymmetric quartic.**
`∫ e^{-U/D} = [e^{5/(12D)}√(2πD/3) + e^{8/(3D)}√(2πD/6)](1 + O(√D))`. -/
theorem asymWell_normalization : ∃ C, ∀ D, 0 < D → D ≤ 1 →
    |normInt awU D / (exp (5 / 12 / D) * √(2 * π * D / 3) + exp (8 / 3 / D) * √(2 * π * D / 6))
      - 1| ≤ C * √D := by
  obtain ⟨C, hC⟩ := normalization_asymp awHyp
  refine ⟨C, fun D hD hD1 => ?_⟩
  have := hC D hD hD1
  obtain ⟨h1, -, h3, -⟩ := awU_vals
  simp only [awHyp, h1, h3] at this
  convert this using 5 <;> ring_nf

/-- **(9.2.23) for the asymmetric quartic.**  `n_a/n_c = √2 e^{-9/(4D)} (1 + O(√D))`. -/
theorem asymWell_population_ratio : ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
    |(popA awU D 0 / popC awU D 0) / (√2 * exp (-(9 / 4) / D)) - 1| ≤ C * √D := by
  obtain ⟨C, D₀, hD₀, hC⟩ := population_ratio_asymp awHyp
  refine ⟨C, D₀, hD₀, fun D hD hD1 => ?_⟩
  have := hC D hD hD1
  obtain ⟨h1, -, h3, -⟩ := awU_vals
  simp only [awHyp, h1, h3] at this
  convert this using 5 <;> norm_num

/-- **(9.1.8) for the asymmetric quartic.**  The upper (left) well's population is
`n_a ≤ C e^{-9/(4D)}`. -/
theorem asymWell_population_small : ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
    popA awU D 0 / normInt awU D ≤ C * exp (-(9 / 4) / D) := by
  obtain ⟨C, D₀, hD₀, hC⟩ := population_small awHyp
  refine ⟨C, D₀, hD₀, fun D hD hD1 => ?_⟩
  have := hC D hD hD1
  obtain ⟨h1, -, h3, -⟩ := awU_vals
  rw [h1, h3] at this
  convert this using 4; norm_num

/-- **(9.1.13) for the asymmetric quartic.**  `∫_{-1}^2 e^{U/D} = √(πD) (1 + O(√D))`. -/
theorem asymWell_barrier_integral : ∃ C, ∀ D, 0 < D → D ≤ 1 →
    |(∫ x in (-1 : ℝ)..2, exp (awU x / D)) / √(π * D) - 1| ≤ C * √D := by
  obtain ⟨C, hC⟩ := barrier_integral_asymp awHyp
  refine ⟨C, fun D hD hD1 => ?_⟩
  have := hC D hD hD1
  obtain ⟨-, h2, -, -⟩ := awU_vals
  simp only [awHyp, h2, zero_div, exp_zero, mul_one] at this
  convert this using 5; ring_nf

/-- **(9.2.24)–(9.2.25) for the asymmetric quartic.**  The relaxation time satisfies
`τ_r = 2π H √(n_a n_c) (1 + O(√D))` with `H = 2^{-1/2} 18^{-1/4} e^{37/(24D)}`. -/
theorem asymWell_relaxTime : ∃ C, ∀ D, 0 < D → D ≤ 1 →
    |relaxTime awU D (-1) 0 2 / (2 * π * ((√2)⁻¹ * (√(√18))⁻¹ * exp (37 / 24 / D)) *
      √((popA awU D 0 / normInt awU D) * (popC awU D 0 / normInt awU D))) - 1| ≤ C * √D := by
  obtain ⟨C, hC⟩ := relaxTime_asymp awHyp
  refine ⟨C, fun D hD hD1 => ?_⟩
  have := hC D hD hD1
  obtain ⟨h1, h2, h3, -⟩ := awU_vals
  simp only [awHyp, Hfac, h1, h2, h3] at this
  convert this using 7 <;> norm_num
  ring_nf

/-- **(9.1.16) for the asymmetric quartic** at `x₀ = -1/2` (`U'(-1/2) = 5/8`):
`π_c(-1/2) = (8/5)√(D/π) e^{-37/(192D)} (1 + O(√D))`. -/
theorem asymWell_splitting_far : ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
    |splitC awU D (-1) 2 (-1 / 2) / (8 / 5 * √(D / π) * exp (-(37 / 192) / D)) - 1|
      ≤ C * √D := by
  obtain ⟨C, D₀, hD₀, hC⟩ := splitting_far awHyp (x₀ := -1 / 2) (g := 5 / 8) (r := 1 / 4)
    (M := 1 / 8) (η := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s hs => by
      have e : awU (-1 / 2) - awU (-1 / 2 - s) - 5 / 8 * s = s ^ 2 * (1 / 8 - 5 * s / 6 - s ^ 2 / 4) := by
        unfold awU; ring
      rw [e, abs_mul, abs_of_nonneg (sq_nonneg s)]
      have : |1 / 8 - 5 * s / 6 - s ^ 2 / 4| ≤ 1 / 8 := by
        rw [abs_le]; constructor <;> nlinarith [hs.1, hs.2]
      nlinarith [sq_nonneg s])
    (by norm_num) (by norm_num)
    (fun z hz => by
      have h1 := hz.1; have h2 : z ≤ -3 / 4 := by linarith [hz.2]
      unfold awU
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), sq_nonneg (z + 1),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)) (sq_nonneg z)])
  refine ⟨C, D₀, hD₀, fun D hD hD1 => ?_⟩
  have := hC D hD hD1
  obtain ⟨-, h2, -, h4⟩ := awU_vals
  simp only [awHyp, h2, h4] at this
  convert this using 5
  · congr 1
    · norm_num
    · congr 1; field_simp
  · congr 1; ring

/-- **(9.1.20) for the asymmetric quartic.**  Starting at `x₀ = -y₀√D`,
`π_c = ½[1 - erf_G(y₀√2)] + O(√D)`. -/
theorem asymWell_splitting_near {y₀ : ℝ} (hy₀ : 0 ≤ y₀) : ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
    |splitC awU D (-1) 2 (-(y₀ * √D)) - (1 - gerf (y₀ * √2)) / 2| ≤ C * √D := by
  obtain ⟨C, D₀, hD₀, hC⟩ := splitting_near awHyp hy₀
  refine ⟨C, D₀, hD₀, fun D hD hD1 => ?_⟩
  have := hC D hD hD1
  simp only [awHyp, zero_sub] at this
  exact this

end Gardiner.Escape
