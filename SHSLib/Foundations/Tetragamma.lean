/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The tetragamma series `ψ''(x) = −2 ∑_{k ≥ 0} 1/(x+k)³`

This file repeats, one derivative higher, the argument of
`SHSLib/Foundations/TrigammaSeries.lean`.  Differentiating the trigamma
recurrence and the trigamma duplication formula gives

  `ψ''(x+1) = ψ''(x) + 2/x³`   and   `ψ''(x) + ψ''(x+1/2) = 8 ψ''(2x)`,

and the same three-step scheme — the defect `ψ''(x) + 2∑_k 1/(x+k)³` is
`1`-periodic, bounded, and quartered by the duplication relation — shows that
the defect vanishes:

  `ψ''(x) = −2 ∑_{k ≥ 0} 1/(x+k)³`   (`SHSLib.Trigamma.hasSum_tetragamma`).

At `x = 1` this is `(log Γ)'''(1) = −2 ζ(3)`
(`SHSLib.Trigamma.tetragamma_one_eq_tsum`).
-/
import SHSLib.Foundations.TrigammaSeries

open Real Set Filter

namespace SHSLib.Trigamma

/-- The tetragamma function `ψ'' = (log Γ)'''. -/
noncomputable def tetragamma (x : ℝ) : ℝ := deriv trigamma x

theorem tetragamma_def (x : ℝ) : tetragamma x = deriv trigamma x := rfl

/-! ### Regularity -/

theorem differentiableAt_trigamma {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ trigamma x :=
  ((contDiffOn_trigamma x hx).differentiableWithinAt (by simp)).differentiableAt
    (Ioi_mem_nhds hx)

theorem contDiffOn_tetragamma : ContDiffOn ℝ (⊤ : ℕ∞) tetragamma (Ioi 0) :=
  ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp contDiffOn_trigamma).2

theorem continuousOn_tetragamma : ContinuousOn tetragamma (Ioi 0) :=
  contDiffOn_tetragamma.continuousOn

/-! ### The recurrence and the duplication formula, one derivative higher -/

/-- Differentiating `ψ'(x+1) = ψ'(x) − 1/x²`. -/
theorem tetragamma_add_one {x : ℝ} (hx : 0 < x) :
    tetragamma (x + 1) = tetragamma x + 2 / x ^ 3 := by
  have hEq : (fun y : ℝ => trigamma (y + 1))
      =ᶠ[nhds x] fun y : ℝ => trigamma y - 1 / y ^ 2 := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with y hy
    exact trigamma_step hy
  have hA : HasDerivAt (fun y : ℝ => trigamma (y + 1)) (tetragamma (x + 1)) x :=
    HasDerivAt.comp_add_const x 1 (differentiableAt_trigamma (by linarith)).hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-(2 * x) / (x ^ 2) ^ 2) x := by
    simpa [one_div] using h1.inv (pow_ne_zero 2 hx.ne')
  have hB : HasDerivAt (fun y : ℝ => trigamma y - 1 / y ^ 2)
      (tetragamma x - -(2 * x) / (x ^ 2) ^ 2) x :=
    (differentiableAt_trigamma hx).hasDerivAt.sub h2
  have hd := hEq.deriv_eq
  rw [hA.deriv, hB.deriv] at hd
  rw [hd]
  field_simp
  ring

/-- Differentiating `ψ'(x) + ψ'(x + 1/2) = 4 ψ'(2x)`. -/
theorem tetragamma_duplication {x : ℝ} (hx : 0 < x) :
    tetragamma x + tetragamma (x + 1 / 2) = 8 * tetragamma (2 * x) := by
  have hEq : (fun y : ℝ => trigamma y + trigamma (y + 1 / 2))
      =ᶠ[nhds x] fun y : ℝ => 4 * trigamma (2 * y) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with y hy
    exact trigamma_dup hy
  have hA : HasDerivAt (fun y : ℝ => trigamma y + trigamma (y + 1 / 2))
      (tetragamma x + tetragamma (x + 1 / 2)) x :=
    (differentiableAt_trigamma hx).hasDerivAt.add
      (HasDerivAt.comp_add_const x (1 / 2)
        (differentiableAt_trigamma (by linarith)).hasDerivAt)
  have hdouble : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hB : HasDerivAt (fun y : ℝ => 4 * trigamma (2 * y))
      (4 * (tetragamma (2 * x) * 2)) x :=
    (((differentiableAt_trigamma (by linarith : (0:ℝ) < 2 * x)).hasDerivAt).comp x
      hdouble).const_mul 4
  have hd := hEq.deriv_eq
  rw [hA.deriv, hB.deriv] at hd
  rw [hd]
  ring

/-! ### The shifted cubic series -/

theorem summable_inv_cube_shift {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => 1 / (x + k) ^ 3) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_inv_sq_shift hx).mul_left (1 / x))
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hxne : x ≠ 0 := hx.ne'
  have hxk : x + (k : ℝ) ≠ 0 := by positivity
  rw [show (1 / x) * (1 / (x + (k : ℝ)) ^ 2) = 1 / (x * (x + k) ^ 2) by field_simp]
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith [sq_nonneg ((x : ℝ) + k), sq_nonneg (x : ℝ)]

/-- The iterated recurrence: `ψ''(x+n) = ψ''(x) + ∑_{k<n} 2/(x+k)³`. -/
theorem tetragamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    tetragamma (x + n) = tetragamma x + ∑ k ∈ Finset.range n, 2 / (x + k) ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : (0 : ℝ) < x + n := by positivity
      have h := tetragamma_add_one hpos
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
        show x + ((n : ℝ) + 1) = x + n + 1 by ring, h, ih, Finset.sum_range_succ]
      ring

/-! ### The defect -/

/-- The difference between `ψ''(x)` and `−2 ∑_k 1/(x+k)³`. -/
noncomputable def defect3 (x : ℝ) : ℝ := tetragamma x + ∑' k : ℕ, 2 / (x + k) ^ 3

theorem tendsto_tetragamma_add_nat {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => tetragamma (x + n)) atTop (nhds (defect3 x)) := by
  have hsum := ((summable_inv_cube_shift hx).mul_left 2).hasSum.tendsto_sum_nat
  have hsum' : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, 2 / (x + (i : ℝ)) ^ 3) atTop
      (nhds (∑' k : ℕ, 2 / (x + (k : ℝ)) ^ 3)) := by
    simpa [mul_one_div] using hsum
  have h : Tendsto (fun n : ℕ => tetragamma x + ∑ i ∈ Finset.range n, 2 / (x + (i : ℝ)) ^ 3)
      atTop (nhds (tetragamma x + ∑' k : ℕ, 2 / (x + (k : ℝ)) ^ 3)) :=
    tendsto_const_nhds.add hsum'
  exact h.congr fun n => (tetragamma_add_nat hx n).symm

theorem defect3_add_one {x : ℝ} (hx : 0 < x) : defect3 (x + 1) = defect3 x := by
  have h1 : Tendsto (fun n : ℕ => tetragamma (x + 1 + n)) atTop (nhds (defect3 (x + 1))) :=
    tendsto_tetragamma_add_nat (by linarith)
  have h2 : Tendsto (fun n : ℕ => tetragamma (x + (n + 1 : ℕ))) atTop (nhds (defect3 x)) :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => tetragamma (x + n)) 1).mpr
      (tendsto_tetragamma_add_nat hx)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  push_cast
  ring_nf

theorem defect3_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) : defect3 (x + n) = defect3 x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : (0 : ℝ) < x + n := by positivity
      have := defect3_add_one hpos
      rw [show x + ((n + 1 : ℕ) : ℝ) = x + n + 1 by push_cast; ring, this, ih]

theorem defect3_duplication {x : ℝ} (hx : 0 < x) :
    defect3 x + defect3 (x + 1 / 2) = 8 * defect3 (2 * x) := by
  have hL : Tendsto (fun n : ℕ => tetragamma (x + n) + tetragamma (x + 1 / 2 + n)) atTop
      (nhds (defect3 x + defect3 (x + 1 / 2))) :=
    (tendsto_tetragamma_add_nat hx).add (tendsto_tetragamma_add_nat (by linarith))
  have hsub : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) (fun b => ⟨b, by omega⟩)
  have hR : Tendsto (fun n : ℕ => 8 * tetragamma (2 * x + ((2 * n : ℕ) : ℝ))) atTop
      (nhds (8 * defect3 (2 * x))) :=
    ((tendsto_tetragamma_add_nat (x := 2 * x) (by linarith)).comp hsub).const_mul 8
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  have h := tetragamma_duplication (x := x + n) (by positivity)
  have h2 : 2 * (x + (n : ℝ)) = 2 * x + ((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [h2] at h
  rw [← h]
  ring_nf

/-! ### `defect3` is bounded, hence zero -/

theorem tsum_inv_cube_shift_le {x : ℝ} (hx : 1 ≤ x) :
    ∑' k : ℕ, 2 / (x + k) ^ 3 ≤ 2 * (π ^ 2 / 6) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hle : ∀ k : ℕ, 2 / (x + (k : ℝ)) ^ 3 ≤ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [show (2 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) = 2 / ((k : ℝ) + 1) ^ 2 by ring]
    have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    have hcube : ((k : ℝ) + 1) ^ 2 ≤ (x + k) ^ 3 := by
      have hxk : ((k : ℝ) + 1) ≤ x + k := by linarith
      have h3 : ((k : ℝ) + 1) ^ 3 ≤ (x + k) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hxk 3
      have h4 : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ 3 := by
        nlinarith [sq_nonneg ((k : ℝ) + 1)]
      linarith
    exact div_le_div_of_nonneg_left (by norm_num) hpos hcube
  calc ∑' k : ℕ, 2 / (x + (k : ℝ)) ^ 3
      ≤ ∑' k : ℕ, 2 * (1 / ((k : ℝ) + 1) ^ 2) :=
        Summable.tsum_le_tsum hle ((summable_inv_cube_shift hx0).mul_left 2 |>.congr
          (fun k => by ring)) (hasSum_basel_shift.summable.mul_left 2)
    _ = 2 * (π ^ 2 / 6) := by
        rw [tsum_mul_left, hasSum_basel_shift.tsum_eq]

theorem exists_defect3_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → |defect3 x| ≤ K := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (continuousOn_tetragamma.mono (fun y hy => lt_of_lt_of_le one_pos hy.1))
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 1 ⟨le_refl _, by norm_num⟩)
  have hpi : (0 : ℝ) ≤ 2 * (π ^ 2 / 6) := by positivity
  refine ⟨M + 2 * (π ^ 2 / 6), by linarith, fun x hx => ?_⟩
  obtain ⟨y, hy1, hy2, hdef⟩ : ∃ y : ℝ, 1 ≤ y ∧ y ≤ 2 ∧ defect3 x = defect3 y := by
    rcases lt_or_ge x 1 with h | h
    · exact ⟨x + 1, by linarith, by linarith, (defect3_add_one hx).symm⟩
    · have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h)
      have hmc : ((⌊x⌋₊ - 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hfl1, Nat.cast_one]
      have hfle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hflt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have hy0 : 0 < x - ((⌊x⌋₊ - 1 : ℕ) : ℝ) := by rw [hmc]; linarith
      refine ⟨x - ((⌊x⌋₊ - 1 : ℕ) : ℝ), by rw [hmc]; linarith, by rw [hmc]; linarith, ?_⟩
      have hper := defect3_add_nat hy0 (⌊x⌋₊ - 1)
      rw [show x - ((⌊x⌋₊ - 1 : ℕ) : ℝ) + ((⌊x⌋₊ - 1 : ℕ) : ℝ) = x by ring] at hper
      exact hper
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy1
  rw [hdef, defect3]
  have h1 : |tetragamma y| ≤ M := hM y ⟨hy1, hy2⟩
  have h2 : 0 ≤ ∑' k : ℕ, 2 / (y + k) ^ 3 := tsum_nonneg fun k => by positivity
  have h3 : ∑' k : ℕ, 2 / (y + k) ^ 3 ≤ 2 * (π ^ 2 / 6) := tsum_inv_cube_shift_le hy1
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

theorem defect3_eq_zero {x : ℝ} (hx : 0 < x) : defect3 x = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_defect3_bound
  have key : ∀ n : ℕ, ∀ y : ℝ, 0 < y → |defect3 y| ≤ K / 2 ^ n := by
    intro n
    induction n with
    | zero => simpa using hK
    | succ n ih =>
        intro y hy
        have hhalf : (0 : ℝ) < y / 2 := by linarith
        have hd := defect3_duplication hhalf
        rw [show 2 * (y / 2) = y by ring] at hd
        have h3 : |defect3 y| ≤ (|defect3 (y / 2)| + |defect3 (y / 2 + 1 / 2)|) / 8 := by
          have heq : defect3 y = (defect3 (y / 2) + defect3 (y / 2 + 1 / 2)) / 8 := by linarith
          rw [heq, abs_div]
          have habs : |defect3 (y / 2) + defect3 (y / 2 + 1 / 2)|
              ≤ |defect3 (y / 2)| + |defect3 (y / 2 + 1 / 2)| := abs_add_le _ _
          simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (8:ℝ))]
          linarith
        have hb1 := ih (y / 2) hhalf
        have hb2 := ih (y / 2 + 1 / 2) (by linarith)
        have hpow : (0 : ℝ) < 2 ^ n := by positivity
        have hq : (0 : ℝ) ≤ K / 2 ^ n := by positivity
        have heq : (K / 2 ^ n + K / 2 ^ n) / 8 ≤ K / (2 ^ n * 2) := by
          have h1 : K / (2 ^ n * 2) = K / 2 ^ n / 2 := (div_div K (2 ^ n) 2).symm
          have h2 : (K / 2 ^ n + K / 2 ^ n) / 8 = K / 2 ^ n / 4 := by ring
          rw [h1, h2]
          linarith
        rw [pow_succ]
        linarith
  have hlim : Tendsto (fun n : ℕ => K / 2 ^ n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, ← inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)
        (by norm_num : (2:ℝ)⁻¹ < 1)).const_mul K
  have hle : |defect3 x| ≤ 0 := ge_of_tendsto' hlim (fun n => key n x hx)
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-! ### The series representation -/

/-- **The tetragamma series.**  For every `x > 0`,
`(log Γ)'''(x) = −2 ∑_{k ≥ 0} 1/(x+k)³`. -/
theorem hasSum_tetragamma {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => -(2 / (x + k) ^ 3)) (tetragamma x) := by
  have h := defect3_eq_zero hx
  rw [defect3] at h
  have hs : HasSum (fun k : ℕ => 2 / (x + (k : ℝ)) ^ 3)
      (∑' k : ℕ, 2 / (x + (k : ℝ)) ^ 3) :=
    (((summable_inv_cube_shift hx).mul_left 2).congr (fun k => by ring)).hasSum
  have hneg := hs.neg
  rw [show -(∑' k : ℕ, 2 / (x + (k : ℝ)) ^ 3) = tetragamma x by linarith] at hneg
  exact hneg

theorem tetragamma_eq_tsum {x : ℝ} (hx : 0 < x) :
    tetragamma x = -(2 * ∑' k : ℕ, 1 / (x + k) ^ 3) := by
  have h := (hasSum_tetragamma hx).tsum_eq
  rw [← h, tsum_neg]
  congr 1
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by ring

/-- The tetragamma series, phrased for `log ∘ Γ` directly. -/
theorem hasSum_deriv_deriv_deriv_log_Gamma {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => -(2 / (x + k) ^ 3))
      (deriv (deriv (deriv (Real.log ∘ Real.Gamma))) x) := by
  rw [logGamma_eq_comp]
  exact hasSum_tetragamma hx

/-- `(log Γ)'''(1) = −2 ζ(3)`. -/
theorem tetragamma_one_eq_tsum :
    tetragamma 1 = -(2 * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) := by
  have h := tetragamma_eq_tsum (x := 1) one_pos
  rw [h]
  congr 2
  exact tsum_congr fun k => by ring

/-- Apéry's constant, as the shifted series appearing in `tetragamma_one_eq_tsum`. -/
theorem tsum_inv_cube_shift_eq_zeta_three :
    ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3 = ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  rw [hs.tsum_eq_zero_add]
  norm_num

/-- `(log Γ)'''(1) = −2 ζ(3)`, with `ζ(3)` written as `∑' n, 1/n³`. -/
theorem tetragamma_one_eq_zeta_three :
    tetragamma 1 = -(2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 3) := by
  rw [tetragamma_one_eq_tsum, tsum_inv_cube_shift_eq_zeta_three]

/-- The tetragamma function is strictly negative on `(0, ∞)`: `ψ'` is strictly
decreasing, as `trigamma_strictAntiOn` says. -/
theorem tetragamma_neg {x : ℝ} (hx : 0 < x) : tetragamma x < 0 := by
  rw [tetragamma_eq_tsum hx, neg_lt_zero]
  have hpos : 0 < ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ 3 := by
    refine Summable.tsum_pos (summable_inv_cube_shift hx) (fun k => by positivity) 0 ?_
    simp only [Nat.cast_zero, add_zero]
    positivity
  linarith

end SHSLib.Trigamma
