/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The trigamma series `ψ'(x) = ∑_{k ≥ 0} 1/(x+k)²`

`SHSLib/Foundations/Trigamma.lean` evaluates the second derivative of `log Γ`
at `1` and at `1/2`, and propagates those two values along the integers and the
half-integers.  This file removes the restriction to those two progressions and
proves the series representation of the trigamma function at *every* positive
real,

  `ψ'(x) = ∑_{k ≥ 0} 1/(x+k)²`   (`SHSLib.Trigamma.hasSum_trigamma`),

of which the Basel sum `ψ'(1) = π²/6` is the case `x = 1`.

The argument uses no asymptotics of `Γ`.  Writing
`defect x = ψ'(x) − ∑_{k ≥ 0} 1/(x+k)²`, the recurrence `ψ'(x+1) = ψ'(x) − 1/x²`
says exactly that `defect x` is the limit of `ψ'(x+n)`, so `defect` is
`1`-periodic, and the duplication formula passes to the limit as
`defect x + defect (x + 1/2) = 4 · defect (2x)`.  Periodicity plus continuity of
`ψ'` on a compact period bounds `defect` by some `K`; the duplication relation
then improves the bound to `K/2`, hence to `K/2ⁿ`, hence to `0`.
-/
import SHSLib.Foundations.Trigamma

open Real Set Filter

namespace SHSLib.Trigamma

/-- The trigamma function `ψ' = (log Γ)''`. -/
noncomputable def trigamma (x : ℝ) : ℝ := deriv (deriv logGamma) x

theorem trigamma_def (x : ℝ) : trigamma x = deriv (deriv logGamma) x := rfl

/-! ### Regularity, the recurrence and the duplication formula, restated -/

theorem contDiffOn_trigamma : ContDiffOn ℝ (⊤ : ℕ∞) trigamma (Ioi 0) :=
  ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp contDiffOn_deriv_logGamma).2

theorem continuousOn_trigamma : ContinuousOn trigamma (Ioi 0) :=
  contDiffOn_trigamma.continuousOn

theorem trigamma_step {x : ℝ} (hx : 0 < x) : trigamma (x + 1) = trigamma x - 1 / x ^ 2 :=
  trigamma_add_one hx

theorem trigamma_dup {x : ℝ} (hx : 0 < x) :
    trigamma x + trigamma (x + 1 / 2) = 4 * trigamma (2 * x) :=
  trigamma_duplication hx

/-! ### The shifted Basel series -/

/-- Termwise comparison bound: `1/(x+k)² ≤ (1/c²) · 1/(k+1)²` with `c = min x 1`. -/
theorem inv_sq_shift_le {x : ℝ} (hx : 0 < x) (k : ℕ) :
    1 / (x + k) ^ 2 ≤ (1 / min x 1 ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hc : 0 < min x 1 := lt_min hx one_pos
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hle : min x 1 * ((k : ℝ) + 1) ≤ x + k := by
    have h1 : min x 1 ≤ x := min_le_left _ _
    have h2 : min x 1 ≤ 1 := min_le_right _ _
    nlinarith
  have hpos : (0 : ℝ) < min x 1 * ((k : ℝ) + 1) := by positivity
  rw [show (1 / min x 1 ^ 2) * (1 / ((k : ℝ) + 1) ^ 2)
      = 1 / (min x 1 * ((k : ℝ) + 1)) ^ 2 by field_simp]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hpos, hle])

theorem summable_inv_sq_shift {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => 1 / (x + k) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (inv_sq_shift_le hx)
    (hasSum_basel_shift.summable.mul_left _)

/-- The trigamma recurrence iterated: `ψ'(x+n) = ψ'(x) − ∑_{k<n} 1/(x+k)²`. -/
theorem trigamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    trigamma (x + n) = trigamma x - ∑ k ∈ Finset.range n, 1 / (x + k) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : (0 : ℝ) < x + n := by positivity
      have h := trigamma_step hpos
      have hcast : x + ((n : ℝ) + 1) = x + n + 1 := by ring
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring, hcast, h, ih,
        Finset.sum_range_succ]
      ring

/-! ### The defect and its vanishing -/

/-- The difference between the trigamma value and the shifted Basel series.  The
whole point of the file is that it is identically zero. -/
noncomputable def defect (x : ℝ) : ℝ := trigamma x - ∑' k : ℕ, 1 / (x + k) ^ 2

/-- `defect x` is the limit of the trigamma values along `x, x+1, x+2, …`. -/
theorem tendsto_trigamma_add_nat {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => trigamma (x + n)) atTop (nhds (defect x)) := by
  have hsum := (summable_inv_sq_shift hx).hasSum.tendsto_sum_nat
  have h : Tendsto (fun n : ℕ => trigamma x - ∑ i ∈ Finset.range n, 1 / (x + (i : ℝ)) ^ 2)
      atTop (nhds (trigamma x - ∑' k : ℕ, 1 / (x + (k : ℝ)) ^ 2)) :=
    tendsto_const_nhds.sub hsum
  exact h.congr fun n => (trigamma_add_nat hx n).symm

theorem defect_add_one {x : ℝ} (hx : 0 < x) : defect (x + 1) = defect x := by
  have h1 : Tendsto (fun n : ℕ => trigamma (x + 1 + n)) atTop (nhds (defect (x + 1))) :=
    tendsto_trigamma_add_nat (by linarith)
  have h2 : Tendsto (fun n : ℕ => trigamma (x + (n + 1 : ℕ))) atTop (nhds (defect x)) :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => trigamma (x + n)) 1).mpr
      (tendsto_trigamma_add_nat hx)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  push_cast
  ring_nf

theorem defect_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) : defect (x + n) = defect x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : (0 : ℝ) < x + n := by positivity
      have := defect_add_one hpos
      rw [show x + ((n + 1 : ℕ) : ℝ) = x + n + 1 by push_cast; ring, this, ih]

/-- The duplication formula in the limit. -/
theorem defect_duplication {x : ℝ} (hx : 0 < x) :
    defect x + defect (x + 1 / 2) = 4 * defect (2 * x) := by
  have hL : Tendsto (fun n : ℕ => trigamma (x + n) + trigamma (x + 1 / 2 + n)) atTop
      (nhds (defect x + defect (x + 1 / 2))) :=
    (tendsto_trigamma_add_nat hx).add (tendsto_trigamma_add_nat (by linarith))
  have hsub : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) (fun b => ⟨b, by omega⟩)
  have hR : Tendsto (fun n : ℕ => 4 * trigamma (2 * x + ((2 * n : ℕ) : ℝ))) atTop
      (nhds (4 * defect (2 * x))) :=
    ((tendsto_trigamma_add_nat (x := 2 * x) (by linarith)).comp hsub).const_mul 4
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  have h := trigamma_dup (x := x + n) (by positivity)
  have h2 : 2 * (x + (n : ℝ)) = 2 * x + ((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [h2] at h
  rw [← h]
  ring_nf

/-! ### `defect` is bounded, hence zero -/

theorem tsum_inv_sq_shift_le {x : ℝ} (hx : 1 ≤ x) :
    ∑' k : ℕ, 1 / (x + k) ^ 2 ≤ π ^ 2 / 6 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  rw [← hasSum_basel_shift.tsum_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_inv_sq_shift hx0)
    hasSum_basel_shift.summable
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- `defect` is bounded on the whole positive half-line: by periodicity it is
determined by its values on a compact period, where `ψ'` is continuous and the
series is dominated by the Basel sum. -/
theorem exists_defect_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → |defect x| ≤ K := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (continuousOn_trigamma.mono (fun y hy => lt_of_lt_of_le one_pos hy.1))
  have hM0 : (0 : ℝ) ≤ M :=
    le_trans (abs_nonneg _) (hM 1 ⟨le_refl _, by norm_num⟩)
  have hpi : (0 : ℝ) ≤ π ^ 2 / 6 := by positivity
  refine ⟨M + π ^ 2 / 6, by linarith, fun x hx => ?_⟩
  -- reduce to a point of `[1, 2]`, using the `1`-periodicity of `defect`
  obtain ⟨y, hy1, hy2, hdef⟩ : ∃ y : ℝ, 1 ≤ y ∧ y ≤ 2 ∧ defect x = defect y := by
    rcases lt_or_ge x 1 with h | h
    · exact ⟨x + 1, by linarith, by linarith, (defect_add_one hx).symm⟩
    · have hfl1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h)
      have hmc : ((⌊x⌋₊ - 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hfl1, Nat.cast_one]
      have hfle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hflt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have hy0 : 0 < x - ((⌊x⌋₊ - 1 : ℕ) : ℝ) := by rw [hmc]; linarith
      refine ⟨x - ((⌊x⌋₊ - 1 : ℕ) : ℝ), by rw [hmc]; linarith, by rw [hmc]; linarith, ?_⟩
      have hper := defect_add_nat hy0 (⌊x⌋₊ - 1)
      rw [show x - ((⌊x⌋₊ - 1 : ℕ) : ℝ) + ((⌊x⌋₊ - 1 : ℕ) : ℝ) = x by ring] at hper
      exact hper
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy1
  rw [hdef, defect]
  have h1 : |trigamma y| ≤ M := hM y ⟨hy1, hy2⟩
  have h2 : 0 ≤ ∑' k : ℕ, 1 / (y + k) ^ 2 :=
    tsum_nonneg fun k => by positivity
  have h3 : ∑' k : ℕ, 1 / (y + k) ^ 2 ≤ π ^ 2 / 6 := tsum_inv_sq_shift_le hy1
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

theorem defect_eq_zero {x : ℝ} (hx : 0 < x) : defect x = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_defect_bound
  have key : ∀ n : ℕ, ∀ y : ℝ, 0 < y → |defect y| ≤ K / 2 ^ n := by
    intro n
    induction n with
    | zero => simpa using hK
    | succ n ih =>
        intro y hy
        have hhalf : (0 : ℝ) < y / 2 := by linarith
        have hd := defect_duplication hhalf
        have h2 : 2 * (y / 2) = y := by ring
        rw [h2] at hd
        have h3 : |defect y| ≤ (|defect (y / 2)| + |defect (y / 2 + 1 / 2)|) / 4 := by
          have : defect y = (defect (y / 2) + defect (y / 2 + 1 / 2)) / 4 := by linarith
          rw [this, abs_div]
          have habs : |defect (y / 2) + defect (y / 2 + 1 / 2)|
              ≤ |defect (y / 2)| + |defect (y / 2 + 1 / 2)| := abs_add_le _ _
          simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (4:ℝ))]
          linarith
        have hb1 := ih (y / 2) hhalf
        have hb2 := ih (y / 2 + 1 / 2) (by linarith)
        have hpow : (0 : ℝ) < 2 ^ n := by positivity
        have heq : (K / 2 ^ n + K / 2 ^ n) / 4 = K / (2 ^ n * 2) := by
          field_simp
          ring
        rw [pow_succ]
        linarith
  have hlim : Tendsto (fun n : ℕ => K / 2 ^ n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, ← inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)
        (by norm_num : (2:ℝ)⁻¹ < 1)).const_mul K
  have : |defect x| ≤ 0 := ge_of_tendsto' hlim (fun n => key n x hx)
  have := abs_nonneg (defect x)
  have h0 : |defect x| = 0 := le_antisymm (by assumption) (by assumption)
  exact abs_eq_zero.mp h0

/-! ### The series representation -/

/-- **The trigamma series.**  For every `x > 0`,
`(log Γ)''(x) = ∑_{k ≥ 0} 1/(x+k)²`. -/
theorem hasSum_trigamma {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => 1 / (x + k) ^ 2) (trigamma x) := by
  have h := defect_eq_zero hx
  rw [defect, sub_eq_zero] at h
  rw [h]
  exact (summable_inv_sq_shift hx).hasSum

theorem trigamma_eq_tsum {x : ℝ} (hx : 0 < x) :
    trigamma x = ∑' k : ℕ, 1 / (x + k) ^ 2 :=
  (hasSum_trigamma hx).tsum_eq.symm

/-- The trigamma series, phrased for `log ∘ Γ` directly. -/
theorem hasSum_deriv_deriv_log_Gamma {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => 1 / (x + k) ^ 2) (deriv (deriv (Real.log ∘ Real.Gamma)) x) := by
  rw [logGamma_eq_comp]
  exact hasSum_trigamma hx

/-- The case `x = 1` of the trigamma series is the Basel sum. -/
theorem trigamma_one_value : trigamma 1 = π ^ 2 / 6 := trigamma_one

/-- The case `x = 1/2` is the odd-denominator Basel sum. -/
theorem trigamma_half_value : trigamma (1 / 2) = π ^ 2 / 2 := trigamma_half

/-- The trigamma function is strictly positive on `(0, ∞)`. -/
theorem trigamma_pos {x : ℝ} (hx : 0 < x) : 0 < trigamma x := by
  rw [trigamma_eq_tsum hx]
  refine Summable.tsum_pos (summable_inv_sq_shift hx) (fun k => by positivity) 0 ?_
  simp only [Nat.cast_zero, add_zero]
  positivity

/-- The trigamma function is strictly decreasing on `(0, ∞)`. -/
theorem trigamma_strictAntiOn : StrictAntiOn trigamma (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) < a := ha
  have hb0 : (0 : ℝ) < b := hb
  rw [trigamma_eq_tsum ha0, trigamma_eq_tsum hb0]
  have hle : ∀ k : ℕ, 1 / (b + (k : ℝ)) ^ 2 ≤ 1 / (a + (k : ℝ)) ^ 2 := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hlt : 1 / (b + ((0 : ℕ) : ℝ)) ^ 2 < 1 / (a + ((0 : ℕ) : ℝ)) ^ 2 := by
    simp only [Nat.cast_zero, add_zero]
    have h1 : (0 : ℝ) < a ^ 2 := by positivity
    have h2 : (0 : ℝ) < b ^ 2 := by positivity
    rw [div_lt_div_iff₀ h2 h1]
    nlinarith
  exact Summable.tsum_lt_tsum (i := 0) hle hlt (summable_inv_sq_shift hb0)
    (summable_inv_sq_shift ha0)

/-- `ψ'(x) → 0` as `x → ∞`. -/
theorem tendsto_trigamma_atTop : Tendsto trigamma atTop (nhds 0) := by
  have hfloor : Tendsto (fun x : ℝ => ⌊x - 1⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have hg : Tendsto (fun x : ℝ => trigamma ((⌊x - 1⌋₊ : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_trigamma_nat_add_one.comp hfloor
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (trigamma_pos (by linarith)).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hle : (⌊x - 1⌋₊ : ℝ) + 1 ≤ x := by
      have := Nat.floor_le (by linarith : (0 : ℝ) ≤ x - 1)
      linarith
    rcases eq_or_lt_of_le hle with h | h
    · rw [h]
    · exact (trigamma_strictAntiOn (mem_Ioi.mpr (by positivity))
        (mem_Ioi.mpr (by linarith)) h).le

end SHSLib.Trigamma
