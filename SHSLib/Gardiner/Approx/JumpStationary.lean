/-
# Stationary distribution of the birth–death approximation of a diffusion

Gardiner, *Handbook of Stochastic Methods*, §7.2.1 c), (7.2.19)–(7.2.21).

The birth–death process (7.2.16) on the lattice `x = kδ`, `k ∈ ℕ` (reflecting at `x = 0`), with
rates `t⁺(x) = A(x)/(2δ) + B(x)/(2δ²)` and `t⁻(x) = -A(x)/(2δ) + B(x)/(2δ²)`
(`Gardiner.bdRate`), has the detailed-balance stationary solution (7.2.19).  As `δ → 0` its
logarithm converges to that of the stationary Fokker–Planck solution (7.2.21),
`P_s(x) = 𝒩 B(x)⁻¹ exp[2∫₀ˣ A/B]`.

* `Gardiner.bdStat` — the product formula (7.2.19), first line.
* `Gardiner.bdStat_flux`, `Gardiner.bdStat_stationary` — it satisfies detailed balance, hence the
  stationary master equation.
* `Gardiner.bdStat_eq_ratio` — the second line of (7.2.19).
* `Gardiner.log_ratio_cubic`, `Gardiner.abs_log_one_sub_le` — the elementary estimates behind
  (7.2.20).
* `Gardiner.bdStat_log_rate` — **(7.2.20)–(7.2.21) with an explicit `O(δ)` error**: at `x = Nδ`,
  `|log P_s(x) - [log P_s(0) + log B(0) - log B(x) + 2∫₀ˣ A/B]|
    ≤ δ (2Lx + 4a/b + 4xδ(a/b)³)`,
  where `B ≥ b > 0`, `|A| ≤ a` on the grid, and `A/B` is `L`-Lipschitz on `[0, x]`.
* `Gardiner.bdStat_ou_rate` — non-degenerate instance: the Ornstein–Uhlenbeck process
  `A(x) = -kx`, `B = D`.
-/
import SHSLib.Gardiner.Approx.KramersMoyal

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators Nat

noncomputable section

namespace Gardiner

/-- The stationary distribution (7.2.19) of the birth–death approximation (7.2.16), on the
lattice `x = kδ`: `P_s(kδ) = P_s(0) ∏_{j<k} [δA(jδ) + B(jδ)] / [-δA((j+1)δ) + B((j+1)δ)]`. -/
def bdStat (A B : ℝ → ℝ) (δ P0 : ℝ) (k : ℕ) : ℝ :=
  P0 * ∏ j ∈ range k, (δ * A (j * δ) + B (j * δ)) / (-δ * A ((j + 1 : ℕ) * δ) + B ((j + 1 : ℕ) * δ))

lemma bdStat_succ (A B : ℝ → ℝ) (δ P0 : ℝ) (k : ℕ) :
    bdStat A B δ P0 (k + 1) = bdStat A B δ P0 k
      * ((δ * A (k * δ) + B (k * δ)) / (-δ * A ((k + 1 : ℕ) * δ) + B ((k + 1 : ℕ) * δ))) := by
  simp only [bdStat, prod_range_succ, mul_assoc]

/-- **Detailed balance** for (7.2.19): the probability flux `t⁺(kδ) P_s(k) - t⁻((k+1)δ) P_s(k+1)`
vanishes. -/
theorem bdStat_flux (A B : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) (P0 : ℝ)
    (hw : ∀ j : ℕ, -δ * A (j * δ) + B (j * δ) ≠ 0) (k : ℕ) :
    bdRate A B δ true (k * δ) * bdStat A B δ P0 k
      = bdRate A B δ false ((k + 1 : ℕ) * δ) * bdStat A B δ P0 (k + 1) := by
  rw [bdStat_succ]
  have h := hw (k + 1)
  simp only [bdRate, if_true, Bool.false_eq_true, if_false]
  generalize A (k * δ) = a0 at *
  generalize B (k * δ) = b0 at *
  generalize A ((k + 1 : ℕ) * δ) = a1 at *
  generalize B ((k + 1 : ℕ) * δ) = b1 at *
  generalize bdStat A B δ P0 k = p at *
  rw [show 1 * a0 / (2 * δ) + b0 / (2 * δ ^ 2) = (δ * a0 + b0) / (2 * δ ^ 2) by
      field_simp,
    show -1 * a1 / (2 * δ) + b1 / (2 * δ ^ 2) = (-δ * a1 + b1) / (2 * δ ^ 2) by
      field_simp]
  generalize -δ * a1 + b1 = w at *
  field_simp

/-- (7.2.19) solves the **stationary master equation** of the birth–death process (7.2.16) on
`ℕ` (with no death out of `k = 0`): at `k = 0`, `t⁻(δ)P(1) - t⁺(0)P(0) = 0`, and for `k ≥ 1`,
`t⁺((k-1)δ)P(k-1) + t⁻((k+1)δ)P(k+1) - [t⁺(kδ) + t⁻(kδ)]P(k) = 0`. -/
theorem bdStat_stationary (A B : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) (P0 : ℝ)
    (hw : ∀ j : ℕ, -δ * A (j * δ) + B (j * δ) ≠ 0) :
    bdRate A B δ false ((1 : ℕ) * δ) * bdStat A B δ P0 1
        - bdRate A B δ true ((0 : ℕ) * δ) * bdStat A B δ P0 0 = 0 ∧
      ∀ k : ℕ, bdRate A B δ true (k * δ) * bdStat A B δ P0 k
        + bdRate A B δ false ((k + 2 : ℕ) * δ) * bdStat A B δ P0 (k + 2)
        - (bdRate A B δ true ((k + 1 : ℕ) * δ) + bdRate A B δ false ((k + 1 : ℕ) * δ))
          * bdStat A B δ P0 (k + 1) = 0 := by
  refine ⟨?_, fun k => ?_⟩
  · rw [bdStat_flux A B hδ P0 hw 0]; ring
  · have h1 := bdStat_flux A B hδ P0 hw k
    have h2 : bdRate A B δ true ((k + 1 : ℕ) * δ) * bdStat A B δ P0 (k + 1)
        = bdRate A B δ false ((k + 2 : ℕ) * δ) * bdStat A B δ P0 (k + 2) :=
      bdStat_flux A B hδ P0 hw (k + 1)
    linear_combination h1 - h2

/-- The second line of (7.2.19):
`P_s(kδ) = P_s(0) [-δA(0) + B(0)]/[δA(kδ) + B(kδ)] ∏_{j=0}^{k} (1 + δA/B)/(1 - δA/B)`. -/
theorem bdStat_eq_ratio (A B : ℝ → ℝ) (δ P0 : ℝ) (hB : ∀ j : ℕ, B (j * δ) ≠ 0)
    (hu : ∀ j : ℕ, δ * A (j * δ) + B (j * δ) ≠ 0) (hw : ∀ j : ℕ, -δ * A (j * δ) + B (j * δ) ≠ 0)
    (k : ℕ) :
    bdStat A B δ P0 k = P0 * ((-δ * A ((0 : ℕ) * δ) + B ((0 : ℕ) * δ)) / (δ * A (k * δ) + B (k * δ)))
      * ∏ j ∈ range (k + 1), (1 + δ * A (j * δ) / B (j * δ)) / (1 - δ * A (j * δ) / B (j * δ)) := by
  have hq : ∀ j : ℕ, (1 + δ * A (j * δ) / B (j * δ)) / (1 - δ * A (j * δ) / B (j * δ))
      = (δ * A (j * δ) + B (j * δ)) / (-δ * A (j * δ) + B (j * δ)) := by
    intro j
    have hBj := hB j
    generalize A (j * δ) = a0 at *
    generalize B (j * δ) = b0 at *
    have h1 : 1 - δ * a0 / b0 = (-δ * a0 + b0) / b0 := by
      field_simp; ring
    have h2 : 1 + δ * a0 / b0 = (δ * a0 + b0) / b0 := by
      field_simp; ring
    rw [h1, h2, div_div_div_cancel_right₀ hBj]
  simp only [hq]
  induction k with
  | zero =>
    simp only [bdStat, Finset.range_zero, Finset.prod_empty, mul_one, zero_add, Finset.range_one,
      Finset.prod_singleton]
    have h1 := hu 0; have h2 := hw 0
    generalize A ((0 : ℕ) * δ) = a0 at *
    generalize B ((0 : ℕ) * δ) = b0 at *
    field_simp
    rw [mul_div_assoc, div_self (by simpa [neg_mul] using h2), mul_one]
  | succ k ih =>
    rw [bdStat_succ, ih, prod_range_succ _ (k + 1)]
    have h1 := hu k; have h2 := hu (k + 1); have h3 := hw (k + 1)
    generalize A (k * δ) = a0 at *
    generalize B (k * δ) = b0 at *
    generalize A ((k + 1 : ℕ) * δ) = a1 at *
    generalize B ((k + 1 : ℕ) * δ) = b1 at *
    field_simp

/-! ### The limit (7.2.20)–(7.2.21) with a rate -/

/-- `|log(1 - v)| ≤ 2|v|` for `|v| ≤ 1/2`. -/
lemma abs_log_one_sub_le {v : ℝ} (hv : |v| ≤ 1 / 2) : |Real.log (1 - v)| ≤ 2 * |v| := by
  have h := Real.abs_log_sub_add_sum_range_le (x := v) (by linarith) 0
  simp only [Finset.range_zero, sum_empty, zero_add, pow_one] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg v]

/-- `|log(1 + v) - log(1 - v) - 2v| ≤ 4|v|³` for `|v| ≤ 1/2`: the step from (7.2.19) to
(7.2.20). -/
lemma log_ratio_cubic {v : ℝ} (hv : |v| ≤ 1 / 2) :
    |Real.log (1 + v) - Real.log (1 - v) - 2 * v| ≤ 4 * |v| ^ 3 := by
  have key : ∀ w : ℝ, |w| ≤ 1 / 2 → |w + w ^ 2 / 2 + Real.log (1 - w)| ≤ 2 * |w| ^ 3 := by
    intro w hw
    have h := Real.abs_log_sub_add_sum_range_le (x := w) (by linarith) 2
    simp only [sum_range_succ, Finset.range_zero, sum_empty] at h
    norm_num at h
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg (abs_nonneg w) 3]
  have h1 := key v hv
  have h2 := key (-v) (by rwa [abs_neg])
  rw [abs_neg, sub_neg_eq_add, add_comm 1 v] at h2
  rw [add_comm 1 v]
  have e : Real.log (v + 1) - Real.log (1 - v) - 2 * v
      = (-v + (-v) ^ 2 / 2 + Real.log (v + 1)) - (v + v ^ 2 / 2 + Real.log (1 - v)) := by ring
  rw [e]
  calc _ ≤ |-v + (-v) ^ 2 / 2 + Real.log (v + 1)| + |v + v ^ 2 / 2 + Real.log (1 - v)| :=
        abs_sub _ _
    _ ≤ _ := by linarith

/-- **(7.2.20)–(7.2.21) with an explicit rate.**  Let `δ > 0`, `x = Nδ`, `B ≥ b > 0` and
`|A| ≤ a` at the grid points of `[0, x]`, `δa/b ≤ 1/2`, and let `A/B` be `L`-Lipschitz on
`[0, x]`.  Then the stationary distribution (7.2.19) satisfies
`|log P_s(x) - [log P_s(0) + log B(0) - log B(x) + 2∫₀ˣ A/B]| ≤ δ (2Lx + 4a/b + 4xδ(a/b)³)`.
In particular `P_s(x) → 𝒩 B(x)⁻¹ exp[2∫₀ˣ A/B]` as `δ → 0`, at rate `O(δ)`. -/
theorem bdStat_log_rate (A B : ℝ → ℝ) {δ P0 a b : ℝ} (L : NNReal) (N : ℕ) (hδ : 0 < δ)
    (hP0 : 0 < P0) (hb : 0 < b) (hB : ∀ j ≤ N, b ≤ B (j * δ)) (hA : ∀ j ≤ N, |A (j * δ)| ≤ a)
    (hsmall : δ * a / b ≤ 1 / 2)
    (hg : LipschitzOnWith L (fun z => A z / B z) (Icc 0 (N * δ))) :
    |Real.log (bdStat A B δ P0 N) - (Real.log P0 + Real.log (B 0) - Real.log (B (N * δ))
        + 2 * ∫ z in (0 : ℝ)..N * δ, A z / B z)|
      ≤ δ * (2 * L * (N * δ) + 4 * a / b + 4 * (N * δ) * δ * (a / b) ^ 3) := by
  set g : ℝ → ℝ := fun z => A z / B z with hgdef
  set v : ℕ → ℝ := fun j => δ * g (j * δ) with hv
  have ha : 0 ≤ a := (abs_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hBpos : ∀ j ≤ N, 0 < B (j * δ) := fun j hj => hb.trans_le (hB j hj)
  have hvle : ∀ j ≤ N, |v j| ≤ δ * a / b := by
    intro j hj
    simp only [hv, hgdef, abs_mul, abs_div, abs_of_pos hδ, abs_of_pos (hBpos j hj)]
    rw [mul_div_assoc]
    gcongr
    · exact hA j hj
    · exact hB j hj
  have hvh : ∀ j ≤ N, |v j| ≤ 1 / 2 := fun j hj => (hvle j hj).trans hsmall
  have hpos1 : ∀ j ≤ N, 0 < 1 + v j := fun j hj => by
    have := neg_abs_le (v j); linarith [hvh j hj]
  have hpos2 : ∀ j ≤ N, 0 < 1 - v j := fun j hj => by
    have := le_abs_self (v j); linarith [hvh j hj]
  have hu : ∀ j ≤ N, δ * A (j * δ) + B (j * δ) = B (j * δ) * (1 + v j) := fun j hj => by
    have hB' := (hBpos j hj).ne'
    simp only [hv, hgdef]
    generalize A (j * δ) = a0 at *
    generalize B (j * δ) = b0 at *
    field_simp
    ring
  have hw : ∀ j ≤ N, -δ * A (j * δ) + B (j * δ) = B (j * δ) * (1 - v j) := fun j hj => by
    have hB' := (hBpos j hj).ne'
    simp only [hv, hgdef]
    generalize A (j * δ) = a0 at *
    generalize B (j * δ) = b0 at *
    field_simp
    ring
  have logu : ∀ j ≤ N, Real.log (δ * A (j * δ) + B (j * δ))
      = Real.log (B (j * δ)) + Real.log (1 + v j) := fun j hj => by
    rw [hu j hj, Real.log_mul (hBpos j hj).ne' (hpos1 j hj).ne']
  have logw : ∀ j ≤ N, Real.log (-δ * A (j * δ) + B (j * δ))
      = Real.log (B (j * δ)) + Real.log (1 - v j) := fun j hj => by
    rw [hw j hj, Real.log_mul (hBpos j hj).ne' (hpos2 j hj).ne']
  -- the logarithm of the product
  have hlog : Real.log (bdStat A B δ P0 N) = Real.log P0
      + ∑ j ∈ range N, (Real.log (1 + v j) - Real.log (1 - v j))
      + (Real.log (B ((0 : ℕ) * δ)) + Real.log (1 - v 0))
      - (Real.log (B (N * δ)) + Real.log (1 - v N)) := by
    have hne : ∀ j ∈ range N, (δ * A (j * δ) + B (j * δ))
        / (-δ * A ((j + 1 : ℕ) * δ) + B ((j + 1 : ℕ) * δ)) ≠ 0 := by
      intro j hj
      have hj' := mem_range.1 hj
      rw [hu j hj'.le, hw (j + 1) hj']
      exact div_ne_zero (mul_ne_zero (hBpos j hj'.le).ne' (hpos1 j hj'.le).ne')
        (mul_ne_zero (hBpos _ hj').ne' (hpos2 _ hj').ne')
    rw [bdStat, Real.log_mul hP0.ne' (prod_ne_zero_iff.2 hne), Real.log_prod hne]
    have : ∀ j ∈ range N, Real.log ((δ * A (j * δ) + B (j * δ))
        / (-δ * A ((j + 1 : ℕ) * δ) + B ((j + 1 : ℕ) * δ)))
        = (Real.log (1 + v j) - Real.log (1 - v j))
          + ((Real.log (B (j * δ)) + Real.log (1 - v j))
            - (Real.log (B ((j + 1 : ℕ) * δ)) + Real.log (1 - v (j + 1)))) := by
      intro j hj
      have hj' := mem_range.1 hj
      have n1 : δ * A (j * δ) + B (j * δ) ≠ 0 := by
        rw [hu j hj'.le]; exact mul_ne_zero (hBpos j hj'.le).ne' (hpos1 j hj'.le).ne'
      have n2 : -δ * A ((j + 1 : ℕ) * δ) + B ((j + 1 : ℕ) * δ) ≠ 0 := by
        rw [hw (j + 1) hj']; exact mul_ne_zero (hBpos _ hj').ne' (hpos2 _ hj').ne'
      rw [Real.log_div n1 n2, logu j hj'.le, logw (j + 1) hj']
      ring
    rw [sum_congr rfl this, sum_add_distrib,
      sum_range_sub' (fun j => Real.log (B (j * δ)) + Real.log (1 - v j))]
    ring
  -- the Riemann sum
  have hint : ∫ z in (0 : ℝ)..N * δ, g z = ∑ j ∈ range N, ∫ z in (j * δ : ℝ)..((j + 1 : ℕ) * δ), g z := by
    have hc : ContinuousOn g (Icc 0 (N * δ)) := hg.continuousOn
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) * δ) (n := N) (fun k hk => by
        refine (hc.mono ?_).intervalIntegrable
        rw [Set.uIcc_of_le (by push_cast; nlinarith)]
        refine Icc_subset_Icc (by positivity) ?_
        have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
        nlinarith)
    simp only [Nat.cast_zero, zero_mul] at this
    exact this.symm
  have hcell : ∀ j < N, |v j - ∫ z in (j * δ : ℝ)..((j + 1 : ℕ) * δ), g z| ≤ L * δ ^ 2 := by
    intro j hj
    have hc : ContinuousOn g (Icc 0 (N * δ)) := hg.continuousOn
    have hsub : uIcc ((j : ℝ) * δ) ((j + 1 : ℕ) * δ) ⊆ Icc 0 (N * δ) := by
      rw [Set.uIcc_of_le (by push_cast; nlinarith)]
      refine Icc_subset_Icc (by positivity) ?_
      have : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
      nlinarith
    have hii : IntervalIntegrable g volume ((j : ℝ) * δ) ((j + 1 : ℕ) * δ) :=
      (hc.mono hsub).intervalIntegrable
    have e : v j - ∫ z in (j * δ : ℝ)..((j + 1 : ℕ) * δ), g z
        = -∫ z in (j * δ : ℝ)..((j + 1 : ℕ) * δ), (g z - g (j * δ)) := by
      rw [intervalIntegral.integral_sub hii intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      simp only [hv]; push_cast; ring
    rw [e, abs_neg]
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (j : ℝ) * δ) (b := ((j + 1 : ℕ) : ℝ) * δ) (C := L * δ)
      (f := fun z => g z - g (j * δ)) (fun z hz => by
        have hz' : z ∈ Icc ((j : ℝ) * δ) ((j + 1 : ℕ) * δ) := by
          rw [Set.uIoc_of_le (by push_cast; nlinarith)] at hz; exact ⟨hz.1.le, hz.2⟩
        have hzI := hsub (Set.uIcc_of_le (by push_cast; nlinarith : (j : ℝ) * δ ≤ ((j + 1 : ℕ) : ℝ) * δ)
          ▸ hz')
        have hjI : (j : ℝ) * δ ∈ Icc 0 (N * δ) := hsub left_mem_uIcc
        have := hg.dist_le_mul z hzI _ hjI
        rw [Real.dist_eq, Real.dist_eq] at this
        rw [Real.norm_eq_abs]
        refine this.trans ?_
        gcongr
        push_cast at hz' ⊢
        rw [abs_of_nonneg (by linarith [hz'.1])]
        linarith [hz'.2])
    rw [Real.norm_eq_abs] at hb'
    refine hb'.trans (le_of_eq ?_)
    push_cast
    rw [show ((j : ℝ) + 1) * δ - j * δ = δ by ring, abs_of_pos hδ]
    ring
  -- assemble
  have hcub : ∀ j < N, |Real.log (1 + v j) - Real.log (1 - v j) - 2 * v j| ≤ 4 * (δ * a / b) ^ 3 :=
    fun j hj => (log_ratio_cubic (hvh j hj.le)).trans (by
      gcongr; exact hvle j hj.le)
  have hb0 := abs_log_one_sub_le (hvh 0 (Nat.zero_le _))
  have hbN := abs_log_one_sub_le (hvh N le_rfl)
  have hv0 := hvle 0 (Nat.zero_le _)
  have hvN := hvle N le_rfl
  rw [hlog, hint]
  simp only [Nat.cast_zero, zero_mul]
  have E : Real.log P0 + ∑ j ∈ range N, (Real.log (1 + v j) - Real.log (1 - v j))
      + (Real.log (B 0) + Real.log (1 - v 0)) - (Real.log (B (N * δ)) + Real.log (1 - v N))
      - (Real.log P0 + Real.log (B 0) - Real.log (B (N * δ))
        + 2 * ∑ j ∈ range N, ∫ z in (j * δ : ℝ)..((j + 1 : ℕ) * δ), g z)
      = ∑ j ∈ range N, (Real.log (1 + v j) - Real.log (1 - v j) - 2 * v j)
        + 2 * ∑ j ∈ range N, (v j - ∫ z in (j * δ : ℝ)..((j + 1 : ℕ) * δ), g z)
        + Real.log (1 - v 0) - Real.log (1 - v N) := by
    simp only [sum_sub_distrib, mul_sub, mul_sum]; ring
  rw [E]
  have S1 : |∑ j ∈ range N, (Real.log (1 + v j) - Real.log (1 - v j) - 2 * v j)|
      ≤ N * (4 * (δ * a / b) ^ 3) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun j hj => hcub j (mem_range.1 hj)).trans ?_
    simp
  have S2 : |∑ j ∈ range N, (v j - ∫ z in (j * δ : ℝ)..((j + 1 : ℕ) * δ), g z)| ≤ N * (L * δ ^ 2) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun j hj => hcell j (mem_range.1 hj)).trans ?_
    simp
  have tri : ∀ p q r s : ℝ, |p + 2 * q + r - s| ≤ |p| + 2 * |q| + |r| + |s| := by
    intro p q r s
    have := abs_add_le (p + 2 * q + r) (-s)
    have := abs_add_le (p + 2 * q) r
    have := abs_add_le p (2 * q)
    rw [abs_neg] at *
    rw [abs_mul, abs_two] at *
    rw [sub_eq_add_neg]
    linarith
  refine (tri _ _ _ _).trans ?_
  have e1 : (N : ℝ) * (4 * (δ * a / b) ^ 3) = δ * (4 * (N * δ) * δ * (a / b) ^ 3) := by ring
  have e2 : δ * (2 * L * (N * δ) + 4 * a / b + 4 * (N * δ) * δ * (a / b) ^ 3)
      = 2 * (N * (L * δ ^ 2)) + 2 * (2 * (δ * a / b)) + δ * (4 * (N * δ) * δ * (a / b) ^ 3) := by
    ring
  rw [e2]
  linarith

/-- A non-degenerate instance of `Gardiner.bdStat_log_rate`: the Ornstein–Uhlenbeck process
`A(x) = -kx`, `B(x) = D > 0` (for which (7.2.21) is the Gaussian `exp(-kx²/D)`), on `[0, Nδ]`
with `δ ≤ D/(2k(Nδ))`. -/
theorem bdStat_ou_rate {k D δ P0 : ℝ} (N : ℕ) (hk : 0 ≤ k) (hD : 0 < D) (hδ : 0 < δ)
    (hP0 : 0 < P0) (hsmall : δ * (k * (N * δ)) / D ≤ 1 / 2) :
    |Real.log (bdStat (fun x => -k * x) (fun _ => D) δ P0 N)
        - (Real.log P0 - k * (N * δ) ^ 2 / D)|
      ≤ δ * (2 * (k / D) * (N * δ) + 4 * (k * (N * δ)) / D
        + 4 * (N * δ) * δ * (k * (N * δ) / D) ^ 3) := by
  have h := bdStat_log_rate (fun x => -k * x) (fun _ => D) (a := k * (N * δ)) (b := D)
    ⟨k / D, by positivity⟩ N hδ hP0 hD (fun _ _ => le_rfl) (fun j hj => by
      rw [abs_mul, abs_neg, abs_of_nonneg hk, abs_of_nonneg (by positivity)]
      gcongr) hsmall (by
      refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y => ?_)
      simp only [Real.dist_eq, NNReal.coe_mk]
      rw [show -k * x / D - -k * y / D = -(k / D) * (x - y) by ring, abs_mul, abs_neg,
        abs_of_nonneg (by positivity)])
  have hI : ∫ z in (0 : ℝ)..N * δ, -k * z / D = -(k * (N * δ) ^ 2 / (2 * D)) := by
    simp_rw [show ∀ z : ℝ, -k * z / D = (-k / D) * z from fun z => by ring]
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hI] at h
  simp only [NNReal.coe_mk] at h
  convert h using 2
  ring
