/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The digamma series `ψ(x) − ψ(1) = ∑_{k ≥ 0} (1/(k+1) − 1/(x+k))`

The series for `ψ' = (log Γ)''` proved in
`SHSLib/Foundations/TrigammaSeries.lean` integrates: the function

  `F(x) = ∑_{k ≥ 0} (1/(k+1) − 1/(x+k))`

is differentiable on `(0, ∞)` with `F' = ψ'` (termwise differentiation, legal
because the differentiated series is dominated by a convergent series on every
`(a, ∞)` with `a > 0`), and `F(1) = 0`, so `ψ − F` is constant on the connected
set `(0, ∞)`:

  `ψ(x) = ψ(1) + ∑_{k ≥ 0} (1/(k+1) − 1/(x+k))`
  (`SHSLib.Trigamma.digamma_sub_digamma_one`).

The classical form of this identity has `−γ` in place of `ψ(1)`; identifying
`ψ(1) = −γ` needs the asymptotics of `Γ`, which this development deliberately
avoids, so the statement is kept in the `γ`-free difference form.  Along the
integers it specialises to `ψ(n+1) = ψ(1) + H_n`.

Also recorded here, as immediate consequences of `trigamma_pos` and
`tetragamma_neg`: `ψ` is strictly increasing, `log Γ` is strictly convex, and
`ψ` is strictly concave on `(0, ∞)`.
-/
import SHSLib.Foundations.Tetragamma

open Real Set Filter

namespace SHSLib.Trigamma

/-- The digamma function `ψ = (log Γ)'`. -/
noncomputable def digamma (x : ℝ) : ℝ := deriv logGamma x

theorem digamma_def (x : ℝ) : digamma x = deriv logGamma x := rfl

theorem deriv_digamma {x : ℝ} (hx : 0 < x) : HasDerivAt digamma (trigamma x) x :=
  (differentiableAt_deriv_logGamma hx).hasDerivAt

theorem digamma_recurrence {x : ℝ} (hx : 0 < x) : digamma (x + 1) = digamma x + 1 / x :=
  digamma_add_one hx

/-! ### Termwise differentiation of the digamma series -/

/-- The `k`-th term of the digamma series, `1/(k+1) − 1/(x+k)`. -/
noncomputable def digammaTerm (k : ℕ) (x : ℝ) : ℝ := 1 / ((k : ℝ) + 1) - 1 / (x + k)

theorem hasDerivAt_digammaTerm (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (digammaTerm k) (1 / (x + (k : ℝ)) ^ 2) x := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hne : x + (k : ℝ) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun w : ℝ => w + (k : ℝ)) 1 x := (hasDerivAt_id x).add_const _
  have h2 : HasDerivAt (fun w : ℝ => (w + (k : ℝ))⁻¹) (-1 / (x + (k : ℝ)) ^ 2) x := h1.inv hne
  have h3 := h2.const_sub (1 / ((k : ℝ) + 1))
  show HasDerivAt (fun z : ℝ => 1 / ((k : ℝ) + 1) - 1 / (z + (k : ℝ))) (1 / (x + (k : ℝ)) ^ 2) x
  simpa [one_div, neg_div] using h3

theorem digammaTerm_one (k : ℕ) : digammaTerm k 1 = 0 := by
  simp [digammaTerm, add_comm]

/-- The digamma series is differentiable on `(a, ∞)` for every `a > 0`, with
derivative the trigamma series, i.e. `ψ'`. -/
theorem hasDerivAt_digammaSeries {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {y : ℝ} (hy : a < y) :
    HasDerivAt (fun z : ℝ => ∑' k : ℕ, digammaTerm k z) (trigamma y) y := by
  have hderiv : ∀ (k : ℕ), ∀ z ∈ Ioi a, HasDerivAt (digammaTerm k) (1 / (z + (k : ℝ)) ^ 2) z :=
    fun k z hz => hasDerivAt_digammaTerm k (lt_trans ha hz)
  have hbound : ∀ (k : ℕ), ∀ z ∈ Ioi a, ‖1 / (z + (k : ℝ)) ^ 2‖ ≤ 1 / (a + (k : ℝ)) ^ 2 := by
    intro k z hz
    have hz' : a < z := hz
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpos : (0 : ℝ) < 1 / (z + (k : ℝ)) ^ 2 := by
      have : (0 : ℝ) < z + k := by linarith
      positivity
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hsum1 : Summable fun k : ℕ => digammaTerm k 1 := by
    simp [digammaTerm_one]
  have h := hasDerivAt_tsum_of_isPreconnected (u := fun k : ℕ => 1 / (a + (k : ℝ)) ^ 2)
    (g := digammaTerm) (g' := fun k z => 1 / (z + (k : ℝ)) ^ 2)
    (summable_inv_sq_shift ha) isOpen_Ioi isPreconnected_Ioi hderiv hbound
    (mem_Ioi.mpr ha1) hsum1 (mem_Ioi.mpr hy)
  rwa [← trigamma_eq_tsum (lt_trans ha hy)] at h

/-! ### The series -/

/-- **The digamma series.**  For every `x > 0`,
`ψ(x) − ψ(1) = ∑_{k ≥ 0} (1/(k+1) − 1/(x+k))`. -/
theorem digamma_sub_digamma_one {x : ℝ} (hx : 0 < x) :
    digamma x - digamma 1 = ∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / (x + k)) := by
  have hmin : (0 : ℝ) < min x 1 := lt_min hx one_pos
  have hminx : min x 1 ≤ x := min_le_left _ _
  have hmin1 : min x 1 ≤ 1 := min_le_right _ _
  set a : ℝ := min x 1 / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hax : a < x := by rw [ha_def]; linarith
  have ha1 : a < 1 := by rw [ha_def]; linarith
  set H : ℝ → ℝ := fun z => digamma z - ∑' k : ℕ, digammaTerm k z with hH_def
  have hH : ∀ z ∈ Ioi a, HasDerivAt H 0 z := by
    intro z hz
    have hz0 : 0 < z := lt_trans ha hz
    have h := (deriv_digamma hz0).sub (hasDerivAt_digammaSeries ha ha1 (mem_Ioi.mp hz))
    simpa [hH_def] using h
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_fderiv_eq_zero (𝕜 := ℝ) isPreconnected_Ioi
    (fun z hz => ((hH z hz).differentiableAt).differentiableWithinAt)
    (fun z hz => by simpa using (hH z hz).hasFDerivAt.fderiv)
  have hx' : H x = H 1 := by rw [hc x (mem_Ioi.mpr hax), hc 1 (mem_Ioi.mpr ha1)]
  have h1 : (∑' k : ℕ, digammaTerm k 1) = 0 := by
    simp [digammaTerm_one]
  have hkey : digamma x - ∑' k : ℕ, digammaTerm k x = digamma 1 := by
    simpa [hH_def, h1] using hx'
  simp only [digammaTerm] at hkey
  linarith

/-- The digamma values along the integers: `ψ(n+1) = ψ(1) + H_n`. -/
theorem digamma_nat_add_one (n : ℕ) :
    digamma ((n : ℝ) + 1) = digamma 1 + ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h := digamma_recurrence hpos
      rw [show ((n + 1 : ℕ) : ℝ) + 1 = ((n : ℝ) + 1) + 1 by push_cast; ring, h, ih,
        Finset.sum_range_succ]
      ring

/-! ### Monotonicity and convexity -/

theorem deriv_digamma_eq (z : ℝ) : deriv digamma z = trigamma z := rfl

/-- `ψ` is strictly increasing on `(0, ∞)`. -/
theorem digamma_strictMonoOn : StrictMonoOn digamma (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) contDiffOn_deriv_logGamma.continuousOn ?_
  intro z hz
  rw [interior_Ioi] at hz
  rw [deriv_digamma_eq]
  exact trigamma_pos hz

/-- `ψ` is strictly concave on `(0, ∞)`. -/
theorem strictConcaveOn_digamma : StrictConcaveOn ℝ (Ioi 0) digamma := by
  refine strictConcaveOn_of_deriv2_neg (convex_Ioi 0)
    contDiffOn_deriv_logGamma.continuousOn ?_
  intro z hz
  rw [interior_Ioi] at hz
  have hz2 : deriv^[2] digamma z = tetragamma z := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, tetragamma_def]
    rfl
  rw [hz2]
  exact tetragamma_neg hz

/-- `log Γ` is strictly convex on `(0, ∞)`. -/
theorem strictConvexOn_logGamma : StrictConvexOn ℝ (Ioi 0) logGamma := by
  refine strictConvexOn_of_deriv2_pos (convex_Ioi 0) contDiffOn_logGamma.continuousOn ?_
  intro z hz
  rw [interior_Ioi] at hz
  have : deriv^[2] logGamma z = trigamma z := by
    simp [Function.iterate_succ_apply', trigamma_def]
  rw [this]
  exact trigamma_pos hz

end SHSLib.Trigamma
