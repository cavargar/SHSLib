/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Beta–Binomial identity as a statement about measures

`SHSLib/Foundations/BetaBinomial.lean` proves the analytic Beta–Binomial
identity

  `I_x(j+1, m+1) = ∑_{i=j+1}^{j+m+1} C(j+m+1,i) x^i (1−x)^{j+m+1−i}`,

and `SHSLib/Foundations/BetaMeasure.lean` identifies the left-hand side with the
mass the Beta law puts on `(-∞, x]`.  This module reads the right-hand side as
an honest probability as well, using Mathlib's binomial probability mass
function `PMF.binomial`.  The outcome is the familiar dictionary

  `P(Beta(j+1, m+1) ≤ x) = P(Bin(j+m+1, x) ≥ j+1)`,
  `P(Beta(j+1, m+1) > x) = P(Bin(j+m+1, x) ≤ j)`,

valid for every `x ∈ [0,1]`.

The proof is bookkeeping: `PMF.binomial_apply` evaluated at the index `j+1+i`
is exactly the `i`-th term `binomTailTerm j m i x` of the tail, once the
`ℝ≥0`-valued success probability `x.toNNReal` is converted back to `x` and the
exponent `(j+m+1) − (j+1+i)` is simplified to `m − i`; summing over the `m+1`
indices of the tail and applying `PMF.toMeasure_apply_finset` finishes it.
-/
import SHSLib.Foundations.BetaBinomial
import SHSLib.Foundations.BetaMeasure
import Mathlib.Probability.ProbabilityMassFunction.Binomial

open Real Set MeasureTheory ENNReal NNReal

namespace SHSLib.Trigamma

/-- The upper-tail event `{i ≥ j+1}` among the `n+1` possible counts of
successes in `n` Bernoulli trials. -/
def binomUpperTail (j n : ℕ) : Set (Fin (n + 1)) := {i | j + 1 ≤ (i : ℕ)}

/-- The complementary (lower-tail) event `{i ≤ j}`. -/
def binomLowerTail (j n : ℕ) : Set (Fin (n + 1)) := {i | (i : ℕ) ≤ j}

theorem compl_binomUpperTail (j n : ℕ) :
    (binomUpperTail j n)ᶜ = binomLowerTail j n := by
  ext i
  simp only [binomUpperTail, binomLowerTail, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  omega

/-- The value of the binomial pmf with `j+m+1` trials and success probability
`x ∈ [0,1]` at the count `j+1+i` is the `i`-th term of the Beta–Binomial
tail. -/
theorem binomial_apply_eq_ofReal_binomTailTerm (j m i : ℕ) (hi : i ≤ m) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    PMF.binomial x.toNNReal (Real.toNNReal_le_one.mpr hx1) (j + m + 1)
        ⟨j + 1 + i, by omega⟩ = ENNReal.ofReal (binomTailTerm j m i x) := by
  have h1x : (0:ℝ) ≤ 1 - x := by linarith
  have e1 : ((1:ℝ≥0∞) - ENNReal.ofReal x) = ENNReal.ofReal (1 - x) := by
    rw [ENNReal.ofReal_sub _ hx0]; simp
  rw [PMF.binomial_apply]
  simp only [Fin.val_last, show j + m + 1 - (j + 1 + i) = m - i by omega,
    show (↑x.toNNReal : ℝ≥0∞) = ENNReal.ofReal x from rfl, e1]
  rw [binomTailTerm, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hx0, ENNReal.ofReal_pow h1x, ENNReal.ofReal_natCast]
  ring

/-- The binomial upper tail, as a measure, is the analytic tail `binomTail`. -/
theorem binomial_toMeasure_upperTail (j m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (PMF.binomial x.toNNReal (Real.toNNReal_le_one.mpr hx1) (j + m + 1)).toMeasure
        (binomUpperTail j (j + m + 1)) = ENNReal.ofReal (binomTail j m x) := by
  have h1x : (0:ℝ) ≤ 1 - x := by linarith
  have hset : binomUpperTail j (j + m + 1)
      = ↑(Finset.filter (fun i : Fin (j + m + 1 + 1) => j + 1 ≤ (i : ℕ)) Finset.univ) := by
    ext i; simp [binomUpperTail]
  rw [hset, PMF.toMeasure_apply_finset, binomTail,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have h : (0:ℝ) ≤ (1 - x) ^ (m - i) := by positivity
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) h)]
  refine Finset.sum_nbij' (i := fun i : Fin (j + m + 1 + 1) => (i : ℕ) - (j + 1))
    (j := fun k => (⟨min (j + 1 + k) (j + m + 1), by omega⟩ : Fin (j + m + 1 + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_range]
    have := a.isLt; omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have := a.isLt
    apply Fin.ext; simp; omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp; omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hlt := a.isLt
    have h := binomial_apply_eq_ofReal_binomTailTerm j m ((a : ℕ) - (j + 1)) (by omega) hx0 hx1
    rw [← h]
    congr 1
    apply Fin.ext; simp; omega

/-- **The Beta CDF is a binomial upper tail.**  For `x ∈ [0,1]`,
`P(Beta(j+1, m+1) ≤ x) = P(Bin(j+m+1, x) ≥ j+1)`. -/
theorem betaMeasure_Iic_eq_binomial_upperTail (j m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1) (Set.Iic x)
      = (PMF.binomial x.toNNReal (Real.toNNReal_le_one.mpr hx1) (j + m + 1)).toMeasure
          (binomUpperTail j (j + m + 1)) := by
  rw [betaMeasure_Iic (by positivity) (by positivity) hx0 hx1, regBetaFn_nat_eq,
    binomial_toMeasure_upperTail j m hx0 hx1]

/-- **The Beta survival function is a binomial lower tail.**  For `x ∈ [0,1]`,
`P(Beta(j+1, m+1) > x) = P(Bin(j+m+1, x) ≤ j)`. -/
theorem betaMeasure_Ioi_eq_binomial_lowerTail (j m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1) (Set.Ioi x)
      = (PMF.binomial x.toNNReal (Real.toNNReal_le_one.mpr hx1) (j + m + 1)).toMeasure
          (binomLowerTail j (j + m + 1)) := by
  haveI : IsProbabilityMeasure (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    isProbabilityMeasure_betaMeasure (by positivity) (by positivity)
  have hbeta : betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1) (Set.Ioi x)
      = 1 - betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1) (Set.Iic x) := by
    rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _)]
    simp
  have hbin : (PMF.binomial x.toNNReal (Real.toNNReal_le_one.mpr hx1) (j + m + 1)).toMeasure
        (binomLowerTail j (j + m + 1))
      = 1 - (PMF.binomial x.toNNReal (Real.toNNReal_le_one.mpr hx1) (j + m + 1)).toMeasure
          (binomUpperTail j (j + m + 1)) := by
    rw [← compl_binomUpperTail, measure_compl (MeasurableSet.of_discrete) (measure_ne_top _ _)]
    simp
  rw [hbeta, hbin, betaMeasure_Iic_eq_binomial_upperTail j m hx0 hx1]

end SHSLib.Trigamma
