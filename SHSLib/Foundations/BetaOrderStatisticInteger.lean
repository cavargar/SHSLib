/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Order statistics of a sample of powers of uniforms

Batches 193–194 expressed the moments of a Beta order statistic as ratios of
Beta functions, `R(c) = B(j+1, m+1+c)/B(j+1, m+1)` and
`R'(c) = B(j+1+c, m+1)/B(j+1, m+1)`.  When the exponent `c` is a natural number
these ratios are *finite products of rational numbers*, by the recursion
`B(x, y+1) = B(x,y)·y/(x+y)` iterated.  This module records the product forms
and uses them for the parent laws with an integer power.

The interesting case is the parent `Beta(1/k, 1)`, the law of `U^k` for a
uniform `U`: the `(j+1)`-st order statistic of `n = j+m+1` such variables has
mean

  `∏_{i<k} (j+1+i)/(n+1+i)`,

which is squeezed between `((j+1)/(n+1))^k` and `((j+k)/(n+k))^k`.  Both bounds
are the parent quantile evaluated at a rank fraction, so this is an explicit,
non-asymptotic form of the statement that a sample quantile sits at the parent
quantile of its rank fraction.
-/
import SHSLib.Foundations.BetaOrderStatisticConcentration

open MeasureTheory ProbabilityTheory Set

namespace SHSLib.Trigamma

/-! ### The Beta-function ratios at a natural exponent -/

/-- The right-hand companion of `betaFn_add_nat_div`:
`B(a, b+k)/B(a,b) = ∏_{i<k} (b+i)/(a+b+i)`. -/
theorem betaFn_add_nat_div_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    betaFn a (b + k) / betaFn a b = ∏ i ∈ Finset.range k, (b + i) / (a + b + i) := by
  rw [betaFn_symm a (b + k), betaFn_symm a b, betaFn_add_nat_div hb ha k]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [add_comm b a]

/-- The reflected ratio of batch 193 at a natural exponent. -/
theorem betaOrderRatio_natCast (j m k : ℕ) :
    betaOrderRatio j m (k : ℝ)
      = ∏ i ∈ Finset.range k, ((m : ℝ) + 1 + i) / ((j : ℝ) + (m : ℝ) + 2 + i) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  rw [betaOrderRatio, betaFn_add_nat_div_right hj hm k]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  ring_nf

/-- The direct ratio of batch 194 at a natural exponent. -/
theorem betaOrderRatioLeft_natCast (j m k : ℕ) :
    betaOrderRatioLeft j m (k : ℝ)
      = ∏ i ∈ Finset.range k, ((j : ℝ) + 1 + i) / ((j : ℝ) + (m : ℝ) + 2 + i) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  rw [betaOrderRatioLeft, betaFn_add_nat_div hj hm k]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  ring_nf

/-! ### The parent `Beta(1/k, 1)`, the law of `U^k` -/

/-- **The mean of the `(j+1)`-st order statistic of a sample of `n = j+m+1`
independent `k`-th powers of uniforms** is `∏_{i<k} (j+1+i)/(n+1+i)`. -/
theorem integral_orderStat_powerSample (k : ℕ) (hk : 0 < k) (j m : ℕ) :
    ∫ w, unifOrderStat j m w
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure (1 / (k : ℝ)) 1))
      = ∏ i ∈ Finset.range k, ((j : ℝ) + 1 + i) / ((j : ℝ) + (m : ℝ) + 2 + i) := by
  have hk' : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have ha : (0:ℝ) < 1 / (k : ℝ) := by positivity
  rw [integral_orderStat_betaOneRightSample ha j m,
    show (1 : ℝ) / (1 / (k : ℝ)) = (k : ℝ) by field_simp,
    betaOrderRatioLeft_natCast j m k]

/-- Each factor of the product lies between `(j+1)/(n+1)` and `(j+k)/(n+k)`. -/
theorem orderStat_power_factor_mem (j m k i : ℕ) (hi : i ∈ Finset.range k) :
    ((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2)
        ≤ ((j : ℝ) + 1 + i) / ((j : ℝ) + (m : ℝ) + 2 + i)
      ∧ ((j : ℝ) + 1 + i) / ((j : ℝ) + (m : ℝ) + 2 + i)
        ≤ ((j : ℝ) + (k : ℝ)) / ((j : ℝ) + (m : ℝ) + 1 + (k : ℝ)) := by
  have hik : (i : ℝ) + 1 ≤ (k : ℝ) := by
    have : i + 1 ≤ k := Finset.mem_range.1 hi
    exact_mod_cast this
  have hi0 : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hd : (0:ℝ) < (j : ℝ) + (m : ℝ) + 2 := by positivity
  have hdi : (0:ℝ) < (j : ℝ) + (m : ℝ) + 2 + i := by positivity
  have hdk : (0:ℝ) < (j : ℝ) + (m : ℝ) + 1 + (k : ℝ) := by
    have : (1:ℝ) ≤ (k : ℝ) := by linarith
    positivity
  constructor
  · rw [div_le_div_iff₀ hd hdi]
    have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  · rw [div_le_div_iff₀ hdi hdk]
    have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith

/-- **The mean of the order statistic of a sample of `k`-th powers of uniforms
is squeezed between two powers of rank fractions**:
`((j+1)/(n+1))^k ≤ E[X_{(j+1)}] ≤ ((j+k)/(n+k))^k`.  Both bounds are the parent
quantile `p ↦ p^k` evaluated at a rank fraction. -/
theorem integral_orderStat_powerSample_bounds (k : ℕ) (hk : 0 < k) (j m : ℕ) :
    (((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2)) ^ k
        ≤ ∫ w, unifOrderStat j m w
            ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure (1 / (k : ℝ)) 1))
      ∧ ∫ w, unifOrderStat j m w
            ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure (1 / (k : ℝ)) 1))
        ≤ (((j : ℝ) + (k : ℝ)) / ((j : ℝ) + (m : ℝ) + 1 + (k : ℝ))) ^ k := by
  rw [integral_orderStat_powerSample k hk j m]
  have hd : (0:ℝ) < (j : ℝ) + (m : ℝ) + 2 := by positivity
  have hlo : (0:ℝ) ≤ ((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) := by positivity
  constructor
  · have hconst : (((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2)) ^ k
        = ∏ _i ∈ Finset.range k, ((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hconst]
    exact Finset.prod_le_prod (fun i _ => hlo)
      (fun i hi => (orderStat_power_factor_mem j m k i hi).1)
  · have hfac : ∀ i ∈ Finset.range k,
        (0:ℝ) ≤ ((j : ℝ) + 1 + i) / ((j : ℝ) + (m : ℝ) + 2 + i) := by
      intro i _
      have hi0 : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      positivity
    have hconst : (((j : ℝ) + (k : ℝ)) / ((j : ℝ) + (m : ℝ) + 1 + (k : ℝ))) ^ k
        = ∏ _i ∈ Finset.range k, ((j : ℝ) + (k : ℝ)) / ((j : ℝ) + (m : ℝ) + 1 + (k : ℝ)) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hconst]
    exact Finset.prod_le_prod hfac
      (fun i hi => (orderStat_power_factor_mem j m k i hi).2)

/-! ### The reflected family at a natural exponent -/

/-- **The mean of the `(j+1)`-st order statistic of a sample of `n = j+m+1`
independent `Beta(1, 1/k)` variables** is `1 − ∏_{i<k} (m+1+i)/(n+1+i)`. -/
theorem integral_orderStat_betaOneOverK (k : ℕ) (hk : 0 < k) (j m : ℕ) :
    ∫ w, unifOrderStat j m w
        ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure 1 (1 / (k : ℝ))))
      = 1 - ∏ i ∈ Finset.range k, ((m : ℝ) + 1 + i) / ((j : ℝ) + (m : ℝ) + 2 + i) := by
  have hk' : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hb : (0:ℝ) < 1 / (k : ℝ) := by positivity
  rw [integral_orderStat_betaOneSample hb j m,
    show (1 : ℝ) / (1 / (k : ℝ)) = (k : ℝ) by field_simp,
    betaOrderRatio_natCast j m k]

end SHSLib.Trigamma
