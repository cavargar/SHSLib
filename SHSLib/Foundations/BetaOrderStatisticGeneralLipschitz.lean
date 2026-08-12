/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The variance of an order statistic under a Lipschitz parent quantile

Batch 197 bounded the variance of the order statistic of a sample of `k`-th
powers of uniforms by `k²` times the variance of the rank variable, using that
the parent quantile `x ↦ x^k` is `k`-Lipschitz on `[0,1]`.  Nothing in that
argument is specific to a power: this module states it once, for an arbitrary
Beta parent whose quantile function is `L`-Lipschitz on `[0,1]`.

  `Var[X_{(j+1)}] ≤ L² · Var[P] = L² (j+1)(m+1)/((n+1)²(n+2)) ≤ L²/(4(n+2))`,

where `P ~ Beta(j+1, m+1)` is the rank variable.  Chebyshev then localizes the
order statistic about its mean at scale `L/√n`.

The hypothesis is a genuine restriction on the parent — it says the parent
density is bounded below on its support — and it is satisfied, with `L = k`, by
the power parents of batch 196.
-/
import SHSLib.Foundations.BetaOrderStatisticLipschitz

open MeasureTheory ProbabilityTheory Set

namespace SHSLib.Trigamma

/-- **The variance of an order statistic under a Lipschitz parent quantile.**
If the `Beta(a,b)` quantile function is `L`-Lipschitz on `[0,1]`, the variance
of the `(j+1)`-st order statistic of a sample of `n = j+m+1` such variables is
at most `L²` times the variance `(j+1)(m+1)/((n+1)²(n+2))` of the rank
variable. -/
theorem variance_orderStat_betaSample_le_of_lipschitz {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (j m : ℕ) {L : ℝ}
    (hlip : ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ q ∈ Set.Icc (0:ℝ) 1,
      |betaQuantileClamp a b p - betaQuantileClamp a b q| ≤ L * |p - q|) :
    variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
      ≤ L ^ 2 * (((j : ℝ) + 1) * ((m : ℝ) + 1)
          / (((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3))) := by
  have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  haveI : IsProbabilityMeasure (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    isProbabilityMeasure_betaMeasure hj hm
  set ν := betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1) with hν
  set e : ℝ := ((j : ℝ) + 1) / (((j : ℝ) + 1) + ((m : ℝ) + 1)) with he
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one (by positivity)]
    linarith
  have hQ2 : MemLp (betaQuantileClamp a b) 2 ν := by
    refine memLp_of_ae_bounded_betaMeasure hj hm
      (continuous_betaQuantileClamp ha hb).measurable.aestronglyMeasurable (C := 1) ?_ 2
    filter_upwards with p
    have h := betaQuantileClamp_mem_Icc ha hb p
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have hstep1 : variance (betaQuantileClamp a b) ν
      ≤ ∫ p, (betaQuantileClamp a b p - betaQuantileClamp a b e) ^ 2 ∂ν :=
    variance_le_integral_sub_sq hQ2 (betaQuantileClamp a b e)
  have hint1 : Integrable
      (fun p => (betaQuantileClamp a b p - betaQuantileClamp a b e) ^ 2) ν := by
    refine integrable_of_ae_bounded_betaMeasure hj hm
      ((((continuous_betaQuantileClamp ha hb).sub continuous_const).pow
        2).measurable.aestronglyMeasurable) (C := 4) ?_
    filter_upwards with p
    have h := betaQuantileClamp_mem_Icc ha hb p
    have he' := betaQuantileClamp_mem_Icc ha hb e
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [h.1, h.2, he'.1, he'.2]
  have hint2 : Integrable (fun p : ℝ => L ^ 2 * (p - e) ^ 2) ν := by
    refine integrable_of_ae_bounded_betaMeasure hj hm
      ((((measurable_id.sub_const e).pow_const 2).const_mul (L ^ 2)).aestronglyMeasurable)
      (C := L ^ 2) ?_
    filter_upwards [ae_mem_Ioo_betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)] with p hp
    have h1 : |p - e| ≤ 1 := by
      rw [abs_le]
      constructor <;> [linarith [hp.1, he1]; linarith [hp.2, he0]]
    have h2 : (p - e) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (p - e), sq_abs (p - e)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (p - e), sq_nonneg L]
  have hstep2 : ∫ p, (betaQuantileClamp a b p - betaQuantileClamp a b e) ^ 2 ∂ν
      ≤ ∫ p, L ^ 2 * (p - e) ^ 2 ∂ν := by
    refine integral_mono_ae hint1 hint2 ?_
    filter_upwards [ae_mem_Ioo_betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)] with p hp
    have hlp : |betaQuantileClamp a b p - betaQuantileClamp a b e| ≤ L * |p - e| :=
      hlip p ⟨hp.1.le, hp.2.le⟩ e ⟨he0, he1⟩
    have h0 : (0:ℝ) ≤ L * |p - e| :=
      le_trans (abs_nonneg _) hlp
    calc (betaQuantileClamp a b p - betaQuantileClamp a b e) ^ 2
        ≤ (L * |p - e|) ^ 2 := by
          nlinarith [abs_nonneg (betaQuantileClamp a b p - betaQuantileClamp a b e),
            sq_abs (betaQuantileClamp a b p - betaQuantileClamp a b e)]
      _ = L ^ 2 * (p - e) ^ 2 := by rw [mul_pow, sq_abs]
  have hmean : ∫ p, p ∂ν = e := by
    rw [hν, he, integral_id_betaMeasure hj hm]
  have hvar : ∫ p, L ^ 2 * (p - e) ^ 2 ∂ν
      = L ^ 2 * (((j : ℝ) + 1) * ((m : ℝ) + 1)
        / (((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3))) := by
    rw [integral_const_mul]
    have hid : variance (id : ℝ → ℝ) ν = ∫ p, (p - e) ^ 2 ∂ν := by
      rw [variance_eq_integral measurable_id.aemeasurable]
      simp only [id_eq]
      rw [hmean]
    rw [← hid, hν, variance_id_betaMeasure hj hm]
    congr 1
    ring_nf
  rw [variance_orderStat_betaSample_eq ha hb j m, ← hvar]
  exact hstep1.trans hstep2

/-- The crude form of the previous bound: `Var ≤ L²/(4(n+2))`. -/
theorem variance_orderStat_betaSample_le_of_lipschitz' {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (j m : ℕ) {L : ℝ}
    (hlip : ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ q ∈ Set.Icc (0:ℝ) 1,
      |betaQuantileClamp a b p - betaQuantileClamp a b q| ≤ L * |p - q|) :
    variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
      ≤ L ^ 2 / (4 * ((j : ℝ) + (m : ℝ) + 3)) := by
  refine (variance_orderStat_betaSample_le_of_lipschitz ha hb j m hlip).trans ?_
  have hd : (0:ℝ) < ((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3) := by positivity
  have hd4 : (0:ℝ) < 4 * ((j : ℝ) + (m : ℝ) + 3) := by positivity
  have hAM : 4 * (((j : ℝ) + 1) * ((m : ℝ) + 1)) ≤ ((j : ℝ) + (m : ℝ) + 2) ^ 2 := by
    nlinarith [sq_nonneg ((j : ℝ) - (m : ℝ))]
  rw [← mul_div_assoc, div_le_div_iff₀ hd hd4]
  nlinarith [mul_le_mul_of_nonneg_left hAM
    (by positivity : (0:ℝ) ≤ L ^ 2 * ((j : ℝ) + (m : ℝ) + 3))]

/-- **Concentration under a Lipschitz parent quantile**: at least
`1 − L²/(4(n+2)c²)` of the mass of the order statistic lies within `c` of its
mean. -/
theorem orderStat_betaSample_concentration_of_lipschitz {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (j m : ℕ) {L : ℝ}
    (hlip : ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ q ∈ Set.Icc (0:ℝ) 1,
      |betaQuantileClamp a b p - betaQuantileClamp a b q| ≤ L * |p - q|)
    {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal (L ^ 2 / (4 * ((j : ℝ) + (m : ℝ) + 3)) / c ^ 2)
      ≤ (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
          {w | unifOrderStat j m w ∈
            Set.Ioo ((∫ w', unifOrderStat j m w'
                ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))) - c)
              ((∫ w', unifOrderStat j m w'
                ∂(Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))) + c)} := by
  refine le_trans (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal ?_) 1)
    (orderStat_betaSample_concentration ha hb j m hc)
  exact div_le_div_of_nonneg_right
    (variance_orderStat_betaSample_le_of_lipschitz' ha hb j m hlip) (by positivity)

/-- The power parents of batch 196 satisfy the Lipschitz hypothesis with
`L = k`. -/
theorem lipschitz_betaQuantileClamp_inv_nat {k : ℕ} (hk : 0 < k) :
    ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ q ∈ Set.Icc (0:ℝ) 1,
      |betaQuantileClamp (1 / (k : ℝ)) 1 p - betaQuantileClamp (1 / (k : ℝ)) 1 q|
        ≤ (k : ℝ) * |p - q| := by
  intro p hp q hq
  rw [betaQuantileClamp_inv_nat hk hp, betaQuantileClamp_inv_nat hk hq]
  exact abs_pow_sub_pow_le_nat_mul hp.1 hp.2 hq.1 hq.2 k

end SHSLib.Trigamma
