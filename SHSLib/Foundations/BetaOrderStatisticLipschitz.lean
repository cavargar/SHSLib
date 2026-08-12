/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A variance bound and localization for the sample quantile of powers of uniforms

Batch 196 computed the mean of the `(j+1)`-st order statistic of a sample of
`n = j+m+1` independent `k`-th powers of uniforms and squeezed it between the
parent quantile at two rank fractions.  This module supplies the missing
quantitative half — a bound on the *variance* — and combines the two into a
localization statement for the order statistic itself.

The variance bound does not use the product formula.  The parent quantile
`p ↦ p^k` is `k`-Lipschitz on `[0,1]`, so the variance of the order statistic is
at most `k²` times the variance of the rank variable, which is the known Beta
variance `(j+1)(m+1)/((n+1)²(n+2)) ≤ 1/(4(n+2))`.  Chebyshev then places the
order statistic within `c` of its mean, and hence — by batch 196 — within
`c + O(k/n)` of the parent quantile at its rank fraction, with probability at
least `1 − k²/(4(n+2)c²)`.
-/
import SHSLib.Foundations.BetaOrderStatisticInteger

open MeasureTheory ProbabilityTheory Set

namespace SHSLib.Trigamma

/-! ### Two general tools -/

/-- The variance is the smallest mean square deviation: for any `c`,
`Var[X] ≤ E[(X − c)²]`. -/
theorem variance_le_integral_sub_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (h : MemLp X 2 μ) (c : ℝ) :
    variance X μ ≤ ∫ x, (X x - c) ^ 2 ∂μ := by
  have hint : Integrable X μ := h.integrable (by norm_num)
  have hsq : Integrable (fun x => X x ^ 2) μ := h.integrable_sq
  have hexp : ∫ x, (X x - c) ^ 2 ∂μ
      = (∫ x, X x ^ 2 ∂μ) - 2 * c * (∫ x, X x ∂μ) + c ^ 2 := by
    have hpt : ∀ x, (X x - c) ^ 2 = X x ^ 2 - 2 * c * X x + c ^ 2 := by intro x; ring
    simp_rw [hpt]
    rw [integral_add (f := fun x => X x ^ 2 - 2 * c * X x) (g := fun _ => c ^ 2)
        (hsq.sub (hint.const_mul (2 * c))) (integrable_const _),
      integral_sub (f := fun x => X x ^ 2) (g := fun x => 2 * c * X x) hsq
        (hint.const_mul (2 * c)),
      integral_const_mul, integral_const]
    simp
  have hpow : ∫ x, (X ^ 2) x ∂μ = ∫ x, X x ^ 2 ∂μ := by simp
  rw [variance_eq_sub h, hexp, hpow]
  nlinarith [sq_nonneg ((∫ x, X x ∂μ) - c)]

/-- On `[0,1]` the map `x ↦ x^k` is `k`-Lipschitz. -/
theorem abs_pow_sub_pow_le_nat_mul {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (hb1 : b ≤ 1) (k : ℕ) :
    |a ^ k - b ^ k| ≤ (k : ℝ) * |a - b| := by
  have h := abs_pow_sub_pow_le a b k
  have hmax : max |a| |b| ≤ 1 := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact max_le ha1 hb1
  have hmax0 : (0:ℝ) ≤ max |a| |b| := le_max_of_le_left (abs_nonneg a)
  calc |a ^ k - b ^ k| ≤ |a - b| * k * max |a| |b| ^ (k - 1) := h
    _ ≤ |a - b| * k * 1 := by
        gcongr
        exact pow_le_one₀ hmax0 hmax
    _ = (k : ℝ) * |a - b| := by ring

/-- The variance of an order statistic of a Beta sample is the variance of the
parent quantile under the rank law. -/
theorem variance_orderStat_betaSample_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j m : ℕ) :
    variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
      = variance (betaQuantileClamp a b) (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) := by
  have hmap : (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)).map
      (unifOrderStat j m)
      = (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp a b) :=
    map_orderStat_betaSample ha hb j m
  have h1 : variance (id : ℝ → ℝ)
      ((Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)).map (unifOrderStat j m))
      = variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)) :=
    variance_map measurable_id.aemeasurable (measurable_unifOrderStat j m).aemeasurable
  have h2 : variance (id : ℝ → ℝ)
      ((betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp a b))
      = variance (betaQuantileClamp a b) (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)) :=
    variance_map measurable_id.aemeasurable
      (continuous_betaQuantileClamp ha hb).measurable.aemeasurable
  rw [← h1, hmap, h2]

/-- The clamped `Beta(1/k, 1)` quantile is the `k`-th power on `[0,1]`. -/
theorem betaQuantileClamp_inv_nat {k : ℕ} (hk : 0 < k) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    betaQuantileClamp (1 / (k : ℝ)) 1 p = p ^ k := by
  have hk' : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [betaQuantileClamp_one_right (by positivity) hp,
    show (1 : ℝ) / (1 / (k : ℝ)) = (k : ℝ) by field_simp, Real.rpow_natCast]

/-! ### The variance bound -/

/-- **The variance of the order statistic of a sample of `k`-th powers of
uniforms** is at most `k²` times the Beta variance of the rank variable. -/
theorem variance_orderStat_powerSample_le {k : ℕ} (hk : 0 < k) (j m : ℕ) :
    variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure (1 / (k : ℝ)) 1))
      ≤ (k : ℝ) ^ 2 * (((j : ℝ) + 1) * ((m : ℝ) + 1)
          / (((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3))) := by
  have hk' : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have ha : (0:ℝ) < 1 / (k : ℝ) := by positivity
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
  have hQ2 : MemLp (betaQuantileClamp (1 / (k : ℝ)) 1) 2 ν := by
    refine memLp_of_ae_bounded_betaMeasure hj hm
      (continuous_betaQuantileClamp ha one_pos).measurable.aestronglyMeasurable (C := 1) ?_ 2
    filter_upwards with p
    have h := betaQuantileClamp_mem_Icc ha one_pos p
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  -- the mean square deviation from `e^k`
  have hstep1 : variance (betaQuantileClamp (1 / (k : ℝ)) 1) ν
      ≤ ∫ p, (betaQuantileClamp (1 / (k : ℝ)) 1 p - e ^ k) ^ 2 ∂ν :=
    variance_le_integral_sub_sq hQ2 (e ^ k)
  -- the Lipschitz comparison
  have hint1 : Integrable
      (fun p => (betaQuantileClamp (1 / (k : ℝ)) 1 p - e ^ k) ^ 2) ν := by
    refine integrable_of_ae_bounded_betaMeasure hj hm
      ((((continuous_betaQuantileClamp ha one_pos).sub continuous_const).pow
        2).measurable.aestronglyMeasurable) (C := 4) ?_
    filter_upwards with p
    have h := betaQuantileClamp_mem_Icc ha one_pos p
    have hek : (0:ℝ) ≤ e ^ k := by positivity
    have hek1 : e ^ k ≤ 1 := pow_le_one₀ he0 he1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [h.1, h.2]
  have hint2 : Integrable (fun p : ℝ => (k : ℝ) ^ 2 * (p - e) ^ 2) ν := by
    refine integrable_of_ae_bounded_betaMeasure hj hm
      ((((measurable_id.sub_const e).pow_const 2).const_mul ((k : ℝ) ^ 2)).aestronglyMeasurable)
      (C := (k : ℝ) ^ 2) ?_
    filter_upwards [ae_mem_Ioo_betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)] with p hp
    have h1 : |p - e| ≤ 1 := by
      rw [abs_le]
      constructor <;> [linarith [hp.1, he1]; linarith [hp.2, he0]]
    have h2 : (p - e) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (p - e), sq_abs (p - e)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (p - e)]
  have hstep2 : ∫ p, (betaQuantileClamp (1 / (k : ℝ)) 1 p - e ^ k) ^ 2 ∂ν
      ≤ ∫ p, (k : ℝ) ^ 2 * (p - e) ^ 2 ∂ν := by
    refine integral_mono_ae hint1 hint2 ?_
    filter_upwards [ae_mem_Ioo_betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)] with p hp
    have hQp : betaQuantileClamp (1 / (k : ℝ)) 1 p = p ^ k :=
      betaQuantileClamp_inv_nat hk ⟨hp.1.le, hp.2.le⟩
    have hlip : |p ^ k - e ^ k| ≤ (k : ℝ) * |p - e| :=
      abs_pow_sub_pow_le_nat_mul hp.1.le hp.2.le he0 he1 k
    have hsq : (p ^ k - e ^ k) ^ 2 ≤ ((k : ℝ) * |p - e|) ^ 2 := by
      have h0 : (0:ℝ) ≤ (k : ℝ) * |p - e| := by positivity
      nlinarith [abs_nonneg (p ^ k - e ^ k), sq_abs (p ^ k - e ^ k)]
    rw [hQp]
    calc (p ^ k - e ^ k) ^ 2 ≤ ((k : ℝ) * |p - e|) ^ 2 := hsq
      _ = (k : ℝ) ^ 2 * (p - e) ^ 2 := by rw [mul_pow, sq_abs]
  -- the rank variance
  have hmean : ∫ p, p ∂ν = e := by
    rw [hν, he, integral_id_betaMeasure hj hm]
  have hvar : ∫ p, (k : ℝ) ^ 2 * (p - e) ^ 2 ∂ν
      = (k : ℝ) ^ 2 * (((j : ℝ) + 1) * ((m : ℝ) + 1)
        / (((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3))) := by
    rw [integral_const_mul]
    have hid : variance (id : ℝ → ℝ) ν = ∫ p, (p - e) ^ 2 ∂ν := by
      rw [variance_eq_integral measurable_id.aemeasurable]
      simp only [id_eq]
      rw [hmean]
    rw [← hid, hν, variance_id_betaMeasure hj hm]
    congr 1
    ring_nf
  rw [variance_orderStat_betaSample_eq ha one_pos j m, ← hvar]
  exact hstep1.trans hstep2

/-- The same bound in the crude, `j`-free form `k²/(4(n+2))`. -/
theorem variance_orderStat_powerSample_le' {k : ℕ} (hk : 0 < k) (j m : ℕ) :
    variance (unifOrderStat j m)
        (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure (1 / (k : ℝ)) 1))
      ≤ (k : ℝ) ^ 2 / (4 * ((j : ℝ) + (m : ℝ) + 3)) := by
  refine (variance_orderStat_powerSample_le hk j m).trans ?_
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hd : (0:ℝ) < ((j : ℝ) + (m : ℝ) + 2) ^ 2 * ((j : ℝ) + (m : ℝ) + 3) := by positivity
  have hd4 : (0:ℝ) < 4 * ((j : ℝ) + (m : ℝ) + 3) := by positivity
  have hAM : 4 * (((j : ℝ) + 1) * ((m : ℝ) + 1)) ≤ ((j : ℝ) + (m : ℝ) + 2) ^ 2 := by
    nlinarith [sq_nonneg ((j : ℝ) - (m : ℝ))]
  rw [← mul_div_assoc, div_le_div_iff₀ hd hd4]
  nlinarith [mul_le_mul_of_nonneg_left hAM
    (by positivity : (0:ℝ) ≤ (k : ℝ) ^ 2 * ((j : ℝ) + (m : ℝ) + 3))]

/-! ### Localization of the sample quantile -/

/-- **Localization of the sample quantile.**  With probability at least
`1 − k²/(4(n+2)c²)` the `(j+1)`-st order statistic of a sample of `n = j+m+1`
independent `k`-th powers of uniforms lies in the interval
`[((j+1)/(n+1))^k − c, ((j+k)/(n+k))^k + c]`, both endpoints being the parent
quantile at a rank fraction. -/
theorem orderStat_powerSample_localization {k : ℕ} (hk : 0 < k) (j m : ℕ)
    {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal ((k : ℝ) ^ 2 / (4 * ((j : ℝ) + (m : ℝ) + 3)) / c ^ 2)
      ≤ (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure (1 / (k : ℝ)) 1))
          {w | unifOrderStat j m w ∈
            Set.Icc ((((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2)) ^ k - c)
              ((((j : ℝ) + (k : ℝ)) / ((j : ℝ) + (m : ℝ) + 1 + (k : ℝ))) ^ k + c)} := by
  have hk' : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have ha : (0:ℝ) < 1 / (k : ℝ) := by positivity
  set μ := Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure (1 / (k : ℝ)) 1) with hμ
  obtain ⟨hlo, hhi⟩ := integral_orderStat_powerSample_bounds k hk j m
  have hconc := orderStat_betaSample_concentration ha one_pos j m hc
  -- weaken the variance
  have hvar : ENNReal.ofReal (variance (unifOrderStat j m) μ / c ^ 2)
      ≤ ENNReal.ofReal ((k : ℝ) ^ 2 / (4 * ((j : ℝ) + (m : ℝ) + 3)) / c ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    exact div_le_div_of_nonneg_right (variance_orderStat_powerSample_le' hk j m) (by positivity)
  -- enlarge the interval
  have hsub : {w | unifOrderStat j m w ∈
        Set.Ioo ((∫ w', unifOrderStat j m w' ∂μ) - c) ((∫ w', unifOrderStat j m w' ∂μ) + c)}
      ⊆ {w | unifOrderStat j m w ∈
        Set.Icc ((((j : ℝ) + 1) / ((j : ℝ) + (m : ℝ) + 2)) ^ k - c)
          ((((j : ℝ) + (k : ℝ)) / ((j : ℝ) + (m : ℝ) + 1 + (k : ℝ))) ^ k + c)} := by
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_Ioo] at hw
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    exact ⟨by linarith [hw.1, hlo], by linarith [hw.2, hhi]⟩
  calc 1 - ENNReal.ofReal ((k : ℝ) ^ 2 / (4 * ((j : ℝ) + (m : ℝ) + 3)) / c ^ 2)
      ≤ 1 - ENNReal.ofReal (variance (unifOrderStat j m) μ / c ^ 2) :=
        tsub_le_tsub_left hvar 1
    _ ≤ μ {w | unifOrderStat j m w ∈
          Set.Ioo ((∫ w', unifOrderStat j m w' ∂μ) - c)
            ((∫ w', unifOrderStat j m w' ∂μ) + c)} := hconc
    _ ≤ _ := measure_mono hsub

end SHSLib.Trigamma
