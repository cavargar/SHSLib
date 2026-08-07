/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chebyshev concentration for the Beta law

Batch 180 proved that the identity is square-integrable for `betaMeasure a b`
and computed its variance.  Chebyshev's inequality therefore applies verbatim,
and this module records the two resulting statements in closed form:

* `betaMeasure_chebyshev` — the deviation bound
  `P(|X − a/(a+b)| ≥ c) ≤ ab/((a+b)²(a+b+1)c²)`;
* `betaMeasure_concentration` — the complementary form, a lower bound for the
  mass of the symmetric interval `(m − c, m + c)` around the mean `m`.
-/
import SHSLib.Foundations.BetaVariance

open Real Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SHSLib.Trigamma

/-- The deviation set of the Beta law is measurable. -/
theorem measurableSet_abs_sub_ge (m c : ℝ) :
    MeasurableSet {t : ℝ | c ≤ |t - m|} := by
  have : {t : ℝ | c ≤ |t - m|} = (fun t : ℝ => |t - m|) ⁻¹' Set.Ici c := rfl
  rw [this]
  exact ((measurable_id.sub_const m).abs) measurableSet_Ici

/-- **Chebyshev's inequality for the Beta law**: the mass of the points at
distance at least `c` from the mean `a/(a+b)` is at most
`ab/((a+b)²(a+b+1)c²)`. -/
theorem betaMeasure_chebyshev {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    betaMeasure a b {t : ℝ | c ≤ |t - a / (a + b)|}
      ≤ ENNReal.ofReal (a * b / ((a + b) ^ 2 * (a + b + 1)) / c ^ 2) := by
  haveI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasure_betaMeasure ha hb
  have hmean : (betaMeasure a b)[(id : ℝ → ℝ)] = a / (a + b) := by
    simpa using integral_id_betaMeasure ha hb
  have h := ProbabilityTheory.meas_ge_le_variance_div_sq (memLp_id_betaMeasure ha hb) hc
  rwa [hmean, variance_id_betaMeasure ha hb] at h

/-- The complementary form of Chebyshev's inequality: at least
`1 − ab/((a+b)²(a+b+1)c²)` of the Beta mass lies within `c` of the mean. -/
theorem betaMeasure_concentration {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    1 - ENNReal.ofReal (a * b / ((a + b) ^ 2 * (a + b + 1)) / c ^ 2)
      ≤ betaMeasure a b (Set.Ioo (a / (a + b) - c) (a / (a + b) + c)) := by
  haveI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasure_betaMeasure ha hb
  set m : ℝ := a / (a + b) with hm
  have hcompl : {t : ℝ | c ≤ |t - m|}ᶜ = Set.Ioo (m - c) (m + c) := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_Ioo, abs_lt]
    constructor
    · intro h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hmeas := measurableSet_abs_sub_ge m c
  have hprob : betaMeasure a b (Set.Ioo (m - c) (m + c))
      = 1 - betaMeasure a b {t : ℝ | c ≤ |t - m|} := by
    rw [← hcompl, prob_compl_eq_one_sub hmeas]
  rw [hprob]
  exact tsub_le_tsub_left (betaMeasure_chebyshev ha hb hc) 1

end SHSLib.Trigamma
