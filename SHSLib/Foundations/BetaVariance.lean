/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integrability and Mathlib's variance for the Beta law

Batch 179 restated the Beta moments as Bochner integrals against
`betaMeasure a b`, but the identity `E[X²] − E[X]² = ab/((a+b)²(a+b+1))` was a
statement about two integrals rather than about Mathlib's
`ProbabilityTheory.variance`.  This module supplies the missing integrability.

The Beta law is carried by `(0,1)`, so every function that is bounded on that
interval is integrable — indeed `MemLp` of every order.  The module records

* `ae_mem_Ioo_betaMeasure` — almost every point lies in `(0,1)`;
* `memLp_of_ae_bounded_betaMeasure` — a bounded a.e.-strongly-measurable
  function is `MemLp` for every exponent;
* `integrable_pow_betaMeasure`, `memLp_id_betaMeasure`;
* `variance_id_betaMeasure` — `Var[id ; betaMeasure a b] = ab/((a+b)²(a+b+1))`.
-/
import SHSLib.Foundations.BetaExpectation

open Real Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SHSLib.Trigamma

/-- The Beta law gives no mass to the complement of `(0,1)`. -/
theorem betaMeasure_compl_Ioo (a b : ℝ) : betaMeasure a b (Set.Ioo (0:ℝ) 1)ᶜ = 0 := by
  rw [betaMeasure_apply a b measurableSet_Ioo.compl, Set.inter_compl_self]
  simp

/-- Almost every point of the Beta law lies in `(0,1)`. -/
theorem ae_mem_Ioo_betaMeasure (a b : ℝ) :
    ∀ᵐ t ∂(betaMeasure a b), t ∈ Set.Ioo (0:ℝ) 1 :=
  MeasureTheory.mem_ae_iff.mpr (betaMeasure_compl_Ioo a b)

/-- Under the Beta law almost every point has norm at most `1`. -/
theorem ae_norm_le_one_betaMeasure (a b : ℝ) :
    ∀ᵐ t ∂(betaMeasure a b), ‖t‖ ≤ 1 := by
  filter_upwards [ae_mem_Ioo_betaMeasure a b] with t ht
  rw [Real.norm_eq_abs, abs_of_pos ht.1]
  exact ht.2.le

/-- A bounded a.e.-strongly-measurable function is `MemLp` of every order for
the Beta law. -/
theorem memLp_of_ae_bounded_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (betaMeasure a b)) {C : ℝ}
    (hC : ∀ᵐ t ∂(betaMeasure a b), ‖g t‖ ≤ C) (p : ℝ≥0∞) :
    MemLp g p (betaMeasure a b) := by
  haveI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasure_betaMeasure ha hb
  exact MemLp.of_bound hg C hC

/-- Every power of the identity is integrable for the Beta law. -/
theorem integrable_pow_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) (betaMeasure a b) := by
  haveI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasure_betaMeasure ha hb
  refine ⟨(measurable_id.pow_const k).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := 1) ?_
  filter_upwards [ae_mem_Ioo_betaMeasure a b] with t ht
  rw [Real.norm_eq_abs, abs_pow, abs_of_pos ht.1]
  exact pow_le_one₀ ht.1.le ht.2.le

/-- The identity is square-integrable for the Beta law. -/
theorem memLp_id_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MemLp (id : ℝ → ℝ) 2 (betaMeasure a b) :=
  memLp_of_ae_bounded_betaMeasure ha hb measurable_id.aestronglyMeasurable
    (ae_norm_le_one_betaMeasure a b) 2

/-- **The variance of the Beta law**, in Mathlib's sense:
`Var[X] = ab/((a+b)²(a+b+1))`. -/
theorem variance_id_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    variance (id : ℝ → ℝ) (betaMeasure a b) = a * b / ((a + b) ^ 2 * (a + b + 1)) := by
  haveI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasure_betaMeasure ha hb
  rw [ProbabilityTheory.variance_eq_sub (memLp_id_betaMeasure ha hb)]
  have h2 : ∫ t, ((id : ℝ → ℝ) ^ 2) t ∂(betaMeasure a b)
      = ∫ t, t ^ (2:ℕ) ∂(betaMeasure a b) := by
    simp
  have h1 : ∫ t, (id : ℝ → ℝ) t ∂(betaMeasure a b) = ∫ t, t ∂(betaMeasure a b) := by
    simp
  rw [h2, h1]
  exact variance_betaMeasure ha hb

end SHSLib.Trigamma
