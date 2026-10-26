/-
# Adapter: a concrete standard Wiener process from the `brownian-motion` library

This is the **only** SHSLib file that imports the `brownian-motion` dependency (and, per
`research/wiki/Dependencies.md`, it imports only `BrownianMotion.Gaussian.BrownianMotion`).  It
turns the library's Brownian motion `ProbabilityTheory.brownian`, indexed by `ℝ≥0` and defined on
`ℝ≥0 → ℝ` under the measure `ProbabilityTheory.gaussianLimit`, into a process on real time,

  `Gardiner.Ito.stdWiener t ω = brownian (max t 0) ω`,

and proves that it satisfies the SHSLib interface `Gardiner.Ito.IsWiener`
(`Gardiner.Ito.isWiener_stdWiener`).  Its paths are continuous for **every** `ω`
(`Gardiner.Ito.continuous_stdWiener`), not just almost surely.

Downstream files should only use the names exported here:

| Name | Meaning |
| --- | --- |
| `Gardiner.Ito.StdWienerSpace` | the sample space |
| `Gardiner.Ito.stdWienerMeasure` | its probability measure |
| `Gardiner.Ito.stdWiener` | the standard Wiener process on real time |
| `Gardiner.Ito.isWiener_stdWiener` | it satisfies `Gardiner.Ito.IsWiener` |
| `Gardiner.Ito.continuous_stdWiener` | every path is continuous |
| `Gardiner.Ito.exists_wiener` | a Wiener process with continuous paths exists |

A future switch to Mathlib's Brownian motion only has to re-prove these six facts.

Library facts used: `IsBrownian_brownian`, `continuous_brownian`, `measurable_brownian`,
`hasLaw_brownian_eval`, `hasLaw_brownian_sub`, `hasIndepIncrements_brownian` and
`IsPreBrownian.isFilteredPreBrownian` (independence of future increments from the `ℝ≥0` natural
filtration, which in turn rests on `IsPreBrownian.indepFun_shift`).
-/
import BrownianMotion.Gaussian.BrownianMotion
import SHSLib.Gardiner.Ito.Wiener

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

/-- The sample space of the standard Wiener process. -/
abbrev StdWienerSpace : Type := ℝ≥0 → ℝ

/-- The probability measure on `StdWienerSpace`. -/
def stdWienerMeasure : Measure StdWienerSpace := gaussianLimit

instance : IsProbabilityMeasure stdWienerMeasure := by
  unfold stdWienerMeasure; infer_instance

/-- The **standard Wiener process on real time**: the library's Brownian motion, extended by its
value at `0` to negative times. -/
def stdWiener (t : ℝ) (ω : StdWienerSpace) : ℝ := brownian t.toNNReal ω

/-- Every path of `stdWiener` is continuous. -/
theorem continuous_stdWiener (ω : StdWienerSpace) : Continuous fun t => stdWiener t ω :=
  (continuous_brownian ω).comp continuous_real_toNNReal

lemma measurable_stdWiener (t : ℝ) : Measurable (stdWiener t) := measurable_brownian _

lemma stdWiener_zero_ae : ∀ᵐ ω ∂stdWienerMeasure, stdWiener 0 ω = 0 := by
  have h : HasLaw (brownian 0) (gaussianReal 0 0) gaussianLimit := hasLaw_brownian_eval
  rw [gaussianReal_zero_var] at h
  have hm := h.map_eq
  have : stdWienerMeasure {ω | brownian 0 ω ≠ 0} = 0 := by
    have hs : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
    have := congrArg (fun μ : Measure ℝ => μ {x : ℝ | x ≠ 0}) hm
    simp only [Measure.map_apply (measurable_brownian 0) hs] at this
    rw [stdWienerMeasure]
    simpa [Set.preimage, Measure.dirac_apply' _ hs] using this
  rw [ae_iff]
  simpa [stdWiener] using this

lemma stdWiener_law_sub (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    stdWienerMeasure.map (stdWiener t - stdWiener s) = gaussianReal 0 (t - s).toNNReal := by
  have h : HasLaw (brownian t.toNNReal - brownian s.toNNReal)
      (gaussianReal 0 (max (t.toNNReal - s.toNNReal) (s.toNNReal - t.toNNReal))) gaussianLimit :=
    hasLaw_brownian_sub
  have hle : s.toNNReal ≤ t.toNNReal := Real.toNNReal_le_toNNReal hst
  have hsub : (t - s).toNNReal = t.toNNReal - s.toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_sub hle, Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith),
      Real.coe_toNNReal _ hs]
  rw [tsub_eq_zero_of_le hle, max_eq_left (zero_le _), ← hsub] at h
  exact h.map_eq

lemma stdWiener_indep_incr (n : ℕ) (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    iIndepFun (fun i : Fin n => stdWiener (t i.succ) - stdWiener (t i.castSucc))
      stdWienerMeasure :=
  hasIndepIncrements_brownian n (fun i => (t i).toNNReal)
    (fun _ _ hij => Real.toNNReal_le_toNNReal (ht hij))

lemma stdWiener_indep_past (s t : ℝ) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (stdWiener t - stdWiener s) inferInstance)
      (wienerFiltration stdWiener measurable_stdWiener s) stdWienerMeasure := by
  have hF := (IsPreBrownian.isFilteredPreBrownian (X := brownian) (P := gaussianLimit)
    measurable_brownian).indep s.toNNReal t.toNNReal (Real.toNNReal_le_toNNReal hst)
  refine indep_of_indep_of_le_right hF ?_
  refine iSup₂_le fun r hr => ?_
  refine le_iSup₂_of_le (f := fun j (_ : j ≤ s.toNNReal) =>
    MeasurableSpace.comap (brownian j) inferInstance) r.toNNReal
    (Real.toNNReal_le_toNNReal hr.2) le_rfl

/-- **The standard Wiener process satisfies the SHSLib interface.** -/
theorem isWiener_stdWiener : IsWiener stdWiener stdWienerMeasure where
  isProbabilityMeasure := inferInstance
  measurable := measurable_stdWiener
  zero := stdWiener_zero_ae
  cont := Filter.Eventually.of_forall continuous_stdWiener
  law_sub := stdWiener_law_sub
  indep_incr n t ht _ := stdWiener_indep_incr n t ht
  indep_past s t _ hst := stdWiener_indep_past s t hst

/-- A standard Wiener process on real time, with continuous paths, exists. -/
theorem exists_wiener :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ W : ℝ → Ω → ℝ,
      IsWiener W P ∧ ∀ ω, Continuous fun t => W t ω :=
  ⟨StdWienerSpace, inferInstance, stdWienerMeasure, stdWiener, isWiener_stdWiener,
    continuous_stdWiener⟩

end Gardiner.Ito
