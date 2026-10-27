/-
# The restart (flow) property of solutions

Gardiner §4.3.2 (first step of the Markov property): "with a given initial condition `x(t₀)`, the
future time development is uniquely determined".  If `x` solves (4.3.4) on `[t₀, T]`, then for
every `s ∈ [t₀, T]` the same process solves (4.3.4) on `[s, T]` with initial value `x(s)`
(`IsSDESol.restart`), and therefore coincides there, up to indistinguishability, with the solution
started afresh at time `s` from `x(s)` (`IsSDESol.eq_sdeSol_restart`).

The Markov property `E[f(x(t)) | 𝓕_s] = (P_{s,t} f)(x(s))` itself is not formalized here; see the
plan file for the remaining steps.
-/
import SHSLib.Gardiner.Ito.StochDE.Euler

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

omit [MeasurableSpace Ω] in
lemma drive_restrict {b : ℝ → ℝ → ℝ} {x : ℝ → Ω → ℝ} {t₀ s : ℝ} (hts : t₀ ≤ s) :
    drive s b x = fun v ω => afterInd s v * drive t₀ b x v ω := by
  funext v ω
  unfold drive
  by_cases h : s < v
  · rw [afterInd_of_lt h, afterInd_of_lt (hts.trans_lt h)]; ring
  · rw [afterInd_of_le (not_lt.mp h)]; ring

namespace IsSDESol

variable {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ}

/-- **Restart property**: a solution on `[t₀, T]` is a solution on `[s, T]` with initial value
`x(s)`, for every `s ∈ [t₀, T]`. -/
theorem restart (hW : IsFWiener W 𝓕 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) {s : ℝ} (hs : s ∈ Set.Icc t₀ T) :
    IsSDESol W 𝓕 P a b s T (x s) x where
  measurable := hx.measurable
  adapted u hu := hx.adapted u ⟨hs.1.trans hu.1, hu.2⟩
  cont := hx.cont.mono fun ω h => h.mono (Set.Icc_subset_Icc_left hs.1)
  sq_int := lt_of_le_of_lt (lintegral_mono_set (Set.Ioc_subset_Ioc_left hs.1)) hx.sq_int
  eq u hu := by
    have := hW.isProbabilityMeasure
    have hD := hx.isItoIntegrand hc ht₀
    have huI : u ∈ Set.Icc t₀ T := ⟨hs.1.trans hu.1, hu.2⟩
    rw [drive_restrict hs.1]
    filter_upwards [hx.eq u huI, hx.eq s hs, hx.cont,
      itoInt_afterInd hW (ht₀.trans hs.1) hu.1 hu.2 hD] with ω h1 h2 h3 h4
    have hint := hc.driftCoeff.integrableOn hx.measurable h3
    have hi : ∀ v ∈ Set.Icc t₀ T, IntervalIntegrable (fun r => a (x r ω) r) volume t₀ v :=
      fun v hv => (hint.mono_set (by rw [Set.uIcc_of_le hv.1]; exact Set.Icc_subset_Icc_right hv.2)).intervalIntegrable
    rw [h4, h1, h2, ← intervalIntegral.integral_interval_sub_left (hi u huI) (hi s hs)]
    ring

/-- A solution has square-integrable values. -/
lemma memLp_apply (hW : IsFWiener W 𝓕 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (hξ : MemLp ξ 2 P) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ T) : MemLp (x s) 2 P := by
  refine memLp_two_of_lintegral_lt_top (measurable_of_uncurry hx.measurable s).aestronglyMeasurable ?_
  refine lt_of_le_of_lt ?_ (hx.supSq_lt_top hW hc ht₀ (hs.1.trans hs.2) hξ)
  exact lintegral_mono fun ω => pow_le_pow_left' (enorm_le_iSup_Icc hs ω) 2

/-- **The future of a solution is determined by its present value**: on `[s, T]`, a solution is
indistinguishable from the solution `sdeSol` started at time `s` from `x(s)`. -/
theorem eq_sdeSol_restart (hW : IsFWiener W 𝓕 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (hξ : MemLp ξ 2 P) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc s T, x t ω = sdeSol W 𝓕 P a b s T (x s) t ω := by
  have hmem := hx.memLp_apply hW hc ht₀ hξ hs
  have hc' := hc.mono_left hs.1
  exact (hx.restart hW hc ht₀ hs).unique hW
    (isSDESol_sdeSol hW hc' (ht₀.trans hs.1) hs.2 (hx.adapted s hs) hmem) hc' (ht₀.trans hs.1)
    hs.2 hmem

end IsSDESol

end Gardiner.Ito.StochDE
