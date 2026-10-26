/-
# Continuity of translation in `L²(ℝ)`

`∫ (f(t - q) - f(t))² dt → 0` as `q → 0` for every `f ∈ L²(ℝ)`
(`Gardiner.Ito.tendsto_translate_sq`).  Used in the density of elementary integrands.
Mathlib only.
-/
import SHSLib.Gardiner.Ito.Calculus.Space

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Gardiner.Ito

lemma memLp_translate {f : ℝ → ℝ} (hf : MemLp f 2 volume) (q : ℝ) :
    MemLp (fun t => f (t - q)) 2 volume :=
  hf.comp_measurePreserving (measurePreserving_sub_right volume q)

lemma integral_translate_sub_sq (f g : ℝ → ℝ) (q : ℝ) :
    ∫ t, (f (t - q) - g (t - q)) ^ 2 = ∫ t, (f t - g t) ^ 2 :=
  integral_sub_right_eq_self (fun t => (f t - g t) ^ 2) q

/-- Translation continuity for a continuous function with compact support. -/
lemma tendsto_translate_sq_of_hasCompactSupport {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Tendsto (fun q => ∫ t, (g (t - q) - g t) ^ 2) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hgc.isCompact.isBounded
  have hzero : ∀ x : ℝ, R < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith
  set bound : ℝ → ℝ := (Set.Icc (-(R + 1)) (R + 1)).indicator (fun _ => (2 * C) ^ 2) with hb
  have hbi : Integrable bound := by
    rw [hb]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp [Real.volume_Icc]))
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 (0 : ℝ))
    (F := fun q t => (g (t - q) - g t) ^ 2) (f := fun _ => 0) bound
    (Eventually.of_forall fun q =>
      (((hg.comp (continuous_id.sub continuous_const)).sub hg).pow 2).aestronglyMeasurable)
    (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with q hq
      refine Eventually.of_forall fun t => ?_
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hq
      by_cases ht : t ∈ Set.Icc (-(R + 1)) (R + 1)
      · rw [hb, Set.indicator_of_mem ht, Real.norm_eq_abs, abs_pow]
        have h1 := hC (t - q); have h2 := hC t
        rw [Real.norm_eq_abs] at h1 h2
        have : |g (t - q) - g t| ≤ 2 * C := by
          calc |g (t - q) - g t| ≤ |g (t - q)| + |g t| := abs_sub _ _
            _ ≤ 2 * C := by linarith
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      · rw [hb, Set.indicator_of_notMem ht]
        have ht' : R + 1 < |t| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
          rcases ht with ht | ht
          · linarith [neg_le_abs t]
          · linarith [le_abs_self t]
        have h1 : g t = 0 := hzero t (by linarith)
        have h2 : g (t - q) = 0 := hzero (t - q) (by
          have := abs_sub_abs_le_abs_sub t q
          linarith)
        simp [h1, h2])
    hbi
    (Eventually.of_forall fun t => by
      have : Continuous fun q => (g (t - q) - g t) ^ 2 :=
        ((hg.comp (continuous_const.sub continuous_id)).sub continuous_const).pow 2
      simpa using this.tendsto 0)
  simpa using h

/-- **Continuity of translation in `L²(ℝ)`**: `∫ (f(t - q) - f(t))² dt → 0` as `q → 0`. -/
theorem tendsto_translate_sq {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun q => ∫ t, (f (t - q) - f t) ^ 2) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := Real.sqrt ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, hgc, hfg, hgcont, hgm⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    (by simp) (ε := ENNReal.ofReal δ) (by simpa using hδ0)
  -- `‖f - g‖ ≤ δ`
  have hfgn : Real.sqrt (∫ t, (f t - g t) ^ 2) ≤ δ := by
    have e := l2_norm_toLp_sub_sq hf hgm
    rw [← MemLp.toLp_sub, Lp.norm_toLp] at e
    rw [← e, Real.sqrt_sq ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal hδ0.le hfg
  have hg := tendsto_translate_sq_of_hasCompactSupport hgcont hgc
  filter_upwards [Metric.tendsto_nhds.mp hg (δ ^ 2) (by positivity)] with q hq
  rw [Real.dist_eq, sub_zero] at hq ⊢
  rw [abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at hq ⊢
  -- triangle inequality in `L²`
  have hfq := memLp_translate hf q
  have hgq := memLp_translate hgm q
  set Fq := hfq.toLp _
  set Gq := hgq.toLp _
  set F := hf.toLp f
  set G := hgm.toLp g
  have n1 : ‖Fq - Gq‖ = Real.sqrt (∫ t, (f t - g t) ^ 2) := by
    rw [← integral_translate_sub_sq f g q, ← l2_norm_toLp_sub_sq hfq hgq,
      Real.sqrt_sq (norm_nonneg _)]
  have n2 : ‖Gq - G‖ ^ 2 < δ ^ 2 := by
    rw [l2_norm_toLp_sub_sq hgq hgm]; exact hq
  have n2' : ‖Gq - G‖ < δ := by
    nlinarith [norm_nonneg (Gq - G)]
  have n3 : ‖G - F‖ = Real.sqrt (∫ t, (f t - g t) ^ 2) := by
    rw [norm_sub_rev, ← l2_norm_toLp_sub_sq hf hgm, Real.sqrt_sq (norm_nonneg _)]
  have htri : ‖Fq - F‖ ≤ ‖Fq - Gq‖ + ‖Gq - G‖ + ‖G - F‖ := by
    calc ‖Fq - F‖ = ‖(Fq - Gq) + (Gq - G) + (G - F)‖ := by congr 1; abel
      _ ≤ ‖(Fq - Gq) + (Gq - G)‖ + ‖G - F‖ := norm_add_le _ _
      _ ≤ ‖Fq - Gq‖ + ‖Gq - G‖ + ‖G - F‖ := by gcongr; exact norm_add_le _ _
  have hle : ‖Fq - F‖ < 3 * δ := by rw [n1, n3] at htri; linarith
  have e := l2_norm_toLp_sub_sq hfq hf
  rw [← e]
  have : ‖Fq - F‖ ^ 2 < (3 * δ) ^ 2 := by
    exact pow_lt_pow_left₀ hle (norm_nonneg _) two_ne_zero
  calc ‖Fq - F‖ ^ 2 < (3 * δ) ^ 2 := this
    _ = 9 / 16 * ε := by
      rw [hδ, mul_pow, div_pow, Real.sq_sqrt hε.le]; ring
    _ < ε := by linarith

end Gardiner.Ito
