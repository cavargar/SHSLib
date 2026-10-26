/-
# Riemann sums for continuous adapted integrands (Gardiner §4.2.1)

`Gardiner.Ito.itoRiemann_tendsto` assumes that the integrand is uniformly continuous in mean square.
Here this hypothesis is derived from path continuity: if almost every path `t ↦ G(t, ω)` is continuous on
`[0, T]` and `|G(t, ω)| ≤ Y(ω)` for some `Y ∈ L²`, then `G` is uniformly continuous in mean square
(`Gardiner.Ito.msUnifCont_of_continuousOn`, by compactness and dominated convergence).  Hence the
left-point Riemann sums of a continuous adapted dominated integrand converge in mean square to its
Itô integral (`Gardiner.Ito.itoRiemann_tendsto_of_continuousOn`), which is Gardiner's definition of
the Itô integral in §4.2.1.  Bounded continuous adapted integrands are the special case `Y = B`
(`Gardiner.Ito.itoRiemann_tendsto_of_bounded`); `cos W` is an instance
(`Gardiner.Ito.IsFWiener.itoRiemann_cos_W_tendsto`).

Some domination is needed: path continuity alone does not give mean-square convergence of the sums.
-/
import SHSLib.Gardiner.Ito.Calculus.ItoFormula
import SHSLib.Gardiner.Ito.Calculus.Riemann

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- A process with paths continuous on `[0, T]`, dominated by a square-integrable `Y`, is
uniformly continuous in mean square on `[0, T]`. -/
lemma msUnifCont_of_continuousOn {T : ℝ} {G : ℝ → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (G t) P) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => G t ω) (Icc 0 T))
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ ω, |G t ω| ≤ Y ω) :
    MSUnifCont P T G := by
  intro ε hε
  by_contra hne
  push_neg at hne
  have hseq : ∀ n : ℕ, ∃ st : ℝ × ℝ, st.1 ∈ Icc (0 : ℝ) T ∧ st.2 ∈ Icc (0 : ℝ) T ∧
      |st.1 - st.2| < 1 / ((n : ℝ) + 1) ∧ ε ≤ ∫ ω, (G st.1 ω - G st.2 ω) ^ 2 ∂P := by
    intro n
    obtain ⟨s, t, hs0, hsT, ht0, htT, hst, hle⟩ := hne (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨(s, t), ⟨hs0, hsT⟩, ⟨ht0, htT⟩, hst, hle⟩
  choose st hs ht hst hle using hseq
  obtain ⟨r, hr, φ, hφ, hlim⟩ := (isCompact_Icc).tendsto_subseq (x := fun n => (st n).1) hs
  have hd : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim2 : Tendsto (fun k => (st (φ k)).2) atTop (𝓝 r) := by
    have h1 : Tendsto (fun k => (st (φ k)).1 - (st (φ k)).2) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => (hst (φ k)).le) (hd.comp hφ.tendsto_atTop)
    have := hlim.sub h1
    simpa using this
  -- dominated convergence along the subsequence
  have hconv : Tendsto (fun k => ∫ ω, (G (st (φ k)).1 ω - G (st (φ k)).2 ω) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (G r ω - G r ω) ^ 2 ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => (2 * Y ω) ^ 2)
      (fun k => ((hm _).sub (hm _)).pow 2) ((hY.const_mul 2).integrable_sq) (fun k => ?_) ?_
    · refine Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      have h1 := hdom _ (hs (φ k)) ω
      have h2 := hdom _ (ht (φ k)) ω
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |G (st (φ k)).1 ω - G (st (φ k)).2 ω| ≤ |G (st (φ k)).1 ω| + |G (st (φ k)).2 ω| :=
            abs_sub _ _
        _ ≤ 2 * Y ω := by linarith
    · filter_upwards [hc] with ω hcω
      have hcw := (hcω r hr).tendsto
      have e1 : Tendsto (fun k => G (st (φ k)).1 ω) atTop (𝓝 (G r ω)) :=
        hcw.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k => hs (φ k)⟩)
      have e2 : Tendsto (fun k => G (st (φ k)).2 ω) atTop (𝓝 (G r ω)) :=
        hcw.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim2, Eventually.of_forall fun k => ht (φ k)⟩)
      exact (e1.sub e2).pow 2
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    at hconv
  have hev := hconv.eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := hev.exists
  exact absurd (hle (φ k)) (not_le.mpr hk)

/-- A jointly measurable adapted process with paths continuous on `[0, T]` and dominated by a
square-integrable `Y` is an Itô integrand on `[0, T]`. -/
lemma isItoIntegrand_of_dominated [IsFiniteMeasure P] {T : ℝ} {G : ℝ → Ω → ℝ}
    (hm : Measurable (Function.uncurry G))
    (had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (G t))
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ ω, |G t ω| ≤ Y ω) :
    IsItoIntegrand 𝓕 P T G := by
  refine ⟨hm, had, ?_⟩
  have hY' : MemLp (fun p : ℝ × Ω => Y p.2) 2 (tsMeasure P T) := by
    unfold tsMeasure
    exact hY.comp_snd _
  refine hY'.of_le hm.aestronglyMeasurable ?_
  have hae : ∀ᵐ p ∂(tsMeasure P T), p.1 ∈ Ioc 0 T := by
    unfold tsMeasure
    exact Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hae] with p hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hdom p.1 ⟨hp.1.le, hp.2⟩ p.2).trans (le_abs_self _)

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **Left-point Riemann sums of a continuous adapted integrand converge to the Itô integral in
mean square** (Gardiner §4.2.1).  The integrand is jointly measurable, nonanticipating, has paths
continuous on `[0, T]` and is dominated by a square-integrable random variable. -/
theorem itoRiemann_tendsto_of_continuousOn {T : ℝ} (hT : 0 < T) {G : ℝ → Ω → ℝ}
    (hm : Measurable (Function.uncurry G))
    (had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (G t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => G t ω) (Icc 0 T))
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ ω, |G t ω| ≤ Y ω) :
    Tendsto (fun n => ∫ ω, (itoRiemann W G T n ω - itoInt W 𝓕 P T G ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  have hmt : ∀ t, Measurable (G t) := fun t => hm.comp (measurable_const.prodMk measurable_id)
  have hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (G t) 2 P := fun t ht htT =>
    hY.of_le (hmt t).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact (hdom t ⟨ht, htT⟩ ω).trans (le_abs_self _))
  exact itoRiemann_tendsto hW hT (isItoIntegrand_of_dominated hm had hY hdom) hL2
    (msUnifCont_of_continuousOn (fun t => (hmt t).aestronglyMeasurable) hc hY hdom)

/-- Left-point Riemann sums of a **bounded** continuous adapted integrand converge to its Itô
integral in mean square. -/
theorem itoRiemann_tendsto_of_bounded {T : ℝ} (hT : 0 < T) {G : ℝ → Ω → ℝ}
    (hm : Measurable (Function.uncurry G))
    (had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (G t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => G t ω) (Icc 0 T)) {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ ω, |G t ω| ≤ B) :
    Tendsto (fun n => ∫ ω, (itoRiemann W G T n ω - itoInt W 𝓕 P T G ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  exact itoRiemann_tendsto_of_continuousOn hW hT hm had hc (memLp_const B) hB

/-- Instance: the left-point sums `Σ cos W(tᵢ) (W(tᵢ₊₁) - W(tᵢ))` converge in mean square to
`∫₀ᵀ cos W dW`. -/
theorem IsFWiener.itoRiemann_cos_W_tendsto (hWj : Measurable (Function.uncurry W)) {T : ℝ}
    (hT : 0 < T) :
    Tendsto (fun n => ∫ ω, (itoRiemann W (fun t ω => Real.cos (W t ω)) T n ω -
      itoInt W 𝓕 P T (fun t ω => Real.cos (W t ω)) ω) ^ 2 ∂P) atTop (𝓝 0) :=
  itoRiemann_tendsto_of_bounded hW hT (Real.continuous_cos.measurable.comp hWj)
    (fun t ht _ => Real.continuous_cos.comp_stronglyMeasurable (hW.adapted t ht))
    (hW.cont.mono fun _ hω => (Real.continuous_cos.comp hω).continuousOn)
    (fun _ _ _ => Real.abs_cos_le_one _)

end Gardiner.Ito
