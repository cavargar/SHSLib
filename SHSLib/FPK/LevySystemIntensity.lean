/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eq. (8) from the Lévy system: the mean jump intensity of spontaneous jumps

Formalization of the derivation of Eq. (8) in Section 3.1 of

  J. Bect, "A unifying formulation of the Fokker–Planck–Kolmogorov equation
  for general stochastic hybrid systems", Nonlinear Analysis: Hybrid Systems 4 (2010).

The Lévy-system identity (5)–(6), applied to the spontaneous part of the jump measure
`R` of Eq. (7) and to the test function `1_{Γ × E⁰}`, gives

  `R⁰(Γ × (0;t]) = E{ ∫₀ᵗ 1_Γ(X_s) λ(X_s) ds }`.

Fubini–Tonelli turns the right-hand side into `∫₀ᵗ (∫_Γ λ dμ_s) ds`, so that

  `r_t⁰(Γ) = ∫_Γ λ dμ_t = E(λ(X_t) 1_{X_t ∈ Γ})`,   (8)

is a mean jump intensity (Definition 6) for the spontaneous jumps: this is
`GSHS.meanJumpIntensity_spontaneous_of_levy` below, which discharges the hypothesis
`hR` of `GSHS.meanJumpIntensity_spontaneous`.
-/
import SHSLib.FPK.MeanJumpIntensity

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

variable {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]

/-- **Fubini–Tonelli for the Lévy-system integral.**  The expected occupation integral of
a nonnegative measurable function of the state equals the time integral of its
expectations, i.e. of its integrals against the laws `μ_s = P ∘ X_s⁻¹`. -/
theorem lintegral_pathOccupation_swap {P : Measure Omega} [SFinite P] {X : ℝ → Omega → E}
    (hX : Measurable (Function.uncurry X)) {h : E → ℝ≥0∞} (hh : Measurable h) (t : ℝ) :
    ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t, h (X s ω)) ∂P
      = ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ x, h x ∂(P.map (X s)) := by
  have hXs : ∀ s : ℝ, Measurable (X s) := fun s =>
    hX.comp (measurable_const.prodMk measurable_id)
  have hmeas : Measurable fun p : Omega × ℝ => h (X p.2 p.1) :=
    hh.comp (hX.comp (measurable_snd.prodMk measurable_fst))
  have hswap := lintegral_lintegral_swap
    (μ := P) (ν := volume.restrict (Ioc (0 : ℝ) t))
    (f := fun (ω : Omega) (s : ℝ) => h (X s ω)) hmeas.aemeasurable
  rw [hswap]
  refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  rw [lintegral_map hh (hXs s)]

/-- Measurability in time of `s ↦ ∫_Γ λ dμ_s`. -/
theorem measurable_lawLintegral {P : Measure Omega} [SFinite P] {X : ℝ → Omega → E}
    (hX : Measurable (Function.uncurry X)) {h : E → ℝ≥0∞} (hh : Measurable h) :
    Measurable fun s : ℝ => ∫⁻ x, h x ∂(P.map (X s)) := by
  have hXs : ∀ s : ℝ, Measurable (X s) := fun s =>
    hX.comp (measurable_const.prodMk measurable_id)
  have hfun : (fun s : ℝ => ∫⁻ x, h x ∂(P.map (X s)))
      = fun s : ℝ => ∫⁻ ω, h (X s ω) ∂P := by
    funext s
    rw [lintegral_map hh (hXs s)]
  rw [hfun]
  exact (hh.comp hX).lintegral_prod_right'

/-- **Eq. (8)** (Bect, 2010), derived from the Lévy-system identity (5)–(6).

If the spontaneous part `R⁰` of the jump measure satisfies the Lévy-system identity

  `R⁰(Γ × (0;t]) = E{ ∫₀ᵗ 1_Γ(X_s) λ(X_s) ds }`

for every measurable `Γ` and every `t ≥ 0`, and the stochastic intensity `λ` is bounded,
then `r_t⁰ = λ · μ_t` is a mean jump intensity (Definition 6) for `R⁰`. -/
theorem meanJumpIntensity_spontaneous_of_levy {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X))
    {lam : E → ℝ≥0∞} (hlam : Measurable lam) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hlam_le : ∀ x, lam x ≤ C) {R₀ : Measure (E × ℝ)}
    (hR : ∀ Γ : Set E, MeasurableSet Γ → ∀ t : ℝ, 0 ≤ t →
      R₀ (Γ ×ˢ Ioc (0 : ℝ) t)
        = ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t, Γ.indicator lam (X s ω)) ∂P) :
    MeanJumpIntensity R₀ (fun t => (P.map (X t)).withDensity lam) := by
  have hXs : ∀ s : ℝ, Measurable (X s) := fun s =>
    hX.comp (measurable_const.prodMk measurable_id)
  have hfin : ∀ t : ℝ, IsFiniteMeasure ((P.map (X t)).withDensity lam) := by
    intro t
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hle : ∫⁻ x, lam x ∂(P.map (X t)) ≤ ∫⁻ _, C ∂(P.map (X t)) :=
      lintegral_mono hlam_le
    have hmap : (P.map (X t)) univ = 1 := by
      rw [Measure.map_apply (hXs t) MeasurableSet.univ]
      simp
    calc ∫⁻ x, lam x ∂(P.map (X t)) ≤ ∫⁻ _, C ∂(P.map (X t)) := hle
      _ = C * (P.map (X t)) univ := by rw [lintegral_const]
      _ = C := by rw [hmap, mul_one]
      _ < ⊤ := lt_top_iff_ne_top.2 hC
  refine meanJumpIntensity_spontaneous hfin (fun Γ hΓ => ?_) (fun Γ hΓ t ht => ?_)
  · have hfun : (fun s : ℝ => ∫⁻ x in Γ, lam x ∂(P.map (X s)))
        = fun s : ℝ => ∫⁻ x, Γ.indicator lam x ∂(P.map (X s)) := by
      funext s
      rw [lintegral_indicator hΓ]
    rw [hfun]
    exact measurable_lawLintegral hX (hlam.indicator hΓ)
  · rw [hR Γ hΓ t ht, lintegral_pathOccupation_swap hX (hlam.indicator hΓ) t]
    refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    rw [lintegral_indicator hΓ]

end GSHS
