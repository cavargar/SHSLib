/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eqs. (6) and (7) of Bect (2010): the Lévy-system process `H` and the jump measure `R`

Section 2.3 of the paper introduces the predictable increasing process

  `H_t = ∫₀ᵗ λ(X_s) ds + Σ_{τ_k ≤ t} 1_{X_{τ_k}⁻ ∈ G}`,        (6)

whose two summands account respectively for the *spontaneous* jumps (triggered randomly
in time with stochastic intensity `λ(X_t)`) and the *forced* jumps (triggered when the
process hits the guard set `G`).  Section 3.1 introduces the jump measure

  `R(A) = E{ Σ_{k ≥ 1} 1_A(X_{τ_k}⁻, τ_k) }`                    (7)

on `E × (0; +∞)`, whose value on `Γ × (0;t]` is the expected number of jumps starting
from `Γ` before time `t`, and splits it as `R = R⁰ + R^G` according to whether the
pre-jump state lies in `E⁰ = E \ G` or in `G`.

Formalized here:

* `GSHS.levyHspont`, `GSHS.levyHforced`, `GSHS.levyH` — the two parts of Eq. (6) and
  their sum, with `GSHS.levyH_eq_add`, `GSHS.levyH_zero`, `GSHS.monotone_levyH`
  (`H` is increasing, as asserted in the paper) and measurability in `ω`;
* `GSHS.jumpMeasureR` — Eq. (7), with `GSHS.jumpMeasureR_apply` and
  `GSHS.jumpMeasureR_prod_Ioc` (the expected number of jumps from `Γ` in `(0;t]`);
* `GSHS.jumpMeasureR_split` — the splitting `R = R⁰ + R^G` of Section 3.1, and
  `GSHS.meanJumpIntensity_of_split`, which assembles a mean jump intensity for `R` out
  of mean jump intensities for the two parts.
-/
import SHSLib.FPK.LevySystemIntensity

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GSHS

variable {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]

/-! ## Eq. (6): the predictable increasing process `H` -/

/-- The *spontaneous* part of Eq. (6): `∫₀ᵗ λ(X_s) ds`, the compensator of the jumps
triggered randomly in time with stochastic intensity `λ(X_t)`. -/
def levyHspont (lam : E → ℝ≥0∞) (X : ℝ → Omega → E) (t : ℝ) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) t, lam (X s ω)

/-- The *forced* part of Eq. (6): `Σ_{0 < τ_k ≤ t} 1_{X_{τ_k}⁻ ∈ G}`, which counts the
jumps that occurred before time `t` from the guard set `G`. -/
def levyHforced (tau : ℕ → Omega → ℝ) (Xpre : ℕ → Omega → E) (G : Set E) (t : ℝ)
    (ω : Omega) : ℝ≥0∞ :=
  ∑' k : ℕ, (Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ≥0∞)) (tau k ω)
    * G.indicator (fun _ => (1 : ℝ≥0∞)) (Xpre k ω)

/-- **Eq. (6)**: the predictable increasing process of the Lévy system `(K, H)`,
`H_t = ∫₀ᵗ λ(X_s) ds + Σ_{0 < τ_k ≤ t} 1_{X_{τ_k}⁻ ∈ G}`. -/
def levyH (lam : E → ℝ≥0∞) (X : ℝ → Omega → E) (tau : ℕ → Omega → ℝ)
    (Xpre : ℕ → Omega → E) (G : Set E) (t : ℝ) (ω : Omega) : ℝ≥0∞ :=
  levyHspont lam X t ω + levyHforced tau Xpre G t ω

omit [MeasurableSpace Omega] [MeasurableSpace E] in
theorem levyH_eq_add (lam : E → ℝ≥0∞) (X : ℝ → Omega → E) (tau : ℕ → Omega → ℝ)
    (Xpre : ℕ → Omega → E) (G : Set E) (t : ℝ) (ω : Omega) :
    levyH lam X tau Xpre G t ω = levyHspont lam X t ω + levyHforced tau Xpre G t ω :=
  rfl

omit [MeasurableSpace Omega] [MeasurableSpace E] in
/-- The process `H` starts at `0`. -/
theorem levyH_zero (lam : E → ℝ≥0∞) (X : ℝ → Omega → E) (tau : ℕ → Omega → ℝ)
    (Xpre : ℕ → Omega → E) (G : Set E) (ω : Omega) :
    levyH lam X tau Xpre G 0 ω = 0 := by
  simp [levyH, levyHspont, levyHforced]

omit [MeasurableSpace Omega] [MeasurableSpace E] in
theorem monotone_levyHspont (lam : E → ℝ≥0∞) (X : ℝ → Omega → E) (ω : Omega) :
    Monotone fun t : ℝ => levyHspont lam X t ω := fun _ _ htu =>
  lintegral_mono_set (Ioc_subset_Ioc_right htu)

omit [MeasurableSpace Omega] [MeasurableSpace E] in
theorem monotone_levyHforced (tau : ℕ → Omega → ℝ) (Xpre : ℕ → Omega → E) (G : Set E)
    (ω : Omega) : Monotone fun t : ℝ => levyHforced tau Xpre G t ω := by
  intro t u htu
  refine ENNReal.tsum_le_tsum fun k => mul_le_mul_left ?_ _
  by_cases hk : tau k ω ∈ Ioc (0 : ℝ) t
  · rw [indicator_of_mem hk, indicator_of_mem (Ioc_subset_Ioc_right htu hk)]
  · rw [indicator_of_notMem hk]; exact zero_le _

omit [MeasurableSpace Omega] [MeasurableSpace E] in
/-- `H` is an increasing process, as required of a Lévy system. -/
theorem monotone_levyH (lam : E → ℝ≥0∞) (X : ℝ → Omega → E) (tau : ℕ → Omega → ℝ)
    (Xpre : ℕ → Omega → E) (G : Set E) (ω : Omega) :
    Monotone fun t : ℝ => levyH lam X tau Xpre G t ω := fun _ _ htu =>
  add_le_add (monotone_levyHspont lam X ω htu) (monotone_levyHforced tau Xpre G ω htu)

theorem measurable_levyHforced {tau : ℕ → Omega → ℝ} {Xpre : ℕ → Omega → E} {G : Set E}
    (htau : ∀ k, Measurable (tau k)) (hXpre : ∀ k, Measurable (Xpre k))
    (hG : MeasurableSet G) (t : ℝ) :
    Measurable fun ω => levyHforced tau Xpre G t ω := by
  refine Measurable.ennreal_tsum fun k => ?_
  exact ((measurable_one.indicator measurableSet_Ioc).comp (htau k)).mul
    ((measurable_one.indicator hG).comp (hXpre k))

theorem measurable_levyHspont {lam : E → ℝ≥0∞} {X : ℝ → Omega → E}
    (hlam : Measurable lam) (hX : Measurable (Function.uncurry X)) (t : ℝ) :
    Measurable fun ω => levyHspont lam X t ω := by
  have hmeas : Measurable fun p : Omega × ℝ => lam (X p.2 p.1) :=
    hlam.comp (hX.comp (measurable_snd.prodMk measurable_fst))
  exact hmeas.lintegral_prod_right'

theorem measurable_levyH {lam : E → ℝ≥0∞} {X : ℝ → Omega → E} {tau : ℕ → Omega → ℝ}
    {Xpre : ℕ → Omega → E} {G : Set E}
    (hlam : Measurable lam) (hX : Measurable (Function.uncurry X))
    (htau : ∀ k, Measurable (tau k)) (hXpre : ∀ k, Measurable (Xpre k))
    (hG : MeasurableSet G) (t : ℝ) :
    Measurable fun ω => levyH lam X tau Xpre G t ω :=
  (measurable_levyHspont hlam hX t).add (measurable_levyHforced htau hXpre hG t)

/-! ## Eq. (7): the jump measure `R` and its splitting -/

/-- **Eq. (7)**: the positive measure `R` on `E × ℝ` defined by
`R(A) = E{ Σ_{k ≥ 1} 1_A(X_{τ_k}⁻, τ_k) }`, i.e. the sum over `k` of the laws of the
pairs `(X_{τ_k}⁻, τ_k)`. -/
def jumpMeasureR (P : Measure Omega) (tau : ℕ → Omega → ℝ) (Xpre : ℕ → Omega → E) :
    Measure (E × ℝ) :=
  Measure.sum fun k => P.map fun ω => (Xpre k ω, tau k ω)

/-- Eq. (7) evaluated on a measurable set: `R(A) = Σ_k P{ (X_{τ_k}⁻, τ_k) ∈ A }`. -/
theorem jumpMeasureR_apply (P : Measure Omega) {tau : ℕ → Omega → ℝ}
    {Xpre : ℕ → Omega → E} (htau : ∀ k, Measurable (tau k))
    (hXpre : ∀ k, Measurable (Xpre k)) {A : Set (E × ℝ)} (hA : MeasurableSet A) :
    jumpMeasureR P tau Xpre A = ∑' k, P {ω | (Xpre k ω, tau k ω) ∈ A} := by
  rw [jumpMeasureR, Measure.sum_apply _ hA]
  exact tsum_congr fun k =>
    Measure.map_apply ((hXpre k).prodMk (htau k)) hA

/-- `R(Γ × (0;t])` is the expected number of jumps starting from `Γ` during `(0;t]`. -/
theorem jumpMeasureR_prod_Ioc (P : Measure Omega) {tau : ℕ → Omega → ℝ}
    {Xpre : ℕ → Omega → E} (htau : ∀ k, Measurable (tau k))
    (hXpre : ∀ k, Measurable (Xpre k)) {Γ : Set E} (hΓ : MeasurableSet Γ) (t : ℝ) :
    jumpMeasureR P tau Xpre (Γ ×ˢ Ioc (0 : ℝ) t)
      = ∑' k, P {ω | Xpre k ω ∈ Γ ∧ tau k ω ∈ Ioc (0 : ℝ) t} := by
  rw [jumpMeasureR_apply P htau hXpre (hΓ.prod measurableSet_Ioc)]
  rfl

/-- The splitting `R = R⁰ + R^G` of Section 3.1: the jumps are separated according to
whether the pre-jump state lies outside or inside the guard set `G`. -/
theorem jumpMeasureR_split (P : Measure Omega) (tau : ℕ → Omega → ℝ)
    (Xpre : ℕ → Omega → E) {G : Set E} (hG : MeasurableSet G) :
    jumpMeasureR P tau Xpre
      = (jumpMeasureR P tau Xpre).restrict (Gᶜ ×ˢ (univ : Set ℝ))
        + (jumpMeasureR P tau Xpre).restrict (G ×ˢ (univ : Set ℝ)) := by
  have hmeas : MeasurableSet (G ×ˢ (univ : Set ℝ)) := hG.prod MeasurableSet.univ
  have hcompl : (G ×ˢ (univ : Set ℝ))ᶜ = Gᶜ ×ˢ (univ : Set ℝ) := by
    ext p; simp
  rw [← hcompl, add_comm]
  exact (Measure.restrict_add_restrict_compl (μ := jumpMeasureR P tau Xpre) hmeas).symm

/-- If both parts of the splitting `R = R⁰ + R^G` admit a mean jump intensity, then so
does `R`, with intensity `r_t = r_t⁰ + r_t^G`.  This is how Definition 6 is verified in
the paper: `r⁰` always exists (Eq. (8)), and the existence of `r^G` is the content of
Theorem 8. -/
theorem meanJumpIntensity_of_split {R R0 RG : Measure (E × ℝ)} {r0 rG : ℝ → Measure E}
    (hsum : R = R0 + RG) (h0 : MeanJumpIntensity R0 r0) (hG : MeanJumpIntensity RG rG) :
    MeanJumpIntensity R (fun t => r0 t + rG t) := by
  subst hsum
  exact MeanJumpIntensity.add h0 hG

/-! ## Eq. (5): from the Lévy-system identity to the spontaneous mean jump intensity -/

/-- **Eq. (5) applied to `φ(x, y) = 1_Γ(x)`**, together with the splitting (6) of the
Lévy-system process `H` into its spontaneous and forced parts, reads

  `R(Γ × (0;t]) = E{ ∫₀ᵗ 1_Γ(X_s) λ(X_s) ds } + R((Γ ∩ G) × (0;t])`.

Since the stochastic intensity `λ` vanishes on the guard set, this identity determines
the spontaneous part `R⁰ = R|_{E⁰ × ℝ}` of the jump measure: it says precisely that
`R⁰(Γ × (0;t]) = E{ ∫₀ᵗ 1_Γ(X_s) λ(X_s) ds }`, the hypothesis `hR` of
`GSHS.meanJumpIntensity_spontaneous_of_levy`. -/
theorem levySystem_spontaneous_part {P : Measure Omega} {X : ℝ → Omega → E}
    {lam : E → ℝ≥0∞} {R : Measure (E × ℝ)} {G : Set E} (hG : MeasurableSet G)
    (hlamG : ∀ x ∈ G, lam x = 0)
    (hlevy : ∀ Γ : Set E, MeasurableSet Γ → ∀ t : ℝ, 0 ≤ t →
      R (Γ ×ˢ Ioc (0 : ℝ) t)
        = (∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t, Γ.indicator lam (X s ω)) ∂P)
          + R ((Γ ∩ G) ×ˢ Ioc (0 : ℝ) t)) :
    ∀ Γ : Set E, MeasurableSet Γ → ∀ t : ℝ, 0 ≤ t →
      (R.restrict (Gᶜ ×ˢ (univ : Set ℝ))) (Γ ×ˢ Ioc (0 : ℝ) t)
        = ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t, Γ.indicator lam (X s ω)) ∂P := by
  intro Γ hΓ t ht
  have hinter : (Γ ×ˢ Ioc (0 : ℝ) t) ∩ (Gᶜ ×ˢ (univ : Set ℝ))
      = (Γ ∩ Gᶜ) ×ˢ Ioc (0 : ℝ) t := by
    rw [Set.prod_inter_prod, Set.inter_univ]
  have hempty : ((Γ ∩ Gᶜ) ∩ G) ×ˢ Ioc (0 : ℝ) t = (∅ : Set (E × ℝ)) := by
    have : (Γ ∩ Gᶜ) ∩ G = (∅ : Set E) := by
      ext x; simp +contextual
    rw [this, Set.empty_prod]
  have hind : (Γ ∩ Gᶜ).indicator lam = Γ.indicator lam := by
    funext x
    by_cases hx : x ∈ Γ
    · by_cases hxG : x ∈ G
      · rw [indicator_of_notMem (by simp [hxG]), indicator_of_mem hx, hlamG x hxG]
      · rw [indicator_of_mem (show x ∈ Γ ∩ Gᶜ from ⟨hx, hxG⟩), indicator_of_mem hx]
    · rw [indicator_of_notMem (fun h => hx h.1), indicator_of_notMem hx]
  rw [Measure.restrict_apply (hΓ.prod measurableSet_Ioc), hinter,
    hlevy (Γ ∩ Gᶜ) (hΓ.inter hG.compl) t ht, hempty]
  simp [hind]

/-- **Eq. (8) from the Lévy system (5)–(6)**: the spontaneous part `R⁰` of the jump
measure always admits the mean jump intensity `r_t⁰ = λ · μ_t`. -/
theorem meanJumpIntensity_spontaneous_of_levySystem {P : Measure Omega}
    [IsProbabilityMeasure P] {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X))
    {lam : E → ℝ≥0∞} (hlam : Measurable lam) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hlam_le : ∀ x, lam x ≤ C) {R : Measure (E × ℝ)} {G : Set E} (hG : MeasurableSet G)
    (hlamG : ∀ x ∈ G, lam x = 0)
    (hlevy : ∀ Γ : Set E, MeasurableSet Γ → ∀ t : ℝ, 0 ≤ t →
      R (Γ ×ˢ Ioc (0 : ℝ) t)
        = (∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t, Γ.indicator lam (X s ω)) ∂P)
          + R ((Γ ∩ G) ×ˢ Ioc (0 : ℝ) t)) :
    MeanJumpIntensity (R.restrict (Gᶜ ×ˢ (univ : Set ℝ)))
      (fun t => (P.map (X t)).withDensity lam) :=
  meanJumpIntensity_spontaneous_of_levy hX hlam hC hlam_le
    (levySystem_spontaneous_part hG hlamG hlevy)

end GSHS
