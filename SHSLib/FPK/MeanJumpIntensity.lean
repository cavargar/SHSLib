/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mean jump intensity of a general stochastic hybrid system

Formalization of Section 3 of

  J. Bect, "A unifying formulation of the Fokker–Planck–Kolmogorov equation
  for general stochastic hybrid systems", Nonlinear Analysis: Hybrid Systems 4 (2010).

The measure `R` on `E × (0;∞)` of Eq. (7) records the pre-jump locations and the
jump times of the process:

  `R(A) = E{ Σ_{k ≥ 1} 1_A(X_{τ_k}⁻, τ_k) }`,

so that `R(Γ × (0;t])` is the expected number of jumps out of `Γ` before time `t`.
Definition 6 asks for a *density in time* of this measure: a family `t ↦ r t` of
bounded positive measures on `E` with `R(Γ × (0;t]) = ∫₀ᵗ r_s(Γ) ds`.

This file contains:

* `GSHS.MeanJumpIntensity` — Definition 6;
* `GSHS.MeanJumpIntensity.eq_of_lt_of_forall` — a mean jump intensity forces the
  expected-jump-count function `t ↦ R(Γ × (0;t])` to have no jump discontinuity
  (the obstruction used in Section 3.2 to rule out its existence);
* `GSHS.meanJumpIntensity_spontaneous` — Eq. (8): for spontaneous jumps with
  stochastic intensity `λ`, the measure `r_t = λ · μ_t` is a mean jump intensity.
-/
import Mathlib

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

/-- Monotone convergence for set-Lebesgue integrals along an increasing sequence of sets. -/
private theorem lintegral_iUnion_monotone {α : Type*} [MeasurableSpace α] {m : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (s : ℕ → Set α)
    (hm : ∀ n, MeasurableSet (s n)) (hmono : Monotone s) :
    ∫⁻ x in ⋃ n, s n, f x ∂m = ⨆ n, ∫⁻ x in s n, f x ∂m := by
  have h1 : ∀ n, ∫⁻ x in s n, f x ∂m = ∫⁻ x, (s n).indicator f x ∂m := by
    intro n; rw [lintegral_indicator (hm n)]
  have h2 : ∫⁻ x in ⋃ n, s n, f x ∂m = ∫⁻ x, (⋃ n, s n).indicator f x ∂m := by
    rw [lintegral_indicator (MeasurableSet.iUnion hm)]
  simp only [h1, h2]
  rw [← lintegral_iSup (fun n => (hf.indicator (hm n))) ?_]
  · congr 1
    funext x
    by_cases hx : x ∈ ⋃ n, s n
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      rw [indicator_of_mem hx]
      exact le_antisymm (le_iSup_of_le n (by rw [indicator_of_mem hn]))
        (iSup_le fun k => indicator_le_self _ _ x)
    · rw [indicator_of_notMem hx]
      refine le_antisymm (zero_le _) (iSup_le fun k => ?_)
      rw [indicator_of_notMem (fun h => hx (mem_iUnion.mpr ⟨k, h⟩))]
  · intro a b hab x
    simp only
    by_cases hx : x ∈ s a
    · rw [indicator_of_mem hx, indicator_of_mem (hmono hab hx)]
    · rw [indicator_of_notMem hx]; exact zero_le _

variable {E : Type*} [MeasurableSpace E]

/-- **Definition 6** (Bect, 2010): a *mean jump intensity* for the jump measure `R`
of Eq. (7).

`r` assigns to each time `t ≥ 0` a bounded positive measure `r t` on the hybrid state
space `E`, such that `t ↦ r t Γ` is measurable and

  `R (Γ × (0; t]) = ∫₀ᵗ r_s(Γ) ds`   for every measurable `Γ` and every `t ≥ 0`. -/
structure MeanJumpIntensity (R : Measure (E × ℝ)) (r : ℝ → Measure E) : Prop where
  /-- Each `r t` is a bounded (finite) positive measure. -/
  isFiniteMeasure : ∀ t : ℝ, IsFiniteMeasure (r t)
  /-- Definition 6(a): `t ↦ r_t(Γ)` is measurable. -/
  measurable_apply : ∀ Γ : Set E, MeasurableSet Γ → Measurable fun s : ℝ => r s Γ
  /-- Definition 6(b): `R(Γ × (0;t]) = ∫₀ᵗ r_s(Γ) ds`. -/
  lintegral_eq : ∀ Γ : Set E, MeasurableSet Γ → ∀ t : ℝ, 0 ≤ t →
    R (Γ ×ˢ Ioc (0 : ℝ) t) = ∫⁻ s in Ioc (0 : ℝ) t, r s Γ

namespace MeanJumpIntensity

variable {R : Measure (E × ℝ)} {r : ℝ → Measure E}

/-- The expected jump count `t ↦ R(Γ × (0;t])` is left-continuous whenever a mean
jump intensity exists: if it is constant on `[0;t)` then it takes the same value at `t`.

This is the key obstruction used in Section 3.2: a jump measure whose expected jump
count has a genuine jump discontinuity admits no mean jump intensity. -/
theorem eq_of_lt_of_forall (h : MeanJumpIntensity R r) {Γ : Set E} (hΓ : MeasurableSet Γ)
    {t : ℝ} (ht : 0 < t) {c : ℝ≥0∞}
    (hc : ∀ u : ℝ, 0 ≤ u → u < t → R (Γ ×ˢ Ioc (0 : ℝ) u) = c) :
    R (Γ ×ˢ Ioc (0 : ℝ) t) = c := by
  classical
  set f : ℝ → ℝ≥0∞ := fun s => r s Γ with hf
  have hfmeas : Measurable f := h.measurable_apply Γ hΓ
  -- the approximating sequence `u n ↑ t`
  set u : ℕ → ℝ := fun n => t - t / (n + 1) with hu
  have hu0 : ∀ n, 0 ≤ u n := by
    intro n
    have h1 : t / ((n : ℝ) + 1) ≤ t := by
      have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      calc t / ((n : ℝ) + 1) ≤ t / 1 := by
            exact div_le_div_of_nonneg_left ht.le zero_lt_one h2
        _ = t := by ring
    simp only [hu]
    linarith
  have hult : ∀ n, u n < t := by
    intro n
    have : 0 < t / ((n : ℝ) + 1) := by positivity
    simp only [hu]
    linarith
  have hmono : Monotone fun n => Ioc (0 : ℝ) (u n) := by
    intro a b hab
    apply Ioc_subset_Ioc_right
    have h1 : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have h2 : t / ((b : ℝ) + 1) ≤ t / ((a : ℝ) + 1) :=
      div_le_div_of_nonneg_left ht.le (by positivity) h1
    simp only [hu]
    linarith
  have hunion : ⋃ n, Ioc (0 : ℝ) (u n) = Ioo (0 : ℝ) t := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨n, hx0, hxn⟩
      exact ⟨hx0, lt_of_le_of_lt hxn (hult n)⟩
    · rintro ⟨hx0, hxt⟩
      have hpos : 0 < t - x := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (t / (t - x))
      refine ⟨n, hx0, ?_⟩
      have h1 : t / ((n : ℝ) + 1) ≤ t - x := by
        rw [div_le_iff₀ (by positivity)]
        have hx : t / (t - x) * (t - x) = t := by field_simp
        nlinarith [hn, hpos]
      simp only [hu]
      linarith
  have hkey : ∫⁻ s in Ioo (0 : ℝ) t, f s = ⨆ n, ∫⁻ s in Ioc (0 : ℝ) (u n), f s := by
    rw [← hunion, lintegral_iUnion_monotone hfmeas _ (fun n => measurableSet_Ioc) hmono]
  have hIoo : ∫⁻ s in Ioc (0 : ℝ) t, f s = ∫⁻ s in Ioo (0 : ℝ) t, f s := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [h.lintegral_eq Γ hΓ t ht.le, hIoo, hkey]
  have heq : ∀ n, ∫⁻ s in Ioc (0 : ℝ) (u n), f s = c := by
    intro n
    rw [← h.lintegral_eq Γ hΓ (u n) (hu0 n)]
    exact hc (u n) (hu0 n) (hult n)
  simp [heq]

end MeanJumpIntensity

/-- **Eq. (8)** (Bect, 2010): for *spontaneous* jumps, a mean jump intensity always
exists, and it is the stochastic intensity `λ` averaged against the law `μ_t` of the
state, i.e. `r_t(Γ) = E(λ(X_t) 1_{X_t ∈ Γ}) = ∫_Γ λ dμ_t`.

Here `R₀` is the spontaneous part of the jump measure; the Lévy-system identity (5)
gives `R₀(Γ × (0;t]) = E ∫₀ᵗ 1_Γ(X_s) λ(X_s) ds = ∫₀ᵗ (∫_Γ λ dμ_s) ds`, which is the
hypothesis `hR` below. -/
theorem meanJumpIntensity_spontaneous {R₀ : Measure (E × ℝ)} {μ : ℝ → Measure E}
    {lam : E → ℝ≥0∞}
    (hfin : ∀ t : ℝ, IsFiniteMeasure ((μ t).withDensity lam))
    (hmeas : ∀ Γ : Set E, MeasurableSet Γ → Measurable fun s : ℝ => ∫⁻ x in Γ, lam x ∂(μ s))
    (hR : ∀ Γ : Set E, MeasurableSet Γ → ∀ t : ℝ, 0 ≤ t →
      R₀ (Γ ×ˢ Ioc (0 : ℝ) t) = ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ x in Γ, lam x ∂(μ s)) :
    MeanJumpIntensity R₀ (fun t => (μ t).withDensity lam) where
  isFiniteMeasure := hfin
  measurable_apply := by
    intro Γ hΓ
    have hrw : (fun s : ℝ => ((μ s).withDensity lam) Γ)
        = fun s : ℝ => ∫⁻ x in Γ, lam x ∂(μ s) := by
      funext s
      rw [withDensity_apply _ hΓ]
    rw [hrw]
    exact hmeas Γ hΓ
  lintegral_eq := by
    intro Γ hΓ t ht
    rw [hR Γ hΓ t ht]
    refine setLIntegral_congr_fun measurableSet_Ioc ?_
    intro s _
    simp only [withDensity_apply lam hΓ]

/-! ## Splitting into spontaneous and forced jumps, and essential uniqueness -/

/-- Section 3.1: the jump measure `R` splits as `R = R⁰ + R^G` into its spontaneous and
forced parts.  Mean jump intensities add accordingly: if `r⁰` is a mean jump intensity
for `R⁰` and `r^G` one for `R^G`, then `r⁰ + r^G` is a mean jump intensity for `R`. -/
theorem MeanJumpIntensity.add {R₁ R₂ : Measure (E × ℝ)} {r₁ r₂ : ℝ → Measure E}
    (h₁ : MeanJumpIntensity R₁ r₁) (h₂ : MeanJumpIntensity R₂ r₂) :
    MeanJumpIntensity (R₁ + R₂) (fun t => r₁ t + r₂ t) where
  isFiniteMeasure := by
    intro t
    have h1 := h₁.isFiniteMeasure t
    have h2 := h₂.isFiniteMeasure t
    infer_instance
  measurable_apply := by
    intro Γ hΓ
    simpa using (h₁.measurable_apply Γ hΓ).add (h₂.measurable_apply Γ hΓ)
  lintegral_eq := by
    intro Γ hΓ t ht
    have hm₁ : Measurable fun s : ℝ => r₁ s Γ := h₁.measurable_apply Γ hΓ
    simp only [Measure.coe_add, Pi.add_apply]
    rw [h₁.lintegral_eq Γ hΓ t ht, h₂.lintegral_eq Γ hΓ t ht, ← lintegral_add_left hm₁]

/-- The lower integrals of two measurable functions over all intervals `(0;t]` determine
them almost everywhere on `(0;∞)`, provided those integrals are finite. -/
theorem ae_eq_of_setLIntegral_Ioc_eq {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfin : ∀ t : ℝ, 0 ≤ t → (∫⁻ s in Ioc (0:ℝ) t, f s) ≠ ⊤)
    (heq : ∀ t : ℝ, 0 ≤ t → (∫⁻ s in Ioc (0:ℝ) t, f s) = ∫⁻ s in Ioc (0:ℝ) t, g s) :
    f =ᵐ[volume.restrict (Ioi (0:ℝ))] g := by
  have key : ∀ c d : ℝ, 0 ≤ c → (∫⁻ s in Ioc c d, f s) = ∫⁻ s in Ioc c d, g s := by
    intro c d hc
    rcases le_or_gt c d with hcd | hdc
    · have hdisj : Disjoint (Ioc (0:ℝ) c) (Ioc c d) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, hx2⟩ ⟨hx3, -⟩
        linarith
      have hsplit : ∀ h : ℝ → ℝ≥0∞,
          (∫⁻ s in Ioc (0:ℝ) c, h s) + (∫⁻ s in Ioc c d, h s) = ∫⁻ s in Ioc (0:ℝ) d, h s := by
        intro h
        rw [← lintegral_union measurableSet_Ioc hdisj, Set.Ioc_union_Ioc_eq_Ioc hc hcd]
      have h1 := hsplit f
      have h2 := hsplit g
      have h3 : (∫⁻ s in Ioc (0:ℝ) c, f s) = ∫⁻ s in Ioc (0:ℝ) c, g s := heq c hc
      have h4 : (∫⁻ s in Ioc (0:ℝ) d, f s) = ∫⁻ s in Ioc (0:ℝ) d, g s := heq d (hc.trans hcd)
      rw [h3, h4] at h1
      exact (ENNReal.add_right_inj (by rw [← h3]; exact hfin c hc)).1 (h1.trans h2.symm)
    · rw [Set.Ioc_eq_empty (not_lt.mpr hdc.le)]
      simp
  set nu : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hnudef
  have hinter : ∀ a b : ℝ, Ioc a b ∩ Ioi (0:ℝ) = Ioc (max a 0) b := by
    intro a b
    ext x
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
    tauto
  have happ : ∀ (h : ℝ → ℝ≥0∞) (a b : ℝ), (nu.withDensity h) (Ioc a b)
      = ∫⁻ s in Ioc (max a 0) b, h s := by
    intro h a b
    rw [withDensity_apply _ measurableSet_Ioc, hnudef,
      Measure.restrict_restrict measurableSet_Ioc, hinter]
  have hlf : IsLocallyFiniteMeasure (nu.withDensity f) := by
    constructor
    intro x
    refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    refine lt_of_le_of_lt (measure_mono (Ioo_subset_Ioc_self (a := x - 1) (b := x + 1))) ?_
    rw [happ f]
    refine lt_of_le_of_lt (lintegral_mono_set (Ioc_subset_Ioc_left (le_max_right (x - 1) 0))) ?_
    rcases le_or_gt 0 (x + 1) with hx | hx
    · exact lt_top_iff_ne_top.2 (hfin (x + 1) hx)
    · rw [Set.Ioc_eq_empty (not_lt.mpr hx.le)]; simp
  have hmu : nu.withDensity f = nu.withDensity g :=
    Measure.ext_of_Ioc _ _ fun a b _ => by
      rw [happ f, happ g, key _ _ (le_max_right a 0)]
  exact (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable hg.aemeasurable).1 hmu

/-- **Essential uniqueness of the mean jump intensity** (Definition 6).  Two mean jump
intensities for the same jump measure `R` agree, for each measurable set `Γ`, at almost
every time `t > 0`.  The finiteness hypothesis is the standing assumption `E(N_t) < ∞`
of Section 3, which makes the restriction of `R` to `E × (0;t]` a bounded measure. -/
theorem MeanJumpIntensity.ae_eq {R : Measure (E × ℝ)} {r r' : ℝ → Measure E}
    (h : MeanJumpIntensity R r) (h' : MeanJumpIntensity R r')
    {Γ : Set E} (hΓ : MeasurableSet Γ)
    (hfin : ∀ t : ℝ, 0 ≤ t → R (Γ ×ˢ Ioc (0:ℝ) t) ≠ ⊤) :
    (fun t => r t Γ) =ᵐ[volume.restrict (Ioi (0:ℝ))] fun t => r' t Γ := by
  refine ae_eq_of_setLIntegral_Ioc_eq (h.measurable_apply Γ hΓ) (h'.measurable_apply Γ hΓ)
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [← h.lintegral_eq Γ hΓ t ht]
    exact hfin t ht
  · rw [← h.lintegral_eq Γ hΓ t ht, ← h'.lintegral_eq Γ hΓ t ht]

end GSHS
