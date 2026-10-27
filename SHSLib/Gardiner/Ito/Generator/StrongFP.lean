/-
# The Fokker–Planck equation in strong form (Gardiner (4.3.19)–(4.3.20))

* `itoFPRHS a b p t y = -∂_y[a(y, t) p(t, y)] + ½ ∂²_y[b(y, t)² p(t, y)]`, the right-hand side
  of (4.3.20) (the one-dimensional, time-dependent analogue of `Gardiner.fpRHS`, with diffusion
  coefficient `B = b²`).
* `integral_itoGen_mul_density`: integration by parts (no surface terms, since `φ ∈ C²_c`):
  `∫ L φ(·, t) p(t, ·) = ∫ φ · itoFPRHS a b p t`.
* `hasDerivAt_integral_mul_density`: `d/dt ∫ φ p(t, ·) = ∫ φ ∂ₜp(t, ·)` for `φ ∈ C_c`, if `∂ₜp`
  exists and is jointly continuous.
* `strongFP_of_weakFP`: **(4.3.19) ⇒ (4.3.20)**: if a density `p` satisfies the weak equation
  `d/dt ∫ φ p(t, ·) = ∫ L φ(·, t) p(t, ·)` for every `φ ∈ C²_c`, then
  `∂ₜp(t, y) = itoFPRHS a b p t y` for every `y` ("since `f(x)` is arbitrary").
* `IsSDESol.strongFP`: if the law of a solution of a Lipschitz SDE has a density with the
  regularity Gardiner assumes, the density solves (4.3.20) pointwise.

Regularity hypotheses (on an open time interval `(t₁, t₂)`): `p(s, ·)` continuous; `∂ₜp` exists
and is jointly continuous; `y ↦ a(y, s) p(s, y)` is `C¹` and `y ↦ b(y, s)² p(s, y)` is `C²`.
-/
import SHSLib.Gardiner.Ito.Generator.WeakFP

open MeasureTheory ProbabilityTheory Filter Topology Set

noncomputable section

namespace Gardiner.Ito.Generator

open Gardiner.Ito Gardiner.Ito.StochDE

/-- **The right-hand side of the Fokker–Planck equation (4.3.20)**:
`-∂_y[a(y, t) p(t, y)] + ½ ∂²_y[b(y, t)² p(t, y)]`. -/
def itoFPRHS (a b : ℝ → ℝ → ℝ) (p : ℝ → ℝ → ℝ) (t y : ℝ) : ℝ :=
  -deriv (fun z => a z t * p t z) y + 1 / 2 * deriv (deriv fun z => b z t ^ 2 * p t z) y

section IBP

variable {φ : ℝ → ℝ}

lemma IsC2c.continuous_deriv (hφ : IsC2c φ) : Continuous (deriv φ) :=
  (contDiff_one_deriv hφ.contDiff).continuous

lemma IsC2c.continuous_deriv2 (hφ : IsC2c φ) : Continuous (deriv (deriv φ)) :=
  continuous_deriv2_of_contDiff hφ.contDiff

lemma IsC2c.hasDerivAt (hφ : IsC2c φ) (y : ℝ) : HasDerivAt φ (deriv φ y) y :=
  ((hφ.contDiff.differentiable (by norm_num)) y).hasDerivAt

lemma IsC2c.hasDerivAt_deriv (hφ : IsC2c φ) (y : ℝ) :
    HasDerivAt (deriv φ) (deriv (deriv φ) y) y :=
  (((contDiff_one_deriv hφ.contDiff).differentiable one_ne_zero) y).hasDerivAt

/-- A continuous function times a compactly supported continuous function is integrable. -/
lemma integrable_mul_of_compact {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hhs : HasCompactSupport h) : Integrable (g * h) :=
  (hg.mul hh).integrable_of_hasCompactSupport hhs.mul_left

/-- **Integration by parts** behind (4.3.19) ⇒ (4.3.20): for `φ ∈ C²_c`, `A ∈ C¹`, `B ∈ C²`,
`∫ (A φ' + B/2 φ'') = ∫ φ (-A' + ½ B'')`. -/
theorem integral_ibp_generator (hφ : IsC2c φ) {A Bf : ℝ → ℝ} (hA : ContDiff ℝ 1 A)
    (hB : ContDiff ℝ 2 Bf) :
    ∫ y, (A y * deriv φ y + Bf y / 2 * deriv (deriv φ) y) =
      ∫ y, φ y * (-deriv A y + 1 / 2 * deriv (deriv Bf) y) := by
  have hφs := hφ.hasCompactSupport
  have hφ1s : HasCompactSupport (deriv φ) := hφs.deriv
  have hφ2s : HasCompactSupport (deriv (deriv φ)) := hφ1s.deriv
  have hAc := hA.continuous
  have hA1 : Continuous (deriv A) := hA.continuous_deriv le_rfl
  have hAd : ∀ y, HasDerivAt A (deriv A y) y :=
    fun y => ((hA.differentiable one_ne_zero) y).hasDerivAt
  have hBc := hB.continuous
  have hB1 : ContDiff ℝ 1 (deriv Bf) := contDiff_one_deriv hB
  have hB2 : Continuous (deriv (deriv Bf)) := continuous_deriv2_of_contDiff hB
  have hBd : ∀ y, HasDerivAt Bf (deriv Bf y) y :=
    fun y => ((hB.differentiable (by norm_num)) y).hasDerivAt
  have hBd' : ∀ y, HasDerivAt (deriv Bf) (deriv (deriv Bf) y) y :=
    fun y => ((hB1.differentiable one_ne_zero) y).hasDerivAt
  -- `∫ A φ' = -∫ A' φ`
  have I1 := integral_mul_deriv_eq_deriv_mul_of_integrable hAd hφ.hasDerivAt
    (integrable_mul_of_compact hAc hφ.continuous_deriv hφ1s)
    (integrable_mul_of_compact hA1 hφ.contDiff.continuous hφs)
    (integrable_mul_of_compact hAc hφ.contDiff.continuous hφs)
  -- `∫ B φ'' = -∫ B' φ'`
  have I2 := integral_mul_deriv_eq_deriv_mul_of_integrable hBd hφ.hasDerivAt_deriv
    (integrable_mul_of_compact hBc hφ.continuous_deriv2 hφ2s)
    (integrable_mul_of_compact hB1.continuous hφ.continuous_deriv hφ1s)
    (integrable_mul_of_compact hBc hφ.continuous_deriv hφ1s)
  -- `∫ B' φ' = -∫ B'' φ`
  have I3 := integral_mul_deriv_eq_deriv_mul_of_integrable hBd' hφ.hasDerivAt
    (integrable_mul_of_compact hB1.continuous hφ.continuous_deriv hφ1s)
    (integrable_mul_of_compact hB2 hφ.contDiff.continuous hφs)
    (integrable_mul_of_compact hB1.continuous hφ.contDiff.continuous hφs)
  have iA : Integrable fun y => A y * deriv φ y :=
    integrable_mul_of_compact hAc hφ.continuous_deriv hφ1s
  have iB : Integrable fun y => Bf y / 2 * deriv (deriv φ) y :=
    integrable_mul_of_compact (hBc.div_const 2) hφ.continuous_deriv2 hφ2s
  have iA' : Integrable fun y => φ y * -deriv A y := by
    have := integrable_mul_of_compact hA1.neg hφ.contDiff.continuous hφs
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]; ring
  have iB' : Integrable fun y => φ y * (1 / 2 * deriv (deriv Bf) y) := by
    have := integrable_mul_of_compact (continuous_const (y := (1 / 2 : ℝ)) |>.mul hB2) hφ.contDiff.continuous hφs
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]; ring
  rw [integral_add iA iB]
  simp_rw [mul_add]
  rw [integral_add iA' iB']
  have e1 : ∫ y, A y * deriv φ y = ∫ y, φ y * -deriv A y := by
    rw [I1, ← integral_neg]; congr 1; funext y; ring
  have e2 : ∫ y, Bf y / 2 * deriv (deriv φ) y = ∫ y, φ y * (1 / 2 * deriv (deriv Bf) y) := by
    have h1 : ∫ y, Bf y / 2 * deriv (deriv φ) y = (1 / 2) * ∫ y, Bf y * deriv (deriv φ) y := by
      rw [← integral_const_mul]; congr 1; funext y; ring
    have h2 : ∫ y, φ y * (1 / 2 * deriv (deriv Bf) y) =
        (1 / 2) * ∫ y, deriv (deriv Bf) y * φ y := by
      rw [← integral_const_mul]; congr 1; funext y; ring
    rw [h1, h2, I2, I3]
    ring
  rw [e1, e2]

/-- **Integration by parts**: `∫ L φ(·, t) p(t, ·) = ∫ φ · itoFPRHS a b p t` for `φ ∈ C²_c`,
when `y ↦ a(y, t) p(t, y)` is `C¹` and `y ↦ b(y, t)² p(t, y)` is `C²`. -/
theorem integral_itoGen_mul_density (hφ : IsC2c φ) {a b p : ℝ → ℝ → ℝ} {t : ℝ}
    (hA : ContDiff ℝ 1 fun z => a z t * p t z) (hB : ContDiff ℝ 2 fun z => b z t ^ 2 * p t z) :
    ∫ y, itoGen a b φ t y * p t y = ∫ y, φ y * itoFPRHS a b p t y := by
  have h := integral_ibp_generator hφ hA hB
  have e : (fun y => itoGen a b φ t y * p t y) = fun y =>
      (a y t * p t y) * deriv φ y + (b y t ^ 2 * p t y) / 2 * deriv (deriv φ) y := by
    funext y; simp only [itoGen]; ring
  rw [e]; exact h

end IBP

/-- **Differentiation under the integral**: `d/dt ∫ φ p(t, ·) = ∫ φ ∂ₜp(t, ·)` for `φ`
continuous with compact support, when `∂ₜp` exists and is jointly continuous on
`(t₁, t₂) × ℝ` and each `p(s, ·)` is continuous. -/
theorem hasDerivAt_integral_mul_density {p pt : ℝ → ℝ → ℝ} {t₁ t₂ t : ℝ} (ht : t ∈ Ioo t₁ t₂)
    {φ : ℝ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hpc : ∀ s ∈ Ioo t₁ t₂, Continuous (p s))
    (hpt : ∀ s ∈ Ioo t₁ t₂, ∀ y, HasDerivAt (fun s => p s y) (pt s y) s)
    (hptc : ContinuousOn (Function.uncurry pt) (Ioo t₁ t₂ ×ˢ univ)) :
    HasDerivAt (fun s => ∫ y, φ y * p s y) (∫ y, φ y * pt t y) t := by
  obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, Icc (t - δ) (t + δ) ⊆ Ioo t₁ t₂ := by
    have hpos : 0 < min (t - t₁) (t₂ - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
    refine ⟨min (t - t₁) (t₂ - t) / 2, half_pos hpos, ?_⟩
    intro s hs
    have h1 := min_le_left (t - t₁) (t₂ - t)
    have h2 := min_le_right (t - t₁) (t₂ - t)
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set K := tsupport φ
  have hK : IsCompact K := hφs.isCompact
  obtain ⟨Cp, hCp⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hptc.mono (prod_mono hδs (subset_univ _)))
  obtain ⟨Cφ, hCφ⟩ := hφc.bounded_above_of_compact_support hφs
  have hptt : ∀ s ∈ Ioo t₁ t₂, Continuous (pt s) := fun s hs =>
    hptc.comp_continuous (continuous_const.prodMk continuous_id) fun y => ⟨hs, trivial⟩
  set bound : ℝ → ℝ := K.indicator fun _ => Cφ * Cp
  have hnhds : Ioo (t - δ) (t + δ) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hsub : Ioo (t - δ) (t + δ) ⊆ Ioo t₁ t₂ := Ioo_subset_Icc_self.trans hδs
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound)
    (F' := fun s y => φ y * pt s y) hnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hnhds] with s hs
    exact (hφc.mul (hpc s (hsub hs))).aestronglyMeasurable
  · exact (hφc.mul (hpc t ht)).integrable_of_hasCompactSupport hφs.mul_right
  · exact (hφc.mul (hptt t ht)).aestronglyMeasurable
  · refine Eventually.of_forall fun y s hs => ?_
    by_cases hy : y ∈ K
    · have h1 := hCp (s, y) ⟨Ioo_subset_Icc_self hs, hy⟩
      have h2 := hCφ y
      simp only [Function.uncurry_apply_pair] at h1
      simp only [bound, indicator_of_mem hy, norm_mul]
      exact mul_le_mul h2 h1 (norm_nonneg _) ((norm_nonneg _).trans h2)
    · simp only [bound, indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, zero_mul,
        norm_zero, le_refl]
  · exact (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const hK.measure_lt_top.ne)
  · exact Eventually.of_forall fun y s hs => (hpt s (hsub hs) y).const_mul (φ y)

/-- **Gardiner (4.3.19) ⇒ (4.3.20)**: if `d/dt ∫ φ p(t, ·) = ∫ L φ(·, t) p(t, ·)` at time `t` for
every `φ ∈ C²_c`, and `p` has the stated regularity, then
`∂ₜp(t, y) = -∂_y[a p] + ½ ∂²_y[b² p]` for every `y`. -/
theorem strongFP_of_weakFP {a b p pt : ℝ → ℝ → ℝ} {t₁ t₂ t : ℝ} (ht : t ∈ Ioo t₁ t₂)
    (hpc : ∀ s ∈ Ioo t₁ t₂, Continuous (p s))
    (hpt : ∀ s ∈ Ioo t₁ t₂, ∀ y, HasDerivAt (fun s => p s y) (pt s y) s)
    (hptc : ContinuousOn (Function.uncurry pt) (Ioo t₁ t₂ ×ˢ univ))
    (hA : ContDiff ℝ 1 fun z => a z t * p t z) (hB : ContDiff ℝ 2 fun z => b z t ^ 2 * p t z)
    (hweak : ∀ φ, IsC2c φ →
      HasDerivAt (fun s => ∫ y, φ y * p s y) (∫ y, itoGen a b φ t y * p t y) t)
    (y : ℝ) : pt t y = itoFPRHS a b p t y := by
  have hptt : Continuous (pt t) :=
    hptc.comp_continuous (continuous_const.prodMk continuous_id) fun y => ⟨ht, trivial⟩
  have hRc : Continuous (itoFPRHS a b p t) :=
    (hA.continuous_deriv le_rfl).neg.add
      (continuous_const.mul (continuous_deriv2_of_contDiff hB))
  set g : ℝ → ℝ := fun y => pt t y - itoFPRHS a b p t y with hg
  have hgc : Continuous g := hptt.sub hRc
  have hzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y, ψ y • g y = 0 := by
    intro ψ hψ hψs
    have hψ2 : IsC2c ψ := ⟨hψ.of_le (WithTop.coe_le_coe.mpr le_top), hψs⟩
    have h1 := hasDerivAt_integral_mul_density ht hψ2.contDiff.continuous hψs hpc hpt hptc
    have h2 := (hweak ψ hψ2).unique h1
    rw [integral_itoGen_mul_density hψ2 hA hB] at h2
    have i1 : Integrable fun y => ψ y * pt t y :=
      (hψ2.contDiff.continuous.mul hptt).integrable_of_hasCompactSupport hψs.mul_right
    have i2 : Integrable fun y => ψ y * itoFPRHS a b p t y :=
      (hψ2.contDiff.continuous.mul hRc).integrable_of_hasCompactSupport hψs.mul_right
    simp only [hg, smul_eq_mul, mul_sub]
    rw [integral_sub i1 i2, h2, sub_self]
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hgc.locallyIntegrable hzero
  have : g = 0 := (Continuous.ae_eq_iff_eq volume hgc continuous_const).mp hae
  have := congrFun this y
  simp only [hg, Pi.zero_apply] at this
  linarith

namespace IsSDESol

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **The Fokker–Planck equation (4.3.20) for solutions of Lipschitz SDEs**: if on `(0, T)` the
law of the solution has a density `p(s, ·)` (`μ_s = p(s, y) dy`) with the regularity listed in
the hypotheses, then `∂ₜp = -∂_y[a p] + ½ ∂²_y[b² p]` on `(0, T) × ℝ`. -/
theorem strongFP {a b : ℝ → ℝ → ℝ} {T K B : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ}
    (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hc : SDECoeffs a b 0 T K)
    (ha : Continuous (Function.uncurry a)) (hb : Continuous (Function.uncurry b))
    (hB : ∀ y t, |b y t| ≤ B) {p pt : ℝ → ℝ → ℝ}
    (hp0 : ∀ s ∈ Ioo (0 : ℝ) T, ∀ y, 0 ≤ p s y)
    (hlaw : ∀ s ∈ Ioo (0 : ℝ) T,
      lawAt P x s = volume.withDensity fun y => ENNReal.ofReal (p s y))
    (hpc : ∀ s ∈ Ioo (0 : ℝ) T, Continuous (p s))
    (hpt : ∀ s ∈ Ioo (0 : ℝ) T, ∀ y, HasDerivAt (fun s => p s y) (pt s y) s)
    (hptc : ContinuousOn (Function.uncurry pt) (Ioo 0 T ×ˢ univ))
    (hA : ∀ s ∈ Ioo (0 : ℝ) T, ContDiff ℝ 1 fun z => a z s * p s z)
    (hBp : ∀ s ∈ Ioo (0 : ℝ) T, ContDiff ℝ 2 fun z => b z s ^ 2 * p s z)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (y : ℝ) : pt t y = itoFPRHS a b p t y := by
  have hdens : ∀ s ∈ Ioo (0 : ℝ) T, ∀ g : ℝ → ℝ,
      ∫ z, g z ∂(lawAt P x s) = ∫ z, g z * p s z := by
    intro s hs g
    rw [hlaw s hs, integral_withDensity_eq_integral_toReal_smul
      (f := fun y => ENNReal.ofReal (p s y)) (hpc s hs).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1; funext z
    rw [ENNReal.toReal_ofReal (hp0 s hs z), smul_eq_mul, mul_comm]
  refine strongFP_of_weakFP ht hpc hpt hptc (hA t ht) (hBp t ht) (fun φ hφ => ?_) y
  have h := weakFP_hasDerivAt hW hx hc ha hb hB hφ ht
  rw [hdens t ht] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact (hdens s hs φ).symm

end IsSDESol

end Gardiner.Ito.Generator
