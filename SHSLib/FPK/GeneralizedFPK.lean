/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The generalized Fokker–Planck–Kolmogorov equation (Section 4 of Bect, 2010)

Formalization of Section 4 of

  J. Bect, "A unifying formulation of the Fokker–Planck–Kolmogorov equation
  for general stochastic hybrid systems", Nonlinear Analysis: Hybrid Systems 4 (2010).

Taking expectations in the generalized Itô formula (3) gives the *generalized Dynkin
formula* (12), which — once a mean jump intensity `r` exists — reads

  `(μ_t − μ_0) φ = ∫₀ᵗ μ_s(Lφ) ds + ∫₀ᵗ r_s(K − I)φ ds`   (13)

for compactly supported `φ ∈ C²(E)`; here `μ_t` is the law of the hybrid state,
`L` the differential generator (4) of the diffusion part and `K` the reset kernel.
Differentiating (13) yields the *generalized FPK equation*

  `μ'_t = L*μ_t + r_t(K − I)`.   (14)

## Formalization choices

* Test functions are an abstract index type `T`; a datum `ev : T → E → ℝ` gives the
  function `φ` itself and `gen : T → E → ℝ` gives `Lφ`.  Compactly supported `C²`
  functions are bounded and measurable, which is exactly what is assumed of `ev`.
* Radon measures are represented by `GSHS.SignedFin`, a difference of two finite
  positive measures, and are paired with test functions.  (The paper works with
  locally finite signed measures and relatively compact sets; here everything is
  globally finite, which is the situation of interest since `μ_t` is a probability
  measure and `r_t` is bounded.)

## Main results

* `GSHS.FPKData.theorem8_ab_imp_c` — Theorem 8, direction (a)+(b) ⇒ (c): if a
  right-continuous mean jump intensity exists and `t ↦ μ_t` is differentiable, then
  `L*μ_t` is (represented by) a finite signed measure and Eq. (14) holds.
* `GSHS.FPKData.theorem8_ac_imp_b` — Theorem 8, direction (a)+(c) ⇒ (b): Eq. (40),
  `t ↦ μ_t` is differentiable with derivative `μ'_t = L*μ_t + r_t(K − I)`.
* `GSHS.nonneg_of_monotone_integral` — the positivity step of the direction
  (b)+(c) ⇒ (a) (Appendix B): since `t ↦ R^G(Γ × (0;t])` is increasing and equals
  `∫₀ᵗ (L*μ_s)(Γ) ds` with a right-continuous integrand, `(L*μ_t)(Γ) ≥ 0`, so that
  `r_t^G = (L*μ_t)(G ∩ ·)` is a *positive* measure: a mean jump intensity for the
  forced jumps.
-/
import SHSLib.FPK.MeanJumpIntensity

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

/-! ## Finite signed measures as differences of finite measures -/

/-- A finite signed measure on `E`, presented as a difference `ν⁺ − ν⁻` of two finite
positive measures.  This is the formalization's stand-in for the signed Radon measures
of the paper. -/
structure SignedFin (E : Type*) [MeasurableSpace E] where
  /-- Positive part. -/
  pos : Measure E
  /-- Negative part. -/
  neg : Measure E
  /-- The positive part is finite. -/
  pos_isFiniteMeasure : IsFiniteMeasure pos
  /-- The negative part is finite. -/
  neg_isFiniteMeasure : IsFiniteMeasure neg

namespace SignedFin

attribute [instance] SignedFin.pos_isFiniteMeasure SignedFin.neg_isFiniteMeasure

variable {E : Type*} [MeasurableSpace E]

/-- Pairing of a finite signed measure with a function: `ν φ = ∫ φ dν⁺ − ∫ φ dν⁻`. -/
def pair (ν : SignedFin E) (f : E → ℝ) : ℝ := ∫ x, f x ∂ν.pos - ∫ x, f x ∂ν.neg

/-- The set function `Γ ↦ ν(Γ)` associated with a finite signed measure. -/
def setFun (ν : SignedFin E) (Γ : Set E) : ℝ := (ν.pos Γ).toReal - (ν.neg Γ).toReal

end SignedFin

/-- A bounded measurable function is integrable with respect to any finite measure. -/
theorem integrable_of_bounded {E : Type*} [MeasurableSpace E] {f : E → ℝ}
    (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) (m : Measure E) [IsFiniteMeasure m] :
    Integrable f m := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  refine (hasFiniteIntegral_const C).mono ?_
  filter_upwards with x using by
    simpa [Real.norm_eq_abs] using (hb x).trans (le_abs_self C)

/-! ## Fundamental theorem of calculus, right-hand version (Lemma 22) -/

/-- **Lemma 22** (Bect, 2010), in the abstract form used in Appendix B: if `g` is
locally integrable and right-continuous at `t`, then `u ↦ ∫₀ᵘ g` has right-derivative
`g t` at `t`. -/
theorem hasDerivWithinAt_intervalIntegral {g : ℝ → ℝ} (hmeas : Measurable g)
    (hint : ∀ u : ℝ, IntervalIntegrable g volume 0 u) {t : ℝ}
    (hrc : ContinuousWithinAt g (Ici t) t) :
    HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, g s) (g t) (Ici t) t :=
  intervalIntegral.integral_hasDerivWithinAt_right (hint t)
    ⟨univ, univ_mem, hmeas.aestronglyMeasurable.restrict⟩ (hrc.mono Ioi_subset_Ici_self)

/-- The positivity step in the proof of Theorem 8, direction (b)+(c) ⇒ (a)
(Appendix B, after Eq. (43)): if `t ↦ ∫₀ᵗ g` is nondecreasing and `g` is
right-continuous at `t ≥ 0`, then `g t ≥ 0`. -/
theorem nonneg_of_monotone_integral {g : ℝ → ℝ} (hmeas : Measurable g)
    (hint : ∀ u : ℝ, IntervalIntegrable g volume 0 u)
    {F : ℝ → ℝ} (hF : ∀ u : ℝ, 0 ≤ u → F u = ∫ s in (0 : ℝ)..u, g s)
    (hmono : ∀ u v : ℝ, 0 ≤ u → u ≤ v → F u ≤ F v)
    {t : ℝ} (ht : 0 ≤ t) (hrc : ContinuousWithinAt g (Ici t) t) :
    0 ≤ g t := by
  have hderiv : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, g s) (g t) (Ici t) t :=
    hasDerivWithinAt_intervalIntegral hmeas hint hrc
  have hslope : Tendsto (slope (fun u => ∫ s in (0 : ℝ)..u, g s) t) (𝓝[Ici t \ {t}] t)
      (𝓝 (g t)) := (hasDerivWithinAt_iff_tendsto_slope).1 hderiv
  have hset : Ici t \ {t} = Ioi t := by
    ext x
    simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h
      exact ⟨h.le, ne_of_gt h⟩
  rw [hset] at hslope
  refine ge_of_tendsto hslope ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxt : t < x := hx
  have h1 : F t ≤ F x := hmono t x ht hxt.le
  rw [hF t ht, hF x (le_trans ht hxt.le)] at h1
  rw [slope_def_field, div_nonneg_iff]
  left
  exact ⟨by linarith, by linarith⟩

/-! ## The weak formulation of the generalized FPK equation -/

variable {E : Type*} [MeasurableSpace E] {T : Type*}

/-- The data entering the weak formulation of the generalized FPK equation of
Section 4: the laws `μ_t` of the hybrid state, a mean jump intensity `r`, the reset
kernel `K`, and a family of test functions `φ` (indexed by `T`) together with the
values `Lφ` of the differential generator (4). -/
structure FPKData (E : Type*) [MeasurableSpace E] (T : Type*) where
  /-- The test function `φ` associated with an index. -/
  ev : T → E → ℝ
  /-- The value `Lφ` of the differential generator (4) on the test function. -/
  gen : T → E → ℝ
  /-- The law `μ_t` of the hybrid state at time `t`. -/
  law : ℝ → Measure E
  /-- The mean jump intensity `r_t` (Definition 6). -/
  r : ℝ → Measure E
  /-- The reset kernel `K` of Section 2.3. -/
  K : Kernel E E
  /-- `K` is a Markov kernel. -/
  markov : IsMarkovKernel K
  /-- Test functions are measurable. -/
  ev_measurable : ∀ φ, Measurable (ev φ)
  /-- Test functions are bounded (they are compactly supported and continuous). -/
  ev_bound : T → ℝ
  /-- The bound on test functions. -/
  ev_le : ∀ φ x, |ev φ x| ≤ ev_bound φ
  /-- Each `μ_t` is a probability measure. -/
  law_isProbabilityMeasure : ∀ t, IsProbabilityMeasure (law t)
  /-- Each `r_t` is a bounded measure. -/
  r_isFiniteMeasure : ∀ t, IsFiniteMeasure (r t)

namespace FPKData

attribute [instance] FPKData.markov FPKData.law_isProbabilityMeasure FPKData.r_isFiniteMeasure

variable (D : FPKData E T)

/-- `μ_t φ`, the expectation of the test function under the law of the state. -/
def lawPair (t : ℝ) (φ : T) : ℝ := ∫ x, D.ev φ x ∂(D.law t)

/-- `μ_t (Lφ)`, the pairing appearing in the first term of Eq. (13). -/
def genPair (t : ℝ) (φ : T) : ℝ := ∫ x, D.gen φ x ∂(D.law t)

/-- `r_t (K − I) φ`, the jump term of Eq. (13). -/
def jumpPair (t : ℝ) (φ : T) : ℝ :=
  ∫ x, ((∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x) ∂(D.r t)

/-- **Eq. (13)**: the generalized Dynkin formula, in the presence of a mean jump
intensity. -/
def WeakDynkin : Prop :=
  ∀ (φ : T) (t : ℝ), 0 ≤ t →
    D.lawPair t φ - D.lawPair 0 φ
      = (∫ s in (0 : ℝ)..t, D.genPair s φ) + ∫ s in (0 : ℝ)..t, D.jumpPair s φ

/-- The finite signed measure `ν − (r_t K − r_t)`; applied to `ν = μ'_t` this is the
candidate for `L*μ_t` in Eq. (14). -/
def subJump (ν : SignedFin E) (t : ℝ) : SignedFin E where
  pos := ν.pos + D.r t
  neg := ν.neg + (D.K ∘ₘ D.r t)
  pos_isFiniteMeasure := by infer_instance
  neg_isFiniteMeasure := by infer_instance

/-- The finite signed measure `ν + (r_t K − r_t)`; applied to `ν = L*μ_t` this is the
candidate for `μ'_t` in Eq. (14). -/
def addJump (ν : SignedFin E) (t : ℝ) : SignedFin E where
  pos := ν.pos + (D.K ∘ₘ D.r t)
  neg := ν.neg + D.r t
  pos_isFiniteMeasure := by infer_instance
  neg_isFiniteMeasure := by infer_instance

/-- Integral of a test function against the source measure `r_t K`. -/
theorem integral_comp_eq (t : ℝ) (φ : T) :
    ∫ y, D.ev φ y ∂(D.K ∘ₘ D.r t) = ∫ x, (∫ y, D.ev φ y ∂(D.K x)) ∂(D.r t) := by
  have h1 : Integrable (D.ev φ) (D.K ∘ₘ D.r t) :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  rw [Measure.comp_eq_comp_const_apply] at *
  rw [Kernel.integral_comp h1]
  simp

theorem integrable_evalKernel (t : ℝ) (φ : T) :
    Integrable (fun x => ∫ y, D.ev φ y ∂(D.K x)) (D.r t) := by
  have h1 : Integrable (D.ev φ) (D.K ∘ₘ D.r t) :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  rw [Measure.comp_eq_comp_const_apply] at h1
  simpa using h1.integral_comp

theorem subJump_pair (ν : SignedFin E) (t : ℝ) (φ : T) :
    (D.subJump ν t).pair (D.ev φ) = ν.pair (D.ev φ) - D.jumpPair t φ := by
  have hev : Integrable (D.ev φ) (D.r t) :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  have hK : Integrable (D.ev φ) (D.K ∘ₘ D.r t) :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  have hpos : Integrable (D.ev φ) ν.pos :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  have hneg : Integrable (D.ev φ) ν.neg :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  simp only [SignedFin.pair, subJump, jumpPair]
  rw [integral_add_measure hpos hev, integral_add_measure hneg hK,
    integral_sub (D.integrable_evalKernel t φ) hev, D.integral_comp_eq t φ]
  ring

theorem addJump_pair (ν : SignedFin E) (t : ℝ) (φ : T) :
    (D.addJump ν t).pair (D.ev φ) = ν.pair (D.ev φ) + D.jumpPair t φ := by
  have hev : Integrable (D.ev φ) (D.r t) :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  have hK : Integrable (D.ev φ) (D.K ∘ₘ D.r t) :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  have hpos : Integrable (D.ev φ) ν.pos :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  have hneg : Integrable (D.ev φ) ν.neg :=
    integrable_of_bounded (D.ev_measurable φ) (D.ev_le φ) _
  simp only [SignedFin.pair, addJump, jumpPair]
  rw [integral_add_measure hpos hK, integral_add_measure hneg hev,
    integral_sub (D.integrable_evalKernel t φ) hev, D.integral_comp_eq t φ]
  ring

/-- **Definition 7** (Bect, 2010), in the weak/tested form used here: `t ↦ μ_t` solves
the generalized FPK equation with derivative `t ↦ μ'_t` when `t ↦ μ_t φ` is
right-differentiable with derivative `μ'_t φ`, and Eq. (14) holds when tested against
every test function. -/
structure IsWeakFPKSolution (μ' : ℝ → SignedFin E) : Prop where
  /-- Definition 7(b): differentiability of the law. -/
  hasDeriv : ∀ (φ : T) (t : ℝ), 0 ≤ t →
    HasDerivWithinAt (fun s => D.lawPair s φ) ((μ' t).pair (D.ev φ)) (Ici t) t
  /-- Definition 7(d): Eq. (14), `μ'_t = L*μ_t + r_t(K − I)`. -/
  fpk : ∀ (φ : T) (t : ℝ), 0 ≤ t →
    (μ' t).pair (D.ev φ) = D.genPair t φ + D.jumpPair t φ

/-! ### Theorem 8 -/

/-- **Theorem 8, direction (a)+(b) ⇒ (c)** (Bect, 2010).

Assume the generalized Dynkin formula (13) (which presupposes 8(a), the existence of a
mean jump intensity), the right-continuity and local integrability of the two terms of
its right-hand side, and 8(b), the right-differentiability of `t ↦ μ_t φ` with
derivative `μ'_t φ`.  Then the generalized FPK equation (14) holds:

  `μ'_t φ = μ_t(Lφ) + r_t(K − I)φ`. -/
theorem theorem8_ab_imp_c (μ' : ℝ → SignedFin E) (hdynkin : D.WeakDynkin)
    (hgen_meas : ∀ φ : T, Measurable fun s => D.genPair s φ)
    (hgen_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.genPair s φ) volume 0 u)
    (hgen_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => D.genPair s φ) (Ici t) t)
    (hjump_meas : ∀ φ : T, Measurable fun s => D.jumpPair s φ)
    (hjump_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.jumpPair s φ) volume 0 u)
    (hjump_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => D.jumpPair s φ) (Ici t) t)
    (hderiv : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun s => D.lawPair s φ) ((μ' t).pair (D.ev φ)) (Ici t) t)
    (φ : T) (t : ℝ) (ht : 0 ≤ t) :
    (μ' t).pair (D.ev φ) = D.genPair t φ + D.jumpPair t φ := by
  have hI : HasDerivWithinAt
      (fun u => (∫ s in (0 : ℝ)..u, D.genPair s φ) + ∫ s in (0 : ℝ)..u, D.jumpPair s φ)
      (D.genPair t φ + D.jumpPair t φ) (Ici t) t :=
    (hasDerivWithinAt_intervalIntegral (hgen_meas φ) (hgen_int φ) (hgen_rc φ t ht)).add
      (hasDerivWithinAt_intervalIntegral (hjump_meas φ) (hjump_int φ) (hjump_rc φ t ht))
  have hcongr : HasDerivWithinAt (fun u => D.lawPair u φ - D.lawPair 0 φ)
      (D.genPair t φ + D.jumpPair t φ) (Ici t) t := by
    refine hI.congr (fun y hy => ?_) ?_
    · exact hdynkin φ y (le_trans ht hy)
    · exact hdynkin φ t ht
  have hother : HasDerivWithinAt (fun u => D.lawPair u φ - D.lawPair 0 φ)
      ((μ' t).pair (D.ev φ)) (Ici t) t := (hderiv φ t ht).sub_const _
  exact UniqueDiffWithinAt.eq_deriv (Ici t) (uniqueDiffOn_Ici t t self_mem_Ici) hother hcongr

/-- **Theorem 8, direction (a)+(b) ⇒ (c)**, statement 8(c) proper: under the
assumptions above, `L*μ_t` is (represented by) the finite signed measure
`μ'_t − (r_t K − r_t)`, i.e. `L*μ_t` is a Radon measure. -/
theorem theorem8_ab_imp_c_signedMeasure (μ' : ℝ → SignedFin E) (hdynkin : D.WeakDynkin)
    (hgen_meas : ∀ φ : T, Measurable fun s => D.genPair s φ)
    (hgen_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.genPair s φ) volume 0 u)
    (hgen_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => D.genPair s φ) (Ici t) t)
    (hjump_meas : ∀ φ : T, Measurable fun s => D.jumpPair s φ)
    (hjump_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.jumpPair s φ) volume 0 u)
    (hjump_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => D.jumpPair s φ) (Ici t) t)
    (hderiv : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun s => D.lawPair s φ) ((μ' t).pair (D.ev φ)) (Ici t) t)
    (φ : T) (t : ℝ) (ht : 0 ≤ t) :
    D.genPair t φ = (D.subJump (μ' t) t).pair (D.ev φ) := by
  rw [D.subJump_pair (μ' t) t φ,
    D.theorem8_ab_imp_c μ' hdynkin hgen_meas hgen_int hgen_rc hjump_meas hjump_int hjump_rc
      hderiv φ t ht]
  ring

/-- **Theorem 8, direction (a)+(c) ⇒ (b)** (Bect, 2010), Eq. (40).

Assume the generalized Dynkin formula (13) and 8(c): `L*μ_t` is the finite signed
measure `lstar t`.  Setting `μ'_t = L*μ_t + r_t(K − I)`, the law satisfies

  `(μ_t − μ_0) φ = ∫₀ᵗ μ'_s φ ds`,

which is Eq. (40), and `t ↦ μ_t φ` is right-differentiable with derivative `μ'_t φ`
whenever the integrand is right-continuous at `t`. -/
theorem theorem8_ac_imp_b_integral (lstar : ℝ → SignedFin E) (hdynkin : D.WeakDynkin)
    (hlstar : ∀ (φ : T) (s : ℝ), 0 ≤ s → D.genPair s φ = (lstar s).pair (D.ev φ))
    (hgen_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.genPair s φ) volume 0 u)
    (hjump_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.jumpPair s φ) volume 0 u)
    (φ : T) (t : ℝ) (ht : 0 ≤ t) :
    D.lawPair t φ - D.lawPair 0 φ
      = ∫ s in (0 : ℝ)..t, (D.addJump (lstar s) s).pair (D.ev φ) := by
  have hsum : ∀ s : ℝ, 0 ≤ s →
      (D.addJump (lstar s) s).pair (D.ev φ) = D.genPair s φ + D.jumpPair s φ := by
    intro s hs
    rw [D.addJump_pair (lstar s) s φ, ← hlstar φ s hs]
  rw [hdynkin φ t ht, ← intervalIntegral.integral_add (hgen_int φ t) (hjump_int φ t)]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
  have hs0 : 0 ≤ s := by
    rw [uIoc_of_le ht] at hs
    exact le_of_lt hs.1
  exact (hsum s hs0).symm

/-- **Theorem 8, direction (a)+(c) ⇒ (b)**: right-differentiability of the law
(Definition 7(b)), with derivative `μ'_t = L*μ_t + r_t(K − I)`. -/
theorem theorem8_ac_imp_b_hasDeriv (lstar : ℝ → SignedFin E) (hdynkin : D.WeakDynkin)
    (hlstar : ∀ (φ : T) (s : ℝ), 0 ≤ s → D.genPair s φ = (lstar s).pair (D.ev φ))
    (hgen_meas : ∀ φ : T, Measurable fun s => D.genPair s φ)
    (hgen_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.genPair s φ) volume 0 u)
    (hgen_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => D.genPair s φ) (Ici t) t)
    (hjump_meas : ∀ φ : T, Measurable fun s => D.jumpPair s φ)
    (hjump_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.jumpPair s φ) volume 0 u)
    (hjump_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => D.jumpPair s φ) (Ici t) t)
    (φ : T) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => D.lawPair s φ)
      ((D.addJump (lstar t) t).pair (D.ev φ)) (Ici t) t := by
  have hI : HasDerivWithinAt
      (fun u => (∫ s in (0 : ℝ)..u, D.genPair s φ) + ∫ s in (0 : ℝ)..u, D.jumpPair s φ)
      (D.genPair t φ + D.jumpPair t φ) (Ici t) t :=
    (hasDerivWithinAt_intervalIntegral (hgen_meas φ) (hgen_int φ) (hgen_rc φ t ht)).add
      (hasDerivWithinAt_intervalIntegral (hjump_meas φ) (hjump_int φ) (hjump_rc φ t ht))
  have hval : (D.addJump (lstar t) t).pair (D.ev φ) = D.genPair t φ + D.jumpPair t φ := by
    rw [D.addJump_pair (lstar t) t φ, ← hlstar φ t ht]
  rw [hval]
  have hshift : HasDerivWithinAt (fun u => D.lawPair u φ - D.lawPair 0 φ)
      (D.genPair t φ + D.jumpPair t φ) (Ici t) t := by
    refine hI.congr (fun y hy => ?_) ?_
    · exact hdynkin φ y (le_trans ht hy)
    · exact hdynkin φ t ht
  simpa using hshift.add_const (D.lawPair 0 φ)

/-- **Theorem 8, direction (b)+(c) ⇒ (a)** (Bect, 2010, Appendix B, Eqs. (43)).

When 8(b) and 8(c) hold, the approximation argument of Appendix B turns the tested
identity (42) into `R^G(Γ × (0;t]) = ∫₀ᵗ (L*μ_s)(Γ) ds` for compact `Γ ⊆ G`
(hypothesis `hR` below).  Since `t ↦ R^G(Γ × (0;t])` counts jumps, it is nondecreasing,
and right-continuity of `t ↦ (L*μ_t)(Γ)` then forces `(L*μ_t)(Γ) ≥ 0`: the set function
`r_t^G = (L*μ_t)(G ∩ ·)` is a *positive* measure, i.e. a mean jump intensity for the
forced jumps. -/
theorem theorem8_bc_imp_a {Rg : ℝ → ℝ} {lstarSet : ℝ → ℝ}
    (hmeas : Measurable lstarSet)
    (hint : ∀ u : ℝ, IntervalIntegrable lstarSet volume 0 u)
    (hR : ∀ u : ℝ, 0 ≤ u → Rg u = ∫ s in (0 : ℝ)..u, lstarSet s)
    (hmono : ∀ u v : ℝ, 0 ≤ u → u ≤ v → Rg u ≤ Rg v)
    (hrc : ∀ u : ℝ, 0 ≤ u → ContinuousWithinAt lstarSet (Ici u) u) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ lstarSet u) ∧
      ∀ t : ℝ, 0 ≤ t →
        ENNReal.ofReal (Rg t) = ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (lstarSet s) := by
  have hnonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ lstarSet u := fun u hu =>
    nonneg_of_monotone_integral hmeas hint hR hmono hu (hrc u hu)
  refine ⟨hnonneg, fun t ht => ?_⟩
  have hIoc : Rg t = ∫ s in Ioc (0 : ℝ) t, lstarSet s := by
    rw [hR t ht, intervalIntegral.integral_of_le ht]
  have hintOn : IntegrableOn lstarSet (Ioc (0 : ℝ) t) volume := by
    have := (hint t)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at this
  have hae : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) t)] lstarSet := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hnonneg s (le_of_lt hs.1)
  rw [hIoc, ofReal_integral_eq_lintegral_ofReal hintOn hae]

/-- **Theorem 8, direction (b)+(c) ⇒ (a)**, existence statement 8(a) proper.

Packaging the previous positivity result over all measurable sets: if Eq. (43),
`R^G(Γ × (0;t]) = ∫₀ᵗ (L*μ_s)(Γ) ds`, holds for every measurable `Γ`, with
`t ↦ (L*μ_t)(Γ)` right-continuous and locally integrable, then the family of measures
`r_t^G` with `r_t^G(Γ) = (L*μ_t)(Γ)` is a *mean jump intensity* for the forced jumps in
the sense of Definition 6. -/
theorem theorem8_bc_imp_a_meanJumpIntensity {RG : Measure (E × ℝ)} {rG : ℝ → Measure E}
    {Lstar : ℝ → Set E → ℝ}
    (hfin : ∀ t : ℝ, IsFiniteMeasure (rG t))
    (hval : ∀ (t : ℝ) (Γ : Set E), MeasurableSet Γ → rG t Γ = ENNReal.ofReal (Lstar t Γ))
    (hmeas : ∀ Γ : Set E, MeasurableSet Γ → Measurable fun s => Lstar s Γ)
    (hint : ∀ Γ : Set E, MeasurableSet Γ → ∀ u : ℝ,
      IntervalIntegrable (fun s => Lstar s Γ) volume 0 u)
    (hRfin : ∀ (Γ : Set E) (u : ℝ), RG (Γ ×ˢ Ioc (0 : ℝ) u) ≠ ⊤)
    (hR : ∀ Γ : Set E, MeasurableSet Γ → ∀ u : ℝ, 0 ≤ u →
      (RG (Γ ×ˢ Ioc (0 : ℝ) u)).toReal = ∫ s in (0 : ℝ)..u, Lstar s Γ)
    (hrc : ∀ Γ : Set E, MeasurableSet Γ → ∀ u : ℝ, 0 ≤ u →
      ContinuousWithinAt (fun s => Lstar s Γ) (Ici u) u) :
    MeanJumpIntensity RG rG where
  isFiniteMeasure := hfin
  measurable_apply := by
    intro Γ hΓ
    have hfun : (fun s : ℝ => rG s Γ) = fun s : ℝ => ENNReal.ofReal (Lstar s Γ) :=
      funext fun s => hval s Γ hΓ
    rw [hfun]
    exact ENNReal.measurable_ofReal.comp (hmeas Γ hΓ)
  lintegral_eq := by
    intro Γ hΓ t ht
    have hmono : ∀ u v : ℝ, 0 ≤ u → u ≤ v →
        (RG (Γ ×ˢ Ioc (0 : ℝ) u)).toReal ≤ (RG (Γ ×ˢ Ioc (0 : ℝ) v)).toReal := by
      intro u v _ huv
      refine ENNReal.toReal_mono (hRfin Γ v) (measure_mono ?_)
      exact Set.prod_mono le_rfl (Set.Ioc_subset_Ioc_right huv)
    obtain ⟨-, hkey⟩ :=
      theorem8_bc_imp_a (hmeas Γ hΓ) (hint Γ hΓ) (hR Γ hΓ) hmono (hrc Γ hΓ)
    have hval_t := hkey t ht
    rw [ENNReal.ofReal_toReal (hRfin Γ t)] at hval_t
    rw [hval_t]
    refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    rw [hval s Γ hΓ]

/-- Under the hypotheses of Theorem 8 (a)+(b), the pair `(μ_t, μ'_t)` is a solution in
the weak sense of the generalized FPK equation (Definition 7). -/
theorem isWeakFPKSolution_of_ab (μ' : ℝ → SignedFin E) (hdynkin : D.WeakDynkin)
    (hgen_meas : ∀ φ : T, Measurable fun s => D.genPair s φ)
    (hgen_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.genPair s φ) volume 0 u)
    (hgen_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => D.genPair s φ) (Ici t) t)
    (hjump_meas : ∀ φ : T, Measurable fun s => D.jumpPair s φ)
    (hjump_int : ∀ (φ : T) (u : ℝ), IntervalIntegrable (fun s => D.jumpPair s φ) volume 0 u)
    (hjump_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t → ContinuousWithinAt (fun s => D.jumpPair s φ) (Ici t) t)
    (hderiv : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun s => D.lawPair s φ) ((μ' t).pair (D.ev φ)) (Ici t) t) :
    D.IsWeakFPKSolution μ' where
  hasDeriv := hderiv
  fpk := fun φ t ht =>
    D.theorem8_ab_imp_c μ' hdynkin hgen_meas hgen_int hgen_rc hjump_meas hjump_int hjump_rc
      hderiv φ t ht

end FPKData

end GSHS
