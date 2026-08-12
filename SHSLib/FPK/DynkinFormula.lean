/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# From the generalized Itô formula to the generalized Dynkin formula (Section 4.1)

Formalization of the step "(3) ⟹ (12) ⟹ (13)" of

  J. Bect, "A unifying formulation of the Fokker–Planck–Kolmogorov equation
  for general stochastic hybrid systems", Nonlinear Analysis: Hybrid Systems 4 (2010).

Taking expectations in the generalized Itô formula (3) — equivalently, using that the
compensated process

  `M_t = φ(X_t) − φ(X_0) − ∫₀ᵗ (Aφ)(X_s) ds`

is a martingale, `A` being the extended generator of the GSHS — gives the *generalized
Dynkin formula* (12).  Writing `Aφ = Lφ + λ (K − I)φ` (the Lévy-system form (5)–(6) of
the generator) and integrating in space against the law `μ_s` of the state turns (12)
into Eq. (13),

  `(μ_t − μ_0) φ = ∫₀ᵗ μ_s(Lφ) ds + ∫₀ᵗ r_s(K − I)φ ds`,

with the mean jump intensity `r_s = λ μ_s` of Eq. (8).  This is exactly the predicate
`GSHS.FPKData.WeakDynkin` which is the standing hypothesis of Theorem 8; the results
below *derive* it from the martingale property, so that the hypotheses of Theorem 8 can
be discharged for a concrete process.

## Main results

* `GSHS.integral_eq_zero_of_martingale` — a martingale vanishing at the initial time has
  zero expectation at all later times.
* `GSHS.dynkin_of_martingale` — Eq. (12): the generalized Dynkin formula, obtained by
  taking expectations in the compensated martingale.
* `GSHS.integral_pathIntervalIntegral_swap` — the Fubini step converting the pathwise
  time integral into a time integral of the laws `μ_s`.
* `GSHS.FPKData.weakDynkin_of_martingale` — Eq. (13): the generalized Dynkin formula in
  the measure-valued form required by Definition 7 and Theorem 8.
* `GSHS.FPKData.isWeakFPKSolution_of_martingale` — combining with Theorem 8(a)+(b)⇒(c):
  the law of the process is a weak solution of the generalized FPK equation (14).
-/
import SHSLib.FPK.HespanhaBridge

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

/-! ## Taking expectations in the martingale -/

/-- A martingale which vanishes (almost surely) at the initial time has zero
expectation at every later time. -/
theorem integral_eq_zero_of_martingale {Omega ι : Type*} [Preorder ι]
    [mOmega : MeasurableSpace Omega] {P : Measure Omega} [IsFiniteMeasure P]
    {M : ι → Omega → ℝ} {F : Filtration ι mOmega} (hM : Martingale M F P)
    {i j : ι} (hij : i ≤ j) (h0 : M i =ᵐ[P] 0) :
    ∫ ω, M j ω ∂P = 0 := by
  have h := hM.setIntegral_eq hij MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [← h, integral_congr_ae h0]
  simp

/-- **Eq. (12)** (Bect, 2010), the *generalized Dynkin formula*: if the compensated
process `f t − f 0 − g t` is a martingale and `g 0 = 0`, then

  `E{f t} − E{f 0} = E{g t}`.

Applied to `f t ω = φ(X_t(ω))` and `g t ω = ∫₀ᵗ (Aφ)(X_s(ω)) ds` this is exactly the
expectation of the generalized Itô formula (3). -/
theorem dynkin_of_martingale {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {P : Measure Omega} [IsFiniteMeasure P] {f g : ℝ → Omega → ℝ} {F : Filtration ℝ mOmega}
    (hM : Martingale (fun t ω => f t ω - f 0 ω - g t ω) F P)
    (hg0 : g 0 =ᵐ[P] 0) {t : ℝ} (hft : Integrable (f t) P) (hf0 : Integrable (f 0) P)
    (hgt : Integrable (g t) P) (ht : 0 ≤ t) :
    ∫ ω, f t ω ∂P - ∫ ω, f 0 ω ∂P = ∫ ω, g t ω ∂P := by
  have h0 : (fun ω => f 0 ω - f 0 ω - g 0 ω) =ᵐ[P] 0 := by
    filter_upwards [hg0] with ω hω
    simp [hω]
  have hzero := integral_eq_zero_of_martingale hM ht h0
  have e1 : ∫ ω, (f t ω - f 0 ω - g t ω) ∂P
      = (∫ ω, (f t ω - f 0 ω) ∂P) - ∫ ω, g t ω ∂P :=
    integral_sub (hft.sub hf0) hgt
  have e2 : ∫ ω, (f t ω - f 0 ω) ∂P = (∫ ω, f t ω ∂P) - ∫ ω, f 0 ω ∂P :=
    integral_sub hft hf0
  simp only [e1, e2] at hzero
  linarith

/-! ## Fubini: from pathwise time integrals to time integrals of the laws -/

variable {Omega E : Type*} [mOmega : MeasurableSpace Omega] [MeasurableSpace E]

/-- The expectation of a bounded measurable function of the state is a measurable
function of time. -/
theorem stronglyMeasurable_pathIntegral {P : Measure Omega} [IsFiniteMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X)) {h : E → ℝ}
    (hh : Measurable h) : StronglyMeasurable fun s : ℝ => ∫ ω, h (X s ω) ∂P := by
  have hmeas : StronglyMeasurable fun p : ℝ × Omega => h (X p.1 p.2) :=
    (hh.comp hX).stronglyMeasurable
  exact hmeas.integral_prod_right'

/-- The expectation of a function of the state is an integral against the law. -/
theorem integral_law_eq {P : Measure Omega} {X : ℝ → Omega → E} (s : ℝ)
    (hXs : Measurable (X s)) {h : E → ℝ} (hh : Measurable h) :
    ∫ x, h x ∂(P.map (X s)) = ∫ ω, h (X s ω) ∂P :=
  integral_map hXs.aemeasurable hh.aestronglyMeasurable

/-- The pathwise time integral of a bounded measurable function of the state is
integrable. -/
theorem integrable_pathIntervalIntegral {P : Measure Omega} [IsFiniteMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X)) {h : E → ℝ}
    (hh : Measurable h) {C : ℝ} (hb : ∀ x, |h x| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..t, h (X s ω)) P := by
  have hprod : Integrable (fun p : Omega × ℝ => h (X p.2 p.1))
      (P.prod (volume.restrict (Ioc (0 : ℝ) t))) := by
    have hmeas : Measurable fun p : Omega × ℝ => h (X p.2 p.1) :=
      hh.comp (hX.comp (measurable_snd.prodMk measurable_fst))
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have : IsFiniteMeasure (P.prod (volume.restrict (Ioc (0 : ℝ) t))) := by
      constructor
      rw [Measure.prod_apply MeasurableSet.univ]
      simp only [Set.preimage_univ]
      have hfin : (volume.restrict (Ioc (0 : ℝ) t)) univ < ⊤ := by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp [Real.volume_Ioc]
      calc ∫⁻ _, (volume.restrict (Ioc (0 : ℝ) t)) univ ∂P
          = P univ * (volume.restrict (Ioc (0 : ℝ) t)) univ := by
            rw [lintegral_const]; ring
        _ < ⊤ := ENNReal.mul_lt_top (measure_lt_top P univ) hfin
    refine (hasFiniteIntegral_const C).mono ?_
    filter_upwards with p using by
      simpa [Real.norm_eq_abs] using (hb (X p.2 p.1)).trans (le_abs_self C)
  have := hprod.integral_prod_left
  refine this.congr ?_
  filter_upwards with ω
  simp only [intervalIntegral.integral_of_le ht]

/-- **Fubini step.** For a bounded measurable `h`, the expectation of the pathwise time
integral is the time integral of the expectations, i.e. of `μ_s h`. -/
theorem integral_pathIntervalIntegral_swap {P : Measure Omega} [IsFiniteMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X)) {h : E → ℝ}
    (hh : Measurable h) {C : ℝ} (hb : ∀ x, |h x| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (∫ s in (0 : ℝ)..t, h (X s ω)) ∂P
      = ∫ s in (0 : ℝ)..t, ∫ ω, h (X s ω) ∂P := by
  have hprod : Integrable (Function.uncurry fun (ω : Omega) (s : ℝ) => h (X s ω))
      (P.prod (volume.restrict (Ioc (0 : ℝ) t))) := by
    have hmeas : Measurable (Function.uncurry fun (ω : Omega) (s : ℝ) => h (X s ω)) :=
      hh.comp (hX.comp (measurable_snd.prodMk measurable_fst))
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have : IsFiniteMeasure (P.prod (volume.restrict (Ioc (0 : ℝ) t))) := by
      constructor
      rw [Measure.prod_apply MeasurableSet.univ]
      simp only [Set.preimage_univ]
      have hfin : (volume.restrict (Ioc (0 : ℝ) t)) univ < ⊤ := by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp [Real.volume_Ioc]
      calc ∫⁻ _, (volume.restrict (Ioc (0 : ℝ) t)) univ ∂P
          = P univ * (volume.restrict (Ioc (0 : ℝ) t)) univ := by
            rw [lintegral_const]; ring
        _ < ⊤ := ENNReal.mul_lt_top (measure_lt_top P univ) hfin
    refine (hasFiniteIntegral_const C).mono ?_
    filter_upwards with p using by
      simpa [Real.norm_eq_abs] using (hb (X p.2 p.1)).trans (le_abs_self C)
  have hswap := integral_integral_swap hprod
  rw [intervalIntegral.integral_of_le ht]
  rw [← hswap]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [intervalIntegral.integral_of_le ht]

/-- Time-integrability of `s ↦ μ_s h` on `[0;t]`, for a bounded measurable `h`. -/
theorem intervalIntegrable_law_integral {P : Measure Omega} [IsFiniteMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X)) {law : ℝ → Measure E}
    (hlaw : ∀ s : ℝ, 0 ≤ s → P.map (X s) = law s) {h : E → ℝ} (hh : Measurable h)
    {C : ℝ} (hb : ∀ x, |h x| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => ∫ x, h x ∂(law s)) volume 0 t := by
  have hXs : ∀ s : ℝ, Measurable (X s) := fun s =>
    hX.comp (measurable_const.prodMk measurable_id)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp [Real.volume_Ioc]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  have hbase : IntegrableOn (fun s : ℝ => ∫ ω, h (X s ω) ∂P) (Ioc 0 t) volume := by
    refine ⟨(stronglyMeasurable_pathIntegral hX hh).aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (C * (P univ).toReal)).mono ?_
    filter_upwards with s
    have h1 : ‖∫ ω, h (X s ω) ∂P‖ ≤ C * (P univ).toReal :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hb (X s ω))
    exact h1.trans (le_abs_self _)
  refine hbase.congr_fun (fun s hs => ?_) measurableSet_Ioc
  rw [← hlaw s (le_of_lt hs.1), integral_law_eq s (hXs s) hh]

/-- If the law of `X s` is `law s` at *every* time, then `s ↦ μ_s h` is measurable on the
whole line, for bounded measurable `h`. -/
theorem stronglyMeasurable_law_integral {P : Measure Omega} [IsFiniteMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X)) {law : ℝ → Measure E}
    (hlaw : ∀ s : ℝ, P.map (X s) = law s) {h : E → ℝ} (hh : Measurable h) :
    StronglyMeasurable fun s : ℝ => ∫ x, h x ∂(law s) := by
  have hXs : ∀ s : ℝ, Measurable (X s) := fun s =>
    hX.comp (measurable_const.prodMk measurable_id)
  have hfun : (fun s : ℝ => ∫ x, h x ∂(law s)) = fun s : ℝ => ∫ ω, h (X s ω) ∂P := by
    funext s
    rw [← hlaw s, integral_law_eq s (hXs s) hh]
  rw [hfun]
  exact stronglyMeasurable_pathIntegral hX hh

/-- Integrability of `s ↦ μ_s h` on any set of finite Lebesgue measure. -/
theorem integrableOn_law_integral {P : Measure Omega} [IsFiniteMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X)) {law : ℝ → Measure E}
    (hlaw : ∀ s : ℝ, P.map (X s) = law s) {h : E → ℝ} (hh : Measurable h)
    {C : ℝ} (hb : ∀ x, |h x| ≤ C) {S : Set ℝ} (hfin : volume S ≠ ⊤) :
    IntegrableOn (fun s : ℝ => ∫ x, h x ∂(law s)) S volume := by
  have hXs : ∀ s : ℝ, Measurable (X s) := fun s =>
    hX.comp (measurable_const.prodMk measurable_id)
  haveI : IsFiniteMeasure (volume.restrict S) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hfin
  refine ⟨(stronglyMeasurable_law_integral hX hlaw hh).aestronglyMeasurable, ?_⟩
  refine (hasFiniteIntegral_const (C * (P univ).toReal)).mono ?_
  filter_upwards with s
  have h1 : ‖∫ x, h x ∂(law s)‖ ≤ C * (P univ).toReal := by
    rw [← hlaw s, integral_law_eq s (hXs s) hh]
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hb (X s ω))
  exact h1.trans (le_abs_self _)

/-- Interval integrability of `s ↦ μ_s h` over an arbitrary interval. -/
theorem intervalIntegrable_law_integral_of_forall {P : Measure Omega} [IsFiniteMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X)) {law : ℝ → Measure E}
    (hlaw : ∀ s : ℝ, P.map (X s) = law s) {h : E → ℝ} (hh : Measurable h)
    {C : ℝ} (hb : ∀ x, |h x| ≤ C) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => ∫ x, h x ∂(law s)) volume a b := by
  constructor <;>
    exact integrableOn_law_integral hX hlaw hh hb
      (by simp [Real.volume_Ioc])

/-! ## The generalized Dynkin formula in measure-valued form (Eq. (13)) -/

namespace FPKData

variable {T : Type*}

/-! ### The two terms of Eq. (13) -/

/-- The kernel average `x ↦ (Kφ)(x) = ∫ φ(y) K(x, dy)` is measurable. -/
theorem measurable_kernelAverage (D : FPKData E T) (φ : T) :
    Measurable fun x => ∫ y, D.ev φ y ∂(D.K x) :=
  (StronglyMeasurable.integral_kernel_prod_right'
    ((D.ev_measurable φ).stronglyMeasurable.comp_measurable measurable_snd)).measurable

/-- The kernel average of a test function obeys the same bound as the test function. -/
theorem abs_kernelAverage_le (D : FPKData E T) (φ : T) (x : E) :
    |∫ y, D.ev φ y ∂(D.K x)| ≤ |D.ev_bound φ| := by
  have h : ‖∫ y, D.ev φ y ∂(D.K x)‖ ≤ |D.ev_bound φ| * ((D.K x) univ).toReal :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using (D.ev_le φ y).trans (le_abs_self _))
  simpa [Real.norm_eq_abs] using h

/-- The jump integrand `λ (K − I)φ` of the Lévy-system form of the extended generator. -/
def jumpIntegrand (D : FPKData E T) (lam : E → ℝ) (φ : T) (x : E) : ℝ :=
  lam x * ((∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x)

theorem measurable_jumpIntegrand (D : FPKData E T) {lam : E → ℝ} (hlam : Measurable lam)
    (φ : T) : Measurable (D.jumpIntegrand lam φ) :=
  hlam.mul ((D.measurable_kernelAverage φ).sub (D.ev_measurable φ))

theorem abs_jumpIntegrand_le (D : FPKData E T) {lam : E → ℝ} {lamBound : ℝ}
    (hlam_nonneg : ∀ x, 0 ≤ lam x) (hlam_le : ∀ x, lam x ≤ lamBound) (φ : T) (x : E) :
    |D.jumpIntegrand lam φ x| ≤ |lamBound| * (2 * |D.ev_bound φ|) := by
  have h1 : |lam x| ≤ |lamBound| := by
    rw [abs_of_nonneg (hlam_nonneg x)]
    exact (hlam_le x).trans (le_abs_self _)
  have h2 : |(∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x| ≤ 2 * |D.ev_bound φ| :=
    calc |(∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x|
        ≤ |∫ y, D.ev φ y ∂(D.K x)| + |D.ev φ x| := abs_sub _ _
      _ ≤ |D.ev_bound φ| + |D.ev_bound φ| :=
          add_le_add (D.abs_kernelAverage_le φ x) ((D.ev_le φ x).trans (le_abs_self _))
      _ = 2 * |D.ev_bound φ| := by ring
  calc |D.jumpIntegrand lam φ x|
      = |lam x| * |(∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x| := abs_mul _ _
    _ ≤ |lamBound| * (2 * |D.ev_bound φ|) := mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)

/-- **Eq. (8) in the jump term of Eq. (13).**  When the mean jump intensity is
`r_s = λ μ_s`, the jump term `r_s(K − I)φ` is the integral of `λ (K − I)φ` against the
law `μ_s` of the state. -/
theorem jumpPair_eq_law_integral (D : FPKData E T) {lam : E → ℝ} (hlam_meas : Measurable lam)
    (hlam_nonneg : ∀ x, 0 ≤ lam x)
    (hr : ∀ s : ℝ, D.r s = (D.law s).withDensity fun x => ENNReal.ofReal (lam x))
    (s : ℝ) (φ : T) : D.jumpPair s φ = ∫ x, D.jumpIntegrand lam φ x ∂(D.law s) := by
  rw [jumpPair, hr s, SHS.integral_withDensity_ofReal hlam_meas hlam_nonneg]
  rfl

/-! ### Eq. (13) -/

/-- **Eq. (13) from Eq. (12)** (Bect, 2010): the generalized Dynkin formula in the
measure-valued form required by Definition 7 and Theorem 8, derived from the scalar
Dynkin formula (12).

The hypotheses are those of Sections 2-3 of the paper:

* `X` is the hybrid state process, with law `μ_s = D.law s` at each time `s ≥ 0`
  (`hlaw`);
* `A φ` is the extended generator of the GSHS, which by the Lévy-system identity
  (5)-(6) splits as `Aφ = Lφ + λ (K − I)φ` (`hA`);
* `r_s = λ μ_s` is the mean jump intensity of Eq. (8) (`hr`);
* Eq. (12) holds: `E{φ(X_t)} − E{φ(X_0)} = E{∫₀ᵗ (Aφ)(X_s) ds}` (`hdynkin12`).

Then `t ↦ μ_t` satisfies the generalized Dynkin formula (13), which is the standing
hypothesis `WeakDynkin` of Theorem 8. -/
theorem weakDynkin_of_dynkin12 (D : FPKData E T) {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X))
    {A : T → E → ℝ} {lam : E → ℝ} {lamBound : ℝ} {genBound : T → ℝ}
    (hlaw : ∀ s : ℝ, 0 ≤ s → P.map (X s) = D.law s)
    (hgen_meas : ∀ φ : T, Measurable (D.gen φ))
    (hgen_le : ∀ (φ : T) (x : E), |D.gen φ x| ≤ genBound φ)
    (hlam_meas : Measurable lam) (hlam_nonneg : ∀ x, 0 ≤ lam x)
    (hlam_le : ∀ x, lam x ≤ lamBound)
    (hr : ∀ s : ℝ, D.r s = (D.law s).withDensity fun x => ENNReal.ofReal (lam x))
    (hA : ∀ (φ : T) (x : E), A φ x = D.gen φ x + D.jumpIntegrand lam φ x)
    (hdynkin12 : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      (∫ ω, D.ev φ (X t ω) ∂P) - ∫ ω, D.ev φ (X 0 ω) ∂P
        = ∫ ω, (∫ s in (0 : ℝ)..t, A φ (X s ω)) ∂P) :
    D.WeakDynkin := by
  have hXs : ∀ s : ℝ, Measurable (X s) := fun s =>
    hX.comp (measurable_const.prodMk measurable_id)
  intro φ t ht
  have hev_meas := D.ev_measurable φ
  have hjint_meas : Measurable (D.jumpIntegrand lam φ) := D.measurable_jumpIntegrand hlam_meas φ
  have hjint_le := D.abs_jumpIntegrand_le hlam_nonneg hlam_le φ
  -- the extended generator
  have hA_eq : A φ = fun x => D.gen φ x + D.jumpIntegrand lam φ x := funext fun x => hA φ x
  have hA_meas : Measurable (A φ) := by
    rw [hA_eq]; exact (hgen_meas φ).add hjint_meas
  have hA_le : ∀ x, |A φ x| ≤ |genBound φ| + |lamBound| * (2 * |D.ev_bound φ|) := by
    intro x
    rw [hA_eq]
    exact (abs_add_le _ _).trans
      (add_le_add ((hgen_le φ x).trans (le_abs_self _)) (hjint_le x))
  -- Eq. (12), with the pathwise time integral turned into a time integral of the laws
  have hdyn := hdynkin12 φ t ht
  rw [integral_pathIntervalIntegral_swap hX hA_meas hA_le ht] at hdyn
  -- rewrite the left-hand side as `(μ_t − μ_0) φ`
  have hL : D.lawPair t φ = ∫ ω, D.ev φ (X t ω) ∂P := by
    rw [lawPair, ← hlaw t ht, integral_law_eq t (hXs t) hev_meas]
  have hL0 : D.lawPair 0 φ = ∫ ω, D.ev φ (X 0 ω) ∂P := by
    rw [lawPair, ← hlaw 0 le_rfl, integral_law_eq 0 (hXs 0) hev_meas]
  -- time-integrability of both terms of the right-hand side
  have hjumpPair_eq := D.jumpPair_eq_law_integral hlam_meas hlam_nonneg hr
  have hgen_ii : IntervalIntegrable (fun s => D.genPair s φ) volume 0 t :=
    intervalIntegrable_law_integral hX hlaw (hgen_meas φ) (fun x => hgen_le φ x) ht
  have hjump_ii : IntervalIntegrable (fun s => D.jumpPair s φ) volume 0 t := by
    have h := intervalIntegrable_law_integral hX hlaw hjint_meas hjint_le ht
    simpa only [← fun s => hjumpPair_eq s φ] using h
  -- split the time integral
  have hR : (∫ s in (0 : ℝ)..t, ∫ ω, A φ (X s ω) ∂P)
      = (∫ s in (0 : ℝ)..t, D.genPair s φ) + ∫ s in (0 : ℝ)..t, D.jumpPair s φ := by
    rw [← intervalIntegral.integral_add hgen_ii hjump_ii]
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hs0 : 0 ≤ s := by
      rw [uIcc_of_le ht] at hs
      exact hs.1
    have hmap : ∫ ω, A φ (X s ω) ∂P = ∫ x, A φ x ∂(D.law s) := by
      rw [← hlaw s hs0, integral_law_eq s (hXs s) hA_meas]
    have hsplit : ∫ x, A φ x ∂(D.law s) = D.genPair s φ + D.jumpPair s φ := by
      rw [hjumpPair_eq s φ, genPair, hA_eq]
      exact integral_add
        (integrable_of_bounded (hgen_meas φ) (fun x => hgen_le φ x) _)
        (integrable_of_bounded hjint_meas hjint_le _)
    simp only [hmap, hsplit]
  rw [hL, hL0, ← hR]
  exact hdyn

/-- **Eq. (13)** (Bect, 2010): the generalized Dynkin formula in the measure-valued form
required by Definition 7 and Theorem 8.

The hypotheses are those of Sections 2–3 of the paper:

* `X` is the hybrid state process, with law `μ_s = D.law s` at each time `s ≥ 0`
  (`hlaw`);
* `A φ` is the extended generator of the GSHS, which by the Lévy-system identity
  (5)–(6) splits as `Aφ = Lφ + λ (K − I)φ` (`hA`);
* `r_s = λ μ_s` is the mean jump intensity of Eq. (8) (`hr`);
* the compensated process `φ(X_t) − φ(X_0) − ∫₀ᵗ (Aφ)(X_s) ds` is a martingale
  (`hmart`); this is the content of the generalized Itô formula (3).

Then `t ↦ μ_t` satisfies the generalized Dynkin formula (13), which is the standing
hypothesis `WeakDynkin` of Theorem 8. -/
theorem weakDynkin_of_martingale (D : FPKData E T) {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X)) {F : Filtration ℝ mOmega}
    {A : T → E → ℝ} {lam : E → ℝ} {lamBound : ℝ} {genBound : T → ℝ}
    (hlaw : ∀ s : ℝ, 0 ≤ s → P.map (X s) = D.law s)
    (hgen_meas : ∀ φ : T, Measurable (D.gen φ))
    (hgen_le : ∀ (φ : T) (x : E), |D.gen φ x| ≤ genBound φ)
    (hlam_meas : Measurable lam) (hlam_nonneg : ∀ x, 0 ≤ lam x)
    (hlam_le : ∀ x, lam x ≤ lamBound)
    (hr : ∀ s : ℝ, D.r s = (D.law s).withDensity fun x => ENNReal.ofReal (lam x))
    (hA : ∀ (φ : T) (x : E), A φ x = D.gen φ x + D.jumpIntegrand lam φ x)
    (hmart : ∀ φ : T, Martingale
      (fun t ω => D.ev φ (X t ω) - D.ev φ (X 0 ω) - ∫ s in (0 : ℝ)..t, A φ (X s ω)) F P) :
    D.WeakDynkin := by
  have hXs : ∀ s : ℝ, Measurable (X s) := fun s =>
    hX.comp (measurable_const.prodMk measurable_id)
  refine D.weakDynkin_of_dynkin12 (lamBound := lamBound) (genBound := genBound) hX hlaw
    hgen_meas hgen_le hlam_meas hlam_nonneg hlam_le hr hA (fun φ t ht => ?_)
  have hev_meas := D.ev_measurable φ
  have hev_le := D.ev_le φ
  have hjint_meas : Measurable (D.jumpIntegrand lam φ) := D.measurable_jumpIntegrand hlam_meas φ
  have hjint_le := D.abs_jumpIntegrand_le hlam_nonneg hlam_le φ
  have hA_eq : A φ = fun x => D.gen φ x + D.jumpIntegrand lam φ x := funext fun x => hA φ x
  have hA_meas : Measurable (A φ) := by
    rw [hA_eq]; exact (hgen_meas φ).add hjint_meas
  have hA_le : ∀ x, |A φ x| ≤ |genBound φ| + |lamBound| * (2 * |D.ev_bound φ|) := by
    intro x
    rw [hA_eq]
    exact (abs_add_le _ _).trans
      (add_le_add ((hgen_le φ x).trans (le_abs_self _)) (hjint_le x))
  have hft : Integrable (fun ω => D.ev φ (X t ω)) P :=
    integrable_of_bounded (hev_meas.comp (hXs t)) (fun ω => hev_le _) P
  have hf0 : Integrable (fun ω => D.ev φ (X 0 ω)) P :=
    integrable_of_bounded (hev_meas.comp (hXs 0)) (fun ω => hev_le _) P
  have hgt : Integrable (fun ω => ∫ s in (0 : ℝ)..t, A φ (X s ω)) P :=
    integrable_pathIntervalIntegral hX hA_meas hA_le ht
  have hg0 : (fun ω => ∫ s in (0 : ℝ)..(0 : ℝ), A φ (X s ω)) =ᵐ[P] 0 :=
    Filter.Eventually.of_forall fun ω => by simp
  exact dynkin_of_martingale (hmart φ) hg0 hft hf0 hgt ht

/-! ### From the martingale property to a weak solution of the FPK equation -/

/-- **From the generalized Dynkin formula (13) to a weak solution of the FPK
equation.**

Theorem 8, direction (a)+(b) ⇒ (c): if the laws of the process satisfy Eq. (13), the
mean jump intensity is `r_t = λ μ_t` (Eq. (8)), the two terms of the right-hand side of
(13) are right-continuous in time, and `t ↦ μ_t φ` is right-differentiable with
derivative `μ'_t φ` (Definition 7(b)), then `t ↦ μ_t` is a solution in the weak sense of
the generalized FPK equation (14).

The measurability and local integrability in time of the two terms of (13) — which are
hypotheses of `theorem8_ab_imp_c` — are *derived* here from the process. -/
theorem isWeakFPKSolution_of_weakDynkin (D : FPKData E T) {P : Measure Omega}
    [IsProbabilityMeasure P] {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X))
    {lam : E → ℝ} {lamBound : ℝ} {genBound : T → ℝ}
    (μ' : ℝ → SignedFin E)
    (hlaw : ∀ s : ℝ, P.map (X s) = D.law s)
    (hgen_meas : ∀ φ : T, Measurable (D.gen φ))
    (hgen_le : ∀ (φ : T) (x : E), |D.gen φ x| ≤ genBound φ)
    (hlam_meas : Measurable lam) (hlam_nonneg : ∀ x, 0 ≤ lam x)
    (hlam_le : ∀ x, lam x ≤ lamBound)
    (hr : ∀ s : ℝ, D.r s = (D.law s).withDensity fun x => ENNReal.ofReal (lam x))
    (hdynkin : D.WeakDynkin)
    (hgen_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      ContinuousWithinAt (fun s => D.genPair s φ) (Ici t) t)
    (hjump_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      ContinuousWithinAt (fun s => D.jumpPair s φ) (Ici t) t)
    (hderiv : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun s => D.lawPair s φ) ((μ' t).pair (D.ev φ)) (Ici t) t) :
    D.IsWeakFPKSolution μ' := by
  have hjumpPair_eq := D.jumpPair_eq_law_integral hlam_meas hlam_nonneg hr
  have hgen_meas_time : ∀ φ : T, Measurable fun s => D.genPair s φ := fun φ =>
    (stronglyMeasurable_law_integral hX hlaw (hgen_meas φ)).measurable
  have hgen_int : ∀ (φ : T) (u : ℝ),
      IntervalIntegrable (fun s => D.genPair s φ) volume 0 u := fun φ u =>
    intervalIntegrable_law_integral_of_forall hX hlaw (hgen_meas φ)
      (fun x => hgen_le φ x) 0 u
  have hjump_meas_time : ∀ φ : T, Measurable fun s => D.jumpPair s φ := by
    intro φ
    have h := (stronglyMeasurable_law_integral hX hlaw
      (D.measurable_jumpIntegrand hlam_meas φ)).measurable
    simpa only [← fun s => hjumpPair_eq s φ] using h
  have hjump_int : ∀ (φ : T) (u : ℝ),
      IntervalIntegrable (fun s => D.jumpPair s φ) volume 0 u := by
    intro φ u
    have h := intervalIntegrable_law_integral_of_forall hX hlaw
      (D.measurable_jumpIntegrand hlam_meas φ)
      (D.abs_jumpIntegrand_le hlam_nonneg hlam_le φ) 0 u
    simpa only [← fun s => hjumpPair_eq s φ] using h
  exact D.isWeakFPKSolution_of_ab μ' hdynkin hgen_meas_time hgen_int hgen_rc
    hjump_meas_time hjump_int hjump_rc hderiv

/-- **The law of a GSHS is a weak solution of the generalized FPK equation.**

Combining Eq. (13) (`weakDynkin_of_martingale`) with Theorem 8, direction (a)+(b) ⇒ (c):
if the compensated process is a martingale, the mean jump intensity is `r_t = λ μ_t`
(Eq. (8)), the two terms of the right-hand side of (13) are right-continuous in time,
and `t ↦ μ_t φ` is right-differentiable with derivative `μ'_t φ` (Definition 7(b)),
then `t ↦ μ_t` is a solution in the weak sense of the generalized FPK equation (14). -/
theorem isWeakFPKSolution_of_martingale (D : FPKData E T) {P : Measure Omega}
    [IsProbabilityMeasure P] {X : ℝ → Omega → E} (hX : Measurable (Function.uncurry X))
    {F : Filtration ℝ mOmega} {A : T → E → ℝ} {lam : E → ℝ} {lamBound : ℝ} {genBound : T → ℝ}
    (μ' : ℝ → SignedFin E)
    (hlaw : ∀ s : ℝ, P.map (X s) = D.law s)
    (hgen_meas : ∀ φ : T, Measurable (D.gen φ))
    (hgen_le : ∀ (φ : T) (x : E), |D.gen φ x| ≤ genBound φ)
    (hlam_meas : Measurable lam) (hlam_nonneg : ∀ x, 0 ≤ lam x)
    (hlam_le : ∀ x, lam x ≤ lamBound)
    (hr : ∀ s : ℝ, D.r s = (D.law s).withDensity fun x => ENNReal.ofReal (lam x))
    (hA : ∀ (φ : T) (x : E), A φ x = D.gen φ x + D.jumpIntegrand lam φ x)
    (hmart : ∀ φ : T, Martingale
      (fun t ω => D.ev φ (X t ω) - D.ev φ (X 0 ω) - ∫ s in (0 : ℝ)..t, A φ (X s ω)) F P)
    (hgen_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      ContinuousWithinAt (fun s => D.genPair s φ) (Ici t) t)
    (hjump_rc : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      ContinuousWithinAt (fun s => D.jumpPair s φ) (Ici t) t)
    (hderiv : ∀ (φ : T) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun s => D.lawPair s φ) ((μ' t).pair (D.ev φ)) (Ici t) t) :
    D.IsWeakFPKSolution μ' :=
  D.isWeakFPKSolution_of_weakDynkin (lamBound := lamBound) (genBound := genBound) hX μ'
    hlaw hgen_meas hgen_le hlam_meas hlam_nonneg hlam_le hr
    (D.weakDynkin_of_martingale hX (fun s _ => hlaw s) hgen_meas hgen_le hlam_meas
      hlam_nonneg hlam_le hr hA hmart)
    hgen_rc hjump_rc hderiv

end FPKData

end GSHS
