/-
# Wiener processes with respect to a filtration (Gardiner §3.8.1, §4.2.4)

The general Itô calculus of `SHSLib.Gardiner.Ito.Calculus` is developed for a Wiener process
`W` **with respect to an arbitrary filtration** `𝓕` (`Gardiner.Ito.IsFWiener W 𝓕 P`):

* `P` is a probability measure, each `W t` is measurable, `W 0 = 0` a.s. and almost every path
  is continuous;
* `W t` is `𝓕 t`-measurable for `t ≥ 0`;
* for `0 ≤ s ≤ t`, `W t - W s ~ N(0, t - s)` and `W t - W s` is independent of `𝓕 s`.

These are exactly the fields of `Gardiner.Ito.IsWiener` with `𝓕 = wienerFiltration W`, so an
`IsWiener` process is an `IsFWiener` process for its natural filtration
(the one-line bridge `Gardiner.Ito.IsWiener.isFWiener` is specified in
`research/docs/plans/plan_gardiner_ito_formula.md`).  Allowing a larger
filtration is what lets an initial value `x(0)` independent of `W` enter an integrand.

This file only depends on Mathlib.  It also provides the first four moments of a centred
Gaussian (`Gardiner.Ito.gaussReal_moment_two`, `Gardiner.Ito.gaussReal_moment_four`, …).
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

/-! ### Moments of a centred Gaussian -/

/-- The moment generating function of `N(0, v)`. -/
private def gmf (v : ℝ) (t : ℝ) : ℝ := Real.exp (v * t ^ 2 / 2)

private lemma hasDerivAt_poly_gmf (v : ℝ) (Q : ℝ → ℝ) (q t : ℝ) (hQ : HasDerivAt Q q t) :
    HasDerivAt (fun s => Q s * gmf v s) ((q + Q t * (v * t)) * gmf v t) t := by
  have hg : HasDerivAt (gmf v) (gmf v t * (v * t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => v * s ^ 2 / 2) (v * t) t := by
      have := ((hasDerivAt_pow 2 t).const_mul v).div_const 2
      convert this using 1; push_cast; ring
    exact h1.exp
  convert hQ.mul hg using 1
  ring

private lemma iteratedDeriv_gmf (v : ℝ) :
    iteratedDeriv 2 (gmf v) = (fun t => (v + v ^ 2 * t ^ 2) * gmf v t) ∧
    iteratedDeriv 4 (gmf v) =
      (fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * gmf v t) := by
  have d1 : deriv (gmf v) = fun t => (v * t) * gmf v t := by
    funext t
    have := hasDerivAt_poly_gmf v (fun _ => 1) 0 t (hasDerivAt_const t 1)
    simp only [one_mul, zero_add] at this
    exact this.deriv
  have d2 : deriv (fun t => (v * t) * gmf v t) = fun t => (v + v ^ 2 * t ^ 2) * gmf v t := by
    funext t
    have hP : HasDerivAt (fun s : ℝ => v * s) v t := by
      simpa using (hasDerivAt_id t).const_mul v
    rw [(hasDerivAt_poly_gmf v _ v t hP).deriv]; ring
  have d3 : deriv (fun t => (v + v ^ 2 * t ^ 2) * gmf v t) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gmf v t := by
    funext t
    have hP : HasDerivAt (fun s : ℝ => v + v ^ 2 * s ^ 2) (v ^ 2 * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (v ^ 2)).const_add v
      convert this using 1; push_cast; ring
    rw [(hasDerivAt_poly_gmf v _ _ t hP).deriv]; ring
  have d4 : deriv (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gmf v t) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * gmf v t := by
    funext t
    have hP : HasDerivAt (fun s : ℝ => 3 * v ^ 2 * s + v ^ 3 * s ^ 3)
        (3 * v ^ 2 + v ^ 3 * (3 * t ^ 2)) t := by
      have h1 : HasDerivAt (fun s : ℝ => 3 * v ^ 2 * s) (3 * v ^ 2) t := by
        simpa using (hasDerivAt_id t).const_mul (3 * v ^ 2)
      have h2 := (hasDerivAt_pow 3 t).const_mul (v ^ 3)
      convert h1.add h2 using 1
    rw [(hasDerivAt_poly_gmf v _ _ t hP).deriv]; ring
  have e2 : iteratedDeriv 2 (gmf v) = fun t => (v + v ^ 2 * t ^ 2) * gmf v t := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, d1, d2]
  have e3 : iteratedDeriv 3 (gmf v) = fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * gmf v t := by
    rw [iteratedDeriv_succ, e2, d3]
  refine ⟨e2, ?_⟩
  rw [iteratedDeriv_succ, e3, d4]

private lemma gaussReal_moment_eq_iteratedDeriv (v : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal 0 v) = iteratedDeriv n (gmf v) 0 := by
  have hm : mgf (fun x => x) (gaussianReal 0 v) = gmf v := by
    rw [mgf_fun_id_gaussianReal]; funext t; simp [gmf]
  rw [← hm, iteratedDeriv_mgf_zero]
  · rfl
  · have : integrableExpSet (fun x : ℝ => x) (gaussianReal 0 v) = Set.univ :=
      integrableExpSet_id_gaussianReal
    simp [this]

/-- Second moment of `N(0, v)`. -/
theorem gaussReal_moment_two (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  rw [gaussReal_moment_eq_iteratedDeriv, (iteratedDeriv_gmf v).1]; simp [gmf]

/-- Fourth moment of `N(0, v)`. -/
theorem gaussReal_moment_four (v : ℝ≥0) : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  rw [gaussReal_moment_eq_iteratedDeriv, (iteratedDeriv_gmf v).2]; simp [gmf]

/-- Every power is integrable under `N(0, v)`. -/
lemma gaussReal_integrable_pow (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h : MemLp (fun x : ℝ => x) (n : ℝ≥0) (gaussianReal 0 v) := memLp_id_gaussianReal _
  have h' := h.integrable_norm_pow (by omega)
  refine h'.mono' (continuous_pow n).aestronglyMeasurable (Filter.Eventually.of_forall
    fun x => ?_)
  simp [Real.norm_eq_abs]

/-- Transfer of integrability along a random variable with law `N(0, v)`. -/
lemma integrable_comp_of_map_gauss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : Measurable X) (hlaw : P.map X = gaussianReal 0 v) {f : ℝ → ℝ}
    (hf : Measurable f) (hi : Integrable f (gaussianReal 0 v)) : Integrable (fun ω => f (X ω)) P := by
  rw [← hlaw] at hi
  exact (integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable).mp hi

/-- Transfer of integrals along a random variable with law `N(0, v)`. -/
lemma integral_comp_of_map_gauss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : Measurable X) (hlaw : P.map X = gaussianReal 0 v) {f : ℝ → ℝ}
    (hf : Measurable f) : ∫ ω, f (X ω) ∂P = ∫ x, f x ∂(gaussianReal 0 v) := by
  rw [← hlaw, integral_map hX.aemeasurable hf.aestronglyMeasurable]

/-! ### The interface -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **A standard Wiener process with respect to the filtration `𝓕`** on real time `t ≥ 0`.
The fields coincide with those of `Gardiner.Ito.IsWiener` (except that independence of increments
over partitions is not required: it follows from `indep_past`), with the natural filtration
replaced by `𝓕`. -/
structure IsFWiener (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  measurable : ∀ t, Measurable (W t)
  zero : ∀ᵐ ω ∂P, W 0 ω = 0
  cont : ∀ᵐ ω ∂P, Continuous fun t => W t ω
  adapted : ∀ t, 0 ≤ t → StronglyMeasurable[𝓕 t] (W t)
  law_sub : ∀ s t : ℝ, 0 ≤ s → s ≤ t → P.map (W t - W s) = gaussianReal 0 (t - s).toNNReal
  indep_past : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    Indep (MeasurableSpace.comap (W t - W s) inferInstance) (𝓕 s) P

namespace IsFWiener

variable {W : ℝ → Ω → ℝ} {𝓕 : Filtration ℝ mΩ} {P : Measure Ω} (hW : IsFWiener W 𝓕 P)
include hW

lemma measurable_incr (s t : ℝ) : Measurable (fun ω => W t ω - W s ω) :=
  (hW.measurable t).sub (hW.measurable s)

lemma law_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P.map (fun ω => W t ω - W s ω) = gaussianReal 0 (t - s).toNNReal :=
  hW.law_sub s t hs hst

lemma integrable_incr_pow {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    Integrable (fun ω => (W t ω - W s ω) ^ n) P :=
  integrable_comp_of_map_gauss (hW.measurable_incr s t) (hW.law_incr hs hst)
    (continuous_pow n).measurable (gaussReal_integrable_pow _ n)

lemma integrable_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => W t ω - W s ω) P := by
  simpa using hW.integrable_incr_pow hs hst 1

lemma integral_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W t ω - W s ω) ∂P = 0 := by
  rw [integral_comp_of_map_gauss (f := fun x => x) (hW.measurable_incr s t) (hW.law_incr hs hst)
    measurable_id]
  simp

lemma integral_incr_sq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W t ω - W s ω) ^ 2 ∂P = t - s := by
  rw [integral_comp_of_map_gauss (f := fun x => x ^ 2) (hW.measurable_incr s t)
    (hW.law_incr hs hst) (continuous_pow 2).measurable, gaussReal_moment_two,
    Real.coe_toNNReal _ (sub_nonneg.mpr hst)]

lemma integral_incr_four {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W t ω - W s ω) ^ 4 ∂P = 3 * (t - s) ^ 2 := by
  rw [integral_comp_of_map_gauss (f := fun x => x ^ 4) (hW.measurable_incr s t)
    (hW.law_incr hs hst) (continuous_pow 4).measurable, gaussReal_moment_four,
    Real.coe_toNNReal _ (sub_nonneg.mpr hst)]

lemma memLp_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    MemLp (fun ω => W t ω - W s ω) 2 P :=
  (memLp_two_iff_integrable_sq (hW.measurable_incr s t).aestronglyMeasurable).mpr
    (hW.integrable_incr_pow hs hst 2)

/-- `E[(ΔW² - Δt)²] = 2Δt²`. -/
lemma integral_incr_sq_sub_sq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, ((W t ω - W s ω) ^ 2 - (t - s)) ^ 2 ∂P = 2 * (t - s) ^ 2 := by
  have := hW.isProbabilityMeasure
  have h4 := hW.integrable_incr_pow hs hst 4
  have h2 := hW.integrable_incr_pow hs hst 2
  have e : (fun ω => ((W t ω - W s ω) ^ 2 - (t - s)) ^ 2) = fun ω =>
      (W t ω - W s ω) ^ 4 - (2 * (t - s)) * (W t ω - W s ω) ^ 2 + (t - s) ^ 2 := by
    funext ω; ring
  have h42 : Integrable (fun ω => (W t ω - W s ω) ^ 4 - 2 * (t - s) * (W t ω - W s ω) ^ 2) P :=
    h4.sub (h2.const_mul _)
  rw [e, integral_add h42 (integrable_const _),
    integral_sub h4 (h2.const_mul _), integral_const_mul, hW.integral_incr_four hs hst,
    hW.integral_incr_sq hs hst]
  simp; ring

lemma memLp_incr_sq_sub {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    MemLp (fun ω => (W t ω - W s ω) ^ 2 - (t - s)) 2 P := by
  have := hW.isProbabilityMeasure
  refine (memLp_two_iff_integrable_sq
    (((hW.measurable_incr s t).pow_const 2).sub_const _).aestronglyMeasurable).mpr ?_
  have h4 := hW.integrable_incr_pow hs hst 4
  have h2 := hW.integrable_incr_pow hs hst 2
  refine ((h4.sub (h2.const_mul (2 * (t - s)))).add (integrable_const ((t - s) ^ 2))).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]; ring

lemma W_eq_incr_ae (t : ℝ) : (fun ω => W t ω) =ᵐ[P] fun ω => W t ω - W 0 ω := by
  filter_upwards [hW.zero] with ω hω
  simp [hω]

/-- `W t ~ N(0, t)`. -/
lemma map_eval {t : ℝ} (ht : 0 ≤ t) : P.map (W t) = gaussianReal 0 t.toNNReal := by
  have h := hW.law_sub 0 t le_rfl ht
  rw [sub_zero] at h
  rw [← h]
  exact Measure.map_congr (hW.W_eq_incr_ae t)

lemma integrable_pow {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : Integrable (fun ω => W t ω ^ n) P :=
  integrable_comp_of_map_gauss (hW.measurable t) (hW.map_eval ht) (continuous_pow n).measurable
    (gaussReal_integrable_pow _ n)

lemma integrable {t : ℝ} (ht : 0 ≤ t) : Integrable (W t) P := by
  simpa using hW.integrable_pow ht 1

lemma memLp {t : ℝ} (ht : 0 ≤ t) : MemLp (W t) 2 P :=
  (memLp_two_iff_integrable_sq (hW.measurable t).aestronglyMeasurable).mpr (hW.integrable_pow ht 2)

lemma integral_sq {t : ℝ} (ht : 0 ≤ t) : ∫ ω, W t ω ^ 2 ∂P = t := by
  rw [integral_comp_of_map_gauss (f := fun x => x ^ 2) (hW.measurable t) (hW.map_eval ht)
    (continuous_pow 2).measurable, gaussReal_moment_two, Real.coe_toNNReal _ ht]

/-- A random variable measurable w.r.t. the past `𝓕 s` is independent of any function of a
future increment `W t - W s`. -/
lemma indepFun_past {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 s] Z) {g : ℝ → ℝ} (hg : Measurable g) :
    IndepFun Z (fun ω => g (W t ω - W s ω)) P := by
  have h := (hW.indep_past s t hs hst).symm
  have h1 : MeasurableSpace.comap Z inferInstance ≤ 𝓕 s := hZ.measurable.comap_le
  have h2 : MeasurableSpace.comap (fun ω => g (W t ω - W s ω)) inferInstance ≤
      MeasurableSpace.comap (W t - W s) inferInstance := by
    have : (fun ω => g (W t ω - W s ω)) = g ∘ (W t - W s) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hg.comap_le
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h h1) h2

/-- `E[Z g(W t - W s)] = E[Z] E[g(ΔW)]` and integrability, for `𝓕 s`-measurable integrable `Z`. -/
lemma mul_incr_fun {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 s] Z) (hZi : Integrable Z P) {g : ℝ → ℝ} (hg : Measurable g)
    (hgi : Integrable (fun ω => g (W t ω - W s ω)) P) :
    Integrable (fun ω => Z ω * g (W t ω - W s ω)) P ∧
      ∫ ω, Z ω * g (W t ω - W s ω) ∂P = (∫ ω, Z ω ∂P) * ∫ ω, g (W t ω - W s ω) ∂P := by
  have hind := hW.indepFun_past hs hst hZ hg
  exact ⟨hind.integrable_mul hZi hgi,
    hind.integral_fun_mul_eq_mul_integral hZi.aestronglyMeasurable hgi.aestronglyMeasurable⟩

/-- `E[Z (W t - W s)] = 0` for an integrable `𝓕 s`-measurable `Z`. -/
lemma mul_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 s] Z) (hZi : Integrable Z P) :
    Integrable (fun ω => Z ω * (W t ω - W s ω)) P ∧ ∫ ω, Z ω * (W t ω - W s ω) ∂P = 0 := by
  obtain ⟨h1, h2⟩ := hW.mul_incr_fun hs hst hZ hZi (g := id) measurable_id
    (hW.integrable_incr hs hst)
  refine ⟨h1, ?_⟩
  simp only [id] at h2
  rw [h2, hW.integral_incr hs hst, mul_zero]

/-- `E[Z (W t - W s)²] = E[Z] (t - s)` for an integrable `𝓕 s`-measurable `Z`. -/
lemma mul_incr_sq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 s] Z) (hZi : Integrable Z P) :
    Integrable (fun ω => Z ω * (W t ω - W s ω) ^ 2) P ∧
      ∫ ω, Z ω * (W t ω - W s ω) ^ 2 ∂P = (∫ ω, Z ω ∂P) * (t - s) := by
  obtain ⟨h1, h2⟩ := hW.mul_incr_fun hs hst hZ hZi (g := fun x => x ^ 2)
    (continuous_pow 2).measurable (hW.integrable_incr_pow hs hst 2)
  exact ⟨h1, by rw [h2, hW.integral_incr_sq hs hst]⟩

/-- `Z (W t - W s)` is square integrable for a square-integrable `𝓕 s`-measurable `Z`. -/
lemma memLp_mul_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 s] Z) (hZ2 : MemLp Z 2 P) :
    MemLp (fun ω => Z ω * (W t ω - W s ω)) 2 P := by
  have hZm : StronglyMeasurable Z := hZ.mono (𝓕.le s)
  refine (memLp_two_iff_integrable_sq
    (hZm.measurable.mul (hW.measurable_incr s t)).aestronglyMeasurable).mpr ?_
  have hsq : StronglyMeasurable[𝓕 s] (fun ω => Z ω ^ 2) := hZ.pow 2
  have := (hW.mul_incr_sq hs hst hsq hZ2.integrable_sq).1
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only; ring

/-- `E[W t - W s | 𝓕 s] = 0`. -/
lemma condExp_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P[fun ω => W t ω - W s ω | 𝓕 s] =ᵐ[P] 0 := by
  have := hW.isProbabilityMeasure
  have h := condExp_indep_eq (hW.measurable_incr s t).comap_le (𝓕.le s)
    (comap_measurable (W t - W s)).stronglyMeasurable (hW.indep_past s t hs hst)
  have h3 : ∫ ω, (W t - W s) ω ∂P = 0 := hW.integral_incr hs hst
  change P[W t - W s | 𝓕 s] =ᵐ[P] 0
  filter_upwards [h] with ω hω
  rw [hω, h3]; rfl

/-- `E[φ (W t - W s) | 𝓕 s] = 0` for square-integrable `𝓕 s`-measurable `φ`. -/
lemma condExp_mul_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {φ : Ω → ℝ}
    (hφ : StronglyMeasurable[𝓕 s] φ) (hφ2 : MemLp φ 2 P) :
    P[fun ω => φ ω * (W t ω - W s ω) | 𝓕 s] =ᵐ[P] 0 := by
  have := hW.isProbabilityMeasure
  have h1 : P[φ * (W t - W s) | 𝓕 s] =ᵐ[P] φ * P[W t - W s | 𝓕 s] :=
    condExp_mul_of_stronglyMeasurable_left hφ
      ((hW.memLp_mul_incr hs hst hφ hφ2).integrable one_le_two)
      (hW.integrable_incr hs hst)
  have h2 := hW.condExp_incr hs hst
  change P[φ * (W t - W s) | 𝓕 s] =ᵐ[P] 0
  filter_upwards [h1, h2] with ω h1 h2
  rw [h1, Pi.mul_apply]
  change φ ω * P[fun ω => W t ω - W s ω | 𝓕 s] ω = 0
  rw [h2]; simp

end IsFWiener

end Gardiner.Ito
