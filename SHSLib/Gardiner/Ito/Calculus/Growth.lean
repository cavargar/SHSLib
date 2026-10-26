/-
# Exponential moments of `W` and functions of moderate growth

The hypotheses of Itô's formula (`MSBounded`, `MSUnifCont`) are verified for `g(t, W(t))` when
`g` has at most exponential growth with an exponentially weighted Lipschitz bound
(`Gardiner.Ito.ExpGrowth`).  This class contains all polynomials in `x` and all functions
`A exp(c x + d t)`, so it covers `Wⁿ` and the exponential functions of geometric Brownian motion,
neither of which has bounded derivatives.

* `Gardiner.Ito.IsFWiener.integral_exp_mul`: `⟨exp(c W(t))⟩ = exp(c² t/2)` (Gardiner (4.4.8)).
* `Gardiner.Ito.ExpGrowth.msBounded`, `Gardiner.Ito.ExpGrowth.msUnifCont`.
* `Gardiner.Ito.ExpGrowth.of_deriv`, `Gardiner.Ito.expGrowth_pow`, `Gardiner.Ito.expGrowth_exp`.
-/
import SHSLib.Gardiner.Ito.Calculus.ItoFormula

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

/-- `∫ exp(c x) dN(0, v) = exp(v c²/2)`. -/
lemma gaussReal_integral_exp (v : ℝ≥0) (c : ℝ) :
    ∫ x, Real.exp (c * x) ∂(gaussianReal 0 v) = Real.exp (v * c ^ 2 / 2) := by
  have := mgf_gaussianReal (p := gaussianReal 0 v) (X := id) (μ := 0) (v := v) Measure.map_id c
  simpa [mgf] using this

lemma exp_mul_abs_le (K x : ℝ) : Real.exp (K * |x|) ≤ Real.exp (K * x) + Real.exp (-K * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-K * x)]
  · rw [abs_of_nonpos hx, show K * -x = -K * x by ring]; linarith [Real.exp_pos (K * x)]

lemma pow_abs_le_factorial_mul_exp (x : ℝ) (k : ℕ) : |x| ^ k ≤ k.factorial * Real.exp |x| := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hk] at h
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

lemma IsFWiener.integrable_exp_mul {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * W t ω)) P :=
  integrable_comp_of_map_gauss (hW.measurable t) (hW.map_eval ht) (by fun_prop)
    (integrable_exp_mul_gaussianReal c)

/-- **Gardiner (4.4.8)** for `z = c W(t)`: `⟨exp(c W(t))⟩ = exp(c² t/2)`. -/
lemma IsFWiener.integral_exp_mul {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    ∫ ω, Real.exp (c * W t ω) ∂P = Real.exp (c ^ 2 * t / 2) := by
  rw [integral_comp_of_map_gauss (f := fun x => Real.exp (c * x)) (hW.measurable t)
    (hW.map_eval ht) (by fun_prop), gaussReal_integral_exp, Real.coe_toNNReal _ ht]
  ring_nf

lemma IsFWiener.integrable_exp_mul_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * (W t ω - W s ω))) P :=
  integrable_comp_of_map_gauss (f := fun x => Real.exp (c * x)) (hW.measurable_incr s t)
    (hW.law_incr hs hst) (by fun_prop) (integrable_exp_mul_gaussianReal c)

lemma IsFWiener.integral_exp_mul_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (c : ℝ) :
    ∫ ω, Real.exp (c * (W t ω - W s ω)) ∂P = Real.exp (c ^ 2 * (t - s) / 2) := by
  rw [integral_comp_of_map_gauss (f := fun x => Real.exp (c * x)) (hW.measurable_incr s t)
    (hW.law_incr hs hst) (by fun_prop), gaussReal_integral_exp,
    Real.coe_toNNReal _ (by linarith)]
  ring_nf

lemma IsFWiener.integrable_exp_abs {t : ℝ} (ht : 0 ≤ t) (K : ℝ) :
    Integrable (fun ω => Real.exp (K * |W t ω|)) P := by
  have hm := hW.measurable t
  refine ((hW.integrable_exp_mul ht K).add (hW.integrable_exp_mul ht (-K))).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_mul_abs_le K (W t ω)

lemma IsFWiener.integral_exp_abs_le {t : ℝ} (ht : 0 ≤ t) (K : ℝ) :
    ∫ ω, Real.exp (K * |W t ω|) ∂P ≤ 2 * Real.exp (K ^ 2 * t / 2) := by
  have h := integral_mono (hW.integrable_exp_abs ht K)
    ((hW.integrable_exp_mul ht K).add (hW.integrable_exp_mul ht (-K)))
    (fun ω => exp_mul_abs_le K (W t ω))
  simp only [Pi.add_apply] at h
  rw [integral_add (hW.integrable_exp_mul ht K) (hW.integrable_exp_mul ht (-K)),
    hW.integral_exp_mul ht, hW.integral_exp_mul ht, neg_sq] at h
  linarith

lemma IsFWiener.integral_sub_pow_four {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ ω, (W s ω - W t ω) ^ 4 ∂P = 3 * (s - t) ^ 2 := by
  rcases le_total s t with hst | hts
  · rw [show (fun ω => (W s ω - W t ω) ^ 4) = fun ω => (W t ω - W s ω) ^ 4 by
      funext ω; ring, hW.integral_incr_four hs hst]
    ring
  · rw [hW.integral_incr_four ht hts]

lemma IsFWiener.integrable_sub_pow_four {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Integrable (fun ω => (W s ω - W t ω) ^ 4) P := by
  rcases le_total s t with hst | hts
  · rw [show (fun ω => (W s ω - W t ω) ^ 4) = fun ω => (W t ω - W s ω) ^ 4 by
      funext ω; ring]
    exact hW.integrable_incr_pow hs hst 4
  · exact hW.integrable_incr_pow ht hts 4

omit hW in
/-- **Moderate growth.** `|g(t, x)| ≤ C e^{K|x|}` and
`|g(s, x) - g(t, y)| ≤ C(|s - t| + |x - y|)(e^{K|x|} + e^{K|y|})` for `s, t ∈ [0, T]`. -/
structure ExpGrowth (g : ℝ → ℝ → ℝ) (T C K : ℝ) : Prop where
  cont : Continuous (Function.uncurry g)
  bound : ∀ t ∈ Icc 0 T, ∀ x, |g t x| ≤ C * Real.exp (K * |x|)
  lip : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x y,
    |g s x - g t y| ≤ C * (|s - t| + |x - y|) * (Real.exp (K * |x|) + Real.exp (K * |y|))

omit hW in
lemma ExpGrowth.C_nonneg {g : ℝ → ℝ → ℝ} {T C K : ℝ} (hg : ExpGrowth g T C K) {t : ℝ}
    (ht : t ∈ Icc 0 T) : 0 ≤ C := by
  have h := (abs_nonneg _).trans (hg.bound t ht 0)
  exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)

/-- Functions of moderate growth of `W` are bounded in mean square. -/
theorem ExpGrowth.msBounded {g : ℝ → ℝ → ℝ} {T C K : ℝ} (hg : ExpGrowth g T C K) :
    MSBounded P T fun t ω => g t (W t ω) := by
  have := hW.isProbabilityMeasure
  refine ⟨C ^ 2 * (2 * Real.exp ((2 * K) ^ 2 * T / 2)), fun t ht => ?_⟩
  have hC := hg.C_nonneg ht
  have hm : Measurable fun ω => g t (W t ω) :=
    hg.cont.measurable.comp (measurable_const.prodMk (hW.measurable t))
  have hpt : ∀ ω, g t (W t ω) ^ 2 ≤ C ^ 2 * Real.exp (2 * K * |W t ω|) := by
    intro ω
    have h1 := hg.bound t ht (W t ω)
    calc g t (W t ω) ^ 2 = |g t (W t ω)| ^ 2 := (sq_abs _).symm
      _ ≤ (C * Real.exp (K * |W t ω|)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = C ^ 2 * Real.exp (2 * K * |W t ω|) := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  have hint : Integrable (fun ω => C ^ 2 * Real.exp (2 * K * |W t ω|)) P :=
    (hW.integrable_exp_abs ht.1 (2 * K)).const_mul _
  have hsq : Integrable (fun ω => g t (W t ω) ^ 2) P :=
    hint.mono' (hm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ω)
  refine ⟨(memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hsq, ?_⟩
  calc ∫ ω, g t (W t ω) ^ 2 ∂P ≤ ∫ ω, C ^ 2 * Real.exp (2 * K * |W t ω|) ∂P :=
        integral_mono hsq hint hpt
    _ = C ^ 2 * ∫ ω, Real.exp (2 * K * |W t ω|) ∂P := integral_const_mul _ _
    _ ≤ C ^ 2 * (2 * Real.exp ((2 * K) ^ 2 * t / 2)) := by
        gcongr; exact hW.integral_exp_abs_le ht.1 _
    _ ≤ C ^ 2 * (2 * Real.exp ((2 * K) ^ 2 * T / 2)) := by
        gcongr
        · exact ht.2

omit hW in
lemma sq_le_aux {G C d a es et δ : ℝ} (hδ : 0 < δ) (h1 : |G| ≤ C * (d + a) * (es + et)) :
    G ^ 2 ≤ C ^ 2 / 2 * (8 * (d ^ 4 + a ^ 4) / δ + δ * (8 * (es ^ 4 + et ^ 4))) := by
  set U := (d + a) ^ 2 with hU
  set V := (es + et) ^ 2 with hV
  have hU0 : 0 ≤ U := sq_nonneg _
  have hV0 : 0 ≤ V := sq_nonneg _
  have step1 : G ^ 2 ≤ C ^ 2 * (U * V) := by
    calc G ^ 2 = |G| ^ 2 := (sq_abs _).symm
      _ ≤ (C * (d + a) * (es + et)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = C ^ 2 * (U * V) := by ring
  have step2 : U * V ≤ (U ^ 2 / δ + δ * V ^ 2) / 2 := by
    have e : (U ^ 2 / δ + δ * V ^ 2) / 2 - U * V = (U - δ * V) ^ 2 / (2 * δ) := by
      field_simp; ring
    have : 0 ≤ (U - δ * V) ^ 2 / (2 * δ) := div_nonneg (sq_nonneg _) (by positivity)
    linarith
  have step3 : U ^ 2 ≤ 8 * (d ^ 4 + a ^ 4) := by
    have u1 : U ≤ 2 * (d ^ 2 + a ^ 2) := by nlinarith [sq_nonneg (d - a)]
    have u2 : U ^ 2 ≤ (2 * (d ^ 2 + a ^ 2)) ^ 2 := pow_le_pow_left₀ hU0 u1 2
    nlinarith [sq_nonneg (d ^ 2 - a ^ 2)]
  have step4 : V ^ 2 ≤ 8 * (es ^ 4 + et ^ 4) := by
    have u1 : V ≤ 2 * (es ^ 2 + et ^ 2) := by nlinarith [sq_nonneg (es - et)]
    have u2 : V ^ 2 ≤ (2 * (es ^ 2 + et ^ 2)) ^ 2 := pow_le_pow_left₀ hV0 u1 2
    nlinarith [sq_nonneg (es ^ 2 - et ^ 2)]
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  calc G ^ 2 ≤ C ^ 2 * (U * V) := step1
    _ ≤ C ^ 2 * ((U ^ 2 / δ + δ * V ^ 2) / 2) := mul_le_mul_of_nonneg_left step2 hC2
    _ ≤ C ^ 2 * ((8 * (d ^ 4 + a ^ 4) / δ + δ * (8 * (es ^ 4 + et ^ 4))) / 2) := by
        gcongr
    _ = _ := by ring

lemma IsFWiener.integral_mom_bound {s t T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (ht : 0 ≤ t)
    (htT : t ≤ T) (K C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun ω => C ^ 2 / 2 * (8 * (|s - t| ^ 4 + (W s ω - W t ω) ^ 4) / δ +
      δ * (8 * (Real.exp (4 * K * |W s ω|) + Real.exp (4 * K * |W t ω|))))) P ∧
    ∫ ω, C ^ 2 / 2 * (8 * (|s - t| ^ 4 + (W s ω - W t ω) ^ 4) / δ +
      δ * (8 * (Real.exp (4 * K * |W s ω|) + Real.exp (4 * K * |W t ω|)))) ∂P ≤
      C ^ 2 / 2 * (8 * (|s - t| ^ 4 + 3 * (s - t) ^ 2) / δ +
        δ * (8 * (4 * Real.exp (8 * K ^ 2 * T)))) := by
  have := hW.isProbabilityMeasure
  have i0 : Integrable (fun ω => |s - t| ^ 4 + (W s ω - W t ω) ^ 4) P :=
    (integrable_const _).add (hW.integrable_sub_pow_four hs ht)
  have ie : Integrable (fun ω => Real.exp (4 * K * |W s ω|) + Real.exp (4 * K * |W t ω|)) P :=
    (hW.integrable_exp_abs hs _).add (hW.integrable_exp_abs ht _)
  have i1 : Integrable (fun ω => 8 * (|s - t| ^ 4 + (W s ω - W t ω) ^ 4) / δ) P :=
    (i0.const_mul 8).div_const _
  have i2 : Integrable (fun ω => δ * (8 * (Real.exp (4 * K * |W s ω|) +
      Real.exp (4 * K * |W t ω|)))) P := (ie.const_mul 8).const_mul _
  refine ⟨(i1.add i2).const_mul _, ?_⟩
  have v0 : ∫ ω, |s - t| ^ 4 + (W s ω - W t ω) ^ 4 ∂P = |s - t| ^ 4 + 3 * (s - t) ^ 2 := by
    rw [integral_add (integrable_const _) (hW.integrable_sub_pow_four hs ht),
      hW.integral_sub_pow_four hs ht]
    simp
  have be : ∀ r, 0 ≤ r → r ≤ T → ∫ ω, Real.exp (4 * K * |W r ω|) ∂P ≤
      2 * Real.exp (8 * K ^ 2 * T) := by
    intro r hr hrT
    refine (hW.integral_exp_abs_le hr _).trans ?_
    have h : (4 * K) ^ 2 * r / 2 ≤ 8 * K ^ 2 * T := by
      nlinarith [mul_le_mul_of_nonneg_left hrT (sq_nonneg K)]
    have := Real.exp_le_exp.mpr h
    linarith
  have ve : ∫ ω, Real.exp (4 * K * |W s ω|) + Real.exp (4 * K * |W t ω|) ∂P ≤
      4 * Real.exp (8 * K ^ 2 * T) := by
    rw [integral_add (hW.integrable_exp_abs hs _) (hW.integrable_exp_abs ht _)]
    linarith [be s hs hsT, be t ht htT]
  rw [integral_const_mul, integral_add i1 i2, integral_div, integral_const_mul, v0,
    integral_const_mul, integral_const_mul]
  have hC2 : 0 ≤ C ^ 2 / 2 := by positivity
  gcongr

/-- Functions of moderate growth of `W` are uniformly continuous in mean square. -/
theorem ExpGrowth.msUnifCont {g : ℝ → ℝ → ℝ} {T C K : ℝ} (hg : ExpGrowth g T C K) :
    MSUnifCont P T fun t ω => g t (W t ω) := by
  have := hW.isProbabilityMeasure
  intro ε hε
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (8 * K ^ 2 * T) := ⟨_, rfl⟩
  have hE0 : 0 < E := hE ▸ Real.exp_pos _
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min 1 (ε / (16 * C ^ 2 * (1 + E) + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ ▸ lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := hδ ▸ min_le_left _ _
  have hδ2 : δ ≤ ε / (16 * C ^ 2 * (1 + E) + 1) := hδ ▸ min_le_right _ _
  refine ⟨δ, hδ0, fun s t hs hsT ht htT hst => ?_⟩
  have hpt : ∀ ω, (g s (W s ω) - g t (W t ω)) ^ 2 ≤ C ^ 2 / 2 *
      (8 * (|s - t| ^ 4 + (W s ω - W t ω) ^ 4) / δ +
        δ * (8 * (Real.exp (4 * K * |W s ω|) + Real.exp (4 * K * |W t ω|)))) := by
    intro ω
    have h := sq_le_aux hδ0 (hg.lip s ⟨hs, hsT⟩ t ⟨ht, htT⟩ (W s ω) (W t ω))
    have e1 : |W s ω - W t ω| ^ 4 = (W s ω - W t ω) ^ 4 := by
      rw [pow_abs, abs_of_nonneg (by positivity)]
    have e2 : ∀ y : ℝ, Real.exp (K * |y|) ^ 4 = Real.exp (4 * K * |y|) := by
      intro y; rw [← Real.exp_nat_mul]; ring_nf
    rw [e1, e2, e2] at h
    exact h
  obtain ⟨hBi, hBle⟩ := hW.integral_mom_bound hs hsT ht htT K C hδ0
  have hd : |s - t| < δ := hst
  have hd0 : 0 ≤ |s - t| := abs_nonneg _
  have hd4 : |s - t| ^ 4 + 3 * (s - t) ^ 2 ≤ 4 * δ ^ 2 := by
    have e : (s - t) ^ 2 = |s - t| ^ 2 := (sq_abs _).symm
    rw [e]
    have h2 : |s - t| ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hd0 hd.le 2
    have h1 : |s - t| ≤ 1 := hd.le.trans hδ1
    have h4 : |s - t| ^ 4 ≤ |s - t| ^ 2 := by
      have : |s - t| ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (|s - t|)]
    linarith
  have v1 : 8 * (|s - t| ^ 4 + 3 * (s - t) ^ 2) / δ ≤ 32 * δ := by
    rw [div_le_iff₀ hδ0]; nlinarith
  have hC2 : 0 ≤ C ^ 2 / 2 := by positivity
  calc ∫ ω, (g s (W s ω) - g t (W t ω)) ^ 2 ∂P
      ≤ ∫ ω, C ^ 2 / 2 * (8 * (|s - t| ^ 4 + (W s ω - W t ω) ^ 4) / δ +
        δ * (8 * (Real.exp (4 * K * |W s ω|) + Real.exp (4 * K * |W t ω|)))) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hBi
          (Eventually.of_forall hpt)
    _ ≤ C ^ 2 / 2 * (8 * (|s - t| ^ 4 + 3 * (s - t) ^ 2) / δ +
        δ * (8 * (4 * Real.exp (8 * K ^ 2 * T)))) := hBle
    _ ≤ C ^ 2 / 2 * (32 * δ + δ * (8 * (4 * E))) := by rw [← hE]; gcongr
    _ = 16 * C ^ 2 * (1 + E) * δ := by ring
    _ ≤ 16 * C ^ 2 * (1 + E) * (ε / (16 * C ^ 2 * (1 + E) + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

omit hW in
/-- Moderate growth from derivative bounds (two mean-value estimates). -/
theorem ExpGrowth.of_deriv {g gt gx : ℝ → ℝ → ℝ} {T C K : ℝ} (hK : 0 ≤ K)
    (hc : Continuous (Function.uncurry g))
    (hgt : ∀ t x, HasDerivAt (fun s => g s x) (gt t x) t)
    (hgx : ∀ t x, HasDerivAt (fun y => g t y) (gx t x) x)
    (hb : ∀ t ∈ Icc 0 T, ∀ x, |g t x| ≤ C * Real.exp (K * |x|))
    (hbt : ∀ t ∈ Icc 0 T, ∀ x, |gt t x| ≤ C * Real.exp (K * |x|))
    (hbx : ∀ t ∈ Icc 0 T, ∀ x, |gx t x| ≤ C * Real.exp (K * |x|)) :
    ExpGrowth g T C K := by
  refine ⟨hc, hb, fun s hs t ht x y => ?_⟩
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hb s hs 0)) (Real.exp_pos _)
  set ex := Real.exp (K * |x|)
  set ey := Real.exp (K * |y|)
  have hex : 0 < ex := Real.exp_pos _
  have hey : 0 < ey := Real.exp_pos _
  have h1 : |g s x - g t x| ≤ C * ex * |s - t| := by
    have := (convex_uIcc t s).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => g r x) (f' := fun r => gt r x) (C := C * ex)
      (fun r _ => (hgt r x).hasDerivWithinAt)
      (fun r hr => by rw [Real.norm_eq_abs]; exact hbt r (Set.uIcc_subset_Icc ht hs hr) x)
      left_mem_uIcc right_mem_uIcc
    simpa [Real.norm_eq_abs] using this
  have h2 : |g t x - g t y| ≤ C * (ex + ey) * |x - y| := by
    have := (convex_uIcc y x).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => g t z) (f' := fun z => gx t z) (C := C * (ex + ey))
      (fun z _ => (hgx t z).hasDerivWithinAt)
      (fun z hz => by
        rw [Real.norm_eq_abs]
        refine (hbx t ht z).trans (mul_le_mul_of_nonneg_left ?_ hC)
        have hz' : |z| ≤ max |y| |x| := by
          rw [Set.mem_uIcc] at hz
          rcases hz with hz | hz
          · exact abs_le_max_abs_abs hz.1 hz.2
          · rw [max_comm]; exact abs_le_max_abs_abs hz.1 hz.2
        rcases le_total |y| |x| with hyx | hxy
        · rw [max_eq_right hyx] at hz'
          have : Real.exp (K * |z|) ≤ ex := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz' hK)
          linarith
        · rw [max_eq_left hxy] at hz'
          have : Real.exp (K * |z|) ≤ ey := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz' hK)
          linarith)
      left_mem_uIcc right_mem_uIcc
    simpa [Real.norm_eq_abs] using this
  calc |g s x - g t y| ≤ |g s x - g t x| + |g t x - g t y| := abs_sub_le _ _ _
    _ ≤ C * ex * |s - t| + C * (ex + ey) * |x - y| := add_le_add h1 h2
    _ ≤ C * (|s - t| + |x - y|) * (ex + ey) := by
        have := abs_nonneg (s - t)
        have := abs_nonneg (x - y)
        nlinarith [mul_nonneg hC hey.le, mul_nonneg (mul_nonneg hC hey.le) (abs_nonneg (s - t))]

omit hW in
/-- `xᵐ` has moderate growth. -/
theorem expGrowth_pow (T : ℝ) (m : ℕ) :
    ExpGrowth (fun _ x => x ^ m) T (m + 1).factorial 1 := by
  have hf : ∀ k : ℕ, (k.factorial : ℝ) ≤ (m + 1).factorial → ∀ x : ℝ,
      |x| ^ k ≤ (m + 1).factorial * Real.exp (1 * |x|) := by
    intro k hk x
    rw [one_mul]
    exact (pow_abs_le_factorial_mul_exp x k).trans
      (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le)
  refine ExpGrowth.of_deriv (gt := fun _ _ => 0) (gx := fun _ x => m * x ^ (m - 1)) zero_le_one
    (by fun_prop) (fun t x => hasDerivAt_const _ _) (fun t x => hasDerivAt_pow m x)
    (fun t _ x => ?_) (fun t _ x => ?_) (fun t _ x => ?_)
  · rw [abs_pow]
    exact hf m (by exact_mod_cast Nat.factorial_le (Nat.le_succ m)) x
  · simp only [abs_zero]; positivity
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [CharP.cast_eq_zero, zero_mul, abs_zero]; positivity
    · rw [abs_mul, abs_pow, Nat.abs_cast]
      have h1 := pow_abs_le_factorial_mul_exp x (m - 1)
      have e : (m + 1).factorial = (m + 1) * (m * (m - 1).factorial) := by
        rw [Nat.factorial_succ]
        congr 1
        conv_lhs => rw [show m = (m - 1) + 1 by omega]
        rw [Nat.factorial_succ, show m - 1 + 1 = m by omega]
      have e' : ((m + 1).factorial : ℝ) = (m + 1) * (m * (m - 1).factorial) := by
        exact_mod_cast e
      rw [e', one_mul]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hfac : (0 : ℝ) ≤ (m - 1).factorial := Nat.cast_nonneg _
      have hex := Real.exp_pos |x|
      calc (m : ℝ) * |x| ^ (m - 1) ≤ m * ((m - 1).factorial * Real.exp |x|) :=
            mul_le_mul_of_nonneg_left h1 hm0
        _ ≤ (m + 1) * (m * (m - 1).factorial) * Real.exp |x| := by
            nlinarith [mul_nonneg (mul_nonneg hm0 hfac) hex.le]

omit hW in
lemma exp_affine_le {c d t T x : ℝ} (ht : t ∈ Icc 0 T) :
    Real.exp (c * x + d * t) ≤ Real.exp (|d| * T) * Real.exp (|c| * |x|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : c * x ≤ |c| * |x| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : d * t ≤ |d| * T := by
    calc d * t ≤ |d| * t := mul_le_mul_of_nonneg_right (le_abs_self d) ht.1
      _ ≤ |d| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg d)
  linarith

omit hW in
/-- `A exp(c x + d t)` has moderate growth on `[0, T]`. -/
theorem expGrowth_exp (A c d T : ℝ) :
    ExpGrowth (fun t x => A * Real.exp (c * x + d * t)) T
      (|A| * (1 + |c| + |d|) * Real.exp (|d| * T)) |c| := by
  have hb : ∀ k : ℝ, |k| ≤ 1 + |c| + |d| → ∀ t ∈ Icc 0 T, ∀ x,
      |k * (A * Real.exp (c * x + d * t))| ≤
        |A| * (1 + |c| + |d|) * Real.exp (|d| * T) * Real.exp (|c| * |x|) := by
    intro k hk t ht x
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h := exp_affine_le (c := c) (d := d) (x := x) ht
    calc |k| * (|A| * Real.exp (c * x + d * t))
        ≤ (1 + |c| + |d|) * (|A| * (Real.exp (|d| * T) * Real.exp (|c| * |x|))) := by
          gcongr
      _ = _ := by ring
  refine ExpGrowth.of_deriv (gt := fun t x => d * (A * Real.exp (c * x + d * t)))
    (gx := fun t x => c * (A * Real.exp (c * x + d * t))) (abs_nonneg c) (by fun_prop)
    (fun t x => ?_) (fun t x => ?_) (fun t ht x => ?_) (fun t ht x => hb d (by
      linarith [abs_nonneg c]) t ht x) (fun t ht x => hb c (by linarith [abs_nonneg d]) t ht x)
  · have := (((hasDerivAt_id t).const_mul d).const_add (c * x)).exp.const_mul A
    convert this using 1; simp; ring
  · have := (((hasDerivAt_id x).const_mul c).add_const (d * t)).exp.const_mul A
    convert this using 1; simp; ring
  · have := hb 1 (by rw [abs_one]; linarith [abs_nonneg c, abs_nonneg d]) t ht x
    simpa using this

end Gardiner.Ito
