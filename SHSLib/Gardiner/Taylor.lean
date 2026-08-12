/-
Second order Taylor expansion with a *uniform* remainder estimate, corresponding to
(3.4.10) and (3.4.11) of Gardiner, §3.4.1.
-/
import SHSLib.Gardiner.Basic

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-- Every vector of `ℝⁿ` is the sum of its components times the standard basis vectors. -/
lemma sum_single_eq (v : Sp n) : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
  have := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v
  simpa using this

/-- A continuous linear functional on `ℝⁿ` is determined by its values on the standard
basis: this is the coordinate expansion used implicitly throughout §3.4.1. -/
lemma clm_apply_eq_sum (φ : Sp n →L[ℝ] ℝ) (v : Sp n) :
    φ v = ∑ i, φ (EuclideanSpace.single i (1 : ℝ)) * v i := by
  conv_lhs => rw [← sum_single_eq v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  simp [mul_comm]

/-- The differential of `f` at `z` expressed through the partial derivatives `pd f i z`. -/
lemma fderiv_apply_eq_sum (f : Sp n → ℝ) (z v : Sp n) :
    fderiv ℝ f z v = ∑ i, pd f i z * v i := clm_apply_eq_sum _ v

/-- The `i`-th partial derivative as the differential applied to a basis vector. -/
lemma pd_eq (f : Sp n → ℝ) (i : Fin n) (z : Sp n) :
    pd f i z = fderiv ℝ f z (EuclideanSpace.single i (1 : ℝ)) := rfl

/-- For a `C²` function the derivative map `fderiv ℝ f` is differentiable. -/
lemma differentiable_fderiv (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fderiv ℝ f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

/-- For a `C²` function, the second partial derivatives are the components of the
second differential. -/
lemma pd2_eq (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin n) (z : Sp n) :
    pd2 f i j z =
      (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i (1 : ℝ)))
        (EuclideanSpace.single j (1 : ℝ)) := by
  set L := ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ)) with hL
  have hF : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    (differentiable_fderiv f hf z).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => pd f j w) (L.comp (fderiv ℝ (fderiv ℝ f) z)) z :=
    (L.hasFDerivAt).comp z hF
  rw [pd2, pd, hcomp.fderiv]
  rfl

lemma sub_apply (x z : Sp n) (i : Fin n) : (x - z) i = x i - z i := rfl

/-- Coordinate-free form of the Taylor remainder (3.4.10). -/
lemma taylorRem_eq (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) (z x : Sp n) :
    taylorRem f z x = f x - f z - fderiv ℝ f z (x - z)
      - (1 / 2) * (fderiv ℝ (fderiv ℝ f) z (x - z)) (x - z) := by
  have h1 : fderiv ℝ f z (x - z) = ∑ i, pd f i z * (x i - z i) := by
    rw [fderiv_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_apply]
  have h2 : (fderiv ℝ (fderiv ℝ f) z (x - z)) (x - z)
      = ∑ i, ∑ j, pd2 f i j z * (x i - z i) * (x j - z j) := by
    have hTv : fderiv ℝ (fderiv ℝ f) z (x - z)
        = ∑ i, (x - z) i • (fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← sum_single_eq (x - z)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    rw [hTv, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul,
      clm_apply_eq_sum ((fderiv ℝ (fderiv ℝ f) z) (EuclideanSpace.single i (1 : ℝ))) (x - z),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pd2_eq f hf i j z]
    simp only [sub_apply]
    ring
  rw [taylorRem, h1, h2]

/-- **Uniform second order Taylor estimate**, (3.4.10)–(3.4.11).  For a compactly
supported `C²` function the remainder `R(x,z) = taylorRem f z x / |x - z|²`
tends to `0` as `|x - z| → 0`, *uniformly* in `z`. -/
theorem uniform_taylorRem (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ z x : Sp n, ‖x - z‖ < ε → |taylorRem f z x| ≤ δ * ‖x - z‖ ^ 2 := by
  have hg1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hgdiff : Differentiable ℝ (fderiv ℝ f) := hg1.differentiable (by norm_num)
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg'cont : Continuous (fderiv ℝ (fderiv ℝ f)) := hg1.continuous_fderiv (by norm_num)
  have hg'supp : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := (hsupp.fderiv ℝ).fderiv ℝ
  have huc : @UniformContinuous (Sp n) (Sp n →L[ℝ] Sp n →L[ℝ] ℝ)
      PseudoMetricSpace.toUniformSpace PseudoMetricSpace.toUniformSpace
      (fderiv ℝ (fderiv ℝ f)) :=
    hg'cont.uniformContinuous_of_tendsto_cocompact hg'supp.is_zero_at_infty
  obtain ⟨ε, hε, hb⟩ : ∃ ε > 0, ∀ a b : Sp n, dist a b < ε →
      ‖fderiv ℝ (fderiv ℝ f) a - fderiv ℝ (fderiv ℝ f) b‖ ≤ δ := by
    obtain ⟨ε, hε, h⟩ := Metric.uniformContinuous_iff.mp huc δ hδ
    refine ⟨ε, hε, fun a b hab => ?_⟩
    exact le_of_lt (by simpa [dist_eq_norm] using h hab)
  refine ⟨ε, hε, fun z x hx => ?_⟩
  set B := fderiv ℝ (fderiv ℝ f) z with hB
  set r := ‖x - z‖ with hr
  set s := Metric.closedBall z r with hs
  have hconv : Convex ℝ s := convex_closedBall z r
  have hzs : z ∈ s := Metric.mem_closedBall_self (norm_nonneg _)
  have hxs : x ∈ s := by simp [hs, Metric.mem_closedBall, dist_eq_norm, hr]
  have hsbound : ∀ w ∈ s, ‖fderiv ℝ (fderiv ℝ f) w - B‖ ≤ δ := by
    intro w hw
    refine hb w z ?_
    have : dist w z ≤ r := by simpa [hs, Metric.mem_closedBall] using hw
    exact lt_of_le_of_lt this hx
  -- symmetry of the second derivative
  have hsym : ∀ v w : Sp n, (B v) w = (B w) v :=
    second_derivative_symmetric (f := f) (f' := fderiv ℝ f) (f'' := B)
      (fun y => (hfdiff y).hasFDerivAt) (hgdiff z).hasFDerivAt
  -- the first-order remainder of the derivative
  set u : Sp n → (Sp n →L[ℝ] ℝ) := fun w => fderiv ℝ f w - fderiv ℝ f z - B (w - z) with hu
  have hBsub : ∀ w : Sp n, HasFDerivAt (fun w : Sp n => B (w - z)) B w := by
    intro w
    have h1 : HasFDerivAt (fun w : Sp n => w - z) (ContinuousLinearMap.id ℝ (Sp n)) w :=
      (hasFDerivAt_id w).sub_const z
    have h2 := (B.hasFDerivAt (x := w - z)).comp w h1
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hud : ∀ w : Sp n, HasFDerivAt u (fderiv ℝ (fderiv ℝ f) w - B) w := by
    intro w
    exact (((hgdiff w).hasFDerivAt.sub_const (fderiv ℝ f z)).sub (hBsub w))
  have huz : u z = 0 := by simp [hu]
  have hubound : ∀ w ∈ s, ‖u w‖ ≤ δ * r := by
    intro w hw
    have hmvt : ‖u w - u z‖ ≤ δ * ‖w - z‖ :=
      hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y _ => (hud y).hasFDerivWithinAt) hsbound hzs hw
    rw [huz, sub_zero] at hmvt
    refine hmvt.trans (by
      have : ‖w - z‖ ≤ r := by simpa [hs, Metric.mem_closedBall, dist_eq_norm] using hw
      exact mul_le_mul_of_nonneg_left this hδ.le)
  -- the second-order remainder itself
  set h : Sp n → ℝ := fun w =>
    f w - f z - (fderiv ℝ f z) (w - z) - (1 / 2) * ((B (w - z)) (w - z)) with hh
  have hquad : ∀ w : Sp n, HasFDerivAt (fun w : Sp n => (B (w - z)) (w - z))
      ((B (w - z)).comp (ContinuousLinearMap.id ℝ (Sp n)) + B.flip (w - z)) w := by
    intro w
    exact (hBsub w).clm_apply ((hasFDerivAt_id w).sub_const z)
  have hd : ∀ w : Sp n, HasFDerivAt h (u w) w := by
    intro w
    have h1 : HasFDerivAt (fun w : Sp n => f w - f z - (fderiv ℝ f z) (w - z))
        (fderiv ℝ f w - fderiv ℝ f z) w := by
      have ha : HasFDerivAt (fun w : Sp n => f w - f z) (fderiv ℝ f w) w :=
        (hfdiff w).hasFDerivAt.sub_const (f z)
      have hbb : HasFDerivAt (fun w : Sp n => (fderiv ℝ f z) (w - z)) (fderiv ℝ f z) w := by
        have h1 : HasFDerivAt (fun w : Sp n => w - z) (ContinuousLinearMap.id ℝ (Sp n)) w :=
          (hasFDerivAt_id w).sub_const z
        have h2 := ((fderiv ℝ f z).hasFDerivAt (x := w - z)).comp w h1
        rw [ContinuousLinearMap.comp_id] at h2
        exact h2
      exact ha.sub hbb
    have h2 := h1.sub (((hquad w).const_mul (1 / 2 : ℝ)))
    refine h2.congr_fderiv ?_
    ext v
    have := hsym (w - z) v
    simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.flip_apply,
      smul_eq_mul, hu]
    rw [this]
    ring
  have hhz : h z = 0 := by simp [hh]
  have hfinal : ‖h x - h z‖ ≤ (δ * r) * ‖x - z‖ :=
    hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y _ => (hd y).hasFDerivWithinAt) hubound hzs hxs
  rw [hhz, sub_zero] at hfinal
  have hval : h x = taylorRem f z x := by
    rw [taylorRem_eq f hf z x, hh]
  rw [hval] at hfinal
  calc |taylorRem f z x| = ‖taylorRem f z x‖ := rfl
    _ ≤ (δ * r) * ‖x - z‖ := hfinal
    _ = δ * ‖x - z‖ ^ 2 := by rw [hr]; ring

/-! ### Continuity of the objects entering the integrals -/

lemma continuous_pd (f : Sp n → ℝ) (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (pd f i) := by
  have : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  exact this.clm_apply continuous_const

/-- A partial derivative of a `C²` function is `C¹`. -/
lemma contDiff_pd (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) (j : Fin n) : ContDiff ℝ 1 (pd f j) := by
  have h : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff.comp h

lemma continuous_pd2 (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) (i j : Fin n) :
    Continuous (pd2 f i j) :=
  continuous_pd _ (contDiff_pd f hf j) i

lemma continuous_taylorPoly (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) :
    Continuous (fun q : Sp n × Sp n => taylorPoly f q.2 q.1) := by
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hc : ∀ i : Fin n, Continuous fun q : Sp n × Sp n => (q.1 i - q.2 i) := fun i =>
    ((PiLp.continuous_apply 2 (fun _ => ℝ) i).comp continuous_fst).sub
      ((PiLp.continuous_apply 2 (fun _ => ℝ) i).comp continuous_snd)
  unfold taylorPoly
  refine Continuous.add (continuous_finset_sum _ fun i _ => ?_)
    (Continuous.mul continuous_const (continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => ?_))
  · exact ((continuous_pd f h1 i).comp continuous_snd).mul (hc i)
  · exact (((continuous_pd2 f hf i j).comp continuous_snd).mul (hc i)).mul (hc j)

lemma continuous_taylorRem (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) :
    Continuous (fun q : Sp n × Sp n => taylorRem f q.2 q.1) := by
  have : (fun q : Sp n × Sp n => taylorRem f q.2 q.1)
      = fun q : Sp n × Sp n => (f q.1 - f q.2) - taylorPoly f q.2 q.1 := by
    funext q; have := taylor_decomp f q.2 q.1; linarith [this]
  rw [this]
  exact ((hf.continuous.comp continuous_fst).sub (hf.continuous.comp continuous_snd)).sub
    (continuous_taylorPoly f hf)

end Gardiner
