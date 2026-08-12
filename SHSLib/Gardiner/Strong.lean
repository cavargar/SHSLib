/-
Integration by parts (3.4.19) and the differential Chapman–Kolmogorov equation
(3.4.22) of Gardiner, §3.4.1.

The process is assumed to take place on all of `ℝⁿ`, so that the surface terms of
(3.4.19) are absent, as in the last paragraph of §3.4.1.
-/
import SHSLib.Gardiner.WeakForm

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-! ### Integration by parts on `ℝⁿ` -/

/-- The integral of a partial derivative of a compactly supported `C¹` function
vanishes. -/
theorem integral_pd_eq_zero (h : Sp n → ℝ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h)
    (i : Fin n) : ∫ z, pd h i z = 0 := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hh (by simp)
  have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Sp n)))
      (f := fun _ : Sp n => (1 : ℝ)) (g := h) (LipschitzWith.const 1) hD hs
      (EuclideanSpace.single i (1 : ℝ))
  have hc : ∀ x v : Sp n, lineDeriv ℝ (fun _ : Sp n => (1 : ℝ)) x v = 0 := by
    intro x v; simp [lineDeriv]
  simp only [hc, zero_mul, integral_zero, mul_one] at key
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hL : ∀ x : Sp n, lineDeriv ℝ h x (-(EuclideanSpace.single i (1 : ℝ))) = -pd h i x := by
    intro x
    rw [(hdiff x).lineDeriv_eq_fderiv]
    simp [pd]
  simp_rw [hL] at key
  rw [integral_neg] at key
  linarith [key]

/-- Leibniz rule for the partial derivatives `pd`. -/
lemma pd_mul (u v : Sp n → ℝ) (i : Fin n) (z : Sp n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    pd (fun w => u w * v w) i z = pd u i z * v z + u z * pd v i z := by
  have hd : HasFDerivAt (fun w => u w * v w)
      (u z • fderiv ℝ v z + v z • fderiv ℝ u z) z := hu.hasFDerivAt.mul hv.hasFDerivAt
  rw [pd, hd.fderiv]
  simp only [pd, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  ring

/-- **Integration by parts**, the step leading to (3.4.19). -/
theorem integral_pd_mul_eq_neg (u v : Sp n → ℝ) (i : Fin n)
    (hu : ContDiff ℝ 1 u) (hus : HasCompactSupport u) (hv : ContDiff ℝ 1 v) :
    ∫ z, pd u i z * v z = -∫ z, u z * pd v i z := by
  have hudiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hvdiff : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hprodC : ContDiff ℝ 1 (fun w => u w * v w) := hu.mul hv
  have hprodS : HasCompactSupport (fun w => u w * v w) := hus.mul_right
  have hzero := integral_pd_eq_zero (fun w => u w * v w) hprodC hprodS i
  have hcongr : ∀ z, pd (fun w => u w * v w) i z = pd u i z * v z + u z * pd v i z := fun z =>
    pd_mul u v i z (hudiff z) (hvdiff z)
  simp_rw [hcongr] at hzero
  have hi1 : Integrable (fun z => pd u i z * v z) :=
    (Continuous.integrable_of_hasCompactSupport
      ((continuous_pd u hu i).mul hv.continuous)
      ((hasCompactSupport_pd hus i).mul_right))
  have hi2 : Integrable (fun z => u z * pd v i z) :=
    (Continuous.integrable_of_hasCompactSupport
      (hu.continuous.mul (continuous_pd v hv i))
      (hus.mul_right))
  rw [MeasureTheory.integral_add hi1 hi2] at hzero
  linarith [hzero]

/-- Symmetry of second partial derivatives (Clairaut/Schwarz). -/
theorem pd2_symm (g : Sp n → ℝ) (hg : ContDiff ℝ 2 g) (i j : Fin n) (z : Sp n) :
    pd2 g i j z = pd2 g j i z := by
  have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hsym := second_derivative_symmetric (f := g) (f' := fderiv ℝ g)
    (f'' := fderiv ℝ (fderiv ℝ g) z) (fun y => (hgdiff y).hasFDerivAt)
    ((differentiable_fderiv g hg z).hasFDerivAt)
  rw [pd2_eq g hg i j z, pd2_eq g hg j i z, hsym]

/-! ### The differential Chapman–Kolmogorov equation -/

/-- The right-hand side of the differential Chapman–Kolmogorov equation (3.4.22). -/
def ckRHS (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (W : Sp n → Sp n → ℝ) (t : ℝ) (z : Sp n) : ℝ :=
  -(∑ i, pd (fun w => A w i * p t w) i z)
    + (1 / 2) * (∑ i, ∑ j, pd2 (fun w => B w i j * p t w) i j z)
    + ∫ x, (W z x * p t x - W x z * p t z)

/-- (3.4.19): the drift/diffusion term (3.4.13), integrated by parts. -/
theorem driftDiffTerm_integrationByParts
    (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (t : ℝ)
    (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hAp : ∀ i, ContDiff ℝ 1 (fun w => A w i * p t w))
    (hBp : ∀ i j, ContDiff ℝ 2 (fun w => B w i j * p t w)) :
    driftDiffTerm p A B f t
      = ∫ z, f z * (-(∑ i, pd (fun w => A w i * p t w) i z)
          + (1 / 2) * (∑ i, ∑ j, pd2 (fun w => B w i j * p t w) i j z)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  set G : Fin n → Sp n → ℝ := fun i w => A w i * p t w with hG
  set H : Fin n → Fin n → Sp n → ℝ := fun i j w => B w i j * p t w with hH
  -- integrability of all the pieces (all are continuous with compact support)
  have hI1 : ∀ i, Integrable (fun z => pd f i z * G i z) := fun i =>
    Continuous.integrable_of_hasCompactSupport
      ((continuous_pd f hf1 i).mul (hAp i).continuous)
      ((hasCompactSupport_pd hfs i).mul_right)
  have hI2 : ∀ i j, Integrable (fun z => pd2 f i j z * H i j z) := fun i j =>
    Continuous.integrable_of_hasCompactSupport
      ((continuous_pd2 f hf i j).mul (hBp i j).continuous)
      ((hasCompactSupport_pd2 hfs i j).mul_right)
  have hJ1 : ∀ i, Integrable (fun z => -(f z * pd (G i) i z)) := fun i =>
    Continuous.integrable_of_hasCompactSupport
      ((hf.continuous.mul (continuous_pd (G i) (hAp i) i)).neg)
      (((hfs.mul_right).neg))
  have hJ2 : ∀ i j, Integrable (fun z => f z * pd2 (H i j) i j z) := fun i j =>
    Continuous.integrable_of_hasCompactSupport
      (hf.continuous.mul (continuous_pd2 (H i j) (hBp i j) i j))
      (hfs.mul_right)
  -- integration by parts, once for the drift term and twice for the diffusion term
  have key1 : ∀ i, (∫ z, pd f i z * G i z) = ∫ z, -(f z * pd (G i) i z) := by
    intro i
    rw [integral_pd_mul_eq_neg f (G i) i hf1 hfs (hAp i), MeasureTheory.integral_neg]
  have key2 : ∀ i j, (∫ z, pd2 f i j z * H i j z) = ∫ z, f z * pd2 (H i j) i j z := by
    intro i j
    have hHC : ContDiff ℝ 2 (H i j) := hBp i j
    have hA1 : (∫ z, pd2 f i j z * H i j z)
        = -∫ z, pd f j z * pd (H i j) i z :=
      integral_pd_mul_eq_neg (pd f j) (H i j) i (contDiff_pd f hf j)
        (hasCompactSupport_pd hfs j) (hHC.of_le (by norm_num))
    have hA2 : (∫ z, pd f j z * pd (H i j) i z) = -∫ z, f z * pd2 (H i j) j i z :=
      integral_pd_mul_eq_neg f (pd (H i j) i) j hf1 hfs (contDiff_pd (H i j) hHC i)
    rw [hA1, hA2, neg_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show f z * pd2 (H i j) j i z = f z * pd2 (H i j) i j z
    rw [pd2_symm (H i j) hHC j i z]
  -- expand both sides into sums of integrals
  have hLHS : driftDiffTerm p A B f t
      = (∑ i, ∫ z, pd f i z * G i z)
        + (1 / 2) * ∑ i, ∑ j, ∫ z, pd2 f i j z * H i j z := by
    have hcongr : ∀ z, (∑ i, A z i * pd f i z + (1 / 2) * ∑ i, ∑ j, B z i j * pd2 f i j z) * p t z
        = (∑ i, pd f i z * G i z) + (1 / 2) * ∑ i, ∑ j, pd2 f i j z * H i j z := by
      intro z
      have e1 : (∑ i, A z i * pd f i z) * p t z = ∑ i, pd f i z * G i z := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by simp only [hG]; ring
      have e2 : (∑ i, ∑ j, B z i j * pd2 f i j z) * p t z
          = ∑ i, ∑ j, pd2 f i j z * H i j z := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by simp only [hH]; ring
      calc (∑ i, A z i * pd f i z + (1 / 2) * ∑ i, ∑ j, B z i j * pd2 f i j z) * p t z
          = (∑ i, A z i * pd f i z) * p t z
            + (1 / 2) * ((∑ i, ∑ j, B z i j * pd2 f i j z) * p t z) := by ring
        _ = (∑ i, pd f i z * G i z) + (1 / 2) * ∑ i, ∑ j, pd2 f i j z * H i j z := by
            rw [e1, e2]
    rw [driftDiffTerm, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
      MeasureTheory.integral_add (MeasureTheory.integrable_finset_sum _ fun i _ => hI1 i)
        ((MeasureTheory.integrable_finset_sum _ fun i _ =>
          MeasureTheory.integrable_finset_sum _ fun j _ => hI2 i j).const_mul _),
      MeasureTheory.integral_finset_sum _ (fun i _ => hI1 i),
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _
        (fun i _ => MeasureTheory.integrable_finset_sum _ fun j _ => hI2 i j)]
    refine congrArg (fun s => (∑ i, ∫ z, pd f i z * G i z) + (1 / 2 : ℝ) * s) ?_
    exact Finset.sum_congr rfl fun i _ =>
      MeasureTheory.integral_finset_sum _ fun j _ => hI2 i j
  have hRHS : (∫ z, f z * (-(∑ i, pd (G i) i z) + (1 / 2) * (∑ i, ∑ j, pd2 (H i j) i j z)))
      = (∑ i, ∫ z, -(f z * pd (G i) i z))
        + (1 / 2) * ∑ i, ∑ j, ∫ z, f z * pd2 (H i j) i j z := by
    have hcongr : ∀ z, f z * (-(∑ i, pd (G i) i z) + (1 / 2) * (∑ i, ∑ j, pd2 (H i j) i j z))
        = (∑ i, -(f z * pd (G i) i z)) + (1 / 2) * ∑ i, ∑ j, f z * pd2 (H i j) i j z := by
      intro z
      have e1 : f z * (-(∑ i, pd (G i) i z)) = ∑ i, -(f z * pd (G i) i z) := by
        rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      have e2 : f z * (∑ i, ∑ j, pd2 (H i j) i j z)
          = ∑ i, ∑ j, f z * pd2 (H i j) i j z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
      calc f z * (-(∑ i, pd (G i) i z) + (1 / 2) * (∑ i, ∑ j, pd2 (H i j) i j z))
          = f z * (-(∑ i, pd (G i) i z))
            + (1 / 2) * (f z * (∑ i, ∑ j, pd2 (H i j) i j z)) := by ring
        _ = (∑ i, -(f z * pd (G i) i z)) + (1 / 2) * ∑ i, ∑ j, f z * pd2 (H i j) i j z := by
            rw [e1, e2]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
      MeasureTheory.integral_add (MeasureTheory.integrable_finset_sum _ fun i _ => hJ1 i)
        ((MeasureTheory.integrable_finset_sum _ fun i _ =>
          MeasureTheory.integrable_finset_sum _ fun j _ => hJ2 i j).const_mul _),
      MeasureTheory.integral_finset_sum _ (fun i _ => hJ1 i),
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _
        (fun i _ => MeasureTheory.integrable_finset_sum _ fun j _ => hJ2 i j)]
    refine congrArg (fun s => (∑ i, ∫ z, -(f z * pd (G i) i z)) + (1 / 2 : ℝ) * s) ?_
    exact Finset.sum_congr rfl fun i _ =>
      MeasureTheory.integral_finset_sum _ fun j _ => hJ2 i j
  rw [hLHS, hRHS]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => key1 i
  · exact congrArg (fun s => (1 / 2 : ℝ) * s)
      (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key2 i j)

/-- **The differential Chapman–Kolmogorov equation**, (3.4.22).

`dtp` stands for `∂_t p(z, t | y, t')`.  The hypothesis `hweak` is the weak form
(3.4.16) of the equation (with the principal value integral written as an ordinary
integral, as Gardiner does from (3.4.18) onwards); the conclusion is the pointwise
equation (3.4.22), valid almost everywhere. -/
theorem differentialCK
    (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (W : Sp n → Sp n → ℝ) (t : ℝ) (dtp : Sp n → ℝ)
    (hAp : ∀ i, ContDiff ℝ 1 (fun w => A w i * p t w))
    (hBp : ∀ i j, ContDiff ℝ 2 (fun w => B w i j * p t w))
    (hjump : LocallyIntegrable (fun z => ∫ x, (W z x * p t x - W x z * p t z)))
    (hdtp : LocallyIntegrable dtp)
    (hweak : ∀ f : Sp n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∫ z, f z * dtp z
        = driftDiffTerm p A B f t + ∫ z, f z * (∫ x, (W z x * p t x - W x z * p t z))) :
    ∀ᵐ z : Sp n, dtp z = ckRHS p A B W t z := by
  set jmp : Sp n → ℝ := fun z => ∫ x, (W z x * p t x - W x z * p t z) with hjmp
  set R : Sp n → ℝ := fun z => -(∑ i, pd (fun w => A w i * p t w) i z)
    + (1 / 2) * (∑ i, ∑ j, pd2 (fun w => B w i j * p t w) i j z) with hR
  have hRcont : Continuous R := by
    refine Continuous.add (continuous_finset_sum _ fun i _ =>
      continuous_pd _ (hAp i) i).neg ?_
    exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => continuous_pd2 _ (hBp i j) i j)
  have hckloc : LocallyIntegrable (ckRHS p A B W t) := hRcont.locallyIntegrable.add hjump
  have hloc : LocallyIntegrable (fun z => dtp z - ckRHS p A B W t z) := hdtp.sub hckloc
  refine (ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_).mono fun z hz => ?_
  · intro g hg hgs
    have hg2 : ContDiff ℝ 2 g := hg.of_le ENat.LEInfty.out
    have hgR : Integrable (fun z => g z * R z) :=
      Continuous.integrable_of_hasCompactSupport (hg.continuous.mul hRcont) hgs.mul_right
    have hgj : Integrable (fun z => g z * jmp z) :=
      hjump.integrable_smul_left_of_hasCompactSupport hg.continuous hgs
    have hgdtp : Integrable (fun z => g z * dtp z) :=
      hdtp.integrable_smul_left_of_hasCompactSupport hg.continuous hgs
    have hgck : Integrable (fun z => g z * ckRHS p A B W t z) :=
      hckloc.integrable_smul_left_of_hasCompactSupport hg.continuous hgs
    have hsplit : (∫ z, g z * ckRHS p A B W t z)
        = (∫ z, g z * R z) + ∫ z, g z * jmp z := by
      rw [← MeasureTheory.integral_add hgR hgj]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show g z * ckRHS p A B W t z = g z * R z + g z * jmp z
      rw [ckRHS]
      ring
    have hIBP := driftDiffTerm_integrationByParts p A B t g hg2 hgs hAp hBp
    have hw := hweak g hg hgs
    have hint : ∀ x : Sp n, g x * (dtp x - ckRHS p A B W t x)
        = g x * dtp x - g x * ckRHS p A B W t x := fun x => by ring
    simp only [smul_eq_mul]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint),
      MeasureTheory.integral_sub hgdtp hgck, hsplit, hw, hIBP]
    ring
  · exact sub_eq_zero.mp hz

end Gardiner
