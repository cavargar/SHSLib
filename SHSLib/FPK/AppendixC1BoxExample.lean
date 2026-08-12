/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A worked instance of Eq. (46) on a box

`GSHS.appendixC1_eq46_box` proves Eq. (46) of Appendix C.1 of Bect (2010) on a box, under
the smoothness and integrability hypotheses of the paper.  This file discharges all of
those hypotheses in a concrete case — no noise (`r = 0`, so the model is a deterministic
flow), constant drift `f₀ ≡ c`, density `p ≡ 1` and the test function
`φ(y) = exp(y¹ + ⋯ + yⁿ⁺¹)` — thereby showing that the hypotheses of the general theorem
are satisfiable and recovering the divergence theorem for the vector field `φ c`:

  `∫_{[a,b]} Σᵢ cⁱ φ = flux of φ c through the faces of the box`.
-/
import SHSLib.FPK.AppendixC1Box

open MeasureTheory Set

noncomputable section

namespace GSHS.BoxExample

variable {n : ℕ}

/-- The linear form `y ↦ Σᵢ yⁱ`. -/
def sumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i

theorem sumCLM_apply (y : Fin n → ℝ) : sumCLM n y = ∑ i, y i := by
  simp [sumCLM, ContinuousLinearMap.sum_apply]

/-- The test function `φ(y) = exp(y¹ + ⋯ + yⁿ)`; all its partial derivatives, of every
order, are equal to `φ` itself. -/
def expSum (y : Fin n → ℝ) : ℝ := Real.exp (∑ i, y i)

theorem expSum_continuous : Continuous (expSum (n := n)) := by
  unfold expSum
  fun_prop

theorem hasFDerivAt_expSum (x : Fin n → ℝ) :
    HasFDerivAt (expSum (n := n)) (expSum x • sumCLM n) x := by
  have hL : HasFDerivAt (fun y : Fin n → ℝ => sumCLM n y) (sumCLM n) x :=
    (sumCLM n).hasFDerivAt
  have hcomp := (Real.hasDerivAt_exp (sumCLM n x)).comp_hasFDerivAt x hL
  have hfun : (Real.exp ∘ (sumCLM n : (Fin n → ℝ) → ℝ)) = expSum := by
    funext y; simp only [Function.comp_apply, expSum, sumCLM_apply]
  rw [hfun] at hcomp
  have hval : Real.exp (sumCLM n x) = expSum x := by rw [expSum, sumCLM_apply]
  rwa [hval] at hcomp

theorem hasPDerivAt_expSum (i : Fin n) (x : Fin n → ℝ) :
    HasPDerivAt (expSum (n := n)) i x (expSum x) := by
  classical
  have hsum : ∀ t : ℝ, ∑ k, Function.update x i t k = (∑ k, x k) - x i + t := by
    intro t
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    have h : ∑ k ∈ Finset.univ \ {i}, x k = (∑ k, x k) - x i := by
      rw [Finset.sum_sdiff_eq_sub (by simp)]
      simp
    rw [h]; ring
  have hfun : (fun t : ℝ => expSum (Function.update x i t))
      = fun t : ℝ => Real.exp ((∑ k, x k) - x i + t) := by
    funext t; rw [expSum, hsum t]
  have hd : HasDerivAt (fun t : ℝ => Real.exp ((∑ k, x k) - x i + t))
      (Real.exp ((∑ k, x k) - x i + x i)) (x i) := by
    have h1 : HasDerivAt (fun t : ℝ => (∑ k, x k) - x i + t) 1 (x i) := by
      simpa using (hasDerivAt_id (x i)).const_add ((∑ k, x k) - x i)
    simpa using h1.exp
  have hval : Real.exp ((∑ k, x k) - x i + x i) = expSum x := by
    rw [expSum]; ring_nf
  rw [HasPDerivAt, hfun]
  rw [hval] at hd
  exact hd

/-! ### The instance -/

section

variable (c : Fin (n + 1) → ℝ)

/-- The (empty) family of noise vector fields: the model has no noise. -/
def noNoise : Fin 0 → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun l => l.elim0

/-- The current of the model: with `p ≡ 1`, `f₀ ≡ c` and no noise, `j ≡ c`. -/
theorem currentField_const (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    currentField (fun _ => c) (fun _ _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) y i = c i := by
  simp [currentField]

/-- **Eq. (46) on a box, worked instance.**  All the hypotheses of
`GSHS.appendixC1_eq46_box` are met by the deterministic model with constant drift `c`,
unit density and test function `φ(y) = exp(Σ yⁱ)`; since the formal adjoint `F p` and
the noise fluxes vanish, Eq. (46) becomes the divergence theorem for the field `φ c`. -/
theorem eq46_expSum (a b : Fin (n + 1) → ℝ) (hab : a ≤ b) :
    ∫ x in Icc a b, (∑ i, c i * expSum x)
      = boxFlux a b (fun y i => expSum y * c i) := by
  classical
  set V' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    fun x => (expSum x • sumCLM (n + 1)).smulRight c with hV'def
  have hVtrace : ∀ x, (∑ i, (V' x (Pi.single i 1)) i) = ∑ i, c i * expSum x := by
    intro x
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hV'def, sumCLM_apply]
    ring
  have hfield : (fun (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) =>
        expSum y * currentField (fun _ => c) (fun _ _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) y i)
      = fun y => expSum y • c := by
    funext y i
    rw [currentField_const]
    simp [smul_eq_mul]
  have hV : ∀ x, HasFDerivAt (fun (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) =>
      expSum y * currentField (fun _ => c) (fun _ _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) y i)
      (V' x) x := by
    intro x
    rw [hfield]
    exact (hasFDerivAt_expSum x).smul_const c
  have hcontTrace : Continuous fun x : Fin (n + 1) → ℝ => ∑ i, c i * expSum x := by
    have : Continuous fun x : Fin (n + 1) → ℝ => expSum x := expSum_continuous
    fun_prop
  have hintV : IntegrableOn (fun x => ∑ i, (V' x (Pi.single i 1)) i) (Icc a b) := by
    have hcont : Continuous fun x : Fin (n + 1) → ℝ => ∑ i, (V' x (Pi.single i 1)) i := by
      have : (fun x : Fin (n + 1) → ℝ => ∑ i, (V' x (Pi.single i 1)) i)
          = fun x => ∑ i, c i * expSum x := funext hVtrace
      rw [this]; exact hcontTrace
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hFpzero : formalAdjointVal (n := n + 1) (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
      = (0 : ℝ) := by
    simp [formalAdjointVal]
  have hintFp : IntegrableOn (fun x : Fin (n + 1) → ℝ =>
      expSum x * formalAdjointVal (n := n + 1) (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) (Icc a b) := by
    have : (fun x : Fin (n + 1) → ℝ =>
        expSum x * formalAdjointVal (n := n + 1) (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
        = fun _ => (0 : ℝ) := by
      funext x; rw [hFpzero, mul_zero]
    rw [this]
    exact integrableOn_zero
  have key := appendixC1_eq46_box (f := noNoise) (f0 := fun _ => c)
    (p := fun _ => (1 : ℝ)) (phi := expSum) (dp := fun _ _ => (0 : ℝ))
    (df := fun _ l => l.elim0) (gphi := fun y _ => expSum y)
    (ddphi := fun y _ _ => expSum y) (gap := fun _ _ _ => (0 : ℝ))
    (dfp := fun _ _ => (0 : ℝ)) (ddgap := fun _ _ _ => (0 : ℝ))
    (V' := V') (W' := fun l => l.elim0)
    a b hab
    (fun x j => by simpa [HasPDerivAt] using hasDerivAt_const (x j) (1 : ℝ))
    (fun _ l => l.elim0)
    (fun x i => hasPDerivAt_expSum i x)
    (fun x i j => hasPDerivAt_expSum j x)
    (fun x i j => by
      simpa [HasPDerivAt, diffusionMatrix, noNoise] using hasDerivAt_const (x j) (0 : ℝ))
    (fun x i => by simpa [HasPDerivAt] using hasDerivAt_const (x i) (c i * 1))
    (fun x i j => by simpa [HasPDerivAt] using hasDerivAt_const (x i) (0 : ℝ))
    hV (fun l => l.elim0) hintV hintFp (fun l => l.elim0)
  -- simplify the two sides
  have hgenVal : ∀ x : Fin (n + 1) → ℝ,
      generatorVal (fun _ => c) noNoise (fun y _ => expSum y) (fun y _ _ => expSum y) x
        * (1 : ℝ) = ∑ i, c i * expSum x := by
    intro x
    simp [generatorVal, diffusionMatrix, noNoise]
  have hlhs : ∫ x in Icc a b,
      generatorVal (fun _ => c) noNoise (fun y _ => expSum y) (fun y _ _ => expSum y) x
        * (1 : ℝ) = ∫ x in Icc a b, (∑ i, c i * expSum x) := by
    exact setIntegral_congr_fun measurableSet_Icc fun x _ => hgenVal x
  have hrhs1 : (∫ x in Icc a b,
      expSum x * formalAdjointVal (n := n + 1) (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) = 0 := by
    have : (fun x : Fin (n + 1) → ℝ =>
        expSum x * formalAdjointVal (n := n + 1) (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
        = fun _ => (0 : ℝ) := by
      funext x; rw [hFpzero, mul_zero]
    rw [this]
    simp
  rw [hlhs, hrhs1] at key
  rw [key, hfield]
  norm_num
  rfl

end

end GSHS.BoxExample
