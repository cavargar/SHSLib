/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 4.2 and Appendix C of Bect (2010): the probability current

Inside one mode of the hybrid state space the continuous variable lives in (an open
subset of) `ℝⁿ`, the diffusion is driven by the vector fields `f₀, f₁, …, f_r`, and the
diffusion matrix is `aⁱʲ = Σ_l f_lⁱ f_lʲ`.  Given a density `p` for the law `μ_t`, the
*probability current* of Eq. (16) is the vector field

  `jⁱ = f₀ⁱ p − ½ Σ_j ∂(aⁱʲ p)/∂zʲ`,

and the *formal adjoint* of the generator, Eq. (21), is

  `F p = −Σ_i ∂(f₀ⁱ p)/∂zⁱ + ½ Σ_{i,j} ∂²(aⁱʲ p)/∂zⁱ∂zʲ`.

This file formalizes the pointwise differential identities of Appendix C.1, which are
the algebraic heart of Proposition 11:

* `GSHS.divergence_current_eq_neg_formalAdjoint` — `F p = −div(j)`, the identity used
  right after Eq. (44);
* `GSHS.current_dot_grad_eq` — Eq. (45): `j·∇φ = div(φ j) + φ F p`;
* `GSHS.generator_mul_density_eq` — Eq. (44): `(Lφ) p = j·∇φ + ½ Σ_l div((f_lφ) p f_l)`,
  the identity which, integrated and combined with the divergence theorem, produces
  Eq. (46).

It also formalizes the measure-theoretic conclusions drawn from Eq. (49) in
Appendices C.2 and C.3:

* `GSHS.forced_intensity_eq_current` and `GSHS.current_nonneg` — Proposition 11(a): on
  the guard set the mean intensity of forced jumps is the outward flow of the
  probability current, and this outward current is nonnegative;
* `GSHS.density_mul_normal_ae_eq_zero` and `GSHS.density_ae_eq_zero_on_pos` —
  Proposition 11(b): the absorbing boundary condition `p_t = 0` on `G⁰`.

Partial derivatives are handled through the predicate `GSHS.HasPDerivAt f i x c`,
"`f` has partial derivative `c` in the direction of the `i`-th coordinate at `x`", and
all differential data (first and second partial derivatives of `p`, of the vector fields
and of the test function) enter the statements as explicit values, so that no global
smoothness assumption is needed.
-/
import Mathlib

open MeasureTheory Set Finset

noncomputable section

namespace GSHS

/-! ## Partial derivatives -/

variable {n : ℕ}

/-- `HasPDerivAt f i x c` means that the function `f` on `ℝⁿ`, viewed as a function of
its `i`-th coordinate with the other coordinates frozen at `x`, has derivative `c` at
`x i`; i.e. `∂f/∂zⁱ (x) = c`. -/
def HasPDerivAt (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) (c : ℝ) : Prop :=
  HasDerivAt (fun t : ℝ => f (Function.update x i t)) c (x i)

namespace HasPDerivAt

variable {f g : (Fin n → ℝ) → ℝ} {i : Fin n} {x : Fin n → ℝ} {a b : ℝ}

theorem add (hf : HasPDerivAt f i x a) (hg : HasPDerivAt g i x b) :
    HasPDerivAt (fun y => f y + g y) i x (a + b) := HasDerivAt.add hf hg

theorem sub (hf : HasPDerivAt f i x a) (hg : HasPDerivAt g i x b) :
    HasPDerivAt (fun y => f y - g y) i x (a - b) := HasDerivAt.sub hf hg

theorem mul (hf : HasPDerivAt f i x a) (hg : HasPDerivAt g i x b) :
    HasPDerivAt (fun y => f y * g y) i x (a * g x + f x * b) := by
  have h := HasDerivAt.mul hf hg
  simpa [Function.update_eq_self] using h

theorem const_mul (c : ℝ) (hf : HasPDerivAt f i x a) :
    HasPDerivAt (fun y => c * f y) i x (c * a) := HasDerivAt.const_mul c hf

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (Fin n → ℝ) → ℝ} {c : ι → ℝ}
    (h : ∀ k ∈ s, HasPDerivAt (F k) i x (c k)) :
    HasPDerivAt (fun y => ∑ k ∈ s, F k y) i x (∑ k ∈ s, c k) := by
  have h2 := HasDerivAt.sum h
  have hfun : (∑ k ∈ s, fun t : ℝ => F k (Function.update x i t))
      = fun t : ℝ => ∑ k ∈ s, F k (Function.update x i t) := by
    funext t; simp [Finset.sum_apply]
  rwa [hfun] at h2

theorem unique (hf : HasPDerivAt f i x a) (hf' : HasPDerivAt f i x b) : a = b :=
  HasDerivAt.unique hf hf'

theorem congr {h : (Fin n → ℝ) → ℝ} (hf : HasPDerivAt f i x a) (heq : ∀ y, h y = f y) :
    HasPDerivAt h i x a := by
  simpa [HasPDerivAt, heq] using hf

end HasPDerivAt

/-! ## The diffusion matrix, the probability current and the formal adjoint -/

variable {r : ℕ}

/-- The diffusion matrix `aⁱʲ = Σ_l f_lⁱ f_lʲ` of Eq. (16). -/
def diffusionMatrix (f : Fin r → (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ l, f l y i * f l y j

variable {f : Fin r → (Fin n → ℝ) → Fin n → ℝ} {p : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
  {df : Fin r → Fin n → Fin n → ℝ} {dp : Fin n → ℝ}

/-- The partial derivative `∂(aⁱʲ p)/∂zʲ`, computed from the partial derivatives of the
noise vector fields and of the density. -/
theorem hasPDerivAt_diffusionMatrix_mul
    (hf : ∀ l k j, HasPDerivAt (fun y => f l y k) j x (df l k j))
    (hp : ∀ j, HasPDerivAt p j x (dp j)) (i j : Fin n) :
    HasPDerivAt (fun y => diffusionMatrix f y i j * p y) j x
      ((∑ l, (df l i j * f l x j + f l x i * df l j j)) * p x
        + diffusionMatrix f x i j * dp j) := by
  have ha : HasPDerivAt (fun y => diffusionMatrix f y i j) j x
      (∑ l, (df l i j * f l x j + f l x i * df l j j)) := by
    have := HasPDerivAt.sum (i := j) (x := x) Finset.univ
      (F := fun l y => f l y i * f l y j)
      (c := fun l => df l i j * f l x j + f l x i * df l j j)
      (fun l _ => (hf l i j).mul (hf l j j))
    exact this
  exact ha.mul (hp j)

/-! ### `F p = −div(j)` -/

/-- The value of the formal adjoint `F p` of Eq. (21) at `x`, in terms of the partial
derivatives `dfp i = ∂(f₀ⁱ p)/∂zⁱ` and `ddgap i j = ∂²(aⁱʲ p)/∂zⁱ∂zʲ`. -/
def formalAdjointVal (dfp : Fin n → ℝ) (ddgap : Fin n → Fin n → ℝ) : ℝ :=
  -(∑ i, dfp i) + 2⁻¹ * ∑ i, ∑ j, ddgap i j

/-- **Eq. (16) and (21)**: the formal adjoint of the generator is minus the divergence of
the probability current, `F p = −div(j)`.

The current is `Jf y i = f₀ⁱ(y) p(y) − ½ Σ_j gapf y i j` with `gapf y i j = ∂(aⁱʲp)/∂zʲ`
(hypothesis `hJdef`); `dfp i` is `∂(f₀ⁱ p)/∂zⁱ` at `x` and `ddgap i j` is
`∂(gapf · i j)/∂zⁱ = ∂²(aⁱʲ p)/∂zⁱ∂zʲ` at `x`. -/
theorem divergence_current_eq_neg_formalAdjoint
    {Jf : (Fin n → ℝ) → Fin n → ℝ} {gapf : (Fin n → ℝ) → Fin n → Fin n → ℝ}
    {f0 : (Fin n → ℝ) → Fin n → ℝ} {dfp : Fin n → ℝ} {ddgap : Fin n → Fin n → ℝ}
    (hJdef : ∀ y i, Jf y i = f0 y i * p y - 2⁻¹ * ∑ j, gapf y i j)
    (hfp : ∀ i, HasPDerivAt (fun y => f0 y i * p y) i x (dfp i))
    (hgap : ∀ i j, HasPDerivAt (fun y => gapf y i j) i x (ddgap i j)) :
    (∀ i, HasPDerivAt (fun y => Jf y i) i x (dfp i - 2⁻¹ * ∑ j, ddgap i j)) ∧
      ∑ i, (dfp i - 2⁻¹ * ∑ j, ddgap i j) = -formalAdjointVal dfp ddgap := by
  constructor
  · intro i
    have h1 : HasPDerivAt (fun y => 2⁻¹ * ∑ j, gapf y i j) i x (2⁻¹ * ∑ j, ddgap i j) :=
      HasPDerivAt.const_mul _ (HasPDerivAt.sum Finset.univ fun j _ => hgap i j)
    exact ((hfp i).sub h1).congr fun y => hJdef y i
  · rw [formalAdjointVal, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

/-! ### Eq. (45): `j·∇φ = div(φ j) + φ F p` -/

/-- The product rule for the components of `φ j`. -/
theorem hasPDerivAt_mul_current {Jf : (Fin n → ℝ) → Fin n → ℝ} {phi : (Fin n → ℝ) → ℝ}
    {dphi dJ : Fin n → ℝ}
    (hphi : ∀ i, HasPDerivAt phi i x (dphi i))
    (hJ : ∀ i, HasPDerivAt (fun y => Jf y i) i x (dJ i)) (i : Fin n) :
    HasPDerivAt (fun y => phi y * Jf y i) i x (dphi i * Jf x i + phi x * dJ i) :=
  (hphi i).mul (hJ i)

/-- **Eq. (45)**: `j·∇φ = div(φ j) − φ div(j) = div(φ j) + φ F p`, where
`div(φ j) = Σ_i (∂φ/∂zⁱ jⁱ + φ ∂jⁱ/∂zⁱ)` and `F p = −div(j)`. -/
theorem current_dot_grad_eq {Jf : (Fin n → ℝ) → Fin n → ℝ} {phi : (Fin n → ℝ) → ℝ}
    {dphi dJ : Fin n → ℝ} (Fpx : ℝ) (hF : ∑ i, dJ i = -Fpx) :
    ∑ i, Jf x i * dphi i
      = (∑ i, (dphi i * Jf x i + phi x * dJ i)) + phi x * Fpx := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hF]
  have : ∑ i, dphi i * Jf x i = ∑ i, Jf x i * dphi i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]
  ring

/-! ### Eq. (44) -/

/-- The vector field `(f_l φ) p f_l` whose divergence appears in Eq. (44). -/
def noiseField (f : Fin r → (Fin n → ℝ) → Fin n → ℝ) (gphi : (Fin n → ℝ) → Fin n → ℝ)
    (p : (Fin n → ℝ) → ℝ) (l : Fin r) (y : Fin n → ℝ) (j : Fin n) : ℝ :=
  (∑ i, f l y i * gphi y i) * p y * f l y j

/-- The `j`-th partial derivative of the `j`-th component of the vector field
`(f_l φ) p f_l`. -/
theorem hasPDerivAt_noiseField {gphi : (Fin n → ℝ) → Fin n → ℝ}
    {ddphi : Fin n → Fin n → ℝ}
    (hf : ∀ l k j, HasPDerivAt (fun y => f l y k) j x (df l k j))
    (hp : ∀ j, HasPDerivAt p j x (dp j))
    (hgphi : ∀ i j, HasPDerivAt (fun y => gphi y i) j x (ddphi i j))
    (l : Fin r) (j : Fin n) :
    HasPDerivAt (fun y => noiseField f gphi p l y j) j x
      ((∑ i, (df l i j * gphi x i + f l x i * ddphi i j)) * (p x * f l x j)
        + (∑ i, f l x i * gphi x i) * (dp j * f l x j + p x * df l j j)) := by
  have hA : HasPDerivAt (fun y => ∑ i, f l y i * gphi y i) j x
      (∑ i, (df l i j * gphi x i + f l x i * ddphi i j)) :=
    HasPDerivAt.sum Finset.univ fun i _ => (hf l i j).mul (hgphi i j)
  have hB : HasPDerivAt (fun y => p y * f l y j) j x (dp j * f l x j + p x * df l j j) :=
    (hp j).mul (hf l j j)
  exact (hA.mul hB).congr fun y => by simp [noiseField, mul_assoc]

/-- Reordering a triple sum. -/
private theorem sum3_comm {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (F : ι → κ → ν → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, F a b c := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- The total divergence of the noise fields, expanded through the derivatives of the
diffusion matrix: `Σ_l div((f_lφ) p f_l) = Σ_i (Σ_j ∂(aⁱʲp)/∂zʲ) ∂φ/∂zⁱ
+ Σ_{i,j} aⁱʲ p ∂²φ/∂zⁱ∂zʲ`. -/
theorem sum_divergence_noiseField_eq {gphi : (Fin n → ℝ) → Fin n → ℝ}
    {ddphi : Fin n → Fin n → ℝ} :
    (∑ l, ∑ j, ((∑ i, (df l i j * gphi x i + f l x i * ddphi i j)) * (p x * f l x j)
        + (∑ i, f l x i * gphi x i) * (dp j * f l x j + p x * df l j j)))
      = (∑ i, (∑ j, ((∑ l, (df l i j * f l x j + f l x i * df l j j)) * p x
          + diffusionMatrix f x i j * dp j)) * gphi x i)
        + ∑ i, ∑ j, (diffusionMatrix f x i j * p x * ddphi i j) := by
  simp only [diffusionMatrix]
  have hL : ∀ l j, ((∑ i, (df l i j * gphi x i + f l x i * ddphi i j)) * (p x * f l x j)
        + (∑ i, f l x i * gphi x i) * (dp j * f l x j + p x * df l j j))
      = ∑ i, ((df l i j * gphi x i + f l x i * ddphi i j) * (p x * f l x j)
        + f l x i * gphi x i * (dp j * f l x j + p x * df l j j)) := by
    intro l j
    simp only [Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  have hR1 : ∀ i, (∑ j, ((∑ l, (df l i j * f l x j + f l x i * df l j j)) * p x
        + (∑ l, f l x i * f l x j) * dp j)) * gphi x i
      = ∑ j, ∑ l, ((df l i j * f l x j + f l x i * df l j j) * p x * gphi x i
          + f l x i * f l x j * dp j * gphi x i) := by
    intro i
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  have hR2 : ∀ i, ∑ j, ((∑ l, f l x i * f l x j) * p x * ddphi i j)
      = ∑ j, ∑ l, (f l x i * f l x j * p x * ddphi i j) := fun i =>
    Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul, Finset.sum_mul]
  simp only [hL, hR1, hR2, ← Finset.sum_add_distrib]
  rw [sum3_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => by ring

/-- **Eq. (44)** (Appendix C.1): with the probability current

  `jⁱ = f₀ⁱ p − ½ Σ_j ∂(aⁱʲ p)/∂zʲ`,

the product of the generator applied to a test function `φ` with the density `p`
decomposes as

  `(Lφ) p = j·∇φ + ½ Σ_l div((f_lφ) p f_l)`.

Here `gphi x i = ∂φ/∂zⁱ(x)`, `ddphi i j = ∂²φ/∂zⁱ∂zʲ(x)`, and `Jx` is the current at
`x`. -/
theorem generator_mul_density_eq {f0 : (Fin n → ℝ) → Fin n → ℝ}
    {gphi : (Fin n → ℝ) → Fin n → ℝ} {ddphi : Fin n → Fin n → ℝ} {Jx : Fin n → ℝ}
    (hJx : ∀ i, Jx i = f0 x i * p x
      - 2⁻¹ * ∑ j, ((∑ l, (df l i j * f l x j + f l x i * df l j j)) * p x
          + diffusionMatrix f x i j * dp j)) :
    (∑ i, f0 x i * gphi x i + 2⁻¹ * ∑ i, ∑ j, diffusionMatrix f x i j * ddphi i j) * p x
      = (∑ i, Jx i * gphi x i)
        + 2⁻¹ * ∑ l, ∑ j, ((∑ i, (df l i j * gphi x i + f l x i * ddphi i j))
            * (p x * f l x j)
          + (∑ i, f l x i * gphi x i) * (dp j * f l x j + p x * df l j j)) := by
  rw [sum_divergence_noiseField_eq (df := df) (dp := dp) (gphi := gphi) (ddphi := ddphi)]
  have hJ : ∑ i, Jx i * gphi x i
      = (∑ i, f0 x i * p x * gphi x i)
        - 2⁻¹ * ∑ i, (∑ j, ((∑ l, (df l i j * f l x j + f l x i * df l j j)) * p x
            + diffusionMatrix f x i j * dp j)) * gphi x i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hJx i]; ring
  rw [hJ]
  have h1 : (∑ i, f0 x i * gphi x i) * p x = ∑ i, f0 x i * p x * gphi x i := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (2⁻¹ * ∑ i, ∑ j, diffusionMatrix f x i j * ddphi i j) * p x
      = 2⁻¹ * ∑ i, ∑ j, diffusionMatrix f x i j * p x * ddphi i j := by
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [add_mul, h1, h2]
  ring

/-! ## Proposition 11: the mean intensity of forced jumps is the outward current -/

variable {E : Type*} [MeasurableSpace E]

/-- **Proposition 11(a)**, first half (Eq. (49) on the guard set).  On a measurable
region `W ⊆ G` of zero volume measure, the balance equation (49) — in which the time
derivative and the source term vanish, since `m(W) = 0` and the reset kernel maps into
`E⁰` — identifies the mean intensity of forced jumps with the outward flow of the
probability current through the surface measure `s`. -/
theorem forced_intensity_eq_current (m s : Measure E) (rG : Measure E) {Fp jout : E → ℝ}
    {W : Set E} (hmW : m W = 0)
    (hbal : ∀ Γ, MeasurableSet Γ → Γ ⊆ W →
      (rG Γ).toReal = ∫ y in Γ, Fp y ∂m + ∫ y in Γ, jout y ∂s) :
    ∀ Γ, MeasurableSet Γ → Γ ⊆ W → (rG Γ).toReal = ∫ y in Γ, jout y ∂s := by
  intro Γ hΓ hsub
  have hmΓ : m Γ = 0 := measure_mono_null hsub hmW
  have hrest : m.restrict Γ = 0 := by
    rw [Measure.restrict_eq_zero]; exact hmΓ
  have : ∫ y in Γ, Fp y ∂m = 0 := by rw [hrest]; simp
  rw [hbal Γ hΓ hsub, this, zero_add]

/-- **Proposition 11(a)**, second half: since the mean intensity of forced jumps is a
positive measure, the outward probability current is nonnegative `s`-almost everywhere
on the guard set. -/
theorem current_nonneg (s : Measure E) (rG : Measure E) {jout : E → ℝ} {W : Set E}
    (hW : MeasurableSet W) (hint : IntegrableOn jout W s)
    (hcur : ∀ Γ, MeasurableSet Γ → Γ ⊆ W → (rG Γ).toReal = ∫ y in Γ, jout y ∂s) :
    0 ≤ᵐ[s.restrict W] jout := by
  refine ae_nonneg_of_forall_setIntegral_nonneg hint fun A hA _ => ?_
  have hsub : A ∩ W ⊆ W := inter_subset_right
  have hAW : MeasurableSet (A ∩ W) := hA.inter hW
  have hrw : ∫ y in A, jout y ∂(s.restrict W) = ∫ y in A ∩ W, jout y ∂s := by
    rw [Measure.restrict_restrict hA]
  rw [hrw, ← hcur (A ∩ W) hAW hsub]
  exact ENNReal.toReal_nonneg

/-- **Proposition 11(b)**, analytic core (Appendix C.2).  If the surface integrals
`∫_Γ p ⟨f_l, n⟩² ds` vanish for all measurable `Γ` inside the smooth part `V` of the
boundary — which is what the limiting argument of Appendix C.2 produces — then the
product `p · Σ_l ⟨f_l, n⟩²` vanishes `s`-almost everywhere on `V`. -/
theorem density_mul_normal_ae_eq_zero (s : Measure E) {pdf w : E → ℝ} {V : Set E}
    (hV : MeasurableSet V) (hint : IntegrableOn (fun y => pdf y * w y) V s)
    (hzero : ∀ Γ, MeasurableSet Γ → Γ ⊆ V → ∫ y in Γ, pdf y * w y ∂s = 0) :
    (fun y => pdf y * w y) =ᵐ[s.restrict V] 0 := by
  refine hint.ae_eq_zero_of_forall_setIntegral_eq_zero fun A hA _ => ?_
  have hrw : ∫ y in A, pdf y * w y ∂(s.restrict V) = ∫ y in A ∩ V, pdf y * w y ∂s := by
    rw [Measure.restrict_restrict hA]
  rw [hrw]
  exact hzero (A ∩ V) (hA.inter hV) inter_subset_right

/-- **Proposition 11(b)**: the *absorbing boundary condition*.  Where the noise vector
fields are not all tangent to the boundary, i.e. on `G⁰ = {Σ_l ⟨f_l, n⟩² > 0}`, the
vanishing of `p · Σ_l ⟨f_l, n⟩²` forces the density itself to vanish. -/
theorem density_ae_eq_zero_on_pos (s : Measure E) {pdf w : E → ℝ} {V : Set E}
    (hprod : (fun y => pdf y * w y) =ᵐ[s.restrict V] 0) :
    ∀ᵐ y ∂(s.restrict V), 0 < w y → pdf y = 0 := by
  filter_upwards [hprod] with y hy hpos
  simp only [Pi.zero_apply] at hy
  rcases mul_eq_zero.1 hy with h | h
  · exact h
  · exact absurd h (ne_of_gt hpos)

/-! ## Appendix C.3: the Radon measure `L^* μ_t`, Eqs. (20) and (48) -/

/-- **Eqs. (20) and (48)**: once Proposition 11(b) has removed the last term of Eq. (46),
the Radon measure `L^* μ_t` is the signed measure with volume density `F p_t` with
respect to `m` plus surface density `j_t^out` with respect to `s` on the boundary. -/
def lstarMeasure (m s : Measure E) (bdry : Set E) (Fp jout : E → ℝ) : SignedMeasure E :=
  m.withDensityᵥ Fp + (s.restrict bdry).withDensityᵥ jout

/-- **Eq. (48)** evaluated on a measurable set:
`(L^* μ_t)(Γ) = ∫_Γ F p_t dm + ∫_{∂E ∩ Γ} j_t^out ds`. -/
theorem lstarMeasure_apply (m s : Measure E) {bdry : Set E} {Fp jout : E → ℝ}
    (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    {Gam : Set E} (hGam : MeasurableSet Gam) :
    lstarMeasure m s bdry Fp jout Gam
      = (∫ x in Gam, Fp x ∂m) + ∫ y in bdry ∩ Gam, jout y ∂s := by
  rw [lstarMeasure, VectorMeasure.add_apply, withDensityᵥ_apply hFp hGam,
    withDensityᵥ_apply hjout hGam, Measure.restrict_restrict hGam, Set.inter_comm]

/-- Away from the boundary, Eq. (48) reduces to the absolutely continuous part alone:
`(L^* μ_t)(Γ) = ∫_Γ F p_t dm` for `Γ` disjoint from `∂E`. -/
theorem lstarMeasure_apply_of_disjoint (m s : Measure E) {bdry : Set E} {Fp jout : E → ℝ}
    (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    {Gam : Set E} (hGam : MeasurableSet Gam) (hdisj : Disjoint bdry Gam) :
    lstarMeasure m s bdry Fp jout Gam = ∫ x in Gam, Fp x ∂m := by
  rw [lstarMeasure_apply m s hFp hjout hGam, hdisj.inter_eq]
  simp

/-- **Eq. (22)**: the measures `β_t` measure the failure of Eq. (48) — equivalently, of
the usual Fokker–Planck equation — on the singular set `H`. -/
def betaMeasure (m s : Measure E) (bdry : Set E) (Fp jout : E → ℝ)
    (lstar : SignedMeasure E) : SignedMeasure E :=
  lstarMeasure m s bdry Fp jout - lstar

/-- Eq. (22) evaluated on a measurable set. -/
theorem betaMeasure_apply (m s : Measure E) {bdry : Set E} {Fp jout : E → ℝ}
    (lstar : SignedMeasure E) (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    {Gam : Set E} (hGam : MeasurableSet Gam) :
    betaMeasure m s bdry Fp jout lstar Gam
      = (∫ x in Gam, Fp x ∂m) + (∫ y in bdry ∩ Gam, jout y ∂s) - lstar Gam := by
  rw [betaMeasure, VectorMeasure.sub_apply, lstarMeasure_apply m s hFp hjout hGam]

/-- If `L^* μ_t` is already given by Eq. (48) on a region, then `β_t` vanishes there:
there is no singular contribution away from `H`. -/
theorem betaMeasure_eq_zero_of_eq (m s : Measure E) {bdry : Set E} {Fp jout : E → ℝ}
    (lstar : SignedMeasure E) (hFp : Integrable Fp m) (hjout : IntegrableOn jout bdry s)
    {Gam : Set E} (hGam : MeasurableSet Gam)
    (heq : lstar Gam = (∫ x in Gam, Fp x ∂m) + ∫ y in bdry ∩ Gam, jout y ∂s) :
    betaMeasure m s bdry Fp jout lstar Gam = 0 := by
  rw [betaMeasure_apply m s lstar hFp hjout hGam, heq]
  ring

end GSHS
