/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The extended generator of a General Stochastic Hybrid System

Formalization of Section 4 ("The Process Generator", Proposition 6 and
Theorem 2) of

  M.L. Bujorianu and J. Lygeros, "Toward a General Theory of Stochastic Hybrid
  Systems", LNCIS 337, Springer, 2006.

Theorem 2 states that for a GSHS the extended generator is

  `Lf(x) = L_cont f(x) + λ(x) ∫_{X̄} (f(y) - f(x)) R(x, dy)`        (28)

with

  `L_cont f(x) = 𝓛_b f(x) + ½ Tr(σ(x) σ(x)ᵀ H^f(x))`,              (29)

on the domain of functions that are twice differentiable in each mode, satisfy
the boundary condition `f(x) = ∫ f(y) R(x, dy)` for `x ∈ ∂X`, and for which
`Bf ∈ L₁^{loc}(p)`.

This file defines these operators and proves their basic structural
properties, including the two facts used in the proof of Theorem 2: the
boundary condition makes the boundary jump term `I₂` vanish, and the generator
annihilates constants.  A scalar instance of the formula is computed
explicitly at the end of the file.
-/
import SHSLib.Bujorianu2006.HybridSpace

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Bujorianu2006

/-! ## The continuous part `L_cont` (Eq. (29)) -/

section Cont

variable {n m : ℕ}

/-- The Hessian matrix `H^f(x) = (∂²f/∂x_i ∂x_j)(x)` of a function on
`ℝⁿ`, expressed through iterated Fréchet derivatives in the coordinate
directions. -/
def hessMat (f : ModeSpace n → ℝ) (x : ModeSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) x
    (EuclideanSpace.single i (1 : ℝ))

/-- The diffusion matrix `D(x) = σ(x) σ(x)ᵀ`. -/
def diffusionMatrix (sig : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  sig * sig.transpose

/-- The diffusion matrix is symmetric. -/
theorem diffusionMatrix_symm (sig : Matrix (Fin n) (Fin m) ℝ) :
    (diffusionMatrix sig).transpose = diffusionMatrix sig := by
  simp [diffusionMatrix, Matrix.transpose_mul]

/-- Expansion of the trace occurring in (29):
`Tr(A B) = ∑_i ∑_j A_{ij} B_{ji}`. -/
theorem trace_mul_expand (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (A * B) = ∑ i, ∑ j, A i j * B j i := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- **Equation (29)**: the continuous (diffusion) part of the generator,
`L_cont f(x) = 𝓛_b f(x) + ½ Tr(σ(x)σ(x)ᵀ H^f(x))`.  The Lie derivative
`𝓛_b f(x) = ∑_i ∂f/∂x_i (x) b_i(x)` is the Fréchet derivative of `f` at `x` in
the direction `b(x)`. -/
def contPart (b : ModeSpace n → ModeSpace n) (sig : ModeSpace n → Matrix (Fin n) (Fin m) ℝ)
    (f : ModeSpace n → ℝ) (x : ModeSpace n) : ℝ :=
  fderiv ℝ f x (b x) + (1 / 2) * Matrix.trace (diffusionMatrix (sig x) * hessMat f x)

/-- The coordinate form of (29): `L_cont f(x)` equals the Lie derivative plus
`½ ∑_{i,j} (σσᵀ)_{ij} ∂²f/∂x_j∂x_i`. -/
theorem contPart_eq_sum (b : ModeSpace n → ModeSpace n)
    (sig : ModeSpace n → Matrix (Fin n) (Fin m) ℝ) (f : ModeSpace n → ℝ) (x : ModeSpace n) :
    contPart b sig f x
      = fderiv ℝ f x (b x)
        + (1 / 2) * ∑ i, ∑ j, (diffusionMatrix (sig x)) i j * hessMat f x j i := by
  rw [contPart, trace_mul_expand]

/-- The Hessian of a constant function vanishes. -/
@[simp] theorem hessMat_const (c : ℝ) (x : ModeSpace n) :
    hessMat (fun _ : ModeSpace n => c) x = 0 := by
  ext i j
  simp [hessMat]

/-- `L_cont` annihilates the constants. -/
@[simp] theorem contPart_const (b : ModeSpace n → ModeSpace n)
    (sig : ModeSpace n → Matrix (Fin n) (Fin m) ℝ) (c : ℝ) (x : ModeSpace n) :
    contPart b sig (fun _ => c) x = 0 := by
  simp [contPart]

end Cont

/-! ## The jump part of the generator (second term of Eq. (28)) -/

section Jump

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The jump part of the generator,
`λ(x) ∫ (f(y) - f(x)) R(x, dy)`, for a reset kernel `R` from `X` to `Y` and a
function `f` on `X ⊔ Y` presented as a pair `(fX, fY)` of its restrictions. -/
def jumpPart (lam : X → ℝ) (R : Kernel X Y) (fX : X → ℝ) (fY : Y → ℝ) (x : X) : ℝ :=
  lam x * ∫ y, (fY y - fX x) ∂(R x)

variable {lam : X → ℝ} {R : Kernel X Y} [IsMarkovKernel R]

/-- With a Markov (probability) reset kernel, the jump part is
`λ(x) (∫ f dR(x, ·) - f(x))`. -/
theorem jumpPart_eq_sub (fX : X → ℝ) (fY : Y → ℝ) (x : X)
    (hint : Integrable fY (R x)) :
    jumpPart lam R fX fY x = lam x * ((∫ y, fY y ∂(R x)) - fX x) := by
  rw [jumpPart, integral_sub hint (integrable_const _)]
  simp

omit [IsMarkovKernel R] in
/-- The jump part annihilates the constants: if `f ≡ c` on both sides of the
jump, the jump term vanishes. -/
@[simp] theorem jumpPart_const (c : ℝ) (x : X) :
    jumpPart lam R (fun _ => c) (fun _ => c) x = 0 := by
  simp [jumpPart]

/-- **The boundary condition of Theorem 2 makes the jump term vanish.**  This
is the vanishing of the integral `I₂` in the proof of Theorem 2: at a boundary
point `x`, where `f(x) = ∫ f(y) R(x, dy)`, the jump contribution is zero. -/
theorem jumpPart_eq_zero_of_boundary (fX : X → ℝ) (fY : Y → ℝ) (x : X)
    (hint : Integrable fY (R x)) (hbdry : fX x = ∫ y, fY y ∂(R x)) :
    jumpPart lam R fX fY x = 0 := by
  rw [jumpPart_eq_sub fX fY x hint, hbdry, sub_self, mul_zero]

/-- The jump part is additive in the function. -/
theorem jumpPart_add (fX gX : X → ℝ) (fY gY : Y → ℝ) (x : X)
    (hf : Integrable fY (R x)) (hg : Integrable gY (R x)) :
    jumpPart lam R (fun z => fX z + gX z) (fun y => fY y + gY y) x
      = jumpPart lam R fX fY x + jumpPart lam R gX gY x := by
  rw [jumpPart_eq_sub (fun z => fX z + gX z) (fun y => fY y + gY y) x (hf.add hg),
    jumpPart_eq_sub fX fY x hf, jumpPart_eq_sub gX gY x hg, integral_add hf hg]
  ring

/-- The jump part is homogeneous in the function. -/
theorem jumpPart_smul (c : ℝ) (fX : X → ℝ) (fY : Y → ℝ) (x : X)
    (hf : Integrable fY (R x)) :
    jumpPart lam R (fun z => c * fX z) (fun y => c * fY y) x
      = c * jumpPart lam R fX fY x := by
  rw [jumpPart_eq_sub (fun z => c * fX z) (fun y => c * fY y) x (hf.const_mul c),
    jumpPart_eq_sub fX fY x hf, integral_const_mul]
  ring

/-- **Maximum principle for the jump part**: at a point where `f` attains its
maximum over the support of the reset kernel, the jump term is nonpositive
(for a nonnegative jump rate). -/
theorem jumpPart_nonpos_of_max (fX : X → ℝ) (fY : Y → ℝ) (x : X)
    (hlam : 0 ≤ lam x) (hint : Integrable fY (R x)) (hmax : ∀ y, fY y ≤ fX x) :
    jumpPart lam R fX fY x ≤ 0 := by
  rw [jumpPart_eq_sub fX fY x hint]
  have hle : (∫ y, fY y ∂(R x)) ≤ fX x := by
    calc (∫ y, fY y ∂(R x)) ≤ ∫ _y, fX x ∂(R x) :=
          integral_mono hint (integrable_const _) hmax
      _ = fX x := by simp
  exact mul_nonpos_of_nonneg_of_nonpos hlam (sub_nonpos.mpr hle)

end Jump

/-! ## The generator of a GSHS (Theorem 2) -/

namespace GSHS

open HybridStateSpace

variable (H : GSHS)

/-- The inclusion `X ↪ X̄` of the hybrid state space into its closure. -/
def incl : Hyb H.toHybridStateSpace → Cl H.toHybridStateSpace :=
  fun p => ⟨p.1, ⟨p.2.1, subset_closure p.2.2⟩⟩

/-- A *test function* for the generator: a family of functions `f^i` on the
ambient spaces `ℝ^{d(i)}`; the associated function on `X̄` is `hybFun`. -/
def hybFun (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ) : Cl H.toHybridStateSpace → ℝ :=
  fun p => F p.1 p.2.1

/-- Condition 1 of Theorem 2: each restriction `f^i` is twice differentiable. -/
def TwiceDifferentiable (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ) : Prop :=
  ∀ i, ContDiff ℝ 2 (F i)

/-- **Condition 2 of Theorem 2** (the boundary condition):
`f(x) = ∫_{X̄} f(y) R(x, dy)` for every `x ∈ ∂X`. -/
def BoundaryCondition (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ) : Prop :=
  ∀ x : Cl H.toHybridStateSpace, (x.2 : ModeSpace (H.d x.1)) ∈ frontier (H.X x.1) →
    H.hybFun F x = ∫ y, H.hybFun F (H.incl y) ∂(H.R x)

/-- The continuous part of the generator of `H`, mode by mode (Eq. (29)). -/
def contGen (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ) : Cl H.toHybridStateSpace → ℝ :=
  fun p => contPart (H.b p.1) (H.sig p.1) (F p.1) p.2.1

/-- The jump part of the generator of `H` (second term of Eq. (28)). -/
def jumpGen (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ) : Cl H.toHybridStateSpace → ℝ :=
  fun x => jumpPart H.lam H.R (H.hybFun F) (fun y => H.hybFun F (H.incl y)) x

/-- **Equation (28)**: the extended generator of a GSHS,
`Lf(x) = L_cont f(x) + λ(x) ∫ (f(y) - f(x)) R(x, dy)`. -/
def gen (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ) : Cl H.toHybridStateSpace → ℝ :=
  fun x => H.contGen F x + H.jumpGen F x

/-- The generator annihilates the constant functions. -/
@[simp] theorem gen_const (c : ℝ) (x : Cl H.toHybridStateSpace) :
    H.gen (fun _ _ => c) x = 0 := by
  simp [gen, contGen, jumpGen, hybFun, jumpPart]

/-- At a boundary point at which the boundary condition of Theorem 2 holds, the
generator reduces to its continuous part.  This is the step
"the second integral `I₂` vanishes" in the proof of Theorem 2. -/
theorem gen_eq_contGen_of_boundary (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ)
    (hb : H.BoundaryCondition F) (x : Cl H.toHybridStateSpace)
    (hx : (x.2 : ModeSpace (H.d x.1)) ∈ frontier (H.X x.1))
    (hint : Integrable (fun y => H.hybFun F (H.incl y)) (H.R x)) :
    H.gen F x = H.contGen F x := by
  have : H.jumpGen F x = 0 :=
    jumpPart_eq_zero_of_boundary _ _ x hint (hb x hx)
  rw [gen, this, add_zero]

/-! ### Proposition 6: the martingale associated with a function in the domain -/

/-- **Equation (27)**: the process `C_t^f = f(x_t) - f(x_0) - ∫₀ᵗ Lf(x_s) ds`
associated with a function `f` in the domain of the generator.  Proposition 6
asserts that `(C_t^f)` is a martingale; here we record the process itself. -/
def dynkinProcess (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ)
    (path : ℝ → Cl H.toHybridStateSpace) (t : ℝ) : ℝ :=
  H.hybFun F (path t) - H.hybFun F (path 0) - ∫ s in (0 : ℝ)..t, H.gen F (path s)

/-- The Dynkin process of (27) starts at zero. -/
@[simp] theorem dynkinProcess_zero (F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ)
    (path : ℝ → Cl H.toHybridStateSpace) : H.dynkinProcess F path 0 = 0 := by
  simp [dynkinProcess]

/-- For a constant function the Dynkin process of (27) vanishes identically —
the constants are in the domain of the extended generator with `Lf = 0`. -/
@[simp] theorem dynkinProcess_const (c : ℝ) (path : ℝ → Cl H.toHybridStateSpace) (t : ℝ) :
    H.dynkinProcess (fun _ _ => c) path t = 0 := by
  simp [dynkinProcess, hybFun]

end GSHS

/-! ## A scalar instance of the generator formula

To exhibit formula (28)–(29) concretely we specialize it to a one-dimensional
single-mode system with deterministic reset `y = a x`:

  `Lf(x) = b(x) f'(x) + ½ σ(x)² f''(x) + λ(x) (f(a x) - f(x))`.
-/

section Scalar

/-- The scalar (one-dimensional, one-mode) version of the generator (28)–(29)
with reset kernel `R(x, ·) = δ_{a x}`. -/
def scalarGen (b sig lam : ℝ → ℝ) (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  b x * deriv f x + (1 / 2) * (sig x) ^ 2 * deriv (deriv f) x + lam x * (f (a * x) - f x)

/-- The scalar generator annihilates the constants. -/
@[simp] theorem scalarGen_const (b sig lam : ℝ → ℝ) (a c x : ℝ) :
    scalarGen b sig lam a (fun _ => c) x = 0 := by
  simp [scalarGen]

/-- The scalar generator applied to `f(x) = x`, for constant coefficients:
`Lf(x) = β + μ (a - 1) x`. -/
theorem scalarGen_id (beta s mu a x : ℝ) :
    scalarGen (fun _ => beta) (fun _ => s) (fun _ => mu) a (fun y => y) x
      = beta + mu * (a - 1) * x := by
  have h1 : deriv (fun y : ℝ => y) = fun _ => (1 : ℝ) := by
    funext y; simp
  have h2 : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => (0 : ℝ) := by
    funext y; simp
  rw [scalarGen, h1, h2]
  ring

/-- The scalar generator applied to `f(x) = x²`, for constant coefficients:
`Lf(x) = 2βx + s² + μ (a² - 1) x²`.  This is the moment equation obtained from
(28)–(29) for a linear stochastic hybrid system with multiplicative reset. -/
theorem scalarGen_sq (beta s mu a x : ℝ) :
    scalarGen (fun _ => beta) (fun _ => s) (fun _ => mu) a (fun y => y ^ 2) x
      = 2 * beta * x + s ^ 2 + mu * (a ^ 2 - 1) * x ^ 2 := by
  have h1 : deriv (fun y : ℝ => y ^ 2) = fun y => 2 * y := by
    funext y
    simp
  have h2 : deriv (fun y : ℝ => 2 * y) = fun _ => (2 : ℝ) := by
    funext y
    rw [deriv_const_mul_field]
    simp
  rw [scalarGen, h1, h2]
  ring

end Scalar

end Bujorianu2006

end
