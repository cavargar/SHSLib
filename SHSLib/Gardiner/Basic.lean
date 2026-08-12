/-
Formalization of the derivation of the *differential Chapman–Kolmogorov equation*
following C. W. Gardiner, *Handbook of Stochastic Methods*, §3.4 and §3.4.1.

This file sets up the state space, partial derivatives, the second order Taylor
remainder (3.4.10)–(3.4.11), the three regularity conditions (i), (ii), (iii)
of §3.4 [(3.4.1), (3.4.2), (3.4.3)], and the four quantities into which the
difference quotient (3.4.8)–(3.4.9) is split in (3.4.12).
-/
import Mathlib

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-- The state space `ℝⁿ` of the process, with its Euclidean norm. -/
abbrev Sp (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ### Partial derivatives -/

/-- `pd f i z` is the partial derivative `∂f(z)/∂z_i`. -/
def pd (f : Sp n → ℝ) (i : Fin n) (z : Sp n) : ℝ :=
  fderiv ℝ f z (EuclideanSpace.single i 1)

/-- `pd2 f i j z` is the second partial derivative `∂²f(z)/∂z_i ∂z_j`. -/
def pd2 (f : Sp n → ℝ) (i j : Fin n) (z : Sp n) : ℝ := pd (pd f j) i z

/-! ### The Taylor remainder (3.4.10), (3.4.11) -/

/-- The second-order Taylor remainder of `f` at `z` evaluated at `x`.  In the
notation of (3.4.10) this is `|x - z|² R(x, z)`. -/
def taylorRem (f : Sp n → ℝ) (z x : Sp n) : ℝ :=
  f x - f z - (∑ i, pd f i z * (x i - z i))
    - (1 / 2) * ∑ i, ∑ j, pd2 f i j z * (x i - z i) * (x j - z j)

/-- The first two nonconstant terms of the Taylor expansion (3.4.10). -/
def taylorPoly (f : Sp n → ℝ) (z x : Sp n) : ℝ :=
  (∑ i, pd f i z * (x i - z i))
    + (1 / 2) * ∑ i, ∑ j, pd2 f i j z * (x i - z i) * (x j - z j)

lemma taylor_decomp (f : Sp n → ℝ) (z x : Sp n) :
    f x - f z = taylorPoly f z x + taylorRem f z x := by
  simp only [taylorPoly, taylorRem]; ring

/-! ### The two regions of integration -/

/-- The set of pairs `(x, z)` with `|x - z| < ε`. -/
def nearDiag (ε : ℝ) : Set (Sp n × Sp n) := {q | dist q.1 q.2 < ε}

/-- The set of pairs `(x, z)` with `|x - z| ≥ ε`. -/
def farDiag (ε : ℝ) : Set (Sp n × Sp n) := {q | ε ≤ dist q.1 q.2}

lemma farDiag_eq_compl (ε : ℝ) : (farDiag ε : Set (Sp n × Sp n)) = (nearDiag ε)ᶜ := by
  ext q; simp [farDiag, nearDiag, not_lt]

lemma measurableSet_nearDiag (ε : ℝ) : MeasurableSet (nearDiag ε : Set (Sp n × Sp n)) :=
  (isOpen_lt (by fun_prop) continuous_const).measurableSet

lemma measurableSet_farDiag (ε : ℝ) : MeasurableSet (farDiag ε : Set (Sp n × Sp n)) := by
  rw [farDiag_eq_compl]; exact (measurableSet_nearDiag ε).compl

lemma nearDiag_symm {ε : ℝ} {q : Sp n × Sp n} (hq : q ∈ nearDiag ε) :
    Prod.swap q ∈ nearDiag ε := by
  simpa [nearDiag, dist_comm] using hq

lemma farDiag_symm {ε : ℝ} {q : Sp n × Sp n} (hq : q ∈ farDiag ε) :
    Prod.swap q ∈ farDiag ε := by
  simpa [farDiag, dist_comm] using hq

/-! ### Conditions (i), (ii), (iii) of §3.4 -/

/-- Condition (i), (3.4.1): `p(x, t+Δt | z, t)/Δt → W(x|z,t)` uniformly in `x, z`
on `|x - z| ≥ ε`, for every `ε > 0`.  Here `k dt z x` stands for
`p(x, t + dt | z, t)` and `W x z` for `W(x | z, t)`. -/
def CondJump (k : ℝ → Sp n → Sp n → ℝ) (W : Sp n → Sp n → ℝ) : Prop :=
  ∀ ε > 0, TendstoUniformlyOn (fun dt (q : Sp n × Sp n) => k dt q.2 q.1 / dt)
    (fun q => W q.1 q.2) (𝓝[>] (0 : ℝ)) (farDiag ε)

/-- Condition (ii), (3.4.2): the first moment over the `ε`-ball produces the drift
vector `A_i(z, t)` up to an error `O(ε)` which is uniform in `z`. -/
def CondDrift (k : ℝ → Sp n → Sp n → ℝ) (A : Sp n → Fin n → ℝ) : Prop :=
  ∃ C : ℝ, ∀ ε > 0, ∀ (i : Fin n) (z : Sp n), ∃ L : ℝ,
    Tendsto (fun dt : ℝ => (1 / dt) * ∫ x in ball z ε, (x i - z i) * k dt z x)
      (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ |L - A z i| ≤ C * ε

/-- Condition (iii), (3.4.3): the second moment over the `ε`-ball produces the
diffusion matrix `B_ij(z, t)` up to an error `O(ε)` which is uniform in `z`. -/
def CondDiffusion (k : ℝ → Sp n → Sp n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) : Prop :=
  ∃ C : ℝ, ∀ ε > 0, ∀ (i j : Fin n) (z : Sp n), ∃ L : ℝ,
    Tendsto (fun dt : ℝ => (1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * k dt z x)
      (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ |L - B z i j| ≤ C * ε

/-! ### The quantities appearing in the derivation

Throughout, `p s z` denotes `p(z, s | y, t')` for a fixed initial condition
`(y, t')`, and `k dt z x` denotes the transition density `p(x, t + dt | z, t)`.
-/

/-- The weight `p(x, t + Δt | z, t) p(z, t | y, t')` occurring in every double
integral of the derivation, as a function of the pair `q = (x, z)`. -/
def kernelWeight (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (t dt : ℝ)
    (q : Sp n × Sp n) : ℝ := k dt q.2 q.1 * p t q.2

/-- (3.4.8): the difference quotient whose limit as `Δt → 0` is
`∂_t ∫ dx f(x) p(x, t | y, t')`. -/
def diffQuot (p : ℝ → Sp n → ℝ) (f : Sp n → ℝ) (t dt : ℝ) : ℝ :=
  ((∫ x, f x * p (t + dt) x) - ∫ z, f z * p t z) / dt

/-- Lines 1 and 2 of (3.4.12): the contribution of the first and second order
Taylor terms on the region `|x - z| < ε`. -/
def Q12 (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (f : Sp n → ℝ) (t dt ε : ℝ) : ℝ :=
  (1 / dt) * ∫ q in nearDiag ε, taylorPoly f q.2 q.1 * kernelWeight p k t dt q

/-- Line 3 of (3.4.12): the remainder term. -/
def Q3 (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (f : Sp n → ℝ) (t dt ε : ℝ) : ℝ :=
  (1 / dt) * ∫ q in nearDiag ε, taylorRem f q.2 q.1 * kernelWeight p k t dt q

/-- Lines 4–6 of (3.4.12), combined as explained in the text: the contribution of
the region `|x - z| ≥ ε`. -/
def Qjump (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (f : Sp n → ℝ) (t dt ε : ℝ) : ℝ :=
  (1 / dt) * ∫ q in farDiag ε, (f q.1 - f q.2) * kernelWeight p k t dt q

/-- The second moment appearing in the estimate (3.4.14) of line 3. -/
def Qsq (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (t dt ε : ℝ) : ℝ :=
  (1 / dt) * ∫ q in nearDiag ε, ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q

/-- (3.4.13): the drift and diffusion part of the right-hand side. -/
def driftDiffTerm (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (f : Sp n → ℝ) (t : ℝ) : ℝ :=
  ∫ z, (∑ i, A z i * pd f i z + (1 / 2) * ∑ i, ∑ j, B z i j * pd2 f i j z) * p t z

/-- The `Δt → 0` limit of `Qjump`, before the change of variables `x ↔ z`. -/
def jumpPre (p : ℝ → Sp n → ℝ) (W : Sp n → Sp n → ℝ) (f : Sp n → ℝ) (t ε : ℝ) : ℝ :=
  ∫ q in farDiag ε, (f q.1 - f q.2) * (W q.1 q.2 * p t q.2)

/-- (3.4.15): the jump contribution, in the form in which it enters (3.4.16). -/
def jumpTerm (p : ℝ → Sp n → ℝ) (W : Sp n → Sp n → ℝ) (f : Sp n → ℝ) (t ε : ℝ) : ℝ :=
  ∫ z, f z * ∫ x in (ball z ε)ᶜ, (W z x * p t x - W x z * p t z)

end Gardiner
