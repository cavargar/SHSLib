/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Example 18 of Bect (2010): Hespanha's generalized FPK equation, Eq. (33)

For a stochastic hybrid system whose jumps are driven by finitely many intensities
`λ_k` with deterministic reset maps `Ψ_k`, each a `C¹`-diffeomorphism with Jacobian
determinant `J_k`, the dual kernel of Eq. (32) (see `SHSLib.FPK.HespanhaResetJacobian`)
turns the source term `K^*(λ p_t)` of Corollary 15 into

  `Σ_k Σ_{y ∈ Ψ_k⁻¹({x})} (λ_k p_t / |J_k|)(y)`,

and Corollary 15 becomes Hespanha's generalized FPK equation

  `∂p/∂t (x, t) = (L^* p_t)(x) + Σ_k Σ_{y ∈ Ψ_k⁻¹({x})} ( (λ_k p_t / |J_k|)(y)
      − (λ_k p_t)(x) )`.                                                        (33)

Since each `Ψ_k` is a bijection, the inner sum has the single term `y = Ψ_k⁻¹(x)`.

What is formalized:

* `GSHS.hespanhaSourceDensity` — the source density of Eq. (33) (in `ℝ≥0∞`), and
  `GSHS.hespanhaSourceDensityReal` — its real-valued counterpart;
* `GSHS.lintegral_hespanha_source` — the duality identity that *identifies* it as the
  density of the source term `r_t K` with respect to `m`;
* `GSHS.hespanha_sink_eq` — the sink term is `λ p_t` with `λ = Σ_k λ_k`;
* `GSHS.hespanha_fpk_equation` — Eq. (33) itself, obtained from the measure-theoretic
  core of Theorem 13.
-/
import Mathlib
import SHSLib.FPK.HespanhaResetJacobian
import SHSLib.FPK.DensityEvolution

open MeasureTheory Set ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace GSHS

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]

variable {I : Type*} [Fintype I]

/-- The source density of Hespanha's equation (33), in `ℝ≥0∞`:
`Σ_k |J_k(Ψ_k⁻¹ y)|⁻¹ (λ_k p)(Ψ_k⁻¹ y)`.  Because each reset map is a bijection, the
inner sum `Σ_{y ∈ Ψ_k⁻¹({x})}` of the paper reduces to the single point `Ψ_k⁻¹(x)`. -/
def hespanhaSourceDensity (PsiInv : I → V → V) (Psi' : I → V → V →L[ℝ] V)
    (lam : I → V → ℝ≥0∞) (p : V → ℝ≥0∞) (y : V) : ℝ≥0∞ :=
  ∑ k : I, ENNReal.ofReal |(Psi' k (PsiInv k y)).det|⁻¹ * (lam k (PsiInv k y) * p (PsiInv k y))

/-- The real-valued source density of Eq. (33). -/
def hespanhaSourceDensityReal (PsiInv : I → V → V) (Psi' : I → V → V →L[ℝ] V)
    (lam : I → V → ℝ) (p : V → ℝ) (y : V) : ℝ :=
  ∑ k : I, |(Psi' k (PsiInv k y)).det|⁻¹ * (lam k (PsiInv k y) * p (PsiInv k y))

/-- The sink density `λ p` of Eq. (33), with the total intensity `λ = Σ_k λ_k`. -/
def hespanhaSink (lam : I → V → ℝ) (p : V → ℝ) (x : V) : ℝ :=
  ∑ k : I, lam k x * p x

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The sink term of Eq. (33) is `λ p_t` with the total intensity `λ = Σ_k λ_k`. -/
theorem hespanha_sink_eq (lam : I → V → ℝ) (p : V → ℝ) (x : V) :
    hespanhaSink lam p x = (∑ k : I, lam k x) * p x := by
  rw [hespanhaSink, ← Finset.sum_mul]

variable {Psi PsiInv : I → V → V} {Psi' : I → V → V →L[ℝ] V}

/-- **Identification of the source density of Eq. (33).**

Testing the source term `r_t K = Σ_k (λ_k p_t) m ∘ Ψ_k⁻¹` against a nonnegative
measurable function `g` gives `∫ g · s dm` with
`s = Σ_k |J_k(Ψ_k⁻¹ ·)|⁻¹ (λ_k p_t)(Ψ_k⁻¹ ·)`, so `s` is the density of the source term
with respect to `m`.  This is Eq. (32) of Example 18 applied to each reset map and summed
over `k`. -/
theorem lintegral_hespanha_source
    (hderiv : ∀ k x, HasFDerivAt (Psi k) (Psi' k x) x)
    (hdet : ∀ k x, (Psi' k x).det ≠ 0)
    (hleft : ∀ k, LeftInverse (PsiInv k) (Psi k))
    (hright : ∀ k, RightInverse (PsiInv k) (Psi k))
    (lam : I → V → ℝ≥0∞) (p g : V → ℝ≥0∞)
    (hmeas : ∀ k, Measurable fun y =>
      ENNReal.ofReal |(Psi' k (PsiInv k y)).det|⁻¹ * (lam k (PsiInv k y) * p (PsiInv k y)) * g y) :
    ∑ k : I, ∫⁻ x, lam k x * p x * g (Psi k x) ∂m
      = ∫⁻ y, hespanhaSourceDensity PsiInv Psi' lam p y * g y ∂m := by
  have hk : ∀ k : I, ∫⁻ x, lam k x * p x * g (Psi k x) ∂m
      = ∫⁻ y, ENNReal.ofReal |(Psi' k (PsiInv k y)).det|⁻¹
          * (lam k (PsiInv k y) * p (PsiInv k y) * g y) ∂m := by
    intro k
    exact lintegral_deterministic_reset_dual m (Psi := Psi k) (PsiInv := PsiInv k)
      (Psi' := Psi' k) (fun x => hderiv k x) (fun x => hdet k x) (hleft k) (hright k)
      (fun x y => lam k x * p x * g y)
  have hsum : ∫⁻ y, hespanhaSourceDensity PsiInv Psi' lam p y * g y ∂m
      = ∑ k : I, ∫⁻ y, ENNReal.ofReal |(Psi' k (PsiInv k y)).det|⁻¹
          * (lam k (PsiInv k y) * p (PsiInv k y) * g y) ∂m := by
    rw [show (fun y => hespanhaSourceDensity PsiInv Psi' lam p y * g y)
        = fun y => ∑ k : I, (ENNReal.ofReal |(Psi' k (PsiInv k y)).det|⁻¹
          * (lam k (PsiInv k y) * p (PsiInv k y)) * g y) from by
      funext y; rw [hespanhaSourceDensity, Finset.sum_mul]]
    rw [lintegral_finset_sum _ (fun k _ => hmeas k)]
    exact Finset.sum_congr rfl fun k _ => lintegral_congr fun y => by ring
  rw [hsum]
  exact Finset.sum_congr rfl fun k _ => hk k

omit [FiniteDimensional ℝ V] [BorelSpace V] [m.IsAddHaarMeasure] in
/-- **Hespanha's generalized FPK equation (33)** (Bect (2010), Example 18).

With `dp` the density of `μ'_t`, `Fp` the density of the absolutely continuous part of
`L^* μ_t`, and the source and sink densities identified above, the measure-theoretic core
of Theorem 13 turns the generalized FPK equation into

`∂p/∂t (x) = (L^* p_t)(x) + Σ_k ( (λ_k p_t)(Ψ_k⁻¹ x) / |J_k(Ψ_k⁻¹ x)| − (λ_k p_t)(x) )`

`m`-almost everywhere on the region `U` where all the terms are absolutely continuous. -/
theorem hespanha_fpk_equation [SigmaFinite m] (U : Set V) {dp Fp : V → ℝ}
    (lam : I → V → ℝ) (p : V → ℝ)
    (hdp : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ →
      IntegrableOn dp s (m.restrict U))
    (hrhs : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ →
      IntegrableOn (fun x => Fp x + hespanhaSourceDensityReal PsiInv Psi' lam p x
        - hespanhaSink lam p x) s (m.restrict U))
    (hbal : ∀ s, MeasurableSet s → (m.restrict U) s < ⊤ →
      ∫ x in s, dp x ∂(m.restrict U)
        = ∫ x in s, (Fp x + hespanhaSourceDensityReal PsiInv Psi' lam p x
            - hespanhaSink lam p x) ∂(m.restrict U)) :
    dp =ᵐ[m.restrict U] fun x => Fp x
      + ∑ k : I, (|(Psi' k (PsiInv k x)).det|⁻¹ * (lam k (PsiInv k x) * p (PsiInv k x))
          - lam k x * p x) := by
  have h := theorem13_pdf_evolution (m := m) U hdp hrhs hbal
  refine h.trans (Filter.Eventually.of_forall fun x => ?_)
  simp only [hespanhaSourceDensityReal, hespanhaSink, Finset.sum_sub_distrib]
  ring

end GSHS
