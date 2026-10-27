/-
# Bridge: the SDE layer (E4) and generator layer (E5) → the rest of `Gardiner`

`SHSLib.Gardiner.Ito.StochDE` (job E4) and `SHSLib.Gardiner.Ito.Generator` (job E5) are stated
for an abstract filtered Wiener process `IsFWiener`, and were developed without access to the
rest of the library. This file connects them to:

* the standard Wiener process `stdWiener` (via `isFWiener_stdWiener` of `CalculusBridge`);
* the Euler map `Gardiner.SDE.eulerStep` and the Brownian grid increments `gridInc` of the
  Itô-free numerics layer (job D);
* the Fokker–Planck right-hand side `Gardiner.fpRHS` of Gardiner Ch. 3, in dimension one.

The connections to the categorical martingale problem (`SHSCat.GenPres`) and to Bect's weak
Dynkin formula (`GSHS.FPKData.WeakDynkin`) live in `SHSLib/Category/ItoDiffusion.lean` and
`SHSLib/FPK/ItoDiffusion.lean`, so that the `Gardiner` layer keeps its import closure.

| Lean | content |
| --- | --- |
| `stdFiltration` | the natural filtration of `stdWiener` |
| `existsUnique_sdeSol_stdWiener` | (4.3.10)–(4.3.11) ⇒ unique strong solution driven by `stdWiener` |
| `sinSDE_stdWiener` | `dx = −sin x dt + σ dW`, `x(0) = 0`, driven by `stdWiener`: a solution with `E|x(T) − x_N|² ≤ C τ` |
| `eulerSeq_succ` | E4's Euler–Maruyama step is job D's `eulerStep` |
| `eulerSeq_zero_succ_gridInc` | on the grid `nτ` the driving increments are job D's `gridInc` |
| `pd_comp_coord` | `∂/∂z₀ (g ∘ z₀) = g′ ∘ z₀` on `Sp 1` |
| `itoFPRHS_eq_fpRHS` | E5's `itoFPRHS` is Gardiner's `fpRHS` (3.5.6) in dimension one |
-/
import SHSLib.Gardiner.Ito.Generator
import SHSLib.Gardiner.Ito.CalculusBridge
import SHSLib.Gardiner.Ito.Schemes
import SHSLib.Gardiner.SDE.Schemes
import SHSLib.Gardiner.Special

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace Gardiner.Ito.SDEBridge

open StochDE Generator

/-! ### The standard Wiener process -/

/-- The natural filtration of the standard Wiener process. -/
abbrev stdFiltration : Filtration ℝ (inferInstance : MeasurableSpace StdWienerSpace) :=
  wienerFiltration stdWiener measurable_stdWiener

/-- **Existence and uniqueness (4.3.10)–(4.3.11) for the standard Wiener process**: under the
Lipschitz and growth conditions on `[t₀, T]`, the SDE driven by `stdWiener` has a solution,
unique up to indistinguishability. -/
theorem existsUnique_sdeSol_stdWiener {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} {ξ : StdWienerSpace → ℝ}
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (hξm : StronglyMeasurable[stdFiltration t₀] ξ) (hξ : MemLp ξ 2 stdWienerMeasure) :
    ∃ x, IsSDESol stdWiener stdFiltration stdWienerMeasure a b t₀ T ξ x ∧
      ∀ y, IsSDESol stdWiener stdFiltration stdWienerMeasure a b t₀ T ξ y →
        ∀ᵐ ω ∂stdWienerMeasure, ∀ t ∈ Set.Icc t₀ T, y t ω = x t ω :=
  existsUnique_sdeSol isFWiener_stdWiener hc ht₀ htT hξm hξ

/-- **A nonlinear SDE driven by the standard Wiener process.** `dx = −sin x dt + σ dW` with
`x(0) = 0` has a solution on `[0, Nτ]` whose Euler–Maruyama approximation on the grid of step
`τ` has mean-square error at most `eulerErrConst (1 + |σ|) (Nτ) 0 · τ` (strong order ½). -/
theorem sinSDE_stdWiener (σ : ℝ) {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    ∃ x, IsSDESol stdWiener stdFiltration stdWienerMeasure (fun y _ => -Real.sin y)
        (fun _ _ => σ) 0 (eulerGrid 0 τ N) (fun _ => 0) x ∧
      ∫ ω, (x (eulerGrid 0 τ N) ω -
          eulerSeq stdWiener (fun y _ => -Real.sin y) (fun _ _ => σ) 0 τ (fun _ => 0) N ω) ^ 2
          ∂stdWienerMeasure ≤
        eulerErrConst (1 + |σ|) (eulerGrid 0 τ N - 0) 0 * τ := by
  have hT : 0 ≤ eulerGrid 0 τ N := by
    unfold eulerGrid; positivity
  obtain ⟨x, hx, -⟩ := sinSDE_existsUnique isFWiener_stdWiener hT σ
    (x0 := fun _ => (0 : ℝ)) stronglyMeasurable_const (memLp_const 0)
  refine ⟨x, hx, ?_⟩
  have h := sinSDE_euler isFWiener_stdWiener σ hτ rfl
    (x0 := fun _ => (0 : ℝ)) stronglyMeasurable_const (memLp_const 0) hx
  simpa using h

/-! ### Job D's Euler map and Brownian grid increments -/

/-- E4's Euler–Maruyama recursion with time-homogeneous coefficients is job D's one-step map
`Gardiner.SDE.eulerStep`, driven by the Wiener increments. -/
theorem eulerSeq_succ {Ω : Type*} (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ) (t₀ τ : ℝ) (ξ : Ω → ℝ)
    (i : ℕ) (ω : Ω) :
    eulerSeq W (fun y _ => a y) (fun y _ => b y) t₀ τ ξ (i + 1) ω =
      Gardiner.SDE.eulerStep a b τ (eulerSeq W (fun y _ => a y) (fun y _ => b y) t₀ τ ξ i ω)
        (W (eulerGrid t₀ τ (i + 1)) ω - W (eulerGrid t₀ τ i) ω) := by
  simp [eulerSeq, Gardiner.SDE.eulerStep]

/-- On the grid `nτ` started at `0`, the driving increments of E4's Euler scheme are the
Brownian grid increments `gridInc` that the job-D moment theorems are applied to
(`SHSLib/Gardiner/Ito/Schemes.lean`). -/
theorem eulerSeq_zero_succ_gridInc {Ω : Type*} (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ) (τ : ℝ≥0)
    (ξ : Ω → ℝ) (i : ℕ) (ω : Ω) :
    eulerSeq W (fun y _ => a y) (fun y _ => b y) 0 τ ξ (i + 1) ω =
      Gardiner.SDE.eulerStep a b τ (eulerSeq W (fun y _ => a y) (fun y _ => b y) 0 τ ξ i ω)
        (gridInc W τ i ω) := by
  rw [eulerSeq_succ]
  congr 1
  simp [gridInc, dW, gridPts, eulerGrid]

/-! ### Gardiner's Fokker–Planck right-hand side in dimension one -/

/-- On `Sp 1 = ℝ¹`, the partial derivative of `g ∘ z₀` is `g′ ∘ z₀`. -/
theorem pd_comp_coord {g : ℝ → ℝ} (hg : Differentiable ℝ g) (w : Gardiner.Sp 1) :
    Gardiner.pd (fun v : Gardiner.Sp 1 => g (v 0)) 0 w = deriv g (w 0) := by
  have hp : HasFDerivAt (fun v : Gardiner.Sp 1 => v 0)
      (EuclideanSpace.proj (0 : Fin 1) : Gardiner.Sp 1 →L[ℝ] ℝ) w :=
    (EuclideanSpace.proj (0 : Fin 1) : Gardiner.Sp 1 →L[ℝ] ℝ).hasFDerivAt
  have h : HasFDerivAt (fun v : Gardiner.Sp 1 => g (v 0))
      (deriv g (w 0) • (EuclideanSpace.proj (0 : Fin 1) : Gardiner.Sp 1 →L[ℝ] ℝ)) w :=
    (hg (w 0)).hasDerivAt.comp_hasFDerivAt w hp
  rw [Gardiner.pd, h.fderiv]
  simp

/-- **E5's Fokker–Planck right-hand side is Gardiner's (3.5.6) in dimension one.** For
time-homogeneous coefficients and a density with the regularity the equation needs,
`-∂_y(a p) + ½ ∂²_y(b² p)` equals `Gardiner.fpRHS` with drift `A = a` and diffusion
`B = b²`, read on `Sp 1` through the coordinate `z₀`. -/
theorem itoFPRHS_eq_fpRHS (a b : ℝ → ℝ) (p : ℝ → ℝ → ℝ) (t : ℝ)
    (h1 : ContDiff ℝ 1 fun y => a y * p t y) (h2 : ContDiff ℝ 2 fun y => b y ^ 2 * p t y)
    (z : Gardiner.Sp 1) :
    itoFPRHS (fun y _ => a y) (fun y _ => b y) p t (z 0) =
      Gardiner.fpRHS (fun s (w : Gardiner.Sp 1) => p s (w 0)) (fun w _ => a (w 0))
        (fun w _ _ => b (w 0) ^ 2) t z := by
  have hd1 : Differentiable ℝ fun y => a y * p t y := h1.differentiable one_ne_zero
  have hd2 : Differentiable ℝ fun y => b y ^ 2 * p t y := h2.differentiable (by norm_num)
  have hd2' : Differentiable ℝ (deriv fun y => b y ^ 2 * p t y) :=
    (contDiff_one_deriv h2).differentiable one_ne_zero
  have e1 : Gardiner.pd (fun w : Gardiner.Sp 1 => a (w 0) * p t (w 0)) 0 z =
      deriv (fun y => a y * p t y) (z 0) := pd_comp_coord hd1 z
  have e2 : Gardiner.pd (fun w : Gardiner.Sp 1 => b (w 0) ^ 2 * p t (w 0)) 0 =
      fun w => deriv (fun y => b y ^ 2 * p t y) (w 0) := funext (pd_comp_coord hd2)
  have e3 : Gardiner.pd2 (fun w : Gardiner.Sp 1 => b (w 0) ^ 2 * p t (w 0)) 0 0 z =
      deriv (deriv fun y => b y ^ 2 * p t y) (z 0) := by
    rw [Gardiner.pd2, e2]; exact pd_comp_coord hd2' z
  simp only [itoFPRHS, Gardiner.fpRHS, Fin.sum_univ_one]
  rw [e1, e3]

end Gardiner.Ito.SDEBridge
