/-
# Numerical schemes driven by Brownian grid increments (Gardiner §10.1–§10.4)

The moment theorems of the Itô-free layer (`Gardiner.SDE.linScheme_moments` and the weak-error
and mean-square-stability theorems built on it) assume a driving sequence `ξ` with

  `∀ n, Measurable (ξ n)`,   `iIndepFun ξ P`,   `∀ n, P.map (ξ n) = gaussianReal 0 τ`.

For a Wiener process `W` (`Gardiner.Ito.IsWiener`) the grid increments
`ξₙ = W((n+1)τ) - W(nτ)` (`Gardiner.Ito.gridInc`) satisfy all three
(`Gardiner.Ito.IsWiener.gridInc_measurable`, `…gridInc_iIndepFun`, `…gridInc_map`).  So the
schemes of Ch. 10 can be driven by a genuine Brownian motion, as in (10.1.15)–(10.1.17):

* `Gardiner.Ito.IsWiener.linScheme_moments`: exact moment recursions;
* `Gardiner.Ito.exists_gaussian_increments_brownian`: the Brownian-driven version of
  `Gardiner.SDE.exists_gaussian_increments`, with the explicit sequence
  `ξ = gridInc stdWiener τ` of increments of the standard Wiener process;
* `Gardiner.Ito.IsWiener.ou_weak`, `…gbm_weak`, `…gbm_ms`: the weak-error and mean-square
  instances `Gardiner.SDE.ou_weak_instance`, `Gardiner.SDE.gbm_weak_instance`,
  `Gardiner.SDE.gbm_ms_instance` for schemes driven by Brownian increments;
* `Gardiner.Ito.ou_weak_stdWiener`: the same for the standard Wiener process.
-/
import SHSLib.Gardiner.Ito.Increments
import SHSLib.Gardiner.SDE.Examples

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

open Gardiner.SDE

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- The grid points `nτ`. -/
def gridPts (τ : ℝ≥0) (n : ℕ) : ℝ := n * τ

/-- The Brownian grid increments `ξₙ = W((n+1)τ) - W(nτ)` of (10.1.15)–(10.1.16). -/
def gridInc (W : ℝ → Ω → ℝ) (τ : ℝ≥0) : ℕ → Ω → ℝ := dW W (gridPts τ)

lemma gridPts_mono (τ : ℝ≥0) : Monotone (gridPts τ) := fun a b hab => by
  unfold gridPts; gcongr

namespace IsWiener

variable (hW : IsWiener W P)
include hW

lemma gridInc_measurable (τ : ℝ≥0) (n : ℕ) : Measurable (gridInc W τ n) :=
  hW.dW_measurable _ n

/-- The Brownian grid increments are independent. -/
theorem gridInc_iIndepFun (τ : ℝ≥0) : iIndepFun (gridInc W τ) P :=
  hW.dW_iIndepFun (gridPts_mono τ) (by simp [gridPts])

/-- The Brownian grid increments are `N(0, τ)`. -/
theorem gridInc_map (τ : ℝ≥0) (n : ℕ) : P.map (gridInc W τ n) = gaussianReal 0 τ := by
  rw [gridInc, hW.dW_map (gridPts_mono τ) (by simp [gridPts]) n]
  congr 1
  simp only [gridPts]
  push_cast
  rw [show ((n : ℝ) + 1) * τ - n * τ = τ by ring, Real.toNNReal_coe]

/-- **Exact moment recursions for linear schemes driven by Brownian increments**
(`Gardiner.SDE.linScheme_moments` with `ξ = gridInc W τ`). -/
theorem linScheme_moments (s : LinStep) (c : ℝ) (τ : ℝ≥0) (n : ℕ) :
    MemLp (linScheme s c (gridInc W τ) n) 2 P ∧
    ∫ ω, linScheme s c (gridInc W τ) (n + 1) ω ∂P =
      s.EG τ * ∫ ω, linScheme s c (gridInc W τ) n ω ∂P + s.EH ∧
    ∫ ω, linScheme s c (gridInc W τ) (n + 1) ω ^ 2 ∂P =
      s.EG2 τ * ∫ ω, linScheme s c (gridInc W τ) n ω ^ 2 ∂P +
      2 * s.EGH τ * ∫ ω, linScheme s c (gridInc W τ) n ω ∂P + s.EH2 τ := by
  have := hW.isProbabilityMeasure
  exact Gardiner.SDE.linScheme_moments s c (hW.gridInc_measurable τ) (hW.gridInc_iIndepFun τ)
    (hW.gridInc_map τ) n

/-- **Weak error, Ornstein–Uhlenbeck `dx = -x dt + dW`, driven by Brownian increments**
(`Gardiner.SDE.ou_weak_instance`). -/
theorem ou_weak {τ : ℝ≥0} (hτ : (τ : ℝ) ≤ 1 / 2) (N : ℕ) :
    |∫ ω, linScheme (eulerOU 1 1 τ) 1 (gridInc W τ) N ω ^ 2 ∂P - ouSecond 1 1 1 (N * τ)| ≤
        19 / 2 * (N * τ) * τ ∧
    |∫ ω, linScheme (semiOU 1 1 τ) 1 (gridInc W τ) N ω ^ 2 ∂P - ouSecond 1 1 1 (N * τ)| ≤
        29 / 2 * (N * τ) * τ ∧
    |∫ ω, linScheme (eulerOU 1 1 τ) 1 (gridInc W τ) N ω ∂P - ouMean 1 1 (N * τ)| ≤
        (N * τ) * Real.exp (N * τ) * τ := by
  have := hW.isProbabilityMeasure
  exact ou_weak_instance (hW.gridInc_measurable τ) (hW.gridInc_iIndepFun τ) (hW.gridInc_map τ)
    hτ N

/-- **Weak error, `dx = -x dt + x dW`, driven by Brownian increments**
(`Gardiner.SDE.gbm_weak_instance`). -/
theorem gbm_weak {τ : ℝ≥0} (hτ : (τ : ℝ) ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (eulerGBM (-1) 1 τ) 1 (gridInc W τ) N ω ∂P - gbmMean (-1) 1 (N * τ)| ≤
        (N * τ) * Real.exp (N * τ) * τ ∧
    |∫ ω, linScheme (eulerGBM (-1) 1 τ) 1 (gridInc W τ) N ω ^ 2 ∂P -
        gbmSecond (-1) 1 1 (N * τ)| ≤ 2 * (N * τ) * Real.exp (2 * (N * τ)) * τ ∧
    |∫ ω, linScheme (milsteinGBM (-1) 1 τ) 1 (gridInc W τ) N ω ^ 2 ∂P -
        gbmSecond (-1) 1 1 (N * τ)| ≤ 5 / 2 * (N * τ) * Real.exp (5 / 2 * (N * τ)) * τ ∧
    |∫ ω, linScheme (semiGBM (-1) 1 τ) 1 (gridInc W τ) N ω ∂P - gbmMean (-1) 1 (N * τ)| ≤
        17 / 8 * (N * τ) * Real.exp (17 / 8 * (N * τ)) * τ := by
  have := hW.isProbabilityMeasure
  exact gbm_weak_instance (hW.gridInc_measurable τ) (hW.gridInc_iIndepFun τ) (hW.gridInc_map τ)
    hτ N

/-- **Mean-square stability of `dx = -x dt + x dW` for schemes driven by Brownian increments**
(`Gardiner.SDE.gbm_ms_instance`). -/
theorem gbm_ms {τ : ℝ≥0} (hτ : 0 < (τ : ℝ)) :
    (Tendsto (fun n => ∫ ω, linScheme (eulerGBM (-1) 1 τ) 1 (gridInc W τ) n ω ^ 2 ∂P) atTop
        (𝓝 0) ↔ (τ : ℝ) < 1) ∧
    (Tendsto (fun n => ∫ ω, linScheme (milsteinGBM (-1) 1 τ) 1 (gridInc W τ) n ω ^ 2 ∂P) atTop
        (𝓝 0) ↔ (τ : ℝ) < 2 / 3) ∧
    Tendsto (fun n => ∫ ω, linScheme (implicitGBM (-1) 1 τ) 1 (gridInc W τ) n ω ^ 2 ∂P) atTop
      (𝓝 0) := by
  have := hW.isProbabilityMeasure
  exact gbm_ms_instance (hW.gridInc_measurable τ) (hW.gridInc_iIndepFun τ) (hW.gridInc_map τ) hτ

end IsWiener

/-- **Brownian-driven version of `Gardiner.SDE.exists_gaussian_increments`.**  The grid increments
of the standard Wiener process form an i.i.d. `N(0, τ)` sequence. -/
theorem exists_gaussian_increments_brownian (τ : ℝ≥0) :
    IsProbabilityMeasure stdWienerMeasure ∧ (∀ n, Measurable (gridInc stdWiener τ n)) ∧
      iIndepFun (gridInc stdWiener τ) stdWienerMeasure ∧
      ∀ n, stdWienerMeasure.map (gridInc stdWiener τ n) = gaussianReal 0 τ :=
  ⟨inferInstance, isWiener_stdWiener.gridInc_measurable τ,
    isWiener_stdWiener.gridInc_iIndepFun τ, isWiener_stdWiener.gridInc_map τ⟩

/-- **Instance:** the Euler and semi-implicit schemes for `dx = -x dt + dW`, `x(0) = 1`, driven by
the increments of the standard Wiener process on the grid `τ = 1/4`, have weak errors
`≤ (19/2)Tτ`, `≤ (29/2)Tτ` (second moment) and `≤ T e^T τ` (mean) at `T = N/4`. -/
theorem ou_weak_stdWiener (N : ℕ) :
    |∫ ω, linScheme (eulerOU 1 1 (1 / 4)) 1 (gridInc stdWiener (1 / 4)) N ω ^ 2 ∂stdWienerMeasure -
        ouSecond 1 1 1 (N * (1 / 4 : ℝ≥0))| ≤ 19 / 2 * (N * (1 / 4 : ℝ≥0)) * (1 / 4 : ℝ≥0) ∧
    |∫ ω, linScheme (semiOU 1 1 (1 / 4)) 1 (gridInc stdWiener (1 / 4)) N ω ^ 2 ∂stdWienerMeasure -
        ouSecond 1 1 1 (N * (1 / 4 : ℝ≥0))| ≤ 29 / 2 * (N * (1 / 4 : ℝ≥0)) * (1 / 4 : ℝ≥0) ∧
    |∫ ω, linScheme (eulerOU 1 1 (1 / 4)) 1 (gridInc stdWiener (1 / 4)) N ω ∂stdWienerMeasure -
        ouMean 1 1 (N * (1 / 4 : ℝ≥0))| ≤
        (N * (1 / 4 : ℝ≥0)) * Real.exp (N * (1 / 4 : ℝ≥0)) * (1 / 4 : ℝ≥0) :=
  isWiener_stdWiener.ou_weak (τ := 1 / 4) (by norm_num) N

end Gardiner.Ito
