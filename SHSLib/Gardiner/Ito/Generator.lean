/-
# Generator, Dynkin's formula and the Fokker–Planck equation for Itô SDEs (job E5)

Index of `SHSLib.Gardiner.Ito.Generator.*` (Gardiner §4.3.4, with the §4.3.2 Markov property for
two explicit SDEs), namespace `Gardiner.Ito.Generator`.  Everything is stated for a Wiener
process with respect to an arbitrary filtration, `Gardiner.Ito.IsFWiener W 𝓕 P`.  Built on the
Itô calculus of job E3 (`IsItoProcess`, `itoInt`, `condExp_itoInt`, `itoInt_mean`,
`ito_formula_process`, `ito_formula_process_C2`) and the SDE layer of job E4 (`SDECoeffs`,
`IsSDESol`, `memLp_apply`, `isItoIntegrand_drive`, `existsUnique_sdeSol`, the GBM/OU/sin
examples).  Plan and remaining work: `research/docs/plans/plan_gardiner_ito_bridges.md`.

## Files

| file | content |
| --- | --- |
| `Basic` | generator `itoGen`, Dynkin process `itoDynkinProc`, `IsMartingaleOn`, test functions `C2BddDeriv` |
| `Dynkin` | Itô processes with coefficients `a(x,t)`, `b(x,t)` (`IsItoDiffusion`): Itô formula in generator form, Dynkin's formula, martingale problem (on `[0,T]` and Mathlib form) |
| `SDE` | the same for solutions of Lipschitz SDEs (`IsSDESol`), via the stopped process `clampProc` |
| `WeakFP` | weak Fokker–Planck equation for the law `lawAt P x t`, integrated and differential forms |
| `StrongFP` | integration by parts, (4.3.19) ⇒ (4.3.20), strong FPE for SDE solutions with a regular density |
| `Gaussian` | Gaussian densities `gaussDens`; they solve the FPE of linear SDEs |
| `Examples` | OU (explicit Gaussian solution, stationary density, Dynkin, weak FPE, martingale problem); Wiener process as an instance of the strong FPE; nonlinear `dx = -sin x dt + σ dW` |
| `ExamplesGBM` | geometric Brownian motion: Itô formula, Dynkin, weak FPE; martingale problem of `W` in Mathlib form |
| `Markov` | freezing lemma; Markov property of `W` and of GBM |

## Gardiner equation ↔ Lean

| Gardiner | Lean |
| --- | --- |
| generator `a ∂ₓf + ½ b² ∂ₓ²f` (r.h.s. of (4.3.18)) | `itoGen a b f t y` |
| Itô's formula (4.3.14) for `f(x(t))`, `dx = a(x,t)dt + b(x,t)dW` | `ito_formula_itoGen` |
| (4.3.18) integrated: `⟨f(x(t))⟩ = ⟨f(x(s))⟩ + ⟨∫ₛᵗ L f⟩` | `dynkin`, `dynkin_zero`, `IsSDESol.dynkin` |
| `⟨f(x(t)) - f(x(0)) - ∫₀ᵗ Lf⟩ = 0` | `integral_itoDynkinProc` |
| martingale problem | `isMartingaleOn_itoDynkinProc`, `IsSDESol.isMartingaleOn_itoDynkinProc`, `martingale_itoDynkinProc_clamp`, `IsSDESol.martingale_itoDynkinProc_clamp` |
| (4.3.18)–(4.3.19) `d/dt ∫ f p = ∫ (a ∂ₓf + ½ b² ∂ₓ²f) p` (weak form, law `μ_t`) | `weakFP_hasDerivWithinAt`, `weakFP_hasDerivAt`, `weakFP_integrated`, `IsSDESol.weakFP_*` |
| integration by parts, surface terms discarded | `integral_ibp_generator`, `integral_itoGen_mul_density` |
| `d/dt ∫ f p = ∫ f ∂ₜp` | `hasDerivAt_integral_mul_density` |
| r.h.s. of (4.3.20) `-∂ₓ[a p] + ½ ∂ₓ²[b² p]` | `itoFPRHS a b p t y` |
| (4.3.20) from (4.3.19) "since `f(x)` is arbitrary" | `strongFP_of_weakFP`, `IsSDESol.strongFP` |
| §4.4.4 OU: Gaussian solution of the FPE, mean (4.4.30), variance (4.4.31) | `ou_density_fokkerPlanck`, `ouMean`, `ouVar`, `ou_stationary_fokkerPlanck` |
| OU: Dynkin / weak FPE / martingale problem | `ou_dynkin`, `ou_weakFP`, `ou_isMartingaleOn` |
| §4.4.2 GBM: Dynkin, weak FPE | `gbm_ito_formula`, `gbm_dynkin`, `gbm_weakFP_integrated` |
| nonlinear `dx = -sin x dt + σ dW` | `sin_dynkin`, `sin_weakFP`, `sin_weakFP_integrated`, `sin_isMartingaleOn`, `sinSDE_exists_dynkin_weakFP` |
| heat equation for `W` (FPE with `a = 0`, `b = 1`) | `wiener_strongFP`, `isSDESol_wiener` |
| §4.3.2 Markov property `E[f(x(t)) | 𝓕 s] = (P_{s,t}f)(x(s))` | `wiener_markov` (`wienerTrans`), `gbm_markov` (`gbmTrans`), freezing lemma `condExp_freeze` |

## Correspondence with existing SHSLib definitions (not imported)

* `SHSCat.GenPres.SolvesMartingaleProblem A P ℱ X` = `∀ φ, Martingale (A.dynkinProcess φ X) ℱ P`.
  With `A.State = ℝ`, `A.Test` = test functions, `A.ev φ = φ`, `A.gen φ = itoGen a b φ 0` for
  autonomous `a`, `b` (`itoGen_autonomous`), `A.dynkinProcess φ X t = itoDynkinProc a b φ X t`
  (definitionally the same expression `φ(X t) - φ(X 0) - ∫₀ᵗ Lφ(X s) ds`).  Our
  `martingale_itoDynkinProc_clamp` gives `Martingale` for the process stopped at `T`
  (`X = x((t ∨ 0) ∧ T)`); `SolvesMartingaleProblem` itself needs a solution on `[0, ∞)`.
* `SHSCat.GenPres.SatisfiesDynkin` ↔ `dynkin_zero` / `IsSDESol.dynkin` with `s = 0`, `t ≤ T`;
  `SatisfiesForward` (right derivative on `Ici t`) ↔ `weakFP_hasDerivWithinAt` (within `[0, T]`).
* `GSHS.FPKData` with `ev φ = φ`, `gen φ = itoGen a b φ t`, `law t = lawAt P x t`, `r = 0`:
  `WeakDynkin` (`lawPair t φ - lawPair 0 φ = ∫₀ᵗ genPair s φ + ∫₀ᵗ jumpPair s φ`, jump term `0`)
  ↔ `weakFP_integrated` / `IsSDESol.weakFP_integrated` (for `t ≤ T`; `FPKData.gen` is
  time-independent, so autonomous coefficients are needed for a literal match).
  `GSHS.generatorL f0 f gphi ddphi x` in dimension `n = r = 1` is
  `f0 x 0 * gphi 0 + 2⁻¹ * (f 0 x 0)² * ddphi 0 0`, i.e. `itoGen` with `a = f0`, `b = f 0`,
  `gphi 0 = f'(x)`, `ddphi 0 0 = f''(x)`.
* `Gardiner.fpRHS p A B t z = -(Σᵢ ∂ᵢ(Aᵢ p)) + ½ Σᵢⱼ ∂ᵢ∂ⱼ(Bᵢⱼ p)` in dimension `1` with
  `A = a(·, t)`, `B = b(·, t)²` is `itoFPRHS a b p t z`; `Gardiner.fokkerPlanck` corresponds to
  `strongFP_of_weakFP` / `IsSDESol.strongFP`.

## Discrepancies with the printed equations

* (4.3.18) is stated in Gardiner for arbitrary `f`; here `f ∈ C²` with bounded `f'`, `f''`
  (Dynkin, martingale problem) or `f ∈ C²_c` (weak FPE).  Integrability of `f(x(t))` is assumed
  for general Itô processes and derived (from `E x(t)² < ∞`) for SDE solutions.
* The SDE results assume, beyond the Lipschitz/growth conditions, that `a`, `b` are jointly
  continuous and `b` is bounded, and they start at `t₀ = 0`.  These come from the E3 Itô formula
  (continuous drift/noise paths, bounded noise coefficient).  GBM (unbounded `b = μx`) is
  handled separately through `φ(X(t)) = F(t, W(t))`, with deterministic `x₀`.
* Gardiner's `d/dt⟨f⟩` is a two-sided derivative; here it is a derivative within `[0, T]`
  (two-sided in `(0, T)`).
* (4.3.20) is derived under explicit regularity hypotheses on the density (see `StrongFP`); the
  density is that of the law `μ_t` (for a deterministic or random `x(0)`), Gardiner's
  `p(x, t | x₀, t₀)` being the case of deterministic `x(0) = x₀`.
* The OU density theorem verifies (4.3.20) for the Gaussian `N(x₀e^{-kt}, D(1-e^{-2kt})/2k)`;
  that this is the law of the OU solution (Gaussianity of Wiener integrals) is not formalized.
  For the Wiener process the law is known (`IsFWiener.map_eval`), giving `wiener_strongFP`.
-/
import SHSLib.Gardiner.Ito.Generator.Basic
import SHSLib.Gardiner.Ito.Generator.Dynkin
import SHSLib.Gardiner.Ito.Generator.SDE
import SHSLib.Gardiner.Ito.Generator.WeakFP
import SHSLib.Gardiner.Ito.Generator.StrongFP
import SHSLib.Gardiner.Ito.Generator.Gaussian
import SHSLib.Gardiner.Ito.Generator.Examples
import SHSLib.Gardiner.Ito.Generator.ExamplesGBM
import SHSLib.Gardiner.Ito.Generator.Markov
