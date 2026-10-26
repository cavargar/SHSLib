/-
# The general Itô integral and Itô's formula (job E3)

Index of the stochastic-calculus layer `SHSLib.Gardiner.Ito.Calculus.*` (Gardiner §4.2–§4.4).
Everything is stated for a Wiener process with respect to an arbitrary filtration,
`Gardiner.Ito.IsFWiener W 𝓕 P`; a process with `Gardiner.Ito.IsWiener W P` is one for its natural
filtration `Gardiner.Ito.wienerFiltration`.  These files import Mathlib only; the bridge to
`IsWiener`, `SimpleIntegrand`, `wienerInt`, `stdWiener` and the job-D GBM theorems is specified in
`research/docs/plans/plan_gardiner_ito_formula.md`.

| file | content |
| --- | --- |
| `Filtered` | `IsFWiener`; Gaussian moments of increments; independence from the past |
| `Elementary` | elementary (simple) integrands, their integral, isometry, martingale property |
| `Space` | `L²` helpers, the time–space measure `tsMeasure P T`, `IsItoIntegrand` |
| `Translation`, `Density` | density of elementary integrands in `L²(tsMeasure)` (§4.2.6) |
| `Integral` | `itoInt`: the isometric extension, mean (4.2.40), correlation (4.2.42), linearity |
| `Martingale` | `t ↦ ∫₀ᵗ G dW` is a martingale |
| `Riemann` | left-point Riemann sums converge to `itoInt` (§4.2.1); agreement with Riemann sums of continuous deterministic `f` |
| `Quadratic` | weighted quadratic variation; `∫₀ᵀ W dW = ½(W(T)² - T)` (4.2.20) |
| `Taylor`, `ItoPath` | deterministic (pathwise) core of Itô's formula |
| `ItoFormula` | Itô's formula (4.3.14) for `x = x₀ + ∫a dt + bW`, `F ∈ C^{1,2}` |
| `Growth` | exponential moments of `W`; moderate-growth functions satisfy the hypotheses |
| `ItoExamples` | (4.2.39) for `f(t, W)`; (4.2.37) `∫ Wⁿ dW`; (4.2.38) `d e^W` |
| `ItoProcess` | (4.3.14) for `eˣ` along `x = μt + σW` (nonzero drift); GBM moments with deterministic `x₀` |
| `MulLeft` | `∫ Z G dW = Z ∫ G dW` for bounded `𝓕 0`-measurable `Z` |
| `GBM` | geometric Brownian motion (4.4.3)–(4.4.13) and `dx = λx dt + μx dW` |
| `Moments` | moment equations of GBM and OU derived from Itô's formula |
| `Localize` | `∫₀ᵀ Z 1_{(s,t]} G dW = Z (∫₀ᵗ G dW - ∫₀ˢ G dW)`; conditional Itô isometry |
| `FourthMoment` | `E[(∫ G dW)⁴] ≤ 3 K⁴ (t - s)²` for `|G| ≤ K` supported in `(s, t]` |
| `QuadVar` | weighted quadratic variation of `∫ b dW`; Riemann sums against its increments |
| `ItoPathGen` | deterministic core of Itô's formula for a general Itô process |
| `ItoGeneral` | `IsItoProcess` (`dx = a dt + b dW`, random `b`); Itô's formula (4.3.14) for it |
| `ItoGeneralExamples` | `W` and `sin W` as Itô processes; (4.3.14) along `sin W` (random `b = cos W`) |
| `RiemannCont` | §4.2.1 for continuous adapted integrands dominated by `Y ∈ L²` (no mean-square continuity hypothesis); `cos W` instance |
| `MulLeftL2` | `∫ Z G dW = Z ∫ G dW` for unbounded `𝓕 0`-measurable `Z`; GBM solves `dx = λx dt + μx dW` for `x₀ ∈ L²` |
| `MomentsL2` | GBM mean / second-moment equations and ODEs from Itô's formula for `x₀ ∈ L²` / `x₀² ∈ L²` |
-/
import SHSLib.Gardiner.Ito.Calculus.Filtered
import SHSLib.Gardiner.Ito.Calculus.Elementary
import SHSLib.Gardiner.Ito.Calculus.Space
import SHSLib.Gardiner.Ito.Calculus.Translation
import SHSLib.Gardiner.Ito.Calculus.Density
import SHSLib.Gardiner.Ito.Calculus.Integral
import SHSLib.Gardiner.Ito.Calculus.Martingale
import SHSLib.Gardiner.Ito.Calculus.Riemann
import SHSLib.Gardiner.Ito.Calculus.Quadratic
import SHSLib.Gardiner.Ito.Calculus.Taylor
import SHSLib.Gardiner.Ito.Calculus.ItoPath
import SHSLib.Gardiner.Ito.Calculus.ItoFormula
import SHSLib.Gardiner.Ito.Calculus.Growth
import SHSLib.Gardiner.Ito.Calculus.ItoExamples
import SHSLib.Gardiner.Ito.Calculus.MulLeft
import SHSLib.Gardiner.Ito.Calculus.GBM
import SHSLib.Gardiner.Ito.Calculus.Moments
import SHSLib.Gardiner.Ito.Calculus.ItoProcess
import SHSLib.Gardiner.Ito.Calculus.Localize
import SHSLib.Gardiner.Ito.Calculus.FourthMoment
import SHSLib.Gardiner.Ito.Calculus.QuadVar
import SHSLib.Gardiner.Ito.Calculus.ItoPathGen
import SHSLib.Gardiner.Ito.Calculus.ItoGeneral
import SHSLib.Gardiner.Ito.Calculus.ItoGeneralExamples
import SHSLib.Gardiner.Ito.Calculus.RiemannCont
import SHSLib.Gardiner.Ito.Calculus.MulLeftL2
import SHSLib.Gardiner.Ito.Calculus.MomentsL2
