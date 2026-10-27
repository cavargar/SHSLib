/-
# Itô stochastic differential equations with state-dependent coefficients (job E4)

Index of `SHSLib.Gardiner.Ito.StochDE.*` (Gardiner §4.3.1–§4.3.2, §4.4.2, §4.4.4,
§10.1.1–§10.1.4), namespace `Gardiner.Ito.StochDE`.  Everything is stated for a Wiener process
with respect to an arbitrary filtration, `Gardiner.Ito.IsFWiener W 𝓕 P`, and built on the Itô
calculus `SHSLib.Gardiner.Ito.Calculus.*` (job E3: `itoInt`, `IsItoIntegrand`, isometry,
martingale property, `geomBM`).  These files import only Mathlib and the E3 calculus.  The plan,
including the remaining work (Markov property §4.3.2), is
`research/docs/plans/plan_gardiner_ito_sde.md`.

## Files

| file | content |
| --- | --- |
| `Doob` | Doob's `L²` maximal inequality, discrete (`doob_L2_nat`) and continuous time (`doob_L2_contin`) |
| `Version` | jointly measurable adapted versions of continuous processes (`regVer`) and of drift integrals (`driftVer`) |
| `ContIto` | continuous version `itoCont` of `t ↦ ∫₀ᵗ G dW`; Doob's `L²` inequality for the Itô integral (`IsContItoVersion.doob`) |
| `Gronwall` | Gronwall's inequality in `ℝ≥0∞` (`gronwall_ennreal`) and the Picard iterate bound |
| `Basic` | conditions (4.3.10)–(4.3.11) (`SDECoeffs`), the noise integrand `drive`, solutions of (4.3.4) (`IsSDESol`) |
| `Estimate` | the basic estimate `E sup |Y|² ≤ 3 E ζ² + 3 (t-t₀) ∫ E A² + 12 ∫ E B²` (`sup_sq_le`) |
| `Wellposed` | moment bound, mean-square continuous dependence, uniqueness |
| `Picard` | Picard iteration and existence on every `[t₀, T]` (`existsUnique_sdeSol`) |
| `ItoIncr` | increments of the Itô integral; locality |
| `EulerDef` | the Euler / Cauchy–Euler scheme (`eulerSeq`) and its continuous interpolation |
| `Euler` | Hölder-½ condition, strong order ½ (`euler_strong_order_half`), convergence (`tendsto_euler`) |
| `Examples` | GBM, Ornstein–Uhlenbeck, and the nonlinear `dx = -sin x dt + σ dW` |
| `Restart` | restart (flow) property of solutions |

## Gardiner equation ↔ Lean

| Gardiner | Lean |
| --- | --- |
| (4.3.3)–(4.3.4) SDE / integral equation on `[t₀, T]` | `IsSDESol W 𝓕 P a b t₀ T ξ x`, `drive` |
| (4.3.10) Lipschitz condition, (4.3.11) growth condition | `SDECoeffs a b t₀ T K` |
| §4.3.1 existence (Picard / Cauchy–Euler) | `picardStep`, `picardSeq`, `sdeSol`, `isSDESol_sdeSol` |
| §4.3.1 uniqueness up to indistinguishability | `IsSDESol.unique`, `existsUnique_sdeSol` |
| moment bound `E sup_{t≤T} |x(t)|² ≤ C(1 + E|x(t₀)|²)` | `IsSDESol.supSq_le_const`, `sdeMomentConst`, `supSq` |
| mean-square continuous dependence on `x(t₀)` | `IsSDESol.supSq_sub_le` |
| Doob's `L²` inequality (used for the sup-estimates) | `doob_L2_nat`, `doob_L2_contin`, `IsContItoVersion.doob` |
| Gronwall's inequality | `gronwall_ennreal` |
| (4.3.5)–(4.3.9), (10.1.15) Euler scheme `x_{i+1} = x_i + a(x_i,t_i)Δt + b(x_i,t_i)ΔW_i` | `eulerGrid`, `eulerSeq`, `eulerSeq_succ`, `eulerInterp` |
| Hölder-½ condition in `t` (§10.1.4) | `SDEHolder` |
| (10.1.26) `E|x(T) - x_N|² ≤ C τ` (strong order ½) | `euler_strong_order_half`, `eulerErrConst`, `eulerC` |
| §4.3.1 convergence of the Cauchy–Euler approximations | `tendsto_euler` |
| §4.3.2 the future depends only on the present value | `IsSDESol.restart`, `IsSDESol.eq_sdeSol_restart` |
| §4.4.2 GBM `dx = λx dt + μx dW` | `sdeCoeffs_gbm`, `isSDESol_geomBM`, `geomBM_unique` |
| §4.4.4 OU `dx = -kx dt + √D dW` | `sdeCoeffs_ou`, `ouSDEPath`, `ou_unique_solution`, `ou_unique_solution_sqrt` |
| nonlinear example `dx = -sin x dt + σ dW` | `sdeCoeffs_sin`, `sdeHolder_sin`, `sinSDE_existsUnique`, `sinSDE_euler`, `sinSDE_tendsto_euler` |

## Discrepancies with the printed text

* Time origin: the E3 integral `itoInt` starts at time `0`, so all results assume `0 ≤ t₀`; the
  noise term `∫_{t₀}^t b dW` is `itoInt` of the integrand `1_{s > t₀} b(x(s), s)` (`drive`).
* (4.3.10)–(4.3.11) are assumed uniformly for `t ∈ [t₀, T]`, written as
  `|a(x,t) - a(y,t)| + |b(x,t) - b(y,t)| ≤ K|x - y|` and `|a|² + |b|² ≤ K²(1 + |x|²)`, together
  with joint measurability of `a`, `b` (implicit in Gardiner).
* A solution is required to be jointly measurable, adapted, almost surely continuous on
  `[t₀, T]` and square integrable on `(t₀, T] × Ω`; (4.3.4) holds almost surely for each `t`.
  Uniqueness is among such solutions.  The initial value must be `𝓕 t₀`-measurable and square
  integrable (Gardiner: independent of `W(t) - W(t₀)`).
* Gardiner sketches existence by the Cauchy–Euler limit; the formal existence proof uses Picard
  iteration, and Cauchy–Euler convergence is derived afterwards (under the extra Hölder-½
  condition) from the strong error bound.
* (10.1.25)–(10.1.26) are heuristic in Gardiner (order counting in `Δt`); here the bound
  `E|x(T) - x_N|² ≤ C τ` is proved with the explicit constant
  `eulerErrConst K (T - t₀) (E ξ²) = eulerC K d (1 + sdeMomentConst K d (1 + E ξ²)) e^{3 L d}`,
  `d = T - t₀`, `L = sdeRate K d`.  The extra Hölder-½ hypothesis in `t` (`SDEHolder`) is needed
  and is automatic for autonomous coefficients (`sdeHolder_autonomous`).
* The OU solution is given pathwise in integrated-by-parts form `ouSDEPath`,
  `x(t) = e^{-kt} x₀ + σ W(t) - kσ ∫₀ᵗ e^{-k(t-s)} W(s) ds`, which equals Gardiner's
  `e^{-kt}x₀ + σ∫₀ᵗ e^{-k(t-s)} dW(s)` (4.4.29) by Itô's product rule.
* GBM and OU are stated with `t₀ = 0` and need the joint measurability `Measurable (uncurry W)`.
* The Markov property `E[f(x(t)) | 𝓕 s] = (P_{s,t} f)(x(s))` (§4.3.2) is not yet formalized;
  only the restart property is.  See the plan.
-/
import SHSLib.Gardiner.Ito.StochDE.Doob
import SHSLib.Gardiner.Ito.StochDE.Version
import SHSLib.Gardiner.Ito.StochDE.ContIto
import SHSLib.Gardiner.Ito.StochDE.Gronwall
import SHSLib.Gardiner.Ito.StochDE.Basic
import SHSLib.Gardiner.Ito.StochDE.Estimate
import SHSLib.Gardiner.Ito.StochDE.Wellposed
import SHSLib.Gardiner.Ito.StochDE.Picard
import SHSLib.Gardiner.Ito.StochDE.ItoIncr
import SHSLib.Gardiner.Ito.StochDE.EulerDef
import SHSLib.Gardiner.Ito.StochDE.Euler
import SHSLib.Gardiner.Ito.StochDE.Examples
import SHSLib.Gardiner.Ito.StochDE.Restart
