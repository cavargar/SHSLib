# Module: SHSLib.Gardiner.Ito

**File:** `SHSLib/Gardiner/Ito.lean` (index and correspondence table) + `SHSLib/Gardiner/Ito/*.lean` (14 modules) + `SHSLib/Gardiner/Ito/Calculus/*.lean` (28 modules, index `Calculus.lean`)
**Layer:** Gardiner Ch. 4 (the Itô calculus)
**Status:** ✅ Complete (0 sorries, standard axioms only)
**Origin:** Aristotle projects `24b4e185`, `36ce5887`, `5be33f27`; `CalculusBridge` written by hand

## What it proves

| Module | Content |
|---|---|
| `Wiener` | `IsWiener W P` is the SHSLib interface to a standard Wiener process on real time `t ≥ 0`. Fields: zero at 0, a.s. continuous paths, `N(0, t−s)` increments, independent increments, and future increments independent of `wienerFiltration W` (the natural filtration). Mathlib-only. Martingale property: `IsWiener.condExp_eq`. |
| `Brownian` | **Only importer of the dependency** (`BrownianMotion.Gaussian.BrownianMotion`). `stdWiener t = brownian t.toNNReal` under `gaussianLimit`, `isWiener_stdWiener`, `continuous_stdWiener` (every path), `exists_wiener`. |
| `Increments` | Gardiner §4.2.2 and §4.2.5. Partition increments are i.i.d. `N(0, Δtᵢ)` (`dW_iIndepFun`, `dW_map`). Quadratic variation has exact mean-square error `2ΣΔtᵢ²` → 0 (`qv_ms_error`, `qv_msLim`). The left-point Itô sum has exact error `½ΣΔtᵢ²`, which gives (4.2.20) (`itoSum_ms_error`, `itoSum_msLim`). `ito_sum_of_qv_ms` discharges `Gardiner.SDE.ito_sum_of_qv`'s QV hypothesis in mean square. Erratum: `eq_4_2_18_printed_wrong`. |
| `Scaling` | (6.2.40) as a law-level statement: `√ε W(τ/ε)` is again a Wiener process (`IsWiener.scale`). Combined with the pathwise `Gardiner.SDE.cubic_scaling` in `cubic_scaling_wiener`. |
| `Pathwise` | The pathwise results of [[Gardiner.SDE]] hold a.s. for Brownian paths: existence of `IsPathSol`, Euler convergence, the linearisation and cubic small-noise expansions. Instances with drift `−sin` driven by `stdWiener`. |
| `Schemes` | Brownian grid increments satisfy the hypotheses of `Gardiner.SDE.linScheme_moments`. Hence `exists_gaussian_increments_brownian` and the Brownian-driven OU/GBM weak-error and GBM mean-square results. |
| `Simple` | Itô integral of simple nonanticipating integrands against any `IsWiener` (§4.2.1, §4.2.4, §4.2.6 e–f): linearity, mean zero (4.2.40)–(4.2.41), Itô isometry / correlation formula (4.2.42)–(4.2.44), martingale property of the running integral (`SimpleIntegrand.integral_mean`, `integral_mul`, `martingale_running`). |
| `MSLimit` | Mean-square limits in L²: existence, uniqueness, passing correlations to the limit, and Gaussian limits. |
| `WienerIntegral` | `wienerInt W P f a b` is the ms-limit of left-point Riemann sums. For continuous `f` it exists (`wienerInt_spec`) and is `N(0, ∫f²)` (`wienerInt_map`), with covariance `∫_a^{min} fg`. Pairs on a common interval are jointly Gaussian. Integration by parts for C¹ `f` holds a.s. (`wienerInt_ibp`). |
| `WienerStep` | For step functions, the Wiener integral equals the simple integral a.s. (`wienerInt_step`). |
| `WienerInstances` | `stdWiener` instances, e.g. `∫₀¹ s dW ~ N(0, 1/3)`. |
| `Linearised` | `x₁(t) = ∫₀ᵗ b e^{−∫k} dW` satisfies `Gardiner.SDE.IsLinearisedLaw` (`isLinearisedLaw_linProc`), so (6.2.31)–(6.2.32) hold unconditionally. It equals the pathwise first-order hierarchy term a.s. (`hierarchy_first_order_ae`). |
| `OU` | §4.4.4: the OU process solves `IsPathSol` with `a(x) = −kx` (`ouProc_isPathSol`). Mean (4.4.27), variance (4.4.29), correlation (4.4.30, including the printed `e^{−k|t−s|}` form), Gaussian law, stationary limit. For deterministic `x(0)` its moments equal `ouMean`/`ouSecond`, so `ou_weak_process` compares the schemes with the real OU process. |
| `Multiple` | (10.1.9)–(10.1.12): `(ΔW, ΔZ)` is jointly Gaussian with covariances `τ, τ²/2, τ³/3`; `ξ, η` are independent standard normals realising `multipleIntegral_moments`; companion identity `∫dW∫ds = τΔW − ΔZ` a.s. Erratum: the printed (10.1.10)/(10.1.11) are identical. |
| `Calculus/*` | Mathlib-only. Stated for `IsFWiener W 𝓕 P`, a Wiener process for an arbitrary filtration, whose fields are those of `IsWiener` with `𝓕 = wienerFiltration`; `CalculusBridge` makes every result apply to `stdWiener`. Contents: the L² Itô integral `itoInt` for `IsItoIntegrand`s, with elementary integrands dense (`exists_elem_approx`); mean (4.2.40), correlation (4.2.42), martingale (`martingale_itoInt`); left-point Riemann sums converge, including for continuous adapted dominated integrands (`itoRiemann_tendsto_of_continuousOn`); (4.2.20) `itoInt_W`, (4.2.37) `itoInt_pow`; Itô's formula (4.3.14) along `IsItoProcess` with random bounded `b` (`ito_formula_process_C2`), (4.2.39) for `f(t,W)`; GBM (4.4.3)–(4.4.13) including Stratonovich-form moments, `geomBM_ito_of_memLp` for `x₀ ∈ L²`; GBM/OU moment ODEs derived from Itô's formula (`Moments`, `MomentsL2`). |
| `CalculusBridge` | `IsWiener.isFWiener`: every `IsWiener` process is an `IsFWiener` process for its natural filtration, so all of `Calculus/*` applies to `stdWiener` (`isFWiener_stdWiener`, `measurable_uncurry_stdWiener`). `IsWiener.itoInt_det_eq_wienerInt`: `itoInt` = `wienerInt` a.s. for continuous deterministic `f`. GBM moments = `Gardiner.SDE.gbmMean`/`gbmSecond` (`IsWiener.integral_geomBM_const`, `integral_geomBM_sq_const`). Instances: (4.2.20) `itoInt_W_stdWiener`, `geomBM_ito_stdWiener`, `∫₀¹ s dW` both ways, `E[exp(W−t/2)²] = eᵗ`. |

Instances: every main theorem is instantiated with `stdWiener`. On the uniform partition of `[0,1]` the QV and Itô-sum errors are `2/n` and `1/(2n)`.

## Depends on

[[Gardiner.SDE]], the pinned `brownian-motion` dependency (see the README; only `Brownian.lean` imports it, and only the sorry-free module `BrownianMotion.Gaussian.BrownianMotion`), and Mathlib's filtrations, conditional expectation and Gaussian measures.

## Open gaps

- The Wiener integral is proved to converge for continuous and step integrands only, not for all of `L²[0,T]`. Joint Gaussian laws are proved only for pairs of integrals on a common interval.
- Not yet proved: agreement of `itoInt` with the `SimpleIntegrand` integral of `Simple`, and the GBM weak-error and mean-square theorems of [[Gardiner.SDE]] restated against the process `geomBM` (as `ou_weak_process` does for OU).
- Itô's formula needs a bounded noise coefficient `b`; unbounded random `b` requires localization by stopping times.
- No existence/uniqueness theory for SDEs with state-dependent coefficients yet, hence no strong-convergence results for the numerical schemes.
- (4.4.31) (start at −∞) is formalized as the `t → ∞` limit of the moments, not as an integral over `(−∞, t]`.
