# Module: SHSLib.Gardiner.Approx

**File:** `SHSLib/Gardiner/Approx.lean` (index and correspondence table) + `SHSLib/Gardiner/Approx/*.lean` (14 modules)
**Layer:** Gardiner (textbook approximation methods)
**Status:** ✅ Complete (0 sorries, standard axioms only)
**Origin:** Aristotle project `198adb7c`

## What it proves

This layer formalizes the small-noise and system-size approximations of Gardiner, *Handbook of Stochastic Methods*: §6.1, §6.3, §7.1.2, §7.2.1–7.2.5 and §7.5, with the covariance equations of §4.4.6 and §4.4.9. Every derivation step is a theorem, and the main approximations carry explicit error terms.

A master equation is represented by its backward generator `L f(x) = Σ_j W_j(x)[f(x + r_j) − f(x)]`, or by the integral version of it. Error bounds are pointwise estimates on smooth test functions, each given together with its derivative tower.

What the layer covers:
- **Small-noise expansion.** The scaled-variable FPE (6.3.8), and the perturbation hierarchy (6.3.14) as an identity of formal power series. The moment, stationary-moment and autocorrelation hierarchies. The worked example of §6.3.2, solved exactly. The asymptotic stationary distribution and the Hamilton–Jacobi equation of §6.3.3.
- **X ⇌ A, exactly.** The exact solution of the master equation through its generating function (§7.1.2).
- **Kramers–Moyal and the jump→diffusion limit.**
  - The Kramers–Moyal expansion, with the truncation error bounded by the next jump moment.
  - The jump→diffusion limit (7.2.6) at an `O(√δ)` rate.
  - The random-walk, Poisson and birth–death examples.
  - The stationary limit (7.2.21) at an `O(δ)` rate.
- **Van Kampen's system-size expansion.** The fluctuation-variable generator differs from the linear-noise (OU) generator by `O(Ω^{-1/2})`, in one dimension and for chemical networks. The text's (7.2.35)/(7.2.40) is formalized with the corrected drift `α̃₁′(φ) z`.
- **Linear propensities.** The LNA mean and variance are exact: for X ⇌ A from the master equation itself, and for the CME with affine drift and diffusion.
- **Kurtz (7.2.64).** Taken as the coupling hypothesis `hcouple`. The characteristic-function deduction (7.2.65)–(7.2.67) is then proved with an explicit `O(V^{-1/2} log V)` constant.
- **Critical fluctuations.** The scaling exponent `μ = q/(q+1)`, and an `O(Ω^{-1/(q+1)})` generator bound at a degenerate fixed point.
- **Chemical networks.** Combinatorial kinetics and the chemical master equation (7.5.9), the chemical Fokker–Planck equation (7.5.30)–(7.5.32), the multivariate LNA, and the Lyapunov equation for its stationary covariance.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `Gardiner.vkGen_sub_lnaGen_le` | Fluctuation generator of a density-dependent master equation minus the LNA generator `α̃₁′(φ) z ∂_z + ½ α̃₂(φ) ∂_z²` is at most `Ω^{-1/2}` times explicit terms, including the third absolute jump moment |
| `Gardiner.mvkGen_sub_mlnaGen_le` | Same `O(Ω^{-1/2})` bound for multivariate chemical networks |
| `Gardiner.xa_vkGen_sub_lnaGen_le` | X ⇌ A instance of the bound; its only hypotheses concern the test function |
| `Gardiner.jumpGen_sub_kmGen_le`, `Gardiner.chem_KM_le` | Kramers–Moyal truncation at order `n` errs by at most `‖f⁽ⁿ⁺¹⁾‖/(n+1)!` times the `(n+1)`-th absolute jump moment |
| `Gardiner.scaled_jumpGen_rate` | (7.2.6) with an `O(√δ)` rate for the scaled kernel (7.2.1) |
| `Gardiner.randomWalk_rate`, `Gardiner.poisson_no_diffusion_limit` | Random walk → diffusion with an `O(δ)` error; the Poisson process has no diffusion limit |
| `Gardiner.bdStat_log_rate` | Birth–death stationary distribution → the potential solution (7.2.21), `O(δ)` |
| `Gardiner.snGen_sub_ouGen_le` | Small-noise generator (6.3.8) minus the OU generator (6.3.12) is `O(ε)` |
| `Gardiner.hierarchy_iff`, `Gardiner.smallNoise_moment_hierarchy` | Equating powers of ε as a theorem (6.3.14), and the moment hierarchy (6.3.18) |
| `Gardiner.xa_mean_variance_exact`, `Gardiner.xa_lna_exact` | X ⇌ A exact mean and variance; the LNA reproduces them exactly |
| `Gardiner.cme_lna_exact` | LNA mean and covariance are exact for the CME with affine drift and diffusion |
| `Gardiner.kurtz_charFun_le` | Kurtz coupling `|b − a| ≤ C log V` ⇒ characteristic functions of the fluctuations differ by `≤ |s| C log V/√V` |
| `Gardiner.critGen_sub_critLim_le`, `Gardiner.critical_exponent` | Critical slowing down: exponent `q/(q+1)` and the slow-time generator limit |
| `Gardiner.hamiltonJacobi_of_stationary`, `Gardiner.ou_hamiltonJacobi` | WKB form `exp(−φ/ε²)` of the stationary density gives the Hamilton–Jacobi equation (6.3.56); OU instance |
| `Gardiner.lyapunov_iff`, `Gardiner.lna_cov_stationary` | Stationary LNA covariance solves the Lyapunov equation (4.4.51) |

The full equation ↔ declaration table is the docstring of `SHSLib/Gardiner/Approx.lean`.

## Depends on

- [[Gardiner]], [[Gardiner]] (`Sp n`, `pd`, `pd2`, `fpRHS`), Mathlib

## Used by

- [[Gardiner.Adiabatic]], [[Gardiner.Escape]], [[Gardiner.SDE]]

## Open gaps / sorries

None. Caveats:
- **Generator-level bounds, not convergence of laws.** The `O(Ω^{-1/2})`, `O(√δ)` and `O(ε)` results are pointwise estimates on smooth test functions. Turning them into convergence of distributions would need a semigroup argument (Trotter–Kurtz), which is not formalized.
- **Kurtz's theorem itself is a hypothesis** (`hcouple`). `kurtz_charFun_lna_le` additionally assumes an `O(V^{-1/2})` law approximation `hy` for the coupled diffusion.
- **Limit interchanges are hypotheses.** Swapping `d/dt` with `∫`/`Σ` in the moment hierarchies is the named hypothesis `hswap` (with summability side conditions), as in the dCKE layer.
- **Non-vacuity.**
  - The 1-D LNA bound, KM truncation, the jump→diffusion rates and the exactness results have concrete instances: X ⇌ A, OU, the random walk, birth–death, and the §6.3.2 example.
  - The multivariate bound `mvkGen_sub_mlnaGen_le` and the full `cme_lna_exact` (on the exact Poisson solution of a burst model's CME) are instantiated in the research repository's bridge to stochastic hybrid systems, which is not part of this distribution.

## Notes

- **Errata.** Ten discrepancies with the printed text are formalized in corrected form; see the docstring of `Approx.lean`. The main ones:
  - (7.2.35)/(7.2.40): the drift is `α̃₁′(φ) z`, not `α̃₁(φ) z`.
  - (7.2.56)/(7.2.58): `k₁` for `k₂`, and `δ + δ²` for `δ − δ²`; the printed (7.2.58) is not normalisable.
  - (6.3.19)–(6.3.21), (6.3.28), (6.3.43), (6.3.51), (6.3.54): wrong indices, signs and coefficients.
  - (7.2.4): `α₂` carries an extra `δA²Q`.
