/-
# Wiener process and the first Itô computations (Gardiner §3.8.1, §4.2.2, §4.2.5, (6.2.40))

Index of the Brownian-motion layer.  It connects a genuine Brownian motion (from the
`brownian-motion` dependency, see `research/wiki/Dependencies.md`) to Gardiner Ch. 4 and to the
Itô-free SDE layer `SHSLib.Gardiner.SDE`, and is the base on which later jobs build the Itô
integral, the Itô formula and SDE solutions.  Plans: `research/docs/plans/plan_gardiner_ito_bm.md`
(job E1) and `research/docs/plans/plan_gardiner_ito_wiener.md` (job E2: simple and Wiener
integrals).
Conventions as in `SHSLib.Gardiner.SDE`:

* all declarations are in the namespace `Gardiner.Ito`;
* **one interface, one adapter.**  Results are stated for any `W : ℝ → Ω → ℝ` with
  `Gardiner.Ito.IsWiener W P` (`SHSLib.Gardiner.Ito.Wiener`, Mathlib only).  The concrete standard
  Wiener process `Gardiner.Ito.stdWiener` comes from the adapter `SHSLib.Gardiner.Ito.Brownian`,
  the only file that imports the dependency (and only `BrownianMotion.Gaussian.BrownianMotion`).
  A switch to Mathlib's Brownian motion replaces that file only;
* time is real, `t ≥ 0`; values at negative times are unconstrained by the interface;
* every main theorem has a non-degenerate instance for `Gardiner.Ito.stdWiener`.

## Guarantees with explicit error terms

| Guarantee | Lean |
| --- | --- |
| a standard Wiener process on real time exists, with continuous paths and its natural filtration | `Gardiner.Ito.isWiener_stdWiener`, `Gardiner.Ito.continuous_stdWiener`, `Gardiner.Ito.exists_wiener` |
| martingale property `E[W t ∣ 𝓕 s] = W s` | `Gardiner.Ito.IsWiener.condExp_eq` |
| increments over a partition are independent and `N(0, Δtᵢ)` | `Gardiner.Ito.IsWiener.dW_iIndepFun`, `Gardiner.Ito.IsWiener.dW_map` |
| quadratic variation: `⟨(Σ ΔWᵢ² - (t - t₀))²⟩ = 2 Σ Δtᵢ² ≤ 2δ(t - t₀)` (mesh `δ`) | `Gardiner.Ito.IsWiener.qv_ms_error`, `Gardiner.Ito.IsWiener.qv_ms_le` |
| `∫W dW`: `⟨(Σ W(tᵢ₋₁)ΔWᵢ - ½[W(t)² - W(t₀)² - (t - t₀)])²⟩ = ½ Σ Δtᵢ²` | `Gardiner.Ito.IsWiener.itoSum_ms_error` |
| instances, uniform partition of `[0, 1]`: `2/n` and `1/(2n)` | `Gardiner.Ito.qv_unif_instance`, `Gardiner.Ito.itoSum_unif_instance` |
| Brownian scaling: `√ε W(τ/ε)` is again a Wiener process | `Gardiner.Ito.IsWiener.scale`, `Gardiner.Ito.stdWiener_scale` |
| Euler scheme driven by a Brownian path converges to the pathwise solution, a.s. | `Gardiner.Ito.IsWiener.ae_euler_tendsto`, `Gardiner.Ito.euler_sin_stdWiener` |
| small-noise linearisation driven by a Brownian path: `|x - εx₁| ≤ Cε²`, a.s. | `Gardiner.Ito.IsWiener.ae_sin_linearisation`, `Gardiner.Ito.sin_linearisation_stdWiener` |
| Brownian grid increments satisfy the hypotheses of the Ch. 10 moment theorems | `Gardiner.Ito.IsWiener.gridInc_measurable`, `Gardiner.Ito.IsWiener.gridInc_iIndepFun`, `Gardiner.Ito.IsWiener.gridInc_map` |
| simple integrals: `⟨∫G dW⟩ = 0`, `⟨∫G dW ∫H dW⟩ = ∫ ds ⟨G(s)H(s)⟩`, running integral is a martingale | `Gardiner.Ito.SimpleIntegrand.integral_mean`, `Gardiner.Ito.SimpleIntegrand.integral_mul`, `Gardiner.Ito.SimpleIntegrand.martingale_running`, `Gardiner.Ito.simpleExample_moments` |
| Wiener integral: `∫ₐᵇ f dW ~ N(0, ∫ₐᵇ f²)`, covariance `∫ₐ^{min(b,d)} f g`, integration by parts | `Gardiner.Ito.IsWiener.wienerInt_map`, `Gardiner.Ito.IsWiener.wienerInt_mul_same`, `Gardiner.Ito.IsWiener.wienerInt_ibp`, `Gardiner.Ito.wienerInt_id_stdWiener` |
| Riemann sums of a step function converge in mean square to its simple integral; `∫ (fₙ - 1_{(α,β]})² ≤ 2(b - a)/(n + 1)` | `Gardiner.Ito.IsWiener.wienerInt_step`, `Gardiner.Ito.integral_stepFn_ind_sub_sq_le` |
| `IsLinearisedLaw` holds for the Wiener-integral linearised process | `Gardiner.Ito.IsWiener.isLinearisedLaw_linProc`, `Gardiner.Ito.ouPath_stdWiener_law` |
| OU process: exact mean, variance, correlation, Gaussian law, stationary limit | `Gardiner.Ito.IsWiener.ouProc_var`, `Gardiner.Ito.IsWiener.ouProc_cov_printed`, `Gardiner.Ito.IsWiener.ouProc_map`, `Gardiner.Ito.IsWiener.ouProc_stationary`, `Gardiner.Ito.ouProc_stdWiener` |
| `(ΔW, ΔZ)` jointly Gaussian with covariance `τ, τ²/2, τ³/3` | `Gardiner.Ito.IsWiener.incr_hasGaussianLaw`, `Gardiner.Ito.IsWiener.incr_moments`, `Gardiner.Ito.multiple_stdWiener` |

## Correspondence with Gardiner

| Gardiner | Lean |
| --- | --- |
| §3.8.1 Wiener process (3.8.4)–(3.8.6), independent increments | `Gardiner.Ito.IsWiener`, `Gardiner.Ito.IsWiener.map_eval`, `Gardiner.Ito.stdWiener`, `Gardiner.Ito.isWiener_stdWiener` |
| §4.2.4 nonanticipation: future increments independent of the past | `Gardiner.Ito.wienerFiltration`, `Gardiner.Ito.IsWiener.indep_past`, `Gardiner.Ito.IsWiener.stronglyAdapted`, `Gardiner.Ito.IsWiener.condExp_eq` |
| partition `t₀ ≤ t₁ ≤ … ≤ tₙ = t` of §4.2.1 | `Gardiner.Ito.IsPartition`, `Gardiner.Ito.unifPart`, `Gardiner.Ito.isPartition_unifPart` |
| `ΔWᵢ`, independence and law (text before (4.2.16)) | `Gardiner.Ito.dW`, `Gardiner.Ito.IsWiener.dW_iIndepFun`, `Gardiner.Ito.IsWiener.dW_map`, `Gardiner.Ito.IsWiener.dW_mean` |
| (4.2.12)–(4.2.13) | `Gardiner.Ito.itoSum`, `Gardiner.Ito.qvSum`, `Gardiner.Ito.psum_dW`, `Gardiner.Ito.itoSum_eq` |
| (4.2.14) | `Gardiner.Ito.IsWiener.dW_sq_mean`, `Gardiner.Ito.IsWiener.qv_mean` |
| (4.2.15)–(4.2.18) (corrected) | `Gardiner.Ito.IsWiener.dW_four`, `Gardiner.Ito.IsWiener.qv_ms_error`, `Gardiner.Ito.IsWiener.qv_ms_le`, `Gardiner.Ito.eq_4_2_18_printed_wrong` |
| (4.2.19) | `Gardiner.Ito.IsWiener.qv_msLim`, `Gardiner.Ito.qv_msLim_unif`, `Gardiner.Ito.qv_unif_instance` |
| (4.2.20) | `Gardiner.Ito.IsWiener.itoSum_ms_error`, `Gardiner.Ito.IsWiener.itoSum_msLim`, `Gardiner.Ito.itoSum_unif_instance` |
| (10.1.9) with real Wiener increments (vs. `Gardiner.SDE.ito_sum_of_qv`) | `Gardiner.Ito.IsWiener.ito_sum_of_qv_ms` |
| §4.2.5 i)–ii) | `Gardiner.Ito.IsWiener.dW_sq_mean`, `Gardiner.Ito.IsWiener.dW_sq_sub_sq` |
| (6.2.40), law-level | `Gardiner.Ito.scaleW`, `Gardiner.Ito.IsWiener.scale`, `Gardiner.Ito.IsWiener.scale_law_sub`, `Gardiner.Ito.stdWiener_scale`, `Gardiner.Ito.stdWiener_scale_two_var` |
| (6.2.39)–(6.2.44) with a Wiener process | `Gardiner.Ito.cubic_scaling_wiener`, `Gardiner.Ito.cubic_scaling_stdWiener` |
| (6.2.1), additive noise, Brownian path | `Gardiner.Ito.IsWiener.ae_exists_pathSol`, `Gardiner.Ito.exists_pathSol_sin_stdWiener` |
| (6.2.9)–(6.2.14), (6.2.22)–(6.2.25), Brownian path | `Gardiner.Ito.ouPath`, `Gardiner.Ito.ouPath_eq`, `Gardiner.Ito.sinHier_isHierarchy`, `Gardiner.Ito.sin_linearisation_path`, `Gardiner.Ito.IsWiener.ae_sin_linearisation`, `Gardiner.Ito.sin_linearisation_stdWiener` |
| (6.2.33), Brownian path | `Gardiner.Ito.cubic_expansion_path`, `Gardiner.Ito.IsWiener.ae_cubic_expansion` |
| (10.1.15)–(10.1.17), Euler driven by a Brownian path | `Gardiner.Ito.euler_tendsto_of_continuous`, `Gardiner.Ito.IsWiener.ae_euler_tendsto`, `Gardiner.Ito.euler_sin_stdWiener` |
| (10.1.21) iv) and the schemes of §10.1–§10.4 driven by Brownian increments | `Gardiner.Ito.gridInc`, `Gardiner.Ito.IsWiener.linScheme_moments`, `Gardiner.Ito.exists_gaussian_increments_brownian`, `Gardiner.Ito.IsWiener.ou_weak`, `Gardiner.Ito.IsWiener.gbm_weak`, `Gardiner.Ito.IsWiener.gbm_ms`, `Gardiner.Ito.ou_weak_stdWiener` |
| §4.2.4, §4.2.6 e–f: simple nonanticipating integrand, its integral and running integral | `Gardiner.Ito.SimpleIntegrand`, `Gardiner.Ito.SimpleIntegrand.process`, `Gardiner.Ito.SimpleIntegrand.integral`, `Gardiner.Ito.SimpleIntegrand.running` |
| linearity of the simple integral | `Gardiner.Ito.SimpleIntegrand.integral_add`, `Gardiner.Ito.SimpleIntegrand.integral_smul` |
| (4.2.40)–(4.2.41) mean value | `Gardiner.Ito.SimpleIntegrand.integral_mean`, `Gardiner.Ito.IsWiener.wienerInt_mean` |
| (4.2.42)–(4.2.44) correlation formula / Itô isometry | `Gardiner.Ito.SimpleIntegrand.integral_mul_eq_sum`, `Gardiner.Ito.SimpleIntegrand.integral_mul`, `Gardiner.Ito.SimpleIntegrand.integral_sq`, `Gardiner.Ito.IsWiener.wienerInt_mul`, `Gardiner.Ito.IsWiener.wienerInt_sq` |
| martingale property of `∫₀ᵗ G dW` | `Gardiner.Ito.SimpleIntegrand.martingale_running`, `Gardiner.Ito.simpleExample_martingale` |
| mean-square limit (4.2.8)–(4.2.10) | `Gardiner.Ito.msLim`, `Gardiner.Ito.msLim_spec`, `Gardiner.Ito.msLim_unique` |
| Wiener integral `∫ f(t') dW(t')` of a deterministic `f` | `Gardiner.Ito.riemannSum`, `Gardiner.Ito.wienerInt`, `Gardiner.Ito.IsWiener.wienerInt_spec`, `Gardiner.Ito.riemannSum_eq` |
| Wiener integral of a step function = simple integral | `Gardiner.Ito.stepIntegrand`, `Gardiner.Ito.IsWiener.wienerInt_step`, `Gardiner.Ito.wienerInt_step_stdWiener` |
| Gaussian law and joint Gaussian law of Wiener integrals | `Gardiner.Ito.IsWiener.wienerInt_map`, `Gardiner.Ito.hasGaussianLaw_pair`, `Gardiner.Ito.IsWiener.wienerInt_hasGaussianLaw_pair` |
| `∫ f dW = f(t)W(t) - f(t₀)W(t₀) - ∫ f'W dt` (integration by parts, `C¹` `f`) | `Gardiner.Ito.IsWiener.wienerInt_ibp`, `Gardiner.Ito.IsWiener.wienerInt_one` |
| (6.2.14) `x₁(t) = ∫₀ᵗ b(t') e^{-∫_{t'}^t k} dW(t')` and its law | `Gardiner.Ito.linProc`, `Gardiner.Ito.IsWiener.isLinearisedLaw_linProc`, `Gardiner.Ito.IsWiener.linProc_map` |
| (6.2.31)–(6.2.32), leading terms, unconditional | `Gardiner.Ito.IsWiener.linProc_variance`, `Gardiner.Ito.IsWiener.linProc_correlation` |
| (6.2.10)–(6.2.14) pathwise first-order term = `x₁` a.s. (additive noise) | `Gardiner.Ito.linPath`, `Gardiner.Ito.linPath_eq`, `Gardiner.Ito.linPath_unique`, `Gardiner.Ito.IsWiener.linProc_ae_linPath`, `Gardiner.Ito.IsWiener.hierarchy_first_order_ae`, `Gardiner.Ito.ouPath_eq_linPath` |
| (4.4.22), (4.4.26) OU process, pathwise solution | `Gardiner.Ito.ouProc`, `Gardiner.Ito.ouProc_isPathSol`, `Gardiner.Ito.IsWiener.ouProc_ae` |
| (4.4.27) | `Gardiner.Ito.IsWiener.ouProc_mean`, `Gardiner.Ito.IsWiener.ouProc_mean_const` |
| (4.4.28)–(4.4.29) | `Gardiner.Ito.IsWiener.ouProc_var`, `Gardiner.Ito.IsWiener.ouInt_sq`, `Gardiner.Ito.IsWiener.ouProc_second`, `Gardiner.Ito.IsWiener.ouProc_second_const` |
| (4.4.30) | `Gardiner.Ito.IsWiener.ouProc_cov`, `Gardiner.Ito.IsWiener.ouProc_cov_printed`, `Gardiner.Ito.IsWiener.ouInt_mul` |
| OU Gaussian law (deterministic or Gaussian `x(0)`) | `Gardiner.Ito.IsWiener.ouProc_map`, `Gardiner.Ito.IsWiener.ouProc_map_const` |
| (4.4.31) stationary limit, `k > 0` | `Gardiner.Ito.IsWiener.ouProc_stationary` |
| OU process vs. `Gardiner.SDE.ouMean`, `Gardiner.SDE.ouSecond` and the OU weak-error theorems | `Gardiner.Ito.IsWiener.ouProc_mean_const`, `Gardiner.Ito.IsWiener.ouProc_second_const`, `Gardiner.Ito.IsWiener.ou_weak_process`, `Gardiner.Ito.ouProc_stdWiener` |
| (10.1.9)–(10.1.10) `ΔW`, `ΔZ = ∫ds∫dW` | `Gardiner.Ito.incrW`, `Gardiner.Ito.incrZ`, `Gardiner.Ito.IsWiener.incrW_ae`, `Gardiner.Ito.IsWiener.incrZ_ae` |
| (10.1.11) (corrected) `∫dW∫ds = τΔW - ΔZ` | `Gardiner.Ito.IsWiener.companion_ae` |
| (10.1.12) joint law and moments of `(ΔW, ΔZ)` | `Gardiner.Ito.IsWiener.incr_lin_map`, `Gardiner.Ito.IsWiener.incr_hasGaussianLaw`, `Gardiner.Ito.IsWiener.incr_moments`, `Gardiner.Ito.IsWiener.multiple_moments` |
| `ΔW = √τ ξ`, `ΔZ = ½τ^{3/2}(ξ + η/√3)`, `ξ, η` independent `N(0, 1)` | `Gardiner.Ito.xiN`, `Gardiner.Ito.etaN`, `Gardiner.Ito.incrW_eq_xi`, `Gardiner.Ito.incrZ_eq_xi_eta`, `Gardiner.Ito.IsWiener.xi_eta_indep`, `Gardiner.Ito.multiple_stdWiener` |

## Errata (formalized in corrected form)

* (4.2.18): the left-hand side is missing the square on `Wᵢ - Wᵢ₋₁`, and the middle line should
  read `Σ_{i,j}(tᵢ - tᵢ₋₁)(tⱼ - tⱼ₋₁) - (t - t₀)² = 0`; as printed it equals `(n - 1)²(t - t₀)²`
  (`Gardiner.Ito.eq_4_2_18_printed_wrong`).  The final value `2 Σ Δtᵢ²` is correct.
* (10.1.10)/(10.1.11): the two printed formulas are identical.  The intended pair is
  `ΔZ = ∫_t^{t+τ} ds ∫_t^s dW(s')` (10.1.10) and its companion
  `∫_t^{t+τ} dW(s) ∫_t^s ds' = τΔW - ΔZ` (10.1.11) (`Gardiner.Ito.IsWiener.incrZ_ae`,
  `Gardiner.Ito.IsWiener.companion_ae`), consistent with the erratum recorded in
  `SHSLib.Gardiner.SDE.Schemes`.
* (4.4.27)–(4.4.30) are correct as printed, for `k ≠ 0` and `x(0)` independent of `W`; the form
  `[var{x(0)} - D/2k]` of (4.4.29)–(4.4.30) uses `(√D)² = D`, i.e. `D ≥ 0`.

## Not in this layer

The Itô integral of a general `L²` nonanticipating integrand (§4.2.6; only simple integrands and
deterministic continuous or step integrands are covered here), the Itô formula (§4.3.3) and
strong solutions of SDEs with multiplicative noise are the subject of later jobs; they should be
built on `Gardiner.Ito.IsWiener` and `Gardiner.Ito.wienerFiltration` only.
-/
import SHSLib.Gardiner.Ito.Wiener
import SHSLib.Gardiner.Ito.Brownian
import SHSLib.Gardiner.Ito.Increments
import SHSLib.Gardiner.Ito.Scaling
import SHSLib.Gardiner.Ito.Pathwise
import SHSLib.Gardiner.Ito.Schemes
import SHSLib.Gardiner.Ito.Simple
import SHSLib.Gardiner.Ito.MSLimit
import SHSLib.Gardiner.Ito.WienerIntegral
import SHSLib.Gardiner.Ito.WienerStep
import SHSLib.Gardiner.Ito.WienerInstances
import SHSLib.Gardiner.Ito.Linearised
import SHSLib.Gardiner.Ito.OU
import SHSLib.Gardiner.Ito.Multiple
