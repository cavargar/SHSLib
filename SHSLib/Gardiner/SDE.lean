/-
# Small-noise expansion of SDEs and numerical simulation of SDEs (Gardiner §6.2, §10.1–§10.5)

Index of the SDE layer (C. W. Gardiner, *Handbook of Stochastic Methods*: §6.2 small-noise
expansions for stochastic differential equations; Ch. 10 §10.1–§10.5 simulation of stochastic
differential equations).  It sits next to `SHSLib.Gardiner.Approx` (whose §6.3 small-noise
Fokker–Planck expansion is the counterpart of §6.2), `SHSLib.Gardiner.Adiabatic` and
`SHSLib.Gardiner.Escape`, and uses the same conventions:

* all declarations are in the namespace `Gardiner.SDE`;
* **Itô-free**: no Brownian motion, stochastic integral or Itô formula is constructed or assumed.
  For additive noise the SDE `dx = a(x)dt + ε dw` is solved *pathwise* for every continuous
  driving path `w` (`Gardiner.SDE.IsPathSol`); the numerical schemes are discrete-time recursions
  driven by i.i.d. `N(0, τ)` increments on an arbitrary probability space;
* **probabilistic inputs that need a Wiener process are named hypotheses**: the law of the
  linearised process (6.2.14) (`Gardiner.SDE.IsLinearisedLaw`), the quadratic (co)variation of
  the increments ((10.1.9), (10.5.10)), the joint law of the multiple integrals
  ((10.1.10)–(10.1.12), (10.5.25)–(10.5.27)), and the factorisations used in (10.1.42);
* **exact moments of the linear test SDEs** (Ornstein–Uhlenbeck and linear multiplicative noise)
  are characterised by their moment ODEs (`Gardiner.SDE.ouSecond_hasDerivAt`, …); the derivation
  of these ODEs from the SDE (Itô's formula) is not part of this layer;
* every main theorem is applied to a concrete non-degenerate instance (`SHSLib.Gardiner.SDE.Examples`
  and the instance sections of the individual files): the cubic process `dx = -x³dt + ε dw`,
  `dx = -sin x dt + ε d√t`, the OU process `γ = σ = x₀ = 1`, `dx = -x dt + x dW`, the linearised
  OU process `k = b = 1`, `B_{ij} = xᵢG_{ij}` with `G = [[1,2],[3,4]]`, `A = sin`, `b = cos`.

**Note (Brownian-motion layer).**  SHSLib now has a genuine Wiener process:
`SHSLib.Gardiner.Ito` (index `SHSLib/Gardiner/Ito.lean`, plan
`research/docs/plans/plan_gardiner_ito_bm.md`) provides the interface `Gardiner.Ito.IsWiener`
with its natural filtration, a concrete standard Wiener process `Gardiner.Ito.stdWiener`, and
instantiates this layer with it: `IsPathSol`, the pathwise expansion and Euler convergence hold
almost surely for Brownian paths, and Brownian grid increments satisfy the hypotheses of
`Gardiner.SDE.linScheme_moments`.  It also proves the quadratic variation (4.2.14)–(4.2.19) that
`Gardiner.SDE.ito_sum_of_qv` assumes (in mean square) and the law-level form of (6.2.40) that
`Gardiner.SDE.cubic_scaling` replaces by a pathwise rescaling.  The declarations of this layer
are unchanged.

## Guarantees with explicit error terms

| Guarantee | Lean |
| --- | --- |
| expansion algebra (6.2.3)–(6.2.7): `|a(Σεᵐxₘ) - Σ_{n≤N} aₙεⁿ| ≤ 2Me^{(N+1)R}|ε|^{N+1}` | `Gardiner.SDE.expansion_remainder` |
| pathwise small-noise expansion, additive noise, uniformly on `[0, T]`: `|x(t) - Σ_{n≤N} εⁿxₙ(t)| ≤ T e^{LT+1/2} · 2Me^{(N+1)R} |ε|^{N+1}` (one-sided Lipschitz drift `L`) | `Gardiner.SDE.pathwise_expansion`, `Gardiner.SDE.remainder_bounded`, `Gardiner.SDE.linearisation_error` |
| instance: cubic process to order `ε³` (error `O(ε⁴)`) and linearisation (error `O(ε²)`) | `Gardiner.SDE.cubic_expansion`, `Gardiner.SDE.cubic_linearisation` |
| pathwise Euler convergence for any continuous path: `|x(T) - y_N| ≤ (e^{LT} - 1)(Aτ + |ε|ω(τ))`, `ω` the modulus of continuity of `w` | `Gardiner.SDE.euler_pathwise_error`, `Gardiner.SDE.euler_pathwise_error_grid`, `Gardiner.SDE.euler_sin_sqrt` |
| existence of the pathwise solution (bounded Lipschitz drift) | `Gardiner.SDE.exists_pathSol`, `Gardiner.SDE.exists_pathSol_sin_sqrt` |
| weak error `O(τ)`, OU, Euler and semi-implicit, mean and second moment, vs. the exact moments | `Gardiner.SDE.eulerOU_weak_mean`, `Gardiner.SDE.eulerOU_weak_second`, `Gardiner.SDE.semiOU_weak_mean`, `Gardiner.SDE.semiOU_weak_second`, `Gardiner.SDE.ou_weak_instance` |
| weak error `O(τ)`, `dx = λx dt + μx dW`, Euler, Milstein, semi-implicit, mean and second moment | `Gardiner.SDE.eulerGBM_weak_mean`, `Gardiner.SDE.eulerGBM_weak_second`, `Gardiner.SDE.milsteinGBM_weak_mean`, `Gardiner.SDE.milsteinGBM_weak_second`, `Gardiner.SDE.semiGBM_weak_mean`, `Gardiner.SDE.semiGBM_weak_second`, `Gardiner.SDE.gbm_weak_instance` |
| linear-test-equation stability regions (10.3.5), (10.3.12), (10.3.15), A-stability | `Gardiner.SDE.euler_stable_iff`, `Gardiner.SDE.implicit_stable_iff`, `Gardiner.SDE.semi_stable_iff`, `Gardiner.SDE.implicit_AStable`, `Gardiner.SDE.semi_AStable`, `Gardiner.SDE.euler_not_AStable` |
| mean-square stability regions for `dx = λx dt + μx dW` | `Gardiner.SDE.ms_tendsto_zero_iff`, `Gardiner.SDE.eulerGBM_ms_stable_iff`, `Gardiner.SDE.milsteinGBM_ms_stable_iff`, `Gardiner.SDE.implicitGBM_ms_stable`, `Gardiner.SDE.eulerGBM_ms_tendsto_iff`, `Gardiner.SDE.milsteinGBM_ms_tendsto_iff`, `Gardiner.SDE.implicitGBM_ms_tendsto`, `Gardiner.SDE.gbm_ms_instance` |
| consistency (§10.3.1) as a property of one-step maps; (10.4.10) is necessary and sufficient | `Gardiner.SDE.IsConsistentAt`, `Gardiner.SDE.euler_consistent`, `Gardiner.SDE.milstein_consistent`, `Gardiner.SDE.thetaTrunc_consistent_iff`, `Gardiner.SDE.naive_implicit_inconsistent` |
| implicit step (10.4.9): `|z - (Aτ + bΔW + θbb'ΔW²)| ≤ 2K₁K₀h|τ| + (½K₂K₀² + K₁²K₀)h³` | `Gardiner.SDE.implicit_step_expansion` |
| error recursions (10.1.24)–(10.1.25), (10.1.28)–(10.1.29) as closed bounds | `Gardiner.SDE.strong_error_bound`, `Gardiner.SDE.mean_error_bound` |

## §6.2 Small-noise expansions for stochastic differential equations

| Gardiner | Lean |
| --- | --- |
| (6.2.1), additive noise `b = 1`, pathwise | `Gardiner.SDE.IsPathSol` |
| (6.2.2)–(6.2.5) | `Gardiner.SDE.pertPoly`, `Gardiner.SDE.compPoly`, `Gardiner.SDE.snCoeff`, `Gardiner.SDE.snCoeff_stable`, `Gardiner.SDE.snCoeff_congr` |
| (6.2.6) | `Gardiner.SDE.snCoeff_zero`, `Gardiner.SDE.snCoeff_one`, `Gardiner.SDE.snCoeff_two`, `Gardiner.SDE.snCoeff_three` |
| (6.2.7) | `Gardiner.SDE.snA`, `Gardiner.SDE.snCoeff_split`, `Gardiner.SDE.snA_indep` |
| (6.2.9)–(6.2.13) | `Gardiner.SDE.hierDrift`, `Gardiner.SDE.IsHierarchy`, `Gardiner.SDE.hierDrift_zero`, `Gardiner.SDE.hierDrift_one`, `Gardiner.SDE.hierDrift_split`, `Gardiner.SDE.snA_one` |
| (6.2.14) variance and correlation | `Gardiner.SDE.linVar`, `Gardiner.SDE.linCov`, `Gardiner.SDE.linVar_hasDerivAt`, `Gardiner.SDE.linVar_unique`, `Gardiner.SDE.linCov_hasDerivAt`, `Gardiner.SDE.IsLinearisedLaw` |
| (6.2.15)–(6.2.16) | `Gardiner.SDE.IsHierarchy` (integral form), `Gardiner.SDE.partialSum_eq` |
| (6.2.17)–(6.2.21) | `Gardiner.SDE.partialSum`, `Gardiner.SDE.aHat`, `Gardiner.SDE.aHat_bounded`, `Gardiner.SDE.remainder_eq` |
| (6.2.22)–(6.2.25) with rate | `Gardiner.SDE.pathwise_expansion`, `Gardiner.SDE.remainder_bounded`, `Gardiner.SDE.linearisation_error` |
| (6.2.26)–(6.2.28) stationary solutions | `Gardiner.SDE.linVar_const`, `Gardiner.SDE.linVar_stationary_error`, `Gardiner.SDE.linVar_tendsto_stationary`, `Gardiner.SDE.linCov_stationary_error`, `Gardiner.SDE.linVar_tendsto_atTop_of_neg` (unstable state) |
| (6.2.29) with rate | `Gardiner.SDE.mean_expansion_of_pathwise`, `Gardiner.SDE.mean_expansion_instance` |
| (6.2.30) (corrected) | `Gardiner.SDE.cov_expansion` |
| (6.2.31)–(6.2.32) | `Gardiner.SDE.var_expansion_three`, `Gardiner.SDE.cov_expansion_three`, `Gardiner.SDE.IsLinearisedLaw.correlation_eq`, `Gardiner.SDE.IsLinearisedLaw.variance_eq`, `Gardiner.SDE.linearised_ou_statistics` |
| (6.2.33), finite-time validity | `Gardiner.SDE.cubicD`, `Gardiner.SDE.cubicHier`, `Gardiner.SDE.cubicHier_isHierarchy`, `Gardiner.SDE.cubic_expansion`, `Gardiner.SDE.cubic_linearisation` |
| (6.2.34)–(6.2.35) | `Gardiner.SDE.cubic_k_zero`, `Gardiner.SDE.linVar_k_zero`, `Gardiner.SDE.linVar_k_zero_unbounded` |
| (6.2.36)–(6.2.37) | `Gardiner.SDE.cubicPs`, `Gardiner.SDE.cubic_ps_flux`, `Gardiner.SDE.cubic_ps_fpe` |
| (6.2.38) | `Gardiner.SDE.cubic_moment_even`, `Gardiner.SDE.cubic_moment_odd`, `Gardiner.SDE.cubic_variance`, `Gardiner.SDE.cubic_variance_not_eps_sq` |
| (6.2.39)–(6.2.44), pathwise scaling | `Gardiner.SDE.cubic_scaling` |
| (6.2.45)–(6.2.47) (corrected) | `Gardiner.SDE.cubic_first_order`, `Gardiner.SDE.cubic_first_order_printed_wrong` |

## Ch. 10 Simulation of stochastic differential equations

| Gardiner | Lean |
| --- | --- |
| (10.1.3), (10.1.13)–(10.1.17) Euler | `Gardiner.SDE.eulerStep`, `Gardiner.SDE.eulerPath` (pathwise, additive noise) |
| (10.1.4)–(10.1.5) | `Gardiner.SDE.L0`, `Gardiner.SDE.L1` |
| (10.1.9) | `Gardiner.SDE.psum`, `Gardiner.SDE.ito_sum_identity`, `Gardiner.SDE.strat_sum_identity`, `Gardiner.SDE.ito_sum_of_qv` |
| (10.1.10)–(10.1.12) as a given law | `Gardiner.SDE.multipleIntegral_moments` |
| (10.1.18) (corrected) | `Gardiner.SDE.milsteinStep`, `Gardiner.SDE.eq_10_1_18_printed_wrong` |
| (10.1.21) i)–iv) | `Gardiner.SDE.gauss_i`, `Gardiner.SDE.gauss_ii`, `Gardiner.SDE.gauss_iii`, `Gardiner.SDE.linScheme_indep` |
| (10.1.22)–(10.1.26) | `Gardiner.SDE.strong_error_bound` |
| (10.1.27)–(10.1.29) | `Gardiner.SDE.mean_error_bound` |
| (10.1.30), weak order for linear SDEs | `Gardiner.SDE.weak_factor`, `Gardiner.SDE.affine_error` and the weak-error theorems above |
| (10.1.31)–(10.1.34) Milstein | `Gardiner.SDE.cMil`, `Gardiner.SDE.milsteinStep`, `Gardiner.SDE.milstein_31_eq_32`, `Gardiner.SDE.milsteinGBM_apply` |
| (10.1.35)–(10.1.42) (corrected) | `Gardiner.SDE.milstein_error_second_moment`, `Gardiner.SDE.eq_10_1_42_printed_wrong` |
| linear schemes and their exact moments | `Gardiner.SDE.LinStep`, `Gardiner.SDE.linScheme`, `Gardiner.SDE.linStep_moments`, `Gardiner.SDE.linScheme_moments`, `Gardiner.SDE.linScheme_mean`, `Gardiner.SDE.linScheme_sq`, `Gardiner.SDE.linScheme_sq_additive` |
| (10.3.1)–(10.3.5) | `Gardiner.SDE.schemeRun`, `Gardiner.SDE.eulerStepC`, `Gardiner.SDE.euler_error_propagation`, `Gardiner.SDE.error_tendsto_zero_iff`, `Gardiner.SDE.euler_stable_iff` |
| (10.3.6)–(10.3.12) | `Gardiner.SDE.implicitStepC`, `Gardiner.SDE.implicitStepC_spec`, `Gardiner.SDE.implicit_error_propagation`, `Gardiner.SDE.implicit_stable_iff`, `Gardiner.SDE.fig10_1c_printed_wrong` |
| (10.3.13)–(10.3.15) | `Gardiner.SDE.semiStepC`, `Gardiner.SDE.semiStepC_spec`, `Gardiner.SDE.semi_error_propagation`, `Gardiner.SDE.semi_region_iff`, `Gardiner.SDE.semi_stable_iff` |
| §10.3 d) A-stability | `Gardiner.SDE.AStable`, `Gardiner.SDE.implicit_AStable`, `Gardiner.SDE.semi_AStable`, `Gardiner.SDE.euler_not_AStable`, `Gardiner.SDE.implicit_stable_growing` |
| mean-square stability (linear multiplicative test equation) | `Gardiner.SDE.implicitGBM`, `Gardiner.SDE.eulerGBM_EG2`, `Gardiner.SDE.milsteinGBM_EG2`, `Gardiner.SDE.implicitGBM_EG2`, `Gardiner.SDE.eulerGBM_ms_stable_imp`, `Gardiner.SDE.eulerGBM_ms_stable_of` and the guarantees above |
| §10.3.1 consistency | `Gardiner.SDE.meanIncr`, `Gardiner.SDE.sqIncr`, `Gardiner.SDE.IsConsistentAt`, `Gardiner.SDE.poly_incr`, `Gardiner.SDE.euler_consistent`, `Gardiner.SDE.milstein_consistent` |
| (10.4.1)–(10.4.9) | `Gardiner.SDE.implicit_step_expansion`, `Gardiner.SDE.thetaTrunc`, `Gardiner.SDE.thetaTrunc_eq`, `Gardiner.SDE.thetaTrunc_incr` |
| (10.4.10), §10.4 a) | `Gardiner.SDE.thetaTrunc_corrected`, `Gardiner.SDE.thetaTrunc_half_eq_milstein`, `Gardiner.SDE.thetaTrunc_consistent_iff`, `Gardiner.SDE.thetaTrunc_corrected_consistent` |
| (10.4.11)–(10.4.17) | `Gardiner.SDE.semiOU`, `Gardiner.SDE.semiOU_spec`, `Gardiner.SDE.semiGBM`, `Gardiner.SDE.semiGBM_iter`, `Gardiner.SDE.midpoint_forms_equiv`, `Gardiner.SDE.strat_sum_identity` |
| (10.5.1)–(10.5.3) | `Gardiner.SDE.pd`, `Gardiner.SDE.Lj` |
| (10.5.6)–(10.5.10) | `Gardiner.SDE.dsum`, `Gardiner.SDE.double_sum_symm`, `Gardiner.SDE.double_sum_symm_of_qv` |
| (10.5.11)–(10.5.14) (corrected) | `Gardiner.SDE.double_sum_decomp`, `Gardiner.SDE.eq_10_5_14_printed_wrong` |
| (10.5.15)–(10.5.18) | `Gardiner.SDE.Ccoef`, `Gardiner.SDE.IsCommutativeNoise`, `Gardiner.SDE.additive_C_zero`, `Gardiner.SDE.additive_commutative`, `Gardiner.SDE.single_noise_commutative`, `Gardiner.SDE.diagForm`, `Gardiner.SDE.diagForm_C`, `Gardiner.SDE.diagForm_commutative` |
| (10.5.19)–(10.5.22) | `Gardiner.SDE.vecEuler` |
| (10.5.23)–(10.5.27) | `Gardiner.SDE.vecMilstein`, `Gardiner.SDE.vecMilstein_decomp`, `Gardiner.SDE.sum_symm_antisymm`, `Gardiner.SDE.vecMilstein_commutative` |
| (10.5.28)–(10.5.34) (corrected) | `Gardiner.SDE.strong_semi_matches_milstein`, `Gardiner.SDE.eq_10_5_34_printed_wrong` |
| (10.5.35)–(10.5.41) (corrected) | `Gardiner.SDE.midpoint_forms_equiv`, `Gardiner.SDE.E_term_mean_zero` |

§10.2 is descriptive; §10.6–§10.8 (higher-order algorithms, stochastic PDEs, software) are out
of scope.

## Errata (formalized in corrected form; see the module docstrings)

* Text around (6.2.12)–(6.2.13): "the solution of (6.2.9)" should be (6.2.10a); "(6.2.10a) for
  `n = 1`" should be (6.2.10b); and it is `A₁` (not `A₀`) that vanishes
  (`Gardiner.SDE.snA_one`).
* (6.2.21): the argument list of `b̂ₙ` must include `yₙ` through `xₙ + εyₙ`; for additive noise
  `b̂ₙ = 0` for `n ≥ 1` and the pathwise form is `Gardiner.SDE.remainder_eq`.
* (6.2.24): the drift term is missing `dt`.
* (6.2.30): the outer index is `n` (printed `s`) and the inner sum runs over `0 ≤ m ≤ n`
  (`Gardiner.SDE.cov_expansion`).
* (6.2.47): the coefficient is `-(3y₀²c(0)y₁ + y₀⁴c'(0))`; the printed `-y₁[3y₀²c(0) + y₀³c'(0)]`
  is wrong (`Gardiner.SDE.cubic_first_order_printed_wrong`).
* (10.1.11) duplicates (10.1.10); the intended integral is `∫dW(s)∫ds'`
  (`Gardiner.SDE.multipleIntegral_moments` treats both).
* (10.1.18): the correction coefficient is `½L₁b`, not `½L₀b` (`Gardiner.SDE.eq_10_1_18_printed_wrong`).
* (10.1.25): the exact exponent from (10.1.24) is `(2A + B + A²τ)T`; the text drops `A²τ`
  (harmless as `τ → 0`) (`Gardiner.SDE.strong_error_bound`).
* (10.1.42): the cross term `2(1 + a'τ)Pτ²⟨eₙ⟩` is missing
  (`Gardiner.SDE.milstein_error_second_moment`, `Gardiner.SDE.eq_10_1_42_printed_wrong`).
* (10.3.1): the drift term is `λx dt`.
* Fig. 10.1c (caption): the implicit-Euler stability region is the exterior of the disc
  `|λ - 1/τ| ≤ 1/τ`, not the right half-plane (`Gardiner.SDE.fig10_1c_printed_wrong`).
* (10.4.16): the left-hand side is `ȳₙ`, not `ȳₙ₊₁` (`Gardiner.SDE.semiGBM_iter`,
  `Gardiner.SDE.midpoint_forms_equiv`).
* (10.5.14): the term `-δᵢⱼ(t - t₀)` is missing (`Gardiner.SDE.eq_10_5_14_printed_wrong`).
* (10.5.34): the antisymmetric term carries a factor `½`: `½Σ C̄_{ijj'}E_{jj'}`
  (`Gardiner.SDE.eq_10_5_34_printed_wrong`).
* (10.5.40): in the form of (10.4.16)–(10.4.17) the left-hand side is `ȳⁿᵢ` and the increment
  carries a factor `½` (`Gardiner.SDE.midpoint_forms_equiv`).

**Discrepancy, not an erratum.**  For multiplicative noise the exactly solved semi-implicit step
`y_{n+1} = yₙ(1 + κ/2)/(1 - κ/2)`, `κ = (λ - μ²/2)τ + μΔWₙ`, has no finite moments (the
denominator vanishes with positive probability density), so its weak error is not defined; we
analyse the scheme as implemented in the text, "by simple iteration" of (10.4.16), with two
iterations (`Gardiner.SDE.semiGBM`).

**Out of scope (needs Itô calculus).**  Strong orders of convergence measured against a true SDE
solution with multiplicative noise ((10.1.26), (10.1.43), the strong orders claimed in §10.4 a)
and §10.5.3–§10.5.5).  The error recursions themselves are proved as inequalities
(`Gardiner.SDE.strong_error_bound`), but connecting them to an SDE solution needs the remainder
estimates (10.1.36)–(10.1.39) of the Itô–Taylor expansion, which are not available without a
stochastic integral.
-/
import SHSLib.Gardiner.SDE.GaussianMoments
import SHSLib.Gardiner.SDE.Expansion
import SHSLib.Gardiner.SDE.Pathwise
import SHSLib.Gardiner.SDE.EulerPathwise
import SHSLib.Gardiner.SDE.Cubic
import SHSLib.Gardiner.SDE.Statistics
import SHSLib.Gardiner.SDE.SchemeMoments
import SHSLib.Gardiner.SDE.WeakError
import SHSLib.Gardiner.SDE.Stability
import SHSLib.Gardiner.SDE.Schemes
import SHSLib.Gardiner.SDE.Vector
import SHSLib.Gardiner.SDE.Examples
