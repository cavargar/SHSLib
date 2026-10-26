/-
# Small-noise and system-size approximations (Gardiner, Ch. 6 and Ch. 7)

Index of the approximation layer built on the dCKE layer of `SHSLib.Gardiner`
(C. W. Gardiner, *Handbook of Stochastic Methods*, §6.1, §6.3, §7.1.2, §7.2, §7.5, with the
covariance equations of §4.4.6 and §4.4.9).  Conventions are those of `SHSLib/Gardiner.lean`:
`Sp n = EuclideanSpace ℝ (Fin n)`, `pd`/`pd2` are partial derivatives defined through `fderiv`,
and `fpRHS` is the Fokker–Planck right-hand side (3.5.6).

Master equations are mostly studied through their *backward generator*
`(L f)(x) = Σ_j W_j(x) [f(x + r_j) - f(x)]` (or its integral version); this is the operator
appearing in the derivation "as in Sect. 3.4" and it is where all error terms are stated.
The limit and integral interchanges the text makes silently are named hypotheses
(`hswap`, …), as in the dCKE layer.

## Approximation guarantees with explicit error terms

| Guarantee | Lean |
| --- | --- |
| master-equation generator vs. linear-noise operator, `O(Ω^{-1/2})` (1-d) | `Gardiner.vkGen_sub_lnaGen_le`, `Gardiner.vkGen_tendsto_lnaGen` |
| same, multivariate (chemical networks) | `Gardiner.mvkGen_sub_mlnaGen_le` |
| same, for `X ⇌ A` (instance) | `Gardiner.xa_vkGen_sub_lnaGen_le` |
| small-noise generator vs. Ornstein–Uhlenbeck generator, `O(ε)` | `Gardiner.snGen_sub_ouGen_le` |
| Kramers–Moyal truncation error via the next jump moment | `Gardiner.jumpGen_sub_kmGen_le`, `Gardiner.finJumpGen_sub_finKM_le` |
| same, on `ℝⁿ` (third absolute jump moment) | `Gardiner.mjGen_sub_mjKM_le`, `Gardiner.chem_KM_le` |
| rate `O(√δ)` of the limit (7.2.6) | `Gardiner.scaled_jumpGen_rate`, `Gardiner.scaled_jumpGen_tendsto` |
| rate `O(δ)` of the stationary limit (7.2.20)–(7.2.21) | `Gardiner.bdStat_log_rate`, `Gardiner.bdStat_ou_rate` |
| critical slow-time generator, `O(Ω^{-1/(q+1)})` | `Gardiner.critGen_sub_critLim_le`, `Gardiner.cubic_critGen_sub_critLim_le` |
| Kurtz coupling ⇒ characteristic functions, `O(V^{-1/2} log V)` | `Gardiner.kurtz_charFun_le`, `Gardiner.kurtz_charFun_lna_le` |
| exactness of the LNA mean and variance for linear propensities | `Gardiner.lna_exact_of_linear`, `Gardiner.xa_lna_exact`, `Gardiner.mlna_exact`, `Gardiner.cme_lna_exact` |
| (6.3.48) with explicit error | `Gardiner.ex_c1_approx` |

## §6.1 and §6.3: the small noise expansion of the Fokker–Planck equation

| Gardiner | Lean |
| --- | --- |
| (6.1.6)–(6.1.8) | `Gardiner.ouDensity` |
| (6.1.9) | `Gardiner.ouDensity_tendsto_delta` |
| (6.1.10)–(6.1.12) | `Gardiner.ouDensity_scaled` |
| (6.3.1) | `Gardiner.snFP` |
| (6.3.2)–(6.3.8) | `Gardiner.scaledDensity`, `Gardiner.scaledFP`, `Gardiner.smallNoise_scaledFP` |
| (6.3.9)–(6.3.11) | `Gardiner.driftSeries`, `Gardiner.diffSeries`, `Gardiner.densitySeries`, `Gardiner.taylor_exact_of_tower` |
| (6.3.12)–(6.3.13) | `Gardiner.hierRHS_zero`, `Gardiner.hierRHS_one` |
| (6.3.14) | `Gardiner.hierRHS`, `Gardiner.formalRHS_eq_hierRHS`, `Gardiner.hierarchy_iff` |
| (6.3.12) limit with error | `Gardiner.snGen`, `Gardiner.ouGen`, `Gardiner.snGen_sub_ouGen_le` |
| (6.3.16)–(6.3.18) | `Gardiner.snMoment`, `Gardiner.hierMomRHS`, `Gardiner.smallNoise_moment_hierarchy`, `Gardiner.smallNoise_moment_ode` |
| (6.3.19)–(6.3.24) (corrected) | `Gardiner.hierMomRHS_0_1`, `…_1_1`, `…_2_1`, `…_0_2`, `…_1_2`, `…_0_3` |
| (6.3.25)–(6.3.28) | `Gardiner.normalization_iff` |
| (6.3.29)–(6.3.31) | `Gardiner.stationary_moments`, `Gardiner.stationary_mean`, `Gardiner.stationary_variance` |
| (6.3.32)–(6.3.35) | `Gardiner.autocorr_affine`, `Gardiner.autocorr_hierarchy`, `Gardiner.autocorr_hierarchy_deriv`, `Gardiner.autocorr_initial` |
| (6.3.36)–(6.3.37) | `Gardiner.exA`, `Gardiner.exB`, `Gardiner.ex_drift_expansion`, `Gardiner.ex_diff_expansion` |
| (6.3.38) | `Gardiner.ex_stationary` |
| (6.3.39)–(6.3.40) | `Gardiner.ex_corr_one`, `Gardiner.ex_corr_three`, `Gardiner.exMat` |
| (6.3.41)–(6.3.43) (corrected sign) | `Gardiner.ex_eigen1`, `Gardiner.ex_eigen2`, `Gardiner.ex_solution` |
| (6.3.44)–(6.3.47) | `Gardiner.ex_initial`, `Gardiner.exA1`, `Gardiner.exA2` |
| (6.3.48) | `Gardiner.ex_c1_error_eq`, `Gardiner.ex_c1_approx` |
| (6.3.49)–(6.3.51) (corrected) | `Gardiner.fourier_exp_abs`, `Gardiner.ex_spectrum` |
| (6.3.52)–(6.3.54) (corrected) | `Gardiner.snStatEq`, `Gardiner.fpRHS_exp_eq`, `Gardiner.stationary_exp_iff`, `Gardiner.ou_stationary_exp` |
| (6.3.55)–(6.3.56) | `Gardiner.snHJ`, `Gardiner.hamiltonJacobi_of_stationary`, `Gardiner.ou_hamiltonJacobi` |

## §7.1.2: the exact solution of `X ⇌ A`

| Gardiner | Lean |
| --- | --- |
| (7.1.24)–(7.1.26) | `Gardiner.xaME` |
| (7.1.27)–(7.1.28) | `Gardiner.xaOp`, `Gardiner.coeff_xaOp`, `Gardiner.SolvesXA`, `Gardiner.solvesXA_iff` |
| (7.1.34)–(7.1.37) | `Gardiner.xaGen`, `Gardiner.xa_exact_solution`, `Gardiner.xaGen_zero`, `Gardiner.coeff_xaGen`, `Gardiner.xaGenFun`, `Gardiner.xaGenFun_hasDerivAt_t` |
| (7.1.38)–(7.1.40) | `Gardiner.xaGenFun_deriv_one`, `Gardiner.xaGenFun_deriv2_one`, `Gardiner.xa_variance_formula`, `Gardiner.xa_mean_variance_exact` |
| (7.1.41)–(7.1.43) | `Gardiner.xa_moment_identities`, `Gardiner.xa_factorial_moment_identity` |
| (7.1.44)–(7.1.45) | `Gardiner.xaGenFun_tendsto`, `Gardiner.poisson_stationary` |
| (7.1.49)–(7.1.55) | `Gardiner.poissonPMF`, `Gardiner.poisson_solves_xaME`, `Gardiner.solvesXA_poisson`, `Gardiner.xaMean` |

## §7.2.1–7.2.2: jump-process approximation of a diffusion; Kramers–Moyal

| Gardiner | Lean |
| --- | --- |
| (7.2.1)–(7.2.3) | `Gardiner.scaledW`, `Gardiner.ScaledKernelHyp` |
| (7.2.4) | `Gardiner.integral_mul_scaledW`, `Gardiner.scaledW_moment_zero/one/two` |
| (7.2.5) | `Gardiner.scaledW_tendsto_zero` |
| (7.2.6) with rate | `Gardiner.scaled_jumpGen_rate`, `Gardiner.scaled_jumpGen_tendsto` |
| (7.2.9)–(7.2.13) | `Gardiner.randomWalk_moments`, `Gardiner.randomWalk_rate` |
| (7.2.14)–(7.2.15) | `Gardiner.poisson_moments`, `Gardiner.poisson_no_diffusion_limit` |
| (7.2.16)–(7.2.18) | `Gardiner.bdRate`, `Gardiner.bd_moments`, `Gardiner.bd_rate` |
| (7.2.19) | `Gardiner.bdStat`, `Gardiner.bdStat_flux`, `Gardiner.bdStat_stationary`, `Gardiner.bdStat_eq_ratio` |
| (7.2.20)–(7.2.21) with rate | `Gardiner.bdStat_log_rate`, `Gardiner.bdStat_ou_rate` |
| (7.2.22)–(7.2.23) | `Gardiner.km_master_change_of_variables` |
| (7.2.25)–(7.2.26) | `Gardiner.jumpMoment`, `Gardiner.kmGen`, `Gardiner.finJumpMoment`, `Gardiner.finKM` |
| truncation error | `Gardiner.jumpGen_sub_kmGen_le`, `Gardiner.finJumpGen_sub_finKM_le` |
| (7.2.27) | `Gardiner.scaledW_jumpMoment_abs_le`, `Gardiner.scaledW_jumpMoment_tendsto_zero` |

## §7.2.3: van Kampen's system size expansion

| Gardiner | Lean |
| --- | --- |
| (7.2.29)–(7.2.31) | `Gardiner.extRate`, `Gardiner.intMoment`, `Gardiner.jumpMoment_extensive` |
| (7.2.30), (7.2.32) | `Gardiner.finJumpGen_fluct`, `Gardiner.hasDerivAt_fluct_frame`, `Gardiner.vkGen` |
| (7.2.33)–(7.2.34) | `Gardiner.vkCoeff`, `Gardiner.vkCoeff_one`, `Gardiner.vkCoeff_two` |
| (7.2.35) (corrected) | `Gardiner.lnaFP`, `Gardiner.vkGen_sub_lnaGen_le`, `Gardiner.vkGen_tendsto_lnaGen` |
| (7.2.36)–(7.2.39) | `Gardiner.kmFP`, `Gardiner.km_change_of_variables`, `Gardiner.lnaFP_eq_hierRHS_zero` |
| comparison KM ↔ vK | `Gardiner.vkGen_sub_kmGen_le`, `Gardiner.kmGen_sub_lnaGen_le` |
| (7.2.40) (corrected) | the drift `α̃₁'(φ) z` of `Gardiner.lnaFP` |
| (7.2.41)–(7.2.46) | `Gardiner.xaPsi`, `Gardiner.xa_extRate`, `Gardiner.xa_intMoment_one`, `Gardiner.xa_intMoment_two`, `Gardiner.xa_phi_hasDerivAt` |
| (7.2.47) | `Gardiner.xa_vkGen_sub_lnaGen_le` |
| (7.2.48)–(7.2.51) | `Gardiner.lna_mean_solution`, `Gardiner.xaSigma`, `Gardiner.xa_lna_variance`, `Gardiner.xa_lna_matches_exact` |
| (7.2.52)–(7.2.53) | `Gardiner.xa_lna_stationary`, `Gardiner.xaKMStationary`, `Gardiner.xa_km_stationary_flux`, `Gardiner.xa_km_stationary` |
| (7.2.54)–(7.2.58) (corrected) | `Gardiner.xa_km_log_expansion`, `Gardiner.xa_km_log_expansion_z` |
| (7.2.59)–(7.2.61) | `Gardiner.vk_moment_hierarchy`, `Gardiner.integral_moments_lnaFP`, `Gardiner.lna_mean_ode`, `Gardiner.lna_second_moment_ode` |

## §7.2.4–7.2.5: Kurtz's theorem and critical fluctuations

| Gardiner | Lean |
| --- | --- |
| (7.2.64) | the hypothesis `hcouple` |
| (7.2.65)–(7.2.67) | `Gardiner.kurtz_phase`, `Gardiner.kurtz_charFun_le`, `Gardiner.kurtz_charFun_tendsto`, `Gardiner.kurtz_charFun_lna_le` |
| (7.2.68), (7.2.70)–(7.2.75) | `Gardiner.critGen`, `Gardiner.critLim`, `Gardiner.critGen_sub_critLim_le` |
| (7.2.71), (7.2.73), (7.2.77) | `Gardiner.critical_exponent`, `Gardiner.critical_scales` |
| (7.2.69) | `Gardiner.critical_cubic`, `Gardiner.critical_cubic_solution`, `Gardiner.cubic_critGen_sub_critLim_le` |
| (7.2.76) | `Gardiner.critical_mean_eq` |

## §7.5: combinatorial kinetics, chemical Fokker–Planck equation, linear noise approximation

| Gardiner | Lean |
| --- | --- |
| (7.5.3)–(7.5.5) | `Gardiner.stoich` |
| (7.5.6)–(7.5.7) | `Gardiner.orthant_forward`, `Gardiner.orthant_backward`, `Gardiner.propCount_ne_zero_iff` |
| (7.5.8) | `Gardiner.propCount`, `Gardiner.propPoly`, `Gardiner.propPoly_natCast`, `Gardiner.tplus`, `Gardiner.tminus` |
| (7.5.9) | `Gardiner.cme`, `Gardiner.cme_eq`, `Gardiner.latME`, `Gardiner.tsum_mul_latME` |
| (7.5.30) → (7.5.31) | `Gardiner.mjGen_sub_mjKM_le`, `Gardiner.chem_KM_le` |
| (7.5.31) | `Gardiner.chemFPE` |
| (7.5.32) | `Gardiner.chemDrift`, `Gardiner.chemDiff`, `Gardiner.chemDiff_nonneg`, `Gardiner.chem_latDrift`, `Gardiner.chem_latDiff`, `Gardiner.chem_mjDrift`, `Gardiner.chem_mjDiff` |
| linearisation about the deterministic solution | `Gardiner.mvkGen`, `Gardiner.mlnaGen`, `Gardiner.mvkGen_sub_mlnaGen_le` |
| (4.4.51) | `Gardiner.lyapunov_iff`, `Gardiner.lna_cov_stationary` |
| (4.4.83)–(4.4.85) | `Gardiner.meanLin`, `Gardiner.covLin`, `Gardiner.mlna_exact`, `Gardiner.cme_lna_exact` |
| `X ⇌ A` as a network | `Gardiner.xa_chem_affine` |

## Errata (formalized in corrected form; see the module docstrings)

* (7.2.35), (7.2.40): the drift is `α̃₁'(φ) z`, not `α̃₁(φ) z` (`SystemSize`).
* (7.2.56), (7.2.58): `k₁` for `k₂` in the numerator and `δ + δ²` for `δ - δ²` (`ReactionXAvk`).
* (6.3.19)–(6.3.21): `M¹` in place of `M⁰` in the `Ã₁` terms; (6.3.28): `r ≥ 1`, not `r ≠ 1`
  (`SmallNoiseMoments`).
* (6.3.43): `e^{λᵢ t}`, not `e^{-λᵢ t}`; (6.3.51): the factor `-2λ₁` (`SmallNoiseExample`).
* (6.3.54): coefficients of the `ε²` and `ε⁴` terms (`SmallNoiseStationary`).
* (7.2.4): `α₂ = ∫ y²Φ + δA²Q`; the text's value is the leading order (`KramersMoyal`).
-/
import SHSLib.Gardiner.Approx.Calculus
import SHSLib.Gardiner.Approx.SmallNoise
import SHSLib.Gardiner.Approx.SmallNoiseMoments
import SHSLib.Gardiner.Approx.SmallNoiseExample
import SHSLib.Gardiner.Approx.SmallNoiseStationary
import SHSLib.Gardiner.Approx.ReactionXA
import SHSLib.Gardiner.Approx.KramersMoyal
import SHSLib.Gardiner.Approx.JumpStationary
import SHSLib.Gardiner.Approx.SystemSize
import SHSLib.Gardiner.Approx.ReactionXAvk
import SHSLib.Gardiner.Approx.Critical
import SHSLib.Gardiner.Approx.Chemical
import SHSLib.Gardiner.Approx.ChemicalKM
import SHSLib.Gardiner.Approx.ChemicalLNA
