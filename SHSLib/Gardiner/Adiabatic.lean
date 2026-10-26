/-
# Adiabatic elimination of fast variables (Gardiner, §6.4–§6.6)

Index of the adiabatic-elimination layer (C. W. Gardiner, *Handbook of Stochastic Methods*,
§6.4 Kramers' equation and the Smoluchowski limit, §6.5 white noise as a limit of non-white
noise, §6.6 adiabatic elimination in the general case).  It sits next to the small-noise and
system-size layer `SHSLib.Gardiner.Approx` and uses the same conventions:

* all declarations are in the namespace `Gardiner.Adiabatic`;
* error terms are stated on the **backward generator** applied to smooth test functions
  (as `Gardiner.snGen_sub_ouGen_le` does for the small-noise expansion).  Where the text
  expands a forward operator in powers of `γ⁻¹` (or of `ε = γ⁻¹`), we construct an explicit
  *perturbed test function* `φ_γ = f + γ⁻¹φ₁ + γ⁻²φ₂ + …` and prove an exact identity
  `G_γ φ_γ = (reduced generator) f + (explicit remainder)`, then bound the remainder;
* the projection-operator manipulations of the text (`P`, `L₁`, `L₂`, `L₃`, Laplace transform)
  are proved in an arbitrary ring/module (`Gardiner.Adiabatic.ProjHyp`), and their `γ → ∞`
  limits are proved with explicit constants under the boundedness hypotheses that the text
  itself flags (§6.4.5 c);
* for the linear/Gaussian cases, where the text has exact solutions, the moment equations are
  solved exactly and the distance to the reduced (Smoluchowski / white-noise / reduced chemical)
  statistics is bounded uniformly in time;
* the limit and integral interchanges made silently by the text (`d/dt ∫ = ∫ ∂ₜ`, the
  Kramers equation tested against polynomials, the vanishing of the Laplace boundary term,
  linearity of the fast generator on test functions) are **named hypotheses**.

## Approximation guarantees with explicit error terms

| Guarantee | Lean |
| --- | --- |
| free Brownian motion: `0 ≤ Var_S(t) - Var_K(t) ≤ 2Dτ`, all `t ≥ 0` (6.4.1)–(6.4.14) | `Gardiner.Adiabatic.free_variance_rate`, `Gardiner.Adiabatic.free_kramers_moments` |
| OU-driven white-noise limit (6.4.6)–(6.4.10): same `2Dτ` bound | `Gardiner.Adiabatic.ouDriven_variance_rate`, `Gardiner.Adiabatic.ouDriven_instance` |
| harmonic Brownian motion, mean: `≤ 4kτ |⟨x⟩(0)|` | `Gardiner.Adiabatic.harmonic_mean_rate` |
| harmonic Brownian motion, variance: `≤ 8kτ |Var(0) - D/k|` | `Gardiner.Adiabatic.harmonic_variance_rate`, `Gardiner.Adiabatic.harmonic_instance` |
| stationary position variance `D/k` for every `τ` | `Gardiner.Adiabatic.harmonic_stationary`, `Gardiner.Adiabatic.harmonic_stationary_instance` |
| Kramers vs. Smoluchowski generator, `O(γ⁻³)` on smooth test functions (6.4.66) | `Gardiner.Adiabatic.kramers_smoluchowski_bound` |
| Kramers vs. corrected Smoluchowski generator, `O(γ⁻⁴)` (6.4.108) | `Gardiner.Adiabatic.kramers_corrected_bound`, `Gardiner.Adiabatic.kRem_le` |
| same, concrete double well `U = y⁴/4 - y²/2`, `f = sin` | `Gardiner.Adiabatic.kramers_doubleWell`, `Gardiner.Adiabatic.kramers_doubleWell_corr` |
| Laplace-domain elimination (6.4.52): `O(γ⁻²)` error | `Gardiner.Adiabatic.kramers_laplace_bound`, `Gardiner.Adiabatic.tg_kramers_bound` |
| Laplace-domain elimination with `PL₃ ≠ L₃P` (6.5.70): `O(γ⁻¹)` | `Gardiner.Adiabatic.threeScale_laplace_bound`, `Gardiner.Adiabatic.tg_nonCommuting_bound` |
| commuting case (6.5.28), (6.6.26): `O(γ⁻¹)` | `Gardiner.Adiabatic.commuting_laplace_bound`, `Gardiner.Adiabatic.tg_whiteNoise_bound` |
| short-time memory equation (6.4.80), corrected: `‖K‖Mγ⁻²` | `Gardiner.Adiabatic.shortTime_bound`, `Gardiner.Adiabatic.shortTime_instance` |
| `γ²g(γ²t) → δ(t)` (6.5.9): `L τ_c / γ²` on Lipschitz test functions | `Gardiner.Adiabatic.scaled_corr_delta`, `Gardiner.Adiabatic.gaussian_corr_delta` |
| white-noise limit, generator form (6.5.53): `O(γ⁻¹)` | `Gardiner.Adiabatic.wn_generator_bound`, `Gardiner.Adiabatic.wn_ou_instance`, `Gardiner.Adiabatic.wn_telegraph_instance` |
| chemical intermediate (6.6.1)–(6.6.33): mean within `O(γ⁻¹)` uniformly in `t` | `Gardiner.Adiabatic.chem_mean_rate`, `Gardiner.Adiabatic.chem_mean_instance` |
| chemical intermediate: stationary variance of `x` exactly that of (6.6.33) | `Gardiner.Adiabatic.chem_stationary_covariance`, `Gardiner.Adiabatic.chem_reduced_stationary` |
| Haken's model (6.6.64), every coupling scale `s`: `O(ε^{1/2})` | `Gardiner.Adiabatic.haken_slave`, `Gardiner.Adiabatic.haken_noisy_instance` |
| nonlinear case (6.6.86): `O(γ⁻²)` | `Gardiner.Adiabatic.nl_generator_bound`, `Gardiner.Adiabatic.nl_haken_instance` |
| arbitrary nonlinear coupling (6.6.122), corrected sign: `O(γ⁻¹)` | `Gardiner.Adiabatic.nlc_generator`, `Gardiner.Adiabatic.nlc_ou_instance` |

## §6.4 Kramers' equation and the Smoluchowski equation

| Gardiner | Lean |
| --- | --- |
| (6.4.1)–(6.4.5), (6.4.11)–(6.4.14) | `Gardiner.Adiabatic.free_kramers_moments`, `Gardiner.Adiabatic.free_variance_rate`, `Gardiner.Adiabatic.tau_one_sub_exp_bounds` |
| (6.4.6)–(6.4.10) | `Gardiner.Adiabatic.ouDriven_variance_rate`, `Gardiner.Adiabatic.ouDriven_instance` |
| (6.4.15)–(6.4.18), harmonic force | `Gardiner.Adiabatic.harmonic_mean_rate`, `Gardiner.Adiabatic.harmonic_mean_rate_exact`, `Gardiner.Adiabatic.harm_mean_sol`, `Gardiner.Adiabatic.harmonic_variance_exact`, `Gardiner.Adiabatic.harmonic_variance_rate`, `Gardiner.Adiabatic.harm_roots`, `Gardiner.Adiabatic.harmonic_moments_sol`, `Gardiner.Adiabatic.harmonic_instance` |
| (6.4.18) stationary statistics | `Gardiner.Adiabatic.harmonic_stationary`, `Gardiner.Adiabatic.harmonic_stationary_instance` |
| (6.4.19)–(6.4.26), (6.4.36), (6.4.41) | `Gardiner.Adiabatic.ProjHyp`, `Gardiner.Adiabatic.split_vw`, `Gardiner.Adiabatic.tg_projHyp`, `Gardiner.Adiabatic.mat_projHyp`, `Gardiner.Adiabatic.r_projHyp` |
| (6.4.42)–(6.4.44) | `Gardiner.Adiabatic.proj_v_eq`, `Gardiner.Adiabatic.proj_w_eq`, `Gardiner.Adiabatic.hasDerivAt_proj_v`, `Gardiner.Adiabatic.hasDerivAt_proj_w`, `Gardiner.Adiabatic.proj_time_instance` |
| (6.4.45)–(6.4.47) | `Gardiner.Adiabatic.laplace`, `Gardiner.Adiabatic.laplace_deriv`, `Gardiner.Adiabatic.laplace_v_eq`, `Gardiner.Adiabatic.laplace_instance` |
| (6.4.48)–(6.4.51) | `Gardiner.Adiabatic.exact_elimination`, `Gardiner.Adiabatic.tg_exact_elimination_instance` |
| (6.4.52)–(6.4.53) with error | `Gardiner.Adiabatic.kramers_laplace_bound`, `Gardiner.Adiabatic.tg_kramers_bound` |
| (6.4.54)–(6.4.57) | `Gardiner.Adiabatic.gauss`, `Gardiner.Adiabatic.L1_gauss`, `Gardiner.Adiabatic.flux_gauss` |
| (6.4.58)–(6.4.61) | `Gardiner.Adiabatic.He`, `Gardiner.Adiabatic.hermite_eigen`, `Gardiner.Adiabatic.hermite_recursion` |
| (6.4.62)–(6.4.64), (6.4.103) | `Gardiner.Adiabatic.L2poly`, `Gardiner.Adiabatic.L2_P0`, `Gardiner.Adiabatic.L2_P1`, `Gardiner.Adiabatic.L2_P2` |
| (6.4.65)–(6.4.66) with error | `Gardiner.Adiabatic.kGen`, `Gardiner.Adiabatic.smolGen`, `Gardiner.Adiabatic.kramers_generator_expansion`, `Gardiner.Adiabatic.kramers_smoluchowski_bound` |
| (6.4.70)–(6.4.76) | `Gardiner.Adiabatic.memKernel`, `Gardiner.Adiabatic.hasDerivAt_memKernel` |
| (6.4.77)–(6.4.78) (corrected) | `Gardiner.Adiabatic.memory_to_telegraph`, `Gardiner.Adiabatic.telegraph_to_memory` |
| (6.4.79) | `Gardiner.Adiabatic.memKernel_ibp`, `Gardiner.Adiabatic.integral_exp_kernel` |
| (6.4.80) (corrected) with error | `Gardiner.Adiabatic.shortTime_bound`, `Gardiner.Adiabatic.shortTime_instance` |
| (6.4.81)–(6.4.83) | `Gardiner.Adiabatic.absorbing_marginal` |
| (6.4.84)–(6.4.85) | `Gardiner.Adiabatic.reflecting_iff_current` |
| (6.4.86)–(6.4.89) | `Gardiner.Adiabatic.reflecting_w_even`, `Gardiner.Adiabatic.reflecting_smoluchowski` |
| (6.4.90)–(6.4.98) | `Gardiner.Adiabatic.resolvent_expansion`, `Gardiner.Adiabatic.longTime_expansion` |
| (6.4.99)–(6.4.101) | `Gardiner.Adiabatic.longTime_rearranged`, `Gardiner.Adiabatic.tg_A`, `Gardiner.Adiabatic.tg_B`, `Gardiner.Adiabatic.tg_C`, `Gardiner.Adiabatic.tg_D`, `Gardiner.Adiabatic.tg_longTime`, `Gardiner.Adiabatic.tg_corrected` |
| (6.4.102)–(6.4.108) with error | `Gardiner.Adiabatic.smolCorr`, `Gardiner.Adiabatic.kRem`, `Gardiner.Adiabatic.kRem_le`, `Gardiner.Adiabatic.kramers_corrected_bound`, `Gardiner.Adiabatic.kramers_doubleWell`, `Gardiner.Adiabatic.kramers_doubleWell_corr`, `Gardiner.Adiabatic.kramers_doubleWell_partials` |
| (6.4.104) `B = 0` | absence of a `γ⁻²` term in `Gardiner.Adiabatic.kramers_generator_expansion` |
| (6.4.109) | `Gardiner.Adiabatic.kramers_initial_layer`, `Gardiner.Adiabatic.kramers_initial_layer_instance` |
| (6.4.110)–(6.4.111) | `Gardiner.Adiabatic.boundary_rescaling` |
| (6.4.112)–(6.4.113) | `Gardiner.Adiabatic.psi0_stationary`, `Gardiner.Adiabatic.psi0'_stationary` |

## §6.5 White noise as a limit of non-white noise

| Gardiner | Lean |
| --- | --- |
| (6.5.1)–(6.5.12) with rate | `Gardiner.Adiabatic.scaled_corr_integral`, `Gardiner.Adiabatic.scaled_corr_delta`, `Gardiner.Adiabatic.gaussCorr`, `Gardiner.Adiabatic.gaussian_corr_delta` |
| (6.5.13)–(6.5.19) | `Gardiner.Adiabatic.ProjHyp`, `Gardiner.Adiabatic.tg_projHyp` (telegraph fast process) |
| (6.5.20)–(6.5.28) | `Gardiner.Adiabatic.commuting_L3_v`, `Gardiner.Adiabatic.commuting_L3_w`, `Gardiner.Adiabatic.exact_elimination_L3`, `Gardiner.Adiabatic.commuting_laplace_bound`, `Gardiner.Adiabatic.tg_whiteNoise_bound`, `Gardiner.Adiabatic.tg_commuting_instance` |
| (6.5.29)–(6.5.42) | `Gardiner.Adiabatic.half_integral_of_even`, the Poisson-equation hypotheses of `Gardiner.Adiabatic.wn_generator` |
| (6.5.43)–(6.5.47) | `Gardiner.Adiabatic.strat_ito_flux`, `Gardiner.Adiabatic.strat_ito_backward`, `Gardiner.Adiabatic.wn_stratonovich`, `Gardiner.Adiabatic.wn_stratonovich_ou` |
| (6.5.48)–(6.5.53) with error | `Gardiner.Adiabatic.wnGen`, `Gardiner.Adiabatic.wnPhix`, `Gardiner.Adiabatic.wnR1`, `Gardiner.Adiabatic.wnR2`, `Gardiner.Adiabatic.wn_generator`, `Gardiner.Adiabatic.wn_generator_bound` |
| §6.5.1 instances | `Gardiner.Adiabatic.ouPhi`, `Gardiner.Adiabatic.wn_ou_instance`, `Gardiner.Adiabatic.tgFast`, `Gardiner.Adiabatic.wn_telegraph_instance` |
| (6.5.54)–(6.5.66) | `Gardiner.Adiabatic.wn_generator_time`, `Gardiner.Adiabatic.wn_time_instance` |
| (6.5.67)–(6.5.70) with error | `Gardiner.Adiabatic.exact_elimination_L3`, `Gardiner.Adiabatic.threeScale_laplace_bound`, `Gardiner.Adiabatic.tg_nonCommuting_bound`, `Gardiner.Adiabatic.tg_exact_elimination_L3_instance` |
| (6.5.71)–(6.5.74) | `Gardiner.Adiabatic.wn_generator_time` (`D(τ)` time dependent), `Gardiner.Adiabatic.wn_time_instance` |

## §6.6 Adiabatic elimination in the general case

| Gardiner | Lean |
| --- | --- |
| (6.6.1)–(6.6.7) | `Gardiner.Adiabatic.chem_mean_rate` (mean equations (6.6.2)) |
| (6.6.8)–(6.6.11) | `Gardiner.Adiabatic.chem_transform_drift`, `Gardiner.Adiabatic.chem_transform_diffusion` |
| (6.6.12)–(6.6.16) (corrected) | `Gardiner.Adiabatic.chem_alpha_split` |
| (6.6.17)–(6.6.28) | `Gardiner.Adiabatic.commuting_L3_v`, `Gardiner.Adiabatic.commuting_laplace_bound`, `Gardiner.Adiabatic.exact_elimination_L3` |
| (6.6.29)–(6.6.33) | `Gardiner.Adiabatic.chem_effective_diffusion` |
| (6.6.34)–(6.6.35) | `Gardiner.Adiabatic.chem_stationary_covariance`, `Gardiner.Adiabatic.chem_reduced_stationary`, `Gardiner.Adiabatic.chem_mean_rate`, `Gardiner.Adiabatic.chem_mean_instance` |
| (6.6.36)–(6.6.39) | `Gardiner.Adiabatic.haken_deterministic` |
| (6.6.40)–(6.6.46) (corrected) | `Gardiner.Adiabatic.haken_beta_drift` |
| (6.6.47)–(6.6.64) (corrected) | `Gardiner.Adiabatic.haken_slave`, `Gardiner.Adiabatic.haken_rewrite`, `Gardiner.Adiabatic.haken_noisy_instance` |
| (6.6.65)–(6.6.87) with error | `Gardiner.Adiabatic.nlGen`, `Gardiner.Adiabatic.nl_generator`, `Gardiner.Adiabatic.nl_generator_bound`, `Gardiner.Adiabatic.hakenPhi`, `Gardiner.Adiabatic.nl_haken_instance` |
| (6.6.88)–(6.6.106) (corrected) | `Gardiner.Adiabatic.secondOrder_commutator_form`, `Gardiner.Adiabatic.P_comm_L3_eq_zero`, `Gardiner.Adiabatic.secondOrder_reduced`, `Gardiner.Adiabatic.mat_secondOrder`, `Gardiner.Adiabatic.nl_second_order_order3` |
| (6.6.107)–(6.6.123) (corrected) | `Gardiner.Adiabatic.nlc_generator`, `Gardiner.Adiabatic.nlc_ou_instance` |

## Errata (formalized in corrected form; see the module docstrings)

* (6.4.2): the noise strength is `√(2kβT)`; `Γ` is printed for the temperature `T`.
* (6.4.77): the left side is `∂²p̂/∂t²`, `p` is printed (`ShortTime`).
* (6.4.80): the right side lacks the factor `γ⁻¹`; with it the equation holds for all `t ≥ 0`
  up to `O(γ⁻²)` (`ShortTime`).
* (6.4.85): the current is printed with the overall sign reversed; immaterial for (6.4.84)
  (`Boundary`).
* The unnumbered identity after (6.4.101):
  `L₁⁻¹(1 - P)L₂L₁⁻¹L₂ = (1/√2) P₂ (U' + ∂_y)²`, not `√2 P₂ (U' + ∂_y)²`, since `L₁⁻¹P₂ = -½P₂`.
  In `Gardiner.Adiabatic.kramers_generator_expansion` this is the coefficient `½He₂ = (1/√2)Q₂`
  of `f''` in `φ₂` (`KramersGenerator`).
* The text "expand the inverse in (6.5.91)" before (6.4.92) refers to (6.4.91).
* (6.5.49): `α(t/γ²)` should be `α(γ²t)`, consistent with (6.5.4) (`WhiteNoise` uses `γ²t`).
* (6.5.72): the drift term of the forward operator is `-∂_α A(α, τ)`, as in (6.5.15)
  (`WhiteNoise`, backward form `A ∂_α`).
* (6.6.4): the reduced deterministic equation is `ẋ = (a - x)/2` (`Chemical`).
* (6.6.15): the `γ^{-1/2}∂_α α` term has coefficient `+½`, not `-1` (`Chemical`).
* (6.6.46): the first term is `∂ₓ aβx`, not `∂_β aβx` (`Nonlinear`).
* (6.6.64): `∂/∂k` is printed for `∂/∂x` (`Nonlinear`).
* (6.6.94): `[a(x)]²` should be `[c(x)]²` (`Nonlinear`).
* (6.6.120), (6.6.122): the overall sign as printed gives a negative diffusion coefficient; the
  correct diffusion is `+D = ⟨ψχ⟩₀` (`Nonlinear`).
-/
import SHSLib.Gardiner.Adiabatic.Projector
import SHSLib.Gardiner.Adiabatic.ProjectorBound
import SHSLib.Gardiner.Adiabatic.Telegraph
import SHSLib.Gardiner.Adiabatic.Brownian
import SHSLib.Gardiner.Adiabatic.KramersGenerator
import SHSLib.Gardiner.Adiabatic.WhiteNoise
import SHSLib.Gardiner.Adiabatic.Chemical
import SHSLib.Gardiner.Adiabatic.Nonlinear
import SHSLib.Gardiner.Adiabatic.ShortTime
import SHSLib.Gardiner.Adiabatic.Boundary
import SHSLib.Gardiner.Adiabatic.Examples
