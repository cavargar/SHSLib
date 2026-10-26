/-
# First-passage times, bistability and escape over a barrier (Gardiner §5.2.7–5.2.8, §7.4, Ch. 9)

Index of the escape layer (C. W. Gardiner, *Handbook of Stochastic Methods*: §5.2.7 mean
first-passage times for homogeneous one-dimensional processes, §5.2.8 probability of exit through
a particular end, §7.4 mean first-passage times for birth–death processes, Ch. 9 bistability,
metastability and escape problems).  It sits next to `SHSLib.Gardiner.Approx` and
`SHSLib.Gardiner.Adiabatic` and uses the same conventions:

* all declarations are in the namespace `Gardiner.Escape`;
* **exact layer**: the boundary-value problems of §5.2.7–5.2.8 and §7.4 are solved exactly, with
  existence *and* uniqueness (`IsBwdSol A B f u` means `u` is twice differentiable with
  `A u' + ½ B u'' = f`);
* **asymptotic layer**: every small-`D` statement of §5.2.7 c), §9.1 and §9.2 is a genuine
  inequality valid for all `0 < D ≤ 1`, with an explicit error term (relative `O(√D)` for
  Gaussian Laplace integrals, `O(D)` for endpoint integrals), proved from the quantitative
  Laplace method of `Gardiner.Escape.laplace_min` and its variants; the hypotheses on the
  potential are bundled in `Gardiner.Escape.KramersHyp` and `Gardiner.Escape.TwoWellHyp`;
* **formal steps as named hypotheses**: Kramers' ansatz (9.2.7), (9.3.52), the sharp-peak
  evaluations (7.4.18), (9.3.55)–(9.3.62), the Green identities (9.3.24)–(9.3.25), (9.3.40) of
  the Matkowsky–Schuss construction, and the interchanges of `∂ₓ` with `∫₀^∞ dt` in (5.2.150),
  (5.2.182) are hypotheses of the theorems that use them; everything downstream is proved;
* **exact cases**: where the text's formulas are exact — the symmetric decay problem (9.1.25),
  the reflecting-barrier formula (9.1.31), the quadratic saddle of §9.3.4, the layer equations of
  §9.3.1 — this is proved;
* every main theorem is applied to a concrete non-degenerate instance: the quartic double well
  `U = x⁴/4 - x²/2` (`Gardiner.Adiabatic.dwU 0`), the asymmetric well
  `U = x⁴/4 - x³/3 - x²` (`Gardiner.Escape.awU`), the Ornstein–Uhlenbeck process, the inverted
  parabola, the walk `t⁺ = 1`, `t⁻ = 2`, and the saddle `γ = 4`, `U₂ = 5`.

## Approximation guarantees with explicit error terms

| Guarantee | Lean |
| --- | --- |
| exact MFPT over a barrier vs. Arrhenius/Kramers (5.2.174): `|T/T_K - 1| ≤ C√D`, `0 < D ≤ 1` | `Gardiner.Escape.mfpt_kramers`, `Gardiner.Escape.mfpt_kramers_tendsto` |
| same to the barrier top (9.1.9), `π(k_ak_b)^{-1/2}e^{ΔU/D}` | `Gardiner.Escape.mfpt_kramers_half`, `Gardiner.Escape.mfpt_kramers_half_tendsto` |
| quartic double well: `T(-1 → ½) = √2π e^{1/4D}(1 + O(√D))`, `T(-1 → 0) = (π/√2)e^{1/4D}(1 + O(√D))` | `Gardiner.Escape.doubleWell_mfpt`, `Gardiner.Escape.doubleWell_mfpt_half` |
| reflecting barrier at `a → -∞` gives (5.2.165) | `Gardiner.Escape.smolReflA_tendsto`, `Gardiner.Escape.doubleWell_reflect_limit` |
| normalisation (9.1.6), relative `O(√D)` | `Gardiner.Escape.normalization_asymp`, `Gardiner.Escape.asymWell_normalization` |
| population ratio (9.2.23), relative `O(√D)`; upper well exponentially empty (9.1.7)–(9.1.8) | `Gardiner.Escape.population_ratio_asymp`, `Gardiner.Escape.population_small`, `Gardiner.Escape.asymWell_population_ratio`, `Gardiner.Escape.asymWell_population_small` |
| barrier integral (9.1.13), relative `O(√D)` | `Gardiner.Escape.barrier_integral_asymp`, `Gardiner.Escape.asymWell_barrier_integral` |
| relaxation time (9.2.18)–(9.2.25), relative `O(√D)` | `Gardiner.Escape.relaxTime_asymp`, `Gardiner.Escape.asymWell_relaxTime` |
| splitting probability far from the barrier (9.1.16), relative `O(√D)` | `Gardiner.Escape.splitting_far`, `Gardiner.Escape.asymWell_splitting_far` |
| splitting probability in the barrier layer (9.1.20)–(9.1.21), absolute `O(√D)` | `Gardiner.Escape.splitting_near`, `Gardiner.Escape.asymWell_splitting_near` |
| §7.4.2 right: small-jump rates, `|log(t⁺/t⁻) - 2(t⁺-t⁻)/(t⁺+t⁻)| ≤ 4|δA/B|³` | `Gardiner.Escape.bdRate_km_ratio`, `Gardiner.Escape.bdRate_log_ratio_close` |
| §7.4.2 wrong: unit jumps, Kramers–Moyal barrier strictly too low, MFPT ratio `→ ∞` | `Gardiner.Escape.km_exponent_lt_log`, `Gardiner.Escape.km_barrier_lt`, `Gardiner.Escape.km_mfpt_ratio_tendsto` |
| sharp-peak evaluation (7.4.18): relative error `δ` of the slowly varying factor | `Gardiner.Escape.bdT_sharp_peak`, `Gardiner.Escape.bdT_sharp_peak_instance` |
| §9.3.4: `|λ/γ - (1 + U₂/γ²)| ≤ (U₂/γ²)²` (9.3.95) | `Gardiner.Escape.lam_ratio_bound` |
| §9.3.4: `τ₀/τ₂ < τ₃/τ₁`, gap `≤ 3s²` (9.3.100) | `Gardiner.Escape.ratio_comparison` |
| (9.3.109) at temperature `T`: exact 1-D time vs. Kramers, `O(√T)` | `Gardiner.Escape.brownian_doubleWell_tau1` |

## §5.2.7–5.2.8 Mean first-passage times and exit probabilities

| Gardiner | Lean |
| --- | --- |
| (5.2.139)–(5.2.152) | `Gardiner.Escape.moment_ibp` (`⟨Tⁿ⟩ = n∫tⁿ⁻¹G`), `Gardiner.Escape.moments_printed_wrong` |
| (5.2.153)–(5.2.154) | `Gardiner.Escape.mfpt_ode_of_backward`, `Gardiner.Escape.backward_ode_instance` |
| (5.2.155)–(5.2.158) | `Gardiner.Escape.IsBwdSol`, `Gardiner.Escape.fpPsi`, `Gardiner.Escape.flux_deriv`, `Gardiner.Escape.combo_isBwdSol`, `Gardiner.Escape.bwd_unique`, `Gardiner.Escape.mfptTwo`, `Gardiner.Escape.mfptTwo_spec` |
| (5.2.159)–(5.2.161) | `Gardiner.Escape.bwd_unique_refl_a`, `Gardiner.Escape.bwd_unique_refl_b`, `Gardiner.Escape.mfptReflA`, `Gardiner.Escape.mfptReflA_spec`, `Gardiner.Escape.mfptReflB`, `Gardiner.Escape.mfptReflB_spec` |
| (5.2.162)–(5.2.165) | `Gardiner.Escape.smolReflA_eq`, `Gardiner.Escape.smolReflA_tendsto`, `Gardiner.Escape.mfptBarrier` |
| (5.2.166)–(5.2.176) with rate | `Gardiner.Escape.arrheniusTime`, `Gardiner.Escape.KramersHyp`, `Gardiner.Escape.mfpt_kramers`, `Gardiner.Escape.doubleWell_mfpt` |
| (5.2.177)–(5.2.183) | `Gardiner.Escape.condExit_ode_of_backward`, `Gardiner.Escape.backward_ode_instance` |
| (5.2.183)–(5.2.185) solved | `Gardiner.Escape.greenSol`, `Gardiner.Escape.greenSol_spec`, `Gardiner.Escape.condExit_spec`, `Gardiner.Escape.condExit_add` |
| (5.2.186)–(5.2.190) (corrected) | `Gardiner.Escape.exitA`, `Gardiner.Escape.exitB`, `Gardiner.Escape.exitA_spec`, `Gardiner.Escape.exitA_add_exitB`, `Gardiner.Escape.exitA_printed_wrong` |
| instance | `Gardiner.Escape.ou_exit_instance` |

## §7.4 Mean first-passage times for birth–death processes

| Gardiner | Lean |
| --- | --- |
| (7.4.1)–(7.4.3) | `Gardiner.Escape.bdBwd` |
| (7.4.4)–(7.4.5) (corrected sign) | `Gardiner.Escape.bd_U_recursion` |
| (7.4.6)–(7.4.12) | `Gardiner.Escape.bdPhi`, `Gardiner.Escape.bdS`, `Gardiner.Escape.bdTreflA`, `Gardiner.Escape.bdT_reflA_spec`, `Gardiner.Escape.bdT_reflA_unique` |
| (7.4.13) (corrected) | `Gardiner.Escape.bdTreflB`, `Gardiner.Escape.bdT_reflB_spec`, `Gardiner.Escape.bdT_reflB_printed_wrong` |
| (7.4.14)–(7.4.15) (corrected) | `Gardiner.Escape.absProb`, `Gardiner.Escape.absProb_spec`, `Gardiner.Escape.absProb_tendsto_summable`, `Gardiner.Escape.absProb_tendsto_not_summable`, `Gardiner.Escape.absProb_printed_wrong` |
| (7.4.16) | `Gardiner.Escape.bdPhi_detailed_balance`, `Gardiner.Escape.bd_stationary_product` |
| (7.4.17) (corrected upper limit) | `Gardiner.Escape.bdT_reflA_stationary` |
| (7.4.18)–(7.4.19) | `Gardiner.Escape.bdT_sharp_peak`, `Gardiner.Escape.bdT_sharp_peak_instance` |
| §7.4.2 | `Gardiner.Escape.bdRate_km_ratio`, `Gardiner.Escape.bdRate_log_ratio_close`, `Gardiner.Escape.km_lt_log_of_one_lt`, `Gardiner.Escape.km_exponent_lt_log`, `Gardiner.Escape.km_barrier_lt`, `Gardiner.Escape.km_mfpt_ratio_tendsto` |
| instance | `Gardiner.Escape.bd_instance` |

**What the comparison of §7.4.2 gets right and wrong.**  Right: for the small-jump scaling of
§7.2.1c (`t^± = ±A/(2δ) + B/(2δ²)`) the Kramers–Moyal Fokker–Planck equation reproduces the
exact one-step exponent `log(t⁺/t⁻)` up to `O(δ³)` per step, so the stationary distributions and
hence the mean first-passage times (7.4.16)–(7.4.17) agree as `δ → 0`.  Wrong: for unit jumps in a
system of size `V` the Kramers–Moyal exponent `2(t⁻ - t⁺)/(t⁻ + t⁺)` is strictly smaller in
absolute value than `log(t⁻/t⁺)` wherever `t⁺ ≠ t⁻`, so the Fokker–Planck barrier is strictly too
low and the Fokker–Planck mean first-passage time is exponentially (in `V`) too short.

## §9.1 Diffusion in a double-well potential

| Gardiner | Lean |
| --- | --- |
| (9.1.1)–(9.1.3) | `Gardiner.Escape.TwoWellHyp`, `Gardiner.Escape.normInt`, `Gardiner.Escape.popA`, `Gardiner.Escape.popC` |
| (9.1.4)–(9.1.6) with rate | `Gardiner.Escape.normalization_asymp` |
| (9.1.7)–(9.1.8) with rate | `Gardiner.Escape.population_small` |
| (9.1.9) with rate | `Gardiner.Escape.mfpt_kramers_half`, `Gardiner.Escape.doubleWell_mfpt_half` |
| (9.1.10)–(9.1.12), (9.1.17) | `Gardiner.Escape.splitC`, `Gardiner.Escape.splitA`, `Gardiner.Escape.splitA_add_splitC`, `Gardiner.Escape.exitA_spec` |
| (9.1.13) with rate | `Gardiner.Escape.barrier_integral_asymp` |
| (9.1.14)–(9.1.16) with rate | `Gardiner.Escape.splitting_far` |
| (9.1.18)–(9.1.21) with rate (corrected (9.1.19)) | `Gardiner.Escape.gerf`, `Gardiner.Escape.gauss_tail_eq`, `Gardiner.Escape.splitting_near` |
| (9.1.22)–(9.1.24) | `Gardiner.Escape.condExit_spec`, `Gardiner.Escape.greenSol_eq_split`, `Gardiner.Escape.condExit_add` |
| (9.1.25) exact | `Gardiner.Escape.symmetric_decay`, `Gardiner.Escape.invertedParabola_decay` |
| (9.1.26)–(9.1.32) | `Gardiner.Escape.smolReflB_eq` ((9.1.31) is exactly the reflecting-barrier MFPT), `Gardiner.Escape.doubleWell_reflB` |
| asymmetric instance | `Gardiner.Escape.awU`, `Gardiner.Escape.awHyp` and the `asymWell_*` theorems |

## §9.2 Equilibration of populations in each well

| Gardiner | Lean |
| --- | --- |
| (9.2.1)–(9.2.6) | `Gardiner.Escape.flux_identity`, `Gardiner.Escape.kramers_integrated` |
| (9.2.7)–(9.2.8) | `Gardiner.Escape.kramers_ansatz` |
| (9.2.9)–(9.2.13) (corrected) | `Gardiner.Escape.barrier_population`, `Gardiner.Escape.barrier_population_printed_wrong` |
| (9.2.14)–(9.2.15) (corrected), three-state interpretation | `Gardiner.Escape.threeState_stationary` |
| (9.2.16)–(9.2.18) (corrected sign) | `Gardiner.Escape.relaxation_rates`, `Gardiner.Escape.relaxTime` |
| (9.2.19)–(9.2.20) | `Gardiner.Escape.escape_time` |
| (9.2.21)–(9.2.25) with rate | `Gardiner.Escape.relaxTime_asymp`, `Gardiner.Escape.population_ratio_asymp`, `Gardiner.Escape.Hfac` |
| (9.2.26)–(9.2.33) chymotrypsinogen (corrected) | `Gardiner.Escape.chymo_extremum`, `Gardiner.Escape.chymo_population_ratio`, `Gardiner.Escape.chymoH`, `Gardiner.Escape.chymo_H_ratio`, `Gardiner.Escape.chymo_relaxTime` |
| (9.2.34)–(9.2.45) | `Gardiner.Escape.bd_mass_flux`, `Gardiner.Escape.bd_flux_beta`, `Gardiner.Escape.bd_flux_identity`, `Gardiner.Escape.bdPhi_detailed_balance` |
| (9.2.46)–(9.2.49) (corrected ranges) | `Gardiner.Escape.discrete_ansatz_M` |
| (9.2.50) | `Gardiner.Escape.bdSplit_spec` |
| instances | `Gardiner.Escape.populations_instance`, `Gardiner.Escape.bd_instance` |

## §9.3 Bistability in multivariable systems

| Gardiner | Lean |
| --- | --- |
| (9.3.1)–(9.3.11) | setting; `Gardiner.Escape.innerSol` |
| (9.3.12)–(9.3.14) | `Gardiner.Escape.interior_layer`, `Gardiner.Escape.interior_layer_unbounded` |
| (9.3.15)–(9.3.22) (corrected sign) | `Gardiner.Escape.bdryLayer`, `Gardiner.Escape.boundary_layer`, `Gardiner.Escape.boundary_layer_tendsto`, `Gardiner.Escape.boundary_layer_printed_unbounded` |
| (9.3.23)–(9.3.31) (corrected) | `Gardiner.Escape.exit_C0`, `Gardiner.Escape.exit_C0_potential`, `Gardiner.Escape.exit_C0_printed_wrong` |
| (9.3.32)–(9.3.35) | `Gardiner.Escape.sepLayer`, `Gardiner.Escape.separatrix_layer`, `Gardiner.Escape.separatrix_layer_tendsto` |
| (9.3.36) (corrected) | `Gardiner.Escape.separatrix_C0` |
| (9.3.37)–(9.3.43) (corrected) | `Gardiner.Escape.meanExit_C0` |
| (9.3.44)–(9.3.46) | `Gardiner.Escape.separatrix_layer_tendsto` (the factor `√(π/2κ)`) |
| (9.3.47)–(9.3.59) | `Gardiner.Escape.kramers_multi_integrated` |
| (9.3.60)–(9.3.64) | `Gardiner.Escape.kramers_multi_relaxation` |
| (9.3.65)–(9.3.69) | `Gardiner.Escape.bmPs`, `Gardiner.Escape.bm_partials`, `Gardiner.Escape.bm_drift`, `Gardiner.Escape.bm_current` |
| (9.3.70)–(9.3.72) | `Gardiner.Escape.bm_plane_deriv`, `Gardiner.Escape.bm_plane_max_quadratic` |
| (9.3.73)–(9.3.84), exact for the quadratic saddle | `Gardiner.Escape.bm_root`, `Gardiner.Escape.bm_x_exact`, `Gardiner.Escape.bm_assumption_III` |
| (9.3.85)–(9.3.87) (corrected) | `Gardiner.Escape.bmPw`, `Gardiner.Escape.bm_pw_eq`, `Gardiner.Escape.bm_pw_printed_wrong` |
| (9.3.88) | `Gardiner.Escape.bmKappa0`, `Gardiner.Escape.bm_kappa0` |
| (9.3.89)–(9.3.90) | `Gardiner.Escape.bm_tau0` |
| (9.3.91)–(9.3.95) | `Gardiner.Escape.tau1`, `Gardiner.Escape.smolReflA_eq`, `Gardiner.Escape.tau0_div_tau2`, `Gardiner.Escape.lam_ratio_bound` |
| (9.3.96)–(9.3.97) (corrected) | `Gardiner.Escape.corrT`, `Gardiner.Escape.corrT_bwd`, `Gardiner.Escape.corrT_spec`, `Gardiner.Escape.tau3`, `Gardiner.Escape.tau3_spec`, `Gardiner.Escape.tau3_printed_wrong` |
| (9.3.98)–(9.3.99), exact for the quadratic saddle | `Gardiner.Escape.tau3_quadratic` |
| (9.3.100) (first order only) | `Gardiner.Escape.ratio_comparison` |
| (9.3.101)–(9.3.108) (corrected) | `Gardiner.Escape.temp_rescale` |
| (9.3.109) | `Gardiner.Escape.mfptBarrier_add_const`, `Gardiner.Escape.brownian_doubleWell_tau1` |
| (9.3.110)–(9.3.113) | `Gardiner.Escape.separatrix_line` |
| instances | `Gardiner.Escape.exitPoints_instance`, `Gardiner.Escape.brownianSaddle_instance`, `Gardiner.Escape.corrSmol_instance` |

Fig. 9.4 (simulations) is numerical and not formalised; the comparisons it illustrates are
`Gardiner.Escape.brownian_doubleWell_tau1` (exact 1-D vs. Kramers), `Gardiner.Escape.tau3_quadratic`
(corrected Smoluchowski) and `Gardiner.Escape.ratio_comparison` (our theory vs. corrected
Smoluchowski).

## Errata (formalized in corrected form; see the module docstrings)

* (5.2.152): `⟨Tⁿ⟩ = n∫₀^∞ tⁿ⁻¹G dt`; the factor `n` is missing (`FirstPassage`).
* (5.2.189)–(5.2.190): the exit probabilities involve `1/ψ`, not `ψ` (`FirstPassage`).
* (7.4.5): the right-hand side is `-1` (`BirthDeath`).
* (7.4.13): the outer factor is `φ(y-1) = t⁺(y)φ(y)/t⁻(y)`, not `φ(y)` (`BirthDeath`).
* (7.4.14)–(7.4.15): the products are `∏ t⁻/t⁺`, and the absorption probability is
  `Σ_{k≥i}ρ_k/Σ_{k≥0}ρ_k`, not `M/(1 + M)` (`BirthDeath`).
* (7.4.17)–(7.4.18): the upper summation limit is `x₃ - 1` (`BirthDeath`).
* (9.1.19): the error function making (9.1.20)–(9.1.21) true is `√(2/π)∫₀ˣe^{-t²/2}`
  (`Splitting`).
* (9.1.30): the case label should read `x' < b` (`Decay`).
* (9.2.4): `n_a = ∫_{-∞}^b p_s`.  (9.2.13): `N_a`, `N_c` are divided by `n_a`, `n_c`.  (9.2.14):
  the coefficient of `N₀` is `Dn₀⁻¹(κ⁻¹ + μ⁻¹)`.  (9.2.16): `Ṅ_a = -r_aN_a + r_cN_c`.
  The label (9.3.32) in §9.2.2 should be (9.2.32).  (9.2.33): factor `γ` (not `γ⁻¹`),
  `(β_aβ_c)^{1/4}`, and `2τ_r(0)`.  (9.2.49): summation ranges (`Populations`).
* (9.3.18)–(9.3.19): the boundary-layer equation is `-(v·ν)f' + f'' = 0` and its bounded solution
  `g + C₁(1 - e^{(v·ν)ρ})` (`v·ν < 0`) (`ExitPoints`).
* (9.3.26): `ε ν·∇f = (v·ν)(C₀ - g)` (factor `ε⁻¹` and sign); (9.3.28) is correct only when
  `(v + ∇φ)·ν = 0` (e.g. the potential case (9.3.30)) (`ExitPoints`).
* (9.3.36): the factors `v·ν` vanish on a separatrix; corrected form in
  `Gardiner.Escape.separatrix_C0` (`ExitPoints`).
* (9.3.40)–(9.3.43): sign of the right-hand side of (9.3.40), `|v·ν|` in (9.3.41), `e^{-φ/ε}` in
  (9.3.43), whose left side is `T = e^{K/ε}τ` (`ExitPoints`).
* (9.3.87): the factor `λ(2π/(λ² - U₂))^{1/2}` is missing; (9.3.88) is correct (`BrownianSaddle`).
* (9.3.89), (9.3.94): the factor `n_a` from (9.2.19) is missing (it cancels in `τ₀/τ₂`)
  (`BrownianSaddle`).
* (9.3.97): the factor is `[1 + γ⁻²U'']⁻¹` (`BrownianSaddle`).
* (9.3.100): equality holds only to first order in `U₂/γ²` (`BrownianSaddle`).
* (9.3.108): `V(x, T) = U(xT^{1/2})/T` (`BrownianSaddle`).
-/
import SHSLib.Gardiner.Escape.Laplace
import SHSLib.Gardiner.Escape.Kramers
import SHSLib.Gardiner.Escape.DoubleWell
import SHSLib.Gardiner.Escape.Splitting
import SHSLib.Gardiner.Escape.AsymWell
import SHSLib.Gardiner.Escape.FirstPassage
import SHSLib.Gardiner.Escape.Decay
import SHSLib.Gardiner.Escape.BirthDeath
import SHSLib.Gardiner.Escape.Populations
import SHSLib.Gardiner.Escape.ExitPoints
import SHSLib.Gardiner.Escape.BrownianSaddle
