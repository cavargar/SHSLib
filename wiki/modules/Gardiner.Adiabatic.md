# Module: SHSLib.Gardiner.Adiabatic

**File:** `SHSLib/Gardiner/Adiabatic.lean` (index and correspondence table) + `SHSLib/Gardiner/Adiabatic/*.lean` (11 modules)
**Layer:** Gardiner (textbook approximation methods)
**Status:** ✅ Complete (0 sorries, standard axioms only)
**Origin:** Aristotle project `6e7392e4`

## What it proves

This layer covers adiabatic elimination of fast variables from Gardiner, *Handbook of Stochastic Methods*: the Kramers equation and its Smoluchowski limit (§6.4), white noise as a limit of non-white noise (§6.5), and adiabatic elimination in the general case (§6.6). All declarations are in the namespace `Gardiner.Adiabatic`.

The method has three parts:
- **Error terms on backward generators.** The forward γ⁻¹ expansions of the text become explicit *perturbed test functions* `φ_γ = f + γ⁻¹φ₁ + γ⁻²φ₂ + …`. Each comes with an exact identity `G_γ φ_γ = (reduced generator) f + remainder`, and the remainder is bounded.
- **Projection-operator algebra in the abstract.** The `P`, `L₁`, `L₂`, `L₃` and Laplace-transform algebra is proved for abstract operators (`ProjHyp`). The γ → ∞ limits get explicit constants under boundedness hypotheses.
- **Exact solutions for the linear/Gaussian cases.** Their distance to the reduced statistics is bounded uniformly in time.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `free_variance_rate`, `ouDriven_variance_rate` | Free Brownian motion and the OU-driven white-noise limit: `0 ≤ Var_Smol(t) − Var_Kramers(t) ≤ 2Dτ` for all `t ≥ 0` |
| `harmonic_mean_rate`, `harmonic_variance_rate` | Harmonic Brownian motion: the mean is within `4kτ|⟨x⟩(0)|` and the variance within `8kτ|Var(0) − D/k|` of the Smoluchowski (OU) values, for all `t ≥ 0` |
| `kramers_smoluchowski_bound`, `kramers_corrected_bound` | Kramers generator on a perturbed test function vs. the Smoluchowski operator: `O(γ⁻³)`; vs. the corrected operator (6.4.108): `≤ 9M(1+K)²(1+|u|)⁵γ⁻⁴`. No `γ⁻²` term, which is the statement `B = 0` of (6.4.104) |
| `kramers_doubleWell`, `kramers_doubleWell_corr` | Instance: `U = y⁴/4 − y²/2`, `f = sin`, with a nonzero correction term |
| `kramers_laplace_bound`, `commuting_laplace_bound`, `threeScale_laplace_bound` | Laplace-domain elimination (6.4.52), (6.5.28), (6.5.70) with explicit `O(γ⁻²)` / `O(γ⁻¹)` errors for bounded operators |
| `shortTime_bound` | Corrected short-time memory equation (6.4.80) up to `‖K‖Mγ⁻²` |
| `scaled_corr_delta`, `gaussian_corr_delta` | `γ²g(γ²t) → δ(t)` at rate `Lτ_c/γ²` on Lipschitz test functions (6.5.9) |
| `wn_generator_bound` | White-noise limit in generator form (6.5.53), `O(γ⁻¹)`; OU and telegraph-noise instances |
| `chem_mean_rate` | Short-lived chemical intermediate (§6.6.1): the mean is within explicit `O(γ⁻¹)` of the reduced equation, uniformly in `t` |
| `haken_slave`, `nl_generator_bound`, `nlc_generator` | Haken's model (6.6.64), the nonlinear case (6.6.86) and arbitrary coupling (6.6.122), as perturbed-test-function expansions with explicit remainders |

The full equation ↔ declaration table and the errata list are the docstring of `SHSLib/Gardiner/Adiabatic.lean`.

## Depends on

- [[Gardiner.Approx]] (conventions, OU generator), [[Gardiner]], Mathlib

## Used by

- [[Gardiner.Escape]] (Kramers/Smoluchowski operators, double-well potential)

## Open gaps / sorries

None. Caveats:
- **Generator-level, not laws.** As in [[Gardiner.Approx]], bounds for nonlinear potentials are on generators applied to perturbed test functions. A weak-error bound on distributions would need regularity of the backward Smoluchowski semigroup, which is not in SHSLib. The linear/Gaussian rates *are* statements about the actual moments.
- **The Laplace-domain bounds need bounded operators.** The concrete instances (telegraph noise, matrices) satisfy this. The Kramers `L₂ = ∂/∂y` does not; the text itself flags this in §6.4.5 c.
- **The nonlinear §6.6 results are exact expansions.** `haken_slave` and its kin bound the error by explicit remainder expressions. Those remainders are shown to be small only in the instances (`haken_noisy_instance`, `nl_haken_instance`, `nlc_ou_instance`).
- **Named hypotheses:**
  - the moment ODEs of the Kramers equation and the chemical SDE (`d/dt ∫ = ∫ ∂ₜ`);
  - the vanishing of the Laplace boundary term;
  - solutions of the fast process's Poisson equations;
  - swapping `K` with a time integral (`ShortTime`);
  - the Maxwellian moments in `kramers_initial_layer`.
- **Boundary layer.** (6.4.110)–(6.4.113) is formalized only to the text's level; the Milne-problem matching is not done.

## Notes

- **Errata.** 14 discrepancies with the printed text are formalized in corrected form, including:
  - (6.4.80): it lacks a `γ⁻¹`;
  - (6.4.85): the sign of the current;
  - the identity after (6.4.101): `1/√2`, not `√2`;
  - (6.5.49): `γ²t`, not `t/γ²`;
  - (6.6.15): coefficient `+½`;
  - (6.6.120)/(6.6.122): the printed sign gives a negative diffusion coefficient.
