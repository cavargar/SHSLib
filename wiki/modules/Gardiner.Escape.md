# Module: SHSLib.Gardiner.Escape

**File:** `SHSLib/Gardiner/Escape.lean` (index and correspondence table) + `SHSLib/Gardiner/Escape/*.lean` (11 modules)
**Layer:** Gardiner (textbook approximation methods)
**Status:** ✅ Complete (0 sorries, standard axioms only)
**Origin:** Aristotle project `ab39a0db`

## What it proves

This layer covers first-passage times, bistability and escape over a barrier, from Gardiner, *Handbook of Stochastic Methods*: §5.2.7–5.2.8, §7.4 and Chapter 9. All declarations are in the namespace `Gardiner.Escape`.

The base is exact. Mean first-passage times and exit probabilities of 1-D diffusions and birth–death processes are characterized as solutions of their backward equations, with uniqueness. On top of that, a quantitative Laplace method (`Laplace`) turns the text's small-D asymptotics into theorems with explicit relative errors of order `O(√D)`.

The headline result is the Kramers/Arrhenius formula (5.2.174) as a genuine limit: the exact barrier-crossing time `T` satisfies `|T/T_K − 1| ≤ C√D` for `0 < D ≤ 1`. The hypotheses are nondegenerate quadratic Taylor windows at the minimum and at the barrier top, separation, and integrability.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `mfpt_kramers`, `mfpt_kramers_tendsto` | Exact MFPT (5.2.165) over a barrier vs. `2π(k_ak_b)^{-1/2}e^{ΔU/D}`: relative error `≤ C√D`, ratio `→ 1` as `D → 0⁺` |
| `mfpt_kramers_half` | Same to the barrier top (9.1.9): half the Kramers time |
| `doubleWell_mfpt`, `doubleWell_mfpt_half` | Quartic double well `x⁴/4 − x²/2`: `T(−1 → ½) = √2π e^{1/(4D)}(1 + O(√D))` |
| `bwd_unique`, `mfptTwo_spec`, `mfptReflA_spec` | Backward-equation characterization of MFPTs with absorbing/reflecting ends (§5.2.7), with uniqueness |
| `normalization_asymp`, `barrier_integral_asymp` | (9.1.6) and (9.1.13) with relative error `O(√D)` |
| `population_ratio_asymp`, `relaxTime_asymp` | Well populations (9.2.23) and relaxation time (9.2.18)–(9.2.25), `O(√D)` |
| `splitting_far`, `splitting_near` | Splitting probabilities (9.1.16) (relative `O(√D)`) and (9.1.20)–(9.1.21) in the barrier layer (absolute `O(√D)`), with the corrected error function |
| `bdRate_log_ratio_close`, `km_exponent_lt_log`, `km_barrier_lt` | §7.4.2: for small jumps the birth–death and Fokker–Planck exponents agree to `4|δA/B|³` per step; for unit jumps the Kramers–Moyal barrier is strictly too low |
| `bdT_sharp_peak` | Sharp-peak evaluation (7.4.18), with relative error `δ` of the slowly varying factor |
| `lam_ratio_bound`, `ratio_comparison`, `brownian_doubleWell_tau1` | §9.3.4 comparisons: Kramers vs. Smoluchowski rates, the ratio inequality (9.3.100) with gap `≤ 3s²`, and the exact 1-D time vs. Kramers at `O(√T)` |
| `tau3_quadratic`, `separatrix_C0` | §9.3: exact results for the quadratic saddle; corrected separatrix condition |

The full equation ↔ declaration table, the guarantees table and the errata list are the docstring of `SHSLib/Gardiner/Escape.lean`.

## Depends on

- [[Gardiner.Adiabatic]] (Kramers/Smoluchowski operators, double-well potential), [[Gardiner.Approx]] (birth–death stationary distributions, small-noise stationary forms), [[Gardiner]], Mathlib

## Used by

- Nothing yet (leaf layer)

## Open gaps / sorries

None. Caveats:
- **§7.4.2 consequence is thin.** `km_mfpt_ratio_tendsto` only says `e^{VΦ}/e^{VΦ_KM} → ∞` when `Φ_KM < Φ`; it does not derive the birth–death MFPT asymptotics `T ~ e^{VΦ}`. The substantive content is the barrier inequality (`km_exponent_lt_log`, `km_barrier_lt`).
- **§9.3 is partly conditional.** The multivariable analysis follows the text's formal matched asymptotics. Kramers' ansatz, the sharp-peak evaluations, the Green identities and the derivative/time-integral swap are named hypotheses. Results are unconditional only in the exact quadratic-saddle cases.
- **One-dimensional Kramers only.** The `O(√D)` theorem is for 1-D Smoluchowski dynamics. The multidimensional Kramers rate (§9.3.3) is not proved as a limit.

## Notes

- **Errata.** About 20 discrepancies with the printed text are formalized in corrected form; where possible a separate theorem shows that the printed version fails. There are 9 such `*_printed_wrong` certificates, e.g. `moments_printed_wrong`, `absProb_printed_wrong`, `exit_C0_printed_wrong` and `tau3_printed_wrong`. Among the errata:
  - (5.2.152): a missing factor `n`;
  - (5.2.189)–(5.2.190): `1/ψ`, not `ψ`;
  - (7.4.13)–(7.4.18): the products, the absorption probability and the summation limits;
  - (9.1.19): the error-function normalization `√(2/π)∫e^{−t²/2}`;
  - several in §9.2–9.3: (9.2.14), (9.2.16), (9.2.33), (9.3.26), (9.3.40)–(9.3.43), (9.3.87), (9.3.97), (9.3.100).
- **Mathlib had no Laplace-method theorem**, so `Laplace` builds a quantitative one from scratch.
