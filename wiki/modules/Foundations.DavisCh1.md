# Module: SHSLib.Foundations.DavisCh1

**File:** `SHSLib/Foundations/DavisCh1.lean`
**Layer:** Foundations
**Status:** ⚠️ Has sorries

## What it proves

Formalizes prerequisite results from Davis's *Markov Models and Optimization* (Chapter 1 and supporting material): topology and analysis foundations, measure-theoretic probability (Doob–Dynkin, convergence theorems, Fatou's lemma, change of variables), martingale theory (sub/supermartingale convergence, optional sampling, UI closure), Markov process foundations (transition functions, semigroups, generators), and the Dynkin formula/martingale. These provide the theoretical backbone for the PDP and SHS generator theories.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `C0T_banach` | C([0,T], ℝ) is a Banach space |
| `C0T_separable` | C([0,T], ℝ) is separable |
| `absContOn_ae_differentiable` | Absolutely continuous functions are a.e. differentiable |
| `ftc_abs_continuous` | Fundamental theorem of calculus for abs. continuous functions |
| `doob_dynkin_factorization` | Doob–Dynkin factorization lemma |
| `monotone_convergence` | Monotone convergence theorem |
| `dominated_convergence` | Dominated convergence theorem |
| `fatou_lemma` | Fatou's lemma |
| `submartingale_convergence` | Submartingale convergence theorem |
| `supermartingale_nonneg_convergence` | Nonneg. supermartingale convergence with Doob decomposition |
| `ui_martingale_closed` | Uniformly integrable martingale closure |
| `optional_sampling_supermartingale` | Optional sampling for supermartingales |
| `optional_sampling_ui_martingale` | Optional sampling for UI martingales |
| `semigroup_property` | Markov semigroup satisfies Chapman–Kolmogorov |
| `dynkin_formula` | Dynkin's formula: `E[f(Xₜ)] - f(x) = E[∫₀ᵗ Af(Xₛ) ds]` |
| `dynkin_martingale` | `f(Xₜ) - ∫₀ᵗ Af(Xₛ) ds` is a martingale |

## Depends on

- Mathlib

## Used by

- [[Core.Generator]], [[Foundations.DavisCh2]]

## Recently closed (Aristotle)

- `strong_law_of_large_numbers` (12.7) — via `ProbabilityTheory.strong_law_ae`.
- `submartingale_convergence` (13.5) — via `Submartingale.ae_tendsto_limitProcess` / `memLp_limitProcess`, with a uniform L¹ bound derived from the positive-part bound.
- `ui_martingale_closed` (13.6(2)) — via `Martingale.ae_eq_condExp_limitProcess`.
- `submartingale_modification` (13.4) — trivial in discrete time (the process itself).
- `C0T_separable` (11.4) — separability of `C(Icc 0 T, ℝ)` transported along `ContinuousMap.equivBoundedOfCompact`.
- `locally_lipschitz_ae_differentiable` (11.8) — Rademacher via `LipschitzOnWith.ae_differentiableWithinAt_of_mem_of_real` over a compact exhaustion of ℝ.
- `absCont_ae_differentiable` (11.6(1), corrected) — Lebesgue's monotone differentiation theorem (`Monotone.ae_differentiableAt`).
- `optional_sampling_supermartingale` (13.7) — optional-sampling inequality `E[X_T | F_S] ≤ X_S` for bounded stopping times, proved from a telescoping-by-increments decomposition over `ℱ k`-measurable cells (`optionalStopping_cell_nonpos`) plus a trim-measure reduction to `F_S`-sets. Supporting helpers added and proved: `integrable_stoppedValue_nat`, `stronglyMeasurable_stoppedValue_nat`, `optionalStopping_integral_mono`, `optionalStopping_cell_nonpos`, `optionalStopping_setIntegral_le`.
- `optional_sampling_ui_martingale` (13.9) — optional sampling `X_S = E[X_T | F_S]` for uniformly integrable martingales at (possibly unbounded) stopping times `S ≤ T`, via Lévy upward convergence (`tendsto_ae_condExp`) of the truncations `τ ∧ n` plus the tower property. Supporting helper `stoppingTime_iSup_min_measurableSpace` (the stopping-time σ-algebra is the supremum of those of its bounded truncations) added and proved.
- `SHS.transition_probability_rate` (in `Core/Basic.lean`) — the survivor function `F = exp(-∫ λ)` satisfies `0 < F ≤ 1`.
- `supermartingale_nonneg_convergence` (13.6(1)) — a non-negative supermartingale converges a.s. to an integrable limit `X_inf` with `E[X_inf | ℱ n] ≤ X n`. Proved via three new reusable helpers: `supermartingale_nonneg_ae_tendsto` (convergence + integrability, through the submartingale `-X`), `supermartingale_setIntegral_limit_le` (the closure inequality at the level of set integrals over `ℱ n`-sets, using Fatou together with `Supermartingale.setIntegral_le`), and `condExp_le_of_forall_setIntegral_le` (a trim-measure reduction: `μ[f | ℱ n] ≤ g` from domination of set integrals over `ℱ n`-sets). This closure route uses ordinary Fatou rather than conditional Fatou.
- `dynkin_formula` (14.12) — proved in a *faithful reformulated* form. A direct proof from the pointwise generator limit alone needs semigroup time-continuity (dominated-convergence exchange), not available in Mathlib. The proved version takes Davis's two genuine sub-results as explicit hypotheses — the semigroup time-derivative identity `hsemi_deriv` (14.10(2), `(d/ds)Pₛf = Pₛ(Âf)`, the real analytic content) and integrability `hint` of `s ↦ Pₛ(Âf)(x)` on `[0,t]`, each strictly weaker than the conclusion — and derives the integral form via the FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`), with the new helper `semigroupOp_zero` (`P₀f = f`). Standard axioms only.

## Corrected statements (were false as originally formalized)

- `absContOn_ae_differentiable` (11.6(1)): the original hypothesis `LocallyIntegrable f` is far too weak (a continuous nowhere-differentiable function is a counterexample). Original preserved (commented); corrected form `absCont_ae_differentiable` uses `Monotone f`.

## Open gaps / sorries

- 3 `by sorry` remain (down from 4; `dynkin_formula` is now proved — see "Recently closed"). The remaining gaps are: a.e. differentiability of a locally-integrable function (`absContOn_ae_differentiable`-style statement, line ~134) and the two `dynkin_martingale` supporting results on adaptedness/integrability of the discrete generator sum `∑ₖ Af(Xₖ)` (lines ~1174, ~1396). `supermartingale_nonneg_convergence` (13.6(1)) and the optional-sampling theorems `optional_sampling_supermartingale` (13.7) / `optional_sampling_ui_martingale` (13.9) are all fully proved (see "Recently closed").

## Notes

This module serves as a "prerequisite ledger" — it states classical results that downstream modules depend on, even when full Lean proofs are not yet available. Many of these results exist in some form in Mathlib but with different formulations. The `IsMarkovProcess'` and `IsStrongMarkovProcess'` definitions provide the Markov process interface used by the PDP theory in `DavisCh2`.
