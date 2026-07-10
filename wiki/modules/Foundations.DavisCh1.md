# Module: SHSLib.Foundations.DavisCh1

**File:** `SHSLib/Foundations/DavisCh1.lean`
**Layer:** Foundations
**Status:** ⚠️ 1 sorry

## What it proves

Formalizes prerequisite results from Davis's *Markov Models and Optimization* (Chapter 1 and supporting material): topology and analysis foundations, measure-theoretic probability (Doob–Dynkin, convergence theorems, Fatou's lemma, change of variables), martingale theory (sub/supermartingale convergence, optional sampling, UI closure), Markov process foundations (transition functions, semigroups, generators), and the Dynkin formula/martingale. These provide the theoretical backbone for the PDP and SHS generator theories.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `C0T_banach` | C([0,T], ℝ) is a Banach space |
| `C0T_separable` | C([0,T], ℝ) is separable |
| `absContOn_ae_differentiable` | Absolutely continuous / monotone functions are a.e. differentiable |
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
| `dynkin_formula` | Dynkin's formula: `E[f(Xₜ)] − f(x) = E[∫₀ᵗ Af(Xₛ) ds]` |
| `dynkin_martingale` | `f(Xₜ) − ∫₀ᵗ Af(Xₛ) ds` is a martingale |

## Depends on

- Mathlib

## Used by

- [Core.Generator](Core.Generator.md), [Foundations.DavisCh2](Foundations.DavisCh2.md)

## Selected results proved

- `strong_law_of_large_numbers` (12.7) — via `ProbabilityTheory.strong_law_ae`.
- `submartingale_convergence` (13.5) — via `Submartingale.ae_tendsto_limitProcess` with a uniform L¹ bound from the positive-part bound.
- `ui_martingale_closed` (13.6(2)) — via `Martingale.ae_eq_condExp_limitProcess`.
- `C0T_separable` (11.4) — separability of `C(Icc 0 T, ℝ)` transported along `ContinuousMap.equivBoundedOfCompact`.
- `locally_lipschitz_ae_differentiable` (11.8) — Rademacher via `LipschitzOnWith.ae_differentiableWithinAt_of_mem_of_real` over a compact exhaustion of ℝ.
- `absCont_ae_differentiable` (11.6(1), corrected) — Lebesgue's monotone differentiation theorem (`Monotone.ae_differentiableAt`).
- `supermartingale_nonneg_convergence` (13.6(1)) — a non-negative supermartingale converges a.s. to an integrable limit; the closure inequality obtained via ordinary Fatou plus a trim-measure reduction (`condExp_le_of_forall_setIntegral_le`), sidestepping the missing conditional Fatou.
- `optional_sampling_supermartingale` (13.7) — `E[X_T | F_S] ≤ X_S` for bounded stopping times, via a telescoping-by-increments decomposition over `ℱ k`-measurable cells.
- `optional_sampling_ui_martingale` (13.9) — `X_S = E[X_T | F_S]` for UI martingales at (possibly unbounded) stopping times, via Lévy upward convergence plus the tower property.

## Corrected statement (was false as originally formalized)

- `absContOn_ae_differentiable` (11.6(1)): the original hypothesis `LocallyIntegrable f` is far too weak (a continuous nowhere-differentiable function is a counterexample). The original is preserved (commented); the corrected form `absCont_ae_differentiable` uses `Monotone f`.

## Open gaps / sorries

- `dynkin_formula` (14.12) — the one remaining sorry. Needs semigroup time-continuity (exchange of the generator limit with the semigroup integral, and a suitable FTC on `[0,t]`) that is not currently available in Mathlib.

## Notes

This module serves as a "prerequisite ledger" — it states classical results that downstream modules depend on. Many exist in some form in Mathlib but under different formulations. The `IsMarkovProcess'` and `IsStrongMarkovProcess'` definitions provide the Markov process interface used by the PDP theory in [Foundations.DavisCh2](Foundations.DavisCh2.md).
