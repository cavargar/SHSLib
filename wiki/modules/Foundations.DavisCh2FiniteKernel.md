# Module: SHSLib.Foundations.DavisCh2FiniteKernel

**File:** `SHSLib/Foundations/DavisCh2FiniteKernel.lean`
**Layer:** Foundations
**Status:** ✅ Complete

## What it proves

On a **finite** measurable state space, the values of the positive normalized
operator `pdpSemigroup` ([[Foundations.DavisCh2]]) on singleton indicators
determine a genuine Markov transition kernel. Establishes that kernel and the
α-excessiveness of the associated resolvent — the interface needed by the
§25/§27 renewal/resolvent development. `sorry`-free, standard axioms.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `pdpSemigroup_eq_sum_singletons` | On a finite space, `pdpSemigroup` is the sum of its singleton-indicator values |
| `pdpSemigroupKernelFinite_markov_and_integral` | The finite-state kernel is Markov and integrates correctly |
| `pdpResolvent_isAlphaExcessive_finite` | The α-resolvent of the finite-state semigroup is α-excessive |

## Key definitions

| Definition | Description |
|------------|-------------|
| `pdpSemigroupKernelFinite` | Finite-state transition kernel from `pdpSemigroup` |

## Depends on

- [[Foundations.DavisCh2]], Mathlib

## Used by

- [[Foundations.DavisCh2FiniteKernelSemigroup]]

## Open gaps / sorries

None.

## Notes

Finiteness is a deliberate simplifying hypothesis; the general-state version is
future work (`docs/analyses/davis_shs_bridge.md`). Introduced by Aristotle
`6cbbd3ec`.
