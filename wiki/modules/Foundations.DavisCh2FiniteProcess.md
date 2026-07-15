# Module: SHSLib.Foundations.DavisCh2FiniteProcess

**File:** `SHSLib/Foundations/DavisCh2FiniteProcess.lean`
**Layer:** Foundations
**Status:** ✅ Complete

## What it proves

Connects the finite-state transition kernels of
[[Foundations.DavisCh2FiniteKernelSemigroup]] to conditional-expectation
formulations of the (strong) Markov property. The hypotheses state explicitly
the missing link between an abstract process `X` and the PDP kernel — the link
whose absence makes the corresponding general-state claims in the Chapter 2
skeleton unprovable. `sorry`-free, standard axioms.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `pdp_simple_markov_finite_of_kernel` | Markov property (conditional-expectation form) from the finite-state kernel |
| `pdp_strong_markov_finite_of_kernel` | Strong Markov property from the finite-state kernel |
| `pdpSemigroupKernelFinite_integral_add` | Time-additivity of the kernel integral along the process |

## Depends on

- [[Foundations.DavisCh2FiniteKernelSemigroup]], Mathlib

## Used by

- (Terminal foundations module)

## Open gaps / sorries

None. The general-state (non-finite) Markov/strong-Markov results remain `sorry`
in [[Foundations.DavisCh2]]; this module discharges the finite-state case under
an explicit process↔kernel hypothesis.

## Notes

Introduced by Aristotle `6cbbd3ec`. See `docs/analyses/davis_shs_bridge.md`.
