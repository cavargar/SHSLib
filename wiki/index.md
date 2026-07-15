# SHSLib Wiki — Index

Documentation for the public **SHSLib** distribution: the foundational theory of Stochastic Hybrid Systems (SHS) formalized in Lean 4 / Mathlib. This public repository contains the core framework only; worked examples and applications live in a separate research library.

**Status key:** ✅ Complete (0 sorries) · ⚠️ Has sorries

## Core

| Module | Status | Summary |
|--------|--------|---------|
| [Core.Basic](modules/Core.Basic.md) | ✅ | SHS definition, state space, hybrid transitions, sample-path assumptions |
| [Core.Generator](modules/Core.Generator.md) | ✅ | Extended generator `L`, moment evolution, Fokker–Planck equation |
| [Core.GeneratorDefs](modules/Core.GeneratorDefs.md) | ✅ | Shared `TestFunction` / `extendedGenerator` defs (breaks import cycle) |
| [Core.DavisBridge](modules/Core.DavisBridge.md) | ✅ | SHS ↦ Davis PDP; PDP generator = extended generator |
| [Core.DavisConstruction](modules/Core.DavisConstruction.md) | ✅ | Concrete time-augmented Davis PDP of an SHS |
| [Core.DavisMartingale](modules/Core.DavisMartingale.md) | ✅ | Compensated-generator martingale; Hespanha Theorem 2 |

## Foundations

| Module | Status | Summary |
|--------|--------|---------|
| [Foundations.DavisCh1](modules/Foundations.DavisCh1.md) | ⚠️ 3 sorries | Davis Ch. 1 — analysis, measure theory, martingales, Dynkin |
| [Foundations.DavisCh2](modules/Foundations.DavisCh2.md) | ⚠️ 9 sorries | Davis Ch. 2 — PDMP theory, ODE flows, Grönwall, inverse-transform sampling |
| [Foundations.DavisCh2FiniteKernel](modules/Foundations.DavisCh2FiniteKernel.md) | ✅ | Finite-state Markov kernel from `pdpSemigroup`; α-excessive resolvent |
| [Foundations.DavisCh2FiniteKernelSemigroup](modules/Foundations.DavisCh2FiniteKernelSemigroup.md) | ✅ | Finite-state kernel semigroup laws (identity + time-addition) |
| [Foundations.DavisCh2FiniteProcess](modules/Foundations.DavisCh2FiniteProcess.md) | ✅ | Finite-state (strong) Markov property from the kernel |

## References

- M. H. A. Davis, *Markov Models and Optimization*, Chapman & Hall, 1993.
- J. P. Hespanha, "A model for stochastic hybrid systems with application to communication networks," *Nonlinear Analysis*, 2005.

Proofs in this library were developed with [Aristotle](https://aristotle.harmonic.fun) (Harmonic).
