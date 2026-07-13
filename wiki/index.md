# SHSLib Wiki — Index

Documentation for the public **SHSLib** distribution: the foundational theory of Stochastic Hybrid Systems (SHS) formalized in Lean 4 / Mathlib. This public repository contains the core framework only; worked examples and applications live in a separate research library.

**Status key:** ✅ Complete (0 sorries) · ⚠️ Has sorries

## Core

| Module | Status | Summary |
|--------|--------|---------|
| [Core.Basic](modules/Core.Basic.md) | ✅ | SHS definition, state space, hybrid transitions, sample-path assumptions |
| [Core.Generator](modules/Core.Generator.md) | ✅ | Extended generator `L`, moment evolution, Fokker–Planck equation |

## Foundations

| Module | Status | Summary |
|--------|--------|---------|
| [Foundations.DavisCh1](modules/Foundations.DavisCh1.md) | ⚠️ 3 sorries | Davis Ch. 1 — analysis, measure theory, martingales, Dynkin |
| [Foundations.DavisCh2](modules/Foundations.DavisCh2.md) | ⚠️ 9 sorries | Davis Ch. 2 — PDMP theory, ODE flows, Grönwall, inverse-transform sampling |

## References

- M. H. A. Davis, *Markov Models and Optimization*, Chapman & Hall, 1993.
- J. P. Hespanha, "A model for stochastic hybrid systems with application to communication networks," *Nonlinear Analysis*, 2005.

Proofs in this library were developed with [Aristotle](https://aristotle.harmonic.fun) (Harmonic).
