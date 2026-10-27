# SHSLib Wiki — Index

Documentation for the public **SHSLib** distribution: the general theory of Stochastic Hybrid Systems (SHS) formalized in Lean 4 / Mathlib. This public repository contains the theory layers only — `Core/`, `Foundations/`, `FPK/`, `Gardiner/`, `Ullah/` and `Bujorianu2006/`; worked examples, agricultural applications and the tactic front-end live in a separate research library.

**Status key:** ✅ Complete (0 sorries) · ⚠️ Has sorries

As of 2026-08-12 the public library is **271 modules and entirely free of `sorry`**;
every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, and
there are no `axiom` declarations.

## Core

| Module | Status | Summary |
|--------|--------|---------|
| [Core.Basic](modules/Core.Basic.md) | ✅ | SHS definition, state space, hybrid transitions, sample-path assumptions |
| [Core.Generator](modules/Core.Generator.md) | ✅ | Extended generator `L`, moment evolution, Fokker–Planck equation |
| [Core.GeneratorDefs](modules/Core.GeneratorDefs.md) | ✅ | Shared `TestFunction` / `extendedGenerator` defs (breaks import cycle) |
| [Core.DavisBridge](modules/Core.DavisBridge.md) | ✅ | SHS ↦ Davis PDP; PDP generator = extended generator |
| [Core.DavisConstruction](modules/Core.DavisConstruction.md) | ✅ | Concrete time-augmented Davis PDP of an SHS |
| [Core.DavisMartingale](modules/Core.DavisMartingale.md) | ✅ | Compensated-generator martingale; Hespanha Theorem 2 |
| [Core.DavisResetCompensation](modules/Core.DavisResetCompensation.md) | ✅ | 55-module chain: reset compensator, conditional one-step laws, occupation centering |
| [Core.DavisProcessExtensions](modules/Core.DavisProcessExtensions.md) | ✅ | 75-module group: elapsed-occupation martingales and filtrations, marked-jump processes, two-channel and clock models |
| [Core.GronwallGrowthBound](modules/Core.GronwallGrowthBound.md) | ✅ | Grönwall with a time-varying rate; Hespanha Lemma 1 / Eq. (35) for flow segments and whole hybrid paths |
| [Core.FlowExistence](modules/Core.FlowExistence.md) | ✅ | 13-module group: global existence and uniqueness of the flow (Lipschitz, and locally Lipschitz + linear growth), flow regularity, growth envelopes and their sharpness, the deterministic Dynkin identity, and Theorem 1 for transition-free and mode-blind systems |

## Foundations

| Module | Status | Summary |
|--------|--------|---------|
| [Foundations.DavisCh1](modules/Foundations.DavisCh1.md) | ✅ | Davis Ch. 1 — analysis, measure theory, martingales, Dynkin |
| [Foundations.DavisCh2](modules/Foundations.DavisCh2.md) | ✅ | Davis Ch. 2 — PDMP theory, ODE flows, Grönwall, inverse-transform sampling. Six statements that were false or unprovable as written are now certified false / replaced by proved corrected forms |
| [Foundations.DavisCh2StrongMarkov](modules/Foundations.DavisCh2StrongMarkov.md) | ✅ | Strong Markov property with the countable-range restriction on τ removed |
| [Foundations.SpecialFunctions](modules/Foundations.SpecialFunctions.md) | ✅ | 51-module layer: Stirling/Binet, Beta, di/tri/tetra/polygamma, Clopper–Pearson, uniform order statistics |
| [Foundations.DavisCh2FiniteKernel](modules/Foundations.DavisCh2FiniteKernel.md) | ✅ | Finite-state Markov kernel from `pdpSemigroup`; α-excessive resolvent |
| [Foundations.DavisCh2FiniteKernelSemigroup](modules/Foundations.DavisCh2FiniteKernelSemigroup.md) | ✅ | Finite-state kernel semigroup laws (identity + time-addition) |
| [Foundations.DavisCh2FiniteProcess](modules/Foundations.DavisCh2FiniteProcess.md) | ✅ | Finite-state (strong) Markov property from the kernel |
| [Foundations.DavisCh2ProcessLinks](modules/Foundations.DavisCh2ProcessLinks.md) | ✅ | Process-level links for Davis Ch. 2: simple/strong Markov under countable-range and right-continuous hypotheses, dyadic approximation, stopped compensators |
| [Foundations.BetaOrderStatistics](modules/Foundations.BetaOrderStatistics.md) | ✅ | 6-module group: moments of order statistics of a Beta sample — fractional and integer moments, Chebyshev concentration, variance bounds from a Lipschitz parent quantile |

## FPK — Bect (2010)

| Module | Status | Summary |
|--------|--------|---------|
| [FPK](modules/FPK.md) | ✅ | 37-module group (v2.3.0 adds one-dimensional Itô diffusions as jump-free FPK data): the generalized Fokker–Planck–Kolmogorov equation for general stochastic hybrid systems. Hybrid state space, Lévy systems, the generalized Dynkin formula (12)/(13), Definition 7 and adjoint uniqueness, probability current, boundary conditions, densities, total-variation bounds, Theorem 13, and worked solutions for the two-state chain (Example 16) and the sawtooth process |

## Gardiner — *Handbook of Stochastic Methods*

| Module | Status | Summary |
|--------|--------|---------|
| [Gardiner](modules/Gardiner.md) | ✅ | 130-module group. Ch. 3: derivation of the dCKE (3.4.16) in weak form and (3.4.22) in strong form, vanishing higher conditional moments, the Master / Fokker–Planck / Liouville special cases, and the backward dCKE. v2.2.0: approximation methods (Ch. 6–7), adiabatic elimination, escape problems, SDE numerics (Ch. 10) and the Itô calculus (Ch. 4) |
| [Gardiner.Approx](modules/Gardiner.Approx.md) | ✅ | Ch. 6–7: small-noise expansion, Kramers–Moyal, system-size expansion and linear noise approximation with explicit `O(Ω^{-1/2})` generator bounds, chemical Fokker–Planck equation, Lyapunov covariance |
| [Gardiner.Adiabatic](modules/Gardiner.Adiabatic.md) | ✅ | §6.4–6.6: adiabatic elimination — Kramers → Smoluchowski, white-noise limit, chemical intermediates, Haken's model — with explicit error bounds |
| [Gardiner.Escape](modules/Gardiner.Escape.md) | ✅ | §5.2.7–5.2.8, §7.4, Ch. 9: first-passage times, splitting probabilities, Kramers escape rate as a limit `|T/T_K − 1| ≤ C√D` |
| [Gardiner.SDE](modules/Gardiner.SDE.md) | ✅ | §6.2, Ch. 10: pathwise small-noise expansion and Euler convergence for additive noise, numerical schemes with `O(τ)` weak error, stability, consistency |
| [Gardiner.Ito](modules/Gardiner.Ito.md) | ✅ | Ch. 4: Wiener process (`IsWiener`, `stdWiener`), quadratic variation, simple / Wiener / L² Itô integrals, Itô's formula (4.3.14), OU and geometric Brownian motion; Lipschitz SDEs (existence, uniqueness, moment bounds) and Euler–Maruyama strong order ½; generator, Dynkin's formula, martingale problem and Fokker–Planck equation (4.3.18)–(4.3.20) |

## Ullah — dCKE via region splitting

| Module | Status | Summary |
|--------|--------|---------|
| [Ullah](modules/Ullah.md) | ✅ | 5-module group: the same dCKE (8.13) derived from the density by near/far region splitting, without integration by parts |

## Bujorianu2006 — general stochastic hybrid systems

| Module | Status | Summary |
|--------|--------|---------|
| [Bujorianu2006](modules/Bujorianu2006.md) | ✅ | 8-module group: hybrid state space, Markov strings with jump times and translations, jump counting measures, semigroup/resolvent and $p$-excessive functions, additive and multiplicative functionals with terminal times, the strong generator and Dynkin's formula, and the extended generator |

## References

- M. H. A. Davis, *Markov Models and Optimization*, Chapman & Hall, 1993.
- J. P. Hespanha, "A model for stochastic hybrid systems with application to communication networks," *Nonlinear Analysis*, 2005.
- J. Bect, "A unifying formulation of the Fokker–Planck–Kolmogorov equation for general stochastic hybrid systems," *Nonlinear Analysis: Hybrid Systems* 4 (2010) 357–370.
- C. W. Gardiner, *Handbook of Stochastic Methods for Physics, Chemistry and the Natural Sciences*, Springer.
- M. Ullah and O. Wolkenhauer, *Stochastic Approaches for Systems Biology*, Springer, 2011.
- M. L. Bujorianu and J. Lygeros, "Toward a general theory of stochastic hybrid systems," in *Stochastic Hybrid Systems*, LNCIS 337, Springer, 2006.

Proofs in this library were developed with [Aristotle](https://aristotle.harmonic.fun) (Harmonic).
