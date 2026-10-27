# SHSLib v2.3.0 — stochastic differential equations and their Fokker–Planck equation

The public library grows from **367 to 393 modules** and remains **entirely free of
`sorry`**: every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`, and there are no `axiom` declarations. This release is additive —
nothing previously public was removed or changed, and there are no new dependencies.

## Added (26 modules)

- **Stochastic differential equations, Gardiner §4.3.1–4.3.2 and §10.1 (`Gardiner.Ito.StochDE`,
  14 modules).** Under the Lipschitz and growth conditions (4.3.10)–(4.3.11), the Itô SDE
  (4.3.4) has a continuous adapted solution on every horizon `[t₀, T]`, unique up to
  indistinguishability (`existsUnique_sdeSol`, Picard iteration), with the moment bound
  `E sup|x|² ≤ C(1 + E|x₀|²)` and mean-square continuous dependence on the initial value. Doob's
  L² maximal inequality in discrete and continuous time and for the Itô integral. The
  Euler–Maruyama scheme converges with **strong order ½** (10.1.26) and an explicit constant
  (`euler_strong_order_half`), so Gardiner's Cauchy–Euler construction converges to the solution.
  Geometric Brownian motion and the Ornstein–Uhlenbeck process are the unique solutions of their
  SDEs; `dx = −sin x dt + σ dW` is a nonlinear instance.
- **Generator, Dynkin's formula, martingale problem and Fokker–Planck equation, Gardiner §4.3.4
  (`Gardiner.Ito.Generator`, 10 modules).** The generator `a f′ + ½ b² f″`; Dynkin's formula and
  the martingale problem for Itô diffusions and SDE solutions; the weak Fokker–Planck equation
  (4.3.18)–(4.3.19) for the law of the solution, and the strong form (4.3.20) under explicit
  regularity hypotheses on the density, fully discharged for the heat kernel. The Ornstein–Uhlenbeck
  Gaussian and stationary densities solve the Fokker–Planck equation; Dynkin's formula and the weak
  equation for OU, geometric Brownian motion and the `sin` SDE; the Markov property for the Wiener
  process and geometric Brownian motion.
- **Bridges (`Gardiner.Ito.SDEBridge`, `FPK.ItoDiffusion`).** The SDE results instantiated with the
  standard Wiener process; the Euler–Maruyama step is the one-step map of the numerics layer
  (`Gardiner.SDE.eulerStep`) driven by Brownian grid increments; the Fokker–Planck right-hand side
  equals Gardiner's `fpRHS` (3.5.6) in dimension one; a one-dimensional diffusion as jump-free
  `GSHS.FPKData` satisfying Bect's generalized Dynkin formula (13), with the Wiener process
  (weak heat equation) as instance.

# SHSLib v2.2.0 — Gardiner's approximation methods, SDE numerics and the Itô calculus

The public library grows from **271 to 367 modules** and remains **entirely free of
`sorry`**: every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`, and there are no `axiom` declarations. This release is additive —
nothing previously public was removed or changed.

**New dependency.** The Itô layer uses
[brownian-motion](https://github.com/RemyDegenne/brownian-motion) (Apache-2.0),
pinned at commit `4fa8fc01` (same Lean `v4.28.0` and Mathlib as SHSLib). Only its
sorry-free module `BrownianMotion.Gaussian.BrownianMotion` is imported.

## Added (all under `SHSLib/Gardiner/`, 96 modules)

- **Approximation methods, Ch. 6–7 (`Approx`, 15 modules).** The small-noise expansion as a
  power-series hierarchy; the Kramers–Moyal expansion with its truncation error; van Kampen's
  system-size expansion and the linear noise approximation, with explicit `O(Ω^{-1/2})` bounds
  between the fluctuation generator and the LNA generator (one- and multi-dimensional); exact
  linear-noise results for affine propensities; the chemical Fokker–Planck equation and the
  Lyapunov equation for the stationary covariance.
- **Adiabatic elimination, §6.4–6.6 (`Adiabatic`, 12 modules).** Kramers → Smoluchowski with
  `O(γ⁻³)` generator bounds, the white-noise limit of coloured noise, chemical intermediates,
  projector/Laplace-transform elimination with explicit bounds, Haken's model.
- **Escape problems, §5.2.7–5.2.8, §7.4, Ch. 9 (`Escape`, 12 modules).** Exact mean
  first-passage times, exit and splitting probabilities via backward equations; a quantitative
  Laplace method; the Kramers/Arrhenius escape rate as a genuine limit,
  `|T/T_K − 1| ≤ C√D`, with a quartic double-well instance.
- **SDE expansions and numerics, §6.2 and Ch. 10 (`SDE`, 13 modules).** The pathwise
  small-noise expansion for additive noise with explicit remainder; pathwise Euler convergence;
  Euler, Milstein and semi-implicit schemes driven by Gaussian increments with exact moments and
  `O(τ)` weak error on the Ornstein–Uhlenbeck and linear multiplicative-noise SDEs; stability
  regions, mean-square stability and consistency; the vector formulae of §10.5.
- **The Itô calculus, Ch. 4 (`Ito`, 44 modules).** `IsWiener`, a standard Wiener process on real
  time with its natural filtration and martingale property, realised by `stdWiener` from the
  brownian-motion dependency; independent Gaussian increments, quadratic variation and the Itô sum
  (4.2.14)–(4.2.20) in mean square; Brownian scaling (6.2.40); the Itô integral of simple
  integrands with the isometry (4.2.42) and martingale property; the Wiener integral of
  deterministic functions; the law of the linearised process (6.2.14); the joint law of the
  multiple integrals of (10.1.10)–(10.1.12); the Ornstein–Uhlenbeck process (4.4.22)–(4.4.31).
  `Ito.Calculus` adds the general L² Itô integral for nonanticipating integrands (density of
  simple integrands, isometry, martingale property, Riemann-sum limits), (4.2.37), Itô's formula
  (4.3.14) along Itô processes, geometric Brownian motion (4.4.3)–(4.4.13), and the GBM/OU moment
  equations derived from Itô's formula. `Ito.CalculusBridge` connects the two, so every result
  applies to `stdWiener`.

Every layer carries a Gardiner-equation ↔ Lean correspondence table in its index module and
records the printed equations it found to be in error, with corrected statements.

# SHSLib v2.1.0 — Bect's FPK equation, Bujorianu GSHS, Gardiner and Ullah

The public library grows from **194 to 271 modules** and remains **entirely free of
`sorry`**: every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`, and there are no `axiom` declarations.

**The scope of the public distribution has widened.** Previously it carried the
`Core/` and `Foundations/` layers only. It now covers the general
stochastic-modeling theory of the research library: `Core/`, `Foundations/`,
`FPK/`, `Gardiner/`, `Ullah/` and `Bujorianu2006/`. Domain-specific models
(`Examples/`, `Applications/`), the moment-analysis framework and the tactic
front-end remain in the research repository. This release is additive — nothing
previously public was removed or changed.

## Added

- **Bect (2010), the unifying FPK equation (36 modules, `SHSLib/FPK/`).** The
  generalized Fokker–Planck–Kolmogorov equation for general stochastic hybrid
  systems, formulated as a measure-valued weak equation
  `d/dt ⟨μ_t, φ⟩ = ⟨μ_t, Lφ⟩` (Definition 7) that covers diffusions, Markov
  chains, spontaneous jumps and forced boundary jumps in one statement. Includes
  the hybrid state space, the pathwise Itô formula (3), the differential
  generator (4)/(16), the Lévy system (6)/(7) and mean jump intensity (8), the
  generalized Dynkin formula (12)/(13), adjoint uniqueness (15), the probability
  current (§4.2, App. C), boundary conditions (19), Assumption 14 as an equality
  of measures (24), the divergence theorem (App. A), total-variation bounds
  (39)/(41), Eqs. (42)–(47) and Theorem 13. Example 18 bridges to the existing
  Hespanha core, recovering Hespanha's FPK equation (33).

  Worked solutions rather than statements alone: the symmetric two-state chain
  (Example 16) is solved through to the master equation, and the sawtooth process
  of §3.2 with uniform initial law is shown to satisfy Definition 7 with the
  transport term exactly cancelling the forced-jump term. Two modules exist to
  certify non-vacuity — `AppendixC1BoxExample` discharges every hypothesis of
  Eq. (46) on a concrete model, and `SawtoothSolution` tests against `sin` to
  witness that the two cancelling terms are individually nonzero.

- **Bujorianu & Lygeros (2006), general stochastic hybrid systems (8 modules,
  `SHSLib/Bujorianu2006/`).** The hybrid state space with its closure and
  boundary; Markov strings — jump times, translation operators, càdlàg paths and
  the Markov property; additive and multiplicative functionals with terminal
  times; jump counting measures; the semigroup, resolvent and `p`-excessive
  functions; the strong generator with uniqueness and Dynkin's formula; and the
  extended generator. Self-contained: it imports nothing else from SHSLib.

- **Gardiner, *Handbook of Stochastic Methods* §3.4–3.6 (8 modules,
  `SHSLib/Gardiner/`).** The textbook derivation of the differential
  Chapman–Kolmogorov equation: conditions (i)–(iii), the uniform Taylor estimate
  (3.4.11), the weak form (3.4.16), integration by parts (3.4.19) and the strong
  form (3.4.22); vanishing of all third and higher conditional moments; the
  Master (3.5.2), Fokker–Planck (3.5.6) and Liouville (3.5.13) special cases with
  the Gaussian solution (3.5.9); and the backward equation (§3.6).

- **Ullah & Wolkenhauer, *Stochastic Approaches for Systems Biology* §8.2
  (5 modules, `SHSLib/Ullah/`).** The same dCKE (8.13) reached by a different
  route — near/far region splitting, with no integration by parts.
  `Ullah.condDrift_iff_mom` and `Ullah.condDiffusion_iff_mom` identify that text's
  conditions (8.8)/(8.9) with Gardiner's, so the two derivations are formally
  connected rather than merely parallel.

- **Flow existence and regularity (13 modules, `SHSLib/Core/`).**
  `SHS.HasGlobalFlow` was previously an assumption; it is now discharged from
  checkable hypotheses on the drift — global existence and uniqueness under
  Lipschitz continuity and under local Lipschitz continuity plus linear growth
  (including time-varying coefficients), flow regularity, dependence on the
  initial state, growth envelopes and their sharpness, and closed-form flows for
  the simplest drifts. `FlowDynkin` upgrades the flow's integral form to the
  deterministic Dynkin identity. `DavisTransitionFree` and `DavisModeBlind`
  inhabit every hypothesis bundle of `SHS.theorem1_generator_formula`,
  establishing that the theorem is not vacuous — including for genuinely jumping
  systems.

- **Beta order statistics (6 modules, `SHSLib/Foundations/`).** Moments of the
  `(j+1)`-st order statistic of a Beta sample: reflected and direct fractional
  moments as Beta-function ratios, mean/second moment/variance, Chebyshev
  concentration, the integer-exponent product form bracketed by the parent
  quantile at two rank fractions, and variance bounds `Var ≤ k²/(4(n+2))` from a
  Lipschitz parent quantile — the first Lipschitz results in the Beta layer.

- **`Foundations.DavisCh2ProcessLinks`.** Process-level links for Davis Ch. 2:
  falsity certificates for the unlinked simple-Markov, strong-Markov and
  Borel-right-process forms, their faithful replacements, and a dyadic
  approximation chain carrying the strong Markov property from countable-range
  stopping times to right-continuous paths.

## Notes

- `SHS.levyTotalIntensity` (`FPK.HespanhaBridge`) is the Lévy-system intensity
  `λ = Σ_ℓ λ_ℓ` and is deliberately distinct from `SHS.totalIntensity`
  (`Core.DavisBridge`), the Davis-state total jump rate.

## Build

- Lean: `leanprover/lean4:v4.28.0`
- Mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

```bash
lake exe cache get   # fetch Mathlib cache
lake build
```

---

# SHSLib v2.0.0 — Sorry-free core, PDMP process extensions, special functions

The library is now **194 modules and entirely free of `sorry`**: every theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`.

**This release is breaking.** Six declarations were removed from
`Foundations.DavisCh2` — see *Removed* below.

## Added

- **Davis PDMP process extensions (75 modules).** Elapsed-occupation martingales
  with their minimal, path and current-state filtrations; observability and
  full-observability criteria; marked-jump processes (filtration, bounded
  intensity, step laws, generator martingale); two-channel characteristics and
  test functions; segment-level conditionals and hazard Riemann sums; and
  concrete age, age-counter, ramped, refractory and Poisson clock models.
- **Special functions (51 modules).** Stirling's formula with Binet's first,
  second and third integrals, Wallis, Gautschi, central-binomial and Catalan
  asymptotics; the Beta distribution, measure, quantile function and
  inverse-transform sampling; the digamma / trigamma / tetragamma / polygamma
  family with reflection formulae and sharp bounds; Clopper–Pearson exact
  binomial intervals with coverage and monotonicity; uniform order statistics.
- **`Core.GronwallGrowthBound`.** Grönwall's inequality in integral form with a
  *time-varying* nonnegative rate — Mathlib's `gronwallBound` covers only the
  constant case — together with the growth envelope, its restart property, and
  the resulting sample-path bounds: `SHS.lemma1_linear_growth_bound_varying_rate`
  for a flow segment and `SHS.hybrid_path_growth_bound` for an entire hybrid
  path across resets. Also `SHS.flow_eq_of_lipschitz`, forward uniqueness of the
  flow.
- **`Foundations.DavisCh2StrongMarkov`.** The strong Markov property without the
  countable-range restriction on the stopping time, by dyadic discretisation.

## Removed

`Foundations.DavisCh2` previously carried six results as `sorry`. They stated
what the source text asserts, but three of them are **false as literally
formalized** and the other three are not provable in the generality claimed.
Rather than leave them as open placeholders, they were retired:

| Removed | Replaced by |
|---------|-------------|
| `pdp_filtration_right_continuous` | `pdp_filtration_right_continuous_false` (counterexample) |
| `compensator_is_local_martingale` | `compensator_is_local_martingale_false` (counterexample) |
| `pdp_generator_boundary_condition_necessary` | `pdp_generator_boundary_condition_necessary_false` (counterexample), plus `pdp_generator_boundary_condition_of_semigroup_limits` |
| `pdp_simple_markov`, `pdp_strong_markov` | `pdp_strong_markov_of_countable_range`, `pdp_strong_markov_of_finite_range`, and `Foundations.DavisCh2StrongMarkov` for general stopping times |
| `pdp_is_borel_right_process` | `pdp_is_borel_right_process_of_localFlow` |

Every original statement is preserved verbatim in a comment block beside its
replacement. Nothing that was ever *proved* was removed.

## Fixed

- Hespanha's Eq. (35) is still certified false as literally stated
  (`lemma1_linear_growth_bound_false`), but the gap noted in v0.1.0 is now
  largely closed by `Core.GronwallGrowthBound`. The paper's *quotient* form,
  with its `c_f / γ_f(t₀)` term valid only when `γ_f` is bounded away from zero,
  remains unformalized.

## Build

- Lean: `leanprover/lean4:v4.28.0`
- Mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

```bash
lake exe cache get   # fetch Mathlib cache
lake build
```

---

# SHSLib v0.1.0 — Core SHS theory & Davis foundations

First public release of **SHSLib** — a Lean 4 / Mathlib formalization of
**Stochastic Hybrid Systems (SHS)**, following Hespanha (2005) and the
piecewise-deterministic Markov process (PDMP) theory of Davis (1993).

This is the curated **core** distribution: the foundational theory only. Worked
examples and applications live in a separate research library.

## Highlights

- **SHS extended generator** (Hespanha 2005, Eq. 9) — the operator `L` computing
  drift + jump contributions, with the moment-evolution / Fokker–Planck machinery.
- **Davis ↔ Hespanha bridge** — the headline contribution: a chain connecting
  Davis's abstract PDMP theory to the concrete SHS generator on the
  time-augmented state `(q, x, t)`. Its central result,
  `pdpGenerator_eq_extendedGenerator`, proves the Davis PDP generator **equals**
  the SHS extended generator, yielding Hespanha's Theorem 2
  (`E[ψ(Xₜ)] = ψ₀ + E[∫ Lψ ds]`) for the constructed process.
- **Davis PDMP foundations** — analysis / measure-theory / martingale
  prerequisites (Ch. 1) and the PDMP theory itself (Ch. 2): ODE flows, Grönwall
  uniqueness, the deterministic Dynkin formula, inverse-transform sampling, the
  PDP semigroup construction, and a finite-state renewal-kernel development.
- **Reset-compensator development** — a 55-module chain building the compensator
  of the reset (jump) part of a Davis PDMP from the ground up: jump-counter
  augmentation and observable stopping times, the conditional holding-time and
  channel laws, their lift to integral identities and Mathlib `condExp`,
  reset-occupation densities, and finite centered reset sums whose deterministic
  caps are removed by dominated convergence. Reaches event-localized centering
  of fixed-time increments; the continuous-time martingale statement is the next
  milestone.

## Modules

**Core**

| Module | Status | Summary |
|--------|--------|---------|
| `Core.Basic` | ✅ | SHS definition, state space, hybrid transitions, sample-path assumptions |
| `Core.Generator` | ✅ | Extended generator `L`, moment evolution, Fokker–Planck equation |
| `Core.GeneratorDefs` | ✅ | Shared `TestFunction` / `extendedGenerator` definitions |
| `Core.DavisBridge` | ✅ | SHS ↦ Davis PDP; PDP generator = extended generator |
| `Core.DavisConstruction` | ✅ | Concrete time-augmented Davis PDP of an SHS |
| `Core.DavisMartingale` | ✅ | Compensated-generator martingale; Hespanha Theorem 2 |
| `Core.Davis*` (55 modules) | ✅ | Reset compensator: conditional one-step laws, reset-occupation densities, occupation centering |

**Foundations**

| Module | Status | Summary |
|--------|--------|---------|
| `Foundations.DavisCh1` | ✅ | Analysis, measure theory, martingales, Dynkin |
| `Foundations.DavisCh2` | ⚠️ | PDMP theory, ODE flows, Grönwall, inverse-transform sampling |
| `Foundations.DavisCh2FiniteKernel` | ✅ | Finite-state Markov kernel from `pdpSemigroup`; α-excessive resolvent |
| `Foundations.DavisCh2FiniteKernelSemigroup` | ✅ | Finite-state kernel semigroup laws (identity + time-addition) |
| `Foundations.DavisCh2FiniteProcess` | ✅ | Finite-state (strong) Markov property from the kernel |

## Status & known limitations

- The **Core** layer (including the reset-compensator chain) and all **bridge** /
  **finite-state** modules are `sorry`-free and use only the standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`).
- `DavisCh2` retains 6 `sorry`s for the deepest measure-theoretic PDMP results —
  `pdp_filtration_right_continuous`, `pdp_simple_markov`, `pdp_strong_markov`,
  `compensator_is_local_martingale`,
  `pdp_generator_boundary_condition_necessary`, `pdp_is_borel_right_process` —
  which require the full probabilistic construction; these are stated faithfully
  and tracked in the docs. `DavisCh1` is `sorry`-free.
- One `DavisCh2` localizing hypothesis was previously stated as
  `Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop atTop`. On `ℝ≥0∞` that target is the
  pure filter at `⊤`, which no coerced `ℝ≥0` value attains, so the hypothesis was
  unsatisfiable and `pdp_generator_bounded_true_martingale` was vacuous. It now
  reads `nhds ⊤` and the theorem is genuinely proved; the impossibility is
  recorded as `no_nnreal_coe_tendsto_ennreal_atTop`.
- Hespanha's Lemma 1 (Eq. 35) is **certified false as literally stated**
  (`lemma1_linear_growth_bound_false`); the true (bounded-away-from-zero) form
  is not yet formalized — a modeling gap, not a `sorry`.

## Build

- Lean: `leanprover/lean4:v4.28.0`
- Mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

```bash
lake exe cache get   # fetch Mathlib cache
lake build
```

Proofs were developed with [Aristotle](https://aristotle.harmonic.fun) (Harmonic).
Licensed under **MIT**.
