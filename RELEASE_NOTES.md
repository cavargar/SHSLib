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
