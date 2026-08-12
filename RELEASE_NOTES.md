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
