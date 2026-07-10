# Module: SHSLib.Foundations.DavisCh2

**File:** `SHSLib/Foundations/DavisCh2.lean`
**Layer:** Foundations
**Status:** ⚠️ 13 sorries

## What it proves

Formalizes Davis's Piecewise-Deterministic Markov Process (PDMP/PDP) theory from Chapters 2 and 24–25 of *Markov Models and Optimization*. Covers: exponential memorylessness, survivor/hazard functions, Poisson process properties, renewal equations, ODE theory (global existence, flow bijectivity, group property, chain rule), the deterministic Dynkin formula, linear ODE solutions (variation of constants), Grönwall uniqueness, inverse-transform sampling, and the PDP structure with its Markov/strong-Markov properties, compensator martingale, extended generator characterization, and boundary conditions.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `exponential_memoryless` | Memoryless property of the exponential distribution |
| `survivor_from_hazard` | Survivor function from cumulative hazard |
| `poisson_markov_property` | Poisson process Markov/Chapman–Kolmogorov property |
| `renewal_equation` | Renewal integral equation |
| `ode_global_existence` | Global existence of the flow of a globally Lipschitz field |
| `flow_group_property` | `φ(t+s, x) = φ(t, φ(s, x))` |
| `flow_chain_rule` | Chain rule along the deterministic flow |
| `deterministic_dynkin` | Dynkin formula for deterministic systems |
| `gronwall_uniqueness` | Grönwall-type uniqueness for ODEs |
| `linear_ode_variation_of_constants` | Variation-of-constants formula |
| `inverse_transform_sampling` | Inverse-transform sampling (23.1) |
| `pdp_simple_markov` / `pdp_strong_markov` | PDP (strong) Markov property |
| `compensator_is_local_martingale` | Compensated PDP is a local martingale |
| `pdp_extended_generator_characterization` | Extended generator domain characterization |
| `pdp_generator_bounded_true_martingale` | Bounded generator ⟹ true martingale |

## Key definitions

| Definition | Description |
|------------|-------------|
| `PDP` | PDP structure: deterministic flow, jump rate, transition kernel |
| `PDPStandard` | PDP with boundary, non-explosion, absolute continuity |
| `pdpGenerator` | PDP extended generator `Af(x) = Xf(x) + λ(x)(Qf(x) − f(x))` |
| `pdpSurvivorFunction` | Survivor function for inter-jump times |

## Depends on

- Mathlib, [Foundations.DavisCh1](Foundations.DavisCh1.md) (via shared definitions)

## Used by

- [Core.Generator](Core.Generator.md)

## Selected results proved

The full ODE / Grönwall / hazard analysis cluster is proved from first principles, using Mathlib's Picard–Lindelöf and absolute-continuity FTC plus reusable infrastructure:

- **`ode_global_existence` (22.1)** — global existence of the flow of a globally Lipschitz autonomous field, built by gluing local Picard–Lindelöf solutions on ever-larger symmetric intervals (`ode_local_fwd/bwd`, `ode_glue`, `ode_pieces`, `ode_within_unique`, `ode_gronwall_dist`, `ode_flow_joint_continuous`).
- **`flow_group_property` (22.3)** — the one-parameter group law, from ODE uniqueness (`ode_gronwall_dist`) under a global Lipschitz hypothesis.
- **`gronwall_uniqueness` (22.9)** — `z t = ∫₀ᵗ a·z` with `z` continuous implies `z ≡ 0`, via the Picard iterate bound `|z t| ≤ M·F(t)ⁿ/n!`.
- **`linear_ode_variation_of_constants` (22.10)** and **`linear_ode_solution_unique_on` (22.9, corrected)** — existence and uniqueness among continuous solutions on `[0,T]`.
- **`survivor_from_hazard` (21.3)** — `Ψ(t) = exp(−∫₀ᵗ ψ/Ψ)`, by differentiating `log Ψ` (AC-FTC).
- **`inverse_transform_sampling` / `realize_measure_real_from_uniform` (23.1)** — any probability measure is the pushforward of `U[0,1]` under the quantile map; supporting `cdf_mem_Icc`, `quantile_le_iff`, `quantile_preimage_ae`.
- **`flow_chain_rule` (22.4)**, **`deterministic_dynkin` (22.5)**, **`exponential_memoryless` (21.1)**, **`poisson_markov_property` (21.5)**, **`renewal_equation` (21.8)**, **`flow_bijective` (22.2)**.
- **`pdp_extended_generator_characterization` (26.14)** — proved in a faithful reformulated form adding the deterministic flow decomposition and the compensated-jump martingale as explicit foundational hypotheses.

## Corrected statements (were false as originally formalized)

- `linear_ode_solution` (22.9): the original `ExistsUnique x : ℝ → ℝ` is false — the fixed-point equation only constrains `x` on `[0,T]`. Corrected to `linear_ode_solution_unique_on` (uniqueness on `[0,T]`).
- `linear_ode_solution_unique_on` / `linear_ode_variation_of_constants` had an operator-precedence bug (the `∫ b` term parsed as nested inside the first integral); now parenthesized as `x₀ + (∫ a·x) + (∫ b)`. Originals preserved (commented).

## Open gaps / sorries

- 13 `sorry` remain. All are the deep measure-theoretic PDP results — the (strong) Markov properties, compensator/martingale representation, `pdpSemigroup` construction, Feller / Borel-right-process properties, and generator-domain boundary conditions — which require building the PDMP itself.

## Notes

This is the most sorry-heavy module in the public distribution, reflecting the depth of Davis's PDP theory. The `PDPStandard` structure bundles non-explosion conditions, filtration properties, and absolute continuity of the jump-time distribution — all needed for the extended generator to be well-defined. The Grönwall uniqueness and ODE comparison results here also support the moment/transient-bound machinery in the full research library.
