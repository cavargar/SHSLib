# Module: SHSLib.Core.Basic

**File:** `SHSLib/Core/Basic.lean`
**Layer:** Core
**Status:** ✅ Complete (0 sorries)

## What it proves

Defines the core `SHS` structure formalizing Hespanha's stochastic hybrid system model (Nonlinear Analysis 2005, Section 2, Eqs. 1–3). An SHS consists of a finite discrete-state space `Q`, continuous state in `ℝⁿ`, `m` reset maps `φ_ℓ`, and `m` transition intensities `λ_ℓ`. The file also formalizes Assumptions 1–2 (global flow existence/uniqueness, measurability/boundedness) and the sample-path construction from Section 2.1.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `SHS.transition_probability_rate` | The probability of a transition in `[t, t+δ)` is `∑ₗ λ_ℓ(q,x,t) δ + o(δ)` |

## Key definitions

| Definition | Description |
|------------|-------------|
| `SHS` | Main SHS structure: vector field `f`, reset maps `phi`, intensities |
| `SHS.phi_q` / `SHS.phi_x` | Projections of reset map onto discrete / continuous components |
| `SHS.HasGlobalFlow` | Assumption 1: global existence and uniqueness of the flow |
| `SHS.GlobalBound` | Assumption 2: measurability and boundedness |
| `SHS.InitialCondition` | Initial condition `(q₀, x₀)` |

## Depends on

- Mathlib

## Used by

- [Core.Generator](Core.Generator.md), and downstream example and application modules in the full research library.

## Notes

This is the foundational module for the entire library. The `SHS` structure is parametric in `Q` (discrete mode type), `n` (continuous dimension), and `m` (number of transition types). Transition intensities carry a built-in nonnegativity proof field. The survivor-function bound underlying `SHS.transition_probability_rate` (Hespanha Eq. 5, `0 < F ≤ 1` for `F = exp(-∫ λ)`) is fully proved.
