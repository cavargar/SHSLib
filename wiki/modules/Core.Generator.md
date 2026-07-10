# Module: SHSLib.Core.Generator

**File:** `SHSLib/Core/Generator.lean`
**Layer:** Core
**Status:** ✅ Complete (0 sorries)

## What it proves

Formalizes the extended generator `L` for SHS expectations (Hespanha 2005, Theorems 1–2, Lemmas 1–2), the Fokker–Planck equation (FPE) for SHS with invertible resets, conservation of probability, generator–FPE duality, and the moment evolution equation derived from the FPE. Also introduces generalizations: `SHS.WithDiffusion` adding Itô diffusion terms, and the full FPE with diffusion.

## The extended generator

For a test function `ψ(q, x, t)`, the extended generator is (Eq. 9)

```
(Lψ)(q,x,t) = ⟨∂ψ/∂x, f(q,x,t)⟩ + ∂ψ/∂t
              + Σ_{ℓ=1}^{m} (ψ(φ_ℓ(q,x,t), t) − ψ(q,x,t)) · λ_ℓ(q,x,t)
```

with the two equivalent formulations of the generator formula:

- **Integral form** (Theorem 1): `E[ψ(q(t),x(t),t)] = ψ(q₀,x₀,t₀) + E[∫_{t₀}^{t} (Lψ) ds]`
- **Differential form** (Eq. 10): `d/dt E[ψ(q(t),x(t),t)] = E[(Lψ)(q(t),x(t),t)]`

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `SHS.theorem2_PDP_generator` | Theorem 2: generator formula for PDP-type SHS |
| `SHS.lemma2_bounded_implies_finite` | Bounded test functions have finite expectations |
| `SHS.theorem1_generator_formula` | Theorem 1: full generator formula (integral form) |
| `SHS.eq10_differential_generator_formula` | Eq. 10: differential form of the generator formula |
| `SHS.lemma1_linear_growth_bound` | Lemma 1: linear growth bound (corrected, provable form) |
| `SHS.lemma1_linear_growth_bound_false` | Certificate that the original Eq. (35) statement is false |
| `SHS.WithDiffusion.generator_limit` | Generator for SHS with Itô diffusion |
| `SHS.fokkerPlanck_weak_form` | Weak-form FPE from generator duality |
| `SHS.fokkerPlanck_from_generator` | Strong-form FPE derived from Theorem 1 |
| `SHS.fokkerPlanck_conserves_mass` | Total probability is conserved by FPE dynamics |
| `SHS.fokkerPlanck_total_mass_one` | Mass stays 1 if initially 1 |
| `SHS.generator_fokkerPlanck_duality` | Full generator–FPE duality |
| `SHS.fokkerPlanck_moment_evolution` | Moment evolution from FPE integration |

## Key definitions

| Definition | Description |
|------------|-------------|
| `SHS.TestFunction` | Test function `ψ(q, x, t)` with required regularity |
| `SHS.extendedGenerator` | Extended generator `Lψ` (Eq. 9) |
| `SHS.FokkerPlanckData` | FPE data: density, inverse resets, Jacobians |
| `SHS.FokkerPlanckData.fokkerPlanckRHS` | Right-hand side of the FPE |
| `SHS.FokkerPlanckData.conditionalMoment` | Conditional moment `E[xᵐ | q]` |
| `SHS.WithDiffusion` | SHS extended with Itô diffusion `σ dW` |

## Depends on

- [Core.Basic](Core.Basic.md), [Foundations.DavisCh1](Foundations.DavisCh1.md), [Foundations.DavisCh2](Foundations.DavisCh2.md)

## Used by

- Downstream example and application modules in the full research library (moment analysis, cell-size control, epidemiological and networked-system examples).

## Notes

At ~1300 lines, this is the largest core module. It bridges the generator (expectation-side) view and the FPE (density-side) view of SHS dynamics. The FPE construction requires invertible continuous resets (`phi_inv_x` with left/right inverse proofs). A `Generalized` variant relaxes the original `SHS` structure to allow measurable-space-valued modes.

Two statement corrections were certified during formalization: Hespanha's Lemma 1 (Eq. 35) is **false** as literally stated (the `c_f / γ_f` term collapses under Lean's division-by-zero convention when `γ_f = 0`); `SHS.lemma1_linear_growth_bound_false` certifies this, and `SHS.lemma1_linear_growth_bound` gives the corrected, provable form using a constant growth rate and a Grönwall envelope.
