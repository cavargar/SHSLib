# Module group: FPK — Bect (2010)

**Files:** 35 modules under `SHSLib/FPK/` + the `SHSLib/FPK.lean` index
**Layer:** FPK
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `53e745c7`, adopted 2026-08-12

A formalization of J. Bect, *A unifying formulation of the Fokker–Planck–Kolmogorov
equation for general stochastic hybrid systems*, Nonlinear Analysis: Hybrid Systems
4 (2010) 357–370.

The organising result is the measure-valued weak formulation of **Definition 7**,

$$\frac{d}{dt}\,\langle \mu_t, \varphi\rangle \;=\; \langle \mu_t, L\varphi\rangle,$$

which covers diffusions, Markov chains, spontaneous jumps and forced (boundary)
jumps in a single statement; the classical density-level equations are recovered
from it under extra regularity. This is what makes the formulation *unifying*, and
it is the reason the same theorem specializes to Hespanha's FPK equation (33) via
`FPK.HespanhaBridge`.

| Group | Modules | Contents |
|-------|--------:|----------|
| State space and generator | 4 | `HybridStateSpace` (§2.1), `PathwiseIto` (3), `DiffusionGenerator` (4)/(16), `DivergenceTheorem` (App. A) |
| Lévy system and intensity | 3 | `LevySystemProcess` (6)/(7), `LevySystemIntensity` (8), `MeanJumpIntensity` (Definition 6) |
| The generalized equation | 3 | `DynkinFormula` (12)/(13), `GeneralizedFPK` (Definition 7), `AdjointUniqueness` (15) |
| Current, flow, densities | 4 | `ProbabilityCurrent`, `ProbabilityFlow` (§4.2, App. C), `DensityEvolution` (§5.3, App. D), `BoundaryGeometry` (19) |
| Jump structure | 4 | `SpontaneousJumps` (§6.1), `ForcedJumps` (§6.2), `JumpDiscontinuity`, `DualKernelMeasure` (24, Assumption 14) |
| Hespanha bridge (Example 18) | 4 | `HespanhaBridge`, `HespanhaDynkin`, `HespanhaResetKernel`, `HespanhaResetJacobian`, giving `HespanhaFPK` (33) |
| Worked solutions | 5 | `MasterEquation` and `TwoStateChain` (Example 16), `SawtoothExample` and `SawtoothSolution` (§3.2), `SwitchingDiffusions` (Example 17), `MarkovChain` |
| Appendices | 5 | `TotalVariationBounds` (39)/(41), `AppendixB42` (42)/(43), `AppendixC1`, `AppendixC1Box`, `AppendixC1BoxExample` (44)–(47), `AppendixE` (Theorem 13) |

`SHSLib/FPK.lean` carries the full Bect-item → Lean-name correspondence table in its
docstring.

## Not vacuous

Two modules exist specifically to show the general statements have content.
`AppendixC1BoxExample` discharges *every* hypothesis of Eq. (46) on a concrete model
(deterministic dynamics, constant drift, unit density, test function
$\exp(y^1+\cdots+y^{n+1})$), recovering the divergence theorem for that field.
`SawtoothSolution` exhibits the transport term and the forced-jump term cancelling
exactly, and tests against $\sin$ to witness that the two cancelling terms are
individually nonzero.

## Naming

`SHS.levyTotalIntensity` (in `FPK.HespanhaBridge`) is $\lambda = \sum_\ell \lambda_\ell$,
the stochastic intensity of the Lévy system (6) for a Hespanha SHS. It is deliberately
distinct from `SHS.totalIntensity` in `Core.DavisBridge`, which is the Davis-state
total jump rate.

## Related

`Core.Generator` · `Core.DavisBridge` · `Bujorianu2006` · `Gardiner`

## Itô diffusions (v2.3.0)

`SHSLib/FPK/ItoDiffusion.lean` builds `GSHS.ItoDiffusion.fpkData a b P x`, the jump-free `FPKData ℝ C2cTest` of a one-dimensional diffusion `dx = a(x) dt + b(x) dW` (laws `P ∘ x(t)⁻¹`, generator `a φ′ + ½ b² φ″`, mean jump intensity `r = 0`), and proves Bect's generalized Dynkin formula (13), `WeakDynkin`, for SDE solutions that exist on every horizon (`weakDynkin_of_isSDESol`). Instance: the standard Wiener process (`weakDynkin_stdWiener`), whose weak Dynkin formula is the weak heat equation. See [[Gardiner.Ito]].
