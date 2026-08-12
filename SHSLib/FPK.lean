/-
# A unifying formulation of the Fokker–Planck–Kolmogorov equation for general
  stochastic hybrid systems

A formalization of J. Bect, *A unifying formulation of the Fokker–Planck–Kolmogorov
equation for general stochastic hybrid systems*, Nonlinear Analysis: Hybrid Systems
4 (2010) 357–370.

The development is organised around the *generalized* FPK equation: a measure-valued
weak formulation `d/dt ⟨μ_t, φ⟩ = ⟨μ_t, L φ⟩` (Definition 7) that covers diffusions,
Markov chains, spontaneous jumps and forced (boundary) jumps in one statement, and
from which the classical density-level equations are recovered under extra regularity.

Correspondence with the items of the paper:

| Bect (2010)                   | Lean                                                        |
| ----------------------------- | ----------------------------------------------------------- |
| §2.1 hybrid state space       | `SHSLib.FPK.HybridStateSpace`                               |
| Eq. (3) pathwise Itô          | `SHSLib.FPK.PathwiseIto`                                    |
| Eq. (4), Eq. (16) generator   | `SHSLib.FPK.DiffusionGenerator`                             |
| Eqs. (6), (7) Lévy system     | `SHSLib.FPK.LevySystemProcess`                              |
| Eq. (8) mean jump intensity   | `SHSLib.FPK.LevySystemIntensity`, `SHSLib.FPK.MeanJumpIntensity` |
| Definition 6                  | `SHSLib.FPK.MeanJumpIntensity`                              |
| Eq. (12), Eq. (13) Dynkin     | `SHSLib.FPK.DynkinFormula`                                  |
| Definition 7, Eq. (15)        | `SHSLib.FPK.GeneralizedFPK`, `SHSLib.FPK.AdjointUniqueness` |
| §3.2 sawtooth                 | `SHSLib.FPK.SawtoothExample`, `SHSLib.FPK.SawtoothSolution` |
| Example 16 master equation    | `SHSLib.FPK.MasterEquation`, `SHSLib.FPK.TwoStateChain`     |
| Example 17 switching diffusions | `SHSLib.FPK.SwitchingDiffusions`                          |
| Example 18 Hespanha SHS       | `SHSLib.FPK.HespanhaBridge`, `SHSLib.FPK.HespanhaDynkin`,   |
|                               | `SHSLib.FPK.HespanhaResetKernel`,                           |
|                               | `SHSLib.FPK.HespanhaResetJacobian`                          |
| Eq. (33) Hespanha FPK         | `SHSLib.FPK.HespanhaFPK`                                    |
| Eq. (19) boundary conditions  | `SHSLib.FPK.BoundaryGeometry`                               |
| Eq. (24), Assumption 14       | `SHSLib.FPK.DualKernelMeasure`                              |
| §4.2, App. C prob. current    | `SHSLib.FPK.ProbabilityCurrent`, `SHSLib.FPK.ProbabilityFlow` |
| §5.3, App. D densities        | `SHSLib.FPK.DensityEvolution`                               |
| §6.1 spontaneous jumps        | `SHSLib.FPK.SpontaneousJumps`                               |
| §6.2 forced jumps             | `SHSLib.FPK.ForcedJumps`, `SHSLib.FPK.JumpDiscontinuity`    |
| App. A divergence theorem     | `SHSLib.FPK.DivergenceTheorem`                              |
| Eqs. (39), (41) TV bounds     | `SHSLib.FPK.TotalVariationBounds`                           |
| Eqs. (42), (43)               | `SHSLib.FPK.AppendixB42`                                    |
| Eqs. (44)–(47)                | `SHSLib.FPK.AppendixC1`, `SHSLib.FPK.AppendixC1Box`,        |
|                               | `SHSLib.FPK.AppendixC1BoxExample`                           |
| Theorem 13 (App. E)           | `SHSLib.FPK.AppendixE`                                      |
| discrete modes only           | `SHSLib.FPK.MarkovChain`                                    |

Naming note: `SHS.levyTotalIntensity` (`SHSLib.FPK.HespanhaBridge`) is `λ = Σ_ℓ λ_ℓ`,
the stochastic intensity of the Lévy system (6) for a Hespanha SHS.  It is distinct
from `SHS.totalIntensity` in `SHSLib.Core.DavisBridge`, which is the Davis-state
total jump rate.
-/

import SHSLib.FPK.AdjointUniqueness
import SHSLib.FPK.AppendixB42
import SHSLib.FPK.AppendixC1
import SHSLib.FPK.AppendixC1Box
import SHSLib.FPK.AppendixC1BoxExample
import SHSLib.FPK.AppendixE
import SHSLib.FPK.BoundaryGeometry
import SHSLib.FPK.DensityEvolution
import SHSLib.FPK.DiffusionGenerator
import SHSLib.FPK.DivergenceTheorem
import SHSLib.FPK.DualKernelMeasure
import SHSLib.FPK.DynkinFormula
import SHSLib.FPK.ForcedJumps
import SHSLib.FPK.GeneralizedFPK
import SHSLib.FPK.HespanhaBridge
import SHSLib.FPK.HespanhaDynkin
import SHSLib.FPK.HespanhaFPK
import SHSLib.FPK.HespanhaResetJacobian
import SHSLib.FPK.HespanhaResetKernel
import SHSLib.FPK.HybridStateSpace
import SHSLib.FPK.JumpDiscontinuity
import SHSLib.FPK.LevySystemIntensity
import SHSLib.FPK.LevySystemProcess
import SHSLib.FPK.MarkovChain
import SHSLib.FPK.MasterEquation
import SHSLib.FPK.MeanJumpIntensity
import SHSLib.FPK.PathwiseIto
import SHSLib.FPK.ProbabilityCurrent
import SHSLib.FPK.ProbabilityFlow
import SHSLib.FPK.SawtoothExample
import SHSLib.FPK.SawtoothSolution
import SHSLib.FPK.SpontaneousJumps
import SHSLib.FPK.SwitchingDiffusions
import SHSLib.FPK.TotalVariationBounds
import SHSLib.FPK.TwoStateChain
