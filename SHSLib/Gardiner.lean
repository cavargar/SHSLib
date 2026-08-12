/-
# Derivation of the differential Chapman–Kolmogorov equation

A formalization of §3.4.1 of C. W. Gardiner, *Handbook of Stochastic Methods*.

The process is a Markov process on `ℝⁿ`; `p s z` denotes the conditional density
`p(z, s | y, t')` for a fixed initial condition, and `k dt z x` denotes the transition
density `p(x, t + dt | z, t)` at the fixed time `t` at which the equation is derived.

Correspondence with the equations of the text:

| Gardiner            | Lean                                                     |
| ------------------- | -------------------------------------------------------- |
| (3.4.1) condition i | `Gardiner.CondJump`                                       |
| (3.4.2) condition ii| `Gardiner.CondDrift`                                      |
| (3.4.3) condition iii| `Gardiner.CondDiffusion`                                 |
| (3.4.8)             | `Gardiner.diffQuot`                                       |
| (3.4.9)             | `Gardiner.diffQuot_eq`                                    |
| (3.4.10)            | `Gardiner.taylorPoly`, `Gardiner.taylorRem`               |
| (3.4.11)            | `Gardiner.uniform_taylorRem`                              |
| (3.4.12)            | `Gardiner.diffQuot_split`                                 |
| (3.4.13)            | `Gardiner.driftDiffTerm`                                  |
| (3.4.14)            | `Gardiner.Q3_le`                                          |
| (3.4.15)            | `Gardiner.jumpPre_eq_jumpTerm`                            |
| (3.4.16)            | `Gardiner.differentialCK_weak`,                           |
|                     | `Gardiner.differentialCK_weak_of_kernel`                  |
| (3.4.17)            | the hypothesis `hPV` of the two theorems above            |
| (3.4.19)            | `Gardiner.driftDiffTerm_integrationByParts`               |
| (3.4.22)            | `Gardiner.differentialCK`                                 |

As in the last paragraph of §3.4.1, the process is taken to live on all of `ℝⁿ`, so
that the surface terms of (3.4.19) are absent.

## §3.5, interpretation of the conditions and results

The three special cases of (3.4.22) and the facts stated about them:

| Gardiner            | Lean                                                      |
| ------------------- | --------------------------------------------------------- |
| (3.5.2) Master equation      | `Gardiner.masterEquation`                          |
| (3.5.6) Fokker–Planck equation | `Gardiner.fpRHS`, `Gardiner.fokkerPlanck`        |
| (3.5.13) Liouville's equation | `Gardiner.liouvilleRHS`, `Gardiner.liouville`     |
| (3.5.17)–(3.5.21) deterministic solution | `Gardiner.liouville_deterministic_weak` |
| symmetry of `B`     | `Gardiner.CondDiffusion.symm_of_cond`                       |
| positive semidefiniteness of `B` | `Gardiner.CondDiffusion.posSemidef_of_cond`    |
| (3.5.9) Gaussian solution of (3.5.8) | `Gardiner.gauss`,                          |
|                     | `Gardiner.gauss_solves_fokkerPlanck`                        |

## §3.4, vanishing of the higher order coefficients

| Gardiner            | Lean                                                      |
| ------------------- | --------------------------------------------------------- |
| (3.4.4)             | `Gardiner.CondThird`                                        |
| (3.4.5)             | `Gardiner.cubicForm`                                        |
| (3.4.7)             | `Gardiner.CondThird.eq_zero`,                               |
|                     | `Gardiner.CondThird.cubicForm_eq_zero`                      |
| all higher orders   | `Gardiner.CondHigher`, `Gardiner.CondHigher.eq_zero`        |

## §3.6, the backward equations

`G s z` is `p(x, t | z, s)` for a fixed final condition `(x, t)`, and `k ds y z` is
`p(z, t' + ds | y, t')`.

| Gardiner            | Lean                                                      |
| ------------------- | --------------------------------------------------------- |
| (3.6.1)–(3.6.2)     | `Gardiner.backward_ck_step`                                 |
| (3.6.3)             | `Gardiner.bwdQuot`, and the hypothesis `h363` of            |
|                     | `Gardiner.backwardDifferentialCK`                           |
| splitting at `|z - y| = ε` | `Gardiner.bwdQuot_split`                             |
| remainder estimate  | `Gardiner.bQ3_le`                                           |
| conditions (ii),(iii) | `Gardiner.bQ12_eq`, `Gardiner.bQ12_tendsto`               |
| generator form      | `Gardiner.backward_generator`,                              |
|                     | `Gardiner.backward_generator_of_kernel`                     |
| (3.6.4)             | `Gardiner.backwardDifferentialCK`                           |
-/
import SHSLib.Gardiner.Basic
import SHSLib.Gardiner.Taylor
import SHSLib.Gardiner.WeakForm
import SHSLib.Gardiner.Strong
import SHSLib.Gardiner.Special
import SHSLib.Gardiner.HigherMoments
import SHSLib.Gardiner.Backward
