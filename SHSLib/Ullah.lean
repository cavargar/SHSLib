/-
# §8.2, Derivation of the differential Chapman–Kolmogorov equation

A formalization of the derivation in §8.2 ("Derivation of the dCKE") of Chapter 8,
*Hybrid Markov Processes*, of M. Ullah and O. Wolkenhauer, *Stochastic Approaches for
Systems Biology*.

Unlike the derivation of Gardiner formalized in `SHSLib.Gardiner`, this one
starts from the time derivative of the probability density itself rather than from
the expectation of an arbitrary test function, so no integration by parts and no
boundary condition on the density are involved.

The process lives on `ℝⁿ` (`Gardiner.Sp n`); `p t y` is the state probability density
`p(y, t)` and `k dt y' y` is the transition density `p(y, t + Δt | y', t)`.
`W y y'` is the transition rate `W(y | y', t)` for the jump `y' → y`.

Correspondence with the equations of the text:

| §8.2                        | Lean                                              |
| --------------------------- | ------------------------------------------------- |
| (8.4)                       | `Ullah.timeQuot`                                   |
| (8.3) + normalization       | `Ullah.timeQuot_eq_IQuot_univ`                     |
| (8.5)                       | `Ullah.flux`, `Ullah.IQuot`                        |
| (8.6)                       | `Ullah.IQuot_split`                                |
| (8.7), `y - y' = q`         | `Ullah.IQuot_ball_eq_shift`                        |
| `f(y; q)`                   | `Ullah.fq`                                         |
| `f(y-q; q) - f(y; -q)`      | `Ullah.flux_sub_eq`                                |
| Taylor expansion            | `Ullah.taylorPoly_shift`, `Ullah.flux_sub_decomp`  |
| `∫ f(y;q) dq = ∫ f(y;-q) dq`| `Ullah.setIntegral_ball_neg`,                      |
|                             | `Ullah.integral_fq_sub_reflect`                    |
| `I_{‖q‖<ε}` after expansion | `Ullah.near_expansion`                             |
| `⟨ΔY_i⟩_y`, `⟨ΔY_iΔY_j⟩_y`  | `Ullah.Mom1`, `Ullah.Mom2`                         |
| (8.8), (8.9)                | `Ullah.condDrift_iff_mom`,                         |
|                             | `Ullah.condDiffusion_iff_mom`                      |
| vanishing of `C_{ijk}`      | `Ullah.third_coefficient_eq_zero`                  |
| (8.11)                      | `Ullah.fpTerm`, `Ullah.near_tendsto`,              |
|                             | `Ullah.near_limit_eps`                             |
| (8.12)                      | `Ullah.jumpFar`, `Ullah.jumpTerm`,                 |
|                             | `Ullah.jumpFar_tendsto`                            |
| (8.13), the dCKE            | `Ullah.differentialCK`,                            |
|                             | `Ullah.differentialCK_of_kernel`                   |

The differentiability conditions (8.8) and (8.9) are the conditions (ii) and (iii)
of Gardiner's §3.4, already available as `Gardiner.CondDrift` and
`Gardiner.CondDiffusion`; `Ullah.condDrift_iff_mom` and `Ullah.condDiffusion_iff_mom`
identify them with the conditions on the conditional moments `⟨ΔY_i⟩_y` and
`⟨ΔY_i ΔY_j⟩_y` used in Chapter 8, via the change of variables `q = y' - y`.

As in the text, the steps that are performed informally appear as explicit
hypotheses: the interchange of `∂/∂y_i` with the `q`-integration (`hswap₁`, `hswap₂`),
the interchange of the limit `Δt → 0` with the `y'`-integration on the far region
(`hfar`), and the vanishing of the Taylor remainder as `ε → 0` (`hReps`).  Every
other step — the passage from (8.4) to (8.5), the splitting (8.6), the two changes of
variables of (8.7), the Taylor expansion, the cancellation of the first two terms,
the recognition of the conditional moments, the vanishing of the third-order
coefficient, the `ε → 0` limit of the jump region, and the final assembly (8.13) —
is proved.
-/
import SHSLib.Ullah.Basic
import SHSLib.Ullah.Near
import SHSLib.Ullah.Limits
import SHSLib.Ullah.DCKE
