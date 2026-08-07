# SHSLib

A Lean 4 / Mathlib formalization of **Stochastic Hybrid Systems (SHS)** — discrete-mode, continuous-state processes that mix ordinary differential flow with random jumps (mode switches and state resets), as introduced by Hespanha (2005) and built on Davis's theory of Piecewise-Deterministic Markov Processes (PDMPs).

## The extended generator

An SHS evolves in mode $q \in Q$ and continuous state $x \in \mathbb{R}^n$, flowing according to $\dot{x} = f(q, x, t)$ between jumps, and jumping to mode $\varphi_q^\ell(q,x,t)$ / state $\varphi_x^\ell(q,x,t)$ with intensity $\lambda_\ell(q,x,t)$, for $\ell = 1, \dots, m$.

For a test function $\psi(q, x, t)$, the **extended generator** $L$ is defined as

$$
(L\psi)(q,x,t) \;=\; \frac{\partial \psi}{\partial x} \cdot f(q,x,t) \;+\; \frac{\partial \psi}{\partial t} \;+\; \sum_{\ell=1}^{m} \Big(\psi\big(\varphi_q^\ell(q,x,t), \varphi_x^\ell(q,x,t), t\big) - \psi(q,x,t)\Big)\, \lambda_\ell(q,x,t).
$$

The first two terms capture drift along the deterministic flow; the sum captures the expected jump contribution across all $m$ transition types.

**Differential form.** Along a sample path of the SHS,

$$
\frac{d}{dt}\, \mathbb{E}\big[\psi(q(t), x(t), t)\big] \;=\; \mathbb{E}\big[(L\psi)(q(t), x(t), t)\big].
$$

**Integral form.** Equivalently,

$$
\mathbb{E}\big[\psi(q(t), x(t), t)\big] \;=\; \psi(q_0, x_0, t_0) \;+\; \mathbb{E}\left[\int_{t_0}^{t} (L\psi)(q(s), x(s), s)\, ds\right].
$$

These identities (`SHS.eq10_differential_generator_formula` and `SHS.theorem1_generator_formula` in `SHSLib/Core/Generator.lean`) are the basis for deriving moment ODEs and the Fokker–Planck equation for the state density.

## A note on faithfulness

Formalizing a paper sometimes shows a stated result to be false as literally
written. Where that happened, this library keeps the original statement in a
comment, proves a **counterexample certificate** next to it, and then proves a
corrected form. Hespanha's Eq. (35) (`SHS.lemma1_linear_growth_bound_false`,
with the corrected `..._varying_rate` in `Core.GronwallGrowthBound`) and three
PDMP results in `Foundations.DavisCh2` are handled this way. Nothing is quietly
weakened.

## Structure

194 modules, entirely free of `sorry` — every theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`.

| Module group | Modules | Contents |
|--------------|--------:|----------|
| `SHSLib.Core.Basic`, `.Generator`, `.GeneratorDefs` | 3 | SHS structure and flow; extended generator $L$, moment evolution, Fokker–Planck |
| `SHSLib.Core.GronwallGrowthBound` | 1 | Grönwall's inequality with a time-varying rate; sample-path growth bounds for flow segments and whole hybrid paths (Hespanha Lemma 1 / Eq. 35) |
| `SHSLib.Core.Davis{Bridge,Construction,Martingale}` | 3 | SHS ↦ Davis PDP; the PDP generator **equals** the extended generator; Hespanha Theorem 2 |
| `SHSLib.Core.Davis*` — reset compensation | 55 | Compensator of the reset part: counter augmentation, conditional holding-time and channel laws, reset-occupation densities, occupation centering |
| `SHSLib.Core.Davis*` — process extensions | 75 | Elapsed-occupation martingales and filtrations, marked-jump processes, two-channel characteristics, age/ramped/refractory/Poisson clock models |
| `SHSLib.Foundations.DavisCh1` | 1 | Measure theory, probability, martingales, Dynkin |
| `SHSLib.Foundations.DavisCh2`, `.DavisCh2StrongMarkov` | 2 | PDMP theory: ODE flows, Grönwall, inverse-transform sampling, the PDP semigroup, and the strong Markov property |
| `SHSLib.Foundations.DavisCh2Finite*` | 3 | Finite-state renewal kernel, semigroup laws, strong Markov property |
| `SHSLib.Foundations.{Stirling,Beta,Digamma,Trigamma,Tetragamma,Polygamma,ClopperPearson,UniformOrderStatistic}*` | 51 | Special-functions groundwork: Stirling/Binet asymptotics, the Beta distribution and its quantiles, the polygamma family, exact binomial intervals, uniform order statistics |

## Building

```bash
lake build
```

Requires [Lean 4](https://leanprover.github.io/) and [Mathlib](https://github.com/leanprover-community/mathlib4) (pinned via `lakefile.toml`).

## Documentation

Per-module notes are in [`wiki/index.md`](./wiki/index.md) — what each module proves, its key theorems and definitions, and remaining gaps.

## References

- M. H. A. Davis, *Markov Models and Optimization*, Chapman & Hall, 1993.
- J. P. Hespanha, "A model for stochastic hybrid systems with application to communication networks," *Nonlinear Analysis*, 2005.

## License

MIT — see [LICENSE](./LICENSE).
