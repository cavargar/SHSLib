# SHSLib

A Lean 4 / Mathlib formalization of **Stochastic Hybrid Systems (SHS)** — discrete-mode, continuous-state processes that mix ordinary differential flow with random jumps (mode switches and state resets), as introduced by Hespanha (2005) and built on Davis's theory of Piecewise-Deterministic Markov Processes (PDMPs).

This is a minimal public mirror containing only the foundational theory. The full research library (worked examples from cell biology, epidemiology, and networked systems) lives in a separate private repository.

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

## Structure

| Module | Contents |
|--------|----------|
| `SHSLib.Core.Basic` | SHS structure, assumptions, flow |
| `SHSLib.Core.Generator` | Extended generator $L$, moment evolution, Fokker–Planck equation |
| `SHSLib.Foundations.DavisCh1` | Measure theory, probability, and stochastic-process foundations |
| `SHSLib.Foundations.DavisCh2` | Piecewise-Deterministic Markov Process (PDMP) theory |

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
