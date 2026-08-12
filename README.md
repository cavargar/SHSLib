# SHSLib

A Lean 4 / Mathlib formalization of **Stochastic Hybrid Systems (SHS)** — discrete-mode, continuous-state processes that mix ordinary differential flow with random jumps (mode switches and state resets), as introduced by Hespanha (2005) and built on Davis's theory of Piecewise-Deterministic Markov Processes (PDMPs).

Alongside the Hespanha/Davis core, the library formalizes three further treatments of the same circle of ideas: Bect's (2010) unifying Fokker–Planck–Kolmogorov equation for general stochastic hybrid systems, Bujorianu & Lygeros's (2006) general theory of stochastic hybrid systems, and the textbook derivations of the differential Chapman–Kolmogorov equation from Gardiner and from Ullah & Wolkenhauer.

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

## Forward equations

Three further layers formalize the *forward* (density- or measure-level) evolution. They are stated here exactly as they appear in Lean, with the declaration that proves each one.

### The differential Chapman–Kolmogorov equation (Gardiner §3.4)

For a Markov process on $\mathbb{R}^n$ with drift $A_i$, diffusion $B_{ij}$ and jump rate $W(z \mid x)$, the transition density $p(z,t \mid y,t')$ satisfies

$$
\frac{\partial p}{\partial t}(z)
\;=\; -\sum_i \frac{\partial}{\partial z_i}\Big[A_i(z)\,p(z)\Big]
\;+\; \frac{1}{2}\sum_{i,j} \frac{\partial^2}{\partial z_i \partial z_j}\Big[B_{ij}(z)\,p(z)\Big]
\;+\; \int \Big( W(z \mid x)\,p(x) - W(x \mid z)\,p(z) \Big)\,dx .
$$

This is Gardiner (3.4.22), proved as `Gardiner.differentialCK` (right-hand side `Gardiner.ckRHS`) from the weak form (3.4.16) `Gardiner.differentialCK_weak` by integration by parts (3.4.19). Dropping the jump term gives the **Fokker–Planck** equation (3.5.6), dropping the second-order term gives the **Master** equation (3.5.2), and keeping only the drift gives **Liouville's** equation (3.5.13) — all three in `Gardiner.Special`. The third and all higher conditional moments are proved to vanish (`Gardiner.CondThird.eq_zero`, `Gardiner.CondHigher.eq_zero`), which is what makes the truncation legitimate rather than an approximation.

### The same equation, derived without integration by parts (Ullah §8.2)

`Ullah.differentialCK` reaches the identical right-hand side — `Ullah.fpTerm` for the drift/diffusion part and `Ullah.jumpTerm` $= \int (W(y \mid y')p(y') - W(y' \mid y)p(y))\,dy'$ for the jump part — by splitting the gain–loss flux into a near region $\lVert q \rVert < \varepsilon$ and a far region and taking the two limits (8.11), (8.12) separately.

The two derivations are formally connected, not merely parallel: `Ullah.condDrift_iff_mom` and `Ullah.condDiffusion_iff_mom` prove that that text's conditions (8.8), (8.9) are Gardiner's conditions (ii), (iii).

### The generalized FPK equation for hybrid systems (Bect 2010)

On a hybrid state space the density may not exist, so the equation is stated for the **law $\mu_t$ as a measure**. Writing $\langle \mu, \varphi\rangle = \int \varphi \, d\mu$, a family $(\mu_t)$ is a solution when $t \mapsto \langle \mu_t, \varphi\rangle$ is differentiable with

$$
\frac{d}{dt}\,\langle \mu_t, \varphi \rangle
\;=\; \underbrace{\langle \mu_t,\, L\varphi \rangle}_{\text{flow and diffusion}}
\;+\; \underbrace{\big\langle r_t,\, (K - I)\varphi \big\rangle}_{\text{jumps}},
\qquad
\big\langle r_t, (K-I)\varphi \big\rangle = \int \Big( \int \varphi\,dK(x,\cdot) - \varphi(x) \Big) dr_t(x),
$$

where $L$ is the generator, $K$ the reset kernel and $r_t$ the mean jump intensity. This is Definition 7 / Eq. (14), `GSHS.FPKData.IsWeakFPKSolution`; its integrated form is the generalized Dynkin formula (13), `GSHS.FPKData.WeakDynkin`:

$$
\langle \mu_t, \varphi\rangle - \langle \mu_0, \varphi\rangle \;=\; \int_0^t \langle \mu_s, L\varphi\rangle\,ds \;+\; \int_0^t \big\langle r_s, (K-I)\varphi \big\rangle\,ds .
$$

For a diffusion in each mode with drift $f_0$ and noise fields $f_1,\dots,f_r$, the generator is Eq. (16), `GSHS.generatorL`:

$$
(L\varphi)(x) \;=\; \sum_i f_0^i(x)\,\partial_i \varphi(x) \;+\; \frac{1}{2}\sum_{i,j} a^{ij}(x)\,\partial^2_{ij}\varphi(x),
\qquad a^{ij} = \sum_{l} f_l^i f_l^j .
$$

The point of the formulation is that a single equation covers diffusions, Markov chains, spontaneous jumps and **forced jumps at the boundary**, with the classical density-level equations recovered under extra regularity. Bect's Example 18 specializes it back to the Hespanha SHS above, recovering Eq. (33) (`SHSLib/FPK/HespanhaFPK.lean`).

## A note on faithfulness

Formalizing a paper sometimes shows a stated result to be false as literally
written. Where that happened, this library keeps the original statement in a
comment, proves a **counterexample certificate** next to it, and then proves a
corrected form. Hespanha's Eq. (35) (`SHS.lemma1_linear_growth_bound_false`,
with the corrected `..._varying_rate` in `Core.GronwallGrowthBound`) and three
PDMP results in `Foundations.DavisCh2` are handled this way. Nothing is quietly
weakened.

## Structure

271 modules, entirely free of `sorry` — every theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. There are no `axiom`
declarations anywhere in the library.

| Module group | Modules | Contents |
|--------------|--------:|----------|
| `SHSLib.Core.Basic`, `.Generator`, `.GeneratorDefs` | 3 | SHS structure and flow; extended generator $L$, moment evolution, Fokker–Planck |
| `SHSLib.Core.GronwallGrowthBound` | 1 | Grönwall's inequality with a time-varying rate; sample-path growth bounds for flow segments and whole hybrid paths (Hespanha Lemma 1 / Eq. 35) |
| `SHSLib.Core.Davis{Bridge,Construction,Martingale}` | 3 | SHS ↦ Davis PDP; the PDP generator **equals** the extended generator; Hespanha Theorem 2 |
| `SHSLib.Core.Davis*` — reset compensation | 55 | Compensator of the reset part: counter augmentation, conditional holding-time and channel laws, reset-occupation densities, occupation centering |
| `SHSLib.Core.Davis*` — process extensions | 75 | Elapsed-occupation martingales and filtrations, marked-jump processes, two-channel characteristics, age/ramped/refractory/Poisson clock models |
| `SHSLib.Core.{Flow,GlobalFlow,Envelope,LinearGrowth,ExplicitFlows}*`, `.DavisModeBlind`, `.DavisTransitionFree` | 13 | Global existence and uniqueness of the flow under Lipschitz and under locally-Lipschitz-plus-linear-growth drifts; flow regularity and dependence on the initial state; growth envelopes and their sharpness; the deterministic Dynkin identity along the flow; Theorem 1 for transition-free and mode-blind systems |
| `SHSLib.Foundations.DavisCh1` | 1 | Measure theory, probability, martingales, Dynkin |
| `SHSLib.Foundations.DavisCh2`, `.DavisCh2StrongMarkov`, `.DavisCh2ProcessLinks` | 3 | PDMP theory: ODE flows, Grönwall, inverse-transform sampling, the PDP semigroup, the strong Markov property, and process-level links |
| `SHSLib.Foundations.DavisCh2Finite*` | 3 | Finite-state renewal kernel, semigroup laws, strong Markov property |
| `SHSLib.Foundations.{Stirling,Beta,Digamma,Trigamma,Tetragamma,Polygamma,ClopperPearson,UniformOrderStatistic}*` | 51 | Special-functions groundwork: Stirling/Binet asymptotics, the Beta distribution and its quantiles, the polygamma family, exact binomial intervals, uniform order statistics |
| `SHSLib.Foundations.BetaOrderStatistic*` | 6 | Moments of order statistics of a Beta sample: reflected and direct fractional moments, mean/variance of the $(j{+}1)$-st order statistic, Chebyshev concentration, the integer-exponent product form, and variance bounds from a Lipschitz parent quantile |
| `SHSLib.FPK.*` | 36 | Bect (2010): the generalized Fokker–Planck–Kolmogorov equation for general stochastic hybrid systems — hybrid state space, Lévy systems, the generalized Dynkin formula, probability current, boundary conditions, densities, and worked solutions (two-state chain, sawtooth) |
| `SHSLib.Gardiner.*` | 8 | Gardiner, *Handbook of Stochastic Methods* §3.4–3.6: derivation of the differential Chapman–Kolmogorov equation in weak and strong form, and its Master / Fokker–Planck / Liouville special cases |
| `SHSLib.Ullah.*` | 5 | Ullah & Wolkenhauer, *Stochastic Approaches for Systems Biology* §8.2: the same dCKE derived by near/far region splitting, without integration by parts |
| `SHSLib.Bujorianu2006.*` | 8 | Bujorianu & Lygeros (2006): general stochastic hybrid systems — hybrid state space, Markov strings, jump measures, resolvent and $p$-excessive functions, terminal times, the strong generator and Dynkin's formula |

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
- J. Bect, "A unifying formulation of the Fokker–Planck–Kolmogorov equation for general stochastic hybrid systems," *Nonlinear Analysis: Hybrid Systems* 4 (2010) 357–370.
- C. W. Gardiner, *Handbook of Stochastic Methods for Physics, Chemistry and the Natural Sciences*, Springer.
- M. Ullah and O. Wolkenhauer, *Stochastic Approaches for Systems Biology*, Springer, 2011.
- M. L. Bujorianu and J. Lygeros, "Toward a general theory of stochastic hybrid systems," in *Stochastic Hybrid Systems*, LNCIS 337, Springer, 2006.

## License

MIT — see [LICENSE](./LICENSE).
