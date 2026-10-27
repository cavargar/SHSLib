# Module: SHSLib.Gardiner.SDE

**File:** `SHSLib/Gardiner/SDE.lean` (index and correspondence table) + `SHSLib/Gardiner/SDE/*.lean` (12 modules)
**Layer:** Gardiner (textbook approximation methods)
**Status:** ✅ Complete (0 sorries, standard axioms only)
**Origin:** Aristotle project `f6c52391`

## What it proves

This layer formalizes the small-noise expansion of SDEs (Gardiner §6.2) and the numerical simulation of SDEs (Ch. 10, §10.1–§10.5). It was built **without Brownian motion or a stochastic integral**, which the pinned Mathlib does not provide. The [[Gardiner.Ito]] layer now supplies both and connects to this layer (see the caveats below). All declarations are in the namespace `Gardiner.SDE`.

The layer has three parts:
- **Pathwise analysis for additive noise.** `dx = a(x)dt + ε dw` is solved pathwise for every continuous driving path `w`. The small-noise expansion `x = Σ εⁿxₙ` gets a uniform `O(|ε|^{N+1})` remainder on `[0, T]`. The Euler scheme converges at a rate set by the step size and the modulus of continuity of `w`.
- **Schemes driven by Gaussian increments.** The one-variable schemes are recursions driven by i.i.d. increments `ΔWₙ ~ N(0, τ)` (Mathlib's `gaussianReal`, `iIndepFun`) on an arbitrary probability space. Their first two moments are computed exactly. They are compared with the closed-form moments of the Ornstein–Uhlenbeck SDE and of linear multiplicative noise, giving weak errors of order `τ`.
- **Deterministic properties of the one-step maps.** Stability regions, A-stability, mean-square stability, and the §10.3.1 consistency conditions.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `expansion_remainder` | Expansion algebra (6.2.3)–(6.2.7): `|a(Σεᵐxₘ) − Σ_{n≤N} aₙεⁿ| ≤ 2Me^{(N+1)R}|ε|^{N+1}` |
| `pathwise_expansion`, `linearisation_error` | Additive noise, any continuous path: `|x(t) − Σ_{n≤N} εⁿxₙ(t)| ≤ T e^{LT+1/2}·2Me^{(N+1)R}|ε|^{N+1}` on `[0, T]` |
| `cubic_expansion`, `cubic_linearisation` | Cubic process `dx = −x³dt + ε dw` to order `ε³`; the failure of the stationary expansion (§6.2.4) |
| `euler_pathwise_error` | Euler for additive noise: `|x(nτ) − yₙ| ≤ (e^{Lnτ} − 1)(Aτ + |ε|ω(τ))` |
| `exists_pathSol` | Existence of the pathwise solution for bounded Lipschitz drift |
| `linScheme_mean`, `linScheme_sq` | Exact first and second moments of linear schemes driven by i.i.d. `N(0, τ)` increments |
| `eulerOU_weak_*`, `semiOU_weak_*` | OU, Euler and semi-implicit: mean and second moment within `O(τ)` of the exact moments |
| `eulerGBM_weak_*`, `milsteinGBM_weak_*`, `semiGBM_weak_*` | `dx = λx dt + μx dW`: weak error `O(τ)` for Euler, Milstein and semi-implicit, with explicit constants |
| `euler_stable_iff`, `implicit_AStable`, `semi_AStable`, `euler_not_AStable` | Stability regions (10.3.5), (10.3.12), (10.3.15); A-stability |
| `eulerGBM_ms_stable_iff`, `milsteinGBM_ms_stable_iff`, `implicitGBM_ms_stable` | Mean-square stability for linear multiplicative noise |
| `IsConsistentAt`, `thetaTrunc_consistent_iff`, `naive_implicit_inconsistent` | §10.3.1 consistency as a property of one-step maps; (10.4.10) is necessary and sufficient |
| `strong_error_bound`, `mean_error_bound` | Error recursions (10.1.24)–(10.1.29) as closed inequalities |

The full equation ↔ declaration table, the guarantees table and the errata are the docstring of `SHSLib/Gardiner/SDE.lean`.

## Depends on

- [[Gardiner.Approx]] (`Approx.Calculus`: derivative towers, Taylor bounds), Mathlib (`gaussianReal`, independence, Bochner integral). The Grönwall arguments are self-contained; the layer does not import [[Core.GronwallGrowthBound]].

## Used by

- [[Gardiner.Ito]], which instantiates the pathwise results with Brownian paths and discharges several of the named hypotheses below.

## Open gaps / sorries

None. Caveats from the Itô-free design, and what [[Gardiner.Ito]] has since resolved:
- **Strong convergence.** For the Euler–Maruyama scheme, (10.1.26) is now proved against the true solution of a Lipschitz SDE in [[Gardiner.Ito]] (`Gardiner.Ito.StochDE.euler_strong_order_half`, strong order ½ with an explicit constant). Milstein's strong order 1 (10.1.43), §10.4 a) and the vector schemes §10.5.3–§10.5.5 are still not proved; they need the Itô–Taylor remainder estimates (10.1.36)–(10.1.39). For additive noise the strong question is also answered pathwise by `euler_pathwise_error`.
- **Target moments.** The exact OU and linear-noise moments were closed forms checked against their moment ODEs. `Gardiner.Ito` now derives the moment ODEs from Itô's formula, shows that the actual OU process has moments `ouMean`/`ouSecond` (`ou_weak_process`), and that geometric Brownian motion has moments `gbmMean`/`gbmSecond`.
- **Linearised-process statistics.** The named hypothesis `IsLinearisedLaw` (§6.2.2–§6.2.3) is now discharged by `Gardiner.Ito.IsWiener.isLinearisedLaw_linProc`.
- **Semi-implicit scheme with multiplicative noise.** Solved exactly, the step has no finite moments (the denominator vanishes with positive density). The weak bounds are for the two-iteration version the text says to run (`semiGBM`).
- **Joint laws of multiple stochastic integrals** (§10.1.3) were taken as given distributions; `Gardiner.Ito` realises them from a Wiener process (`multiple_moments`). The vector case (§10.5.2) is still a given distribution.

## Notes

- **Errata.** 16 discrepancies with the printed text are formalized in corrected form, several with `_printed_wrong` certificates:
  - (6.2.47): coefficient;
  - (10.1.18): `½L₁b`, not `½L₀b`;
  - (10.1.42): missing cross term;
  - Fig. 10.1c: the implicit-Euler stability region is the exterior of a disc;
  - (10.5.14): a missing `−δᵢⱼ(t − t₀)`;
  - (10.5.34): a factor `½`.
