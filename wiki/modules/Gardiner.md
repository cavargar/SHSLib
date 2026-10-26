# Module group: Gardiner — *Handbook of Stochastic Methods*

**Files:** 7 Ch. 3 modules under `SHSLib/Gardiner/` + the `SHSLib/Gardiner.lean` index, and five further layers (96 modules, v2.2.0) listed below
**Layer:** Gardiner
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `9bb78578`

A formalization of §3.4–3.6 of C. W. Gardiner, *Handbook of Stochastic Methods*:
the textbook derivation of the differential Chapman–Kolmogorov equation (dCKE) from
three conditions on the short-time behaviour of the transition density.

The process lives on all of $\mathbb{R}^n$, as in the last paragraph of §3.4.1, so
the surface terms of (3.4.19) are absent.

| Module | Contents |
|--------|----------|
| `Basic` | State space $\mathbb{R}^n$, partial derivatives, Taylor remainder, conditions (i)–(iii) |
| `Taylor` | Uniform second-order Taylor estimate (3.4.11) |
| `WeakForm` | Weak form of the dCKE (3.4.16) against test functions |
| `Strong` | Integration by parts (3.4.19) and the strong form (3.4.22) |
| `HigherMoments` | Vanishing of the third (3.4.4)–(3.4.7) and all higher conditional moments |
| `Special` | The three special cases of (3.4.22): Master equation (3.5.2), Fokker–Planck (3.5.6), Liouville (3.5.13); symmetry and positive semidefiniteness of $B$; the Gaussian solution (3.5.9) |
| `Backward` | The backward differential Chapman–Kolmogorov equation (§3.6) |

`SHSLib/Gardiner.lean` carries the full (3.4.x)/(3.5.x) equation → Lean-name
correspondence table in its docstring.

## Further layers (v2.2.0)

| Layer | Modules | Contents |
|-------|--------:|----------|
| [[Gardiner.Approx]] | 15 | Ch. 6–7: small-noise expansion, Kramers–Moyal, system-size expansion / linear noise approximation with explicit generator bounds, chemical Fokker–Planck equation |
| [[Gardiner.Adiabatic]] | 12 | §6.4–6.6: adiabatic elimination with explicit error bounds |
| [[Gardiner.Escape]] | 12 | §5.2.7–5.2.8, §7.4, Ch. 9: first-passage times, splitting probabilities, Kramers escape rate as a limit |
| [[Gardiner.SDE]] | 13 | §6.2, Ch. 10: pathwise small-noise expansion, numerical schemes with weak-error bounds, stability, consistency |
| [[Gardiner.Ito]] | 44 | Ch. 4: Wiener process (`IsWiener`, `stdWiener`), simple / Wiener / L² Itô integrals, Itô's formula (4.3.14), Ornstein–Uhlenbeck and geometric Brownian motion; `Ito.Calculus` and `Ito.CalculusBridge` |

Each layer's index module (`SHSLib/Gardiner/{Approx,Adiabatic,Escape,SDE,Ito}.lean`) carries its
equation → Lean correspondence table and errata. The Itô layer depends on the pinned
`brownian-motion` package; see the README.

## Related

`Ullah` — the same equation derived by a different route (near/far region splitting,
no integration by parts), with `Ullah.condDrift_iff_mom` and
`Ullah.condDiffusion_iff_mom` identifying that text's conditions (8.8)/(8.9) with
`Gardiner.CondDrift` and `Gardiner.CondDiffusion`.

`FPK` — Bect's measure-valued generalization to hybrid state spaces.
