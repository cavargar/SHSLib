# Module group: Davis PDMP process extensions

**Files:** 75 modules under `SHSLib/Core/Davis*.lean`
**Layer:** Core
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `6cbbd3ec`, adopted 2026-08-07

Documented as one page rather than 75 near-identical stubs, following the
convention already used for [[Core.DavisResetCompensation]].

## Scope

Extends the Davis PDMP development past the reset-compensator chain toward a
full generator–martingale theory for the elapsed-time and marked-jump
formulations.

| Family | Count | What it covers |
|--------|-------|----------------|
| `DavisElapsed*` | 20 | Elapsed-occupation martingales; minimal, path and current-state filtrations; observability and full-observability criteria; conditional increments; pathwise products, square-integrability and test bounds; bounded vs relaxed regimes |
| `DavisMarkedJump*` | 9 | Marked-jump filtration, adaptedness, bounded intensity, step laws (incl. horizon), segment and generator martingales, observability |
| `DavisTwoChannel*` | 6 | Two-channel clocks, characteristics, joint/mixed/age test functions |
| `DavisSegment*` | 6 | Segment-level active/completed conditionals, random-window conditionals, fresh centering, hazard Riemann sums, profile regularity |
| `DavisConditional*` | 6 | Conditional holding densities (incl. random window and random threshold), weighted channel and holding variants |
| `DavisStopped*` | 2 | Stopped elapsed-occupation increments and their laws |
| Clock models | 11 | Age, age-counter, ramped, refractory, Poisson clock models with their noise and hazard structure |
| Misc | 15 | `DavisProfileTruncation{,Core}`, `DavisProfileLinearGrowth`, `DavisNonExplosiveLowerBound`, `DavisOccupationRegularCriterion`, `DavisBoundedHazardVacuity`, `DavisCoordinateNoise`, `DavisNoiseBlockMeasurable`, `DavisHoldingDensityHorizon`, `DavisOneSegment*` |

## Provenance caveat

These were built across earlier tasks of project `6cbbd3ec` and sat unapplied
in Aristotle's workspace for roughly four weeks — see
[[Core.DavisResetCompensation]] for the chain they continue. Every module was
verified to compile fresh against the repo with no `sorry` warnings, and none
transitively imports a module containing a live `sorry`.

## Related

[[Core.DavisResetCompensation]] · [[Core.DavisMartingale]] ·
[[Foundations.DavisCh2]] · [[Foundations.DavisCh2StrongMarkov]]
