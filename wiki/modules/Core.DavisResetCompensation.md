# Core.DavisResetCompensation — the reset-compensator / occupation-martingale chain

**Status:** ✅ 0 sorries · 55 modules · ~7.4k lines · 176 theorems, 71 defs, 14 structures
**Provenance:** Aristotle project `6cbbd3ec` (`SHSLib_core_theory`), incremental batches 1–74.

This is not a single file but a dependency chain of 55 `SHSLib/Core/Davis*.lean`
modules built one small batch at a time. Its purpose is to construct, from the
ground up, the **compensator of the reset (jump) part of a Davis PDMP** and to
prove that the compensated reset process is a martingale — the ingredient that
[[Core.DavisMartingale]] needs in order to state Hespanha's Theorem 2 for a
concretely constructed process rather than for an assumed local martingale.

## Why it takes 55 modules

The martingale property of the compensated jump process is where the real
measure-theoretic work in PDMP theory lives. Each link in the chain removes one
approximation or one artificial hypothesis:

1. **Observability and history.** `DavisNaturalStopping`,
   `DavisObservableCounter`, `DavisCounterAugmentation`, `DavisPreJumpHistory` —
   augment the mode space with a jump counter, show the jump times are stopping
   times of the resulting natural filtration, and package the information
   available strictly before jump `k` as a finite history with its own discrete
   filtration.
2. **The one-step law.** `DavisHazardLaw`, `DavisHazardDensity`,
   `DavisChannelLaw`, `DavisOneStepLaw` — integrated hazard along the next flow
   segment gives the conditional holding-time law; normalized reset weights give
   the conditional channel law; together they give the joint one-step law.
3. **From event-level laws to integrals.** The `DavisConditionalHolding*` and
   `DavisConditionalChannel*` families lift event-level conditional laws to
   integral identities: threshold-step tests → monotone limits → signed
   (positive/negative-part) tests → Mathlib `condExp`.
4. **Occupation densities.** `DavisResetOccupation*`, `DavisOneSegmentResetCompensation`,
   `DavisResetDecomposition` — identify the density that, weighted by the
   survivor factor, compensates one segment's reset contribution, and split the
   accumulated contribution into realized and compensating parts.
5. **Finite sums, then caps removed.** `DavisFinite*` and `DavisElapsed*` /
   `DavisStopped*` — assemble finite conditionally-centered reset sums, bound
   them uniformly, prove them integrable, then use dominated convergence to
   strip the *deterministic jump caps* and *duration caps* that made each finite
   stage tractable. `DavisFiniteResetMartingale` turns the one-step mean-zero
   identity into a discrete-index martingale; `DavisStoppedResetSum` and the
   `Elapsed` modules transport it from jump index to elapsed time.

## Status of the endpoint

The chain currently reaches **event-localized centering of fixed-time increments**
(`DavisElapsedOccupationIncrementCentering`). The final continuous-time
martingale statement is not yet closed. The remaining documented steps, per
the research repository’s batch notes, are:
natural-filtration measurability/adaptedness, restricted-integrability
constructors, direct conditional increment laws, and martingale/generator
packaging.

Batch-by-batch rationale is kept in the research repository and is not mirrored
here.

## Related

- [[Core.DavisConstruction]] — the concrete time-augmented Davis PDP this chain compensates
- [[Core.DavisMartingale]] — consumer of the martingale result
- [[Core.DavisBridge]] — SHS ↦ Davis PDP compatibility
- [[Foundations.DavisCh2]] — Davis Chapter 2 statements this development discharges
