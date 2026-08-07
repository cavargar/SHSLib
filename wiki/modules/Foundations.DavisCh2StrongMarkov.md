# Module: SHSLib.Foundations.DavisCh2StrongMarkov

**File:** `SHSLib/Foundations/DavisCh2StrongMarkov.lean`
**Layer:** Foundations
**Status:** ✅ 0 sorries (standard axioms only)

## What it proves

[[Foundations.DavisCh2]] proves the strong Markov property only for stopping
times with **countable range** (`Davis.pdp_strong_markov_of_countable_range`).
This module removes that restriction by dyadic discretisation of `τ`:
approximate a general stopping time from above by countable-range stopping
times, apply the countable-range result to each, and pass to the limit using
right-continuity of the paths.

Key results include `Davis.pdp_strong_markov_of_countable_range_adapted` (a
restatement in which the adaptedness side conditions are discharged) together
with the supporting measurability API:

- `Davis.measurable_apply_stoppingTime_of_countable_range`
- `Davis.measurable_apply_stoppingTime_of_progMeasurable`
- `Davis.measurable_uncurry_of_countable_range`
- `Davis.progMeasurable_of_rightContinuous`

## Caveat

This module imports the *forked-then-adopted* `DavisCh2.lean`. The six original
sorried statements in that file — including the unrestricted `pdp_strong_markov`
— were retired rather than proved; see [[Foundations.DavisCh2]] for the full
accounting of what was certified false and what was replaced.

## Related

[[Foundations.DavisCh2]] · [[Foundations.DavisCh2FiniteProcess]] ·
[[Core.DavisProcessExtensions]]
