# Foundations.DavisCh2ProcessLinks

**File:** `SHSLib/Foundations/DavisCh2ProcessLinks.lean`
**Layer:** Foundations
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `53e745c7`, adopted 2026-08-12

Process-level links for Davis Chapter 2. Several statements in the text relate a PDP
to a filtration and a process; formalized *without* those links they are false, and
this module supplies both the certificates and the faithful replacements.

## Contents

- **Falsity certificates.** `pdp_simple_markov_false`, `pdp_strong_markov_false` and
  `pdp_is_borel_right_process_false` show that the unlinked forms fail. (The
  certificates for Davis (25.3), (26.7) and (26.14) live in
  [Foundations.DavisCh2](Foundations.DavisCh2.md).)
- **Faithful replacements.** `filtration_rightLimit_idem` — the right-limit
  filtration $\mathcal{F}^+_t = \bigwedge_{\varepsilon>0}\mathcal{F}_{t+\varepsilon}$
  *is* right-continuous; `pdp_simple_markov_of_kernel`;
  `strong_markov_of_simple_of_countable_range`;
  `compensator_is_local_martingale_of_stopped`; `pdp_boundary_condition_const`.
- **Dyadic approximation.** `dyadicUp` and its convergence and stopping-time lemmas,
  used to pass from countable-range stopping times to right-continuous paths:
  `strong_markov_of_simple_of_rightContinuous`,
  `expectation_strong_markov_of_simple_of_rightContinuous`,
  `strong_markov_of_simple_of_progMeasurable`.

## On faithfulness

Davis's Proposition 25.3(i) asserts right-continuity of an arbitrary filtration given
right-continuous paths. That is refuted here: take $X$ constant and $\mathcal{F}$ the
filtration on `Bool` that is trivial at time $0$ and complete afterwards, so
$\mathcal{F}_0 = \bot$ while $\bigwedge_{\varepsilon>0}\mathcal{F}_\varepsilon = \top$.
Any faithful version must go through the right-continuation $\mathcal{F}^+$.

## Related

`Foundations.DavisCh2` · `Foundations.DavisCh2StrongMarkov`
