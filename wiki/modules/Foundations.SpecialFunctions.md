# Module group: Special functions

**Files:** 51 modules under `SHSLib/Foundations/`
**Layer:** Foundations
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `6cbbd3ec`, adopted 2026-08-07

A special-functions layer with no prior counterpart in SHSLib. It exists to
support Beta-distributed division partitioning
(`Examples.BetaPartitioning`) and interval estimation for cell-cycle data.

| Family | Count | Contents |
|--------|-------|----------|
| `Stirling*` | 18 | Stirling's formula and constant; Binet's first/second/third integrals; Wallis product; Gautschi's inequality; central binomial and Catalan asymptotics; half-integer and shift/ratio forms; log-Gamma bounds; `StirlingBeta*` asymptotics, integral and reflection |
| `Beta*` | 13 | Beta distribution, measure and density; expectation, variance, recurrence; quantile, quantile function and its continuity; inverse-transform sampling; Beta–binomial and its measure; concentration; power law |
| Polygamma family | 12 | `Digamma` (+ Euler, reflection, asymptotics, sharp bounds), `Trigamma` (+ series, sharp bracket), `Tetragamma` (+ reflection), `Polygamma` (+ asymptotics) |
| `ClopperPearson*` | 3 | Clopper–Pearson exact binomial intervals; coverage; monotonicity |
| `UniformOrderStatistic*` | 3 | Uniform order statistics: the law, one-dimensional marginals, moments |
| Other | 2 | `IncompleteBeta`, `OrderStatisticTransform` |

## Related

`Examples.BetaPartitioning` · `Examples.BetaPartitioningLinearGrowth` ·
`Examples.CellSizeHomeostasis`
