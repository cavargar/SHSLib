# Module group: Beta order statistics

**Files:** 6 modules under `SHSLib/Foundations/`
**Layer:** Foundations
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `6cbbd3ec`, adopted 2026-08-12

Moments and concentration for the $(j{+}1)$-st order statistic of a sample of $n = j+m+1$
independent draws from a Beta law. Builds on the `Beta*` and `UniformOrderStatistic*`
families of [Foundations.SpecialFunctions](Foundations.SpecialFunctions.md), in
particular `map_orderStat` (the law of a uniform order statistic *is* a Beta measure)
and `map_orderStat_betaSample`.

| Module | Contents |
|--------|----------|
| `BetaOrderStatisticMoments` | Reflected fractional moments $E[(1-X)^s] = B(a,b+s)/B(a,b)$, and from them the mean, second moment and variance of the order statistic of a $\mathrm{Beta}(1,b)$ sample, as ratios of Beta functions |
| `BetaOrderStatisticMomentsPower` | The same for the other elementary parent family $\mathrm{Beta}(a,1)$, with quantile $p \mapsto p^{1/a}$, where the direct rather than reflected moments appear |
| `BetaOrderStatisticConcentration` | Chebyshev concentration for the order statistic of an arbitrary Beta sample, with square-integrability proved from scratch |
| `BetaOrderStatisticInteger` | At an integer exponent the Beta-function ratios collapse to a finite product of rationals, bracketed between the parent quantile at two rank fractions |
| `BetaOrderStatisticLipschitz` | A variance bound $\mathrm{Var} \le k^2/(4(n+2))$ from a $k$-Lipschitz parent quantile, and the resulting localization |
| `BetaOrderStatisticGeneralLipschitz` | The same for an arbitrary Beta parent with an $L$-Lipschitz quantile; the power case is the instance $L = k$ |

These are the first Lipschitz-type results in the Beta layer.

## Sanity checks carried in the modules

The mean formula is checked against two known cases: at $b = 1$ it returns the
classical uniform value $(j{+}1)/(n{+}1)$, and at $j = 0$ it returns $1/(nb+1)$, the
mean of the $\mathrm{Beta}(1, nb)$ minimum. The two parent families are checked to
agree at the uniform law.

## Related

`Foundations.SpecialFunctions`
