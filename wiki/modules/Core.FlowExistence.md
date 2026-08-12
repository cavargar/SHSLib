# Module group: Flow existence and regularity

**Files:** 13 modules under `SHSLib/Core/`
**Layer:** Core
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `6cbbd3ec`, adopted 2026-08-12

`SHS.HasGlobalFlow` is an *assumption* in Hespanha's development: the ODE
$\dot{x} = f(q,x,t)$ is taken to have a global solution between jumps. This group
discharges that assumption from checkable hypotheses on the drift, and then upgrades
the flow's integral form to the differential and Dynkin forms.

| Module | Contents |
|--------|----------|
| `GlobalFlowExistence` | Global existence and uniqueness of the flow for a Lipschitz drift |
| `GlobalFlowLinearGrowth` | The same under local Lipschitz continuity plus linear growth |
| `GlobalFlowVaryingGrowth` | Linear growth with time-varying coefficients |
| `LinearGrowthCriteria` | Convenient sufficient conditions for the linear-growth hypotheses |
| `FlowRegularity` | Regularity of the flow for a Lipschitz drift |
| `FlowRegularityLinearGrowth` | Regularity when the drift is only locally Lipschitz |
| `FlowInitialStateDependence` | Dependence of the flow on the initial state |
| `EnvelopeIntensityBounds` | Discharging the hypotheses of Lemma 2 from a growth envelope |
| `EnvelopeSharpness` | Sharpness of the linear-growth envelope |
| `ExplicitFlows` | Closed-form flows for the two simplest drifts |
| `FlowDynkin` | The deterministic (jump-free) Dynkin identity along the flow, from the integral form plus the chain rule |
| `DavisTransitionFree` | Theorem 1 for an SHS with no transition channels — every Davis data bundle constructed, no assumptions left standing |
| `DavisModeBlind` | Theorem 1 for systems whose resets only relabel the discrete mode, so the sample path genuinely jumps |

## Why it matters

`DavisTransitionFree` and `DavisModeBlind` inhabit every hypothesis bundle of
`SHS.theorem1_generator_formula`, which is what shows that theorem is not vacuous:
there exist systems — including jumping ones — for which all of its Davis-level
hypotheses hold simultaneously.

Counterexample: `Examples.QuadraticBlowUp` (research repository) exhibits a drift
without linear growth whose flow escapes in finite time, showing the growth
hypothesis cannot simply be dropped.

## Related

`Core.Generator` · `Core.GronwallGrowthBound` · `Core.DavisBridge`
