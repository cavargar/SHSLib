# Module: SHSLib.Core.DavisConstruction

**File:** `SHSLib/Core/DavisConstruction.lean`
**Layer:** Core
**Status:** ✅ Complete

## What it proves

Builds the concrete homogeneous time-augmented Davis PDP of an SHS and proves it
is `DavisCompatible` ([[Core.DavisBridge]]). Isolates the regularity not already
in `SHS.HasGlobalFlow` (measurable flow + composition law, measurable resets, a
measurable non-self fallback used only where total intensity vanishes),
constructs the marked reset kernel, and proves it is Markov with correct
integral behaviour. `sorry`-free, standard axioms.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `markedResetKernel_isMarkov` | The marked reset kernel is a Markov kernel |
| `markedResetKernel_no_self_jump` | Resets never map a state to itself |
| `markedResetKernel_weighted_integral` | Intensity-weighted integral against the reset kernel |
| `markedResetMeasure_measurable` | Measurability of the reset measure |
| `toDavisPDP_compatible` / `toDavisPDPStandard_compatible` | The constructed PDP (standard PDP) is `DavisCompatible` with the SHS |

## Key definitions

| Definition | Description |
|------------|-------------|
| `davisFlow` / `DavisFlowRegular` | Time-augmented flow and its regularity bundle |
| `davisJumpRate` / `zeroIntensityFallback` / `DavisResetRegular` | Jump rate, degenerate fallback, reset regularity |
| `markedResetMeasure` / `markedResetKernel` | Marked reset measure/kernel |
| `toDavisPDP` / `toDavisPDPStandard` | The assembled (standard) Davis PDP |
| `DavisLocallyIntegrable` / `DavisNonExplosive` | Non-explosion / integrability side-conditions |

## Depends on

- [[Core.DavisBridge]], Mathlib

## Used by

- [[Core.DavisMartingale]]

## Open gaps / sorries

None.

## Notes

Introduced by the Davis-to-SHS bridge (Aristotle `6cbbd3ec`). See
`docs/analyses/davis_shs_bridge.md`.
