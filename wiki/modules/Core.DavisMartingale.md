# Module: SHSLib.Core.DavisMartingale

**File:** `SHSLib/Core/DavisMartingale.lean`
**Layer:** Core
**Status:** ✅ Complete

## What it proves

The process-level payoff of the Davis-to-SHS bridge: from a
`DavisProcessRealization` (a probability space, an adapted coordinate process,
and the compensated jump-measure result), derives that the compensated generator
process is a true martingale and proves Hespanha **Theorem 2**
(`E[ψ] = ψ₀ + E[∫ Lψ]`) for the constructed process. `sorry`-free, standard
axioms.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `toDavisPDPStandard_compensated_martingale` | The compensated generator process is a true martingale |
| `theorem2_PDP_generator` | Hespanha Thm 2 (elapsed-time form): `E[ψ(X_t)] = ψ₀ + E[∫ Lψ ds]` |
| `theorem2_PDP_generator_absolute` | Same in absolute-time coordinates |
| `integral_Icc_elapsed_to_absolute` | Converts elapsed-time integrals to absolute-time |
| `DavisTrueMartingaleData.compensated_integrable` | Integrability of the compensated process |

## Key definitions

| Definition | Description |
|------------|-------------|
| `DavisProcessRealization` | Probability space + adapted process + compensated jump-measure data |
| `DavisCompensatorData` / `DavisTrueMartingaleData` | The primitive probabilistic input (Davis 26.7/26.12) as realization data |
| `qProc` / `xProc` / `timeProc` / `qProcAbsolute` / `xProcAbsolute` | Coordinate projections of the realization |

## Depends on

- [[Core.DavisConstruction]], Mathlib

## Used by

- [[Core.Generator]] (re-exports `theorem2_PDP_generator` as `SHS.theorem2_PDP_generator_of_martingale`)

## Open gaps / sorries

None.

## Notes

The genuine probabilistic content (compensated jump measure is a martingale)
enters as realization data rather than being rebuilt from a counting-measure
construction — faithful to Davis's own decomposition (flow part via
`deterministic_dynkin`, jump part via the compensator theorem). Introduced by
the Davis-to-SHS bridge (Aristotle `6cbbd3ec`); see
`docs/analyses/davis_shs_bridge.md`.
