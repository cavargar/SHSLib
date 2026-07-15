# Module: SHSLib.Core.DavisBridge

**File:** `SHSLib/Core/DavisBridge.lean`
**Layer:** Core
**Status:** ✅ Complete

## What it proves

The compatibility layer connecting a Hespanha SHS to a Davis PDMP. Since the SHS
is time-inhomogeneous and `Davis.PDP` is homogeneous, the connection is made on
the **time-augmented state** `(q, x, t)`. Records the data a concrete PDP must
supply (`DavisCompatible`) and proves the Davis generator then agrees with
[[Core.GeneratorDefs]]'s `SHS.extendedGenerator`. `sorry`-free, standard axioms.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `DavisCompatible.pdpGenerator_eq_extendedGenerator` | Davis PDP generator `𝔄f = 𝔛f + λ(Qf−f)` equals `SHS.extendedGenerator` on the augmented state |
| `DavisCompatible.jumpRate_eq_sum` | Davis jump rate equals `Σ_ℓ λ_ℓ` |
| `DavisCompatible.pdpGenerator_along_process` / `_toDavisProcess` | The generator identity evaluated along the (augmented) process |
| `totalIntensity_nonneg` | Total transition intensity `Σ_ℓ λ_ℓ ≥ 0` |

## Key definitions

| Definition | Description |
|------------|-------------|
| `InitialCondition.toDavisState` / `TestFunction.toDavisFunction` / `toDavisProcess` | Time-augmentation maps SHS ↦ Davis |
| `flowGenerator` / `totalIntensity` / `resetDavisState` | Davis local characteristics from SHS data |
| `DavisCompatible` | Bundle of facts a concrete PDP must satisfy to match the SHS |

## Depends on

- [[Core.GeneratorDefs]], [[Foundations.DavisCh2]], Mathlib

## Used by

- [[Core.DavisConstruction]]

## Open gaps / sorries

None.

## Notes

Introduced by the Davis-to-SHS bridge (Aristotle `6cbbd3ec`). See
`docs/analyses/davis_shs_bridge.md` for the full narrative.
