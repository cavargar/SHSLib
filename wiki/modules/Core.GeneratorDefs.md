# Module: SHSLib.Core.GeneratorDefs

**File:** `SHSLib/Core/GeneratorDefs.lean`
**Layer:** Core
**Status:** ✅ Complete

## What it proves

Definition-only module holding `SHS.TestFunction` and `SHS.extendedGenerator`
(Hespanha Eq. 9), extracted from [[Core.Generator]] so that both the Davis
construction ([[Core.DavisBridge]]) and the generator theorems can share them
without an import cycle. No theorems — purely the shared definitions.

## Key definitions

| Definition | Description |
|------------|-------------|
| `SHS.TestFunction` | Test function `ψ(q,x,t)` with fields `toFun`, `grad_x` (∂ψ/∂x), `partial_t` (∂ψ/∂t) |
| `SHS.extendedGenerator` | The SHS extended generator `(Lψ)(q,x,t) = ⟨∇ψ,f⟩ + ∂ψ/∂t + Σ_ℓ (ψ∘φ_ℓ − ψ)·λ_ℓ` |

## Depends on

- [[Core.Basic]], Mathlib

## Used by

- [[Core.Generator]], [[Core.DavisBridge]]

## Open gaps / sorries

None.

## Notes

Pure refactor introduced by the Davis-to-SHS bridge (Aristotle `6cbbd3ec`): the
definitions were moved verbatim from `Core/Generator.lean`. `TestFunction`'s
derivative fields are independent (nothing forces them to be the actual
derivatives of `toFun`); C¹/C² regularity is imposed downstream where needed
(e.g. `SHS.TestFunctionC2` in [[Core.Generator]]).
