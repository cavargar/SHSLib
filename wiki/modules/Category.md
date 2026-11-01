# Module: SHSLib.Category

**File:** `SHSLib/Category.lean` (index and correspondence table) + `SHSLib/Category/*.lean` (10 modules)
**Layer:** Category — cross-framework organization
**Status:** ✅ Complete (0 sorries, standard axioms only)
**Origin:** Aristotle project `42dd2dce`; `ItoDiffusion` written by hand

## What it proves

This layer connects the five SHS frameworks of the library through one category, `SHSCat.GenPres`, of **generator presentations**.

- **Object:** a state type, a type of test functions, and two maps from tests to functions on states, an evaluation `ev` and a generator `gen`.
- **Morphism (intertwiner):** a state map together with a pull-back of test functions that commutes with both `ev` and `gen`. Formally this is a Chu-space morphism over `ℝ × ℝ`.

Three process-level properties transfer along every morphism and are invariant under isomorphism:
- `SatisfiesDynkin`: Dynkin's formula in expectation
- `SatisfiesForward`: the forward equation in right-derivative form
- `SolvesMartingaleProblem`: the martingale problem

Each framework enters as objects and arrows of `GenPres`:
- Transition semigroups and Davis PDP conjugacies map in through functors.
- Hespanha's SHS and the Bujorianu–Lygeros GSHS are each isomorphic to Bect's Lévy-system form.
- A compatible Davis PDP maps to its SHS.
- Gardiner/Ullah kernel semigroups map to the dCKE presentation.

Composing these arrows produces cross-framework results. In particular, Bect's generalized Dynkin formula (13) follows for a GSHS that satisfies Dynkin's formula.

Generator presentations were chosen over Markov kernels because the Hespanha, Bect and GSHS frameworks come with generators but no constructed semigroups.

## Key theorems

| Theorem | Statement (informal) |
|---------|----------------------|
| `SHSCat.GenPres.SatisfiesDynkin.map` (+ `SatisfiesForward.map`, `SolvesMartingaleProblem.map`) | A property of a process for `A` holds for its push-forward along any morphism `A ⟶ B` |
| `SHSCat.GenPres.satisfiesDynkin_iso_iff` (+ forward, martingale) | The three properties are invariant under isomorphism |
| `SHSCat.SemigroupSys.strongGenerator` | Functor from transition semigroups (Bujorianu §3.2) to `GenPres` |
| `SHSCat.LevyData.weakDynkin_of_satisfiesDynkin` | Dynkin's formula for a Lévy-form presentation gives Bect's (13), the hypothesis of his Theorem 8 |
| `Davis.PDPSys.toGenPresFunctor`, `Davis.finiteSemigroupSys` | Functor from Davis PDP conjugacies; a finite Davis PDP as a semigroup object |
| `SHS.levyIso` | Hespanha SHS ≅ its Lévy form (Bect Example 18) |
| `SHS.DavisCompatible.hom` | Morphism from a compatible Davis PDP to the SHS presentation |
| `SHS.realization_satisfiesDynkin`, `SHS.realization_weakDynkin` | Hespanha Thm 2 for a Davis realization; Bect (13) for time-dependent SHS tests |
| `SHS.isFlowDerivative_of_hasPartials`, `SHS.toClassicalPres`, `SHS.satisfiesDynkin_classical` | Classical C¹ test functions belong to the generator domain, given right-continuity of the drift; Dynkin transfers to all of them |
| `Bujorianu2006.GSHS.levyIso`, `Bujorianu2006.GSHS.weakDynkin_of_satisfiesDynkin` | GSHS ≅ Lévy form; Dynkin for a GSHS gives Bect (13) |
| `Gardiner.hasStrongGenerator_of_kernel`, `Gardiner.GardinerKernel.hom`, `GardinerKernel.ofUllah` | The strong generator of a kernel semigroup meeting Gardiner's conditions is the dCKE operator; the same bridge can be built from Ullah's conditions |
| `SHS.DavisCompatible.weakDynkin` | Composite Davis ⟶ SHS ⟶ Lévy: Dynkin for a compatible PDP gives Bect (13) |

## Depends on

- [[Core.DavisBridge]], [[Core.DavisMartingale]], `Core.FlowDynkin`, [[Foundations.DavisCh2FiniteProcess]], `FPK.HespanhaBridge`, `FPK.DynkinFormula` ([[FPK]]), `Bujorianu2006.Generator`, `Bujorianu2006.Martingale` ([[Bujorianu2006]]), `Gardiner.Backward`, `Gardiner.Strong` ([[Gardiner]]), `Gardiner.Ito.SDEBridge` ([[Gardiner.Ito]]), `Ullah.DCKE` ([[Ullah]]), Mathlib

## Used by

- No other layer of the public library imports `Category`; it sits on top of the others.
- `Category/ItoDiffusion.lean` builds on `GenPres` for Itô diffusions (see the section below). `Gardiner.Ito.SDEBridge` points to it for the categorical form of the martingale problem.

## Open gaps / sorries

None. Caveats:
- **The transfers are conditional.** Most cross-framework theorems take Dynkin's formula for the source process as a hypothesis. This applies to the GSHS, Davis-compatible and Gardiner-kernel transfers, and to `satisfiesDynkin_classical`. The library does not yet prove Dynkin's formula for a general GSHS, a compatible Davis PDP or a kernel semigroup. `SHS.realization_satisfiesDynkin` derives it from Hespanha Thm 2.
- **Integrability is not built in.** `SatisfiesDynkin` and `SatisfiesForward` use the Bochner integral with no integrability hypothesis. Non-integrable expectations evaluate to 0 in Lean, so the properties are weaker than the textbook statements when the expectations do not exist.
- **Open directions:**
  - a strong- vs extended-generator morphism for Davis
  - a kernel-level functor into the Kleisli category of the Giry monad
  - forward equations at the level of laws
  - a Markov-string semigroup for GSHS

## Itô diffusions

`SHSLib/Category/ItoDiffusion.lean` adds horizon-`T` versions `GenPres.SolvesMartingaleProblemOn` and `GenPres.SatisfiesDynkinOn` (with `satisfiesDynkin_iff_forall_on`) next to the existing predicates, which are unchanged. It defines the generator presentation `SHSCat.ItoDiffusion.genPres a b` of `dx = a(x)dt + b(x)dW` (tests: `C²` with bounded derivatives), and transfers the martingale problem and Dynkin's formula for Lipschitz SDE solutions (`Gardiner.Ito.Generator`) to it. Instances: the standard Wiener process (martingale problem up to every `T`, Dynkin on `[0,∞)`), and `dx = −sin x dt + σ dW` (Dynkin up to `T`). See [[Gardiner.Ito]].
