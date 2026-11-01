/-
# Category-theoretic organization of SHSLib

Design document: `research/docs/plans/plan_category_theory.md`.

The five frameworks of the library are related through one category,
`SHSCat.GenPres`, of **generator presentations** (state space, test functions,
evaluation, generator) and **intertwiners** (state map + test-function pull-back
commuting with evaluation and generator).  Process-level results
(`SatisfiesDynkin`, `SatisfiesForward`, `SolvesMartingaleProblem`) transfer along
every morphism and are invariant under isomorphism.

| Framework / bridge                         | Lean                                                    |
| ------------------------------------------ | ------------------------------------------------------- |
| hub category, transfer theorems            | `SHSCat.GenPres`, `SHSCat.GenPres.SatisfiesDynkin.map`  |
| transition semigroups (Bujorianu §3.2)     | `SHSCat.SemigroupSys`, `SemigroupSys.strongGenerator`   |
| Lévy-system form (Bect §2.3, Eqs. (4)–(6)) | `SHSCat.LevyData`, `LevyData.toGenPres`                 |
| Lévy form ⟹ Bect (13) / Theorem 8          | `SHSCat.LevyData.weakDynkin_of_satisfiesDynkin`         |
| Davis PDP (26.15)                          | `Davis.genPres`, `Davis.PDPSys.toGenPresFunctor`        |
| Davis finite semigroup as semigroup object | `Davis.finiteSemigroupSys`, `Davis.finite_pdpSemigroup_dynkin` |
| Hespanha SHS (Eq. 9)                       | `SHS.presOn`, `SHS.genPres`                             |
| Hespanha = Lévy (Bect Example 18)          | `SHS.levyIso`                                           |
| classical C¹ tests in the SHS domain       | `SHS.isFlowDerivative_of_hasPartials`, `SHS.toClassicalPres` |
| SHS as time-augmented Davis PDP            | `SHS.DavisCompatible.hom`                               |
| Hespanha Thm. 2 for a Davis realization    | `SHS.realization_satisfiesDynkin`, `SHS.realization_weakDynkin` |
| GSHS (Bujorianu–Lygeros Eq. (28))          | `Bujorianu2006.GSHS.genPres`, `Bujorianu2006.GSHS.levyIso` |
| dCKE (Gardiner §3.4/3.6, Ullah §8.2)       | `Gardiner.dckePres`, `Gardiner.GardinerKernel.hom`      |
| Ullah's conditions = Gardiner's            | `Gardiner.GardinerKernel.ofUllah`, `Ullah.fpTerm_add_jumpTerm` |
| composite transfers                        | `SHS.DavisCompatible.weakDynkin`, `Bujorianu2006.GSHS.weakDynkin_of_satisfiesDynkin` |
-/
import SHSLib.Category.GenPres
import SHSLib.Category.Semigroup
import SHSLib.Category.Levy
import SHSLib.Category.Davis
import SHSLib.Category.Hespanha
import SHSLib.Category.HespanhaRegular
import SHSLib.Category.Bujorianu
import SHSLib.Category.DCKE
import SHSLib.Category.Diagram
