/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The diagram of frameworks, and results transferred along its paths

The framework files provide objects and arrows of `GenPres`:

```
  PDPSys ──toGenPresFunctor──▶ GenPres ◀──strongGenerator── SemigroupSys
                                  ▲                           ▲      ▲
   Davis.genPres pdp ──DavisCompatible.hom──▶ SHS.genPres     │      │
                                                 │≅ levyIso   │  finiteSemigroupSys
                                                 ▼            │   (Davis, finite E)
   Bujorianu2006.GSHS.genPres ──≅ levyIso──▶ LevyData.toGenPres
                                                 │
                                                 ▼ weakDynkin_of_satisfiesDynkin
                                       Bect: FPKData.WeakDynkin ⟹ Theorem 8
   strongGenerator.obj ⟨ℝⁿ, S⟩ ──GardinerKernel.hom──▶ Gardiner.dckePres
```

This file composes these arrows and records the resulting cross-framework
transfer theorems:

* `SHS.DavisCompatible.toLevy` — Davis ⟶ SHS ⟶ Lévy (composite morphism);
* `SHS.DavisCompatible.solvesMartingaleProblem_levy` — a solution of the Davis
  martingale problem solves the martingale problem of the SHS in Lévy form;
* `SHS.DavisCompatible.weakDynkin` — Dynkin's formula for a compatible Davis
  PDP yields Bect's generalized Dynkin formula (13) for the SHS;
* `Bujorianu2006.GSHS.weakDynkin_of_satisfiesDynkin` — Dynkin's formula for a
  GSHS yields Bect's (13) on the closed hybrid space;
* `Gardiner.GardinerKernel.satisfiesDynkin` — Dynkin's formula for the strong
  generator of a kernel semigroup yields Dynkin's formula for the dCKE operator.
-/
import SHSLib.Category.Hespanha
import SHSLib.Category.Bujorianu
import SHSLib.Category.DCKE

open CategoryTheory MeasureTheory Set Filter
open scoped ENNReal

universe u

noncomputable section

namespace SHS

open SHSCat

variable {Q : Type u} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}
  {S : SHS Q n m} {hflow : S.HasGlobalFlow} {pdp : Davis.PDP (DavisState Q n)}

/-- The composite **Davis ⟶ SHS ⟶ Lévy** morphism for a compatible PDP. -/
def DavisCompatible.toLevy (h : S.DavisCompatible hflow pdp) :
    Davis.genPres pdp ⟶ (S.levyDataOn (GenTest.toTestFunction (S := S) (hflow := hflow))).toGenPres :=
  h.hom ≫ (S.levyIso (GenTest.toTestFunction (S := S) (hflow := hflow))).hom

/-- **Martingale problems transfer from Davis to the Lévy form of the SHS.** -/
theorem DavisCompatible.solvesMartingaleProblem_levy (h : S.DavisCompatible hflow pdp)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℝ ‹_›}
    {X : ℝ → Ω → DavisState Q n}
    (hX : (Davis.genPres pdp).SolvesMartingaleProblem P ℱ X) :
    (S.levyDataOn (GenTest.toTestFunction (S := S) (hflow := hflow))).toGenPres.SolvesMartingaleProblem
      P ℱ X :=
  hX.map h.toLevy

/-- **Cross-framework transfer: Davis ⟹ Bect.**  If a jointly measurable
process satisfies Dynkin's formula for a Davis PDP compatible with the SHS
(e.g. by Davis's Theorem 26.14), then Bect's generalized Dynkin formula (13)
— the hypothesis of Theorem 8 — holds for the laws of the process, for any
Bect data `D` on the augmented state built on the SHS test functions with the
SHS drift, reset kernel and mean jump intensity `λ μ_s`. -/
theorem DavisCompatible.weakDynkin (h : S.DavisCompatible hflow pdp)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ → Ω → DavisState Q n} (hXm : Measurable (Function.uncurry X))
    (hX : (Davis.genPres pdp).SatisfiesDynkin P X)
    (D : GSHS.FPKData (DavisState Q n) (S.GenTest hflow))
    (hev : D.ev = fun ψ => ψ.toTestFunction.toDavisFunction)
    (hdrift : D.gen = fun ψ => S.flowGenerator ψ.toTestFunction)
    (hK : ∀ (ψ : S.GenTest hflow) (z : DavisState Q n),
      ∫ y, ψ.toTestFunction.toDavisFunction y ∂(D.K z)
        = ∫ y, ψ.toTestFunction.toFun y.1 y.2 z.2.2 ∂(S.resetKernel z.1 z.2.1 z.2.2))
    (hlaw : ∀ s : ℝ, 0 ≤ s → P.map (X s) = D.law s)
    {genBound : S.GenTest hflow → ℝ}
    (hgen_le : ∀ ψ z, |S.flowGenerator ψ.toTestFunction z| ≤ genBound ψ)
    (hdrift_meas : ∀ ψ : S.GenTest hflow, Measurable (S.flowGenerator ψ.toTestFunction))
    (hrate_meas : Measurable S.totalIntensity)
    {rateBound : ℝ} (hrate_le : ∀ z, S.totalIntensity z ≤ rateBound)
    (hrD : ∀ s : ℝ, D.r s = (D.law s).withDensity fun z => ENNReal.ofReal (S.totalIntensity z)) :
    D.WeakDynkin := by
  letI : MeasurableSpace
      (S.levyDataOn (GenTest.toTestFunction (S := S) (hflow := hflow))).State :=
    inferInstanceAs (MeasurableSpace (DavisState Q n))
  exact (S.levyDataOn (GenTest.toTestFunction (S := S) (hflow := hflow))).weakDynkin_of_satisfiesDynkin
    D hXm (hX.map h.toLevy) hev hdrift hK hlaw hgen_le hdrift_meas hrate_meas
    S.totalIntensity_nonneg hrate_le hrD

end SHS

namespace Bujorianu2006.GSHS

open SHSCat HybridStateSpace

variable (H : GSHS)

/-- **Cross-framework transfer: Bujorianu–Lygeros ⟹ Bect.**  Dynkin's formula
for the GSHS generator (28) yields Bect's generalized Dynkin formula (13) on the
closed hybrid space, for Bect data `D` built on the GSHS test functions, with the
continuous part (29) as drift, a Markov kernel on `X̄` with the averages of the
reset kernel `R` (`hK`), and mean jump intensity `λ μ_s`. -/
theorem weakDynkin_of_satisfiesDynkin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ → Ω → Cl H.toHybridStateSpace} (hXm : Measurable (Function.uncurry X))
    (hX : (genPres H).SatisfiesDynkin P X)
    (D : _root_.GSHS.FPKData (Cl H.toHybridStateSpace) (GenTest H))
    (hev : D.ev = fun φ => H.hybFun φ.F) (hdrift : D.gen = fun φ => H.contGen φ.F)
    (hK : ∀ (φ : GenTest H) (x : Cl H.toHybridStateSpace),
      ∫ y, H.hybFun φ.F y ∂(D.K x) = ∫ y, H.hybFun φ.F (H.incl y) ∂(H.R x))
    (hlaw : ∀ s : ℝ, 0 ≤ s → P.map (X s) = D.law s)
    {genBound : GenTest H → ℝ} (hgen_le : ∀ φ x, |H.contGen φ.F x| ≤ genBound φ)
    (hdrift_meas : ∀ φ : GenTest H, Measurable (H.contGen φ.F))
    (hlam : H.DiscreteTransitions) {rateBound : ℝ} (hlam_le : ∀ x, H.lam x ≤ rateBound)
    (hrD : ∀ s : ℝ, D.r s = (D.law s).withDensity fun x => ENNReal.ofReal (H.lam x)) :
    D.WeakDynkin := by
  letI : MeasurableSpace (levyData H).State :=
    inferInstanceAs (MeasurableSpace (Cl H.toHybridStateSpace))
  exact (levyData H).weakDynkin_of_satisfiesDynkin D hXm (hX.map (levyIso H).hom) hev hdrift
    hK hlaw hgen_le hdrift_meas hlam.measurable_lam hlam.nonneg_lam hlam_le hrD

end Bujorianu2006.GSHS

namespace Gardiner

open SHSCat

variable {n : ℕ}

/-- **Transfer along the Gardiner bridge**: a process satisfying Dynkin's
formula for the strong generator of a kernel semigroup satisfying Gardiner's
hypotheses satisfies Dynkin's formula for the dCKE operator. -/
theorem GardinerKernel.satisfiesDynkin {S : Bujorianu2006.TransitionSemigroup (Sp n)}
    {k : ℝ → Sp n → Sp n → ℝ} {A : Sp n → Fin n → ℝ} {B : Sp n → Fin n → Fin n → ℝ}
    {W : Sp n → Sp n → ℝ} (h : GardinerKernel S k A B W)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ → Ω → Sp n}
    (hX : (SemigroupSys.strongGenerator.obj (⟨Sp n, S⟩ : SemigroupSys.{0})).SatisfiesDynkin P X) :
    (dckePres A B W).SatisfiesDynkin P X :=
  hX.map h.hom

end Gardiner
