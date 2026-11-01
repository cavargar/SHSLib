/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General stochastic hybrid systems (Bujorianu–Lygeros 2006) in the
# categorical organization

* `Bujorianu2006.GSHS.genPres H` — the generator presentation of a GSHS `H`
  on the closed hybrid space `X̄`, with Eq. (28) as generator; test functions
  are twice-differentiable mode families (Condition 1 of Theorem 2) whose
  post-jump values are integrable for the reset kernel.
* `Bujorianu2006.GSHS.levyData H` and the isomorphism
  `Bujorianu2006.GSHS.levyIso H : genPres H ≅ (levyData H).toGenPres` — the GSHS
  generator is a Lévy-system generator whose jump targets live in the open
  hybrid space `X` and land in `X̄` through the inclusion `X ↪ X̄`.  So the GSHS,
  Hespanha's SHS (`SHS.levyIso`) and Davis PDPs (`Davis.genPres`, by definition)
  are all Lévy presentations, and Bect's bridge
  `LevyData.weakDynkin_of_satisfiesDynkin` applies uniformly to all three.
* `Bujorianu2006.GSHS.domainPres H` — the restriction to the test functions
  satisfying the boundary condition of Theorem 2; on the boundary its generator
  reduces to the continuous part (`domainPres_gen_of_frontier`).
-/
import SHSLib.Category.Levy
import SHSLib.Bujorianu2006.Generator

open CategoryTheory MeasureTheory Set Filter ProbabilityTheory

noncomputable section

namespace Bujorianu2006

namespace GSHS

open SHSCat HybridStateSpace

variable (H : GSHS)

/-- A test function of the GSHS generator: a twice differentiable family of
mode functions whose post-jump values are integrable for the reset kernel. -/
structure GenTest : Type where
  /-- The mode functions `f^i : ℝ^{d(i)} → ℝ`. -/
  F : ∀ i : H.Q, ModeSpace (H.d i) → ℝ
  twiceDifferentiable : H.TwiceDifferentiable F
  integrable : ∀ x : Cl H.toHybridStateSpace,
    Integrable (fun y => H.hybFun F (H.incl y)) (H.R x)

/-- **The generator presentation of a GSHS** (Eq. (28)). -/
def genPres : GenPres.{0} where
  State := Cl H.toHybridStateSpace
  Test := GenTest H
  ev := fun φ => H.hybFun φ.F
  gen := fun φ => H.gen φ.F

/-- The Lévy-system data of a GSHS: drift = continuous part (29), rate `λ`,
post-jump law `R(x, ·)` on `X`, landing by the inclusion `X ↪ X̄`. -/
def levyData : LevyData.{0} where
  State := Cl H.toHybridStateSpace
  Jump := Hyb H.toHybridStateSpace
  instJump := inferInstance
  Test := GenTest H
  ev := fun φ => H.hybFun φ.F
  drift := fun φ => H.contGen φ.F
  rate := H.lam
  jump := fun x => H.R x
  land := fun _ y => H.incl y

/-- The GSHS generator (28) is the Lévy-system generator. -/
theorem gen_eq_levyData_gen (φ : GenTest H) (x : Cl H.toHybridStateSpace) :
    H.gen φ.F x = (levyData H).gen φ x := by
  haveI := H.isMarkovKernel_R
  simp only [gen, jumpGen, jumpPart, LevyData.gen, LevyData.jumpTerm, levyData]
  rw [integral_sub (φ.integrable x) (integrable_const _)]
  simp

/-- **The GSHS presentation is isomorphic to its Lévy-system form.** -/
def levyIso : genPres H ≅ (levyData H).toGenPres where
  hom :=
    { map := fun x => x
      pull := fun φ => φ
      ev_pull := fun _ _ => rfl
      gen_pull := fun φ x => gen_eq_levyData_gen H φ x }
  inv :=
    { map := fun x => x
      pull := fun φ => φ
      ev_pull := fun _ _ => rfl
      gen_pull := fun φ x => (gen_eq_levyData_gen H φ x).symm }

/-- The test functions in the domain of Theorem 2: those also satisfying the
boundary condition `f = Rf` on `∂X`. -/
def DomainTest : Type := {φ : GenTest H // H.BoundaryCondition φ.F}

/-- The GSHS presentation restricted to the domain of Theorem 2. -/
def domainPres : GenPres.{0} := (genPres H).restrict (fun φ : DomainTest H => φ.1)

/-- The inclusion of the domain of Theorem 2, as a morphism of presentations. -/
def toDomainPres : genPres H ⟶ domainPres H :=
  (genPres H).toRestrict (fun φ : DomainTest H => φ.1)

/-- On the boundary, the generator of the domain presentation is the continuous
part only (the step "`I₂` vanishes" in the proof of Theorem 2). -/
theorem domainPres_gen_of_frontier (φ : DomainTest H) (x : Cl H.toHybridStateSpace)
    (hx : (x.2 : ModeSpace (H.d x.1)) ∈ frontier (H.X x.1)) :
    (domainPres H).gen φ x = H.contGen φ.1.F x :=
  H.gen_eq_contGen_of_boundary φ.1.F φ.2 x hx (φ.1.integrable x)

end GSHS

end Bujorianu2006
