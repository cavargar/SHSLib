/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lévy-system presentations: the common shape of the hybrid generators

Davis's PDP generator (26.15), Hespanha's SHS generator (Eq. 9, in the form of
Bect's Example 18), and the GSHS generator (28) of Bujorianu–Lygeros all have the
shape of Bect's Lévy-system generator (Eqs. (4)–(6) of Bect 2010):

  `Lφ(x) = (drift part)φ(x) + λ(x) · (∫ φ(ℓ_x(y)) J(x, dy) − φ(x))`

where `λ` is the total jump intensity, `J(x, ·)` the post-jump law (on a space
of *jump targets*), and `ℓ_x` *lands* a jump target in the state space (the
identity for Davis, the inclusion `X ↪ X̄` for a GSHS, and "keep the clock" on
the time-augmented state of an SHS).

A `LevyData` packages these ingredients; `LevyData.toGenPres` is the
corresponding generator presentation.  The framework files prove that each
framework's native presentation is *isomorphic* (or equal) to its Lévy form.

The Lévy form is also what connects to Bect's measure-valued theory:
`LevyData.weakDynkin_of_satisfiesDynkin` turns Dynkin's formula for the
presentation (a `GenPres` property, hence transportable along morphisms) into
the hypothesis `WeakDynkin` of Bect's Theorem 8, via
`GSHS.FPKData.weakDynkin_of_dynkin12`.
-/
import SHSLib.Category.GenPres
import SHSLib.FPK.DynkinFormula

open CategoryTheory MeasureTheory Set Filter
open scoped ENNReal

universe u

noncomputable section

namespace SHSCat

/-- **Lévy-system data**: test functions with their drift (differential)
generator, a total jump intensity, a post-jump law on a space of jump targets,
and the landing map from jump targets to states. -/
structure LevyData : Type (u + 1) where
  /-- The state space. -/
  State : Type u
  /-- The space on which the post-jump law lives. -/
  Jump : Type u
  /-- The σ-algebra on jump targets. -/
  instJump : MeasurableSpace Jump
  /-- The test functions. -/
  Test : Type u
  /-- Evaluation of test functions. -/
  ev : Test → State → ℝ
  /-- The drift (differential) part of the generator. -/
  drift : Test → State → ℝ
  /-- The total jump intensity `λ`. -/
  rate : State → ℝ
  /-- The post-jump law `J(x, ·)`. -/
  jump : State → @Measure Jump instJump
  /-- Landing of a jump target from the pre-jump state `x`. -/
  land : State → Jump → State

attribute [instance] LevyData.instJump

namespace LevyData

variable (L : LevyData.{u})

/-- The jump part `λ(x) (∫ φ(ℓ_x y) J(x,dy) − φ(x))` of the generator. -/
def jumpTerm (φ : L.Test) (x : L.State) : ℝ :=
  L.rate x * ((∫ y, L.ev φ (L.land x y) ∂(L.jump x)) - L.ev φ x)

/-- The full Lévy-system generator `drift + λ (J − I)`. -/
def gen (φ : L.Test) (x : L.State) : ℝ :=
  L.drift φ x + L.jumpTerm φ x

/-- The generator presentation of Lévy-system data. -/
def toGenPres : GenPres.{u} where
  State := L.State
  Test := L.Test
  ev := L.ev
  gen := L.gen

@[simp] theorem toGenPres_ev : L.toGenPres.ev = L.ev := rfl

@[simp] theorem toGenPres_gen : L.toGenPres.gen = L.gen := rfl

/-- For a probability post-jump law and integrable test functions, the jump
part can be written in Bujorianu's form `λ(x) ∫ (φ(ℓ_x y) − φ(x)) J(x, dy)`. -/
theorem jumpTerm_eq_integral_sub (φ : L.Test) (x : L.State)
    [IsProbabilityMeasure (L.jump x)]
    (hint : Integrable (fun y => L.ev φ (L.land x y)) (L.jump x)) :
    L.jumpTerm φ x = L.rate x * ∫ y, (L.ev φ (L.land x y) - L.ev φ x) ∂(L.jump x) := by
  rw [jumpTerm, integral_sub hint (integrable_const _)]
  simp

/-! ### From Dynkin's formula to Bect's generalized Dynkin formula (13) -/

/-- **Bridge to Bect's measure-valued framework.**

Let `X` be a jointly measurable process whose laws are `D.law s`, for Bect data
`D` built on the same test functions as `L` (`hev`), with the drift part of
`L` as differential generator (`hdrift`), with a Markov kernel `D.K` having the
same test-function averages as the post-jump law of `L` (`hK`), and with mean
jump intensity `r_s = λ μ_s` (`hr`).  If `X` satisfies Dynkin's formula for the
Lévy presentation `L.toGenPres`, then `D` satisfies the generalized Dynkin
formula (13), the standing hypothesis of Theorem 8 of Bect (2010). -/
theorem weakDynkin_of_satisfiesDynkin [MeasurableSpace L.State]
    (D : GSHS.FPKData L.State L.Test)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ → Ω → L.State} (hX : Measurable (Function.uncurry X))
    (hdyn : L.toGenPres.SatisfiesDynkin P X)
    (hev : D.ev = L.ev) (hdrift : D.gen = L.drift)
    (hK : ∀ (φ : L.Test) (x : L.State),
      ∫ y, L.ev φ y ∂(D.K x) = ∫ y, L.ev φ (L.land x y) ∂(L.jump x))
    (hlaw : ∀ s : ℝ, 0 ≤ s → P.map (X s) = D.law s)
    {genBound : L.Test → ℝ} (hgen_le : ∀ (φ : L.Test) (x : L.State), |L.drift φ x| ≤ genBound φ)
    (hdrift_meas : ∀ φ, Measurable (L.drift φ))
    (hrate_meas : Measurable L.rate) (hrate_nonneg : ∀ x, 0 ≤ L.rate x)
    {rateBound : ℝ} (hrate_le : ∀ x, L.rate x ≤ rateBound)
    (hr : ∀ s : ℝ, D.r s = (D.law s).withDensity fun x => ENNReal.ofReal (L.rate x)) :
    D.WeakDynkin := by
  refine D.weakDynkin_of_dynkin12 (A := L.gen) (lam := L.rate) (lamBound := rateBound)
    (genBound := genBound) hX hlaw (fun φ => hdrift ▸ hdrift_meas φ)
    (fun φ x => hdrift ▸ hgen_le φ x) hrate_meas hrate_nonneg hrate_le hr
    (fun φ x => ?_) (fun φ t ht => ?_)
  · simp only [gen, jumpTerm, GSHS.FPKData.jumpIntegrand, hdrift, hev, hK]
  · have := hdyn φ t ht
    rw [hev]
    exact this

end LevyData

end SHSCat
