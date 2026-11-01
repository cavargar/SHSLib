/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The category of transition semigroups and the strong-generator functor

Objects are transition semigroups `(P_t)_{t ≥ 0}` in the sense of
`Bujorianu2006.TransitionSemigroup` (Bujorianu–Lygeros 2006, Section 3.2).
A morphism `(X, S) ⟶ (Y, T)` is a map `φ : X → Y` which **intertwines** the
semigroups, `P^S_t (f ∘ φ) = (P^T_t f) ∘ φ` for `t ≥ 0`: the image of an
`S`-Markov process under `φ` is a `T`-Markov process (a *Markov function*, or
*lumping*).

The strong generator `Lf = lim_{t↓0} (P_t f − f)/t` (`HasStrongGenerator`) is
natural for intertwiners, which gives a functor

  `SemigroupSys.strongGenerator : SemigroupSys ⥤ GenPres`.

Consequently every result about generator presentations (Dynkin's formula,
martingale problems, forward equations — see `SHSLib.Category.GenPres`)
applies to transition semigroups, and transfers along intertwiners.  We also
show that intertwiners transport resolvents and Bujorianu's Dynkin formula.
-/
import SHSLib.Category.GenPres
import SHSLib.Bujorianu2006.Martingale

open CategoryTheory MeasureTheory Set Filter Topology

universe u

noncomputable section

namespace SHSCat

open Bujorianu2006

/-- A transition semigroup, bundled with its state space. -/
structure SemigroupSys : Type (u + 1) where
  /-- The state space. -/
  carrier : Type u
  /-- The transition semigroup `(P_t)`. -/
  sg : TransitionSemigroup carrier

namespace SemigroupSys

/-- An intertwiner of transition semigroups. -/
@[ext]
structure Hom (X Y : SemigroupSys.{u}) : Type u where
  /-- The map of state spaces. -/
  toFun : X.carrier → Y.carrier
  /-- `P_t (f ∘ φ) = (P_t f) ∘ φ` for `t ≥ 0`. -/
  intertwine : ∀ (t : ℝ), 0 ≤ t → ∀ (f : Y.carrier → ℝ) (x : X.carrier),
    X.sg.P t (fun y => f (toFun y)) x = Y.sg.P t f (toFun x)

instance : LargeCategory SemigroupSys.{u} where
  Hom := Hom
  id X := ⟨fun x => x, fun _ _ _ _ => rfl⟩
  comp F G := ⟨fun x => G.toFun (F.toFun x), fun t ht f x => by
    rw [F.intertwine t ht (fun y => f (G.toFun y)) x, G.intertwine t ht f (F.toFun x)]⟩

@[simp] theorem id_toFun (X : SemigroupSys.{u}) (x : X.carrier) :
    (𝟙 X : X ⟶ X).toFun x = x := rfl

@[simp] theorem comp_toFun {X Y Z : SemigroupSys.{u}} (F : X ⟶ Y) (G : Y ⟶ Z)
    (x : X.carrier) : (F ≫ G).toFun x = G.toFun (F.toFun x) := rfl

/-- Intertwiners transport strong generators: if `Lf = g` for `T`, then
`L(f ∘ φ) = g ∘ φ` for `S`. -/
theorem Hom.hasStrongGenerator_comp {X Y : SemigroupSys.{u}} (F : X ⟶ Y)
    {f g : Y.carrier → ℝ} (h : Y.sg.HasStrongGenerator f g) :
    X.sg.HasStrongGenerator (fun x => f (F.toFun x)) (fun x => g (F.toFun x)) := by
  intro x
  refine (h (F.toFun x)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [F.intertwine t (le_of_lt ht) f x]

/-- **The strong-generator presentation** of a transition semigroup: test
functions are the pairs `(f, Lf)` in the graph of the strong generator. -/
def toGenPres (X : SemigroupSys.{u}) : GenPres.{u} where
  State := X.carrier
  Test := {p : (X.carrier → ℝ) × (X.carrier → ℝ) // X.sg.HasStrongGenerator p.1 p.2}
  ev := fun p => p.1.1
  gen := fun p => p.1.2

/-- **The strong-generator functor** `SemigroupSys ⥤ GenPres`. -/
def strongGenerator : SemigroupSys.{u} ⥤ GenPres.{u} where
  obj X := X.toGenPres
  map {X Y} F :=
    { map := F.toFun
      pull := fun p => ⟨(fun x => p.1.1 (F.toFun x), fun x => p.1.2 (F.toFun x)),
        F.hasStrongGenerator_comp p.2⟩
      ev_pull := fun _ _ => rfl
      gen_pull := fun _ _ => rfl }

@[simp] theorem strongGenerator_obj (X : SemigroupSys.{u}) :
    strongGenerator.obj X = X.toGenPres := rfl

@[simp] theorem strongGenerator_map_map {X Y : SemigroupSys.{u}} (F : X ⟶ Y) (x : X.carrier) :
    (strongGenerator.map F).map x = F.toFun x := rfl

/-- Intertwiners transport resolvents: `U_p (f ∘ φ) = (U_p f) ∘ φ`. -/
theorem Hom.resolvent_comp {X Y : SemigroupSys.{u}} (F : X ⟶ Y) (p : ℝ)
    (f : Y.carrier → ℝ) (x : X.carrier) :
    X.sg.resolvent p (fun y => f (F.toFun y)) x = Y.sg.resolvent p f (F.toFun x) := by
  unfold TransitionSemigroup.resolvent
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [F.intertwine t (le_of_lt (mem_Ioi.mp ht)) f x]

/-- **Transfer of Bujorianu's Dynkin formula along an intertwiner**: the
semigroup-level Dynkin formula `P_t f(y) − f(y) = ∫₀ᵗ P_s(Lf)(y) ds` at the
image point `y = φ x`, rewritten as a statement about the source semigroup
acting on the pulled-back function `f ∘ φ`. -/
theorem Hom.dynkin_formula_comp {X Y : SemigroupSys.{u}} (F : X ⟶ Y)
    {f Lf : Y.carrier → ℝ} (t : ℝ) (ht : 0 ≤ t) (x : X.carrier)
    (hcont : ContinuousOn (fun u => Y.sg.P u f (F.toFun x)) (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivWithinAt (fun u => Y.sg.P u f (F.toFun x))
      (Y.sg.P s Lf (F.toFun x)) (Ioi s) s)
    (hint : IntervalIntegrable (fun s => Y.sg.P s Lf (F.toFun x)) volume 0 t) :
    X.sg.P t (fun y => f (F.toFun y)) x - f (F.toFun x)
      = ∫ s in (0 : ℝ)..t, X.sg.P s (fun y => Lf (F.toFun y)) x := by
  rw [F.intertwine t ht f x, TransitionSemigroup.dynkin_formula t ht (F.toFun x) hcont hderiv hint]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs0 : 0 ≤ s := by
    rcases hs with ⟨h1, _⟩
    exact le_trans (by simp [ht]) h1
  exact (F.intertwine s hs0 Lf x).symm

end SemigroupSys

end SHSCat
