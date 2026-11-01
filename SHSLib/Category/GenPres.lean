/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generator presentations and their intertwining morphisms

This file is the hub of the category-theoretic organization of SHSLib
(see `research/docs/plans/plan_category_theory.md`).

Every framework formalized in the library — Hespanha's SHS, Davis's PDPs,
Bujorianu–Lygeros GSHS and transition semigroups, Bect's Lévy-system
formulation and the differential Chapman–Kolmogorov equation of
Gardiner/Ullah — describes a Markov process through the action of a
*generator* on a class of *test functions*.  We abstract exactly this:

* a **generator presentation** `GenPres` is a state type, a type of test
  functions (possibly carrying derivative data or regularity witnesses), an
  evaluation `ev : Test → State → ℝ` and a generator `gen : Test → State → ℝ`;
* a **morphism** `A ⟶ B` is a map of states `map : A.State → B.State`
  together with a pull-back of test functions `pull : B.Test → A.Test` that
  *intertwines* evaluation and generator:
  `A.ev (pull φ) = B.ev φ ∘ map` and `A.gen (pull φ) = B.gen φ ∘ map`.

Composition is composition of state maps and (reversed) composition of
pull-backs, so presentations form a (large) category `GenPres`.  A morphism is
precisely a *Chu-space morphism* over the value object `ℝ × ℝ` (pairing
`(ev, gen)`).  It is the generator-level formulation of Dynkin's criterion for
Markov functions: if `X` is a process for `A`, then `map ∘ X` is a process for
`B`.

The main point of the category is that properties phrased through `ev` and
`gen` **transfer along morphisms**.  We prove this for the three process-level
properties used across the library:

* `SatisfiesDynkin` — Dynkin's formula in expectation
  (Hespanha Thm. 2, Davis (26.14), Bujorianu (27), Bect (12));
* `SatisfiesForward` — the forward (Kolmogorov / FPK) equation for the
  expectations of test functions, in right-derivative form;
* `SolvesMartingaleProblem` — the compensated processes
  `φ(X_t) − φ(X_0) − ∫₀ᵗ Lφ(X_s) ds` are martingales.

Each transfers along any morphism (`SatisfiesDynkin.map`, …), and is invariant
under isomorphism (`satisfiesDynkin_iso_iff`, …).
-/
import Mathlib

open CategoryTheory MeasureTheory Set Filter

universe u v

noncomputable section

namespace SHSCat

/-- A **generator presentation** of a Markov process: a state type, a type of
test functions, the evaluation of a test function on states, and the action of
the generator on test functions. -/
structure GenPres : Type (u + 1) where
  /-- The state space of the process. -/
  State : Type u
  /-- The (indexing type of the) test functions in the generator domain. -/
  Test : Type u
  /-- The function `φ : State → ℝ` represented by a test. -/
  ev : Test → State → ℝ
  /-- The generator applied to a test function, `Lφ : State → ℝ`. -/
  gen : Test → State → ℝ

namespace GenPres

/-- A **morphism of generator presentations** (an intertwiner): a map of states
together with a pull-back of test functions which intertwines both the
evaluation and the generator. -/
@[ext]
structure Hom (A B : GenPres.{u}) : Type u where
  /-- The map of state spaces. -/
  map : A.State → B.State
  /-- The pull-back of test functions. -/
  pull : B.Test → A.Test
  /-- The pulled-back test represents `φ ∘ map`. -/
  ev_pull : ∀ (φ : B.Test) (x : A.State), A.ev (pull φ) x = B.ev φ (map x)
  /-- The generator of the pulled-back test is `(Lφ) ∘ map`. -/
  gen_pull : ∀ (φ : B.Test) (x : A.State), A.gen (pull φ) x = B.gen φ (map x)

/-- The identity intertwiner. -/
def Hom.id (A : GenPres.{u}) : Hom A A where
  map := fun x => x
  pull := fun φ => φ
  ev_pull := fun _ _ => rfl
  gen_pull := fun _ _ => rfl

/-- Composition of intertwiners. -/
def Hom.comp {A B C : GenPres.{u}} (F : Hom A B) (G : Hom B C) : Hom A C where
  map := fun x => G.map (F.map x)
  pull := fun φ => F.pull (G.pull φ)
  ev_pull := fun φ x => by rw [F.ev_pull, G.ev_pull]
  gen_pull := fun φ x => by rw [F.gen_pull, G.gen_pull]

instance : LargeCategory GenPres.{u} where
  Hom := Hom
  id := Hom.id
  comp F G := Hom.comp F G

@[ext]
theorem hom_ext {A B : GenPres.{u}} {F G : A ⟶ B} (hmap : F.map = G.map)
    (hpull : F.pull = G.pull) : F = G :=
  Hom.ext hmap hpull

@[simp] theorem id_map (A : GenPres.{u}) (x : A.State) : (𝟙 A : A ⟶ A).map x = x := rfl

@[simp] theorem id_pull (A : GenPres.{u}) (φ : A.Test) : (𝟙 A : A ⟶ A).pull φ = φ := rfl

@[simp] theorem comp_map {A B C : GenPres.{u}} (F : A ⟶ B) (G : B ⟶ C) (x : A.State) :
    (F ≫ G).map x = G.map (F.map x) := rfl

@[simp] theorem comp_pull {A B C : GenPres.{u}} (F : A ⟶ B) (G : B ⟶ C) (φ : C.Test) :
    (F ≫ G).pull φ = F.pull (G.pull φ) := rfl

/-! ### The two forgetful functors

A morphism carries two pieces of data, a covariant map of states and a
contravariant map of test functions; these are the two functors below. -/

/-- The covariant functor sending a presentation to its state space. -/
def stateFunctor : GenPres.{u} ⥤ Type u where
  obj A := A.State
  map F := F.map

/-- The contravariant functor sending a presentation to its test functions. -/
def testFunctor : GenPres.{u}ᵒᵖ ⥤ Type u where
  obj A := A.unop.Test
  map F := F.unop.pull

/-! ### Restriction to a sub-family of test functions -/

/-- Restrict a presentation to the test functions indexed by `ι : T → A.Test`
(e.g. the test functions satisfying additional regularity). -/
def restrict (A : GenPres.{u}) {T : Type u} (ι : T → A.Test) : GenPres.{u} where
  State := A.State
  Test := T
  ev := fun φ => A.ev (ι φ)
  gen := fun φ => A.gen (ι φ)

/-- The canonical morphism from a presentation to any of its restrictions. -/
def toRestrict (A : GenPres.{u}) {T : Type u} (ι : T → A.Test) : A ⟶ A.restrict ι where
  map := fun x => x
  pull := ι
  ev_pull := fun _ _ => rfl
  gen_pull := fun _ _ => rfl

/-! ### Process-level properties and their transfer -/

section Process

variable {Ω : Type v}

/-- Push a process forward along the state map of a morphism. -/
def Hom.mapProcess {A B : GenPres.{u}} (F : A ⟶ B) (X : ℝ → Ω → A.State) :
    ℝ → Ω → B.State :=
  fun t ω => F.map (X t ω)

@[simp] theorem id_mapProcess (A : GenPres.{u}) (X : ℝ → Ω → A.State) :
    Hom.mapProcess (𝟙 A) X = X := rfl

@[simp] theorem comp_mapProcess {A B C : GenPres.{u}} (F : A ⟶ B) (G : B ⟶ C)
    (X : ℝ → Ω → A.State) :
    Hom.mapProcess (F ≫ G) X = Hom.mapProcess G (Hom.mapProcess F X) := rfl

/-- The compensated (Dynkin) process `φ(X_t) − φ(X_0) − ∫₀ᵗ Lφ(X_s) ds`. -/
def dynkinProcess (A : GenPres.{u}) (φ : A.Test) (X : ℝ → Ω → A.State) (t : ℝ)
    (ω : Ω) : ℝ :=
  A.ev φ (X t ω) - A.ev φ (X 0 ω) - ∫ s in (0 : ℝ)..t, A.gen φ (X s ω)

@[simp] theorem dynkinProcess_zero (A : GenPres.{u}) (φ : A.Test) (X : ℝ → Ω → A.State)
    (ω : Ω) : A.dynkinProcess φ X 0 ω = 0 := by
  simp [dynkinProcess]

section Naturality

variable {A B : GenPres.{u}}

/-- The key rewriting: pulled-back test functions evaluate along `X` exactly as
the original ones evaluate along the pushed-forward process. -/
theorem Hom.ev_mapProcess (F : A ⟶ B) (φ : B.Test) (X : ℝ → Ω → A.State) (t : ℝ) (ω : Ω) :
    A.ev (F.pull φ) (X t ω) = B.ev φ (F.mapProcess X t ω) :=
  F.ev_pull φ (X t ω)

theorem Hom.gen_mapProcess (F : A ⟶ B) (φ : B.Test) (X : ℝ → Ω → A.State) (t : ℝ) (ω : Ω) :
    A.gen (F.pull φ) (X t ω) = B.gen φ (F.mapProcess X t ω) :=
  F.gen_pull φ (X t ω)

/-- Dynkin processes are natural with respect to morphisms. -/
theorem Hom.dynkinProcess_pull (F : A ⟶ B) (φ : B.Test) (X : ℝ → Ω → A.State) :
    A.dynkinProcess (F.pull φ) X = B.dynkinProcess φ (F.mapProcess X) := by
  funext t ω
  simp only [dynkinProcess, Hom.ev_mapProcess, Hom.gen_mapProcess]

/-- Pushing forward along `F` and then along an inverse of `F` gives back the
original process. -/
theorem Iso.mapProcess_inv_hom (e : A ≅ B) (X : ℝ → Ω → A.State) :
    Hom.mapProcess e.inv (Hom.mapProcess e.hom X) = X := by
  rw [← comp_mapProcess, e.hom_inv_id, id_mapProcess]

end Naturality

variable [MeasurableSpace Ω]

/-- **Dynkin's formula in expectation**:
`E φ(X_t) − E φ(X_0) = E ∫₀ᵗ Lφ(X_s) ds` for every test function and `t ≥ 0`.
This is the form of Hespanha's Theorem 2 / Bect's Eq. (12). -/
def SatisfiesDynkin (A : GenPres.{u}) (P : Measure Ω) (X : ℝ → Ω → A.State) : Prop :=
  ∀ (φ : A.Test) (t : ℝ), 0 ≤ t →
    (∫ ω, A.ev φ (X t ω) ∂P) - ∫ ω, A.ev φ (X 0 ω) ∂P
      = ∫ ω, (∫ s in (0 : ℝ)..t, A.gen φ (X s ω)) ∂P

/-- **The forward equation** for the expectations of test functions, in
right-derivative form: `d⁺/dt E φ(X_t) = E (Lφ)(X_t)` for `t ≥ 0`. -/
def SatisfiesForward (A : GenPres.{u}) (P : Measure Ω) (X : ℝ → Ω → A.State) : Prop :=
  ∀ (φ : A.Test) (t : ℝ), 0 ≤ t →
    HasDerivWithinAt (fun s => ∫ ω, A.ev φ (X s ω) ∂P) (∫ ω, A.gen φ (X t ω) ∂P) (Ici t) t

/-- **The martingale problem**: for every test function the compensated process
`φ(X_t) − φ(X_0) − ∫₀ᵗ Lφ(X_s) ds` is a martingale for the filtration `ℱ`. -/
def SolvesMartingaleProblem (A : GenPres.{u}) (P : Measure Ω) (ℱ : Filtration ℝ ‹_›)
    (X : ℝ → Ω → A.State) : Prop :=
  ∀ φ : A.Test, Martingale (A.dynkinProcess φ X) ℱ P

variable {A B : GenPres.{u}}

/-- **Transfer of Dynkin's formula** along a morphism. -/
theorem SatisfiesDynkin.map {P : Measure Ω} {X : ℝ → Ω → A.State}
    (h : A.SatisfiesDynkin P X) (F : A ⟶ B) : B.SatisfiesDynkin P (F.mapProcess X) := by
  intro φ t ht
  have := h (F.pull φ) t ht
  simpa only [Hom.ev_mapProcess, Hom.gen_mapProcess] using this

/-- **Transfer of the forward equation** along a morphism. -/
theorem SatisfiesForward.map {P : Measure Ω} {X : ℝ → Ω → A.State}
    (h : A.SatisfiesForward P X) (F : A ⟶ B) : B.SatisfiesForward P (F.mapProcess X) := by
  intro φ t ht
  have := h (F.pull φ) t ht
  simpa only [Hom.ev_mapProcess, Hom.gen_mapProcess] using this

/-- **Transfer of the martingale problem** along a morphism. -/
theorem SolvesMartingaleProblem.map {P : Measure Ω} {ℱ : Filtration ℝ ‹_›}
    {X : ℝ → Ω → A.State} (h : A.SolvesMartingaleProblem P ℱ X) (F : A ⟶ B) :
    B.SolvesMartingaleProblem P ℱ (F.mapProcess X) := by
  intro φ
  rw [← Hom.dynkinProcess_pull]
  exact h (F.pull φ)

/-- Dynkin's formula is invariant under isomorphism of presentations. -/
theorem satisfiesDynkin_iso_iff (e : A ≅ B) (P : Measure Ω) (X : ℝ → Ω → A.State) :
    A.SatisfiesDynkin P X ↔ B.SatisfiesDynkin P (e.hom.mapProcess X) := by
  refine ⟨fun h => h.map e.hom, fun h => ?_⟩
  have := h.map e.inv
  rwa [Iso.mapProcess_inv_hom] at this

/-- The forward equation is invariant under isomorphism of presentations. -/
theorem satisfiesForward_iso_iff (e : A ≅ B) (P : Measure Ω) (X : ℝ → Ω → A.State) :
    A.SatisfiesForward P X ↔ B.SatisfiesForward P (e.hom.mapProcess X) := by
  refine ⟨fun h => h.map e.hom, fun h => ?_⟩
  have := h.map e.inv
  rwa [Iso.mapProcess_inv_hom] at this

/-- The martingale problem is invariant under isomorphism of presentations. -/
theorem solvesMartingaleProblem_iso_iff (e : A ≅ B) (P : Measure Ω) (ℱ : Filtration ℝ ‹_›)
    (X : ℝ → Ω → A.State) :
    A.SolvesMartingaleProblem P ℱ X ↔ B.SolvesMartingaleProblem P ℱ (e.hom.mapProcess X) := by
  refine ⟨fun h => h.map e.hom, fun h => ?_⟩
  have := h.map e.inv
  rwa [Iso.mapProcess_inv_hom] at this

/-- A solution of the martingale problem has centred compensated processes:
`E[φ(X_t) − φ(X_0) − ∫₀ᵗ Lφ(X_s) ds] = 0` for `t ≥ 0`. -/
theorem SolvesMartingaleProblem.integral_dynkinProcess_eq_zero {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℝ ‹_›} {X : ℝ → Ω → A.State}
    (h : A.SolvesMartingaleProblem P ℱ X) (φ : A.Test) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, A.dynkinProcess φ X t ω ∂P = 0 := by
  have hset := (h φ).setIntegral_eq ht (MeasurableSet.univ (m := ℱ 0))
  simp only [Measure.restrict_univ] at hset
  rw [← hset]
  simp

end Process

end GenPres

end SHSCat
