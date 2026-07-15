import SHSLib.Core.GeneratorDefs
import SHSLib.Foundations.DavisCh2

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-!
# Bridge from stochastic hybrid systems to Davis PDP characteristics

Hespanha's SHS is time-inhomogeneous, whereas `Davis.PDP` is homogeneous.
The standard connection is therefore made on the time-augmented state
`(q, x, t)`.  This file records the compatibility data that a concrete PDP
construction must establish and proves that the Davis generator then agrees
with `SHS.extendedGenerator`.
-/

namespace SHS

/-- Time-augmented state used to regard an SHS as a homogeneous Davis PDP. -/
abbrev DavisState (Q : Type*) (n : ℕ) :=
  Q × EuclideanSpace ℝ (Fin n) × ℝ

/-- Embed an SHS initial condition into the time-augmented Davis state. -/
def InitialCondition.toDavisState {Q : Type*} {n : ℕ}
    (z₀ : InitialCondition Q n) : DavisState Q n :=
  (z₀.q₀, z₀.x₀, z₀.t₀)

/-- Lift a time-dependent SHS test function to the augmented Davis state. -/
def TestFunction.toDavisFunction {Q : Type*} {n : ℕ}
    (ψ : TestFunction Q n) : DavisState Q n → ℝ :=
  fun z => ψ.toFun z.1 z.2.1 z.2.2

/-- Package SHS coordinate processes as one time-augmented state process. -/
def toDavisProcess {Q Omega : Type*} {n : ℕ}
    (q : ℝ → Omega → Q)
    (x : ℝ → Omega → EuclideanSpace ℝ (Fin n)) :
    ℝ → Omega → DavisState Q n :=
  fun t omega => (q t omega, x t omega, t)

@[simp] theorem TestFunction.toDavisFunction_toDavisProcess
    {Q Omega : Type*} {n : ℕ} (ψ : TestFunction Q n)
    (q : ℝ → Omega → Q)
    (x : ℝ → Omega → EuclideanSpace ℝ (Fin n)) (t : ℝ) (omega : Omega) :
    ψ.toDavisFunction (toDavisProcess q x t omega) =
      ψ.toFun (q t omega) (x t omega) t := rfl

/-- The deterministic (flow) part of the generator on augmented states. -/
def flowGenerator {Q : Type*} {n m : ℕ} (S : SHS Q n m)
    (ψ : TestFunction Q n) : DavisState Q n → ℝ :=
  fun z => @inner ℝ _ _ (ψ.grad_x z.1 z.2.1 z.2.2)
      (S.f z.1 z.2.1 z.2.2) + ψ.partial_t z.1 z.2.1 z.2.2

/-- Total SHS jump intensity at an augmented state. -/
def totalIntensity {Q : Type*} {n m : ℕ} (S : SHS Q n m)
    (z : DavisState Q n) : ℝ :=
  ∑ ℓ : Fin m, S.intensity ℓ z.1 z.2.1 z.2.2

/-- The augmented state obtained by applying reset channel `ℓ`.
The clock is unchanged at an instantaneous reset. -/
def resetDavisState {Q : Type*} {n m : ℕ} (S : SHS Q n m)
    (ℓ : Fin m) (z : DavisState Q n) : DavisState Q n :=
  (S.phi_q ℓ z.1 z.2.1 z.2.2,
    S.phi_x ℓ z.1 z.2.1 z.2.2, z.2.2)

/-- Compatibility between an SHS and a Davis PDP on the augmented state.

`flow_eq` identifies deterministic motion, `jumpRate_eq` identifies the total
hazard, and `jumpCompensator_eq` says that the marked reset channels have the
same weighted jump compensator as the Davis transition kernel.  The last field
is stated in weighted form so that states with zero total intensity require no
arbitrary normalization convention.
-/
structure DavisCompatible {Q : Type*} [MeasurableSpace Q] {n m : ℕ}
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (pdp : Davis.PDP (DavisState Q n)) : Prop where
  flow_eq : ∀ (u : ℝ≥0) (z : DavisState Q n),
    pdp.flow u z =
      (z.1, hflow.flow z.2.2 z.1 z.2.1 (z.2.2 + (u : ℝ)),
        z.2.2 + (u : ℝ))
  jumpRate_eq : ∀ z : DavisState Q n,
    (pdp.jumpRate z : ℝ) = S.totalIntensity z
  jumpCompensator_eq : ∀ (g : DavisState Q n → ℝ), Measurable g →
    ∀ z : DavisState Q n,
      (pdp.jumpRate z : ℝ) *
          (∫ y, g y ∂(pdp.transitionMeasure z)) -
        (pdp.jumpRate z : ℝ) * g z =
      ∑ ℓ : Fin m,
        (g (S.resetDavisState ℓ z) - g z) *
          S.intensity ℓ z.1 z.2.1 z.2.2

/-- The total intensity is nonnegative. -/
theorem totalIntensity_nonneg {Q : Type*} {n m : ℕ} (S : SHS Q n m)
    (z : DavisState Q n) : 0 ≤ S.totalIntensity z := by
  exact Finset.sum_nonneg fun ℓ _ => S.intensity_nonneg ℓ z.1 z.2.1 z.2.2

/-- A compatible Davis jump rate is exactly the sum of the SHS channel rates. -/
theorem DavisCompatible.jumpRate_eq_sum {Q : Type*} [MeasurableSpace Q]
    {n m : ℕ} {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {pdp : Davis.PDP (DavisState Q n)}
    (h : DavisCompatible S hflow pdp) (z : DavisState Q n) :
    (pdp.jumpRate z : ℝ) =
      ∑ ℓ : Fin m, S.intensity ℓ z.1 z.2.1 z.2.2 := by
  exact h.jumpRate_eq z

/-- **Generator bridge.** For compatible local characteristics, the Davis PDP
extended generator of the lifted test function is exactly Hespanha's SHS
extended generator. -/
theorem DavisCompatible.pdpGenerator_eq_extendedGenerator
    {Q : Type*} [MeasurableSpace Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {pdp : Davis.PDP (DavisState Q n)}
    (h : DavisCompatible S hflow pdp) (ψ : TestFunction Q n)
    (hψ : Measurable ψ.toDavisFunction) (z : DavisState Q n) :
    Davis.pdpGenerator pdp (S.flowGenerator ψ) ψ.toDavisFunction z =
      S.extendedGenerator ψ z.1 z.2.1 z.2.2 := by
  rw [Davis.pdpGenerator]
  have hjump := h.jumpCompensator_eq ψ.toDavisFunction hψ z
  rw [mul_sub, hjump]
  rfl

/-- Pointwise process form of the generator bridge.  This is the rewrite used
when transporting Davis compensated-process martingales into
`SHS.theorem2_PDP_generator`. -/
theorem DavisCompatible.pdpGenerator_along_process
    {Q Omega : Type*} [MeasurableSpace Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {pdp : Davis.PDP (DavisState Q n)}
    (h : DavisCompatible S hflow pdp) (ψ : TestFunction Q n)
    (hψ : Measurable ψ.toDavisFunction)
    (Z : ℝ → Omega → DavisState Q n) (t : ℝ) (omega : Omega) :
    Davis.pdpGenerator pdp (S.flowGenerator ψ) ψ.toDavisFunction (Z t omega) =
      S.extendedGenerator ψ (Z t omega).1 (Z t omega).2.1
        (Z t omega).2.2 := by
  exact h.pdpGenerator_eq_extendedGenerator ψ hψ (Z t omega)

/-- Generator compatibility specialized to the canonical augmented process
formed from the discrete and continuous SHS coordinates. -/
theorem DavisCompatible.pdpGenerator_toDavisProcess
    {Q Omega : Type*} [MeasurableSpace Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {pdp : Davis.PDP (DavisState Q n)}
    (h : DavisCompatible S hflow pdp) (ψ : TestFunction Q n)
    (hψ : Measurable ψ.toDavisFunction)
    (q : ℝ → Omega → Q)
    (x : ℝ → Omega → EuclideanSpace ℝ (Fin n))
    (t : ℝ) (omega : Omega) :
    Davis.pdpGenerator pdp (S.flowGenerator ψ) ψ.toDavisFunction
        (toDavisProcess q x t omega) =
      S.extendedGenerator ψ (q t omega) (x t omega) t := by
  exact h.pdpGenerator_eq_extendedGenerator ψ hψ
    (toDavisProcess q x t omega)

end SHS
