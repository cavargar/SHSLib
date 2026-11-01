/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Classical `C¹` test functions belong to the SHS generator domain

`SHS.genPres S hflow` (in `SHSLib.Category.Hespanha`) takes as tests the
measurable test functions whose declared derivative data `(∇ₓψ, ∂ₜψ)` is the true
right derivative of `ψ` along the SHS flow (`SHS.IsFlowDerivative`).  This file
shows that this condition is automatic for classical test functions:

* `SHS.HasGlobalFlow.hasDerivWithinAt_flow_Ici` — the one-sided differential
  form of the flow ODE at the initial time;
* `SHS.isFlowDerivative_of_hasPartials` — a test function with genuine partial
  derivatives (`TestFunction.HasPartials`, from `SHSLib.Core.FlowDynkin`) has
  correct flow derivative data, provided the drift is right-continuous along
  each trajectory (`SHS.DriftRightContinuous`);
* `SHS.GenTest.ofHasPartials` — every measurable `C¹` test function is a test of
  `SHS.genPres`, and `SHS.genPres_gen_ofHasPartials` says its generator is
  Hespanha's extended generator.
* `SHS.toClassicalPres` — the corresponding morphism from `SHS.genPres` to
  the presentation restricted to classical test functions, so that every
  transferable property of `genPres` holds for all classical test functions.
-/
import SHSLib.Category.Hespanha
import SHSLib.Core.FlowDynkin

open CategoryTheory MeasureTheory Set Filter Topology

universe u

noncomputable section

namespace SHS

open SHSCat

variable {Q : Type u} {n m : ℕ}

/-- **One-sided differential form of the ODE at the initial time.**  If the drift
along the trajectory started at `(t₀, q, x)` is continuous on `[t₀, t₁]` for some
`t₁ > t₀`, then the flow has right derivative `f(q, x, t₀)` at `t₀`. -/
theorem HasGlobalFlow.hasDerivWithinAt_flow_Ici (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (t₀ t₁ : ℝ) (ht : t₀ < t₁) (q : Q)
    (x : EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s) (Icc t₀ t₁)) :
    HasDerivWithinAt (hflow.flow t₀ q x) (S.f q x t₀) (Ici t₀) t₀ := by
  haveI : Fact (t₀ ∈ Icc t₀ t₁) := ⟨⟨le_rfl, ht.le⟩⟩
  have hint : IntervalIntegrable (fun r => S.f q (hflow.flow t₀ q x r) r) volume t₀ t₀ :=
    IntervalIntegrable.refl
  have hFTC : HasDerivWithinAt (fun u => ∫ r in t₀..u, S.f q (hflow.flow t₀ q x r) r)
      (S.f q (hflow.flow t₀ q x t₀) t₀) (Icc t₀ t₁) t₀ :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t₀)
      (hcont t₀ ⟨le_rfl, ht.le⟩)
  have hFTC' : HasDerivWithinAt (fun u => x + ∫ r in t₀..u, S.f q (hflow.flow t₀ q x r) r)
      (S.f q x t₀) (Icc t₀ t₁) t₀ := by
    simpa [hflow.flow_init] using hFTC.const_add x
  have hIcc : HasDerivWithinAt (hflow.flow t₀ q x) (S.f q x t₀) (Icc t₀ t₁) t₀ :=
    hFTC'.congr (fun s hs => hflow.flow_eq_intervalIntegral S t₀ q x hs.1)
      (hflow.flow_eq_intervalIntegral S t₀ q x le_rfl)
  exact hIcc.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE ht)

/-- The drift is right-continuous along every trajectory: from every augmented
state `(q, x, t)` the drift along the flow line is continuous on some interval
`[t, t₁]` with `t₁ > t`.  (Satisfied, e.g., if `f` is jointly continuous and the
trajectories are continuous: `driftRightContinuous_of_continuous`.) -/
def DriftRightContinuous (S : SHS Q n m) (hflow : S.HasGlobalFlow) : Prop :=
  ∀ z : DavisState Q n, ∃ t₁, z.2.2 < t₁ ∧
    ContinuousOn (fun s => S.f z.1 (hflow.flow z.2.2 z.1 z.2.1 s) s) (Icc z.2.2 t₁)

/-- A jointly continuous drift with continuous trajectories is right-continuous
along trajectories. -/
theorem driftRightContinuous_of_continuous (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : ∀ q, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => S.f q p.1 p.2))
    (htraj : ∀ t₀ q x, Continuous (hflow.flow t₀ q x)) :
    S.DriftRightContinuous hflow := by
  rintro ⟨q, x, t₀⟩
  refine ⟨t₀ + 1, by linarith, ?_⟩
  exact ((hf q).comp ((htraj t₀ q x).prodMk continuous_id)).continuousOn

/-- **Classical test functions have correct flow-derivative data.**  If `ψ` has
genuine partial derivatives `(∇ₓψ, ∂ₜψ)` and the drift is right-continuous along
trajectories, then `⟨∇ₓψ, f⟩ + ∂ₜψ` is the right derivative of `ψ` along the
SHS flow. -/
theorem isFlowDerivative_of_hasPartials (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hdrift : S.DriftRightContinuous hflow) (ψ : TestFunction Q n) (hψ : ψ.HasPartials) :
    S.IsFlowDerivative hflow ψ := by
  rintro ⟨q, x, t₀⟩
  obtain ⟨t₁, ht, hcont⟩ := hdrift (q, x, t₀)
  have hcurve : HasDerivWithinAt (fun r => (hflow.flow t₀ q x r, r))
      (S.f q x t₀, (1 : ℝ)) (Ici t₀) t₀ :=
    (hflow.hasDerivWithinAt_flow_Ici S t₀ t₁ ht q x hcont).prodMk (hasDerivWithinAt_id _ _)
  have hψ' := hψ q (hflow.flow t₀ q x t₀) t₀
  have hcomp : HasDerivWithinAt (fun r => ψ.toFun q (hflow.flow t₀ q x r) r)
      (S.flowGenerator ψ (q, x, t₀)) (Ici t₀) t₀ := by
    have h := hψ'.comp_hasDerivWithinAt (x := t₀) (f := fun r => (hflow.flow t₀ q x r, r))
      hcurve
    simpa [SHS.flowGenerator, real_inner_comm, Function.comp_def, hflow.flow_init] using h
  have hshift : HasDerivWithinAt (fun u : ℝ => t₀ + u) 1 (Ici 0) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add t₀).hasDerivWithinAt
  have hmaps : MapsTo (fun u : ℝ => t₀ + u) (Ici 0) (Ici t₀) := fun u hu => by
    simp only [mem_Ici] at hu ⊢; linarith
  have h := hcomp.comp_of_eq (0 : ℝ) hshift hmaps (by simp)
  simpa [Function.comp_def] using h

/-- **Every measurable classical test function is a test of `SHS.genPres`.** -/
def GenTest.ofHasPartials (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hdrift : S.DriftRightContinuous hflow) (ψ : TestFunction Q n) (hψ : ψ.HasPartials)
    [MeasurableSpace Q] (hmeas : Measurable ψ.toDavisFunction) : S.GenTest hflow where
  toTestFunction := ψ
  measurable := hmeas
  flowDeriv := S.isFlowDerivative_of_hasPartials hflow hdrift ψ hψ

/-- The generator of a classical test function in `SHS.genPres` is Hespanha's
extended generator (Eq. 9). -/
theorem genPres_gen_ofHasPartials [MeasurableSpace Q] (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hdrift : S.DriftRightContinuous hflow) (ψ : TestFunction Q n)
    (hψ : ψ.HasPartials) (hmeas : Measurable ψ.toDavisFunction) (z : DavisState Q n) :
    (S.genPres hflow).gen (GenTest.ofHasPartials S hflow hdrift ψ hψ hmeas) z =
      S.extendedGenerator ψ z.1 z.2.1 z.2.2 := rfl

/-- The **classical test functions** of an SHS: measurable test functions with
genuine partial derivatives. -/
structure ClassicalTest (Q : Type u) (n : ℕ) [MeasurableSpace Q] : Type u where
  /-- The underlying test function. -/
  toTestFunction : TestFunction Q n
  hasPartials : toTestFunction.HasPartials
  measurable : Measurable toTestFunction.toDavisFunction

/-- **The SHS generator domain contains all classical test functions**: the
canonical morphism from `SHS.genPres` to the SHS presentation on classical test
functions.  Along it, any transferable property of `genPres` (Dynkin's formula,
the forward equation, the martingale problem) yields the property for all
classical test functions at once. -/
def toClassicalPres [MeasurableSpace Q] (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hdrift : S.DriftRightContinuous hflow) :
    S.genPres hflow ⟶ S.presOn (ClassicalTest.toTestFunction (Q := Q) (n := n)) where
  map := fun z => z
  pull := fun ψ => GenTest.ofHasPartials S hflow hdrift ψ.toTestFunction ψ.hasPartials
    ψ.measurable
  ev_pull := fun _ _ => rfl
  gen_pull := fun _ _ => rfl

/-- **Dynkin's formula for all classical test functions**, transferred along
`toClassicalPres` from Dynkin's formula on `SHS.genPres`. -/
theorem satisfiesDynkin_classical [MeasurableSpace Q] (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (hdrift : S.DriftRightContinuous hflow)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ → Ω → DavisState Q n}
    (h : (S.genPres hflow).SatisfiesDynkin P X) :
    (S.presOn (ClassicalTest.toTestFunction (Q := Q) (n := n))).SatisfiesDynkin P X :=
  h.map (S.toClassicalPres hflow hdrift)

end SHS
