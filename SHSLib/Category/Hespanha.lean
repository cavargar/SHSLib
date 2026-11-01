/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hespanha's SHS in the categorical organization

* `SHS.presOn S ι` — the generator presentation of an SHS on the
  time-augmented state `(q, x, t)` (`SHS.DavisState`), for any family of test
  functions `ι : T → SHS.TestFunction Q n`; the generator is Hespanha's
  extended generator (Eq. 9).
* `SHS.levyDataOn S ι` and the isomorphism `SHS.levyIso S ι :
  presOn S ι ≅ (levyDataOn S ι).toGenPres` — Bect's Example 18 (the content of
  `SHS.extendedGenerator_eq_levy`) as an isomorphism of presentations.
* `SHS.genPres S hflow` — the presentation whose tests are measurable test
  functions whose declared derivative data is the true derivative along the
  SHS flow (`SHS.IsFlowDerivative`).
* `SHS.DavisCompatible.hom` — the bridge of `SHSLib.Core.DavisBridge` as a
  morphism `Davis.genPres pdp ⟶ SHS.genPres S hflow`: a compatible Davis PDP
  realizes the SHS, so Dynkin's formula / martingale problems / forward
  equations for the PDP transfer to the SHS.
* `SHS.realizationPres R` and `SHS.realization_satisfiesDynkin` — Hespanha's
  Theorem 2 for the concrete Davis realization `R` (`SHS.theorem2_PDP_generator`)
  restated as the `GenPres` property `SatisfiesDynkin`.
* `SHS.realization_weakDynkin` — **a transferred result**: composing the above
  with the Lévy isomorphism and `LevyData.weakDynkin_of_satisfiesDynkin` yields
  Bect's generalized Dynkin formula (13) for the laws of the time-augmented
  state of any Davis realization and *time-dependent* test functions
  (`SHS.weakDynkin_of_davis` covers time-independent test functions only).
-/
import SHSLib.Category.Davis
import SHSLib.Core.DavisMartingale
import SHSLib.FPK.HespanhaBridge

open CategoryTheory MeasureTheory Set Filter
open scoped ENNReal NNReal

universe u

noncomputable section

namespace SHS

open SHSCat

variable {Q : Type u} {n m : ℕ}

/-! ### The SHS presentation and its Lévy form -/

/-- The generator presentation of an SHS on the time-augmented state, for the
test functions indexed by `ι`. -/
def presOn (S : SHS Q n m) {T : Type u} (ι : T → TestFunction Q n) : GenPres.{u} where
  State := DavisState Q n
  Test := T
  ev := fun φ => (ι φ).toDavisFunction
  gen := fun φ z => S.extendedGenerator (ι φ) z.1 z.2.1 z.2.2

variable [MeasurableSpace Q]

/-- The Lévy-system data of an SHS (Bect's Example 18) on the time-augmented
state: drift `⟨∇ψ, f⟩ + ∂ₜψ`, total intensity `Σ λ_ℓ`, reset kernel
`K = Σ (λ_ℓ/λ) δ_{φ_ℓ}` on `Q × ℝⁿ`, landing a reset while keeping the clock. -/
def levyDataOn [MeasurableSingletonClass Q] (S : SHS Q n m) {T : Type u} (ι : T → TestFunction Q n) : LevyData.{u} where
  State := DavisState Q n
  Jump := Q × EuclideanSpace ℝ (Fin n)
  instJump := inferInstance
  Test := T
  ev := fun φ => (ι φ).toDavisFunction
  drift := fun φ => S.flowGenerator (ι φ)
  rate := S.totalIntensity
  jump := fun z => S.resetKernel z.1 z.2.1 z.2.2
  land := fun z y => (y.1, y.2, z.2.2)

/-- The generator of the SHS equals the Lévy-system generator (Bect, Example 18). -/
theorem extendedGenerator_eq_levyData_gen [MeasurableSingletonClass Q] (S : SHS Q n m) {T : Type u}
    (ι : T → TestFunction Q n) (φ : T) (z : DavisState Q n) :
    S.extendedGenerator (ι φ) z.1 z.2.1 z.2.2 = (S.levyDataOn ι).gen φ z :=
  S.extendedGenerator_eq_levy (ι φ) z.1 z.2.1 z.2.2

/-- **Hespanha's SHS presentation is isomorphic to its Lévy-system form**
(Example 18 of Bect 2010, as an isomorphism in `GenPres`). -/
def levyIso [MeasurableSingletonClass Q] (S : SHS Q n m) {T : Type u} (ι : T → TestFunction Q n) :
    S.presOn ι ≅ (S.levyDataOn ι).toGenPres where
  hom :=
    { map := fun z => z
      pull := fun φ => φ
      ev_pull := fun _ _ => rfl
      gen_pull := fun φ z => S.extendedGenerator_eq_levyData_gen ι φ z }
  inv :=
    { map := fun z => z
      pull := fun φ => φ
      ev_pull := fun _ _ => rfl
      gen_pull := fun φ z => (S.extendedGenerator_eq_levyData_gen ι φ z).symm }

/-! ### Test functions with correct derivative data along the flow -/

/-- The derivative data `(∇ₓψ, ∂ₜψ)` of `ψ` gives the true right derivative of
`ψ` along the SHS flow: `d⁺/du ψ(q, x(t+u), t+u)|_{u=0} = ⟨∇ₓψ, f⟩ + ∂ₜψ`. -/
def IsFlowDerivative (S : SHS Q n m) (hflow : S.HasGlobalFlow) (ψ : TestFunction Q n) :
    Prop :=
  ∀ z : DavisState Q n,
    HasDerivWithinAt
      (fun u : ℝ => ψ.toFun z.1 (hflow.flow z.2.2 z.1 z.2.1 (z.2.2 + u)) (z.2.2 + u))
      (S.flowGenerator ψ z) (Ici 0) 0

/-- A test function of the SHS generator domain: measurable on the augmented
state, with derivative data correct along the flow. -/
structure GenTest (S : SHS Q n m) (hflow : S.HasGlobalFlow) : Type u where
  /-- The underlying test function. -/
  toTestFunction : TestFunction Q n
  measurable : Measurable toTestFunction.toDavisFunction
  flowDeriv : S.IsFlowDerivative hflow toTestFunction

/-- **The generator presentation of an SHS** with flow `hflow`. -/
def genPres (S : SHS Q n m) (hflow : S.HasGlobalFlow) : GenPres.{u} :=
  S.presOn (GenTest.toTestFunction (S := S) (hflow := hflow))

/-- A clock-only test function `ψ(q, x, t) = h(t)` for differentiable `h`: an
explicit element of the SHS generator domain (its declared derivative data is
correct along every flow line). -/
def GenTest.ofClock (S : SHS Q n m) (hflow : S.HasGlobalFlow) (h : ℝ → ℝ)
    (hd : Differentiable ℝ h) : S.GenTest hflow where
  toTestFunction := ⟨fun _ _ t => h t, fun _ _ _ => 0, fun _ _ t => deriv h t⟩
  measurable := hd.continuous.measurable.comp (measurable_snd.comp measurable_snd)
  flowDeriv := by
    intro z
    have hz : HasDerivAt (fun u : ℝ => h (z.2.2 + u)) (deriv h z.2.2) 0 := by
      have := (hd (z.2.2 + 0)).hasDerivAt.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add z.2.2)
      simpa using this
    simpa [flowGenerator] using hz.hasDerivWithinAt

/-- The SHS generator of a clock-only test function is `h'(t)`: resets do not
change the clock, so the jump part vanishes. -/
theorem genPres_gen_ofClock (S : SHS Q n m) (hflow : S.HasGlobalFlow) (h : ℝ → ℝ)
    (hd : Differentiable ℝ h) (z : DavisState Q n) :
    (S.genPres hflow).gen (GenTest.ofClock S hflow h hd) z = deriv h z.2.2 := by
  simp [genPres, presOn, GenTest.ofClock, extendedGenerator]

/-- **The Davis bridge as a morphism.**  A Davis PDP compatible with the SHS
(`SHS.DavisCompatible`) intertwines the two generators: SHS test functions pull
back to Davis test functions (with flow derivative `S.flowGenerator ψ`), and
the Davis generator of the pulled-back test is the SHS extended generator
(`DavisCompatible.pdpGenerator_eq_extendedGenerator`). -/
def DavisCompatible.hom {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {pdp : Davis.PDP (DavisState Q n)} (h : S.DavisCompatible hflow pdp) :
    Davis.genPres pdp ⟶ S.genPres hflow where
  map := fun z => z
  pull := fun ψ =>
    { f := ψ.toTestFunction.toDavisFunction
      Xf := S.flowGenerator ψ.toTestFunction
      measurable := ψ.measurable
      flowDeriv := by
        intro z
        refine (ψ.flowDeriv z).congr (fun u hu => ?_) ?_
        · have hu' : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu
          simp only [TestFunction.toDavisFunction, h.flow_eq, hu']
        · simp [TestFunction.toDavisFunction, h.flow_eq] }
  ev_pull := fun _ _ => rfl
  gen_pull := fun ψ z =>
    h.pdpGenerator_eq_extendedGenerator ψ.toTestFunction ψ.measurable z

/-- **Transfer along the Davis bridge**: if a process satisfies Dynkin's formula
for a compatible Davis PDP, it satisfies Dynkin's formula for the SHS. -/
theorem DavisCompatible.satisfiesDynkin {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {pdp : Davis.PDP (DavisState Q n)} (h : S.DavisCompatible hflow pdp)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ → Ω → DavisState Q n}
    (hX : (Davis.genPres pdp).SatisfiesDynkin P X) :
    (S.genPres hflow).SatisfiesDynkin P X :=
  hX.map h.hom

/-! ### Hespanha's Theorem 2 for a concrete Davis realization -/

section Realization

variable [MeasurableSingletonClass Q]
variable {S : SHS Q n m} {hflow : S.HasGlobalFlow}
  {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
  [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
  {hne : DavisNonExplosive S hflow hf hr}

/-- The test functions for which the hypotheses of Hespanha's Theorem 2
(`SHS.theorem2_PDP_generator`) hold for the realization `R`. -/
def RealizedTest (R : DavisProcessRealization S hflow hf hr hli hne) : Type u :=
  {ψ : TestFunction Q n // DavisTestFunctionRegular S hflow hf hr hli hne R ψ ∧
    Nonempty (DavisCompensatorData S hflow hf hr hli hne R ψ) ∧
    Nonempty (DavisTrueMartingaleData S hflow hf hr hli hne R ψ)}

/-- The SHS presentation restricted to the test functions realized by `R`. -/
def realizationPres (R : DavisProcessRealization S hflow hf hr hli hne) : GenPres.{u} :=
  S.presOn (fun ψ : RealizedTest R => ψ.1)

/-- The time-augmented state process of a realization, indexed by `ℝ`
(negative times are clamped to `0`). -/
def DavisProcessRealization.augProc (R : DavisProcessRealization S hflow hf hr hli hne) :
    ℝ → R.Omega → DavisState Q n :=
  fun s ω => R.process s.toNNReal ω

/-- **Hespanha's Theorem 2 as a `GenPres` property**: the time-augmented state
process of a Davis realization satisfies Dynkin's formula for every realized
(time-dependent) test function. -/
theorem realization_satisfiesDynkin [Fintype Q]
    (R : DavisProcessRealization S hflow hf hr hli hne) :
    (realizationPres R).SatisfiesDynkin R.P R.augProc := by
  intro ψ t ht
  obtain ⟨hψ, ⟨hc⟩, ⟨htm⟩⟩ := ψ.2
  have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
  have key := theorem2_PDP_generator S hflow hf hr hli hne R ψ.1 hψ hc htm t.toNNReal
  have hinit : ∫ ω, (realizationPres R).ev ψ (R.augProc 0 ω) ∂ R.P
      = ψ.1.toDavisFunction R.initial := by
    have hconst : ∫ ω, (realizationPres R).ev ψ (R.augProc 0 ω) ∂ R.P
        = ∫ _ω, ψ.1.toDavisFunction R.initial ∂ R.P := by
      refine integral_congr_ae ?_
      filter_upwards [R.process_zero] with ω hω
      simp only [realizationPres, presOn, DavisProcessRealization.augProc,
        Real.toNNReal_zero, hω]
    rw [hconst, integral_const]
    simp
  have hgen : ∀ ω : R.Omega,
      (∫ u in Icc (0 : ℝ) ((t.toNNReal : ℝ≥0) : ℝ),
        S.extendedGenerator ψ.1 (R.qProc u.toNNReal ω) (R.xProc u.toNNReal ω)
          (R.timeProc u.toNNReal ω))
        = ∫ s in (0 : ℝ)..t, (realizationPres R).gen ψ (R.augProc s ω) := by
    intro ω
    rw [hcoe, intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    rfl
  simp only [hgen] at key
  rw [hinit]
  have hleft : ∫ ω, (realizationPres R).ev ψ (R.augProc t ω) ∂ R.P
      = ∫ ω, ψ.1.toFun (R.qProc t.toNNReal ω) (R.xProc t.toNNReal ω)
          (R.timeProc t.toNNReal ω) ∂ R.P := rfl
  rw [hleft, key]
  ring

/-- **A transferred result: Bect's generalized Dynkin formula (13) for the
time-augmented state of a Davis realization of an SHS.**

Hespanha's Theorem 2 (`realization_satisfiesDynkin`) is transported along the
Lévy isomorphism `levyIso` (Bect's Example 18) and fed to
`LevyData.weakDynkin_of_satisfiesDynkin`.  Here `D` is Bect's data on the
augmented state `(q, x, t)`, indexed by the realized test functions, with the
SHS test functions as test functions (`hev`), the flow part of the generator as
drift (`hdrift`), a Markov kernel with the averages of the SHS reset kernel
(`hK`), the laws of the augmented process (`hlaw`) and mean jump intensity
`λ μ_s` (`hr`).  Unlike `SHS.weakDynkin_of_davis`, the test functions may depend
on time. -/
theorem realization_weakDynkin [Fintype Q]
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (D : GSHS.FPKData (DavisState Q n) (RealizedTest R))
    (hX : Measurable (Function.uncurry R.augProc))
    (hev : D.ev = fun ψ => ψ.1.toDavisFunction)
    (hdrift : D.gen = fun ψ => S.flowGenerator ψ.1)
    (hK : ∀ (ψ : RealizedTest R) (z : DavisState Q n),
      ∫ y, ψ.1.toDavisFunction y ∂(D.K z)
        = ∫ y, ψ.1.toFun y.1 y.2 z.2.2 ∂(S.resetKernel z.1 z.2.1 z.2.2))
    (hlaw : ∀ s : ℝ, 0 ≤ s → R.P.map (R.augProc s) = D.law s)
    {genBound : RealizedTest R → ℝ}
    (hgen_le : ∀ ψ z, |S.flowGenerator ψ.1 z| ≤ genBound ψ)
    (hdrift_meas : ∀ ψ : RealizedTest R, Measurable (S.flowGenerator ψ.1))
    (hrate_meas : Measurable S.totalIntensity)
    {rateBound : ℝ} (hrate_le : ∀ z, S.totalIntensity z ≤ rateBound)
    (hrD : ∀ s : ℝ, D.r s = (D.law s).withDensity fun z => ENNReal.ofReal (S.totalIntensity z)) :
    D.WeakDynkin := by
  have hdyn := (realization_satisfiesDynkin R).map (S.levyIso (fun ψ : RealizedTest R => ψ.1)).hom
  letI : MeasurableSpace (S.levyDataOn (fun ψ : RealizedTest R => ψ.1)).State :=
    inferInstanceAs (MeasurableSpace (DavisState Q n))
  exact (S.levyDataOn (fun ψ : RealizedTest R => ψ.1)).weakDynkin_of_satisfiesDynkin D hX hdyn
    hev hdrift hK hlaw hgen_le hdrift_meas hrate_meas (S.totalIntensity_nonneg) hrate_le hrD

end Realization

end SHS
