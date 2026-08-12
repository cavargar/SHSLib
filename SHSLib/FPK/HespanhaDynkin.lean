/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eq. (12) for a concrete stochastic hybrid system

The generalized Dynkin formula (12) of Bect (2010),

  `E{φ(X_t)} − E{φ(X_0)} = E{∫₀ᵗ (Aφ)(X_s) ds}`,

is derived in `SHSLib/FPK/DynkinFormula.lean` from the martingale property of the
compensated process.  This file instantiates it for the *concrete* stochastic hybrid
system of `SHSLib.Core`: the Davis realization of a Hespanha SHS, for which the
identity above is available as `SHS.theorem2_PDP_generator`.

The state process of the realization is the pair `(mode, continuous state)`,
`SHS.DavisProcessRealization.stateProc`, indexed by elapsed time.  For a
time-homogeneous system and a time-independent test function — i.e. when the test
function `ψ` and the extended generator `Aψ` only depend on the state and not on the
clock coordinate — the Dynkin formula takes exactly the form
`GSHS.FPKData.weakDynkin_of_dynkin12` expects, so that the weak formulation of the
generalized FPK equation applies to the concrete process.
-/
import SHSLib.Core.DavisMartingale
import SHSLib.FPK.DynkinFormula
import SHSLib.FPK.HespanhaResetKernel

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace SHS

/-- The SHS state process `(q_t, x_t)` of a Davis realization, indexed by elapsed time
in `ℝ` (times before the start of the realization are clamped to the initial time). -/
def DavisProcessRealization.stateProc
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
    {hne : DavisNonExplosive S hflow hf hr}
    (R : DavisProcessRealization S hflow hf hr hli hne) :
    ℝ → R.Omega → Q × EuclideanSpace ℝ (Fin n) :=
  fun s ω => ((R.process s.toNNReal ω).1, (R.process s.toNNReal ω).2.1)

variable {Q : Type*} [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}

/-- **Eq. (12) of Bect (2010) for a concrete SHS.**  For the Davis realization of a
Hespanha stochastic hybrid system, whose extended generator is compensated by a true
martingale (`SHS.theorem2_PDP_generator`), the generalized Dynkin formula holds in the
form used by the weak formulation of the generalized FPK equation:

  `E{φ(X_t)} − E{φ(X_0)} = E{∫₀ᵗ (Aφ)(X_s) ds}`,

where `X` is the state process `(q_t, x_t)`, `φ = ev` is a time-independent test
function (`hev`) and `A` is the corresponding time-independent extended generator
(`hA`) — the situation of a time-homogeneous system. -/
theorem dynkin12_of_davis
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hr)
    (R : DavisProcessRealization S hflow hf hr hli hne)
    (ψ : TestFunction Q n)
    (hψ : DavisTestFunctionRegular S hflow hf hr hli hne R ψ)
    (hc : DavisCompensatorData S hflow hf hr hli hne R ψ)
    (htm : DavisTrueMartingaleData S hflow hf hr hli hne R ψ)
    {ev A : Q × EuclideanSpace ℝ (Fin n) → ℝ}
    (hev : ∀ q x t, ψ.toFun q x t = ev (q, x))
    (hA : ∀ q x t, S.extendedGenerator ψ q x t = A (q, x))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, ev (R.stateProc t ω) ∂ R.P) - ∫ ω, ev (R.stateProc 0 ω) ∂ R.P
      = ∫ ω, (∫ s in (0 : ℝ)..t, A (R.stateProc s ω)) ∂ R.P := by
  have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
  have key := theorem2_PDP_generator S hflow hf hr hli hne R ψ hψ hc htm t.toNNReal
  -- the endpoint term
  have hleft : ∫ ω, ψ.toFun (R.qProc t.toNNReal ω) (R.xProc t.toNNReal ω)
        (R.timeProc t.toNNReal ω) ∂ R.P
      = ∫ ω, ev (R.stateProc t ω) ∂ R.P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact hev _ _ _
  -- the initial term
  have hinit : ψ.toDavisFunction R.initial = ∫ ω, ev (R.stateProc 0 ω) ∂ R.P := by
    have hconst : ∫ ω, ev (R.stateProc 0 ω) ∂ R.P
        = ∫ _ω, ev (R.initial.1, R.initial.2.1) ∂ R.P := by
      refine integral_congr_ae ?_
      filter_upwards [R.process_zero] with ω hω
      simp only [DavisProcessRealization.stateProc, Real.toNNReal_zero, hω]
    rw [hconst, integral_const]
    simp [TestFunction.toDavisFunction, hev]
  -- the generator term
  have hgen : ∀ ω : R.Omega,
      (∫ u in Icc (0 : ℝ) ((t.toNNReal : ℝ≥0) : ℝ),
        S.extendedGenerator ψ (R.qProc u.toNNReal ω) (R.xProc u.toNNReal ω)
          (R.timeProc u.toNNReal ω))
        = ∫ s in (0 : ℝ)..t, A (R.stateProc s ω) := by
    intro ω
    rw [hcoe, intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    exact hA _ _ _
  rw [hleft, hinit] at key
  simp only [hgen] at key
  linarith [key]

/-- **Eq. (13) for a concrete SHS.**  The law of the state process of a Davis
realization of a (time-homogeneous) Hespanha stochastic hybrid system satisfies the
generalized Dynkin formula (13) of Bect (2010), i.e. the standing hypothesis
`WeakDynkin` of Theorem 8.

The data `D` collects the objects of Bect's framework: the test functions `D.ev i`
(the SHS test functions `ψ i`, time-independent by `hev`), the drift part `D.gen i` of
the generator (`hgen`), the laws `D.law s` of the state process (`hlaw`), the reset
kernel `D.K` of Eq. (31) (`hK`) and the mean jump intensity `D.r s = λ μ_s` of Eq. (8)
(`hr_eq`).  The remaining hypotheses are the regularity conditions under which the
compensated generator of the SHS is a true martingale. -/
theorem weakDynkin_of_davis
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hrr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hrr)
    (R : DavisProcessRealization S hflow hf hrr hli hne)
    {ι : Type*} (psi : ι → TestFunction Q n)
    (hpsi_reg : ∀ i, DavisTestFunctionRegular S hflow hf hrr hli hne R (psi i))
    (hcomp : ∀ i, DavisCompensatorData S hflow hf hrr hli hne R (psi i))
    (htrue : ∀ i, DavisTrueMartingaleData S hflow hf hrr hli hne R (psi i))
    (D : GSHS.FPKData (Q × EuclideanSpace ℝ (Fin n)) ι)
    (t₀ : ℝ) (hphi : ∀ ℓ, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      S.phi ℓ z.1 z.2 t₀)
    {A : ι → Q × EuclideanSpace ℝ (Fin n) → ℝ} {genBound : ι → ℝ} {lamBound : ℝ}
    (hX : Measurable (Function.uncurry R.stateProc))
    (hlaw : ∀ s : ℝ, 0 ≤ s → R.P.map (R.stateProc s) = D.law s)
    (hev : ∀ (i : ι) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      (psi i).toFun q x t = D.ev i (q, x))
    (hA : ∀ (i : ι) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      S.extendedGenerator (psi i) q x t = A i (q, x))
    (hgen : ∀ (i : ι) (z : Q × EuclideanSpace ℝ (Fin n)),
      D.gen i z = @inner ℝ _ _ ((psi i).grad_x z.1 z.2 t₀) (S.f z.1 z.2 t₀)
        + (psi i).partial_t z.1 z.2 t₀)
    (hgen_meas : ∀ i, Measurable (D.gen i))
    (hgen_le : ∀ (i : ι) (z : Q × EuclideanSpace ℝ (Fin n)), |D.gen i z| ≤ genBound i)
    (hK : D.K = S.resetKernelAt t₀ hphi)
    (hlam_le : ∀ z : Q × EuclideanSpace ℝ (Fin n), S.levyTotalIntensity z.1 z.2 t₀ ≤ lamBound)
    (hr_eq : ∀ s : ℝ, D.r s = (D.law s).withDensity fun z =>
      ENNReal.ofReal (S.levyTotalIntensity z.1 z.2 t₀)) :
    D.WeakDynkin := by
  refine D.weakDynkin_of_dynkin12 (A := A) (lam := fun z => S.levyTotalIntensity z.1 z.2 t₀)
    (lamBound := lamBound) (genBound := genBound) hX hlaw hgen_meas hgen_le
    (S.measurable_levyTotalIntensity t₀) (fun z => S.levyTotalIntensity_nonneg z.1 z.2 t₀)
    hlam_le hr_eq (fun i z => ?_) (fun i t ht => ?_)
  · -- the Lévy-system splitting of the extended generator
    have hlevy := S.extendedGenerator_eq_levy (psi i) z.1 z.2 t₀
    have hker : (∫ y, D.ev i y ∂(D.K z))
        = ∫ y, (psi i).toFun y.1 y.2 t₀ ∂(S.resetKernel z.1 z.2 t₀) := by
      rw [hK]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hev i y.1 y.2 t₀).symm)
    rw [← hA i z.1 z.2 t₀, hlevy, hgen i z, GSHS.FPKData.jumpIntegrand, hker,
      hev i z.1 z.2 t₀]
  · exact dynkin12_of_davis S hflow hf hrr hli hne R (psi i) (hpsi_reg i) (hcomp i)
      (htrue i) (hev i) (hA i) ht

/-- **The law of a concrete SHS is a weak solution of the generalized FPK equation.**

Combining `SHS.weakDynkin_of_davis` (Eq. (13) for the Davis realization of a
time-homogeneous Hespanha SHS) with Theorem 8, direction (a)+(b) ⇒ (c): if in addition
the two terms of the right-hand side of (13) are right-continuous in time and
`t ↦ μ_t φ` is right-differentiable with derivative `μ'_t φ`, then the laws of the state
process solve the generalized FPK equation (14) in the weak sense of Definition 7. -/
theorem isWeakFPKSolution_of_davis
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hrr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hrr)
    (R : DavisProcessRealization S hflow hf hrr hli hne)
    {ι : Type*} (psi : ι → TestFunction Q n)
    (hpsi_reg : ∀ i, DavisTestFunctionRegular S hflow hf hrr hli hne R (psi i))
    (hcomp : ∀ i, DavisCompensatorData S hflow hf hrr hli hne R (psi i))
    (htrue : ∀ i, DavisTrueMartingaleData S hflow hf hrr hli hne R (psi i))
    (D : GSHS.FPKData (Q × EuclideanSpace ℝ (Fin n)) ι)
    (mu' : ℝ → GSHS.SignedFin (Q × EuclideanSpace ℝ (Fin n)))
    (t₀ : ℝ) (hphi : ∀ ℓ, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      S.phi ℓ z.1 z.2 t₀)
    {A : ι → Q × EuclideanSpace ℝ (Fin n) → ℝ} {genBound : ι → ℝ} {lamBound : ℝ}
    (hX : Measurable (Function.uncurry R.stateProc))
    (hlaw : ∀ s : ℝ, R.P.map (R.stateProc s) = D.law s)
    (hev : ∀ (i : ι) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      (psi i).toFun q x t = D.ev i (q, x))
    (hA : ∀ (i : ι) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      S.extendedGenerator (psi i) q x t = A i (q, x))
    (hgen : ∀ (i : ι) (z : Q × EuclideanSpace ℝ (Fin n)),
      D.gen i z = @inner ℝ _ _ ((psi i).grad_x z.1 z.2 t₀) (S.f z.1 z.2 t₀)
        + (psi i).partial_t z.1 z.2 t₀)
    (hgen_meas : ∀ i, Measurable (D.gen i))
    (hgen_le : ∀ (i : ι) (z : Q × EuclideanSpace ℝ (Fin n)), |D.gen i z| ≤ genBound i)
    (hK : D.K = S.resetKernelAt t₀ hphi)
    (hlam_le : ∀ z : Q × EuclideanSpace ℝ (Fin n), S.levyTotalIntensity z.1 z.2 t₀ ≤ lamBound)
    (hr_eq : ∀ s : ℝ, D.r s = (D.law s).withDensity fun z =>
      ENNReal.ofReal (S.levyTotalIntensity z.1 z.2 t₀))
    (hgen_rc : ∀ (i : ι) (t : ℝ), 0 ≤ t →
      ContinuousWithinAt (fun s => D.genPair s i) (Set.Ici t) t)
    (hjump_rc : ∀ (i : ι) (t : ℝ), 0 ≤ t →
      ContinuousWithinAt (fun s => D.jumpPair s i) (Set.Ici t) t)
    (hderiv : ∀ (i : ι) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun s => D.lawPair s i) ((mu' t).pair (D.ev i)) (Set.Ici t) t) :
    D.IsWeakFPKSolution mu' :=
  D.isWeakFPKSolution_of_weakDynkin (lamBound := lamBound) (genBound := genBound) hX mu'
    hlaw hgen_meas hgen_le (S.measurable_levyTotalIntensity t₀)
    (fun z => S.levyTotalIntensity_nonneg z.1 z.2 t₀) hlam_le hr_eq
    (weakDynkin_of_davis S hflow hf hrr hli hne R psi hpsi_reg hcomp htrue D t₀ hphi
      (A := A) (genBound := genBound) (lamBound := lamBound) hX (fun s _ => hlaw s) hev hA
      hgen hgen_meas hgen_le hK hlam_le hr_eq)
    hgen_rc hjump_rc hderiv

/-! ### The FPK data of a concrete SHS -/

/-- **The data of the generalized FPK equation for a concrete SHS.**  Given a Davis
realization `R` of a Hespanha SHS `S` and a family `ψ` of test functions, this packages
Bect's ingredients: the test functions and the drift part of the generator evaluated at
the clock value `t₀`, the laws `μ_s` of the state process, the reset kernel `K` of
Eq. (31) and the mean jump intensity `r_s = λ μ_s` of Eq. (8). -/
def davisFPKData
    (S : SHS Q n m) {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hrr : DavisResetRegular S}
    [S.IntensitiesMeasurable] {hli : DavisLocallyIntegrable S hflow}
    {hne : DavisNonExplosive S hflow hf hrr}
    (R : DavisProcessRealization S hflow hf hrr hli hne)
    {ι : Type*} (psi : ι → TestFunction Q n)
    (t₀ : ℝ) (hphi : ∀ ℓ, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      S.phi ℓ z.1 z.2 t₀)
    (evBound : ι → ℝ) {lamBound : ℝ}
    (hX : ∀ s : ℝ, Measurable (R.stateProc s))
    (hev_meas : ∀ i, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      (psi i).toFun z.1 z.2 t₀)
    (hev_le : ∀ (i : ι) (z : Q × EuclideanSpace ℝ (Fin n)),
      |(psi i).toFun z.1 z.2 t₀| ≤ evBound i)
    (hlam_le : ∀ z : Q × EuclideanSpace ℝ (Fin n), S.levyTotalIntensity z.1 z.2 t₀ ≤ lamBound) :
    GSHS.FPKData (Q × EuclideanSpace ℝ (Fin n)) ι where
  ev i z := (psi i).toFun z.1 z.2 t₀
  gen i z := @inner ℝ _ _ ((psi i).grad_x z.1 z.2 t₀) (S.f z.1 z.2 t₀)
    + (psi i).partial_t z.1 z.2 t₀
  law s := R.P.map (R.stateProc s)
  r s := (R.P.map (R.stateProc s)).withDensity fun z =>
    ENNReal.ofReal (S.levyTotalIntensity z.1 z.2 t₀)
  K := S.resetKernelAt t₀ hphi
  markov := inferInstance
  ev_measurable := hev_meas
  ev_bound := evBound
  ev_le := hev_le
  law_isProbabilityMeasure s := Measure.isProbabilityMeasure_map (hX s).aemeasurable
  r_isFiniteMeasure s := by
    haveI : IsProbabilityMeasure (R.P.map (R.stateProc s)) :=
      Measure.isProbabilityMeasure_map (hX s).aemeasurable
    refine isFiniteMeasure_withDensity ?_
    have hle : (∫⁻ z, ENNReal.ofReal (S.levyTotalIntensity z.1 z.2 t₀) ∂(R.P.map (R.stateProc s)))
        ≤ ∫⁻ _, ENNReal.ofReal lamBound ∂(R.P.map (R.stateProc s)) :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hlam_le z)
    simp only [lintegral_const, measure_univ, mul_one] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- **Eq. (13) for the FPK data of a concrete SHS.**  For a time-homogeneous system —
test functions independent of the clock coordinate (`hpsi_time`) and likewise for the
extended generator (`hgen_time`) — the laws of the state process satisfy the generalized
Dynkin formula (13), the standing hypothesis of Theorem 8. -/
theorem weakDynkin_davisFPKData
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hrr : DavisResetRegular S)
    [S.IntensitiesMeasurable] (hli : DavisLocallyIntegrable S hflow)
    (hne : DavisNonExplosive S hflow hf hrr)
    (R : DavisProcessRealization S hflow hf hrr hli hne)
    {ι : Type*} (psi : ι → TestFunction Q n)
    (hpsi_reg : ∀ i, DavisTestFunctionRegular S hflow hf hrr hli hne R (psi i))
    (hcomp : ∀ i, DavisCompensatorData S hflow hf hrr hli hne R (psi i))
    (htrue : ∀ i, DavisTrueMartingaleData S hflow hf hrr hli hne R (psi i))
    (t₀ : ℝ) (hphi : ∀ ℓ, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      S.phi ℓ z.1 z.2 t₀)
    (evBound : ι → ℝ) {genBound : ι → ℝ} {lamBound : ℝ}
    (hXjoint : Measurable (Function.uncurry R.stateProc))
    (hX : ∀ s : ℝ, Measurable (R.stateProc s))
    (hev_meas : ∀ i, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      (psi i).toFun z.1 z.2 t₀)
    (hev_le : ∀ (i : ι) (z : Q × EuclideanSpace ℝ (Fin n)),
      |(psi i).toFun z.1 z.2 t₀| ≤ evBound i)
    (hlam_le : ∀ z : Q × EuclideanSpace ℝ (Fin n), S.levyTotalIntensity z.1 z.2 t₀ ≤ lamBound)
    (hgen_meas : ∀ i, Measurable fun z : Q × EuclideanSpace ℝ (Fin n) =>
      @inner ℝ _ _ ((psi i).grad_x z.1 z.2 t₀) (S.f z.1 z.2 t₀)
        + (psi i).partial_t z.1 z.2 t₀)
    (hgen_le : ∀ (i : ι) (z : Q × EuclideanSpace ℝ (Fin n)),
      |@inner ℝ _ _ ((psi i).grad_x z.1 z.2 t₀) (S.f z.1 z.2 t₀)
        + (psi i).partial_t z.1 z.2 t₀| ≤ genBound i)
    (hpsi_time : ∀ (i : ι) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      (psi i).toFun q x t = (psi i).toFun q x t₀)
    (hgen_time : ∀ (i : ι) (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      S.extendedGenerator (psi i) q x t = S.extendedGenerator (psi i) q x t₀) :
    (davisFPKData S R psi t₀ hphi evBound (lamBound := lamBound) hX hev_meas hev_le
      hlam_le).WeakDynkin :=
  weakDynkin_of_davis S hflow hf hrr hli hne R psi hpsi_reg hcomp htrue _ t₀ hphi
    (A := fun i z => S.extendedGenerator (psi i) z.1 z.2 t₀)
    (genBound := genBound) (lamBound := lamBound) hXjoint (fun _ _ => rfl)
    hpsi_time hgen_time
    (fun _ _ => rfl) hgen_meas hgen_le rfl hlam_le (fun _ => rfl)

end SHS
