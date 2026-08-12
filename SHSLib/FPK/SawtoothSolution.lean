/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sawtooth process with uniform initial law solves the generalized FPK equation

`SHSLib.FPK.SawtoothExample` studies the process of Section 3.2 of Bect (2010) — motion
at constant speed `v > 0` on `E = [0;1]`, with a forced jump back to `0` at the guard
`G = {1}` — and shows that, started from the uniform law, it admits the mean jump
intensity `r_t = v δ₁` (Eq. (8)).

This file completes that example into a fully verified solution of the generalized FPK
equation: the uniform law is stationary, and Definition 7 holds with `μ'_t = 0`,

  `0 = L^* μ_t + r_t(K − I)`,

the transport term `(L^* μ_t)(φ) = ∫₀¹ v φ'(x) dx = v(φ(1) − φ(0))` being exactly
compensated by the forced-jump term `r_t(K − I)φ = v(φ(0) − φ(1))`, with `K(x, ·) = δ₀`.
This is the measure-valued form of the "probability current" picture of Section 4.2: the
mass leaving the state space at the guard `x = 1` re-enters it at `x = 0`.

Main results:

* `GSHS.Sawtooth.uniformData` — the model as an instance of `GSHS.FPKData`;
* `GSHS.Sawtooth.uniformData_weakDynkin` — the generalized Dynkin formula (13);
* `GSHS.Sawtooth.uniformData_isWeakFPKSolution` — Definition 7 with `μ'_t = 0`.
-/
import SHSLib.FPK.GeneralizedFPK
import SHSLib.FPK.SawtoothExample

open MeasureTheory Set ProbabilityTheory intervalIntegral
open scoped ENNReal

noncomputable section

namespace GSHS.Sawtooth

/-- A bounded `C¹` test function on the line, together with its derivative. -/
structure Test where
  /-- The test function itself. -/
  fn : ℝ → ℝ
  /-- Its derivative. -/
  der : ℝ → ℝ
  /-- `der` really is the derivative of `fn`. -/
  hasDeriv : ∀ x, HasDerivAt fn (der x) x
  /-- The derivative is continuous, so `fn ∈ C¹`. -/
  cont_der : Continuous der
  /-- A bound for the test function. -/
  bound : ℝ
  /-- `fn` is bounded by `bound`. -/
  fn_le : ∀ x, |fn x| ≤ bound

/-- The uniform law on `[0;1]`, the (stationary) law of the sawtooth process. -/
def uniformLaw : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure uniformLaw := by
  constructor
  simp [uniformLaw]

/-- The mean jump intensity `r_t = v δ₁` of the sawtooth process started from the
uniform law (Eq. (8); see `GSHS.Sawtooth.meanJumpIntensity_uniform`). -/
def guardIntensity (v : ℝ) : Measure ℝ := ENNReal.ofReal v • Measure.dirac (1 : ℝ)

instance (v : ℝ) : IsFiniteMeasure (guardIntensity v) := by
  constructor
  simp [guardIntensity, Measure.smul_apply]

theorem integral_guardIntensity {v : ℝ} (hv : 0 ≤ v) (f : ℝ → ℝ) :
    ∫ x, f x ∂(guardIntensity v) = v * f 1 := by
  rw [guardIntensity, MeasureTheory.integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal hv]
  simp

/-- The reset kernel of the sawtooth process: from the guard, the state is sent back to
`0`. -/
def resetKernel : Kernel ℝ ℝ := Kernel.deterministic (fun _ : ℝ => (0 : ℝ)) measurable_const

instance : IsMarkovKernel resetKernel := by
  rw [resetKernel]; infer_instance

theorem integral_resetKernel (f : ℝ → ℝ) (x : ℝ) : ∫ y, f y ∂(resetKernel x) = f 0 := by
  rw [resetKernel, Kernel.deterministic_apply, integral_dirac]

/-- The sawtooth process with uniform initial law, as data for the generalized FPK
equation: the differential generator is the transport operator `Lφ = v φ'`, the law is
uniform at all times, the mean jump intensity is `r_t = v δ₁` and the reset kernel sends
the guard back to `0`. -/
def uniformData (v : ℝ) : FPKData ℝ Test where
  ev := fun phi => phi.fn
  gen := fun phi x => v * phi.der x
  law := fun _ => uniformLaw
  r := fun _ => guardIntensity v
  K := resetKernel
  markov := inferInstance
  ev_measurable := fun phi =>
    (Continuous.measurable (by
      have : Differentiable ℝ phi.fn := fun x => (phi.hasDeriv x).differentiableAt
      exact this.continuous))
  ev_bound := fun phi => phi.bound
  ev_le := fun phi x => phi.fn_le x
  law_isProbabilityMeasure := fun _ => inferInstance
  r_isFiniteMeasure := fun _ => inferInstance

variable {v : ℝ}

theorem uniformData_lawPair (t : ℝ) (phi : Test) :
    (uniformData v).lawPair t phi = ∫ x in Icc (0 : ℝ) 1, phi.fn x := by
  rfl

/-- The transport term: `(L^* μ_t)(φ) = ∫₀¹ v φ'(x) dx = v (φ(1) − φ(0))`, by the
fundamental theorem of calculus. -/
theorem uniformData_genPair (t : ℝ) (phi : Test) :
    (uniformData v).genPair t phi = v * (phi.fn 1 - phi.fn 0) := by
  have hcont : Continuous fun x => v * phi.der x := continuous_const.mul phi.cont_der
  have h1 : (uniformData v).genPair t phi = ∫ x in Ioc (0 : ℝ) 1, v * phi.der x := by
    simp only [FPKData.genPair, uniformData, uniformLaw]
    exact integral_Icc_eq_integral_Ioc
  have h2 : ∫ x in (0 : ℝ)..1, v * phi.der x = v * (phi.fn 1 - phi.fn 0) := by
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun y => v * phi.fn y) (v * phi.der x) x :=
      fun x _ => (phi.hasDeriv x).const_mul v
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable 0 1)]
    ring
  rw [h1, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), h2]

/-- The forced-jump term: `r_t(K − I)φ = v (φ(0) − φ(1))`. -/
theorem uniformData_jumpPair (hv : 0 ≤ v) (t : ℝ) (phi : Test) :
    (uniformData v).jumpPair t phi = v * (phi.fn 0 - phi.fn 1) := by
  simp only [FPKData.jumpPair, uniformData]
  rw [integral_guardIntensity hv]
  simp only [integral_resetKernel]

/-- The transport term and the forced-jump term cancel: the uniform law is stationary
for the sawtooth process. -/
theorem uniformData_balance (hv : 0 ≤ v) (t : ℝ) (phi : Test) :
    (uniformData v).genPair t phi + (uniformData v).jumpPair t phi = 0 := by
  rw [uniformData_genPair t phi, uniformData_jumpPair hv t phi]
  ring

/-- The zero derivative `μ'_t = 0`. -/
def zeroDeriv : SignedFin ℝ where
  pos := 0
  neg := 0
  pos_isFiniteMeasure := inferInstance
  neg_isFiniteMeasure := inferInstance

theorem zeroDeriv_pair (f : ℝ → ℝ) : zeroDeriv.pair f = 0 := by
  simp [SignedFin.pair, zeroDeriv]

/-- **The generalized Dynkin formula (13)** for the sawtooth process with uniform
initial law: both sides vanish, the transport and forced-jump contributions cancelling
at every time. -/
theorem uniformData_weakDynkin (hv : 0 ≤ v) : (uniformData v).WeakDynkin := by
  intro phi t ht
  have hgen : ∫ s in (0 : ℝ)..t, (uniformData v).genPair s phi
      = t * (v * (phi.fn 1 - phi.fn 0)) := by
    simp only [uniformData_genPair]
    simp
    ring
  have hjump : ∫ s in (0 : ℝ)..t, (uniformData v).jumpPair s phi
      = t * (v * (phi.fn 0 - phi.fn 1)) := by
    simp only [uniformData_jumpPair hv]
    simp
    ring
  rw [hgen, hjump, uniformData_lawPair t phi, uniformData_lawPair 0 phi]
  ring

/-- The measure `r_t` used in `GSHS.Sawtooth.uniformData` is not an ad hoc choice: it is
the mean jump intensity of Definition 6 for this process, as established in
`GSHS.Sawtooth.meanJumpIntensity_uniform` from the jump measure (7). -/
theorem uniformData_r_isMeanJumpIntensity (hv : 0 < v) :
    MeanJumpIntensity (jumpMeasure v (volume.restrict (Ioo (0 : ℝ) 1)))
      (fun t => (uniformData v).r t) :=
  meanJumpIntensity_uniform hv

/-! ### The example is not vacuous -/

/-- `sin` is a bounded `C¹` test function, so the class `GSHS.Sawtooth.Test` is not
empty. -/
def sinTest : Test where
  fn := Real.sin
  der := Real.cos
  hasDeriv := Real.hasDerivAt_sin
  cont_der := Real.continuous_cos
  bound := 1
  fn_le := Real.abs_sin_le_one

/-- Tested against `sin`, both the transport term and the forced-jump term are nonzero
(for `v > 0`): the balance `L^*μ_t + r_t(K − I) = 0` of the sawtooth process is a
cancellation of two nonvanishing contributions, not a triviality. -/
theorem genPair_sinTest_pos (hv : 0 < v) : 0 < (uniformData v).genPair 0 sinTest := by
  have h1 : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hsin : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi (by norm_num) h1
  rw [uniformData_genPair]
  have : sinTest.fn 1 - sinTest.fn 0 = Real.sin 1 := by simp [sinTest]
  rw [this]
  positivity

/-- **Definition 7** for the sawtooth process with uniform initial law: `t ↦ μ_t` (the
constant uniform law) solves the generalized FPK equation with `μ'_t = 0`.  The content
of the equation is the exact compensation of the transport term `(L^*μ_t)(φ)` by the
forced-jump term `r_t(K − I)φ`. -/
theorem uniformData_isWeakFPKSolution (hv : 0 ≤ v) :
    (uniformData v).IsWeakFPKSolution (fun _ => zeroDeriv) where
  hasDeriv := by
    intro phi t ht
    have hconst : (fun s => (uniformData v).lawPair s phi)
        = fun _ : ℝ => ∫ x in Icc (0 : ℝ) 1, phi.fn x := by
      funext s
      exact uniformData_lawPair s phi
    rw [hconst, zeroDeriv_pair]
    exact (hasDerivAt_const t _).hasDerivWithinAt
  fpk := by
    intro phi t ht
    rw [zeroDeriv_pair, ← uniformData_balance hv t phi]

end GSHS.Sawtooth
