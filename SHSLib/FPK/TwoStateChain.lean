/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A concrete solution of the generalized FPK equation: the symmetric two-state chain

The framework of Section 4 of Bect (2010) — the data `GSHS.FPKData`, the generalized
Dynkin formula (13) (`GSHS.FPKData.WeakDynkin`) and Definition 7
(`GSHS.FPKData.IsWeakFPKSolution`) — is instantiated here on the simplest nontrivial
example of Example 16: the symmetric continuous-time Markov chain on two states, with
jump rate `λ ≥ 0` and reset kernel `K(x, ·) = δ_{¬x}`.

There is no continuous dynamics (`L = 0`), the law started from the state `false` is

  `μ_t = q_t δ_false + (1 − q_t) δ_true`,   `q_t = (1 + e^{−2λt})/2`,

the mean jump intensity of Definition 6 is `r_t = λ μ_t`, and the FPK equation (14)
reduces to the master equation `q̇_t = λ(1 − q_t) − λ q_t`.

Main results:

* `GSHS.chainData` — the model as an instance of `GSHS.FPKData`;
* `GSHS.chainData_weakDynkin` — the generalized Dynkin formula (13) holds;
* `GSHS.chainData_isWeakFPKSolution` — `t ↦ μ_t` solves the generalized FPK equation in
  the sense of Definition 7, with derivative `μ'_t = λ e^{−2λt} (δ_true − δ_false)`.

In particular the hypotheses of Theorem 8 are satisfiable: the definitions of the
general theory are not vacuous.
-/
import SHSLib.FPK.GeneralizedFPK
import SHSLib.FPK.SpontaneousJumps

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GSHS

/-! ## Measures on a two-point space -/

/-- The measure `u δ_false + v δ_true` on `Bool`. -/
def twoPoint (u v : ℝ) : Measure Bool :=
  ENNReal.ofReal u • Measure.dirac false + ENNReal.ofReal v • Measure.dirac true

instance smulDiracFinite (c : ℝ) (b : Bool) :
    IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac b) := by
  constructor
  simp [Measure.smul_apply]

instance twoPointFinite (u v : ℝ) : IsFiniteMeasure (twoPoint u v) := by
  rw [twoPoint]; infer_instance

theorem integral_twoPoint {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (f : Bool → ℝ) :
    ∫ x, f x ∂(twoPoint u v) = u * f false + v * f true := by
  rw [twoPoint, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp [ENNReal.toReal_ofReal hu, ENNReal.toReal_ofReal hv]

theorem twoPoint_isProbabilityMeasure {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u + v = 1) :
    IsProbabilityMeasure (twoPoint u v) := by
  constructor
  simp [twoPoint, Measure.add_apply, Measure.smul_apply, ← ENNReal.ofReal_add hu hv, h]

theorem twoPoint_smul {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    ENNReal.ofReal c • twoPoint u v = twoPoint (c * u) (c * v) := by
  simp only [twoPoint, smul_add, smul_smul, ENNReal.ofReal_mul hc]

/-! ## The symmetric two-state chain -/

/-- The reset kernel of the two-state chain: a jump flips the state. -/
def flipKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun b => !b) (measurable_of_countable _)

instance : IsMarkovKernel flipKernel := by
  rw [flipKernel]; infer_instance

theorem integral_flipKernel (f : Bool → ℝ) (x : Bool) :
    ∫ y, f y ∂(flipKernel x) = f (!x) := by
  rw [flipKernel, Kernel.deterministic_apply, integral_dirac]

/-- `q_t = (1 + e^{−2λt})/2`, the probability of being in the initial state at time `t`
(frozen at its value `1` for negative times, so that `μ_t` is a probability measure for
every real `t`). -/
def chainProb (lam t : ℝ) : ℝ := (1 + Real.exp (-(2 * lam * max t 0))) / 2

theorem chainProb_nonneg (lam t : ℝ) : 0 ≤ chainProb lam t := by
  have := (Real.exp_pos (-(2 * lam * max t 0))).le
  simp only [chainProb]
  linarith

theorem chainProb_le_one {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) : chainProb lam t ≤ 1 := by
  have hmax : 0 ≤ max t 0 := le_max_right _ _
  have : Real.exp (-(2 * lam * max t 0)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 2 * lam * max t 0 := by positivity
    linarith
  simp only [chainProb]
  linarith

theorem chainProb_of_nonneg {lam t : ℝ} (ht : 0 ≤ t) :
    chainProb lam t = (1 + Real.exp (-(2 * lam * t))) / 2 := by
  rw [chainProb, max_eq_left ht]

theorem chainProb_zero (lam : ℝ) : chainProb lam 0 = 1 := by
  simp [chainProb]

/-- The law `μ_t = q_t δ_false + (1 − q_t) δ_true` of the chain started at `false`. -/
def chainLaw (lam t : ℝ) : Measure Bool :=
  twoPoint (chainProb lam t) (1 - chainProb lam t)

/-- The mean jump intensity `r_t = λ μ_t` of Definition 6 (Eq. (8)). -/
def chainIntensity (lam t : ℝ) : Measure Bool :=
  twoPoint (lam * chainProb lam t) (lam * (1 - chainProb lam t))

/-- The two-state chain as data for the generalized FPK equation: no continuous
dynamics (`Lφ = 0`), law `μ_t`, mean jump intensity `r_t = λ μ_t` and reset kernel
`K(x, ·) = δ_{¬x}`. -/
def chainData (lam : ℝ) (hlam : 0 ≤ lam) : FPKData Bool (Bool → ℝ) where
  ev := id
  gen := fun _ _ => 0
  law := chainLaw lam
  r := chainIntensity lam
  K := flipKernel
  markov := inferInstance
  ev_measurable := fun _ => measurable_of_countable _
  ev_bound := fun phi => |phi false| + |phi true|
  ev_le := by
    intro phi x
    cases x with
    | false => have := abs_nonneg (phi true); simp only [id]; linarith
    | true => have := abs_nonneg (phi false); simp only [id]; linarith
  law_isProbabilityMeasure := fun t =>
    twoPoint_isProbabilityMeasure (chainProb_nonneg lam t)
      (by linarith [chainProb_le_one hlam t]) (by ring)
  r_isFiniteMeasure := fun _ => by rw [chainIntensity]; infer_instance

/-- **Eq. (8)** for the two-state chain: the mean jump intensity used in
`GSHS.chainData` is `r_t = λ μ_t`, the intensity of Definition 6 for spontaneous jumps
with constant stochastic intensity `λ`. -/
theorem chainIntensity_eq_withDensity {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) :
    chainIntensity lam t = (chainLaw lam t).withDensity (fun _ => ENNReal.ofReal lam) := by
  rw [withDensity_const, chainLaw, twoPoint_smul hlam, chainIntensity]

/-! ### The pairings of the model -/

theorem chainData_lawPair (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ) (phi : Bool → ℝ) :
    (chainData lam hlam).lawPair t phi
      = chainProb lam t * phi false + (1 - chainProb lam t) * phi true := by
  simp only [FPKData.lawPair, chainData, chainLaw, id]
  exact integral_twoPoint (chainProb_nonneg lam t)
    (by linarith [chainProb_le_one hlam t]) phi

theorem chainData_genPair (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ) (phi : Bool → ℝ) :
    (chainData lam hlam).genPair t phi = 0 := by
  simp [FPKData.genPair, chainData]

theorem chainData_jumpPair (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ) (phi : Bool → ℝ) :
    (chainData lam hlam).jumpPair t phi
      = lam * Real.exp (-(2 * lam * max t 0)) * (phi true - phi false) := by
  have hq : 0 ≤ chainProb lam t := chainProb_nonneg lam t
  have hq' : chainProb lam t ≤ 1 := chainProb_le_one hlam t
  simp only [FPKData.jumpPair, chainData, chainIntensity, id]
  rw [integral_twoPoint (by positivity) (by nlinarith) _]
  simp only [integral_flipKernel]
  simp only [Bool.not_false, Bool.not_true, chainProb]
  ring

/-! ### Assumption 14 and Corollary 15 for the chain -/

/-- The law of the chain has a density with respect to the counting measure on the two
states: `μ_t = p_t · #`, with `p_t(false) = q_t` and `p_t(true) = 1 − q_t`. -/
theorem twoPoint_eq_withDensity_count (u v : ℝ) :
    twoPoint u v
      = Measure.count.withDensity
          (fun b => if b then ENNReal.ofReal v else ENNReal.ofReal u) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_count, tsum_bool]
  simp only [twoPoint, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]
  by_cases h1 : (false : Bool) ∈ s <;> by_cases h2 : (true : Bool) ∈ s <;>
    simp [h1, h2, Set.indicator_of_mem, Set.indicator_of_notMem]

/-- **Assumption 14** for the two-state chain: the reset kernel `K(x, ·) = δ_{¬x}` is
self-dual with respect to the counting measure, `K^* = K`.  Hence Corollary 15 applies:
the source term of the FPK equation has density `K^*(λ p_t)`, and the FPK equation is
the master equation of the chain. -/
theorem isDualKernel_flipKernel :
    IsDualKernel (Measure.count : Measure Bool) flipKernel flipKernel := by
  intro f hf
  have h : ∀ (g : Bool → ℝ≥0∞) (x : Bool), ∫⁻ y, g y ∂(flipKernel x) = g (!x) := by
    intro g x
    rw [flipKernel, Kernel.deterministic_apply, lintegral_dirac]
  rw [lintegral_count, lintegral_count, tsum_bool, tsum_bool,
    h (fun y => f false y) false, h (fun y => f true y) true,
    h (fun x => f x false) false, h (fun x => f x true) true]
  simp [add_comm]

/-! ### The time derivative `μ'_t` -/

/-- The derivative `μ'_t = λ e^{−2λt} (δ_true − δ_false)` of the law of the chain. -/
def chainDeriv (lam t : ℝ) : SignedFin Bool where
  pos := twoPoint 0 (lam * Real.exp (-(2 * lam * t)))
  neg := twoPoint (lam * Real.exp (-(2 * lam * t))) 0
  pos_isFiniteMeasure := inferInstance
  neg_isFiniteMeasure := inferInstance

theorem chainDeriv_pair {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (phi : Bool → ℝ) :
    (chainDeriv lam t).pair phi
      = lam * Real.exp (-(2 * lam * t)) * (phi true - phi false) := by
  have hpos : 0 ≤ lam * Real.exp (-(2 * lam * t)) := by positivity
  simp only [SignedFin.pair, chainDeriv]
  rw [integral_twoPoint le_rfl hpos, integral_twoPoint hpos le_rfl]
  ring

/-- Differentiability of `t ↦ μ_t φ` for `t ≥ 0`, with derivative `μ'_t φ`. -/
theorem chainData_hasDerivWithinAt (lam : ℝ) (hlam : 0 ≤ lam) (phi : Bool → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => (chainData lam hlam).lawPair s phi)
      ((chainDeriv lam t).pair phi) (Ici t) t := by
  have hfun : ∀ s : ℝ, 0 ≤ s → (chainData lam hlam).lawPair s phi
      = ((1 + Real.exp (-(2 * lam * s))) / 2) * phi false
        + (1 - (1 + Real.exp (-(2 * lam * s))) / 2) * phi true := by
    intro s hs
    rw [chainData_lawPair lam hlam s phi, chainProb_of_nonneg hs]
  have hbase : HasDerivAt (fun s : ℝ => Real.exp (-(2 * lam * s)))
      (-(2 * lam) * Real.exp (-(2 * lam * t))) t := by
    have h1 : HasDerivAt (fun s : ℝ => -(2 * lam * s)) (-(2 * lam)) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * lam)).neg
    simpa [mul_comm] using h1.exp
  have hderiv : HasDerivAt
      (fun s : ℝ => ((1 + Real.exp (-(2 * lam * s))) / 2) * phi false
        + (1 - (1 + Real.exp (-(2 * lam * s))) / 2) * phi true)
      ((chainDeriv lam t).pair phi) t := by
    have h2 := ((hbase.const_add 1).div_const 2).mul_const (phi false)
    have h3 := (((hbase.const_add 1).div_const 2).const_sub 1).mul_const (phi true)
    have h := h2.add h3
    rw [chainDeriv_pair hlam t phi]
    convert h using 1
    ring
  refine (hderiv.hasDerivWithinAt (s := Ici t)).congr (fun s hs => ?_) ?_
  · exact hfun s (le_trans ht hs)
  · exact hfun t ht

/-- **The master equation (27) for the two-state chain**: the density `q_t` of the state
`false` satisfies `q̇_t = λ(1 − q_t) − λ q_t`, the gain from the other state minus the
loss to it (right-derivative, since `q` is frozen for negative times). -/
theorem chainProb_hasDerivWithinAt (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (chainProb lam)
      (lam * (1 - chainProb lam t) - lam * chainProb lam t) (Ici t) t := by
  have hbase : HasDerivAt (fun s : ℝ => Real.exp (-(2 * lam * s)))
      (-(2 * lam) * Real.exp (-(2 * lam * t))) t := by
    have h1 : HasDerivAt (fun s : ℝ => -(2 * lam * s)) (-(2 * lam)) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * lam)).neg
    simpa [mul_comm] using h1.exp
  have hderiv : HasDerivAt (fun s : ℝ => (1 + Real.exp (-(2 * lam * s))) / 2)
      (lam * (1 - chainProb lam t) - lam * chainProb lam t) t := by
    have h := (hbase.const_add 1).div_const 2
    convert h using 1
    rw [chainProb_of_nonneg ht]
    ring
  refine (hderiv.hasDerivWithinAt (s := Ici t)).congr (fun s hs => ?_) ?_
  · exact chainProb_of_nonneg (le_trans ht hs)
  · exact chainProb_of_nonneg ht

/-! ### The two-state chain solves the generalized FPK equation -/

/-- **The generalized Dynkin formula (13)** for the two-state chain: with `Lφ = 0`, the
increment of `μ_t φ` is the time integral of the jump term `r_s(K − I)φ`. -/
theorem chainData_weakDynkin (lam : ℝ) (hlam : 0 ≤ lam) : (chainData lam hlam).WeakDynkin := by
  intro phi t ht
  have hjump : ∀ s ∈ Set.uIcc (0 : ℝ) t, (chainData lam hlam).jumpPair s phi
      = lam * Real.exp (-(2 * lam * s)) * (phi true - phi false) := by
    intro s hs
    have hs0 : 0 ≤ s := by
      rcases Set.mem_uIcc.1 hs with h | h
      · exact h.1
      · exact le_trans ht h.1
    rw [chainData_jumpPair lam hlam s phi, max_eq_left hs0]
  have hG : ∀ s : ℝ, HasDerivAt (fun u : ℝ => (1 - Real.exp (-(2 * lam * u))) / 2)
      (lam * Real.exp (-(2 * lam * s)) * (1 : ℝ)) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => -(2 * lam * u)) (-(2 * lam)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * lam)).neg
    have hbase : HasDerivAt (fun u : ℝ => Real.exp (-(2 * lam * u)))
        (-(2 * lam) * Real.exp (-(2 * lam * s))) s := by
      simpa [mul_comm] using h1.exp
    have := (hbase.const_sub 1).div_const 2
    convert this using 1
    ring
  have hint : ∫ s in (0 : ℝ)..t, (chainData lam hlam).jumpPair s phi
      = ((1 - Real.exp (-(2 * lam * t))) / 2) * (phi true - phi false) := by
    have hcongr : ∫ s in (0 : ℝ)..t, (chainData lam hlam).jumpPair s phi
        = ∫ s in (0 : ℝ)..t, lam * Real.exp (-(2 * lam * s)) * (phi true - phi false) :=
      intervalIntegral.integral_congr hjump
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun u : ℝ => ((1 - Real.exp (-(2 * lam * u))) / 2) * (phi true - phi false))
          (lam * Real.exp (-(2 * lam * s)) * (phi true - phi false)) s := by
      intro s _
      have := (hG s).mul_const (phi true - phi false)
      convert this using 1
      ring
    have hintegrable : IntervalIntegrable
        (fun s => lam * Real.exp (-(2 * lam * s)) * (phi true - phi false)) volume 0 t := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable]
    simp
  rw [chainData_lawPair lam hlam t phi, chainData_lawPair lam hlam 0 phi,
    chainProb_zero, chainProb_of_nonneg ht, hint]
  simp only [chainData_genPair]
  simp only [intervalIntegral.integral_zero]
  ring

/-- **Definition 7** for the two-state chain: `t ↦ μ_t` solves the generalized FPK
equation with derivative `μ'_t = λ e^{−2λt}(δ_true − δ_false)`.  Since `Lφ = 0`, the
equation `μ'_t = L^*μ_t + r_t(K − I)` reduces to the master equation. -/
theorem chainData_isWeakFPKSolution (lam : ℝ) (hlam : 0 ≤ lam) :
    (chainData lam hlam).IsWeakFPKSolution (chainDeriv lam) where
  hasDeriv := fun phi t ht => chainData_hasDerivWithinAt lam hlam phi ht
  fpk := by
    intro phi t ht
    have hev : (chainData lam hlam).ev phi = phi := rfl
    rw [hev, chainDeriv_pair hlam t phi, chainData_genPair lam hlam t phi,
      chainData_jumpPair lam hlam t phi, max_eq_left ht]
    ring

end GSHS
