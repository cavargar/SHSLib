import SHSLib.Gardiner.Ito.WienerIntegral

/-!
# Instances of the simple and Wiener integrals for the standard Wiener process

* `Gardiner.Ito.simpleExample`: the simple nonanticipating integrand `G(s) = (W(1) - W(0)) 1_{(1,2]}(s)`
  for `W = stdWiener`; its integral `(W(1) - W(0))(W(2) - W(1))` has mean `0` and second moment `1`
  (`Gardiner.Ito.simpleExample_moments`), and its running integral is a martingale
  (`Gardiner.Ito.simpleExample_martingale`).
* `Gardiner.Ito.wienerInt_id_stdWiener`: `∫₀¹ s dW(s) ~ N(0, 1/3)` and
  `∫₀¹ s dW(s) = W(1) - ∫₀¹ W(s) ds` almost surely.
-/

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Gardiner.Ito

/-- The simple integrand `G(s) = (W(1) - W(0)) 1_{(1,2]}(s)` for the standard Wiener process. -/
def simpleExample : SimpleIntegrand stdWiener isWiener_stdWiener.measurable stdWienerMeasure (Fin 1)
    where
  left _ := 1
  right _ := 2
  val _ := fun ω => stdWiener 1 ω - stdWiener 0 ω
  left_nonneg _ := zero_le_one
  left_le_right _ := by norm_num
  adapted _ := isWiener_stdWiener.sm_incr le_rfl zero_le_one le_rfl
  memLp _ := isWiener_stdWiener.memLp_incr le_rfl zero_le_one

/-- **Instance of (4.2.40)–(4.2.44)**: `∫ G dW = (W(1) - W(0))(W(2) - W(1))` has mean `0` and
second moment `∫ ds ⟨G(s)²⟩ = 1`. -/
theorem simpleExample_moments :
    (∀ ω, simpleExample.integral ω =
      (stdWiener 1 ω - stdWiener 0 ω) * (stdWiener 2 ω - stdWiener 1 ω)) ∧
    ∫ ω, simpleExample.integral ω ∂stdWienerMeasure = 0 ∧
    ∫ ω, simpleExample.integral ω ^ 2 ∂stdWienerMeasure = 1 := by
  refine ⟨fun ω => by simp [simpleExample, SimpleIntegrand.integral],
    SimpleIntegrand.integral_mean isWiener_stdWiener _, ?_⟩
  simp_rw [sq]
  rw [SimpleIntegrand.integral_mul_eq_sum isWiener_stdWiener]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  simp only [simpleExample, ← sq]
  rw [isWiener_stdWiener.integral_incr_sq le_rfl zero_le_one]
  simp [overlap]
  norm_num

/-- **Instance of the martingale property**: the running integral of `G` is a martingale for the
natural filtration of the standard Wiener process. -/
theorem simpleExample_martingale :
    Martingale simpleExample.running (wienerFiltration stdWiener isWiener_stdWiener.measurable)
      stdWienerMeasure :=
  SimpleIntegrand.martingale_running isWiener_stdWiener _

/-- **Instance of the Wiener integral**: `∫₀¹ s dW(s) ~ N(0, 1/3)`, and
`∫₀¹ s dW(s) = W(1) - ∫₀¹ W(s) ds` almost surely (integration by parts). -/
theorem wienerInt_id_stdWiener :
    stdWienerMeasure.map (wienerInt stdWiener stdWienerMeasure (fun s => s) 0 1) =
      gaussianReal 0 (1 / 3 : ℝ).toNNReal ∧
    wienerInt stdWiener stdWienerMeasure (fun s => s) 0 1 =ᵐ[stdWienerMeasure]
      fun ω => stdWiener 1 ω - ∫ s in (0 : ℝ)..1, stdWiener s ω := by
  constructor
  · rw [isWiener_stdWiener.wienerInt_map (f := fun s => s) continuous_id le_rfl zero_le_one]
    congr 2
    rw [integral_pow]
    norm_num
  · have h := isWiener_stdWiener.wienerInt_ibp (f := fun s => s) (f' := fun _ => 1) (a := 0)
      (b := 1) (fun s => hasDerivAt_id s) continuous_const le_rfl zero_le_one
    refine h.trans (Eventually.of_forall fun ω => ?_)
    simp

end Gardiner.Ito
