/-
# The Ornstein–Uhlenbeck process (Gardiner §4.4.4, (4.4.22)–(4.4.31))

`Gardiner.Ito.ouProc k D x0 W t = x(0)e^{-kt} + √D ∫₀ᵗ e^{-k(t-t')} dW(t')` (4.4.26), written
pathwise with the integration-by-parts form of the stochastic integral, which agrees almost surely
with the Wiener integral `Gardiner.Ito.ouInt` (`Gardiner.Ito.IsWiener.ouProc_ae`).

* **Pathwise solution** of `dx = -kx dt + √D dW` (4.4.22): `Gardiner.SDE.IsPathSol` with
  `a(x) = -kx` for every continuous path (`Gardiner.Ito.ouProc_isPathSol`).
* For `x(0) ∈ L²` independent of `W` (`IndepFun x0 (pathMap W) P`): mean (4.4.27)
  (`Gardiner.Ito.IsWiener.ouProc_mean`), variance (4.4.29) (`…ouProc_var`), correlation (4.4.30)
  for `s ≤ t` (`…ouProc_cov`) and in the printed `e^{-k|t-s|}` form (`…ouProc_cov_printed`), second
  moment (`…ouProc_second`); `k ≠ 0`, `D ≥ 0`.
* **Gaussian**: for Gaussian `x(0)` independent of `W`, `x(t)` is Gaussian with the above mean and
  variance (`Gardiner.Ito.IsWiener.ouProc_map`); for deterministic `x(0) = c`,
  `x(t) ~ N(ce^{-kt}, D(1 - e^{-2kt})/2k)` (`…ouProc_map_const`).
* **Stationary limit** (`k > 0`): mean `→ 0`, variance `→ D/2k`, `⟨x(t+τ), x(t)⟩ → (D/2k)e^{-k|τ|}`
  (`Gardiner.Ito.IsWiener.ouProc_stationary`), the moments of the stationary solution (4.4.31).
* **Connection to job D**: for deterministic `x(0) = c`, `⟨x(t)⟩ = Gardiner.SDE.ouMean k c t` and
  `⟨x(t)²⟩ = Gardiner.SDE.ouSecond k √D c t` (`…ouProc_mean_const`, `…ouProc_second_const`), so the
  OU weak-error theorems compare the schemes with the actual OU process driven by the same Wiener
  process (`Gardiner.Ito.IsWiener.ou_weak_process`).
* Instance for `stdWiener`: `Gardiner.Ito.ouProc_stdWiener`.

The printed (4.4.27), (4.4.29), (4.4.30) are correct (for `k ≠ 0`, with `x(0)` independent of `W`).
-/
import SHSLib.Gardiner.Ito.Linearised
import SHSLib.Gardiner.Ito.Schemes

open MeasureTheory ProbabilityTheory Filter Topology Set intervalIntegral Finset
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

open Gardiner.SDE

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-! ### Random variables independent of the Wiener process -/

/-- The path map `ω ↦ (t ↦ W t ω)`, a random element of `ℝ → ℝ`. -/
def pathMap (W : ℝ → Ω → ℝ) (ω : Ω) : ℝ → ℝ := fun t => W t ω

lemma measurable_pathMap (hW : ∀ t, Measurable (W t)) : Measurable (pathMap W) :=
  measurable_pi_lambda _ hW

/-- The Riemann sum as a function of the path. -/
def riemannOnPath (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (w : ℝ → ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), f (grid a b n i) * (w (grid a b n (i + 1)) - w (grid a b n i))

lemma measurable_riemannOnPath (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    Measurable (riemannOnPath f a b n) :=
  Finset.measurable_fun_sum _ fun _ _ =>
    measurable_const.mul ((measurable_pi_apply _).sub (measurable_pi_apply _))

omit [MeasurableSpace Ω] in
lemma riemannSum_eq_comp (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    riemannSum W f a b n = riemannOnPath f a b n ∘ pathMap W := rfl

namespace IsWiener

variable (hW : IsWiener W P) {f : ℝ → ℝ} {a b : ℝ}
include hW

/-- A square-integrable `Y` independent of `W` is uncorrelated with every Wiener integral. -/
theorem integral_mul_wienerInt_of_indep {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hind : IndepFun Y (pathMap W) P) (hf : Continuous f) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, Y ω * wienerInt W P f a b ω ∂P = 0 := by
  have := hW.isProbabilityMeasure
  obtain ⟨h1, h2⟩ := hW.wienerInt_spec hf ha hab
  have h := tendsto_integral_mul_of_ms (fun _ => hY) (fun n => memLp_riemannSum hW ha hab n) hY h1
    (by simp) h2
  have h0 : ∀ n, ∫ ω, Y ω * riemannSum W f a b n ω ∂P = 0 := by
    intro n
    have hI : IndepFun Y (riemannSum W f a b n) P := by
      rw [riemannSum_eq_comp]
      exact hind.comp measurable_id (measurable_riemannOnPath f a b n)
    have := hI.integral_mul_eq_mul_integral hY.aestronglyMeasurable
      (memLp_riemannSum hW ha hab n).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, riemannSum_eq hW ha hab, SimpleIntegrand.integral_mean hW, mul_zero]
  simp only [h0] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end IsWiener

/-! ### The Ornstein–Uhlenbeck process (Gardiner §4.4.4) -/

/-- The Ornstein–Uhlenbeck kernel `e^{-k(t - s)}`. -/
def ouKernel (k t s : ℝ) : ℝ := Real.exp (-k * (t - s))

lemma continuous_ouKernel (k t : ℝ) : Continuous (ouKernel k t) := by
  unfold ouKernel; fun_prop

lemma integral_ouKernel_mul {k : ℝ} (hk : k ≠ 0) (s t : ℝ) :
    ∫ u in (0 : ℝ)..s, ouKernel k t u * ouKernel k s u =
      (Real.exp (-k * (t - s)) - Real.exp (-k * (t + s))) / (2 * k) := by
  have hF : ∀ u, HasDerivAt (fun u => Real.exp (2 * k * u - k * (t + s)) / (2 * k))
      (ouKernel k t u * ouKernel k s u) u := by
    intro u
    have := ((((hasDerivAt_id u).const_mul (2 * k)).sub_const (k * (t + s))).exp).div_const
      (2 * k)
    convert this using 1
    simp only [ouKernel, id]
    rw [← Real.exp_add]
    field_simp
    ring_nf
  rw [integral_eq_sub_of_hasDerivAt (fun u _ => hF u)
    (((continuous_ouKernel k t).mul (continuous_ouKernel k s)).intervalIntegrable _ _)]
  rw [show 2 * k * s - k * (t + s) = -k * (t - s) by ring,
    show 2 * k * 0 - k * (t + s) = -k * (t + s) by ring]
  ring

/-- The stochastic part of (4.4.26), `∫₀ᵗ e^{-k(t-t')} dW(t')`. -/
def ouInt (W : ℝ → Ω → ℝ) (P : Measure Ω) (k t : ℝ) : Ω → ℝ := wienerInt W P (ouKernel k t) 0 t

/-- **The Ornstein–Uhlenbeck process** `x(t) = x(0)e^{-kt} + √D ∫₀ᵗ e^{-k(t-t')} dW(t')` (4.4.26),
written pathwise: the stochastic integral is replaced by its integration-by-parts form
`linPath k W(·, ω)` (which agrees with it almost surely, `Gardiner.Ito.IsWiener.ouProc_ae`). -/
def ouProc (k D : ℝ) (x0 : Ω → ℝ) (W : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  x0 ω * Real.exp (-k * t) + Real.sqrt D * linPath (fun _ => k) (fun s => W s ω) t

lemma linPath_zero (k w : ℝ → ℝ) : linPath k w 0 = 0 := by simp [linPath]

omit [MeasurableSpace Ω] in
lemma ouProc_zero (k D : ℝ) (x0 : Ω → ℝ) (W : ℝ → Ω → ℝ) (ω : Ω) :
    ouProc k D x0 W 0 ω = x0 ω := by
  simp [ouProc, linPath_zero]

omit [MeasurableSpace Ω] in
/-- **The OU process solves `dx = -kx dt + √D dW` pathwise** (4.4.22): for every sample point
with a continuous path, `x(t) = x(0) + ∫₀ᵗ (-k x(s)) ds + √D (W(t) - W(0))` for all `t`. -/
theorem ouProc_isPathSol (k D : ℝ) (x0 : Ω → ℝ) {ω : Ω} (hω : Continuous fun t => W t ω)
    (T : ℝ) :
    IsPathSol (fun x => -k * x) (Real.sqrt D) (fun t => W t ω) (fun t => ouProc k D x0 W t ω) T := by
  have hL := continuous_linPath (k := fun _ => k) continuous_const hω
  refine ⟨?_, fun t _ => ?_⟩
  · unfold ouProc; fun_prop
  · rw [ouProc_zero]
    have h1 := linPath_eq (k := fun _ => k) continuous_const hω t
    have h2 : ∫ s in (0 : ℝ)..t, -k * Real.exp (-k * s) = Real.exp (-k * t) - 1 := by
      rw [integral_eq_sub_of_hasDerivAt (f := fun s => Real.exp (-k * s)) (fun s _ => by
        simpa [mul_comm] using ((hasDerivAt_id s).const_mul (-k)).exp)
        ((by fun_prop : Continuous fun s => -k * Real.exp (-k * s)).intervalIntegrable _ _)]
      simp
    have hA : IntervalIntegrable (fun s => x0 ω * (-k * Real.exp (-k * s))) volume 0 t := by
      apply Continuous.intervalIntegrable; fun_prop
    have hB : IntervalIntegrable (fun s => Real.sqrt D *
        (k * linPath (fun _ => k) (fun s => W s ω) s)) volume 0 t :=
      (continuous_const.mul (continuous_const.mul hL)).intervalIntegrable _ _
    have e : ∫ s in (0 : ℝ)..t, -k * ouProc k D x0 W s ω =
        x0 ω * (Real.exp (-k * t) - 1) -
          Real.sqrt D * ∫ s in (0 : ℝ)..t, k * linPath (fun _ => k) (fun s => W s ω) s := by
      rw [show (fun s => -k * ouProc k D x0 W s ω) = fun s => x0 ω * (-k * Real.exp (-k * s)) -
          Real.sqrt D * (k * linPath (fun _ => k) (fun s => W s ω) s) from
          funext fun s => by simp only [ouProc]; ring]
      rw [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul (x0 ω),
        intervalIntegral.integral_const_mul (Real.sqrt D), h2]
    rw [e]
    simp only [ouProc]
    rw [h1]
    ring

namespace IsWiener

variable (hW : IsWiener W P) {k D : ℝ} {x0 : Ω → ℝ}
include hW

/-- **(4.4.26)**: almost surely, `x(t) = x(0)e^{-kt} + √D ∫₀ᵗ e^{-k(t-t')} dW(t')` with the
mean-square Wiener integral. -/
theorem ouProc_ae {t : ℝ} (ht : 0 ≤ t) :
    ouProc k D x0 W t =ᵐ[P] fun ω => x0 ω * Real.exp (-k * t) + Real.sqrt D * ouInt W P k t ω := by
  have h := hW.linProc_ae_linPath (k := fun _ => k) continuous_const ht
  have hfun : (fun s => (fun _ => (1 : ℝ)) s * linKernel (fun _ => k) t s) = ouKernel k t := by
    funext s; simp [linKernel_const, ouKernel]
  rw [linProc, hfun] at h
  filter_upwards [h] with ω hω
  simp only [ouProc, ouInt, hω]

lemma memLp_ouInt {t : ℝ} (ht : 0 ≤ t) : MemLp (ouInt W P k t) 2 P :=
  (hW.wienerInt_spec (continuous_ouKernel k t) le_rfl ht).1

lemma ouInt_mean {t : ℝ} (ht : 0 ≤ t) : ∫ ω, ouInt W P k t ω ∂P = 0 :=
  hW.wienerInt_mean (continuous_ouKernel k t) le_rfl ht

/-- The covariance of the stochastic parts: for `0 ≤ s ≤ t`, `k ≠ 0`,
`⟨∫₀ᵗ e^{-k(t-u)} dW ∫₀ˢ e^{-k(s-u)} dW⟩ = (e^{-k(t-s)} - e^{-k(t+s)})/(2k)`. -/
theorem ouInt_mul (hk : k ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, ouInt W P k t ω * ouInt W P k s ω ∂P =
      (Real.exp (-k * (t - s)) - Real.exp (-k * (t + s))) / (2 * k) := by
  rw [ouInt, ouInt, hW.wienerInt_mul_same (continuous_ouKernel k t) (continuous_ouKernel k s)
    le_rfl (hs.trans hst) hs, min_eq_right hst, integral_ouKernel_mul hk]

/-- The variance of the stochastic part, `(1 - e^{-2kt})/(2k)`. -/
theorem ouInt_sq (hk : k ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ouInt W P k t ω ^ 2 ∂P = (1 - Real.exp (-2 * k * t)) / (2 * k) := by
  simp_rw [sq]
  rw [hW.ouInt_mul hk ht le_rfl]
  congr 1
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring_nf

section Moments

variable (hx0 : MemLp x0 2 P) (hind : IndepFun x0 (pathMap W) P)
include hx0 hind

/-- The second-order cross moment of the representation (4.4.26). -/
lemma ou_cross {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, ouProc k D x0 W t ω * ouProc k D x0 W s ω ∂P =
      Real.exp (-k * (t + s)) * ∫ ω, x0 ω ^ 2 ∂P +
        Real.sqrt D ^ 2 * ∫ ω, ouInt W P k t ω * ouInt W P k s ω ∂P := by
  have ht : 0 ≤ t := hs.trans hst
  have hIt := hW.memLp_ouInt (k := k) ht
  have hIs := hW.memLp_ouInt (k := k) hs
  have h1 := hW.integral_mul_wienerInt_of_indep hx0 hind (continuous_ouKernel k t) le_rfl ht
  have h2 := hW.integral_mul_wienerInt_of_indep hx0 hind (continuous_ouKernel k s) le_rfl hs
  have hint1 : Integrable (fun ω => x0 ω * x0 ω) P := hx0.integrable_mul hx0
  have hint2 : Integrable (fun ω => x0 ω * ouInt W P k s ω) P := hx0.integrable_mul hIs
  have hint3 : Integrable (fun ω => x0 ω * ouInt W P k t ω) P := hx0.integrable_mul hIt
  have hint4 : Integrable (fun ω => ouInt W P k t ω * ouInt W P k s ω) P := hIt.integrable_mul hIs
  rw [MeasureTheory.integral_congr_ae (by
    filter_upwards [hW.ouProc_ae (k := k) (D := D) (x0 := x0) ht,
      hW.ouProc_ae (k := k) (D := D) (x0 := x0) hs] with ω h1 h2
    rw [h1, h2])]
  have e : ∀ ω, (x0 ω * Real.exp (-k * t) + Real.sqrt D * ouInt W P k t ω) *
      (x0 ω * Real.exp (-k * s) + Real.sqrt D * ouInt W P k s ω) =
      Real.exp (-k * (t + s)) * (x0 ω * x0 ω) +
        (Real.sqrt D * Real.exp (-k * t)) * (x0 ω * ouInt W P k s ω) +
        (Real.sqrt D * Real.exp (-k * s)) * (x0 ω * ouInt W P k t ω) +
        Real.sqrt D ^ 2 * (ouInt W P k t ω * ouInt W P k s ω) := by
    intro ω
    rw [show -k * (t + s) = -k * t + -k * s by ring, Real.exp_add]
    ring
  simp_rw [e]
  set E := Real.exp (-k * (t + s))
  set A := Real.sqrt D * Real.exp (-k * t)
  set B := Real.sqrt D * Real.exp (-k * s)
  have i2 : Integrable (fun ω => E * (x0 ω * x0 ω) + A * (x0 ω * ouInt W P k s ω)) P :=
    (hint1.const_mul _).add (hint2.const_mul _)
  have i1 : Integrable (fun ω => E * (x0 ω * x0 ω) + A * (x0 ω * ouInt W P k s ω) +
      B * (x0 ω * ouInt W P k t ω)) P := i2.add (hint3.const_mul _)
  rw [integral_add i1 (hint4.const_mul _), integral_add i2 (hint3.const_mul _),
    integral_add (hint1.const_mul _) (hint2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  simp only [ouInt] at *
  rw [h1, h2]
  simp [sq]

omit hind in
/-- **(4.4.27): the mean of the OU process**, `⟨x(t)⟩ = ⟨x(0)⟩ e^{-kt}`. -/
theorem ouProc_mean {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ouProc k D x0 W t ω ∂P = (∫ ω, x0 ω ∂P) * Real.exp (-k * t) := by
  have := hW.isProbabilityMeasure
  rw [MeasureTheory.integral_congr_ae (hW.ouProc_ae ht), integral_add ((hx0.integrable one_le_two).mul_const _)
    ((hW.memLp_ouInt ht).integrable one_le_two |>.const_mul _), MeasureTheory.integral_mul_const,
    MeasureTheory.integral_const_mul, hW.ouInt_mean ht, mul_zero, add_zero]

/-- **The correlation function (4.4.30)**: for `k ≠ 0`, `D ≥ 0` and `0 ≤ s ≤ t`,
`⟨x(t), x(s)⟩ = var{x(0)} e^{-k(t+s)} + (D/2k)(e^{-k(t-s)} - e^{-k(t+s)})`. -/
theorem ouProc_cov (hk : k ≠ 0) (hD : 0 ≤ D) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, ouProc k D x0 W t ω * ouProc k D x0 W s ω ∂P -
        (∫ ω, ouProc k D x0 W t ω ∂P) * (∫ ω, ouProc k D x0 W s ω ∂P) =
      (∫ ω, x0 ω ^ 2 ∂P - (∫ ω, x0 ω ∂P) ^ 2) * Real.exp (-k * (t + s)) +
        D / (2 * k) * (Real.exp (-k * (t - s)) - Real.exp (-k * (t + s))) := by
  rw [hW.ou_cross hx0 hind hs hst, hW.ouInt_mul hk hs hst, hW.ouProc_mean hx0 (hs.trans hst),
    hW.ouProc_mean hx0 hs, Real.sq_sqrt hD,
    show -k * (t + s) = -k * t + -k * s by ring, Real.exp_add]
  field_simp
  ring

/-- **The variance (4.4.29)**: `var{x(t)} = {var{x(0)} - D/2k} e^{-2kt} + D/2k`. -/
theorem ouProc_var (hk : k ≠ 0) (hD : 0 ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ouProc k D x0 W t ω ^ 2 ∂P - (∫ ω, ouProc k D x0 W t ω ∂P) ^ 2 =
      (∫ ω, x0 ω ^ 2 ∂P - (∫ ω, x0 ω ∂P) ^ 2 - D / (2 * k)) * Real.exp (-2 * k * t) +
        D / (2 * k) := by
  have h := hW.ouProc_cov hx0 hind hk hD ht le_rfl
  simp only [← sq, sub_self, mul_zero, Real.exp_zero] at h
  rw [h, show -k * (t + t) = -2 * k * t by ring]
  ring

/-- The printed form of (4.4.30), for all `s, t ≥ 0`:
`⟨x(t), x(s)⟩ = [var{x(0)} - D/2k] e^{-k(t+s)} + (D/2k) e^{-k|t-s|}`. -/
theorem ouProc_cov_printed (hk : k ≠ 0) (hD : 0 ≤ D) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ ω, ouProc k D x0 W t ω * ouProc k D x0 W s ω ∂P -
        (∫ ω, ouProc k D x0 W t ω ∂P) * (∫ ω, ouProc k D x0 W s ω ∂P) =
      (∫ ω, x0 ω ^ 2 ∂P - (∫ ω, x0 ω ∂P) ^ 2 - D / (2 * k)) * Real.exp (-k * (t + s)) +
        D / (2 * k) * Real.exp (-k * |t - s|) := by
  rcases le_total s t with hst | hts
  · rw [hW.ouProc_cov hx0 hind hk hD hs hst, abs_of_nonneg (sub_nonneg.mpr hst)]
    ring
  · have h := hW.ouProc_cov hx0 hind (D := D) hk hD ht hts
    rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
    simp_rw [mul_comm (ouProc k D x0 W t _) (ouProc k D x0 W s _)]
    rw [mul_comm (∫ ω, ouProc k D x0 W t ω ∂P), h, add_comm s t]
    ring

/-- The second moment of the OU process, `⟨x(t)²⟩ = ⟨x(0)²⟩ e^{-2kt} + (D/2k)(1 - e^{-2kt})`. -/
theorem ouProc_second (hk : k ≠ 0) (hD : 0 ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ouProc k D x0 W t ω ^ 2 ∂P =
      Real.exp (-2 * k * t) * ∫ ω, x0 ω ^ 2 ∂P + D / (2 * k) * (1 - Real.exp (-2 * k * t)) := by
  simp_rw [sq]
  rw [hW.ou_cross hx0 hind ht le_rfl, hW.ouInt_mul hk ht le_rfl, Real.sq_sqrt hD]
  simp only [sub_self, mul_zero, Real.exp_zero, show -k * (t + t) = -2 * k * t by ring, sq]
  ring

end Moments

/-- **Gaussian law of the OU process**: if `x(0) ~ N(m, v₀)` is independent of `W` (in particular
if `x(0)` is deterministic, `v₀ = 0`), then
`x(t) ~ N(m e^{-kt}, v₀ e^{-2kt} + D ∫₀ᵗ e^{-2k(t-s)} ds)`. -/
theorem ouProc_map (hD : 0 ≤ D) {m : ℝ} {v₀ : ℝ≥0} (hx0m : Measurable x0)
    (hlaw : P.map x0 = gaussianReal m v₀) (hind : IndepFun x0 (pathMap W) P) {t : ℝ}
    (ht : 0 ≤ t) :
    P.map (ouProc k D x0 W t) = gaussianReal (m * Real.exp (-k * t))
      (v₀ * (Real.exp (-k * t) ^ 2).toNNReal +
        (D * ∫ s in (0 : ℝ)..t, ouKernel k t s ^ 2).toNNReal) := by
  have := hW.isProbabilityMeasure
  have hx0 : MemLp x0 2 P := by
    have h : MemLp id 2 (P.map x0) := by rw [hlaw]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id hx0m.aemeasurable).mp h
  obtain ⟨hI1, hI2⟩ := hW.wienerInt_spec (continuous_ouKernel k t) le_rfl ht
  set e := Real.exp (-k * t)
  set X : ℕ → Ω → ℝ := fun n ω =>
    x0 ω * e + Real.sqrt D * riemannSum W (ouKernel k t) 0 t n ω
  have hX : ∀ n, MemLp (X n) 2 P := fun n =>
    (hx0.mul_const e).add ((memLp_riemannSum hW le_rfl ht n).const_mul _)
  have hY : MemLp (fun ω => x0 ω * e + Real.sqrt D * ouInt W P k t ω) 2 P :=
    (hx0.mul_const e).add (hI1.const_mul _)
  choose v hv using fun n => exists_gauss_riemannSum (f := ouKernel k t) hW le_rfl ht n
  -- the law of the approximations
  have hXlaw : ∀ n, P.map (X n) = gaussianReal (m * e)
      (v₀ * (e ^ 2).toNNReal + ⟨Real.sqrt D ^ 2, sq_nonneg _⟩ * v n) := by
    intro n
    have hI : IndepFun (fun ω => x0 ω * e) (fun ω => Real.sqrt D * riemannSum W (ouKernel k t) 0 t n ω)
        P := by
      have h := hind.comp (measurable_id.mul_const e)
        ((measurable_riemannOnPath (ouKernel k t) 0 t n).const_mul (Real.sqrt D))
      exact h
    have hm1 : Measurable fun ω => x0 ω * e := hx0m.mul_const e
    have hm2 : Measurable fun ω => Real.sqrt D * riemannSum W (ouKernel k t) 0 t n ω :=
      (hW.measurable_riemannSum _ 0 t n).const_mul _
    have hl1 : P.map (fun ω => x0 ω * e) = gaussianReal (m * e) (v₀ * (e ^ 2).toNNReal) := by
      have : (fun ω => x0 ω * e) = (fun x => e * x) ∘ x0 := by funext ω; simp [mul_comm]
      rw [this, ← Measure.map_map (by fun_prop) hx0m, hlaw, gaussianReal_map_const_mul]
      congr 1
      · ring
      · rw [mul_comm]; congr 1; ext; simp [Real.coe_toNNReal _ (sq_nonneg e)]
    have hl2 : P.map (fun ω => Real.sqrt D * riemannSum W (ouKernel k t) 0 t n ω) =
        gaussianReal 0 (⟨Real.sqrt D ^ 2, sq_nonneg _⟩ * v n) := by
      have : (fun ω => Real.sqrt D * riemannSum W (ouKernel k t) 0 t n ω) =
          (fun x => Real.sqrt D * x) ∘ riemannSum W (ouKernel k t) 0 t n := rfl
      rw [this, ← Measure.map_map (by fun_prop) (hW.measurable_riemannSum _ 0 t n), hv n,
        gaussianReal_map_const_mul, mul_zero]
    have : X n = (fun ω => x0 ω * e) + fun ω => Real.sqrt D * riemannSum W (ouKernel k t) 0 t n ω :=
      rfl
    rw [this, hI.map_add_eq_map_conv_map hm1 hm2, hl1, hl2, gaussianReal_conv_gaussianReal,
      add_zero]
  -- convergence of the variances
  have hvn : ∀ n, (v n : ℝ) = ∫ ω, riemannSum W (ouKernel k t) 0 t n ω *
      riemannSum W (ouKernel k t) 0 t n ω ∂P := by
    intro n
    have h := Gardiner.SDE.integral_comp_gauss (P := P) (hW.measurable_riemannSum _ 0 t n) (hv n)
      (continuous_pow 2)
    rw [Gardiner.SDE.gauss_m2] at h
    rw [← h]; simp [sq]
  have hvlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (∫ s in (0 : ℝ)..t, ouKernel k t s ^ 2)) := by
    have h := tendsto_integral_mul_of_ms (fun n => memLp_riemannSum hW le_rfl ht n)
      (fun n => memLp_riemannSum hW le_rfl ht n) hI1 hI1 hI2 hI2
    simp only [← sq, hW.wienerInt_sq (continuous_ouKernel k t) le_rfl ht] at h
    simp only [hvn, ← sq]; exact h
  have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, ouKernel k t s ^ 2 :=
    intervalIntegral.integral_nonneg ht fun s _ => sq_nonneg _
  have hlimlaw := map_eq_gaussianReal_of_ms hX hY hXlaw tendsto_const_nhds
    (v' := v₀ * (e ^ 2).toNNReal + (D * ∫ s in (0 : ℝ)..t, ouKernel k t s ^ 2).toNNReal)
    (by
      push_cast
      rw [Real.coe_toNNReal _ (mul_nonneg hD hnn), Real.sq_sqrt hD]
      exact tendsto_const_nhds.add (hvlim.const_mul D))
    (by
      have h := hI2.const_mul (Real.sqrt D ^ 2)
      rw [mul_zero] at h
      refine h.congr fun n => ?_
      rw [← MeasureTheory.integral_const_mul]
      congr 1; funext ω; simp only [X, ouInt]; ring)
  rw [Measure.map_congr (hW.ouProc_ae ht)]
  exact hlimlaw

/-! ### Deterministic initial value: the moments of Job D -/

section Deterministic

/-- **Mean, deterministic `x(0) = c`**: `⟨x(t)⟩ = ouMean k c t` (`Gardiner.SDE.ouMean`). -/
theorem ouProc_mean_const (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ouProc k D (fun _ => c) W t ω ∂P = ouMean k c t := by
  have := hW.isProbabilityMeasure
  rw [hW.ouProc_mean (memLp_const c) ht]
  simp [ouMean]

/-- **Second moment, deterministic `x(0) = c`**: `⟨x(t)²⟩ = ouSecond k √D c t`
(`Gardiner.SDE.ouSecond`, with noise amplitude `σ = √D`). -/
theorem ouProc_second_const (hk : k ≠ 0) (hD : 0 ≤ D) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ouProc k D (fun _ => c) W t ω ^ 2 ∂P = ouSecond k (Real.sqrt D) c t := by
  have := hW.isProbabilityMeasure
  rw [hW.ouProc_second (memLp_const c) (indepFun_const_left c _) hk hD ht]
  simp [ouSecond, Real.sq_sqrt hD]

/-- **Gaussian law, deterministic `x(0) = c`** (4.4.27)–(4.4.29):
`x(t) ~ N(c e^{-kt}, D(1 - e^{-2kt})/2k)`. -/
theorem ouProc_map_const (hk : k ≠ 0) (hD : 0 ≤ D) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.map (ouProc k D (fun _ => c) W t) =
      gaussianReal (c * Real.exp (-k * t)) (D * (1 - Real.exp (-2 * k * t)) / (2 * k)).toNNReal := by
  have := hW.isProbabilityMeasure
  have h := hW.ouProc_map (k := k) hD (m := c) (v₀ := 0) measurable_const
    (by rw [Measure.map_const, measure_univ, one_smul, gaussianReal_zero_var])
    (indepFun_const_left c _) ht
  rw [h, zero_mul, zero_add]
  congr 2
  simp_rw [sq]
  rw [integral_ouKernel_mul hk t t]
  simp only [sub_self, mul_zero, Real.exp_zero, show -k * (t + t) = -2 * k * t by ring]
  ring

end Deterministic

/-! ### The OU weak-error theorems refer to the actual OU process -/

/-- **The OU weak-error theorems compare the schemes with the actual OU process.**  For the OU
process `x(t)` solving `dx = -x dt + dW`, `x(0) = 1`, driven by the *same* Wiener process `W` as the
Euler and semi-implicit schemes (`Gardiner.Ito.IsWiener.ou_weak`), the weak errors at `T = Nτ` are
`≤ (19/2)Tτ`, `≤ (29/2)Tτ` (second moment) and `≤ T e^T τ` (mean). -/
theorem ou_weak_process {τ : ℝ≥0} (hτ : (τ : ℝ) ≤ 1 / 2) (N : ℕ) :
    |∫ ω, linScheme (eulerOU 1 1 τ) 1 (gridInc W τ) N ω ^ 2 ∂P -
        ∫ ω, ouProc 1 1 (fun _ => 1) W (N * τ) ω ^ 2 ∂P| ≤ 19 / 2 * (N * τ) * τ ∧
    |∫ ω, linScheme (semiOU 1 1 τ) 1 (gridInc W τ) N ω ^ 2 ∂P -
        ∫ ω, ouProc 1 1 (fun _ => 1) W (N * τ) ω ^ 2 ∂P| ≤ 29 / 2 * (N * τ) * τ ∧
    |∫ ω, linScheme (eulerOU 1 1 τ) 1 (gridInc W τ) N ω ∂P -
        ∫ ω, ouProc 1 1 (fun _ => 1) W (N * τ) ω ∂P| ≤ (N * τ) * Real.exp (N * τ) * τ := by
  have hT : (0 : ℝ) ≤ N * τ := by positivity
  rw [hW.ouProc_second_const one_ne_zero zero_le_one 1 hT, hW.ouProc_mean_const 1 hT,
    Real.sqrt_one]
  exact hW.ou_weak hτ N

/-! ### Stationary limit (§4.4.4, `k > 0`) -/

omit hW in
lemma tendsto_exp_neg_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t => Real.exp (-c * t)) atTop (𝓝 0) := by
  have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
  simpa [Function.comp_def, neg_mul] using this

/-- **Stationary limit of the OU process** (cf. (4.4.31)): for `k > 0`, as `t → ∞`, the mean
tends to `0`, the variance to `D/2k`, and the covariance `⟨x(t+τ), x(t)⟩` to `(D/2k) e^{-k|τ|}`,
for every square-integrable initial value independent of `W`. -/
theorem ouProc_stationary (hk : 0 < k) (hD : 0 ≤ D) (hx0 : MemLp x0 2 P)
    (hind : IndepFun x0 (pathMap W) P) :
    Tendsto (fun t => ∫ ω, ouProc k D x0 W t ω ∂P) atTop (𝓝 0) ∧
    Tendsto (fun t => ∫ ω, ouProc k D x0 W t ω ^ 2 ∂P - (∫ ω, ouProc k D x0 W t ω ∂P) ^ 2)
      atTop (𝓝 (D / (2 * k))) ∧
    ∀ τ : ℝ, Tendsto (fun t => ∫ ω, ouProc k D x0 W (t + τ) ω * ouProc k D x0 W t ω ∂P -
        (∫ ω, ouProc k D x0 W (t + τ) ω ∂P) * (∫ ω, ouProc k D x0 W t ω ∂P))
      atTop (𝓝 (D / (2 * k) * Real.exp (-k * |τ|))) := by
  have h1 := tendsto_exp_neg_mul_atTop hk
  have h2 := tendsto_exp_neg_mul_atTop (show 0 < 2 * k by linarith)
  set V := ∫ ω, x0 ω ^ 2 ∂P - (∫ ω, x0 ω ∂P) ^ 2
  refine ⟨?_, ?_, fun τ => ?_⟩
  · have h := h1.const_mul (∫ ω, x0 ω ∂P)
    rw [mul_zero] at h
    refine (h.congr' ?_)
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [hW.ouProc_mean hx0 ht, mul_comm]
  · have h := (h2.const_mul (V - D / (2 * k))).add_const (D / (2 * k))
    rw [mul_zero, zero_add] at h
    refine (h.congr' ?_)
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [hW.ouProc_var hx0 hind hk.ne' hD ht]; simp only [V]; ring_nf
  · have h := ((h2.const_mul (Real.exp (-k * τ))).const_mul (V - D / (2 * k))).add_const
      (D / (2 * k) * Real.exp (-k * |τ|))
    rw [mul_zero, mul_zero, zero_add] at h
    refine (h.congr' ?_)
    filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (-τ)] with t ht htτ
    rw [hW.ouProc_cov_printed hx0 hind hk.ne' hD ht (by linarith),
      show t + τ - t = τ by ring, show -k * (t + τ + t) = -k * τ + -(2 * k) * t by ring,
      Real.exp_add]

end IsWiener

/-- **Instance (standard Wiener process).** The OU process `dx = -x dt + √2 dW`, `x(0) = 3`, driven
by `stdWiener`: `x(t) ~ N(3e^{-t}, 1 - e^{-2t})`, it solves the SDE pathwise, and its first two
moments are `ouMean 1 3 t`, `ouSecond 1 √2 3 t`. -/
theorem ouProc_stdWiener {t : ℝ} (ht : 0 ≤ t) (ω : StdWienerSpace) :
    stdWienerMeasure.map (ouProc 1 2 (fun _ => 3) stdWiener t) =
      gaussianReal (3 * Real.exp (-t)) (1 - Real.exp (-2 * t)).toNNReal ∧
    IsPathSol (fun x => -1 * x) (Real.sqrt 2) (fun s => stdWiener s ω)
      (fun s => ouProc 1 2 (fun _ => 3) stdWiener s ω) t ∧
    ∫ ω, ouProc 1 2 (fun _ => 3) stdWiener t ω ∂stdWienerMeasure = ouMean 1 3 t ∧
    ∫ ω, ouProc 1 2 (fun _ => 3) stdWiener t ω ^ 2 ∂stdWienerMeasure =
      ouSecond 1 (Real.sqrt 2) 3 t := by
  refine ⟨?_, ouProc_isPathSol 1 2 _ (continuous_stdWiener ω) t,
    isWiener_stdWiener.ouProc_mean_const 3 ht,
    isWiener_stdWiener.ouProc_second_const one_ne_zero zero_le_two 3 ht⟩
  rw [isWiener_stdWiener.ouProc_map_const one_ne_zero zero_le_two 3 ht]
  congr 2 <;> ring_nf
end Gardiner.Ito
