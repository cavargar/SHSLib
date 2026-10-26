/-
# The law of the linearised process (Gardiner (6.2.14), (6.2.31)–(6.2.32))

For continuous `k`, `b` the first-order term of the small-noise expansion,
`x₁(t) = ∫₀ᵗ b(t') e^{-∫_{t'}^t k} dW(t')` (`Gardiner.Ito.linProc`, a Wiener integral), satisfies the
former named hypothesis `Gardiner.SDE.IsLinearisedLaw` (`Gardiner.Ito.IsWiener.isLinearisedLaw_linProc`),
so the leading-order variance (6.2.31) and correlation (6.2.32) hold unconditionally
(`Gardiner.Ito.IsWiener.linProc_variance`, `…linProc_correlation`), and `x₁(t) ~ N(0, V(t))`
(`Gardiner.Ito.IsWiener.linProc_map`).

**Relation with the pathwise layer** (additive noise, `b = 1`): the pathwise first-order term
`linPath k w` solves `y(t) = w(t) - w(0) - ∫₀ᵗ k y` (`Gardiner.Ito.linPath_eq`, unique by
`Gardiner.Ito.linPath_unique`), and `x₁(t) = linPath k W(·, ω) t` almost surely
(`Gardiner.Ito.IsWiener.linProc_ae_linPath`, by integration by parts).  Hence the first-order term
of any almost-sure pathwise hierarchy (`Gardiner.SDE.IsHierarchy`) is almost surely `x₁`
(`Gardiner.Ito.IsWiener.hierarchy_first_order_ae`).  Instance: the Brownian `Gardiner.Ito.ouPath`
of `SHSLib.Gardiner.Ito.Pathwise` (`Gardiner.Ito.ouPath_stdWiener_law`).
-/
import SHSLib.Gardiner.Ito.WienerIntegral
import SHSLib.Gardiner.Ito.Pathwise
import SHSLib.Gardiner.SDE.Statistics

open MeasureTheory ProbabilityTheory Filter Topology Set intervalIntegral
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

open Gardiner.SDE

/-! ### The kernel `e^{-∫ₛᵗ k}` and the pathwise linear equation -/

/-- The propagator of `dx = -k(t) x dt`, `linKernel k t s = e^{-∫ₛᵗ k}`. -/
def linKernel (k : ℝ → ℝ) (t s : ℝ) : ℝ := Real.exp (-∫ v in s..t, k v)

lemma linKernel_self (k : ℝ → ℝ) (t : ℝ) : linKernel k t t = 1 := by simp [linKernel]

lemma hasDerivAt_linKernel {k : ℝ → ℝ} (hk : Continuous k) (t s : ℝ) :
    HasDerivAt (linKernel k t) (k s * linKernel k t s) s := by
  have h : HasDerivAt (fun s => ∫ v in s..t, k v) (-k s) s :=
    intervalIntegral.integral_hasDerivAt_left (hk.intervalIntegrable _ _)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have := h.neg.exp
  simp only [neg_neg] at this
  convert this using 1
  simp [linKernel, mul_comm]

lemma continuous_linKernel {k : ℝ → ℝ} (hk : Continuous k) (t : ℝ) : Continuous (linKernel k t) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_linKernel hk t s).continuousAt

lemma linKernel_const (k t s : ℝ) : linKernel (fun _ => k) t s = Real.exp (-k * (t - s)) := by
  simp [linKernel]; ring_nf

/-- The integral of `k e^{-∫ₛᵗ k}` over `[0, t]` is `1 - e^{-∫₀ᵗ k}`. -/
lemma integral_k_linKernel {k : ℝ → ℝ} (hk : Continuous k) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, k s * linKernel k t s = 1 - linKernel k t 0 := by
  rw [integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_linKernel hk t s)
    ((hk.mul (continuous_linKernel hk t)).intervalIntegrable _ _), linKernel_self]

/-- The first-order term of the small-noise hierarchy for additive noise, written without a
stochastic integral (the integration-by-parts form of `∫₀ᵗ e^{-∫ₛᵗ k} dw(s)`):
`x₁(t) = w(t) - w(0) - ∫₀ᵗ k(s) e^{-∫ₛᵗ k} (w(s) - w(0)) ds`. -/
def linPath (k w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (w t - w 0) - ∫ s in (0 : ℝ)..t, k s * linKernel k t s * (w s - w 0)

/-- `linKernel k t s = e^{K(s) - K(t)}` with `K` the primitive of `k`. -/
lemma linKernel_eq {k : ℝ → ℝ} (hk : Continuous k) (t s : ℝ) :
    linKernel k t s = Real.exp (-∫ v in (0 : ℝ)..t, k v) * Real.exp (∫ v in (0 : ℝ)..s, k v) := by
  rw [linKernel, ← Real.exp_add, integral_sub_split hk s t]
  ring_nf

lemma linPath_eq_aux {k w : ℝ → ℝ} (hk : Continuous k) (t : ℝ) :
    linPath k w t = (w t - w 0) - Real.exp (-∫ v in (0 : ℝ)..t, k v) *
      ∫ s in (0 : ℝ)..t, k s * Real.exp (∫ v in (0 : ℝ)..s, k v) * (w s - w 0) := by
  rw [linPath, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [linKernel_eq hk]; ring

lemma continuous_linPath {k w : ℝ → ℝ} (hk : Continuous k) (hw : Continuous w) :
    Continuous (linPath k w) := by
  have hK : Continuous fun t => ∫ v in (0 : ℝ)..t, k v := continuous_primitive' hk
  have h : Continuous fun t => (w t - w 0) - Real.exp (-∫ v in (0 : ℝ)..t, k v) *
      ∫ s in (0 : ℝ)..t, k s * Real.exp (∫ v in (0 : ℝ)..s, k v) * (w s - w 0) :=
    (hw.sub continuous_const).sub ((Real.continuous_exp.comp hK.neg).mul
      (continuous_primitive' ((hk.mul (Real.continuous_exp.comp hK)).mul
        (hw.sub continuous_const))))
  exact h.congr fun t => (linPath_eq_aux hk t).symm

/-- **The pathwise first-order equation** (6.2.10b) with additive noise:
`x₁(t) = w(t) - w(0) - ∫₀ᵗ k(s) x₁(s) ds` for every continuous path `w`. -/
theorem linPath_eq {k w : ℝ → ℝ} (hk : Continuous k) (hw : Continuous w) (t : ℝ) :
    linPath k w t = (w t - w 0) - ∫ s in (0 : ℝ)..t, k s * linPath k w s := by
  set K : ℝ → ℝ := fun t => ∫ v in (0 : ℝ)..t, k v
  have hK : ∀ t, HasDerivAt K (k t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 t)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  set g : ℝ → ℝ := fun s => k s * Real.exp (K s) * (w s - w 0)
  have hg : Continuous g := (hk.mul (Real.continuous_exp.comp (continuous_primitive' hk))).mul
    (hw.sub continuous_const)
  set F : ℝ → ℝ := fun t => Real.exp (-K t) * ∫ s in (0 : ℝ)..t, g s
  have hF : ∀ t, HasDerivAt F (k t * linPath k w t) t := by
    intro t
    have h1 : HasDerivAt (fun t => Real.exp (-K t)) (Real.exp (-K t) * -k t) t :=
      (hK t).neg.exp
    have h2 : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, g s) (g t) t :=
      intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
        hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    convert h1.mul h2 using 1
    rw [linPath_eq_aux hk t]
    simp only [g, K]
    have : Real.exp (-∫ v in (0 : ℝ)..t, k v) * Real.exp (∫ v in (0 : ℝ)..t, k v) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (-(k t * (w t - w 0))) * this
  have hint : ∫ s in (0 : ℝ)..t, k s * linPath k w s = F t - F 0 :=
    integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
      ((hk.mul (continuous_linPath hk hw)).intervalIntegrable 0 t)
  rw [hint]
  simp only [F, intervalIntegral.integral_same, mul_zero, sub_zero]
  rw [linPath_eq_aux hk t]

/-- **Uniqueness of the pathwise first-order term**: a continuous solution of
`y(t) = w(t) - w(0) - ∫₀ᵗ k y` on `[0, T]` is `linPath k w`. -/
theorem linPath_unique {k w y : ℝ → ℝ} (hk : Continuous k) (hw : Continuous w)
    (hy : Continuous y) {T : ℝ}
    (hyeq : ∀ t ∈ Icc 0 T, y t = (w t - w 0) - ∫ s in (0 : ℝ)..t, k s * y s) :
    ∀ t ∈ Icc 0 T, y t = linPath k w t := by
  set e : ℝ → ℝ := fun t => y t - linPath k w t
  have he : Continuous e := hy.sub (continuous_linPath hk hw)
  set E : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, k s * e s
  have hE : ∀ t, HasDerivAt E (k t * e t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right ((hk.mul he).intervalIntegrable 0 t)
      (hk.mul he).aestronglyMeasurable.stronglyMeasurableAtFilter (hk.mul he).continuousAt
  have heE : ∀ t ∈ Icc 0 T, e t = -E t := by
    intro t ht
    have h1 := hyeq t ht
    have h2 := linPath_eq hk hw t
    have h3 : E t = (∫ s in (0 : ℝ)..t, k s * y s) - ∫ s in (0 : ℝ)..t, k s * linPath k w s := by
      have i1 : IntervalIntegrable (fun s => k s * y s) volume 0 t :=
        (hk.mul hy).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun s => k s * linPath k w s) volume 0 t :=
        (hk.mul (continuous_linPath hk hw)).intervalIntegrable _ _
      rw [← intervalIntegral.integral_sub i1 i2]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [e]; ring
    simp only [e]
    linarith
  set K : ℝ → ℝ := fun t => ∫ v in (0 : ℝ)..t, k v
  have hK : ∀ t, HasDerivAt K (k t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 t)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  set H : ℝ → ℝ := fun t => E t * Real.exp (K t)
  have hH : ∀ t, HasDerivAt H (k t * e t * Real.exp (K t) + E t * (Real.exp (K t) * k t)) t :=
    fun t => (hE t).mul (hK t).exp
  have hHc : ContinuousOn H (Icc 0 T) :=
    (continuous_iff_continuousAt.mpr fun t => (hH t).continuousAt).continuousOn
  have hH0 : ∀ t ∈ Ico 0 T, HasDerivWithinAt H 0 (Ici t) t := by
    intro t ht
    have := (hH t).hasDerivWithinAt (s := Ici t)
    convert this using 1
    rw [heE t (Ico_subset_Icc_self ht)]; ring
  have hconst := constant_of_has_deriv_right_zero hHc hH0
  intro t ht
  have h1 : H t = H 0 := hconst t ht
  simp only [H, E, intervalIntegral.integral_same, zero_mul] at h1
  have h2 : E t = 0 := by
    have := mul_eq_zero.mp h1
    rcases this with h | h
    · exact h
    · exact absurd h (Real.exp_pos _).ne'
  have := heE t ht
  rw [h2, neg_zero] at this
  simp only [e] at this
  linarith

/-! ### The linearised process as a Wiener integral -/

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- **The linearised process** (6.2.14), `x₁(t) = ∫₀ᵗ b(t') e^{-∫_{t'}^t k} dW(t')`, a Wiener
integral of a deterministic integrand. -/
def linProc (W : ℝ → Ω → ℝ) (P : Measure Ω) (k b : ℝ → ℝ) (t : ℝ) : Ω → ℝ :=
  wienerInt W P (fun s => b s * linKernel k t s) 0 t

lemma continuous_kernel {k b : ℝ → ℝ} (hk : Continuous k) (hb : Continuous b) (t : ℝ) :
    Continuous fun s => b s * linKernel k t s :=
  hb.mul (continuous_linKernel hk t)

namespace IsWiener

variable (hW : IsWiener W P) {k b : ℝ → ℝ}
include hW

/-- **The law of the linearised process** (6.2.14): for continuous `k`, `b`, the Wiener integral
`x₁(t) = ∫₀ᵗ b(t') e^{-∫_{t'}^t k} dW(t')` has mean zero and covariance
`⟨x₁(t) x₁(s)⟩ = ∫₀ˢ b(u)² e^{-∫ᵤᵗ k - ∫ᵤˢ k} du` (`s ≤ t`), i.e. it satisfies the former named
hypothesis `Gardiner.SDE.IsLinearisedLaw`. -/
theorem isLinearisedLaw_linProc (hk : Continuous k) (hb : Continuous b) :
    IsLinearisedLaw P (linProc W P k b) k b where
  mean t ht := hW.wienerInt_mean (continuous_kernel hk hb t) le_rfl ht
  cov s t hs hst := by
    rw [linProc, linProc, hW.wienerInt_mul_same (continuous_kernel hk hb t)
      (continuous_kernel hk hb s) le_rfl (hs.trans hst) hs, min_eq_right hst]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [linKernel]
    rw [show b u * Real.exp (-∫ v in u..t, k v) * (b u * Real.exp (-∫ v in u..s, k v)) =
      (Real.exp (-∫ v in u..t, k v) * Real.exp (-∫ v in u..s, k v)) * b u ^ 2 by ring,
      ← Real.exp_add]
    ring_nf

/-- (6.2.32), leading term, now unconditional: `⟨x₁(t) x₁(s)⟩ = e^{-∫ₛᵗ k} V(s)`. -/
theorem linProc_correlation (hk : Continuous k) (hb : Continuous b) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    ∫ ω, linProc W P k b t ω * linProc W P k b s ω ∂P = linCov k b t s :=
  (hW.isLinearisedLaw_linProc hk hb).correlation_eq hk hs hst

/-- (6.2.31), leading term, now unconditional: `var{x₁(t)} = V(t)`. -/
theorem linProc_variance (hk : Continuous k) (hb : Continuous b) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, linProc W P k b t ω * linProc W P k b t ω ∂P - (∫ ω, linProc W P k b t ω ∂P) ^ 2 =
      linVar k b t :=
  (hW.isLinearisedLaw_linProc hk hb).variance_eq hk ht

/-- The linearised process is Gaussian: `x₁(t) ~ N(0, V(t))`. -/
theorem linProc_map (hk : Continuous k) (hb : Continuous b) {t : ℝ} (ht : 0 ≤ t) :
    P.map (linProc W P k b t) = gaussianReal 0 (linVar k b t).toNNReal := by
  rw [linProc, hW.wienerInt_map (continuous_kernel hk hb t) le_rfl ht, linVar]
  congr 2
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [linKernel]
  rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- **The Wiener integral and the pathwise first-order term agree almost surely** (additive noise,
`b = 1`): `∫₀ᵗ e^{-∫ₛᵗ k} dW(s) = linPath k W(·, ω) t` a.s.  (Integration by parts.) -/
theorem linProc_ae_linPath (hk : Continuous k) {t : ℝ} (ht : 0 ≤ t) :
    linProc W P k (fun _ => 1) t =ᵐ[P] fun ω => linPath k (fun s => W s ω) t := by
  have hfun : (fun s => (fun _ => (1 : ℝ)) s * linKernel k t s) = linKernel k t := by
    funext s; simp
  rw [linProc, hfun]
  filter_upwards [hW.wienerInt_ibp (hasDerivAt_linKernel hk t)
    (hk.mul (continuous_linKernel hk t)) le_rfl ht, hW.cont] with ω hω hc
  rw [hω, linPath, linKernel_self]
  have hi1 : IntervalIntegrable (fun s => k s * linKernel k t s * W s ω) volume 0 t :=
    ((hk.mul (continuous_linKernel hk t)).mul hc).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => k s * linKernel k t s * W 0 ω) volume 0 t :=
    ((hk.mul (continuous_linKernel hk t)).mul continuous_const).intervalIntegrable _ _
  have e1 : ∫ s in (0 : ℝ)..t, k s * linKernel k t s * (W s ω - W 0 ω) =
      (∫ s in (0 : ℝ)..t, k s * linKernel k t s * W s ω) -
        (∫ s in (0 : ℝ)..t, k s * linKernel k t s) * W 0 ω := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub hi1 hi2]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  rw [e1, integral_k_linKernel hk t]
  ring

/-- **Relation with the pathwise small-noise hierarchy** (6.2.10)–(6.2.14) for additive noise:
if, almost surely, `X(ω)` is a hierarchy of `dx = a(x)dt + ε dW` driven by the path of `W` whose
zeroth-order term is a given deterministic path `φ`, then for every `t ∈ [0, T]` its first-order
term is almost surely the Wiener integral `∫₀ᵗ e^{-∫ₛᵗ k} dW(s)` with `k = -a'(φ)`. -/
theorem hierarchy_first_order_ae {Da : ℕ → ℝ → ℝ} (hDa : Continuous (Da 1)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {x0 : ℝ} {N : ℕ} (hN : 1 ≤ N) {T : ℝ} {X : Ω → ℕ → ℝ → ℝ}
    (hX : ∀ᵐ ω ∂P, IsHierarchy Da (fun t => W t ω) x0 (X ω) N T ∧ X ω 0 = φ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    (fun ω => X ω 1 t) =ᵐ[P] linProc W P (fun s => -Da 1 (φ s)) (fun _ => 1) t := by
  have hk : Continuous fun s => -Da 1 (φ s) := (hDa.comp hφ).neg
  filter_upwards [hX, hW.cont, hW.linProc_ae_linPath hk ht.1] with ω ⟨hH, h0⟩ hc hlin
  rw [hlin]
  refine linPath_unique hk hc (hH.cont 1) (fun s hs => ?_) t ht
  rw [hH.eq 1 hN s hs]
  simp only [one_ne_zero, if_false, if_true, zero_add]
  have : ∫ u in (0 : ℝ)..s, -Da 1 (φ u) * X ω 1 u = -∫ u in (0 : ℝ)..s, hierDrift Da (X ω) 1 u := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hierDrift, snCoeff_one, h0]
    ring
  rw [this]; ring

end IsWiener

/-! ### Brownian instance: the pathwise Ornstein–Uhlenbeck process of `Gardiner.Ito.ouPath` -/

lemma ouPath_eq_linPath (w : ℝ → ℝ) (t : ℝ) : ouPath w t = linPath (fun _ => 1) w t := by
  rw [ouPath, linPath, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [linKernel_const, one_mul]
  rw [show -1 * (t - s) = -t + s by ring, Real.exp_add]
  ring

/-- **Instance.**  The first-order term `ouPath` of the linearisation of `dx = -sin x dt + ε dW`
(`Gardiner.Ito.sin_linearisation_stdWiener`), driven by the standard Wiener process, is almost
surely the Wiener integral `∫₀ᵗ e^{-(t-s)} dW(s)`, satisfies `Gardiner.SDE.IsLinearisedLaw` with
`k = b = 1`, and has variance `(1 - e^{-2t})/2`. -/
theorem ouPath_stdWiener_law :
    (∀ t, 0 ≤ t → (fun ω => ouPath (fun s => stdWiener s ω) t) =ᵐ[stdWienerMeasure]
      linProc stdWiener stdWienerMeasure (fun _ => 1) (fun _ => 1) t) ∧
    IsLinearisedLaw stdWienerMeasure (fun t ω => ouPath (fun s => stdWiener s ω) t)
      (fun _ => 1) (fun _ => 1) ∧
    ∀ t, 0 ≤ t → ∫ ω, ouPath (fun s => stdWiener s ω) t ^ 2 ∂stdWienerMeasure =
      (1 - Real.exp (-2 * t)) / 2 := by
  have hW := isWiener_stdWiener
  have hae : ∀ t, 0 ≤ t → (fun ω => ouPath (fun s => stdWiener s ω) t) =ᵐ[stdWienerMeasure]
      linProc stdWiener stdWienerMeasure (fun _ => 1) (fun _ => 1) t := by
    intro t ht
    filter_upwards [hW.linProc_ae_linPath continuous_const ht] with ω hω
    rw [hω, ouPath_eq_linPath]
  have hL := hW.isLinearisedLaw_linProc (k := fun _ => 1) (b := fun _ => 1) continuous_const
    continuous_const
  have hlaw : IsLinearisedLaw stdWienerMeasure (fun t ω => ouPath (fun s => stdWiener s ω) t)
      (fun _ => 1) (fun _ => 1) := by
    refine ⟨fun t ht => ?_, fun s t hs hst => ?_⟩
    · rw [integral_congr_ae (hae t ht)]; exact hL.mean t ht
    · rw [← hL.cov s t hs hst]
      refine integral_congr_ae ?_
      filter_upwards [hae t (hs.trans hst), hae s hs] with ω h1 h2
      simp only [h1, h2]
  refine ⟨hae, hlaw, fun t ht => ?_⟩
  have h := hlaw.variance_eq continuous_const ht
  rw [hlaw.mean t ht, linVar_const one_ne_zero] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at h
  simp_rw [sq]
  rw [h]; ring_nf

end Gardiner.Ito
