/-
# Stationary solutions, mean, variance and time correlation (Gardiner §6.2.2–§6.2.3)

Gardiner (6.2.14), (6.2.26)–(6.2.32).  The linearised process (6.2.13)–(6.2.14),
`dx₁ = -k(t) x₁ dt + b(t) dW`, `x₁(0) = 0`, is a time-dependent Ornstein–Uhlenbeck process.
Everything the text derives about its statistics is deterministic once the **law** of `x₁` is
known; that law needs the Itô isometry, so we take it as a named hypothesis
(`Gardiner.SDE.IsLinearisedLaw`: mean zero and the covariance
`⟨x₁(t)x₁(s)⟩ = ∫₀^{s} b(u)² e^{-∫ᵤᵗk - ∫ᵤˢk} du`, `s ≤ t`, which is what the Itô isometry gives
for (6.2.14)).  From it we derive:

* the variance `V(t) = ∫₀ᵗ b(s)² e^{-2∫ₛᵗ k} ds` (`Gardiner.SDE.linVar`) solves the moment equation
  `V' = -2kV + b²`, `V(0) = 0`, and is its unique solution (`Gardiner.SDE.linVar_hasDerivAt`,
  `Gardiner.SDE.linVar_unique`, `Gardiner.SDE.IsLinearisedLaw.variance_eq`);
* the time correlation `⟨x₁(t)x₁(s)⟩ = e^{-∫ₛᵗ k} V(s)` for `s ≤ t`
  (`Gardiner.SDE.IsLinearisedLaw.correlation_eq`), which solves the regression equation
  `∂ₜ C(t, s) = -k(t) C(t, s)` (`Gardiner.SDE.linCov_hasDerivAt`);
* §6.2.2, stationary solutions (6.2.26)–(6.2.27): for constant `k > 0`,
  `V(t) = b²(1 - e^{-2kt})/2k → b²/2k` with error exactly `(b²/2k) e^{-2kt}`
  (`Gardiner.SDE.linVar_const`, `Gardiner.SDE.linVar_stationary_error`,
  `Gardiner.SDE.linVar_tendsto_stationary`), and the correlation tends to the stationary
  `(b²/2k) e^{-k(t-s)}` (`Gardiner.SDE.linCov_stationary_error`).  For `k = 0` (the cubic case
  (6.2.34)–(6.2.35)) `V(t) = b²t` is unbounded (`Gardiner.SDE.linVar_k_zero`,
  `Gardiner.SDE.linVar_k_zero_unbounded`), and for `k < 0` (unstable state) `V(t) → ∞`
  (`Gardiner.SDE.linVar_tendsto_atTop_of_neg`): only stable states give a stationary solution;
* §6.2.3, (6.2.29)–(6.2.32): the covariance of two truncated expansions is the double sum
  `Σ_{m,n} εᵐ⁺ⁿ ⟨xₘ, yₙ⟩` (`Gardiner.SDE.cov_expansion`), and with `x₀` deterministic this gives
  the variance (6.2.31) and correlation (6.2.32) to every order shown in the text
  (`Gardiner.SDE.var_expansion_three`, `Gardiner.SDE.cov_expansion_three`).  **Erratum
  (6.2.30)**: the outer index is `n` (printed `s`) and the inner sum runs over `0 ≤ m ≤ n`
  (printed `∞`).
* the mean (6.2.29) with an error term: a pathwise remainder bound `|x - Σ_{n≤N} εⁿxₙ| ≤ C|ε|^{N+1}`
  with integrable `C` (e.g. `Gardiner.SDE.pathwise_expansion` applied path by path) gives
  `|⟨x⟩ - Σ εⁿ⟨xₙ⟩| ≤ ⟨C⟩ |ε|^{N+1}` (`Gardiner.SDE.mean_expansion_of_pathwise`).
-/
import SHSLib.Gardiner.SDE.Pathwise
import SHSLib.Gardiner.Approx.Calculus

open Set Finset MeasureTheory ProbabilityTheory intervalIntegral Filter Topology

noncomputable section

namespace Gardiner.SDE

/-! ### The variance equation of the linearised process -/

/-- The variance of the linearised process (6.2.14), `V(t) = ∫₀ᵗ b(s)² e^{-2∫ₛᵗ k} ds`. -/
def linVar (k b : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (-2 * ∫ u in s..t, k u) * b s ^ 2

/-- The time correlation `C(t, s) = e^{-∫ₛᵗ k} V(s)` (`s ≤ t`). -/
def linCov (k b : ℝ → ℝ) (t s : ℝ) : ℝ := Real.exp (-∫ u in s..t, k u) * linVar k b s

lemma integral_sub_split {k : ℝ → ℝ} (hk : Continuous k) (s t : ℝ) :
    ∫ u in s..t, k u = (∫ u in (0 : ℝ)..t, k u) - ∫ u in (0 : ℝ)..s, k u := by
  rw [intervalIntegral.integral_interval_sub_left (hk.intervalIntegrable _ _)
    (hk.intervalIntegrable _ _)]

lemma linVar_eq_prod {k b : ℝ → ℝ} (hk : Continuous k) (t : ℝ) :
    linVar k b t = Real.exp (-2 * ∫ u in (0 : ℝ)..t, k u) *
      ∫ s in (0 : ℝ)..t, Real.exp (2 * ∫ u in (0 : ℝ)..s, k u) * b s ^ 2 := by
  rw [linVar, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [integral_sub_split hk s t, ← mul_assoc, ← Real.exp_add]
  ring_nf

lemma linVar_zero (k b : ℝ → ℝ) : linVar k b 0 = 0 := by simp [linVar]

/-- The variance solves the moment equation `V' = -2k V + b²`. -/
theorem linVar_hasDerivAt {k b : ℝ → ℝ} (hk : Continuous k) (hb : Continuous b) (t : ℝ) :
    HasDerivAt (linVar k b) (-2 * k t * linVar k b t + b t ^ 2) t := by
  set K : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, k u
  have hK : ∀ t, HasDerivAt K (k t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 t)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hKc : Continuous K := continuous_iff_continuousAt.mpr fun t => (hK t).continuousAt
  set g : ℝ → ℝ := fun s => Real.exp (2 * K s) * b s ^ 2
  have hgc : Continuous g := (Real.continuous_exp.comp (continuous_const.mul hKc)).mul (hb.pow 2)
  have hG : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, g s) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 t)
      hgc.aestronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
  have hE : HasDerivAt (fun t => Real.exp (-2 * K t)) (Real.exp (-2 * K t) * (-2 * k t)) t :=
    ((hK t).const_mul (-2)).exp
  have hfun : linVar k b = fun t => Real.exp (-2 * K t) * ∫ s in (0 : ℝ)..t, g s := by
    funext t; exact linVar_eq_prod hk t
  rw [hfun]
  convert hE.mul hG using 1
  simp only [g]
  rw [show Real.exp (-2 * K t) * (Real.exp (2 * K t) * b t ^ 2) = b t ^ 2 by
    rw [← mul_assoc, ← Real.exp_add]; simp]
  ring

/-- Uniqueness: `V` is the only solution of `V' = -2kV + b²` with `V(0) = 0`. -/
theorem linVar_unique {k b : ℝ → ℝ} (hk : Continuous k) (hb : Continuous b) (V : ℝ → ℝ)
    (hV : ∀ t, HasDerivAt V (-2 * k t * V t + b t ^ 2) t) (h0 : V 0 = 0) : V = linVar k b :=
  Gardiner.linear_ode_unique (fun t => -2 * k t) (fun t => b t ^ 2)
    (continuous_const.mul hk) (hb.pow 2) V (linVar k b) hV (linVar_hasDerivAt hk hb)
    (by rw [h0, linVar_zero])

/-- The regression equation for the time correlation, `∂ₜ C(t, s) = -k(t) C(t, s)`. -/
theorem linCov_hasDerivAt {k b : ℝ → ℝ} (hk : Continuous k) (s t : ℝ) :
    HasDerivAt (fun t => linCov k b t s) (-k t * linCov k b t s) t := by
  have hK : HasDerivAt (fun t => ∫ u in s..t, k u) (k t) t :=
    intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable s t)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have := (hK.neg.exp).mul_const (linVar k b s)
  convert this using 1
  simp only [linCov, Pi.neg_apply]; ring

lemma linCov_self (k b : ℝ → ℝ) (s : ℝ) : linCov k b s s = linVar k b s := by
  simp [linCov]

/-! ### The law of the linearised process as a named hypothesis -/

/-- **Named hypothesis**: the law of the linearised process (6.2.14).  For a Wiener process `W`,
`x₁(t) = ∫₀ᵗ b(t') e^{-∫_{t'}^t k} dW(t')` has mean zero and, by the Itô isometry, the covariance
below.  (Constructing `W` and the Itô integral is outside the scope of this layer.) -/
structure IsLinearisedLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ → Ω → ℝ)
    (k b : ℝ → ℝ) : Prop where
  mean : ∀ t, 0 ≤ t → ∫ ω, X t ω ∂P = 0
  cov : ∀ s t, 0 ≤ s → s ≤ t → ∫ ω, X t ω * X s ω ∂P =
    ∫ u in (0 : ℝ)..s, Real.exp (-(∫ v in u..t, k v) - ∫ v in u..s, k v) * b u ^ 2

namespace IsLinearisedLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ → Ω → ℝ} {k b : ℝ → ℝ}

/-- (6.2.32), leading term: `⟨x₁(t)x₁(s)⟩ = e^{-∫ₛᵗ k} V(s)` for `0 ≤ s ≤ t`. -/
theorem correlation_eq (h : IsLinearisedLaw P X k b) (hk : Continuous k) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : ∫ ω, X t ω * X s ω ∂P = linCov k b t s := by
  rw [h.cov s t hs hst, linCov, linVar, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hk.intervalIntegrable u s)
    (hk.intervalIntegrable s t)]
  ring

/-- (6.2.31), leading term: `var{x₁(t)} = V(t)`. -/
theorem variance_eq (h : IsLinearisedLaw P X k b) (hk : Continuous k) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, X t ω * X t ω ∂P - (∫ ω, X t ω ∂P) ^ 2 = linVar k b t := by
  rw [h.correlation_eq hk ht le_rfl, h.mean t ht, linCov_self]; ring

end IsLinearisedLaw

/-! ### Stationary solutions (6.2.26)–(6.2.28) and their failure -/

/-- For constant `k ≠ 0`, `b`: `V(t) = b²(1 - e^{-2kt})/(2k)`. -/
theorem linVar_const {k : ℝ} (hk : k ≠ 0) (b t : ℝ) :
    linVar (fun _ => k) (fun _ => b) t = b ^ 2 * (1 - Real.exp (-2 * k * t)) / (2 * k) := by
  have h := linVar_unique (k := fun _ => k) (b := fun _ => b) continuous_const continuous_const
    (fun t => b ^ 2 * (1 - Real.exp (-2 * k * t)) / (2 * k)) (fun t => by
      have := (((hasDerivAt_id t).const_mul (-2 * k)).exp.const_sub 1).const_mul (b ^ 2)
        |>.div_const (2 * k)
      convert this using 1
      simp only [id]
      field_simp
      ring) (by simp)
  rw [← h]

/-- (6.2.34)–(6.2.35): for `k = 0` the variance `V(t) = b² t` grows without bound. -/
theorem linVar_k_zero (b t : ℝ) : linVar (fun _ => 0) (fun _ => b) t = b ^ 2 * t := by
  simp [linVar]; ring

theorem linVar_k_zero_unbounded {b : ℝ} (hb : b ≠ 0) (C : ℝ) :
    ∃ t, C < linVar (fun _ => 0) (fun _ => b) t := by
  refine ⟨(|C| + 1) / b ^ 2, ?_⟩
  rw [linVar_k_zero, mul_div_cancel₀ _ (by positivity)]
  linarith [le_abs_self C]

/-- §6.2.2, stable state `k > 0`: the variance approaches the stationary value `b²/2k` with error
exactly `(b²/2k) e^{-2kt}`. -/
theorem linVar_stationary_error {k : ℝ} (hk : 0 < k) (b t : ℝ) :
    |linVar (fun _ => k) (fun _ => b) t - b ^ 2 / (2 * k)| =
      b ^ 2 / (2 * k) * Real.exp (-2 * k * t) := by
  rw [linVar_const hk.ne']
  rw [show b ^ 2 * (1 - Real.exp (-2 * k * t)) / (2 * k) - b ^ 2 / (2 * k) =
      -(b ^ 2 / (2 * k) * Real.exp (-2 * k * t)) by field_simp; ring, abs_neg,
    abs_of_nonneg (by positivity)]

theorem linVar_tendsto_stationary {k : ℝ} (hk : 0 < k) (b : ℝ) :
    Tendsto (linVar (fun _ => k) (fun _ => b)) atTop (𝓝 (b ^ 2 / (2 * k))) := by
  have h : Tendsto (fun t => b ^ 2 * (1 - Real.exp (-2 * k * t)) / (2 * k)) atTop
      (𝓝 (b ^ 2 * (1 - 0) / (2 * k))) := by
    refine ((tendsto_const_nhds.sub ?_).const_mul _).div_const _
    have h1 : Tendsto (fun t : ℝ => -2 * k * t) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
    exact Real.tendsto_exp_atBot.comp h1
  simp only [sub_zero, mul_one] at h
  exact h.congr fun t => (linVar_const hk.ne' b t).symm

/-- §6.2.2, stationary correlation (6.2.27): for `k > 0`, `0 ≤ s ≤ t`,
`|C(t, s) - (b²/2k) e^{-k(t-s)}| ≤ (b²/2k) e^{-2ks}`. -/
theorem linCov_stationary_error {k : ℝ} (hk : 0 < k) (b : ℝ) {s t : ℝ} (hst : s ≤ t) :
    |linCov (fun _ => k) (fun _ => b) t s - b ^ 2 / (2 * k) * Real.exp (-k * (t - s))| ≤
      b ^ 2 / (2 * k) * Real.exp (-2 * k * s) := by
  have hint : ∫ _ in s..t, k = (t - s) * k := by simp
  rw [linCov, hint, linVar_const hk.ne']
  have h1 : Real.exp (-((t - s) * k)) * (b ^ 2 * (1 - Real.exp (-2 * k * s)) / (2 * k)) -
      b ^ 2 / (2 * k) * Real.exp (-k * (t - s)) =
      -(b ^ 2 / (2 * k) * Real.exp (-2 * k * s) * Real.exp (-((t - s) * k))) := by
    rw [show -k * (t - s) = -((t - s) * k) by ring]; field_simp; ring
  rw [h1, abs_neg, abs_of_nonneg (by positivity)]
  have : Real.exp (-((t - s) * k)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc b ^ 2 / (2 * k) * Real.exp (-2 * k * s) * Real.exp (-((t - s) * k))
      ≤ b ^ 2 / (2 * k) * Real.exp (-2 * k * s) * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := mul_one _

/-- Unstable state `k < 0`: the variance diverges, so no stationary solution arises. -/
theorem linVar_tendsto_atTop_of_neg {k : ℝ} (hk : k < 0) {b : ℝ} (hb : b ≠ 0) :
    Tendsto (linVar (fun _ => k) (fun _ => b)) atTop atTop := by
  have hfun : linVar (fun _ => k) (fun _ => b) =
      fun t => b ^ 2 / (2 * -k) * (Real.exp (-2 * k * t) - 1) := by
    funext t; rw [linVar_const hk.ne]; field_simp; ring
  rw [hfun]
  have hb2 : 0 < b ^ 2 := by positivity
  refine Tendsto.const_mul_atTop (div_pos hb2 (by linarith)) ?_
  refine tendsto_atTop_add_const_right _ (-1) ?_
  exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))

/-! ### The expansion of mean, variance and correlation (6.2.29)–(6.2.32) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- (6.2.30), (6.2.32), corrected: the covariance of two truncated expansions is the double sum
`Σ_{m,n ≤ N} εᵐ⁺ⁿ ⟨xₘ, yₙ⟩`. -/
theorem cov_expansion [IsFiniteMeasure P] (X Y : ℕ → Ω → ℝ) (N : ℕ) (ε : ℝ)
    (hX : ∀ n, MemLp (X n) 2 P) (hY : ∀ n, MemLp (Y n) 2 P) :
    cov[fun ω => ∑ m ∈ range (N + 1), ε ^ m * X m ω,
        fun ω => ∑ n ∈ range (N + 1), ε ^ n * Y n ω; P] =
      ∑ m ∈ range (N + 1), ∑ n ∈ range (N + 1), ε ^ (m + n) * cov[X m, Y n; P] := by
  have h := covariance_fun_sum_fun_sum' (μ := P) (s := range (N + 1)) (t := range (N + 1))
    (X := fun m ω => ε ^ m * X m ω) (Y := fun n ω => ε ^ n * Y n ω)
    (fun i _ => (hX i).const_mul _) (fun i _ => (hY i).const_mul _)
  rw [h]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right, pow_add]; ring

/-- (6.2.32) to the orders shown in the text: with `x₀(t)`, `x₀(s)` deterministic,
`⟨x(t), x(s)⟩ = ε²⟨x₁,y₁⟩ + ε³(⟨x₁,y₂⟩ + ⟨x₂,y₁⟩) + ε⁴(⟨x₁,y₃⟩ + ⟨x₃,y₁⟩ + ⟨x₂,y₂⟩)
+ ε⁵(⟨x₂,y₃⟩ + ⟨x₃,y₂⟩) + ε⁶⟨x₃,y₃⟩` for the third-order truncation
(`xₙ = xₙ(t)`, `yₙ = xₙ(s)`). -/
theorem cov_expansion_three [IsProbabilityMeasure P] (X Y : ℕ → Ω → ℝ) (ε : ℝ)
    (hX : ∀ n, MemLp (X n) 2 P) (hY : ∀ n, MemLp (Y n) 2 P)
    (hX0 : ∃ c, X 0 = fun _ => c) (hY0 : ∃ c, Y 0 = fun _ => c) :
    cov[fun ω => ∑ m ∈ range 4, ε ^ m * X m ω, fun ω => ∑ n ∈ range 4, ε ^ n * Y n ω; P] =
      ε ^ 2 * cov[X 1, Y 1; P] + ε ^ 3 * (cov[X 1, Y 2; P] + cov[X 2, Y 1; P]) +
      ε ^ 4 * (cov[X 1, Y 3; P] + cov[X 3, Y 1; P] + cov[X 2, Y 2; P]) +
      ε ^ 5 * (cov[X 2, Y 3; P] + cov[X 3, Y 2; P]) + ε ^ 6 * cov[X 3, Y 3; P] := by
  obtain ⟨c, hc⟩ := hX0
  obtain ⟨d, hd⟩ := hY0
  rw [cov_expansion X Y 3 ε hX hY]
  have h0l : ∀ n, cov[X 0, Y n; P] = 0 := fun n => by rw [hc, covariance_const_left]
  have h0r : ∀ m, cov[X m, Y 0; P] = 0 := fun m => by rw [hd, covariance_const_right]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h0l, h0r]
  ring

/-- (6.2.31): with `x₀` deterministic,
`var{x} = ε² var{x₁} + 2ε³⟨x₁,x₂⟩ + ε⁴(2⟨x₁,x₃⟩ + var{x₂}) + 2ε⁵⟨x₂,x₃⟩ + ε⁶ var{x₃}`
for the third-order truncation. -/
theorem var_expansion_three [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (ε : ℝ)
    (hX : ∀ n, MemLp (X n) 2 P) (hX0 : ∃ c, X 0 = fun _ => c) :
    Var[fun ω => ∑ m ∈ range 4, ε ^ m * X m ω; P] =
      ε ^ 2 * Var[X 1; P] + 2 * ε ^ 3 * cov[X 1, X 2; P] +
      ε ^ 4 * (2 * cov[X 1, X 3; P] + Var[X 2; P]) + 2 * ε ^ 5 * cov[X 2, X 3; P] +
      ε ^ 6 * Var[X 3; P] := by
  have hm : MemLp (fun ω => ∑ m ∈ range 4, ε ^ m * X m ω) 2 P :=
    memLp_finset_sum _ fun i _ => (hX i).const_mul _
  rw [← covariance_self hm.aemeasurable, cov_expansion_three X X ε hX hX hX0 hX0,
    ← covariance_self (hX 1).aemeasurable, ← covariance_self (hX 2).aemeasurable,
    ← covariance_self (hX 3).aemeasurable, covariance_comm (X := X 2) (Y := X 1),
    covariance_comm (X := X 3) (Y := X 1), covariance_comm (X := X 3) (Y := X 2)]
  ring

/-- (6.2.29) with an error term: if `|x - Σ_{n≤N} εⁿxₙ| ≤ C |ε|^{N+1}` almost surely with
`C` integrable, then `|⟨x⟩ - Σ_{n≤N} εⁿ⟨xₙ⟩| ≤ ⟨C⟩ |ε|^{N+1}`. -/
theorem mean_expansion_of_pathwise [IsFiniteMeasure P] (x C : Ω → ℝ) (X : ℕ → Ω → ℝ)
    (N : ℕ) (ε : ℝ) (hx : Integrable x P) (hX : ∀ n, Integrable (X n) P) (hC : Integrable C P)
    (hb : ∀ᵐ ω ∂P, |x ω - ∑ n ∈ range (N + 1), ε ^ n * X n ω| ≤ C ω * |ε| ^ (N + 1)) :
    |∫ ω, x ω ∂P - ∑ n ∈ range (N + 1), ε ^ n * ∫ ω, X n ω ∂P| ≤
      (∫ ω, C ω ∂P) * |ε| ^ (N + 1) := by
  have hS : Integrable (fun ω => ∑ n ∈ range (N + 1), ε ^ n * X n ω) P :=
    integrable_finset_sum _ fun n _ => (hX n).const_mul _
  have hsum : ∑ n ∈ range (N + 1), ε ^ n * ∫ ω, X n ω ∂P =
      ∫ ω, ∑ n ∈ range (N + 1), ε ^ n * X n ω ∂P := by
    rw [integral_finset_sum _ fun n _ => (hX n).const_mul _]
    simp [MeasureTheory.integral_const_mul]
  rw [hsum, ← integral_sub hx hS, ← MeasureTheory.integral_mul_const]
  refine (MeasureTheory.abs_integral_le_integral_abs).trans (integral_mono_ae ?_ (hC.mul_const _) hb)
  exact (hx.sub hS).abs

end Gardiner.SDE
