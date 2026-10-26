/-
# Failure of small-noise perturbation theory: the cubic process (Gardiner §6.2.4 a)

Gardiner (6.2.33)–(6.2.47).  For `dx = -x³dt + ε dW`:

* **finite time: the expansion is valid** (text after (6.2.33)).  At `x(0) = 0` the hierarchy is
  `x₀ = 0`, `x₁ = w - w(0)`, `x₂ = 0`, `x₃ = -∫₀ᵗ x₁³` (`Gardiner.SDE.cubicHier`,
  `Gardiner.SDE.cubicHier_isHierarchy`), and the pathwise theorem gives
  `|x(t) - εx₁(t) - ε³x₃(t)| ≤ C ε⁴` on `[0, T]` with an explicit `C` depending on `T` and on
  `sup |w - w(0)|` (`Gardiner.SDE.cubic_expansion`).  The drift is not globally Lipschitz; the
  one-sided Lipschitz version of the pathwise theorem applies with `L = 0`.
* **stationary: the expansion fails.**  (6.2.34) `k(0) = 0` (`Gardiner.SDE.cubic_k_zero`); the
  linearised variance with `k = 0` grows like `t` (`Gardiner.SDE.linVar_k_zero`, in
  `SHSLib.Gardiner.SDE.Statistics`), so (6.2.35) has no stationary limit.
* (6.2.36)–(6.2.37): `p_s ∝ exp(-x⁴/2ε²)` has zero probability current, hence solves the
  stationary Fokker–Planck equation (`Gardiner.SDE.cubic_ps_flux`, `Gardiner.SDE.cubic_ps_fpe`).
* (6.2.38): `⟨x²ᵏ⟩ = (2ε²)^{2k/4} Γ((2k+1)/4)/Γ(1/4)`, odd moments vanish
  (`Gardiner.SDE.cubic_moment_even`, `Gardiner.SDE.cubic_moment_odd`); in particular the
  variance is `√2 Γ(3/4)/Γ(1/4) · ε` (`Gardiner.SDE.cubic_variance`), of order `ε`, not `ε²`
  as (6.2.31) would predict (`Gardiner.SDE.cubic_variance_not_eps_sq`).
* (6.2.39)–(6.2.44): the scaling `x = √ε y`, `t = τ/ε`, pathwise: with the rescaled path
  `w̃(τ) = √ε w(τ/ε)` (which for a Wiener process is again a Wiener process — this is (6.2.40),
  a statement about laws that we do not need), `y` solves `dy = -y³c(√εy)dτ + b dw̃`
  (`Gardiner.SDE.cubic_scaling`, for drifts `a(x) = -x³c(x)` (6.2.43) and constant `b`).
* (6.2.45)–(6.2.47): the first-order coefficient of the drift `-y³c(√εy)` along
  `y = y₀ + √ε y₁` is `-(3y₀²c(0)y₁ + y₀⁴c'(0))` (`Gardiner.SDE.cubic_first_order`).
  **Erratum:** (6.2.47) prints `-y₁[3y₀²c(0) + y₀³c'(0)]`; the term `y₀⁴c'(0)` does not
  contain `y₁` (`Gardiner.SDE.cubic_first_order_printed_wrong`).
-/
import SHSLib.Gardiner.SDE.EulerPathwise

open Set Finset MeasureTheory intervalIntegral Real
open scoped Topology

noncomputable section

namespace Gardiner.SDE

/-! ### The cubic drift and its derivative tower -/

/-- The derivative tower of `a(x) = -x³`. -/
def cubicD : ℕ → ℝ → ℝ
  | 0 => fun z => -z ^ 3
  | 1 => fun z => -3 * z ^ 2
  | 2 => fun z => -6 * z
  | 3 => fun _ => -6
  | _ + 4 => fun _ => 0

lemma cubicD_hasDerivAt (k : ℕ) (y : ℝ) : HasDerivAt (cubicD k) (cubicD (k + 1) y) y := by
  match k with
  | 0 =>
    show HasDerivAt (fun z : ℝ => -z ^ 3) (-3 * y ^ 2) y
    have h := (hasDerivAt_pow 3 y).neg
    convert h using 1; push_cast; ring
  | 1 =>
    show HasDerivAt (fun z : ℝ => -3 * z ^ 2) (-6 * y) y
    have h := (hasDerivAt_pow 2 y).const_mul (-3)
    convert h using 1; push_cast; ring
  | 2 =>
    show HasDerivAt (fun z : ℝ => -6 * z) (-6) y
    simpa using (hasDerivAt_id y).const_mul (-6 : ℝ)
  | 3 => exact hasDerivAt_const y (-6 : ℝ)
  | k + 4 => exact hasDerivAt_const y (0 : ℝ)

lemma cubicD_continuous (p : ℕ) : Continuous (cubicD p) :=
  continuous_iff_continuousAt.mpr fun y => (cubicD_hasDerivAt p y).continuousAt

/-- (6.2.34): `k(0) = -a'(0) = 0` for `a = -x³`. -/
theorem cubic_k_zero : -cubicD 1 0 = 0 := by simp [cubicD]

/-- `-x³` is one-sided Lipschitz with constant `0` (it is monotone decreasing). -/
lemma cubic_osl (u v : ℝ) : (cubicD 0 u - cubicD 0 v) * (u - v) ≤ 0 * (u - v) ^ 2 := by
  simp only [cubicD, zero_mul]
  nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), sq_nonneg u, sq_nonneg v,
    mul_nonneg (sq_nonneg (u - v)) (add_nonneg (sq_nonneg (u + v)) (add_nonneg (sq_nonneg u)
      (sq_nonneg v)))]

/-! ### Finite time: the expansion at the origin is valid -/

/-- The pathwise hierarchy of the cubic process started at `0`:
`x₀ = 0`, `x₁ = w - w(0)`, `x₂ = 0`, `x₃ = -∫₀ᵗ x₁³`, `xₙ = 0` for `n ≥ 4`. -/
def cubicHier (w : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 1 => fun t => w t - w 0
  | 3 => fun t => -∫ s in (0 : ℝ)..t, (w s - w 0) ^ 3
  | _ => fun _ => 0

lemma continuous_primitive' {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun t => ∫ s in (0 : ℝ)..t, f s :=
  continuous_iff_continuousAt.mpr fun t =>
    (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).continuousAt

lemma cubicHier_cont {w : ℝ → ℝ} (hw : Continuous w) (n : ℕ) : Continuous (cubicHier w n) := by
  match n with
  | 0 => exact continuous_const
  | 1 => exact hw.sub continuous_const
  | 2 => exact continuous_const
  | 3 => exact (continuous_primitive' ((hw.sub continuous_const).pow 3)).neg
  | n + 4 => exact continuous_const

/-- The functions `cubicHier w` solve the hierarchy (6.2.10) up to order `3`. -/
theorem cubicHier_isHierarchy {w : ℝ → ℝ} (hw : Continuous w) (T : ℝ) :
    IsHierarchy cubicD w 0 (cubicHier w) 3 T := by
  refine ⟨cubicHier_cont hw, fun n hn t _ => ?_⟩
  interval_cases n
  · simp [hierDrift, snCoeff_zero, cubicHier, cubicD]
  · simp [hierDrift, snCoeff_one, cubicHier, cubicD]
  · simp [hierDrift, snCoeff_two, cubicHier, cubicD]
  · simp only [hierDrift, snCoeff_three]
    simp [cubicHier, cubicD, ← intervalIntegral.integral_neg]

/-- **The finite-time expansion of the cubic process is valid** (text after (6.2.33)), with an
explicit remainder: if `x` is a pathwise solution of `dx = -x³dt + ε dw` with `x(0) = 0` and
`|w(t) - w(0)| ≤ W` on `[0, T]`, then with `R = W + TW³` and `M = 6 + 24R + 48R² + 64R³`,

  `|x(t) - ε(w(t) - w(0)) + ε³∫₀ᵗ(w - w(0))³| ≤ T e^{1/2} · 2M e^{4R} · ε⁴`   on `[0, T]`,

for `|ε| ≤ 1`. -/
theorem cubic_expansion {ε T W : ℝ} (hε : |ε| ≤ 1) (hT : 0 < T) {w x : ℝ → ℝ}
    (hw : Continuous w) (hW : ∀ t ∈ Icc 0 T, |w t - w 0| ≤ W)
    (hx : IsPathSol (cubicD 0) ε w x T) (hx0 : x 0 = 0) :
    ∀ t ∈ Icc 0 T, |x t - (ε * (w t - w 0) + ε ^ 3 * -∫ s in (0 : ℝ)..t, (w s - w 0) ^ 3)| ≤
      T * Real.exp (1 / 2) *
        (2 * (6 + 24 * (W + T * W ^ 3) + 48 * (W + T * W ^ 3) ^ 2 + 64 * (W + T * W ^ 3) ^ 3) *
          Real.exp (4 * (W + T * W ^ 3))) * ε ^ 4 := by
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0 ⟨le_rfl, hT.le⟩)
  set R := W + T * W ^ 3 with hRdef
  have hR : 0 ≤ R := by positivity
  have hH : IsHierarchy cubicD w (x 0) (cubicHier w) 3 T := by
    rw [hx0]; exact cubicHier_isHierarchy hw T
  -- bounds on the hierarchy
  have hx3 : ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, (w s - w 0) ^ 3| ≤ T * W ^ 3 := by
    intro t ht
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := W ^ 3)
      (f := fun s => (w s - w 0) ^ 3) (fun s hs => by
        rw [Set.uIoc_of_le ht.1] at hs
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hW s ⟨hs.1.le, hs.2.trans ht.2⟩) 3)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at this
    calc _ ≤ W ^ 3 * t := this
      _ ≤ W ^ 3 * T := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = T * W ^ 3 := mul_comm _ _
  have hxR : ∀ m, 1 ≤ m → m ≤ 3 → ∀ t ∈ Icc 0 T, |cubicHier w m t| ≤ R := by
    intro m h1 h2 t ht
    interval_cases m
    · simp only [cubicHier]; have := hW t ht; nlinarith [pow_nonneg hW0 3, hT.le]
    · simp [cubicHier]; positivity
    · simp only [cubicHier, abs_neg]; have := hx3 t ht; nlinarith
  have hM : ∀ p ≤ 3 + 1, ∀ t ∈ Icc 0 T, ∀ z, |z - cubicHier w 0 t| ≤ (((3 : ℕ) : ℝ) + 1) * R →
      |cubicD p z| ≤ 6 + 24 * R + 48 * R ^ 2 + 64 * R ^ 3 := by
    intro p hp t _ z hz
    simp only [cubicHier, sub_zero] at hz
    push_cast at hz
    have hz' : |z| ≤ 4 * R := by linarith
    have hz2 : z ^ 2 ≤ 16 * R ^ 2 := by
      have := sq_abs z ▸ pow_le_pow_left₀ (abs_nonneg z) hz' 2; nlinarith
    interval_cases p
    · simp only [cubicD, abs_neg, abs_pow]
      have := pow_le_pow_left₀ (abs_nonneg z) hz' 3
      nlinarith [sq_nonneg R, pow_nonneg hR 3]
    · simp only [cubicD, abs_mul, abs_neg, abs_pow, sq_abs]
      norm_num; nlinarith [sq_nonneg R, pow_nonneg hR 3]
    · simp only [cubicD, abs_mul, abs_neg]
      norm_num; nlinarith [sq_nonneg R, pow_nonneg hR 3]
    · simp only [cubicD]; norm_num; nlinarith [sq_nonneg R, pow_nonneg hR 3]
    · simp only [cubicD]; norm_num; nlinarith [sq_nonneg R, pow_nonneg hR 3]
  have h := pathwise_expansion 3 (by norm_num) cubicD (fun k _ y => cubicD_hasDerivAt k y)
    cubicD_continuous le_rfl cubic_osl hε hT hR hx hH hxR hM
  intro t ht
  have ht' := h t ht
  simp only [partialSum, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    cubicHier] at ht'
  norm_num at ht'
  convert ht' using 2
  · ring
  · have : |ε| ^ 4 = ε ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
    rw [this]

/-! ### The stationary distribution (6.2.36)–(6.2.38) -/

/-- (6.2.37): the (unnormalised) stationary density `exp(-x⁴/2ε²)`. -/
def cubicPs (ε : ℝ) (x : ℝ) : ℝ := Real.exp (-x ^ 4 / (2 * ε ^ 2))

lemma cubicPs_hasDerivAt (ε x : ℝ) :
    HasDerivAt (cubicPs ε) (-(2 * x ^ 3 / ε ^ 2) * cubicPs ε x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 4 / (2 * ε ^ 2)) (-(4 * x ^ 3) / (2 * ε ^ 2)) x := by
    have := ((hasDerivAt_pow 4 x).neg).div_const (2 * ε ^ 2)
    convert this using 1
  have h2 := h1.exp
  convert h2 using 1
  simp only [cubicPs]
  by_cases hε : ε = 0
  · simp [hε]
  · field_simp
    ring

/-- (6.2.36)–(6.2.37): the probability current `J = -x³ p - ½ ε² p'` of `p_s` vanishes. -/
theorem cubic_ps_flux {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    x ^ 3 * cubicPs ε x + ε ^ 2 / 2 * deriv (cubicPs ε) x = 0 := by
  rw [(cubicPs_hasDerivAt ε x).deriv]
  field_simp
  ring

/-- (6.2.36): `p_s` solves the stationary Fokker–Planck equation
`∂ₓ(x³ p) + ½ ε² ∂ₓ² p = 0`. -/
theorem cubic_ps_fpe {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    deriv (fun y => y ^ 3 * cubicPs ε y + ε ^ 2 / 2 * deriv (cubicPs ε) y) x = 0 := by
  have : (fun y => y ^ 3 * cubicPs ε y + ε ^ 2 / 2 * deriv (cubicPs ε) y) = fun _ => 0 := by
    funext y; exact cubic_ps_flux hε y
  rw [this, deriv_const]

/-- `∫₀^∞ yⁿ exp(-y⁴/2ε²) dy = (1/4) (2ε²)^{(n+1)/4} Γ((n+1)/4)`. -/
lemma cubic_halfline_moment {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ n * cubicPs ε y =
      (2 * ε ^ 2) ^ (((n : ℝ) + 1) / 4) * (1 / 4) * Real.Gamma (((n : ℝ) + 1) / 4) := by
  have hb : (0 : ℝ) < 1 / (2 * ε ^ 2) := by positivity
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 4) (q := n) (b := 1 / (2 * ε ^ 2))
    (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hb
  have hcongr : ∫ y in Ioi (0 : ℝ), y ^ n * cubicPs ε y =
      ∫ y in Ioi (0 : ℝ), y ^ (n : ℝ) * Real.exp (-(1 / (2 * ε ^ 2)) * y ^ (4 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    simp only [cubicPs, Real.rpow_natCast]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    congr 2; ring
  rw [hcongr, h]
  congr 1
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  congr 1; ring_nf

/-- (6.2.38), even moments: `∫ x²ᵏ p_s / ∫ p_s = (2ε²)^{2k/4} Γ((2k+1)/4)/Γ(1/4)`. -/
theorem cubic_moment_even {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    (∫ x, x ^ (2 * k) * cubicPs ε x) / (∫ x, cubicPs ε x) =
      (2 * ε ^ 2) ^ ((2 * k : ℝ) / 4) * Real.Gamma ((2 * k + 1 : ℝ) / 4) /
        Real.Gamma (1 / 4) := by
  have heven : ∀ n : ℕ, Even n → ∫ x, x ^ n * cubicPs ε x =
      2 * ∫ y in Ioi (0 : ℝ), y ^ n * cubicPs ε y := by
    intro n hn
    rw [← integral_comp_abs (f := fun y => y ^ n * cubicPs ε y)]
    congr 1; funext x
    simp only [cubicPs, hn.pow_abs]
    congr 3
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
  have h0 := heven 0 (by decide)
  simp only [pow_zero, one_mul] at h0
  rw [heven (2 * k) (even_two_mul k), h0, cubic_halfline_moment hε,
    show (∫ y in Ioi (0 : ℝ), cubicPs ε y) = ∫ y in Ioi (0 : ℝ), y ^ 0 * cubicPs ε y by simp,
    cubic_halfline_moment hε]
  have hG : Real.Gamma (1 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hpos : (0 : ℝ) < 2 * ε ^ 2 := by positivity
  push_cast
  rw [show ((2 * (k : ℝ)) + 1) / 4 = (2 * k / 4) + (0 + 1) / 4 by ring, Real.rpow_add hpos]
  field_simp
  ring_nf

/-- (6.2.38), odd moments vanish. -/
theorem cubic_moment_odd (ε : ℝ) (k : ℕ) : ∫ x, x ^ (2 * k + 1) * cubicPs ε x = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => x ^ (2 * k + 1) * cubicPs ε x) volume
  have hodd : (fun x : ℝ => (-x) ^ (2 * k + 1) * cubicPs ε (-x)) =
      fun x => -(x ^ (2 * k + 1) * cubicPs ε x) := by
    funext x
    simp only [cubicPs, Odd.neg_pow (odd_two_mul_add_one k), neg_mul]
    congr 3
    rw [Even.neg_pow (by decide)]
  rw [hodd, MeasureTheory.integral_neg] at h
  linarith

/-- (6.2.38) for `n = 2`: the stationary variance of the cubic process is
`√2 Γ(3/4)/Γ(1/4) · ε` — of order `ε`, not `ε²`. -/
theorem cubic_variance {ε : ℝ} (hε : 0 < ε) :
    (∫ x, x ^ 2 * cubicPs ε x) / (∫ x, cubicPs ε x) =
      Real.sqrt 2 * Real.Gamma (3 / 4) / Real.Gamma (1 / 4) * ε := by
  have h := cubic_moment_even hε 1
  simp only [mul_one, Nat.cast_one] at h
  rw [h]
  have : (2 * ε ^ 2) ^ ((2 : ℝ) / 4) = Real.sqrt 2 * ε := by
    rw [show (2 : ℝ) / 4 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq hε.le]
  rw [this, show ((2 : ℝ) + 1) / 4 = 3 / 4 by norm_num]
  ring

/-- The leading small-noise behaviour (6.2.31), `var = O(ε²)`, fails for the cubic process: no
bound `var ≤ C ε²` holds for all small `ε`. -/
theorem cubic_variance_not_eps_sq :
    ¬ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫ x, x ^ 2 * cubicPs ε x) / (∫ x, cubicPs ε x) ≤ C * ε ^ 2 := by
  rintro ⟨C, hC⟩
  set K := Real.sqrt 2 * Real.Gamma (3 / 4) / Real.Gamma (1 / 4)
  have hK : 0 < K := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)
    positivity
  have hC0 : 0 < C := by
    have := hC 1 one_pos le_rfl
    rw [cubic_variance one_pos] at this
    nlinarith
  set ε := min 1 (K / (2 * C))
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have h := hC ε hε (min_le_left _ _)
  rw [cubic_variance hε] at h
  have h2 : ε ≤ K / (2 * C) := min_le_right _ _
  have : C * ε ≤ K / 2 := by
    calc C * ε ≤ C * (K / (2 * C)) := mul_le_mul_of_nonneg_left h2 hC0.le
      _ = K / 2 := by field_simp
  nlinarith

/-! ### Scaling (6.2.39)–(6.2.44) and the perturbation theory (6.2.45)–(6.2.47) -/

/-- (6.2.39)–(6.2.44), pathwise for additive noise.  Let `a(x) = -x³ c(x)` (6.2.43) and let `x`
solve `dx = a(x)dt + ε b dw` on `[0, T]` (`b` constant, `ε > 0`).  Then `y(τ) = x(τ/ε)/√ε`
(6.2.39), (6.2.42) solves, on `[0, εT]`,

  `y(τ) = y(0) + ∫₀^τ -y³ c(√ε y) + b (w̃(τ) - w̃(0))`,   `w̃(τ) = √ε w(τ/ε)`,

i.e. (6.2.44) `dy = -y³ c(y√ε) dτ + b dw̃`, and for `c ≡ 1` the parameterless cubic process
(6.2.41). -/
theorem cubic_scaling {c : ℝ → ℝ} {ε b T : ℝ} (hε : 0 < ε)
    {w x : ℝ → ℝ} (hx : IsPathSol (fun z => -z ^ 3 * c z) (ε * b) w x T) :
    IsPathSol (fun y => -y ^ 3 * c (Real.sqrt ε * y)) b (fun τ => Real.sqrt ε * w (τ / ε))
      (fun τ => x (τ / ε) / Real.sqrt ε) (ε * T) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hss : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
  refine ⟨(hx.cont.comp (continuous_id.div_const ε)).div_const _, fun τ hτ => ?_⟩
  have hτ' : τ / ε ∈ Icc 0 T := by
    constructor
    · exact div_nonneg hτ.1 hε.le
    · rw [div_le_iff₀ hε]; linarith [hτ.2]
  have h := hx.eq (τ / ε) hτ'
  -- change of variables in the drift integral
  have hcv : ∫ s in (0 : ℝ)..τ / ε, -x s ^ 3 * c (x s) =
      ε⁻¹ * ∫ u in (0 : ℝ)..τ, -x (u / ε) ^ 3 * c (x (u / ε)) := by
    have := intervalIntegral.integral_comp_div (fun s => -x s ^ 3 * c (x s)) hε.ne'
      (a := 0) (b := τ)
    rw [zero_div] at this
    rw [this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
  have hint : ∫ u in (0 : ℝ)..τ, -(x (u / ε) / Real.sqrt ε) ^ 3 *
      c (Real.sqrt ε * (x (u / ε) / Real.sqrt ε)) =
      (Real.sqrt ε)⁻¹ * ε⁻¹ * ∫ u in (0 : ℝ)..τ, -x (u / ε) ^ 3 * c (x (u / ε)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext u
    rw [mul_div_cancel₀ _ hs.ne', div_pow,
      show Real.sqrt ε ^ 3 = Real.sqrt ε * ε by rw [pow_succ, sq, hss, mul_comm]]
    field_simp
  simp only [zero_div] at h ⊢
  rw [hint, h, hcv]
  field_simp
  rw [show Real.sqrt ε ^ 2 = ε by rw [sq, hss]]
  ring

/-- The drift `F(δ) = -(y₀ + δy₁)³ c(δ(y₀ + δy₁))` of (6.2.44) along `y = y₀ + √ε y₁`
(`δ = √ε`, (6.2.45)) has `F(0) = -y₀³c(0)` and, for differentiable `c`,
`F'(0) = -(3y₀²c(0)y₁ + y₀⁴c'(0))` — the corrected drift of (6.2.46)–(6.2.47). -/
theorem cubic_first_order {c : ℝ → ℝ} {c' : ℝ} (hc : HasDerivAt c c' 0) (y₀ y₁ : ℝ) :
    HasDerivAt (fun δ : ℝ => -(y₀ + δ * y₁) ^ 3 * c (δ * (y₀ + δ * y₁)))
      (-(3 * y₀ ^ 2 * c 0 * y₁ + y₀ ^ 4 * c')) 0 := by
  have h1 : HasDerivAt (fun δ : ℝ => y₀ + δ * y₁) y₁ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y₁).const_add y₀
  have h2 : HasDerivAt (fun δ : ℝ => δ * (y₀ + δ * y₁)) y₀ 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul h1
    simpa using this
  have h3 : HasDerivAt (fun δ : ℝ => c (δ * (y₀ + δ * y₁))) (c' * y₀) 0 := by
    have hc' : HasDerivAt c c' ((fun δ : ℝ => δ * (y₀ + δ * y₁)) 0) := by simpa using hc
    exact hc'.comp 0 h2
  have h4 := ((h1.pow 3).neg).mul h3
  convert h4 using 1
  simp; ring

/-- (6.2.47) as printed, `dy₁ = -y₁[3y₀²c(0) + y₀³ c'(0)]dτ + …`, has the wrong drift: for
`c(0) = c'(0) = 1` (e.g. `c(x) = 1 + x`), `y₀ = 1`, `y₁ = 0` the true first-order drift is `-1`,
the printed one `0`. -/
theorem cubic_first_order_printed_wrong :
    ∃ y₀ y₁ c0 c' : ℝ, -(3 * y₀ ^ 2 * c0 * y₁ + y₀ ^ 4 * c') ≠
      -y₁ * (3 * y₀ ^ 2 * c0 + y₀ ^ 3 * c') :=
  ⟨1, 0, 1, 1, by norm_num⟩

end Gardiner.SDE
