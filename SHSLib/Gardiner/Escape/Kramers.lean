/-
# Escape over a potential barrier: the Kramers/Arrhenius limit with rate `O(√D)`

Gardiner, *Handbook of Stochastic Methods*, §5.2.7 c) (5.2.162)–(5.2.176) and §9.1.3 (9.1.9).
For the Smoluchowski process `∂ₜp = ∂ₓ[U'(x)p] + D∂ₓ²p` (5.2.162) on the whole line, the exact
mean first-passage time from `x` to `x₀`, with reflection at `-∞`, is (5.2.165)

`T(x → x₀) = D⁻¹ ∫ₓ^{x₀} dy e^{U(y)/D} ∫_{-∞}^y e^{-U(z)/D} dz`   (`Gardiner.Escape.mfptBarrier`).

The text evaluates it by freezing the inner integral at the barrier top `b` (5.2.166) and Gaussian
approximations (5.2.168)–(5.2.173), arriving at the Arrhenius formula (5.2.174)

`T(a → x₀) ≃ 2π [U''(a)|U''(b)|]^{-1/2} exp{[U(b) - U(a)]/D}`

when `x₀` is beyond the barrier, and at (9.1.9), half of it, when `x₀ = b`.  Here this is proved
as a genuine limit with an explicit rate:

* `Gardiner.Escape.mfpt_kramers` — **(5.2.174) with rate**:
  `|T(x → x₀) / [2π(k_a k_b)^{-1/2} e^{(U(b)-U(a))/D}] - 1| ≤ C √D` for all `0 < D ≤ 1`;
* `Gardiner.Escape.mfpt_kramers_half` — **(9.1.9) with rate**: the same for `x₀ = b` with
  `π(k_a k_b)^{-1/2}`;
* `Gardiner.Escape.mfpt_kramers_tendsto`, `Gardiner.Escape.mfpt_kramers_half_tendsto` — the
  ratios tend to `1` as `D → 0⁺`;
* `Gardiner.Escape.doubleWell_mfpt`, `Gardiner.Escape.doubleWell_mfpt_half` — the concrete quartic
  double well `U = x⁴/4 - x²/2` (`Gardiner.Adiabatic.dwU 0`): `T(-1 → ½) ~ √2 π e^{1/(4D)}` and
  `T(-1 → 0) ~ (π/√2) e^{1/(4D)}`, each with error `O(√D)`.

## Conditions on the potential (`Gardiner.Escape.KramersHyp`)

`k_a = U''(a) > 0` and `k_b = |U''(b)| > 0` enter through the quantitative Taylor bounds
`|U(a + s) - U(a) - k_a s²/2| ≤ M|s|³`, `|U(b) - U(b + s) - k_b s²/2| ≤ M|s|³` for `|s| ≤ r`
(which hold for `U ∈ C³` with `U'(a) = U'(b) = 0`); `a` is the strict global minimum of `U` on
`(-∞, x₀]` (`U ≥ U(a) + η` at distance `≥ r` from `a`), `b` is the strict maximum of `U` on the
range `[x, x₀]` of the outer integral, and `e^{-U}` is integrable on `(-∞, x₀]`.  The start point
`x` is arbitrary below `b - r` (the result does not depend on it, as the text remarks after
(5.2.167)).

The proof is the text's argument made quantitative: `F(y) = ∫_{-∞}^y e^{-(U - U(a))/D}` is
increasing and pinned between its values at `a + r` and `x₀`, both `√(2πD/k_a)(1 + O(√D))` by
Laplace's method (`Gardiner.Escape.laplace_min`); the outer integral is `√(2πD/k_b)(1 + O(√D))`.
-/
import SHSLib.Gardiner.Escape.Laplace
import SHSLib.Gardiner.Adiabatic.KramersGenerator

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-- The exact mean first-passage time (5.2.165) from `x` to `x₀` for the Smoluchowski equation
(5.2.162), with a reflecting boundary at `-∞`:
`T = D⁻¹ ∫ₓ^{x₀} dy e^{U(y)/D} ∫_{-∞}^y e^{-U(z)/D} dz`. -/
def mfptBarrier (U : ℝ → ℝ) (D x x₀ : ℝ) : ℝ :=
  D⁻¹ * ∫ y in x..x₀, exp (U y / D) * ∫ z in Iic y, exp (-U z / D)

/-- The Arrhenius/Kramers time (5.2.174): `2π (k_a k_b)^{-1/2} e^{ΔU/D}`. -/
def arrheniusTime (ka kb ΔU D : ℝ) : ℝ := 2 * π / √(ka * kb) * exp (ΔU / D)

/-- Hypotheses on the potential for the escape-time asymptotics: nondegenerate minimum `a`
(curvature `ka`), nondegenerate barrier top `b` (curvature `-kb`), quantitative Taylor bounds on
`|s| ≤ r`, `a` the strict global minimum on `(-∞, x₀]`, and integrability of `e^{-U}`. -/
structure KramersHyp (U : ℝ → ℝ) (a b x₀ : ℝ) where
  /-- radius of the Taylor windows -/
  r : ℝ
  /-- `U''(a)` -/
  ka : ℝ
  /-- `|U''(b)|` -/
  kb : ℝ
  /-- cubic Taylor constant -/
  M : ℝ
  /-- separation of the minimum and the barrier from the rest of the range -/
  η : ℝ
  cont : Continuous U
  hr : 0 < r
  hka : 0 < ka
  hkb : 0 < kb
  hM : 0 ≤ M
  hMra : M * r ≤ ka / 4
  hMrb : M * r ≤ kb / 4
  hη : 0 < η
  taylor_a : ∀ s, |s| ≤ r → |U (a + s) - U a - ka / 2 * s ^ 2| ≤ M * |s| ^ 3
  taylor_b : ∀ s, |s| ≤ r → |U b - U (b + s) - kb / 2 * s ^ 2| ≤ M * |s| ^ 3
  sep : a + r ≤ b - r
  well : ∀ z ≤ x₀, r ≤ |z - a| → U a + η ≤ U z
  integrable : IntegrableOn (fun z => exp (-U z)) (Iic x₀)

/-! ### The final algebra: a sandwich gives a relative rate -/

/-- If `F_lo In ≤ I ≤ F_hi I_b` with `F_hi, F_lo = αt + O(t²)`, `I_b ≤ γt + O(t²)` and
`In = γt + O(t²)`, then `I/(αγt²) = 1 + O(t)`. -/
lemma sandwich_rate {I α γ t C₁ C₂ C₃ Fhi Flo Ib In : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hα : 0 < α) (hγ : 0 < γ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hup : I ≤ Fhi * Ib) (hlo : Flo * In ≤ I) (hIb0 : 0 ≤ Ib) (hIn0 : 0 ≤ In)
    (hFhi : Fhi ≤ α * t + C₁ * t ^ 2) (hFlo : α * t - C₁ * t ^ 2 ≤ Flo)
    (hIb : Ib ≤ γ * t + C₂ * t ^ 2) (hIn : |In - γ * t| ≤ C₃ * t ^ 2) :
    |I / (α * γ * t ^ 2) - 1|
      ≤ (α * C₂ + α * C₃ + 2 * γ * C₁ + C₁ * C₂ + C₁ * C₃) / (α * γ) * t := by
  have hIn' := abs_le.mp hIn
  have h1 : Fhi * Ib ≤ (α * t + C₁ * t ^ 2) * (γ * t + C₂ * t ^ 2) := by
    apply mul_le_mul hFhi hIb hIb0; positivity
  have h2 : (α * t - C₁ * t ^ 2) * In ≤ Flo * In := mul_le_mul_of_nonneg_right hFlo hIn0
  have ht2 : t ^ 4 ≤ t ^ 3 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
  have hup' : I - α * γ * t ^ 2 ≤ (α * C₂ + γ * C₁ + C₁ * C₂) * t ^ 3 := by
    have : (α * t + C₁ * t ^ 2) * (γ * t + C₂ * t ^ 2)
        = α * γ * t ^ 2 + (α * C₂ + γ * C₁) * t ^ 3 + C₁ * C₂ * t ^ 4 := by ring
    nlinarith [mul_le_mul_of_nonneg_left ht2 (mul_nonneg hC₁ hC₂)]
  have hlo' : -((α * C₃ + γ * C₁ + C₁ * C₃) * t ^ 3) ≤ I - α * γ * t ^ 2 := by
    have e : (α * t - C₁ * t ^ 2) * In = α * t * In - C₁ * t ^ 2 * In := by ring
    have h3 : α * t * (γ * t - C₃ * t ^ 2) ≤ α * t * In :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : C₁ * t ^ 2 * In ≤ C₁ * t ^ 2 * (γ * t + C₃ * t ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left ht2 (mul_nonneg hC₁ hC₃)]
  have hpos : 0 < α * γ * t ^ 2 := by positivity
  rw [div_sub_one hpos.ne', abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_le]
  have e : (α * C₂ + α * C₃ + 2 * γ * C₁ + C₁ * C₂ + C₁ * C₃) / (α * γ) * t * (α * γ * t ^ 2)
      = (α * C₂ + α * C₃ + 2 * γ * C₁ + C₁ * C₂ + C₁ * C₃) * t ^ 3 := by
    field_simp
  rw [e]
  have h5 : 0 ≤ (α * C₂ + γ * C₁) * t ^ 3 := by positivity
  have h6 : 0 ≤ (α * C₃ + γ * C₁) * t ^ 3 := by positivity
  have h7 : 0 ≤ C₁ * C₂ * t ^ 3 := by positivity
  have h8 : 0 ≤ C₁ * C₃ * t ^ 3 := by positivity
  constructor <;> nlinarith

/-! ### Rewriting the mean first-passage time -/

lemma integral_exp_shift (U : ℝ → ℝ) (Ua D y : ℝ) :
    ∫ z in Iic y, exp (-U z / D) = exp (-Ua / D) * ∫ z in Iic y, exp (-((U z - Ua) / D)) := by
  rw [← integral_const_mul]
  congr 1; ext z
  rw [← exp_add]; congr 1; ring

lemma mfptBarrier_eq (U : ℝ → ℝ) (a b D x x₀ : ℝ) :
    mfptBarrier U D x x₀ = D⁻¹ * exp ((U b - U a) / D) *
      ∫ y in x..x₀, exp (-((U b - U y) / D)) * ∫ z in Iic y, exp (-((U z - U a) / D)) := by
  unfold mfptBarrier
  rw [mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  simp only
  rw [integral_exp_shift U (U a) D y, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← exp_add, ← exp_add]; congr 1; ring

/-! ### The common core of (5.2.174) and (9.1.9) -/

section core

variable {U : ℝ → ℝ} {a b x₀ : ℝ}

/-- Laplace estimates for the well integral `F(y) = ∫_{-∞}^y e^{-(U - U(a))/D}`. -/
lemma well_laplace (h : KramersHyp U a b x₀) {y : ℝ} (hy₁ : a + h.r ≤ y) (hy₂ : y ≤ x₀) :
    ∃ C, 0 ≤ C ∧ ∀ D, 0 < D → D ≤ 1 →
      IntegrableOn (fun z => exp (-((U z - U a) / D))) (Iic y) ∧
        |(∫ z in Iic y, exp (-((U z - U a) / D))) - √(2 * π * D / h.ka)| ≤ C * D := by
  have hint : IntegrableOn (fun z => exp (-(U z - U a))) (Iic y) := by
    have := (h.integrable.mono_set (Iic_subset_Iic.mpr hy₂)).const_mul (exp (U a))
    refine IntegrableOn.congr_fun this (fun z _ => ?_) measurableSet_Iic
    rw [← exp_add]; congr 1; ring
  obtain ⟨C, hC⟩ := laplace_min (W := fun z => U z - U a) (S := Iic y) (m := a) (by
      have := h.cont; fun_prop) measurableSet_Iic h.hr h.hka h.hM h.hMra
    (fun s hs => h.taylor_a s hs) (fun z hz => hz.2.trans hy₁) h.hη
    (fun z hz hz' => by have := h.well z (le_trans (mem_Iic.mp hz) hy₂) hz'; linarith) hint
  refine ⟨max C 0, le_max_right _ _, fun D hD hD1 => ?_⟩
  obtain ⟨h1, h2⟩ := hC D hD hD1
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le)⟩


lemma sqrt_two_pi_D (k D : ℝ) (hD : 0 ≤ D) : √(2 * π * D / k) = √(2 * π / k) * √D := by
  rw [← sqrt_mul' _ hD]
  congr 1; ring

/-- Convert a set integral over `Icc` into an interval integral. -/
lemma setIntegral_Icc_eq (f : ℝ → ℝ) {x y : ℝ} (hxy : x ≤ y) :
    ∫ z in Icc x y, f z = ∫ z in x..y, f z := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hxy]

/-- **Common core of (5.2.174) and (9.1.9).**  If the outer integral `∫ₓ^{x₀} e^{-(U(b)-U)/D}`
and its near-barrier part `∫_{b-r}^{q} e^{-(U(b)-U)/D}` are both `γ√D + O(D)`, then
`T(x → x₀) = √(2π/k_a) γ e^{(U(b)-U(a))/D} (1 + O(√D))`. -/
lemma mfpt_core (h : KramersHyp U a b x₀) {x q γ : ℝ} (hx : x ≤ b - h.r) (hq : b ≤ q)
    (hqx : q ≤ x₀) (hγ : 0 < γ)
    (hIb : ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |(∫ y in x..x₀, exp (-((U b - U y) / D))) - γ * √D| ≤ C * D)
    (hIn : ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |(∫ y in b - h.r..q, exp (-((U b - U y) / D))) - γ * √D| ≤ C * D) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |mfptBarrier U D x x₀ / (√(2 * π / h.ka) * γ * exp ((U b - U a) / D)) - 1| ≤ C * √D := by
  have hr := h.hr
  have hsep := h.sep
  have har : a + h.r ≤ x₀ := by linarith
  obtain ⟨C₁a, hC₁a0, hC₁a⟩ := well_laplace h le_rfl har
  obtain ⟨C₁b, hC₁b0, hC₁b⟩ := well_laplace h har le_rfl
  obtain ⟨C₂, hC₂⟩ := hIb
  obtain ⟨C₃, hC₃⟩ := hIn
  set α := √(2 * π / h.ka) with hαdef
  have hα : 0 < α := sqrt_pos.mpr (by have := h.hka; positivity)
  set C₁ := max C₁a C₁b
  set C₂' := max C₂ 0
  set C₃' := max C₃ 0
  refine ⟨(α * C₂' + α * C₃' + 2 * γ * C₁ + C₁ * C₂' + C₁ * C₃') / (α * γ),
    fun D hD hD1 => ?_⟩
  set t := √D with htdef
  have ht : 0 < t := sqrt_pos.mpr hD
  have ht1 : t ≤ 1 := by rw [htdef]; exact sqrt_le_one.mpr hD1
  have hDt : D = t ^ 2 := by rw [htdef, sq_sqrt hD.le]
  have hcont := h.cont
  -- the well integral
  set F : ℝ → ℝ := fun y => ∫ z in Iic y, exp (-((U z - U a) / D)) with hFdef
  obtain ⟨hintx₀, hFx₀⟩ := hC₁b D hD hD1
  obtain ⟨-, hFa⟩ := hC₁a D hD hD1
  have hF0 : ∀ y, 0 ≤ F y := fun y =>
    setIntegral_nonneg measurableSet_Iic (fun _ _ => (exp_pos _).le)
  have hFmono : ∀ y₁ y₂, y₁ ≤ y₂ → y₂ ≤ x₀ → F y₁ ≤ F y₂ := by
    intro y₁ y₂ h12 h2
    exact setIntegral_mono_set (hintx₀.mono_set (Iic_subset_Iic.mpr h2))
      ((ae_restrict_iff' measurableSet_Iic).mpr
        (Eventually.of_forall (fun _ _ => (exp_pos _).le)))
      (ae_of_all _ (fun z (hz : z ∈ Iic y₁) => (le_trans (mem_Iic.mp hz) h12 : z ∈ Iic y₂)))
  set E : ℝ → ℝ := fun y => exp (-((U b - U y) / D)) with hEdef
  have hEc : Continuous E := by rw [hEdef]; fun_prop
  have hxx₀ : x ≤ x₀ := by linarith
  have hEF : ∀ u v, x ≤ u → v ≤ x₀ → u ≤ v →
      IntervalIntegrable (fun y => E y * F y) volume u v := by
    intro u v hu hv huv
    have hm : MonotoneOn F (uIcc u v) := by
      intro y₁ hy₁ y₂ hy₂ h12
      apply hFmono y₁ y₂ h12
      rw [uIcc_of_le huv] at hy₂; exact hy₂.2.trans hv
    exact (hm.intervalIntegrable).continuousOn_mul hEc.continuousOn
  set I := ∫ y in x..x₀, E y * F y with hIdef
  -- upper bound
  have hup : I ≤ F x₀ * ∫ y in x..x₀, E y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hxx₀ (hEF x x₀ le_rfl le_rfl hxx₀)
      ((hEc.intervalIntegrable _ _).const_mul _)
    intro y hy
    rw [mul_comm (F x₀)]
    exact mul_le_mul_of_nonneg_left (hFmono y x₀ hy.2 le_rfl) (exp_pos _).le
  -- lower bound
  have hlo : F (a + h.r) * ∫ y in b - h.r..q, E y ≤ I := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hEF x (b - h.r) le_rfl (by linarith) hx) (hEF (b - h.r) q (by linarith) hqx (by linarith))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hEF x q le_rfl hqx (by linarith)) (hEF q x₀ (by linarith) le_rfl hqx)
    have h3 : 0 ≤ ∫ y in x..b - h.r, E y * F y :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun y _ => mul_nonneg (exp_pos _).le (hF0 y))
    have h4 : 0 ≤ ∫ y in q..x₀, E y * F y :=
      intervalIntegral.integral_nonneg hqx (fun y _ => mul_nonneg (exp_pos _).le (hF0 y))
    have h5 : F (a + h.r) * ∫ y in b - h.r..q, E y ≤ ∫ y in b - h.r..q, E y * F y := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hEc.intervalIntegrable _ _).const_mul _) (hEF (b - h.r) q (by linarith) hqx (by linarith))
      intro y hy
      rw [mul_comm (F _)]
      exact mul_le_mul_of_nonneg_left (hFmono _ y (by linarith [hy.1]) (by linarith [hy.2]))
        (exp_pos _).le
    rw [hIdef]; linarith
  -- the estimates in the variable `t = √D`
  have hsa : √(2 * π * D / h.ka) = α * t := sqrt_two_pi_D _ _ hD.le
  have hFhi : F x₀ ≤ α * t + C₁ * t ^ 2 := by
    have := (abs_le.mp hFx₀).2
    rw [hsa, ← hDt] at *
    have : C₁b * D ≤ C₁ * D := mul_le_mul_of_nonneg_right (le_max_right _ _) hD.le
    linarith
  have hFlo : α * t - C₁ * t ^ 2 ≤ F (a + h.r) := by
    have := (abs_le.mp hFa).1
    rw [hsa, ← hDt] at *
    have : C₁a * D ≤ C₁ * D := mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le
    linarith
  have hIb' : (∫ y in x..x₀, E y) ≤ γ * t + C₂' * t ^ 2 := by
    have := (abs_le.mp (hC₂ D hD hD1)).2
    rw [← hDt]
    have : C₂ * D ≤ C₂' * D := mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le
    linarith
  have hIn' : |(∫ y in b - h.r..q, E y) - γ * t| ≤ C₃' * t ^ 2 := by
    rw [← hDt]
    exact (hC₃ D hD hD1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le)
  have hIb0 : 0 ≤ ∫ y in x..x₀, E y :=
    intervalIntegral.integral_nonneg hxx₀ (fun _ _ => (exp_pos _).le)
  have hIn0 : 0 ≤ ∫ y in b - h.r..q, E y :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => (exp_pos _).le)
  have key := sandwich_rate ht ht1 hα hγ (le_trans hC₁a0 (le_max_left _ _))
    (le_max_right _ _) (le_max_right _ _) hup hlo hIb0 hIn0 hFhi hFlo hIb' hIn'
  have hmf : mfptBarrier U D x x₀ / (α * γ * exp ((U b - U a) / D)) = I / (α * γ * t ^ 2) := by
    rw [mfptBarrier_eq U a b D x x₀, ← hDt]
    have he : exp ((U b - U a) / D) ≠ 0 := (exp_pos _).ne'
    have := hD.ne'; have := hα.ne'; have := hγ.ne'
    field_simp
    rfl
  rw [hmf]
  exact key

end core

lemma sqrt_two_pi_mul' {ka : ℝ} (kb : ℝ) (hka : 0 < ka) :
    √(2 * π / ka) * √(2 * π / kb) = 2 * π / √(ka * kb) := by
  rw [← sqrt_mul (by positivity), show 2 * π / ka * (2 * π / kb) = (2 * π) ^ 2 / (ka * kb) by
    ring, sqrt_div (by positivity), sqrt_sq (by positivity)]

/-- **The Arrhenius formula (5.2.174) as a limit with rate `O(√D)`.**  Under `KramersHyp` (the
minimum `a`, curvature `k_a`, is the strict global minimum of `U` on `(-∞, x₀]`), for a start
point `x ≤ b - r` and an end point `x₀ ≥ b + r` beyond the barrier top `b` (curvature `-k_b`),
with `b` the strict maximum of `U` on `[x, x₀]`, the exact mean first-passage time (5.2.165)
satisfies `|T(x → x₀) / [2π(k_a k_b)^{-1/2} e^{(U(b)-U(a))/D}] - 1| ≤ C√D` for `0 < D ≤ 1`. -/
theorem mfpt_kramers {U : ℝ → ℝ} {a b x₀ : ℝ} (h : KramersHyp U a b x₀) {x : ℝ}
    (hx : x ≤ b - h.r) (hx₀ : b + h.r ≤ x₀)
    (hbar : ∀ y ∈ Icc x x₀, h.r ≤ |y - b| → U y + h.η ≤ U b) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |mfptBarrier U D x x₀ / arrheniusTime h.ka h.kb (U b - U a) D - 1| ≤ C * √D := by
  have hr := h.hr
  have hcont := h.cont
  set γ := √(2 * π / h.kb)
  have hγ : 0 < γ := sqrt_pos.mpr (by have := h.hkb; positivity)
  have hWc : Continuous fun y => U b - U y := by fun_prop
  have hIb : ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |(∫ y in x..x₀, exp (-((U b - U y) / D))) - γ * √D| ≤ C * D := by
    obtain ⟨C, hC⟩ := laplace_min (W := fun y => U b - U y) (S := Icc x x₀) (m := b) hWc
      measurableSet_Icc hr h.hkb h.hM h.hMrb h.taylor_b
      (Icc_subset_Icc hx hx₀) h.hη (fun z hz hz' => by have := hbar z hz hz'; linarith)
      (Continuous.integrableOn_Icc (by fun_prop))
    refine ⟨C, fun D hD hD1 => ?_⟩
    have := (hC D hD hD1).2
    rwa [setIntegral_Icc_eq _ (by linarith), sqrt_two_pi_D _ _ hD.le] at this
  have hIn : ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |(∫ y in b - h.r..b + h.r, exp (-((U b - U y) / D))) - γ * √D| ≤ C * D := by
    obtain ⟨C, hC⟩ := laplace_min (W := fun y => U b - U y) (S := Icc (b - h.r) (b + h.r))
      (m := b) hWc measurableSet_Icc hr h.hkb h.hM h.hMrb h.taylor_b le_rfl h.hη
      (fun z hz hz' => by
        have := hbar z ⟨by linarith [hz.1], by linarith [hz.2]⟩ hz'; linarith)
      (Continuous.integrableOn_Icc (by fun_prop))
    refine ⟨C, fun D hD hD1 => ?_⟩
    have := (hC D hD hD1).2
    rwa [setIntegral_Icc_eq _ (by linarith), sqrt_two_pi_D _ _ hD.le] at this
  obtain ⟨C, hC⟩ := mfpt_core h hx (by linarith) hx₀ hγ hIb hIn
  refine ⟨C, fun D hD hD1 => ?_⟩
  have e : arrheniusTime h.ka h.kb (U b - U a) D
      = √(2 * π / h.ka) * γ * exp ((U b - U a) / D) := by
    rw [arrheniusTime, sqrt_two_pi_mul' h.kb h.hka]
  rw [e]; exact hC D hD hD1

/-- **(9.1.9) as a limit with rate `O(√D)`**: the mean first-passage time to the barrier top
itself is half the Arrhenius time, `|T(x → b) / [π(k_a k_b)^{-1/2} e^{(U(b)-U(a))/D}] - 1| ≤ C√D`. -/
theorem mfpt_kramers_half {U : ℝ → ℝ} {a b : ℝ} (h : KramersHyp U a b b) {x : ℝ}
    (hx : x ≤ b - h.r) (hbar : ∀ y ∈ Icc x b, h.r ≤ |y - b| → U y + h.η ≤ U b) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |mfptBarrier U D x b / (arrheniusTime h.ka h.kb (U b - U a) D / 2) - 1| ≤ C * √D := by
  have hr := h.hr
  have hcont := h.cont
  set γ := √(2 * π / h.kb) / 2
  have hγ : 0 < γ := by have := h.hkb; positivity
  have hWc : Continuous fun y => U b - U y := by fun_prop
  have hIb : ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |(∫ y in x..b, exp (-((U b - U y) / D))) - γ * √D| ≤ C * D := by
    obtain ⟨C, hC⟩ := laplace_min_half (W := fun y => U b - U y) (S := Icc x b) (m := b) hWc
      measurableSet_Icc hr h.hkb h.hM h.hMrb h.taylor_b
      (Icc_subset_Icc hx le_rfl) (fun z hz hz' => absurd hz.2 (not_le.mpr hz')) h.hη
      (fun z hz hz' => by have := hbar z hz hz'; linarith)
      (Continuous.integrableOn_Icc (by fun_prop))
    refine ⟨C, fun D hD hD1 => ?_⟩
    have := (hC D hD hD1).2
    rw [setIntegral_Icc_eq _ (by linarith), sqrt_two_pi_D _ _ hD.le] at this
    convert this using 3; ring
  have hIn : ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |(∫ y in b - h.r..b, exp (-((U b - U y) / D))) - γ * √D| ≤ C * D := by
    obtain ⟨C, hC⟩ := laplace_min_half (W := fun y => U b - U y) (S := Icc (b - h.r) b)
      (m := b) hWc measurableSet_Icc hr h.hkb h.hM h.hMrb h.taylor_b le_rfl
      (fun z hz hz' => absurd hz.2 (not_le.mpr hz')) h.hη
      (fun z hz hz' => by have := hbar z ⟨by linarith [hz.1], hz.2⟩ hz'; linarith)
      (Continuous.integrableOn_Icc (by fun_prop))
    refine ⟨C, fun D hD hD1 => ?_⟩
    have := (hC D hD hD1).2
    rw [setIntegral_Icc_eq _ (by linarith), sqrt_two_pi_D _ _ hD.le] at this
    convert this using 3; ring
  obtain ⟨C, hC⟩ := mfpt_core h hx le_rfl le_rfl hγ hIb hIn
  refine ⟨C, fun D hD hD1 => ?_⟩
  have e : arrheniusTime h.ka h.kb (U b - U a) D / 2
      = √(2 * π / h.ka) * γ * exp ((U b - U a) / D) := by
    rw [arrheniusTime, ← sqrt_two_pi_mul' h.kb h.hka]; ring
  rw [e]; exact hC D hD hD1

/-- The Arrhenius ratio tends to `1` as `D → 0⁺` ((5.2.174) as a true limit). -/
theorem mfpt_kramers_tendsto {U : ℝ → ℝ} {a b x₀ : ℝ} (h : KramersHyp U a b x₀) {x : ℝ}
    (hx : x ≤ b - h.r) (hx₀ : b + h.r ≤ x₀)
    (hbar : ∀ y ∈ Icc x x₀, h.r ≤ |y - b| → U y + h.η ≤ U b) :
    Tendsto (fun D => mfptBarrier U D x x₀ / arrheniusTime h.ka h.kb (U b - U a) D)
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨C, hC⟩ := mfpt_kramers h hx hx₀ hbar
  exact tendsto_of_sqrt_rate one_pos hC

/-- (9.1.9) as a true limit. -/
theorem mfpt_kramers_half_tendsto {U : ℝ → ℝ} {a b : ℝ} (h : KramersHyp U a b b) {x : ℝ}
    (hx : x ≤ b - h.r) (hbar : ∀ y ∈ Icc x b, h.r ≤ |y - b| → U y + h.η ≤ U b) :
    Tendsto (fun D => mfptBarrier U D x b / (arrheniusTime h.ka h.kb (U b - U a) D / 2))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨C, hC⟩ := mfpt_kramers_half h hx hbar
  exact tendsto_of_sqrt_rate one_pos hC

/-! ### Instance: the quartic double well `U = x⁴/4 - x²/2` -/

section doubleWell

open Gardiner.Adiabatic

lemma dwU_zero : dwU 0 = fun y => y ^ 4 / 4 - y ^ 2 / 2 := rfl

lemma dwU_zero_apply (y : ℝ) : dwU 0 y = y ^ 4 / 4 - y ^ 2 / 2 := rfl

/-- `exp(-U)` is integrable for the quartic double well: `-U(z) ≤ 1 - z²/2`. -/
lemma dwU_integrable (s : Set ℝ) : IntegrableOn (fun z => exp (-dwU 0 z)) s := by
  have hg : Integrable (fun z : ℝ => exp 1 * exp (-(1 / 2) * z ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  refine (hg.mono' (Continuous.aestronglyMeasurable
    (by rw [dwU_zero]; fun_prop : Continuous fun z => exp (-dwU 0 z)))
    (Eventually.of_forall (fun z => ?_))).integrableOn
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add, dwU_zero_apply]
  apply exp_le_exp.mpr
  nlinarith [sq_nonneg (z ^ 2 / 2 - 1)]

/-- The hypotheses `KramersHyp` for the quartic double well, with minimum `a = -1`
(`U''(-1) = 2`), barrier top `b = 0` (`U''(0) = -1`), and any end point `x₀ ≤ 1/2`. -/
def dwKramers (x₀ : ℝ) (hx₀ : x₀ ≤ 1 / 2) : KramersHyp (dwU 0) (-1) 0 x₀ where
  r := 1 / 8
  ka := 2
  kb := 1
  M := 2
  η := 1 / 300
  cont := by rw [dwU_zero]; fun_prop
  hr := by norm_num
  hka := by norm_num
  hkb := by norm_num
  hM := by norm_num
  hMra := by norm_num
  hMrb := by norm_num
  hη := by norm_num
  taylor_a := by
    intro s hs
    have e : dwU 0 (-1 + s) - dwU 0 (-1) - 2 / 2 * s ^ 2 = s ^ 3 * (s / 4 - 1) := by
      simp only [dwU_zero_apply]; ring
    rw [e, abs_mul, abs_pow]
    have h1 : |s / 4 - 1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
    nlinarith [pow_nonneg (abs_nonneg s) 3]
  taylor_b := by
    intro s hs
    have e : dwU 0 0 - dwU 0 (0 + s) - 1 / 2 * s ^ 2 = -(|s| ^ 3 * (|s| / 4)) := by
      simp only [dwU_zero_apply]
      have : s ^ 4 = |s| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      ring_nf; rw [this]
    rw [e, abs_neg, abs_mul, abs_pow, abs_abs, abs_div, abs_abs]
    have h1 : |s| / |4| ≤ 2 := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith [abs_nonneg s]
    nlinarith [pow_nonneg (abs_nonneg s) 3]
  sep := by norm_num
  well := by
    intro z hz hza
    rw [dwU_zero_apply, dwU_zero_apply]
    rcases le_or_gt 0 (z - -1) with h | h
    · rw [abs_of_nonneg h] at hza
      have h1 : z ^ 2 ≤ 49 / 64 := by nlinarith
      nlinarith [sq_nonneg z]
    · rw [abs_of_neg h] at hza
      have h1 : 81 / 64 ≤ z ^ 2 := by nlinarith
      nlinarith
  integrable := dwU_integrable _

lemma dw_barrier {x₀ : ℝ} (hx₀ : x₀ ≤ 1 / 2) :
    ∀ y ∈ Icc (-1) x₀, (dwKramers x₀ hx₀).r ≤ |y - 0| →
      dwU 0 y + (dwKramers x₀ hx₀).η ≤ dwU 0 0 := by
  intro y hy hy'
  simp only [dwKramers, sub_zero] at hy' ⊢
  rw [dwU_zero_apply, dwU_zero_apply]
  have h1 : 1 / 64 ≤ y ^ 2 := by
    have := sq_abs y; nlinarith [abs_nonneg y]
  have h2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  nlinarith

/-- **Instance of (5.2.174): quartic double well.**  For `U = x⁴/4 - x²/2` the exact mean
first-passage time from the minimum `-1` to `1/2` (beyond the barrier at `0`) satisfies
`|T(-1 → ½) / (√2 π e^{1/(4D)}) - 1| ≤ C √D` for `0 < D ≤ 1`. -/
theorem doubleWell_mfpt : ∃ C, ∀ D, 0 < D → D ≤ 1 →
    |mfptBarrier (dwU 0) D (-1) (1 / 2) / (√2 * π * exp (1 / (4 * D))) - 1| ≤ C * √D := by
  obtain ⟨C, hC⟩ := mfpt_kramers (dwKramers (1 / 2) le_rfl) (x := -1)
    (by simp [dwKramers]; norm_num) (by simp [dwKramers]; norm_num) (dw_barrier le_rfl)
  refine ⟨C, fun D hD hD1 => ?_⟩
  have e : arrheniusTime (dwKramers (1 / 2) le_rfl).ka (dwKramers (1 / 2) le_rfl).kb
      (dwU 0 0 - dwU 0 (-1)) D = √2 * π * exp (1 / (4 * D)) := by
    simp only [arrheniusTime, dwKramers, dwU_zero_apply]
    have h2 : (2 : ℝ) / √2 = √2 := by
      rw [div_eq_iff (by positivity), mul_self_sqrt (by norm_num)]
    norm_num
    rw [show 2 * π / √2 = 2 / √2 * π by ring, h2]
    congr 2; field_simp
  rw [← e]; exact hC D hD hD1

/-- **Instance of (9.1.9): quartic double well.**  The mean first-passage time from `-1` to the
barrier top `0` satisfies `|T(-1 → 0) / ((π/√2) e^{1/(4D)}) - 1| ≤ C √D`. -/
theorem doubleWell_mfpt_half : ∃ C, ∀ D, 0 < D → D ≤ 1 →
    |mfptBarrier (dwU 0) D (-1) 0 / (π / √2 * exp (1 / (4 * D))) - 1| ≤ C * √D := by
  obtain ⟨C, hC⟩ := mfpt_kramers_half (dwKramers 0 (by norm_num)) (x := -1)
    (by simp [dwKramers]; norm_num) (dw_barrier (by norm_num))
  refine ⟨C, fun D hD hD1 => ?_⟩
  have e : arrheniusTime (dwKramers 0 (by norm_num)).ka (dwKramers 0 (by norm_num)).kb
      (dwU 0 0 - dwU 0 (-1)) D / 2 = π / √2 * exp (1 / (4 * D)) := by
    simp only [arrheniusTime, dwKramers, dwU_zero_apply]
    norm_num
    rw [show 2 * π / √2 * exp (1 / 4 / D) / 2 = π / √2 * exp (1 / 4 / D) by ring]
    congr 2; field_simp
  rw [← e]; exact hC D hD hD1

end doubleWell

end Gardiner.Escape
