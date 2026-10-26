/-
# Bistability in several dimensions, II: Brownian motion in a double potential, §9.3.4

For the Kramers equation (9.3.65) we verify the structure (9.3.66)–(9.3.69), (9.3.75) exactly, and
we show that for the **quadratic saddle** `U = U₀ - U₂x²/2` (9.3.80)/(9.3.86) every step of the
text's construction is exact:

* `bm_partials`, `bm_drift`, `bm_current` — **(9.3.66)–(9.3.69)**;
* `bm_plane_deriv` — **(9.3.72)**; `bm_plane_max_quadratic` — the maximiser on the plane
  `λx + p = w` is `x = λw/(λ² - U₂)` (unique, `λ² > U₂`);
* `bm_root` — **(9.3.81)–(9.3.82)**; `bm_x_exact` — **(9.3.79) is exact**: `x(w) = w/γ`;
* `bm_assumption_III` — **(9.3.73)–(9.3.76), (9.3.83)–(9.3.84)**: `𝒟ᵀn = d(w) ∂_w u(w)` holds for
  all `w` with `d = γ(1 + λ²)^{-1/2}` (so `dλ/dw = 0` exactly);
* `bm_pw_eq` — **(9.3.85) evaluated exactly**; `bm_pw_printed_wrong` — **(9.3.87) erratum**;
* `bm_kappa0` — **(9.3.88)** (correct as printed); `bm_tau0` — **(9.3.89)–(9.3.90)**;
* `lam_ratio_bound` — **(9.3.95)** with an explicit error: `|λ/γ - (1 + s)| ≤ s²`, `s = U₂/γ²`;
* `corrT_spec`, `tau3_spec` — **(9.3.96)–(9.3.97), corrected**: the exact MFPT of the corrected
  Smoluchowski equation has the factor `[1 + γ⁻²U'']⁻¹`; `tau3_quadratic` — **(9.3.99) exact**
  for the quadratic saddle; `tau3_printed_wrong`;
* `ratio_comparison` — **(9.3.100)** holds only to first order in `s`: `τ₀/τ₂ < τ₃/τ₁` for
  `0 < s < 1`, with `|τ₃/τ₁ - τ₀/τ₂| ≤ 3s²` for `s ≤ 1/2`;
* `temp_rescale` — **(9.3.106)–(9.3.108), corrected**: `V(x, T) = U(xT^{1/2})/T`;
* `brownian_doubleWell_tau1` — **(9.3.93) for (9.3.109)**: the exact one-dimensional time at
  temperature `T` against Kramers' formula, ratio `→ 1` with error `O(√T)`;
* `separatrix_line` — **(9.3.112)–(9.3.113)**, including invariance of the line `p = -λx`;
* `brownianSaddle_instance` — `γ = 4`, `U₂ = 5`, `λ = 5`; `corrSmol_instance` — the quadratic saddle
  `U = -5x²/2`, `γ = 4`.

**Errata recorded.**
(9.3.87) the Gaussian integral contributes `λ(2π/(λ² - U₂))^{1/2}`, missing from the printed
`p(w)`; (9.3.88) is nevertheless correct (it follows from the corrected `p(w)`).
(9.3.89), (9.3.94) by (9.2.19) the escape time is `n_a κ/d`; the factor `n_a` (`= ½` for the
symmetric well) is missing from both `τ₀` and `τ₂`; it cancels in `τ₀/τ₂`.
(9.3.97) for (9.3.96) (`A = 𝒟' - 𝒟U'`, `B = 2𝒟`, `𝒟 = γ⁻¹[1 + γ⁻²U'']`) the integrand carries
`[1 + γ⁻²U'']⁻¹`, not `[1 + γ⁻²U'']`; only the inverse gives (9.3.99).
(9.3.100) is not an identity: `τ₃/τ₁ = (1 - s)⁻¹` and `τ₀/τ₂ = λ/γ = ½ + (¼ + s)^{1/2}` agree to
`O(s)` but differ at `O(s²)`.  (9.3.108) `V(x, T) = U(xT^{1/2})/T` (the factor `T⁻¹` is missing).
(9.3.81) is printed with `+U''(0) = -U₂`, consistent with (9.3.113).
-/
import SHSLib.Gardiner.Escape.FirstPassage

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-! ### (9.3.66)–(9.3.69): structure of the Kramers equation -/

/-- The stationary density (9.3.66): `P_s(x, p) = 𝒩₂ exp(-p²/2 - U(x))`. -/
def bmPs (U : ℝ → ℝ) (N₂ x p : ℝ) : ℝ := N₂ * exp (-p ^ 2 / 2 - U x)

/-- The partial derivatives of `P_s`: `∂ₓP_s = -U' P_s`, `∂_p P_s = -p P_s`. -/
theorem bm_partials {U : ℝ → ℝ} {U'x : ℝ} (N₂ x p : ℝ) (hU : HasDerivAt U U'x x) :
    HasDerivAt (fun x => bmPs U N₂ x p) (-U'x * bmPs U N₂ x p) x ∧
    HasDerivAt (fun p => bmPs U N₂ x p) (-p * bmPs U N₂ x p) p := by
  constructor
  · have := ((hU.const_sub (-p ^ 2 / 2)).exp).const_mul N₂
    convert this using 1; simp [bmPs]; ring
  · have h1 : HasDerivAt (fun p : ℝ => -p ^ 2 / 2 - U x) (-p) p := by
      convert ((hasDerivAt_pow 2 p).neg.div_const 2).sub_const (U x) using 1; ring
    convert (h1.exp).const_mul N₂ using 1; simp [bmPs]; ring

/-- **(9.3.67)**: `v = (p, -U' - γp) = [[0, -1], [1, γ]]·∇ log P_s`, `∇ log P_s = (-U', -p)`. -/
theorem bm_drift (γ U'x p : ℝ) :
    0 * (-U'x) + (-1) * (-p) = p ∧ 1 * (-U'x) + γ * (-p) = -U'x - γ * p := by
  constructor <;> ring

/-- **(9.3.68)–(9.3.69)**: the stationary current `J_s = -vP_s + 𝐃·∇P_s` (with
`𝐃 = diag(0, γ)`) equals `-∇·(𝐀P_s)`, `𝐀 = [[0, -1], [1, 0]]`, i.e.
`(-(-∂_pP_s), -(∂ₓP_s))`. -/
theorem bm_current {U : ℝ → ℝ} {U'x : ℝ} (γ N₂ x p : ℝ) (hU : HasDerivAt U U'x x) :
    ∃ Px Pp, HasDerivAt (fun x => bmPs U N₂ x p) Px x ∧ HasDerivAt (fun p => bmPs U N₂ x p) Pp p ∧
      -p * bmPs U N₂ x p + (0 * Px + 0 * Pp) = -(0 * Px + (-1) * Pp) ∧
      -(-U'x - γ * p) * bmPs U N₂ x p + (0 * Px + γ * Pp) = -(1 * Px + 0 * Pp) := by
  obtain ⟨h1, h2⟩ := bm_partials N₂ x p hU
  exact ⟨_, _, h1, h2, by ring, by ring⟩

/-! ### (9.3.70)–(9.3.84): the planes `λx + p = w` -/

/-- **(9.3.72)**: on the plane `λx + p = w`, `log P_s = -(w - λx)²/2 - U(x)` (up to a constant)
has derivative `-(U'(x) + λ²x - λw)`. -/
theorem bm_plane_deriv {U : ℝ → ℝ} {U'x : ℝ} (lam w x : ℝ) (hU : HasDerivAt U U'x x) :
    HasDerivAt (fun x => -(w - lam * x) ^ 2 / 2 - U x) (-(U'x + lam ^ 2 * x - lam * w)) x := by
  have h1 : HasDerivAt (fun x => w - lam * x) (-lam) x := by
    simpa using ((hasDerivAt_id x).const_mul lam).const_sub w
  convert ((h1.pow 2).neg.div_const 2).sub hU using 1
  push_cast; ring

/-- **(9.3.72) for the quadratic saddle** `U = U₀ - U₂x²/2`: if `λ² > U₂`, the maximum of `P_s` on
the plane `λx + p = w` is attained exactly at `x* = λw/(λ² - U₂)`:
`F(x) = F(x*) - (λ² - U₂)(x - x*)²/2`. -/
theorem bm_plane_max_quadratic {U₀ U₂ lam : ℝ} (hl : U₂ < lam ^ 2) (w x : ℝ) :
    let F := fun x : ℝ => -(w - lam * x) ^ 2 / 2 - (U₀ - U₂ * x ^ 2 / 2)
    F x = F (lam * w / (lam ^ 2 - U₂)) - (lam ^ 2 - U₂) * (x - lam * w / (lam ^ 2 - U₂)) ^ 2 / 2 := by
  intro F
  have h : lam ^ 2 - U₂ ≠ 0 := by linarith
  simp only [F]
  field_simp
  ring

/-- **(9.3.81)–(9.3.82)**: `λ = γ/2 + √(γ²/4 + U₂)` solves `λ² - γλ - U₂ = 0`; for `γ, U₂ > 0` it
satisfies `λ ≥ γ > 0` and `λ² - U₂ = γλ > 0`. -/
theorem bm_root {γ U₂ : ℝ} (hγ : 0 < γ) (hU : 0 < U₂) :
    let lam := γ / 2 + √(γ ^ 2 / 4 + U₂)
    lam ^ 2 - γ * lam - U₂ = 0 ∧ γ ≤ lam ∧ 0 < lam ∧ lam ^ 2 - U₂ = γ * lam := by
  intro lam
  have hs : √(γ ^ 2 / 4 + U₂) ^ 2 = γ ^ 2 / 4 + U₂ := sq_sqrt (by positivity)
  have hge : γ / 2 ≤ √(γ ^ 2 / 4 + U₂) := by
    rw [show γ / 2 = √((γ / 2) ^ 2) from (sqrt_sq (by positivity)).symm]
    exact sqrt_le_sqrt (by nlinarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [lam]; nlinarith
  · simp only [lam]; linarith
  · simp only [lam]; positivity
  · simp only [lam]; nlinarith

/-- **(9.3.79) is exact**: with `λ² - γλ - U₂ = 0` the maximiser `λw/(λ² - U₂)` is `w/γ`. -/
theorem bm_x_exact {γ U₂ lam : ℝ} (hγ : 0 < γ) (hl : 0 < lam) (hroot : lam ^ 2 - γ * lam - U₂ = 0)
    (w : ℝ) : lam * w / (lam ^ 2 - U₂) = w / γ := by
  have e : lam ^ 2 - U₂ = γ * lam := by linarith
  rw [e]; field_simp

/-- **(9.3.73)–(9.3.76), (9.3.83)–(9.3.84)**: along `u(w) = (w/γ, w - λw/γ)` (constant `λ`),
`𝒟ᵀ = [[0, 1], [-1, γ]]` applied to the unit normal `(λ, 1)/(1 + λ²)^{1/2}` equals
`d · ∂_w u` with `d = γ(1 + λ²)^{-1/2}` — for every `w`, so Assumption III holds exactly. -/
theorem bm_assumption_III {γ lam : ℝ} (hγ : 0 < γ) (w : ℝ) :
    HasDerivAt (fun w => (w / γ, w - lam * (w / γ))) (1 / γ, 1 - lam / γ) w ∧
    (0 * lam + 1 * 1, -1 * lam + γ * 1) = ((1 : ℝ), γ - lam) ∧
    (√(1 + lam ^ 2))⁻¹ * 1 = γ * (√(1 + lam ^ 2))⁻¹ * (1 / γ) ∧
    (√(1 + lam ^ 2))⁻¹ * (γ - lam) = γ * (√(1 + lam ^ 2))⁻¹ * (1 - lam / γ) := by
  refine ⟨?_, Prod.ext (by ring) (by ring), by field_simp, by field_simp⟩
  have h1 : HasDerivAt (fun w : ℝ => w / γ) (1 / γ) w := by
    simpa using (hasDerivAt_id w).div_const γ
  have h2 : HasDerivAt (fun w : ℝ => w - lam * (w / γ)) (1 - lam / γ) w := by
    convert (hasDerivAt_id w).sub (h1.const_mul lam) using 1; simp; ring
  exact h1.prodMk h2

/-! ### (9.3.85)–(9.3.90): `p(w)`, `κ(0)` and `τ₀` -/

/-- `p(w)` (9.3.85), for the quadratic saddle (9.3.86): `𝒩₂ (1 + λ²)^{1/2} λ⁻¹ ∫ dq
exp[-q²/2 - U((w - q)/λ)]` with `U(x) = U₀ - U₂x²/2`. -/
def bmPw (U₀ U₂ lam N₂ w : ℝ) : ℝ :=
  N₂ * (√(1 + lam ^ 2) / lam) * ∫ q, exp (-q ^ 2 / 2 - (U₀ - U₂ * ((w - q) / lam) ^ 2 / 2))

/-- (9.3.87) **as printed**. -/
def bmPwPrinted (U₀ U₂ lam N₂ w : ℝ) : ℝ :=
  √(1 + lam ^ 2) / lam * N₂ * exp (-U₀) * exp (U₂ * w ^ 2 / (2 * (lam ^ 2 - U₂)))

lemma gauss_shift (a c q₀ : ℝ) (ha : 0 < a) :
    ∫ q, exp (c - a / 2 * (q - q₀) ^ 2) = exp c * √(2 * π / a) := by
  have e : (fun q => exp (c - a / 2 * (q - q₀) ^ 2))
      = fun q => exp c * (fun q => exp (-(a / 2) * q ^ 2)) (q - q₀) := by
    ext q; simp only; rw [← exp_add]; ring_nf
  rw [e, integral_const_mul, integral_sub_right_eq_self (fun q => exp (-(a / 2) * q ^ 2)) q₀,
    integral_gaussian]
  congr 2; field_simp

/-- **(9.3.85)–(9.3.87), exact for the quadratic saddle**: for `λ > 0`, `λ² > U₂`,
`p(w) = 𝒩₂ (1 + λ²)^{1/2}λ⁻¹ e^{-U₀} · λ(2π/(λ² - U₂))^{1/2} · exp[U₂w²/(2(λ² - U₂))]`. -/
theorem bm_pw_eq {U₀ U₂ lam : ℝ} (hl : 0 < lam) (hlu : U₂ < lam ^ 2) (N₂ w : ℝ) :
    bmPw U₀ U₂ lam N₂ w = N₂ * (√(1 + lam ^ 2) / lam) *
      (exp (-U₀) * (lam * √(2 * π / (lam ^ 2 - U₂))) *
        exp (U₂ * w ^ 2 / (2 * (lam ^ 2 - U₂)))) := by
  have hd : 0 < lam ^ 2 - U₂ := by linarith
  have e : (fun q => exp (-q ^ 2 / 2 - (U₀ - U₂ * ((w - q) / lam) ^ 2 / 2)))
      = fun q => exp ((-U₀ + U₂ * w ^ 2 / (2 * (lam ^ 2 - U₂))) -
          (lam ^ 2 - U₂) / lam ^ 2 / 2 * (q - (-U₂ * w / (lam ^ 2 - U₂))) ^ 2) := by
    ext q; congr 1; field_simp; ring
  unfold bmPw
  have e2 : √(2 * π / ((lam ^ 2 - U₂) / lam ^ 2)) = lam * √(2 * π / (lam ^ 2 - U₂)) := by
    rw [show 2 * π / ((lam ^ 2 - U₂) / lam ^ 2) = lam ^ 2 * (2 * π / (lam ^ 2 - U₂)) by
      field_simp, sqrt_mul (sq_nonneg _), sqrt_sq hl.le]
  rw [e, gauss_shift _ _ _ (by positivity), exp_add, e2]; ring

/-- **(9.3.87) erratum**: with `λ² - γλ - U₂ = 0` (`γ, U₂ > 0`) the true `p(w)` is
`(2πλ/γ)^{1/2}` times the printed one, and `(2πλ/γ)^{1/2} > 1`. -/
theorem bm_pw_printed_wrong {γ U₂ : ℝ} (hγ : 0 < γ) (hU : 0 < U₂) (U₀ N₂ w : ℝ) :
    let lam := γ / 2 + √(γ ^ 2 / 4 + U₂)
    bmPw U₀ U₂ lam N₂ w = √(2 * π * lam / γ) * bmPwPrinted U₀ U₂ lam N₂ w ∧
      1 < √(2 * π * lam / γ) := by
  intro lam
  obtain ⟨-, hge, hl, he⟩ := bm_root hγ hU
  have hge' : γ ≤ lam := hge
  have hl' : 0 < lam := hl
  have he' : lam ^ 2 - U₂ = γ * lam := he
  clear_value lam
  have hlu : U₂ < lam ^ 2 := by nlinarith
  have hfac : lam * √(2 * π / (lam ^ 2 - U₂)) = √(2 * π * lam / γ) := by
    rw [he', show 2 * π * lam / γ = lam ^ 2 * (2 * π / (γ * lam)) by field_simp,
      sqrt_mul (sq_nonneg _), sqrt_sq hl'.le]
  refine ⟨?_, ?_⟩
  · rw [bm_pw_eq hl' hlu, hfac, bmPwPrinted]; ring
  · rw [show (1 : ℝ) = √1 from sqrt_one.symm]
    apply sqrt_lt_sqrt (by norm_num)
    rw [lt_div_iff₀ hγ]; nlinarith [pi_gt_three]

/-- `κ(0) = ∫_{-∞}^0 p(w)⁻¹ dw` (9.3.88). -/
def bmKappa0 (U₀ U₂ lam N₂ : ℝ) : ℝ := ∫ w in Iic 0, (bmPw U₀ U₂ lam N₂ w)⁻¹

lemma gauss_Iic (b : ℝ) : ∫ w in Iic (0 : ℝ), exp (-b * w ^ 2) = √(π / b) / 2 := by
  rw [← integral_gaussian_Ioi b, ← neg_zero, ← integral_comp_neg_Ioi]
  simp

/-- **(9.3.88)**, correct as printed (given the corrected (9.3.87)): with `λ² - γλ - U₂ = 0`,
`λ, γ, U₂, 𝒩₂ > 0`, `κ(0) = ½ 𝒩₂⁻¹ λγ(1 + λ²)^{-1/2} e^{U₀} U₂^{-1/2}`. -/
theorem bm_kappa0 {γ U₂ lam N₂ : ℝ} (hγ : 0 < γ) (hU : 0 < U₂) (hl : 0 < lam) (hN : 0 < N₂)
    (hroot : lam ^ 2 - γ * lam - U₂ = 0) (U₀ : ℝ) :
    bmKappa0 U₀ U₂ lam N₂ = 1 / 2 * N₂⁻¹ * (lam * γ / √(1 + lam ^ 2)) * (exp U₀ / √U₂) := by
  have he : lam ^ 2 - U₂ = γ * lam := by linarith
  have hlu : U₂ < lam ^ 2 := by nlinarith
  have hd : 0 < lam ^ 2 - U₂ := by linarith
  have hsq : 0 < √(2 * π / (lam ^ 2 - U₂)) := sqrt_pos.mpr (div_pos (by positivity) hd)
  set K := N₂ * (√(1 + lam ^ 2) / lam) * (exp (-U₀) * (lam * √(2 * π / (lam ^ 2 - U₂))))
  have hK : 0 < K := by simp only [K]; positivity
  have e : (fun w => (bmPw U₀ U₂ lam N₂ w)⁻¹)
      = fun w => K⁻¹ * exp (-(U₂ / (2 * (lam ^ 2 - U₂))) * w ^ 2) := by
    ext w; rw [bm_pw_eq hl hlu, ← mul_assoc, mul_inv, ← exp_neg]; congr 2; ring
  unfold bmKappa0
  rw [e, integral_const_mul, gauss_Iic]
  simp only [K, he]
  have h1 : √(π / (U₂ / (2 * (γ * lam)))) = √(2 * π / (γ * lam)) * (γ * lam / √U₂) := by
    rw [show γ * lam / √U₂ = √((γ * lam) ^ 2 / U₂) by
      rw [sqrt_div (sq_nonneg _), sqrt_sq (by positivity)], ← sqrt_mul (by positivity)]
    congr 1; field_simp
  rw [h1]
  have := exp_pos U₀
  have h2 : 0 < √(2 * π / (γ * lam)) := by positivity
  have h3 : 0 < √(1 + lam ^ 2) := by positivity
  have h4 : 0 < √U₂ := by positivity
  rw [exp_neg]
  field_simp

/-- **(9.3.89)–(9.3.90)** (as printed, i.e. without the factor `n_a` — see the errata):
`τ₀ = κ(0)/d(0) = (λ/2) e^{U₀} 𝒩₁⁻¹ (2π/U₂)^{1/2}` with `𝒩₂ = (2π)^{-1/2}𝒩₁`. -/
theorem bm_tau0 {γ U₂ lam N₁ : ℝ} (hγ : 0 < γ) (hU : 0 < U₂) (hl : 0 < lam) (hN : 0 < N₁)
    (hroot : lam ^ 2 - γ * lam - U₂ = 0) (U₀ : ℝ) :
    bmKappa0 U₀ U₂ lam (N₁ / √(2 * π)) / (γ / √(1 + lam ^ 2))
      = lam / 2 * exp U₀ * N₁⁻¹ * √(2 * π / U₂) := by
  rw [bm_kappa0 hγ hU hl (by positivity) hroot, sqrt_div (by positivity)]
  have h3 : 0 < √(1 + lam ^ 2) := by positivity
  have h4 : 0 < √U₂ := by positivity
  have h5 : 0 < √(2 * π) := by positivity
  field_simp

/-! ### (9.3.94)–(9.3.100): comparisons -/

/-- **(9.3.95)** with an explicit error: for `s = U₂/γ² ≥ 0`,
`λ/γ = ½ + √(¼ + s)` satisfies `|λ/γ - (1 + s)| ≤ s²`. -/
theorem lam_ratio_bound {s : ℝ} (hs : 0 ≤ s) :
    |1 / 2 + √(1 / 4 + s) - (1 + s)| ≤ s ^ 2 ∧ 1 / 2 + √(1 / 4 + s) ≤ 1 + s := by
  have hq : √(1 / 4 + s) ^ 2 = 1 / 4 + s := sq_sqrt (by positivity)
  have hq0 : 0 ≤ √(1 / 4 + s) := sqrt_nonneg _
  have up : √(1 / 4 + s) ≤ 1 / 2 + s := by nlinarith
  have lo : 1 / 2 + s - s ^ 2 ≤ √(1 / 4 + s) := by
    by_cases h : 1 / 2 + s - s ^ 2 ≤ 0
    · linarith
    · push_neg at h
      have hs2 : s ≤ 2 := by nlinarith
      have hy : (1 / 2 + s - s ^ 2) ^ 2 ≤ 1 / 4 + s := by
        nlinarith [mul_nonneg (pow_nonneg hs 3) (by linarith : (0:ℝ) ≤ 2 - s)]
      exact Real.le_sqrt_of_sq_le hy
  refine ⟨abs_le.mpr ⟨by linarith, by nlinarith⟩, by linarith⟩

/-- The ratio `τ₀/τ₂ = λ/γ` of (9.3.90) to (9.3.94) is `½ + √(¼ + U₂/γ²)`. -/
theorem tau0_div_tau2 {γ U₂ : ℝ} (hγ : 0 < γ) (hU : 0 ≤ U₂) (c : ℝ) (hc : c ≠ 0) :
    (γ / 2 + √(γ ^ 2 / 4 + U₂)) / 2 * c / (1 / 2 * γ * c) = 1 / 2 + √(1 / 4 + U₂ / γ ^ 2) := by
  have : √(γ ^ 2 / 4 + U₂) = γ * √(1 / 4 + U₂ / γ ^ 2) := by
    rw [show γ ^ 2 / 4 + U₂ = γ ^ 2 * (1 / 4 + U₂ / γ ^ 2) by field_simp, sqrt_mul (sq_nonneg _),
      sqrt_sq hγ.le]
  rw [this]; field_simp

/-- **(9.3.100) holds only to first order.**  With `τ₃/τ₁ = (1 - s)⁻¹` (9.3.99) and
`τ₀/τ₂ = ½ + √(¼ + s)`: for `0 < s < 1`, `τ₀/τ₂ < τ₃/τ₁` strictly, and for `0 ≤ s ≤ ½` the two
agree up to `3s²`. -/
theorem ratio_comparison {s : ℝ} (hs : 0 ≤ s) :
    (0 < s → s < 1 → 1 / 2 + √(1 / 4 + s) < (1 - s)⁻¹) ∧
    (s ≤ 1 / 2 → |(1 - s)⁻¹ - (1 / 2 + √(1 / 4 + s))| ≤ 3 * s ^ 2) := by
  obtain ⟨h1, h2⟩ := lam_ratio_bound hs
  constructor
  · intro hs0 hs1
    have : 1 + s < (1 - s)⁻¹ := by
      rw [lt_inv_comm₀ (by linarith) (by linarith)]
      rw [inv_eq_one_div, lt_div_iff₀ (by linarith)]; nlinarith
    linarith
  · intro hs2
    have e : (1 - s)⁻¹ - (1 + s) = s ^ 2 / (1 - s) := by
      field_simp [show (1 - s) ≠ 0 by linarith]; ring
    have h3 : s ^ 2 / (1 - s) ≤ 2 * s ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h4 : 0 ≤ s ^ 2 / (1 - s) := div_nonneg (sq_nonneg _) (by linarith)
    have := abs_le.mp h1
    rw [abs_le]; constructor <;> linarith

/-! ### (9.3.96)–(9.3.99): the corrected Smoluchowski equation -/

/-- Mean first-passage time to `b`, reflecting at `a`, for `∂_t P = ∂ₓ{𝒟(x)[U'P + ∂ₓP]}`:
`T(x) = ∫_x^b dy e^{U(y)}/𝒟(y) ∫_a^y e^{-U(z)} dz`. -/
def corrT (U Dc : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∫ y in x..b, exp (U y) / Dc y * ∫ z in a..y, exp (-U z)

section corrSmol

variable {U U' Dc Dc' : ℝ → ℝ} (hU : ∀ x, HasDerivAt U (U' x) x)
  (hDc : ∀ x, HasDerivAt Dc (Dc' x) x) (hDpos : ∀ x, 0 < Dc x)
include hU hDc hDpos

/-- **(9.3.97), corrected — the general statement.**  The equation
`∂_t P = ∂ₓ{𝒟[U'P + ∂ₓP]}` has drift `A = 𝒟' - 𝒟U'` and diffusion `B = 2𝒟`; `corrT` solves
`A T' + ½BT'' = -1`, `T'(a) = 0`, `T(b) = 0`. -/
theorem corrT_bwd (a b : ℝ) :
    IsBwdSol (fun x => Dc' x - Dc x * U' x) (fun x => 2 * Dc x) (fun _ => -1) (corrT U Dc a b) ∧
    HasDerivAt (corrT U Dc a b) 0 a ∧ corrT U Dc a b b = 0 := by
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun x => (hU x).continuousAt
  have hDcc : Continuous Dc := continuous_iff_continuousAt.mpr fun x => (hDc x).continuousAt
  set I := fun y => ∫ z in a..y, exp (-U z)
  have hI : ∀ y, HasDerivAt I (exp (-U y)) y := fun y =>
    ((by fun_prop : Continuous fun z => exp (-U z)).integral_hasStrictDerivAt a y).hasDerivAt
  have hIc : Continuous I := continuous_iff_continuousAt.mpr fun x => (hI x).continuousAt
  set g := fun y => exp (U y) * I y / Dc y
  have hgc : Continuous g :=
    ((by fun_prop : Continuous fun y => exp (U y)).mul hIc).div hDcc fun x => (hDpos x).ne'
  have heq : corrT U Dc a b = fun x => -∫ y in b..x, g y := by
    ext x; rw [corrT, intervalIntegral.integral_symm]
    congr 1
    apply intervalIntegral.integral_congr; intro y _; simp only [g, I]; ring
  have hT : ∀ x, HasDerivAt (corrT U Dc a b) (-g x) x := by
    intro x; rw [heq]; exact (hgc.integral_hasStrictDerivAt b x).hasDerivAt.neg
  set g' := fun x => ((exp (U x) * U' x * I x + exp (U x) * exp (-U x)) * Dc x
      - exp (U x) * I x * Dc' x) / Dc x ^ 2
  have hg : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    have := (((hU x).exp).mul (hI x)).div (hDc x) (hDpos x).ne'
    convert this using 1
  refine ⟨⟨fun x => -g x, fun x => -g' x, fun x => ⟨hT x, (hg x).neg, ?_⟩⟩, ?_, ?_⟩
  · have e1 : exp (U x) * exp (-U x) = 1 := by rw [← exp_add]; simp
    have hD := (hDpos x).ne'
    simp only [g, g']
    rw [e1]; field_simp; ring
  · convert hT a using 1; simp [g, I]
  · simp [corrT]

/-- `corrT` is the (unique) mean first-passage time (5.2.160) of the corrected equation. -/
theorem corrT_spec (hU' : Continuous U') (hDc' : Continuous Dc') (a b : ℝ) :
    corrT U Dc a b = mfptReflA (fun x => Dc' x - Dc x * U' x) (fun x => 2 * Dc x) a b := by
  have hDcc : Continuous Dc := continuous_iff_continuousAt.mpr fun x => (hDc x).continuousAt
  obtain ⟨hsol, hder, hb⟩ := corrT_bwd hU hDc hDpos a b
  exact (mfptReflA_spec (by fun_prop) (by fun_prop) (fun x => by linarith [hDpos x]) a b).2.2.2
    _ hsol hder.deriv hb

end corrSmol

/-- The one-dimensional time (9.3.93) with a reflecting barrier at `a`:
`τ₁ = γ∫_x^b e^{U} ∫_a^y e^{-U}`. -/
def tau1 (U : ℝ → ℝ) (γ a b x : ℝ) : ℝ := γ * ∫ y in x..b, exp (U y) * ∫ z in a..y, exp (-U z)

/-- (9.3.97), **corrected**: `τ₃ = γ∫_x^b [1 + γ⁻²U''(y)]⁻¹ e^{U} ∫_a^y e^{-U}`. -/
def tau3 (U U'' : ℝ → ℝ) (γ a b x : ℝ) : ℝ :=
  γ * ∫ y in x..b, (1 + U'' y / γ ^ 2)⁻¹ * (exp (U y) * ∫ z in a..y, exp (-U z))

/-- (9.3.97) **as printed**. -/
def tau3Printed (U U'' : ℝ → ℝ) (γ a b x : ℝ) : ℝ :=
  γ * ∫ y in x..b, (1 + U'' y / γ ^ 2) * (exp (U y) * ∫ z in a..y, exp (-U z))

/-- **(9.3.96)–(9.3.97), corrected.**  For `𝒟 = γ⁻¹[1 + γ⁻²U'']` (positive), the corrected
`τ₃` is the exact mean first-passage time of (9.3.96) with reflecting barrier at `a`. -/
theorem tau3_spec {U U' U'' U''' : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ) (hU : ∀ x, HasDerivAt U (U' x) x)
    (hU2 : ∀ x, HasDerivAt U' (U'' x) x) (hU3 : ∀ x, HasDerivAt U'' (U''' x) x)
    (hU3c : Continuous U''') (hpos : ∀ x, 0 < 1 + U'' x / γ ^ 2) (a b x : ℝ) :
    tau3 U U'' γ a b x = mfptReflA (fun x => U''' x / γ ^ 3 - (1 + U'' x / γ ^ 2) / γ * U' x)
      (fun x => 2 * ((1 + U'' x / γ ^ 2) / γ)) a b x := by
  have hDc : ∀ x, HasDerivAt (fun x => (1 + U'' x / γ ^ 2) / γ) (U''' x / γ ^ 3) x := by
    intro x
    convert (((hU3 x).div_const (γ ^ 2)).const_add 1).div_const γ using 1; field_simp
  have hU'c : Continuous U' := continuous_iff_continuousAt.mpr fun x => (hU2 x).continuousAt
  rw [← corrT_spec hU hDc (fun x => by have := hpos x; positivity) hU'c (by fun_prop)]
  rw [tau3, corrT, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro y _
  have := hpos y
  simp only; field_simp

/-- **(9.3.99) is exact for the quadratic saddle** (`U'' ≡ -U₂`): `τ₃ = (1 - U₂/γ²)⁻¹ τ₁`,
whereas the printed (9.3.97) would give `(1 - U₂/γ²) τ₁`. -/
theorem tau3_quadratic (U : ℝ → ℝ) (γ U₂ a b x : ℝ) :
    tau3 U (fun _ => -U₂) γ a b x = (1 - U₂ / γ ^ 2)⁻¹ * tau1 U γ a b x ∧
    tau3Printed U (fun _ => -U₂) γ a b x = (1 - U₂ / γ ^ 2) * tau1 U γ a b x := by
  constructor
  · rw [tau3, tau1, intervalIntegral.integral_const_mul]; ring_nf
  · rw [tau3Printed, tau1, intervalIntegral.integral_const_mul]; ring_nf

lemma tau1_pos (U : ℝ → ℝ) (hU : Continuous U) {γ a b x : ℝ} (hγ : 0 < γ) (hax : a < x)
    (hxb : x < b) : 0 < tau1 U γ a b x := by
  unfold tau1
  apply mul_pos hγ
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hxb
  · exact ((by fun_prop : Continuous fun y => exp (U y)).mul
      (intervalIntegral.continuous_primitive (fun _ _ =>
        (by fun_prop : Continuous fun z => exp (-U z)).intervalIntegrable _ _) a)).intervalIntegrable _ _
  · intro y hy
    apply mul_pos (exp_pos _)
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((by fun_prop : Continuous fun z => exp (-U z)).intervalIntegrable _ _)
      (fun z _ => exp_pos _) (by linarith [hy.1])

/-- **(9.3.97) as printed is wrong**: for the quadratic saddle with `0 < U₂ < γ²` and
`a < x < b`, the printed formula differs from the exact mean first-passage time. -/
theorem tau3_printed_wrong (U : ℝ → ℝ) (hU : Continuous U) {γ U₂ a b x : ℝ} (hγ : 0 < γ)
    (hU2 : 0 < U₂) (hU2γ : U₂ < γ ^ 2) (hax : a < x) (hxb : x < b) :
    tau3Printed U (fun _ => -U₂) γ a b x ≠ tau3 U (fun _ => -U₂) γ a b x := by
  obtain ⟨h1, h2⟩ := tau3_quadratic U γ U₂ a b x
  rw [h1, h2]
  have ht := tau1_pos U hU hγ hax hxb
  have hs0 : 0 < U₂ / γ ^ 2 := by positivity
  have hs1 : U₂ / γ ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact hU2γ
  intro h
  have := mul_right_cancel₀ ht.ne' h
  have hlt : 1 - U₂ / γ ^ 2 < (1 - U₂ / γ ^ 2)⁻¹ := by
    rw [lt_inv_comm₀ (by linarith) (by linarith)]
    calc (1 - U₂ / γ ^ 2)⁻¹ > 1 := one_lt_inv₀ (by linarith) |>.mpr (by linarith)
      _ > 1 - U₂ / γ ^ 2 := by linarith
  linarith

/-! ### (9.3.104)–(9.3.109): temperature scaling and the quartic double well -/

/-- **(9.3.106)–(9.3.108), corrected.**  With `x = T^{1/2}x̃`, `p = T^{1/2}p̃`, the drift of
(9.3.105) becomes `-[γp̃ + V'(x̃)]` with `V(x̃) = U(x̃T^{1/2})/T` (not `U(x̃T^{1/2})`). -/
theorem temp_rescale {U U' : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hU : ∀ x, HasDerivAt U (U' x) x)
    (γ x p : ℝ) :
    HasDerivAt (fun x => U (x * √T) / T) (U' (x * √T) / √T) x ∧
    -(γ * (p * √T) + U' (x * √T)) / √T = -(γ * p + U' (x * √T) / √T) := by
  have hs : 0 < √T := sqrt_pos.mpr hT
  constructor
  · have := ((hU (x * √T)).comp x ((hasDerivAt_id x).mul_const √T)).div_const T
    convert this using 1
    simp only [one_mul]
    rw [div_eq_div_iff hs.ne' hT.ne', mul_assoc, mul_self_sqrt hT.le]
  · field_simp

/-- The exact mean first-passage time (5.2.165) is unchanged by adding a constant to `U`. -/
lemma mfptBarrier_add_const (U : ℝ → ℝ) (c D x x₀ : ℝ) :
    mfptBarrier (fun y => U y + c) D x x₀ = mfptBarrier U D x x₀ := by
  unfold mfptBarrier
  congr 1
  apply intervalIntegral.integral_congr; intro y _
  simp only
  have e : (fun z => exp (-(U z + c) / D)) = fun z => exp (-c / D) * exp (-U z / D) := by
    ext z; rw [← exp_add]; ring_nf
  rw [e, integral_const_mul, show (U y + c) / D = U y / D + c / D by ring, exp_add,
    show -c / D = -(c / D) by ring, exp_neg]
  have := exp_pos (c / D)
  field_simp

/-- **(9.3.93) for the potential (9.3.109)** `U = ¼(x² - 1)²` at temperature `T` (time unit
`γ`): the exact one-dimensional time `τ₁(T) = γ·T(-1 → 0)` compared with Kramers' formula
`γ (π/√2) e^{1/(4T)}` [(9.3.94) with `n_a` restored, at temperature `T`]: ratio `→ 1` with error
`O(√T)`. -/
theorem brownian_doubleWell_tau1 {γ : ℝ} (hγ : 0 < γ) : ∃ C, ∀ T, 0 < T → T ≤ 1 →
    |γ * mfptBarrier (fun x => (x ^ 2 - 1) ^ 2 / 4) T (-1) 0 /
      (γ * (π / √2 * exp (1 / (4 * T)))) - 1| ≤ C * √T := by
  obtain ⟨C, hC⟩ := doubleWell_mfpt_half
  refine ⟨C, fun T hT hT1 => ?_⟩
  have e : (fun x : ℝ => (x ^ 2 - 1) ^ 2 / 4) = fun x => Gardiner.Adiabatic.dwU 0 x + 1 / 4 := by
    ext x; rw [dwU_zero_apply]; ring
  rw [e, mfptBarrier_add_const, mul_div_mul_left _ _ hγ.ne']
  exact hC T hT hT1

/-! ### (9.3.110)–(9.3.113): the separatrix -/

/-- **(9.3.112)–(9.3.113)**: on the line `p = -λx` (`x ≠ 0`), the linearised drift
`(p, -γp + U₂x)` is parallel to `(x, p)` iff `λ² - λγ - U₂ = 0`; moreover
`d/dt(p + λx) = -(λ² - λγ - U₂)x` there, so the line is invariant exactly for these `λ`. -/
theorem separatrix_line (γ U₂ lam : ℝ) {x : ℝ} (hx : x ≠ 0) :
    ((-lam * x) * (-lam * x) = x * (-γ * (-lam * x) + U₂ * x) ↔ lam ^ 2 - lam * γ - U₂ = 0) ∧
    (-γ * (-lam * x) + U₂ * x) + lam * (-lam * x) = -(lam ^ 2 - lam * γ - U₂) * x := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by ring⟩
  · have : x ^ 2 * (lam ^ 2 - lam * γ - U₂) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h') hx
    · exact h'
  · linear_combination x ^ 2 * h

/-! ### A concrete instance -/

/-- **Instance**: `γ = 4`, `U₂ = 5` give `λ = 5` (9.3.82); then `x(w) = w/4` exactly (9.3.79),
`d(0) = 4/√26` (9.3.84), `s = 5/16`, `τ₀/τ₂ = 5/4` within `s²` of `1 + s` (9.3.95), while
`τ₃/τ₁ = 16/11 ≠ 5/4` (9.3.100), and the true `p(w)` is `√(5π/2)` times the printed (9.3.87). -/
theorem brownianSaddle_instance :
    (4 : ℝ) / 2 + √((4 : ℝ) ^ 2 / 4 + 5) = 5 ∧
    (∀ w : ℝ, 5 * w / ((5 : ℝ) ^ 2 - 5) = w / 4) ∧
    |(5 : ℝ) / 4 - (1 + 5 / 16)| ≤ (5 / 16) ^ 2 ∧
    (1 - (5 : ℝ) / 16)⁻¹ = 16 / 11 ∧ (5 : ℝ) / 4 < 16 / 11 ∧
    (∀ U₀ N₂ w : ℝ, bmPw U₀ 5 5 N₂ w = √(2 * π * 5 / 4) * bmPwPrinted U₀ 5 5 N₂ w) ∧
    bmKappa0 0 5 5 1 = 1 / 2 * 1⁻¹ * (5 * 4 / √(1 + 5 ^ 2)) * (exp 0 / √5) := by
  have hs : √((4 : ℝ) ^ 2 / 4 + 5) = 3 := by
    rw [show (4 : ℝ) ^ 2 / 4 + 5 = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have hl : (4 : ℝ) / 2 + √((4 : ℝ) ^ 2 / 4 + 5) = 5 := by rw [hs]; norm_num
  refine ⟨hl, fun w => bm_x_exact (by norm_num) (by norm_num) (by norm_num) w, ?_, by norm_num,
    by norm_num, fun U₀ N₂ w => ?_, ?_⟩
  · rw [abs_le]; constructor <;> norm_num
  · have := (bm_pw_printed_wrong (γ := 4) (U₂ := 5) (by norm_num) (by norm_num) U₀ N₂ w).1
    simp only [hl] at this; exact this
  · exact bm_kappa0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0

/-- **Instance of (9.3.96)–(9.3.99)**: the quadratic saddle `U = -5x²/2` with `γ = 4`
(`s = 5/16`): the corrected `τ₃` is the exact mean first-passage time of (9.3.96), and the
printed (9.3.97) differs from it on `(-1, 0)`. -/
theorem corrSmol_instance (a b x : ℝ) :
    tau3 (fun y => -(5 / 2) * y ^ 2) (fun _ => -5) 4 a b x
      = mfptReflA (fun y => (0 : ℝ) / 4 ^ 3 - (1 + -5 / 4 ^ 2) / 4 * (-5 * y))
          (fun _ => 2 * ((1 + -5 / 4 ^ 2) / 4)) a b x ∧
    tau3Printed (fun y => -(5 / 2) * y ^ 2) (fun _ => -5) 4 (-1) 0 (-1 / 2)
      ≠ tau3 (fun y => -(5 / 2) * y ^ 2) (fun _ => -5) 4 (-1) 0 (-1 / 2) := by
  constructor
  · refine tau3_spec (U' := fun y => -5 * y) (U''' := fun _ => 0) (by norm_num) (fun y => ?_)
      (fun y => ?_) (fun y => hasDerivAt_const _ _) continuous_const (fun _ => by norm_num) a b x
    · convert (hasDerivAt_pow 2 y).const_mul (-(5 / 2) : ℝ) using 1; push_cast; ring
    · simpa using (hasDerivAt_id y).const_mul (-5 : ℝ)
  · exact tau3_printed_wrong _ (by fun_prop) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

end Gardiner.Escape
