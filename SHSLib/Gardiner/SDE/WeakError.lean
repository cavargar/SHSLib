/-
# Weak error of order `τ` for the Euler, Milstein and semi-implicit schemes on linear SDEs
(Gardiner §10.1.4 b), §10.1.5, §10.4)

The text's weak-order arguments ((10.1.27)–(10.1.30), (10.1.41)) are heuristic.  For the two
linear test SDEs

* Ornstein–Uhlenbeck `dx = -γx dt + σ dW`, exact moments `⟨x⟩ = x₀e^{-γt}`,
  `⟨x²⟩ = x₀²e^{-2γt} + (σ²/2γ)(1 - e^{-2γt})` (`Gardiner.SDE.ouMean`, `Gardiner.SDE.ouSecond`);
* linear multiplicative noise `dx = λx dt + μx dW`, exact moments `⟨x⟩ = x₀e^{λt}`,
  `⟨x²⟩ = x₀²e^{(2λ+μ²)t}` (`Gardiner.SDE.gbmMean`, `Gardiner.SDE.gbmSecond`),

the moments of every scheme can be computed exactly (`SHSLib.Gardiner.SDE.SchemeMoments`), and we
prove **genuine weak-error bounds of order `τ` with explicit constants**, for the schemes driven
by i.i.d. `N(0, τ)` increments.  The exact moments are characterised by their moment ODEs
(`Gardiner.SDE.ouMean_hasDerivAt`, …); deriving those ODEs from the SDE requires Itô's formula
and is not part of this layer.

| scheme | SDE | Lean |
|---|---|---|
| Euler (10.1.15) | OU | `Gardiner.SDE.eulerOU_weak_mean`, `Gardiner.SDE.eulerOU_weak_second` |
| semi-implicit (10.3.13) = (10.4.12)–(10.4.15) | OU | `Gardiner.SDE.semiOU_weak_mean`, `Gardiner.SDE.semiOU_weak_second` |
| Euler (10.1.15) | multiplicative | `Gardiner.SDE.eulerGBM_weak_mean`, `Gardiner.SDE.eulerGBM_weak_second` |
| Milstein (10.1.32) | multiplicative | `Gardiner.SDE.milsteinGBM_weak_mean`, `Gardiner.SDE.milsteinGBM_weak_second` |
| semi-implicit (10.4.16)–(10.4.17), two fixed-point iterations | multiplicative | `Gardiner.SDE.semiGBM_weak_mean`, `Gardiner.SDE.semiGBM_weak_second` |

For additive noise Milstein coincides with Euler (`b' = 0`).  The semi-implicit scheme for
multiplicative noise is implemented as in the text "by simple iteration": with two iterations
from `ȳ⁰ = yₙ` it is `y_{n+1} = yₙ(1 + κ + κ²/2)`, `κ = (λ - μ²/2)τ + μΔWₙ`
(`Gardiner.SDE.semiGBM_iter`).

Two generic lemmas carry the analysis: `Gardiner.SDE.weak_factor` (an amplification factor
`1 + cτ + O(τ²)` raised to the power `N = T/τ` is within `O(τ)` of `e^{cT}`) and
`Gardiner.SDE.affine_error` (local errors `O(τ²)` of a stable affine recursion accumulate to
`O(τ)`).
-/
import SHSLib.Gardiner.SDE.SchemeMoments

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section

namespace Gardiner.SDE

/-! ### Generic analysis -/

/-- Telescoping: `|gᴺ - e^{cNτ}| ≤ N K τ² e^{BNτ}` if `|g - e^{cτ}| ≤ Kτ²`, `|g| ≤ e^{Bτ}`,
`c ≤ B`, `0 ≤ B`. -/
lemma pow_sub_exp_le {g c τ K B : ℝ} (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hcB : c ≤ B)
    (hg : |g - Real.exp (c * τ)| ≤ K * τ ^ 2) (hgB : |g| ≤ Real.exp (B * τ)) (N : ℕ) :
    |g ^ N - Real.exp (c * (N * τ))| ≤ N * (K * τ ^ 2) * Real.exp (B * (N * τ)) := by
  have hKt : 0 ≤ K * τ ^ 2 := (abs_nonneg _).trans hg
  induction N with
  | zero => simp
  | succ N ih =>
    have hsplit : g ^ (N + 1) - Real.exp (c * ((N + 1 : ℕ) * τ)) =
        g * (g ^ N - Real.exp (c * (N * τ))) + Real.exp (c * (N * τ)) * (g - Real.exp (c * τ)) := by
      rw [show c * (((N + 1 : ℕ) : ℝ) * τ) = c * (N * τ) + c * τ by push_cast; ring, Real.exp_add]
      ring
    have h1 : Real.exp (c * (N * τ)) ≤ Real.exp (B * (N * τ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcB (by positivity))
    have h2 : Real.exp (B * (N * τ)) ≤ Real.exp (B * ((N + 1 : ℕ) * τ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by push_cast; nlinarith) hB)
    have h3 : Real.exp (B * τ) * Real.exp (B * (N * τ)) = Real.exp (B * ((N + 1 : ℕ) * τ)) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    rw [hsplit]
    calc |g * (g ^ N - Real.exp (c * (N * τ))) + Real.exp (c * (N * τ)) * (g - Real.exp (c * τ))|
        ≤ |g| * |g ^ N - Real.exp (c * (N * τ))| +
          Real.exp (c * (N * τ)) * |g - Real.exp (c * τ)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (B * τ) * (N * (K * τ ^ 2) * Real.exp (B * (N * τ))) +
          Real.exp (B * (N * τ)) * (K * τ ^ 2) := by
          gcongr
      _ ≤ Real.exp (B * ((N + 1 : ℕ) * τ)) * (N * (K * τ ^ 2)) +
          Real.exp (B * ((N + 1 : ℕ) * τ)) * (K * τ ^ 2) := by
          rw [← h3]
          nlinarith [Real.exp_pos (B * τ), Real.exp_pos (B * (N * τ))]
      _ = ((N + 1 : ℕ) : ℝ) * (K * τ ^ 2) * Real.exp (B * ((N + 1 : ℕ) * τ)) := by
          push_cast; ring

/-- Local error of an amplification factor `1 + cτ + τ²q`, `|q| ≤ Q`. -/
lemma local_of_expansion {c τ q Q : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hcτ : |c * τ| ≤ 1)
    (hq : |q| ≤ Q) :
    |(1 + c * τ + τ ^ 2 * q) - Real.exp (c * τ)| ≤ (c ^ 2 + Q) * τ ^ 2 ∧
    |1 + c * τ + τ ^ 2 * q| ≤ Real.exp ((|c| + Q) * τ) := by
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hq
  have he := Real.abs_exp_sub_one_sub_id_le hcτ
  constructor
  · have : (1 + c * τ + τ ^ 2 * q) - Real.exp (c * τ) =
        -(Real.exp (c * τ) - 1 - c * τ) + τ ^ 2 * q := by ring
    rw [this]
    calc |-(Real.exp (c * τ) - 1 - c * τ) + τ ^ 2 * q|
        ≤ |Real.exp (c * τ) - 1 - c * τ| + τ ^ 2 * |q| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg τ)]
      _ ≤ (c * τ) ^ 2 + τ ^ 2 * Q := by gcongr
      _ = (c ^ 2 + Q) * τ ^ 2 := by ring
  · calc |1 + c * τ + τ ^ 2 * q| ≤ 1 + |c| * τ + τ ^ 2 * Q := by
          refine (abs_add_le _ _).trans ?_
          refine add_le_add ((abs_add_le _ _).trans ?_) ?_
          · rw [abs_one, abs_mul, abs_of_nonneg hτ0]
          · rw [abs_mul, abs_of_nonneg (sq_nonneg τ)]; gcongr
      _ ≤ (|c| + Q) * τ + 1 := by
          have h1 : τ ^ 2 ≤ τ := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right h1 hQ]
      _ ≤ Real.exp ((|c| + Q) * τ) := Real.add_one_le_exp _

/-- **Generic weak error for an amplification factor**: if `g = 1 + cτ + τ²q` with `|q| ≤ Q`,
`0 < τ ≤ 1` and `|cτ| ≤ 1`, then `|gᴺ - e^{cT}| ≤ (c² + Q) T e^{(|c|+Q)T} τ` with `T = Nτ`. -/
theorem weak_factor {c τ q Q : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hcτ : |c * τ| ≤ 1)
    (hq : |q| ≤ Q) (N : ℕ) :
    |(1 + c * τ + τ ^ 2 * q) ^ N - Real.exp (c * (N * τ))| ≤
      (c ^ 2 + Q) * (N * τ) * Real.exp ((|c| + Q) * (N * τ)) * τ := by
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hq
  obtain ⟨h1, h2⟩ := local_of_expansion hτ0 hτ1 hcτ hq
  have := pow_sub_exp_le hτ0 (by positivity) (by linarith [le_abs_self c]) h1 h2 N
  calc _ ≤ N * ((c ^ 2 + Q) * τ ^ 2) * Real.exp ((|c| + Q) * (N * τ)) := this
    _ = _ := by ring

/-- **Accumulation of local errors in a stable affine recursion.**  If `v_{n+1} = ρvₙ + q`,
`S_{n+1} = RSₙ + p`, `v₀ = S₀`, `|ρ| ≤ 1`, `|ρ - R| ≤ K₁τ²`, `|q - p| ≤ K₂τ²` and `|Sₙ| ≤ M`, then
`|v_N - S_N| ≤ N (K₁M + K₂) τ²`. -/
theorem affine_error {ρ R q p M K₁ K₂ τ : ℝ} (v S : ℕ → ℝ) (hv : ∀ n, v (n + 1) = ρ * v n + q)
    (hS : ∀ n, S (n + 1) = R * S n + p) (h0 : v 0 = S 0) (hρ : |ρ| ≤ 1)
    (hρR : |ρ - R| ≤ K₁ * τ ^ 2) (hqp : |q - p| ≤ K₂ * τ ^ 2) (hM : ∀ n, |S n| ≤ M) (N : ℕ) :
    |v N - S N| ≤ N * (K₁ * M + K₂) * τ ^ 2 := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    have hsplit : v (N + 1) - S (N + 1) = ρ * (v N - S N) + (ρ - R) * S N + (q - p) := by
      rw [hv, hS]; ring
    rw [hsplit]
    calc |ρ * (v N - S N) + (ρ - R) * S N + (q - p)|
        ≤ |ρ| * |v N - S N| + |ρ - R| * |S N| + |q - p| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
          rw [abs_mul, abs_mul]
      _ ≤ 1 * (N * (K₁ * M + K₂) * τ ^ 2) + K₁ * τ ^ 2 * M + K₂ * τ ^ 2 := by
          gcongr
          · exact (abs_nonneg _).trans hρR
          · exact hM N
      _ = ((N + 1 : ℕ) : ℝ) * (K₁ * M + K₂) * τ ^ 2 := by push_cast; ring

/-! ### Exact moments of the two linear SDEs and their moment equations -/

/-- Mean of the Ornstein–Uhlenbeck process `dx = -γx dt + σ dW`, `x(0) = x₀`. -/
def ouMean (γ x0 t : ℝ) : ℝ := x0 * Real.exp (-γ * t)
/-- Second moment of the Ornstein–Uhlenbeck process. -/
def ouSecond (γ σ x0 t : ℝ) : ℝ :=
  Real.exp (-2 * γ * t) * x0 ^ 2 + σ ^ 2 / (2 * γ) * (1 - Real.exp (-2 * γ * t))
/-- Mean of `dx = λx dt + μx dW`. -/
def gbmMean (lam x0 t : ℝ) : ℝ := x0 * Real.exp (lam * t)
/-- Second moment of `dx = λx dt + μx dW`. -/
def gbmSecond (lam mu x0 t : ℝ) : ℝ := x0 ^ 2 * Real.exp ((2 * lam + mu ^ 2) * t)

theorem ouMean_hasDerivAt (γ x0 t : ℝ) :
    HasDerivAt (ouMean γ x0) (-γ * ouMean γ x0 t) t := by
  have := (((hasDerivAt_id t).const_mul (-γ)).exp).const_mul x0
  convert this using 1; simp [ouMean]; ring

theorem ouSecond_hasDerivAt {γ : ℝ} (hγ : γ ≠ 0) (σ x0 t : ℝ) :
    HasDerivAt (ouSecond γ σ x0) (-2 * γ * ouSecond γ σ x0 t + σ ^ 2) t := by
  have he := ((hasDerivAt_id t).const_mul (-2 * γ)).exp
  have := (he.mul_const (x0 ^ 2)).add ((he.const_sub 1).const_mul (σ ^ 2 / (2 * γ)))
  convert this using 1
  simp only [ouSecond, id]; field_simp; ring

theorem gbmMean_hasDerivAt (lam x0 t : ℝ) :
    HasDerivAt (gbmMean lam x0) (lam * gbmMean lam x0 t) t := by
  have := (((hasDerivAt_id t).const_mul lam).exp).const_mul x0
  convert this using 1; simp [gbmMean]; ring

theorem gbmSecond_hasDerivAt (lam mu x0 t : ℝ) :
    HasDerivAt (gbmSecond lam mu x0) ((2 * lam + mu ^ 2) * gbmSecond lam mu x0 t) t := by
  have := (((hasDerivAt_id t).const_mul (2 * lam + mu ^ 2)).exp).const_mul (x0 ^ 2)
  convert this using 1; simp [gbmSecond]; ring

lemma ouSecond_step (γ σ x0 τ : ℝ) (n : ℕ) :
    ouSecond γ σ x0 ((n + 1 : ℕ) * τ) = Real.exp (-2 * γ * τ) * ouSecond γ σ x0 (n * τ) +
      σ ^ 2 / (2 * γ) * (1 - Real.exp (-2 * γ * τ)) := by
  simp only [ouSecond]
  rw [show -2 * γ * (((n + 1 : ℕ) : ℝ) * τ) = -2 * γ * τ + -2 * γ * (n * τ) by push_cast; ring,
    Real.exp_add]
  ring

lemma ouSecond_bound {γ : ℝ} (hγ : 0 < γ) (σ x0 t : ℝ) (ht : 0 ≤ t) :
    |ouSecond γ σ x0 t| ≤ x0 ^ 2 + σ ^ 2 / (2 * γ) := by
  have h1 : 0 < Real.exp (-2 * γ * t) := Real.exp_pos _
  have h2 : Real.exp (-2 * γ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h3 : 0 ≤ σ ^ 2 / (2 * γ) := by positivity
  rw [ouSecond, abs_of_nonneg (by nlinarith [sq_nonneg x0])]
  nlinarith [sq_nonneg x0]

/-! ### The schemes as linear one-step maps -/

/-- Euler (10.1.15) for the OU process (also Milstein, since `b' = 0`). -/
def eulerOU (γ σ τ : ℝ) : LinStep := ⟨1 - γ * τ, 0, 0, 0, σ⟩

/-- Semi-implicit (10.3.13) / (10.4.12)–(10.4.15) for the OU process. -/
def semiOU (γ σ τ : ℝ) : LinStep := ⟨(1 - γ * τ / 2) / (1 + γ * τ / 2), 0, 0, 0, σ / (1 + γ * τ / 2)⟩

/-- Euler (10.1.15) for `dx = λx dt + μx dW`. -/
def eulerGBM (lam mu τ : ℝ) : LinStep := ⟨1 + lam * τ, mu, 0, 0, 0⟩

/-- Milstein (10.1.32) for `dx = λx dt + μx dW`. -/
def milsteinGBM (lam mu τ : ℝ) : LinStep := ⟨1 + lam * τ - mu ^ 2 * τ / 2, mu, mu ^ 2 / 2, 0, 0⟩

/-- Semi-implicit (10.4.16)–(10.4.17) with two fixed-point iterations, for
`dx = λx dt + μx dW` (Stratonovich drift `A = (λ - μ²/2)x`, (10.4.10)). -/
def semiGBM (lam mu τ : ℝ) : LinStep :=
  ⟨1 + (lam - mu ^ 2 / 2) * τ + (lam - mu ^ 2 / 2) ^ 2 * τ ^ 2 / 2,
    mu * (1 + (lam - mu ^ 2 / 2) * τ), mu ^ 2 / 2, 0, 0⟩

theorem eulerOU_apply (γ σ τ y z : ℝ) : (eulerOU γ σ τ).apply y z = y + (-γ * y) * τ + σ * z := by
  simp [eulerOU, LinStep.apply, LinStep.G, LinStep.H]; ring

/-- `semiOU` solves the semi-implicit equation `y' = y + a((y + y')/2) τ + σ ΔW`, `a(x) = -γx`. -/
theorem semiOU_spec {γ τ : ℝ} (h : 1 + γ * τ / 2 ≠ 0) (σ y z : ℝ) :
    (semiOU γ σ τ).apply y z =
      y + (-γ * ((y + (semiOU γ σ τ).apply y z) / 2)) * τ + σ * z := by
  simp only [semiOU, LinStep.apply, LinStep.G, LinStep.H, zero_mul, add_zero, zero_add]
  have hu : (1 + γ * τ / 2) * (1 + γ * τ / 2)⁻¹ = 1 := mul_inv_cancel₀ h
  simp only [div_eq_mul_inv (1 - γ * τ / 2)]
  linear_combination ((1 - γ * τ / 2) * y + σ * z) * hu

theorem eulerGBM_apply (lam mu τ y z : ℝ) :
    (eulerGBM lam mu τ).apply y z = y + lam * y * τ + mu * y * z := by
  simp [eulerGBM, LinStep.apply, LinStep.G, LinStep.H]; ring

/-- `milsteinGBM` is (10.1.32) with `a = λx`, `b = μx`, `c = ½bb' = ½μ²x`. -/
theorem milsteinGBM_apply (lam mu τ y z : ℝ) :
    (milsteinGBM lam mu τ).apply y z =
      y + lam * y * τ + mu * y * z + (1 / 2) * (mu * y) * mu * (z ^ 2 - τ) := by
  simp [milsteinGBM, LinStep.apply, LinStep.G, LinStep.H]; ring

/-- `semiGBM` is (10.4.16)–(10.4.17) with two fixed-point iterations started at `ȳ⁰ = yₙ`:
`ȳ^{k+1} = yₙ + ½A(ȳᵏ)τ + ½b(ȳᵏ)ΔW`, `y_{n+1} = 2ȳ² - yₙ`, with `A(x) = (λ - μ²/2)x`,
`b(x) = μx`. -/
theorem semiGBM_iter (lam mu τ y z : ℝ) :
    let A : ℝ → ℝ := fun x => (lam - mu ^ 2 / 2) * x
    let b : ℝ → ℝ := fun x => mu * x
    let y1 := y + A y * τ / 2 + b y * z / 2
    let y2 := y + A y1 * τ / 2 + b y1 * z / 2
    (semiGBM lam mu τ).apply y z = 2 * y2 - y := by
  simp only [semiGBM, LinStep.apply, LinStep.G, LinStep.H]; ring

/-! ### Weak errors -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {τ : ℝ≥0} {ξ : ℕ → Ω → ℝ}

/-- **Euler, multiplicative noise, mean**: `|⟨y_N⟩ - x₀e^{λT}| ≤ |x₀| λ² T e^{|λ|T} τ`,
`T = Nτ`, for `τ ≤ 1`, `|λτ| ≤ 1`. -/
theorem eulerGBM_weak_mean (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {lam mu x0 : ℝ} (hτ1 : (τ : ℝ) ≤ 1)
    (hl : |lam * τ| ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (eulerGBM lam mu τ) x0 ξ N ω ∂P - gbmMean lam x0 (N * τ)| ≤
      |x0| * (lam ^ 2 * (N * τ) * Real.exp (|lam| * (N * τ)) * τ) := by
  rw [linScheme_mean _ x0 hξm hind hlaw rfl, gbmMean, ← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := weak_factor (q := 0) (Q := 0) τ.2 hτ1 hl (by simp) N
  simp only [LinStep.EG, eulerGBM, mul_zero, add_zero, zero_mul] at this ⊢
  exact this

/-- **Euler, multiplicative noise, second moment**:
`|⟨y_N²⟩ - x₀²e^{(2λ+μ²)T}| ≤ x₀² ((2λ+μ²)² + λ²) T e^{(|2λ+μ²| + λ²)T} τ`. -/
theorem eulerGBM_weak_second (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {lam mu x0 : ℝ} (hτ1 : (τ : ℝ) ≤ 1)
    (hc : |(2 * lam + mu ^ 2) * τ| ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (eulerGBM lam mu τ) x0 ξ N ω ^ 2 ∂P - gbmSecond lam mu x0 (N * τ)| ≤
      x0 ^ 2 * (((2 * lam + mu ^ 2) ^ 2 + lam ^ 2) * (N * τ) *
        Real.exp ((|2 * lam + mu ^ 2| + lam ^ 2) * (N * τ)) * τ) := by
  rw [linScheme_sq _ x0 hξm hind hlaw rfl rfl, gbmSecond, ← mul_sub, abs_mul, abs_of_nonneg
    (sq_nonneg x0)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have h := weak_factor (q := lam ^ 2) (Q := lam ^ 2) τ.2 hτ1 hc (by simp) N
  have hEG2 : (eulerGBM lam mu τ).EG2 τ = 1 + (2 * lam + mu ^ 2) * τ + (τ : ℝ) ^ 2 * lam ^ 2 := by
    simp only [LinStep.EG2, eulerGBM]; ring
  rw [hEG2]; exact h

/-- **Milstein, multiplicative noise, mean** (same factor `1 + λτ` as Euler). -/
theorem milsteinGBM_weak_mean (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {lam mu x0 : ℝ} (hτ1 : (τ : ℝ) ≤ 1)
    (hl : |lam * τ| ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (milsteinGBM lam mu τ) x0 ξ N ω ∂P - gbmMean lam x0 (N * τ)| ≤
      |x0| * (lam ^ 2 * (N * τ) * Real.exp (|lam| * (N * τ)) * τ) := by
  rw [linScheme_mean _ x0 hξm hind hlaw rfl, gbmMean, ← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := weak_factor (q := 0) (Q := 0) τ.2 hτ1 hl (by simp) N
  have hEG : (milsteinGBM lam mu τ).EG τ = 1 + lam * τ + (τ : ℝ) ^ 2 * 0 := by
    simp only [LinStep.EG, milsteinGBM]; ring
  rw [hEG]; simpa using h

/-- **Milstein, multiplicative noise, second moment**: the factor is
`(1+λτ)² + μ²τ + ½μ⁴τ²`, so the constant is `(2λ+μ²)² + λ² + μ⁴/2`. -/
theorem milsteinGBM_weak_second (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {lam mu x0 : ℝ} (hτ1 : (τ : ℝ) ≤ 1)
    (hc : |(2 * lam + mu ^ 2) * τ| ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (milsteinGBM lam mu τ) x0 ξ N ω ^ 2 ∂P - gbmSecond lam mu x0 (N * τ)| ≤
      x0 ^ 2 * (((2 * lam + mu ^ 2) ^ 2 + (lam ^ 2 + mu ^ 4 / 2)) * (N * τ) *
        Real.exp ((|2 * lam + mu ^ 2| + (lam ^ 2 + mu ^ 4 / 2)) * (N * τ)) * τ) := by
  rw [linScheme_sq _ x0 hξm hind hlaw rfl rfl, gbmSecond, ← mul_sub, abs_mul, abs_of_nonneg
    (sq_nonneg x0)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have h := weak_factor (q := lam ^ 2 + mu ^ 4 / 2) (Q := lam ^ 2 + mu ^ 4 / 2) τ.2 hτ1 hc
    (by rw [abs_of_nonneg (by positivity)]) N
  have hEG2 : (milsteinGBM lam mu τ).EG2 τ =
      1 + (2 * lam + mu ^ 2) * τ + (τ : ℝ) ^ 2 * (lam ^ 2 + mu ^ 4 / 2) := by
    simp only [LinStep.EG2, milsteinGBM]; ring
  rw [hEG2]; exact h

/-- **Semi-implicit (iterated), multiplicative noise, mean**: the factor is
`1 + λτ + β²τ²/2`, `β = λ - μ²/2`. -/
theorem semiGBM_weak_mean (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {lam mu x0 : ℝ} (hτ1 : (τ : ℝ) ≤ 1)
    (hl : |lam * τ| ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (semiGBM lam mu τ) x0 ξ N ω ∂P - gbmMean lam x0 (N * τ)| ≤
      |x0| * ((lam ^ 2 + (lam - mu ^ 2 / 2) ^ 2 / 2) * (N * τ) *
        Real.exp ((|lam| + (lam - mu ^ 2 / 2) ^ 2 / 2) * (N * τ)) * τ) := by
  rw [linScheme_mean _ x0 hξm hind hlaw rfl, gbmMean, ← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := weak_factor (q := (lam - mu ^ 2 / 2) ^ 2 / 2) (Q := (lam - mu ^ 2 / 2) ^ 2 / 2)
    τ.2 hτ1 hl (by rw [abs_of_nonneg (by positivity)]) N
  have hEG : (semiGBM lam mu τ).EG τ = 1 + lam * τ + (τ : ℝ) ^ 2 * ((lam - mu ^ 2 / 2) ^ 2 / 2) := by
    simp only [LinStep.EG, semiGBM]; ring
  rw [hEG]; exact h

/-- The constant in the second-moment weak error of the iterated semi-implicit scheme. -/
def semiGBMConst (lam mu : ℝ) : ℝ :=
  let β := lam - mu ^ 2 / 2
  2 * β ^ 2 + 3 * |β| * mu ^ 2 + 3 / 4 * mu ^ 4 + |β| ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2 + β ^ 4 / 4

/-- **Semi-implicit (iterated), multiplicative noise, second moment**. -/
theorem semiGBM_weak_second (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {lam mu x0 : ℝ} (hτ1 : (τ : ℝ) ≤ 1)
    (hc : |(2 * lam + mu ^ 2) * τ| ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (semiGBM lam mu τ) x0 ξ N ω ^ 2 ∂P - gbmSecond lam mu x0 (N * τ)| ≤
      x0 ^ 2 * (((2 * lam + mu ^ 2) ^ 2 + semiGBMConst lam mu) * (N * τ) *
        Real.exp ((|2 * lam + mu ^ 2| + semiGBMConst lam mu) * (N * τ)) * τ) := by
  rw [linScheme_sq _ x0 hξm hind hlaw rfl rfl, gbmSecond, ← mul_sub, abs_mul, abs_of_nonneg
    (sq_nonneg x0)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  set β := lam - mu ^ 2 / 2 with hβ
  set t : ℝ := (τ : ℝ)
  have ht0 : 0 ≤ t := τ.2
  set q := 2 * β ^ 2 + 3 * β * mu ^ 2 + 3 / 4 * mu ^ 4 + t * (β ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2) +
    t ^ 2 * (β ^ 4 / 4)
  have hq : |q| ≤ semiGBMConst lam mu := by
    simp only [semiGBMConst, q]
    rw [← hβ]
    have hb3 : |β ^ 3| = |β| ^ 3 := abs_pow β 3
    have h1 : |t * (β ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2)| ≤ |β| ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2 := by
      rw [abs_mul, abs_of_nonneg ht0]
      have : |β ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2| ≤ |β| ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [hb3, abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 / 2 * β ^ 2 * mu ^ 2)]
      calc t * |β ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2| ≤ 1 * (|β| ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2) :=
            mul_le_mul hτ1 this (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have h2 : |t ^ 2 * (β ^ 4 / 4)| ≤ β ^ 4 / 4 := by
      rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have : t ^ 2 ≤ 1 := by nlinarith
      nlinarith [pow_nonneg (sq_nonneg β) 2]
    have h3 : |3 * β * mu ^ 2| = 3 * |β| * mu ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg mu)]; norm_num
    have h4 : |2 * β ^ 2 + 3 * β * mu ^ 2 + 3 / 4 * mu ^ 4| ≤ 2 * β ^ 2 + 3 * |β| * mu ^ 2 +
        3 / 4 * mu ^ 4 := by
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ((abs_add_le _ _).trans ?_) ?_
      · rw [h3, abs_of_nonneg (by positivity)]
      · rw [abs_of_nonneg (by positivity)]
    calc |2 * β ^ 2 + 3 * β * mu ^ 2 + 3 / 4 * mu ^ 4 + t * (β ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2) +
          t ^ 2 * (β ^ 4 / 4)|
        ≤ |2 * β ^ 2 + 3 * β * mu ^ 2 + 3 / 4 * mu ^ 4| +
          |t * (β ^ 3 + 3 / 2 * β ^ 2 * mu ^ 2)| + |t ^ 2 * (β ^ 4 / 4)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have h := weak_factor (q := q) (Q := semiGBMConst lam mu) ht0 hτ1 hc hq N
  have hEG2 : (semiGBM lam mu τ).EG2 τ = 1 + (2 * lam + mu ^ 2) * t + t ^ 2 * q := by
    simp only [LinStep.EG2, semiGBM, q, β, t]; ring
  rw [hEG2]; exact h

/-- **Euler, Ornstein–Uhlenbeck, mean**: `|⟨y_N⟩ - x₀e^{-γT}| ≤ |x₀| γ² T e^{|γ|T} τ`. -/
theorem eulerOU_weak_mean (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {γ σ x0 : ℝ} (hτ1 : (τ : ℝ) ≤ 1)
    (hl : |γ * τ| ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (eulerOU γ σ τ) x0 ξ N ω ∂P - ouMean γ x0 (N * τ)| ≤
      |x0| * (γ ^ 2 * (N * τ) * Real.exp (|γ| * (N * τ)) * τ) := by
  rw [linScheme_mean _ x0 hξm hind hlaw rfl, ouMean, ← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := weak_factor (c := -γ) (q := 0) (Q := 0) τ.2 hτ1 (by rwa [neg_mul, abs_neg]) (by simp) N
  have hEG : (eulerOU γ σ τ).EG τ = 1 + -γ * τ + (τ : ℝ) ^ 2 * 0 := by
    simp only [LinStep.EG, eulerOU]; ring
  rw [hEG]; simpa [abs_neg] using h

/-- **Semi-implicit, Ornstein–Uhlenbeck, mean**: the factor is
`r = (1 - γτ/2)/(1 + γτ/2) = 1 - γτ + γ²τ²/(2 + γτ)`. -/
theorem semiOU_weak_mean (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {γ σ x0 : ℝ} (hγ : 0 ≤ γ) (hτ1 : (τ : ℝ) ≤ 1)
    (hl : γ * τ ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (semiOU γ σ τ) x0 ξ N ω ∂P - ouMean γ x0 (N * τ)| ≤
      |x0| * ((γ ^ 2 + γ ^ 2 / 2) * (N * τ) * Real.exp ((γ + γ ^ 2 / 2) * (N * τ)) * τ) := by
  rw [linScheme_mean _ x0 hξm hind hlaw rfl, ouMean, ← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  set t : ℝ := (τ : ℝ)
  have ht0 : 0 ≤ t := τ.2
  have hpos : 0 < 2 + γ * t := by positivity
  have hq : |γ ^ 2 / (2 + γ * t)| ≤ γ ^ 2 / 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by nlinarith)
  have hγt : |-γ * t| ≤ 1 := by
    rw [neg_mul, abs_neg, abs_of_nonneg (by positivity)]; exact hl
  have h := weak_factor (c := -γ) (q := γ ^ 2 / (2 + γ * t)) (Q := γ ^ 2 / 2) ht0 hτ1 hγt hq N
  have hEG : (semiOU γ σ τ).EG τ = 1 + -γ * t + t ^ 2 * (γ ^ 2 / (2 + γ * t)) := by
    simp only [LinStep.EG, semiOU, t]
    field_simp
    ring
  rw [hEG]
  simpa [abs_neg, abs_of_nonneg hγ] using h

/-- **Euler, Ornstein–Uhlenbeck, second moment**: with `M = x₀² + σ²/2γ`,
`|⟨y_N²⟩ - ⟨x²⟩(T)| ≤ T (5γ²M + 2γσ²) τ` for `γ > 0`, `2γτ ≤ 1`. -/
theorem eulerOU_weak_second (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {γ σ x0 : ℝ} (hγ : 0 < γ)
    (hl : 2 * γ * τ ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (eulerOU γ σ τ) x0 ξ N ω ^ 2 ∂P - ouSecond γ σ x0 (N * τ)| ≤
      (N * τ) * (5 * γ ^ 2 * (x0 ^ 2 + σ ^ 2 / (2 * γ)) + 2 * γ * σ ^ 2) * τ := by
  set t : ℝ := (τ : ℝ)
  have ht0 : 0 ≤ t := τ.2
  have hx : |-2 * γ * t| ≤ 1 := by
    rw [abs_of_nonpos (by nlinarith)]; linarith
  have he := Real.abs_exp_sub_one_sub_id_le hx
  have h := affine_error (ρ := (1 - γ * t) ^ 2) (R := Real.exp (-2 * γ * t)) (q := σ ^ 2 * t)
    (p := σ ^ 2 / (2 * γ) * (1 - Real.exp (-2 * γ * t))) (M := x0 ^ 2 + σ ^ 2 / (2 * γ))
    (K₁ := 5 * γ ^ 2) (K₂ := 2 * γ * σ ^ 2) 
    (fun n => ∫ ω, linScheme (eulerOU γ σ τ) x0 ξ n ω ^ 2 ∂P)
    (fun n => ouSecond γ σ x0 (n * t))
    (fun n => by
      beta_reduce
      rw [linScheme_sq_additive _ x0 hξm hind hlaw rfl rfl rfl n]; simp [eulerOU, t])
    (fun n => ouSecond_step γ σ x0 t n)
    (by simp [linScheme, ouSecond])
    (by
      have : 0 ≤ γ * t := by positivity
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith)
    (by
      have : (1 - γ * t) ^ 2 - Real.exp (-2 * γ * t) =
          -(Real.exp (-2 * γ * t) - 1 - -2 * γ * t) + γ ^ 2 * t ^ 2 := by ring
      rw [this]
      calc _ ≤ |Real.exp (-2 * γ * t) - 1 - -2 * γ * t| + |γ ^ 2 * t ^ 2| :=
            (abs_add_le _ _).trans (by rw [abs_neg])
        _ ≤ (-2 * γ * t) ^ 2 + γ ^ 2 * t ^ 2 := by
            gcongr; exact (abs_of_nonneg (by positivity)).le
        _ = 5 * γ ^ 2 * t ^ 2 := by ring)
    (by
      have : σ ^ 2 * t - σ ^ 2 / (2 * γ) * (1 - Real.exp (-2 * γ * t)) =
          σ ^ 2 / (2 * γ) * (Real.exp (-2 * γ * t) - 1 - -2 * γ * t) := by field_simp; ring
      rw [this, abs_mul, abs_of_nonneg (by positivity)]
      calc σ ^ 2 / (2 * γ) * |Real.exp (-2 * γ * t) - 1 - -2 * γ * t|
          ≤ σ ^ 2 / (2 * γ) * (-2 * γ * t) ^ 2 := by gcongr
        _ = 2 * γ * σ ^ 2 * t ^ 2 := by field_simp)
    (fun n => ouSecond_bound hγ σ x0 _ (by positivity)) N
  calc _ ≤ N * (5 * γ ^ 2 * (x0 ^ 2 + σ ^ 2 / (2 * γ)) + 2 * γ * σ ^ 2) * t ^ 2 := h
    _ = _ := by ring

/-- **Semi-implicit, Ornstein–Uhlenbeck, second moment**: with `M = x₀² + σ²/2γ`,
`|⟨y_N²⟩ - ⟨x²⟩(T)| ≤ T (7γ²M + 4γσ²) τ` for `γ > 0`, `2γτ ≤ 1`. -/
theorem semiOU_weak_second (hξm : ∀ n, Measurable (ξ n)) (hind : iIndepFun ξ P)
    (hlaw : ∀ n, P.map (ξ n) = gaussianReal 0 τ) {γ σ x0 : ℝ} (hγ : 0 < γ)
    (hl : 2 * γ * τ ≤ 1) (N : ℕ) :
    |∫ ω, linScheme (semiOU γ σ τ) x0 ξ N ω ^ 2 ∂P - ouSecond γ σ x0 (N * τ)| ≤
      (N * τ) * (7 * γ ^ 2 * (x0 ^ 2 + σ ^ 2 / (2 * γ)) + 4 * γ * σ ^ 2) * τ := by
  set t : ℝ := (τ : ℝ)
  have ht0 : 0 ≤ t := τ.2
  set x := γ * t with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by linarith
  have hpos : 0 < 2 + x := by linarith
  have hxe : |-2 * γ * t| ≤ 1 := by
    rw [abs_of_nonpos (by nlinarith)]; linarith
  have he := Real.abs_exp_sub_one_sub_id_le hxe
  have hr : (semiOU γ σ τ).g0 = (2 - x) / (2 + x) := by
    simp only [semiOU, hxdef, t]; field_simp
  have hh : (semiOU γ σ τ).h1 = 2 * σ / (2 + x) := by
    simp only [semiOU, hxdef, t]; field_simp
  have h := affine_error (ρ := ((2 - x) / (2 + x)) ^ 2) (R := Real.exp (-2 * γ * t))
    (q := (2 * σ / (2 + x)) ^ 2 * t)
    (p := σ ^ 2 / (2 * γ) * (1 - Real.exp (-2 * γ * t))) (M := x0 ^ 2 + σ ^ 2 / (2 * γ))
    (K₁ := 7 * γ ^ 2) (K₂ := 4 * γ * σ ^ 2) 
    (fun n => ∫ ω, linScheme (semiOU γ σ τ) x0 ξ n ω ^ 2 ∂P)
    (fun n => ouSecond γ σ x0 (n * t))
    (fun n => by
      beta_reduce
      rw [linScheme_sq_additive _ x0 hξm hind hlaw rfl rfl rfl n, hr, hh])
    (fun n => ouSecond_step γ σ x0 t n)
    (by simp [linScheme, ouSecond])
    (by
      rw [abs_of_nonneg (sq_nonneg _), div_pow, div_le_one (by positivity)]
      nlinarith)
    (by
      -- `r² - (1 - 2x) = 2x²(4 + x)/(2 + x)²`
      have hid : ((2 - x) / (2 + x)) ^ 2 - Real.exp (-2 * γ * t) =
          2 * x ^ 2 * (4 + x) / (2 + x) ^ 2 + -(Real.exp (-2 * γ * t) - 1 - -2 * γ * t) := by
        rw [hxdef]; field_simp; ring
      rw [hid]
      have h1 : 2 * x ^ 2 * (4 + x) / (2 + x) ^ 2 ≤ 3 * x ^ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have h2 : 0 ≤ 2 * x ^ 2 * (4 + x) / (2 + x) ^ 2 := by positivity
      calc _ ≤ |2 * x ^ 2 * (4 + x) / (2 + x) ^ 2| + |Real.exp (-2 * γ * t) - 1 - -2 * γ * t| :=
            (abs_add_le _ _).trans (by rw [abs_neg])
        _ ≤ 3 * x ^ 2 + (-2 * γ * t) ^ 2 := by
            rw [abs_of_nonneg h2]; exact add_le_add h1 he
        _ ≤ 7 * γ ^ 2 * t ^ 2 := by rw [hxdef]; nlinarith)
    (by
      have hid : (2 * σ / (2 + x)) ^ 2 * t - σ ^ 2 / (2 * γ) * (1 - Real.exp (-2 * γ * t)) =
          -(σ ^ 2 * t * (4 * x + x ^ 2) / (2 + x) ^ 2) +
          σ ^ 2 / (2 * γ) * (Real.exp (-2 * γ * t) - 1 - -2 * γ * t) := by
        rw [hxdef]; field_simp; ring
      rw [hid]
      have h1 : σ ^ 2 * t * (4 * x + x ^ 2) / (2 + x) ^ 2 ≤ 2 * γ * σ ^ 2 * t ^ 2 := by
        rw [div_le_iff₀ (by positivity), hxdef]
        have : 0 ≤ σ ^ 2 * t := by positivity
        nlinarith [mul_nonneg this hx0, mul_nonneg (mul_nonneg this hx0) hx0]
      have h2 : 0 ≤ σ ^ 2 * t * (4 * x + x ^ 2) / (2 + x) ^ 2 := by positivity
      have h3 : σ ^ 2 / (2 * γ) * |Real.exp (-2 * γ * t) - 1 - -2 * γ * t| ≤
          2 * γ * σ ^ 2 * t ^ 2 := by
        calc _ ≤ σ ^ 2 / (2 * γ) * (-2 * γ * t) ^ 2 := by gcongr
          _ = 2 * γ * σ ^ 2 * t ^ 2 := by field_simp
      calc _ ≤ |σ ^ 2 * t * (4 * x + x ^ 2) / (2 + x) ^ 2| +
            |σ ^ 2 / (2 * γ) * (Real.exp (-2 * γ * t) - 1 - -2 * γ * t)| :=
            (abs_add_le _ _).trans (by rw [abs_neg])
        _ ≤ 2 * γ * σ ^ 2 * t ^ 2 + 2 * γ * σ ^ 2 * t ^ 2 := by
            rw [abs_of_nonneg h2, abs_mul, abs_of_nonneg (by positivity)]
            exact add_le_add h1 h3
        _ = 4 * γ * σ ^ 2 * t ^ 2 := by ring)
    (fun n => ouSecond_bound hγ σ x0 _ (by positivity)) N
  calc _ ≤ N * (7 * γ ^ 2 * (x0 ^ 2 + σ ^ 2 / (2 * γ)) + 4 * γ * σ ^ 2) * t ^ 2 := h
    _ = _ := by ring

end Gardiner.SDE
