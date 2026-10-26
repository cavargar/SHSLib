/-
# One-variable schemes: Taylor expansion, Euler, Milstein, implicit schemes and consistency
(Gardiner §10.1, §10.3.1, §10.4)

* **Operators and one-step maps.**  `L₀f = af' + ½b²f''` (10.1.4), `L₁f = bf'` (10.1.5)
  (`Gardiner.SDE.L0`, `Gardiner.SDE.L1`), the Euler map (10.1.15) and the Milstein map (10.1.32)
  with `c = ½L₁b = ½bb'` (10.1.33) (`Gardiner.SDE.eulerStep`, `Gardiner.SDE.milsteinStep`); the
  two printed forms of Milstein agree, (10.1.31) = (10.1.32) (`Gardiner.SDE.milstein_31_eq_32`).
* **Erratum (10.1.18).**  The correction term of the exact one-step expansion is
  `½L₁b(ΔW² - τ)` (from (10.1.7) and (10.1.9)), not `½L₀b(ΔW² - τ)`
  (`Gardiner.SDE.eq_10_1_18_printed_wrong`).
* **The double integral (10.1.9), Itô-free.**  For *any* partition increments `δᵢ` with partial
  sums `Sᵢ`, the left-point sum is `Σ Sᵢδᵢ = ½(S_n² - Σδᵢ²)` (`Gardiner.SDE.ito_sum_identity`),
  while the midpoint (Stratonovich) sum is exactly `½S_n²`
  (`Gardiner.SDE.strat_sum_identity`).  With the quadratic variation `Σδᵢ² = t - t₀` as a
  hypothesis this is (10.1.9) (`Gardiner.SDE.ito_sum_of_qv`).
* **Multiple integrals (10.1.10)–(10.1.12) as a given law.**  The pair `(ΔW, ΔZ)`,
  `ΔZ = ∫ds∫dW`, is not a function of `ΔW`; we take its law as given through the standard
  realisation `ΔW = √τ ξ`, `ΔZ = ½τ^{3/2}(ξ + η/√3)` with `ξ, η` uncorrelated, unit variance, and
  prove `⟨ΔZ⟩ = 0`, `⟨ΔZ²⟩ = τ³/3`, `⟨ΔWΔZ⟩ = τ²/2`, together with the companion integral
  `∫dW∫ds = τΔW - ΔZ` (`Gardiner.SDE.multipleIntegral_moments`).  Erratum: (10.1.11) repeats
  (10.1.10); the intended integral is `∫dW(s)∫ds'`.
* **Error recursions (10.1.22)–(10.1.29) made rigorous.**  `Gardiner.SDE.strong_error_bound`
  turns the recursion inequality (10.1.23) into the closed bound (10.1.24) and the exponential
  bound (10.1.25) (with the exponent `(2A + B + A²τ)T`, which the text rounds to `(2A + B)T`);
  `Gardiner.SDE.mean_error_bound` does the same for (10.1.28) → (10.1.29).
* **Erratum (10.1.42).**  Squaring (10.1.40) gives the cross term
  `2[(1 + a'τ)Pτ² + b'Uτ² + c'Vτ³]⟨eₙ⟩`; the printed formula omits `(1 + a'τ)Pτ²`
  (`Gardiner.SDE.milstein_error_second_moment`, `Gardiner.SDE.eq_10_1_42_printed_wrong`).
  The conclusion `⟨eₙ²⟩ = O(τ²)` is unaffected since `⟨eₙ⟩ = O(τ)`.
* **Implicit schemes (10.4.1)–(10.4.9).**  If `z = y_{n+1} - yₙ` solves the implicit equation
  `z = A(y + θz)τ + b(y + θz)ΔW` (the text's `ε` is our `θ`), then
  `|z - (Aτ + bΔW + θbb'ΔW²)| ≤ 2K₁K₀h|τ| + (½K₂K₀² + K₁²K₀)h³`, `h = |τ| + |ΔW|`
  (`Gardiner.SDE.implicit_step_expansion`); this is (10.4.9).  With `A = a - θbb'` (10.4.10) the
  truncated map is Euler plus `θbb'(ΔW² - τ)`, and for `θ = ½` it is exactly Milstein
  (`Gardiner.SDE.thetaTrunc_half_eq_milstein`).
* **Consistency (§10.3.1) as properties of the one-step maps.**  A map `Φ(y, ΔW)` driven by
  `ΔW ~ N(0, τ)` is consistent with `dx = a dt + b dW` at `y` if its first two increment moments
  are `a(y)τ + O(τ²)` and `b(y)²τ + O(τ²)` (`Gardiner.SDE.IsConsistentAt`).  Euler and
  Milstein are consistent (`Gardiner.SDE.euler_consistent`, `Gardiner.SDE.milstein_consistent`);
  the truncated θ-scheme with drift `A` is consistent iff `A + θbb' = a` at `y`
  (`Gardiner.SDE.thetaTrunc_consistent_iff`), so the naive implicit/semi-implicit scheme
  (`A = a`, `θ > 0`) is inconsistent unless `bb' = 0` (`Gardiner.SDE.naive_implicit_inconsistent`).
-/
import SHSLib.Gardiner.SDE.SchemeMoments
import SHSLib.Gardiner.Approx.Calculus

open MeasureTheory ProbabilityTheory Finset Real
open scoped NNReal

noncomputable section

namespace Gardiner.SDE

/-! ### Operators and one-step maps -/

/-- (10.1.4) `L₀f = af' + ½b²f''`. -/
def L0 (a b f : ℝ → ℝ) (x : ℝ) : ℝ := a x * deriv f x + 1 / 2 * b x ^ 2 * deriv (deriv f) x
/-- (10.1.5) `L₁f = bf'`. -/
def L1 (b f : ℝ → ℝ) (x : ℝ) : ℝ := b x * deriv f x
/-- (10.1.33) `c = ½L₁b = ½bb'`. -/
def cMil (b : ℝ → ℝ) (x : ℝ) : ℝ := 1 / 2 * L1 b b x

/-- The Euler map (10.1.15). -/
def eulerStep (a b : ℝ → ℝ) (τ y dw : ℝ) : ℝ := y + a y * τ + b y * dw
/-- The Milstein map (10.1.32). -/
def milsteinStep (a b : ℝ → ℝ) (τ y dw : ℝ) : ℝ := y + a y * τ + b y * dw + cMil b y * (dw ^ 2 - τ)

/-- (10.1.31) = (10.1.32). -/
theorem milstein_31_eq_32 (a b : ℝ → ℝ) (τ y dw : ℝ) :
    milsteinStep a b τ y dw = y + (a y - 1 / 2 * b y * deriv b y) * τ + b y * dw +
      1 / 2 * b y * deriv b y * dw ^ 2 := by
  simp only [milsteinStep, cMil, L1]; ring

/-- **Erratum (10.1.18)**: the printed coefficient `L₀b` differs from the correct `L₁b`:
for `a = 0`, `b(x) = x` one has `L₀b = 0` but `L₁b(x) = x`. -/
theorem eq_10_1_18_printed_wrong : ¬ ∀ (a b : ℝ → ℝ) (x : ℝ), L0 a b b x = L1 b b x := by
  intro h
  have := h (fun _ => 0) id 1
  simp [L0, L1] at this

/-! ### The double stochastic integral (10.1.9), Itô-free -/

/-- Partial sums `Sᵢ = Σ_{j<i} δⱼ`. -/
def psum (δ : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range i, δ j

/-- Left-point (Itô) sum: `Σ_{i<n} Sᵢδᵢ = ½(S_n² - Σ_{i<n} δᵢ²)`, for any increments. -/
theorem ito_sum_identity (δ : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, psum δ i * δ i = 1 / 2 * (psum δ n ^ 2 - ∑ i ∈ range n, δ i ^ 2) := by
  induction n with
  | zero => simp [psum]
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [psum, sum_range_succ]; ring

/-- Midpoint (Stratonovich) sum: `Σ_{i<n} ½(Sᵢ + S_{i+1})δᵢ = ½S_n²`, for any increments. -/
theorem strat_sum_identity (δ : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (psum δ i + psum δ (i + 1)) / 2 * δ i = 1 / 2 * psum δ n ^ 2 := by
  induction n with
  | zero => simp [psum]
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [psum, sum_range_succ]; ring

/-- (10.1.9) given the quadratic variation of the increments: if `Σδᵢ² = t - t₀` then the
left-point sum is `½[(W(t) - W(t₀))² - (t - t₀)]`. -/
theorem ito_sum_of_qv (δ : ℕ → ℝ) (n : ℕ) {s : ℝ} (hqv : ∑ i ∈ range n, δ i ^ 2 = s) :
    ∑ i ∈ range n, psum δ i * δ i = 1 / 2 * (psum δ n ^ 2 - s) := by
  rw [ito_sum_identity, hqv]

/-! ### Multiple integrals as a given law (10.1.10)–(10.1.12) -/

section MultipleIntegrals

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Moments of the realisation `ΔW = √τ ξ`, `ΔZ = ½τ^{3/2}(ξ + η/√3)` of the pair
`(ΔW, ∫ds∫dW)`, with `ξ, η` uncorrelated of unit variance and mean zero, and of the companion
integral `∫dW∫ds = τΔW - ΔZ`. -/
theorem multipleIntegral_moments {ξ η : Ω → ℝ} (τ : ℝ) (hτ : 0 ≤ τ)
    (hξ : Integrable ξ P) (hη : Integrable η P) (hξ2 : Integrable (fun ω => ξ ω ^ 2) P)
    (hη2 : Integrable (fun ω => η ω ^ 2) P) (hξη : Integrable (fun ω => ξ ω * η ω) P)
    (m1 : ∫ ω, ξ ω ∂P = 0) (m2 : ∫ ω, η ω ∂P = 0) (v1 : ∫ ω, ξ ω ^ 2 ∂P = 1)
    (v2 : ∫ ω, η ω ^ 2 ∂P = 1) (c : ∫ ω, ξ ω * η ω ∂P = 0) :
    let dW := fun ω => √τ * ξ ω
    let dZ := fun ω => 1 / 2 * τ * √τ * (ξ ω + η ω / √3)
    ∫ ω, dZ ω ∂P = 0 ∧ ∫ ω, dW ω * dZ ω ∂P = τ ^ 2 / 2 ∧ ∫ ω, dZ ω ^ 2 ∂P = τ ^ 3 / 3 ∧
      ∫ ω, dW ω * (τ * dW ω - dZ ω) ∂P = τ ^ 2 / 2 ∧
      ∫ ω, (τ * dW ω - dZ ω) ^ 2 ∂P = τ ^ 3 / 3 := by
  intro dW dZ
  have hs : √τ ^ 2 = τ := sq_sqrt hτ
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  -- all integrands are combinations `αξ + βη` or `αξ² + βξη + γη²`
  have lin : ∀ α β : ℝ, ∫ ω, (α * ξ ω + β * η ω) ∂P = 0 := by
    intro α β
    rw [integral_add (hξ.const_mul α) (hη.const_mul β), integral_const_mul, integral_const_mul,
      m1, m2]; ring
  have quad : ∀ α β γ : ℝ, ∫ ω, (α * ξ ω ^ 2 + β * (ξ ω * η ω) + γ * η ω ^ 2) ∂P = α + γ := by
    intro α β γ
    have h1 : Integrable (fun ω => α * ξ ω ^ 2 + β * (ξ ω * η ω)) P :=
      (hξ2.const_mul α).add (hξη.const_mul β)
    rw [integral_add h1 (hη2.const_mul γ),
      integral_add (hξ2.const_mul α) (hξη.const_mul β), integral_const_mul, integral_const_mul,
      integral_const_mul, v1, v2, c]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := lin (1 / 2 * τ * √τ) (1 / 2 * τ * √τ / √3)
    rw [← this]; congr 1; funext ω; simp only [dZ]; ring
  · have := quad (1 / 2 * τ * √τ ^ 2) (1 / 2 * τ * √τ ^ 2 / √3) 0
    rw [show (fun ω => dW ω * dZ ω) = fun ω => 1 / 2 * τ * √τ ^ 2 * ξ ω ^ 2 +
      1 / 2 * τ * √τ ^ 2 / √3 * (ξ ω * η ω) + 0 * η ω ^ 2 by funext ω; simp only [dW, dZ]; ring,
      this, hs]; ring
  · have := quad (1 / 4 * τ ^ 2 * √τ ^ 2) (1 / 2 * τ ^ 2 * √τ ^ 2 / √3)
      (1 / 4 * τ ^ 2 * √τ ^ 2 / √3 ^ 2)
    rw [show (fun ω => dZ ω ^ 2) = fun ω => 1 / 4 * τ ^ 2 * √τ ^ 2 * ξ ω ^ 2 +
      1 / 2 * τ ^ 2 * √τ ^ 2 / √3 * (ξ ω * η ω) + 1 / 4 * τ ^ 2 * √τ ^ 2 / √3 ^ 2 * η ω ^ 2 by
        funext ω; simp only [dZ]; field_simp; ring, this, hs, h3]; ring
  · have := quad (1 / 2 * τ * √τ ^ 2) (-(1 / 2 * τ * √τ ^ 2 / √3)) 0
    rw [show (fun ω => dW ω * (τ * dW ω - dZ ω)) = fun ω => 1 / 2 * τ * √τ ^ 2 * ξ ω ^ 2 +
      -(1 / 2 * τ * √τ ^ 2 / √3) * (ξ ω * η ω) + 0 * η ω ^ 2 by
        funext ω; simp only [dW, dZ]; ring, this, hs]; ring
  · have := quad (1 / 4 * τ ^ 2 * √τ ^ 2) (-(1 / 2 * τ ^ 2 * √τ ^ 2 / √3))
      (1 / 4 * τ ^ 2 * √τ ^ 2 / √3 ^ 2)
    rw [show (fun ω => (τ * dW ω - dZ ω) ^ 2) = fun ω => 1 / 4 * τ ^ 2 * √τ ^ 2 * ξ ω ^ 2 +
      -(1 / 2 * τ ^ 2 * √τ ^ 2 / √3) * (ξ ω * η ω) + 1 / 4 * τ ^ 2 * √τ ^ 2 / √3 ^ 2 * η ω ^ 2 by
        funext ω; simp only [dW, dZ]; field_simp; ring, this, hs, h3]; ring

end MultipleIntegrals

/-! ### Error recursions (10.1.22)–(10.1.29) -/

/-- A recursion inequality `v_{n+1} ≤ r vₙ + q`, `v₀ = 0`, `r ≥ 0`, gives `v_N ≤ (Σ_{k<N} rᵏ) q`. -/
lemma geom_recursion {r q : ℝ} (hr : 0 ≤ r) (v : ℕ → ℝ) (h0 : v 0 = 0)
    (h : ∀ n, v (n + 1) ≤ r * v n + q) (N : ℕ) : v N ≤ (∑ k ∈ range N, r ^ k) * q := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    calc v (N + 1) ≤ r * v N + q := h N
      _ ≤ r * ((∑ k ∈ range N, r ^ k) * q) + q := by gcongr
      _ = (∑ k ∈ range (N + 1), r ^ k) * q := by
          rw [sum_range_succ']; simp only [pow_succ', ← mul_sum, pow_zero]; ring

/-- `Σ_{k<N} (1 + κτ)ᵏ ≤ (e^{κNτ} - 1)/(cτ)` for `0 < c ≤ κ`, `τ > 0`. -/
lemma geom_sum_le_exp {c κ τ : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hcκ : c ≤ κ) (N : ℕ) :
    ∑ k ∈ range N, (1 + κ * τ) ^ k ≤ (Real.exp (κ * (N * τ)) - 1) / (c * τ) := by
  have hκτ : 0 < κ * τ := by nlinarith
  rw [geom_sum_eq (by linarith), add_sub_cancel_left]
  have h1 : (1 + κ * τ) ^ N ≤ Real.exp (κ * (N * τ)) := by
    calc (1 + κ * τ) ^ N ≤ Real.exp (κ * τ) ^ N := by
          gcongr; linarith [Real.add_one_le_exp (κ * τ)]
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : 0 ≤ (1 + κ * τ) ^ N - 1 := by
    have := one_le_pow₀ (n := N) (by linarith : (1 : ℝ) ≤ 1 + κ * τ); linarith
  calc ((1 + κ * τ) ^ N - 1) / (κ * τ) ≤ ((1 + κ * τ) ^ N - 1) / (c * τ) :=
        div_le_div_of_nonneg_left h2 (by positivity) (by nlinarith)
    _ ≤ _ := by gcongr

/-- **(10.1.22)–(10.1.25), rigorous form.**  If the mean-square error obeys (10.1.23),
`v_{n+1} ≤ [(1 + Aτ)² + Bτ] vₙ + Cτ²`, `v₀ = 0`, with `2A + B > 0`, then (10.1.24)
`v_N ≤ (ρᴺ - 1)/(ρ - 1) Cτ²`, `ρ = (1 + Aτ)² + Bτ`, and (10.1.25)
`v_N ≤ (e^{(2A+B+A²τ)T} - 1)/(2A + B) · Cτ`, `T = Nτ`.  Hence `√v_N = O(τ^{1/2})` (10.1.26). -/
theorem strong_error_bound {A B C τ : ℝ} (hτ : 0 < τ) (hAB : 0 < 2 * A + B) (hC : 0 ≤ C)
    (v : ℕ → ℝ) (h0 : v 0 = 0)
    (h : ∀ n, v (n + 1) ≤ ((1 + A * τ) ^ 2 + B * τ) * v n + C * τ ^ 2) (N : ℕ) :
    v N ≤ (((1 + A * τ) ^ 2 + B * τ) ^ N - 1) / (((1 + A * τ) ^ 2 + B * τ) - 1) * (C * τ ^ 2) ∧
    v N ≤ (Real.exp ((2 * A + B + A ^ 2 * τ) * (N * τ)) - 1) / (2 * A + B) * (C * τ) := by
  have hρ : (1 + A * τ) ^ 2 + B * τ = 1 + (2 * A + B + A ^ 2 * τ) * τ := by ring
  have hκ : 2 * A + B ≤ 2 * A + B + A ^ 2 * τ := by nlinarith [sq_nonneg A]
  have hr : 0 ≤ (1 + A * τ) ^ 2 + B * τ := by rw [hρ]; nlinarith
  have hg := geom_recursion hr v h0 h N
  have hne : (1 + A * τ) ^ 2 + B * τ ≠ 1 := by rw [hρ]; nlinarith
  constructor
  · rwa [geom_sum_eq hne] at hg
  · have := geom_sum_le_exp hτ hAB hκ N
    rw [← hρ] at this
    calc v N ≤ (∑ k ∈ range N, ((1 + A * τ) ^ 2 + B * τ) ^ k) * (C * τ ^ 2) := hg
      _ ≤ (Real.exp ((2 * A + B + A ^ 2 * τ) * (N * τ)) - 1) / ((2 * A + B) * τ) * (C * τ ^ 2) := by
          gcongr
      _ = _ := by field_simp

/-- **(10.1.28)–(10.1.29), rigorous form.**  If `|m_{n+1}| ≤ (1 + Dτ)|mₙ| + Pτ²`, `m₀ = 0`,
`D > 0`, then `|m_N| ≤ (e^{DT} - 1)/D · Pτ`, `T = Nτ`: the mean error is `O(τ)`. -/
theorem mean_error_bound {D P τ : ℝ} (hτ : 0 < τ) (hD : 0 < D) (hP : 0 ≤ P) (m : ℕ → ℝ)
    (h0 : m 0 = 0) (h : ∀ n, |m (n + 1)| ≤ (1 + D * τ) * |m n| + P * τ ^ 2) (N : ℕ) :
    |m N| ≤ (Real.exp (D * (N * τ)) - 1) / D * (P * τ) := by
  have hg := geom_recursion (v := fun n => |m n|) (by nlinarith) (by simp [h0]) h N
  have := geom_sum_le_exp hτ hD le_rfl N
  calc |m N| ≤ (∑ k ∈ range N, (1 + D * τ) ^ k) * (P * τ ^ 2) := hg
    _ ≤ (Real.exp (D * (N * τ)) - 1) / (D * τ) * (P * τ ^ 2) := by gcongr
    _ = _ := by field_simp

/-! ### The Milstein error recursion (10.1.40)–(10.1.42) -/

section MilsteinError

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Second moment of the Milstein error recursion (10.1.40), corrected (10.1.42).**
Let `e_{n+1} = G eₙ + Rₙ`, `G = 1 + a'τ + b'ΔW + c'(ΔW² - τ)`, `ΔW ~ N(0, τ)`, and assume the
factorisations coming from the independence of `eₙ` and `(ΔW, Rₙ)`:
`⟨G²eₙ²⟩ = ⟨G²⟩⟨eₙ²⟩`, `⟨GeₙRₙ⟩ = ⟨eₙ⟩⟨GRₙ⟩`, together with (10.1.36)–(10.1.39).  Then
`⟨e²_{n+1}⟩ = [(1 + a'τ)² + b'²τ + 2c'²τ²]⟨eₙ²⟩ + 2[(1 + a'τ)Pτ² + b'Uτ² + c'Vτ³]⟨eₙ⟩ + Qτ³`. -/
theorem milstein_error_second_moment {e R z : Ω → ℝ} {τ : ℝ≥0} {a b c Pc U V Q : ℝ}
    (hz : Measurable z) (hlaw : P.map z = gaussianReal 0 τ)
    (hi1 : Integrable (fun ω => (1 + a * τ + b * z ω + c * (z ω ^ 2 - τ)) ^ 2 * e ω ^ 2) P)
    (hi2 : Integrable (fun ω => (1 + a * τ + b * z ω + c * (z ω ^ 2 - τ)) * e ω * R ω) P)
    (hi3 : Integrable (fun ω => R ω ^ 2) P) (hR : Integrable R P)
    (hzR : Integrable (fun ω => z ω * R ω) P) (hz2R : Integrable (fun ω => (z ω ^ 2 - τ) * R ω) P)
    (hf1 : ∫ ω, (1 + a * τ + b * z ω + c * (z ω ^ 2 - τ)) ^ 2 * e ω ^ 2 ∂P =
      (∫ ω, (1 + a * τ + b * z ω + c * (z ω ^ 2 - τ)) ^ 2 ∂P) * ∫ ω, e ω ^ 2 ∂P)
    (hf2 : ∫ ω, (1 + a * τ + b * z ω + c * (z ω ^ 2 - τ)) * e ω * R ω ∂P =
      (∫ ω, e ω ∂P) * ∫ ω, (1 + a * τ + b * z ω + c * (z ω ^ 2 - τ)) * R ω ∂P)
    (hP : ∫ ω, R ω ∂P = Pc * τ ^ 2) (hU : ∫ ω, z ω * R ω ∂P = U * τ ^ 2)
    (hV : ∫ ω, (z ω ^ 2 - τ) * R ω ∂P = V * τ ^ 3) (hQ : ∫ ω, R ω ^ 2 ∂P = Q * τ ^ 3) :
    ∫ ω, ((1 + a * τ + b * z ω + c * (z ω ^ 2 - τ)) * e ω + R ω) ^ 2 ∂P =
      ((1 + a * τ) ^ 2 + b ^ 2 * τ + 2 * c ^ 2 * τ ^ 2) * ∫ ω, e ω ^ 2 ∂P +
      2 * ((1 + a * τ) * Pc * τ ^ 2 + b * U * τ ^ 2 + c * V * τ ^ 3) * ∫ ω, e ω ∂P +
      Q * τ ^ 3 := by
  set G := fun ω => 1 + a * τ + b * z ω + c * (z ω ^ 2 - τ) with hG
  -- `⟨G²⟩` from the Gaussian law of `ΔW`
  have hG2 : ∫ ω, G ω ^ 2 ∂P = (1 + a * τ) ^ 2 + b ^ 2 * τ + 2 * c ^ 2 * τ ^ 2 := by
    have := integral_comp_gauss hz hlaw
      (f := fun x => (⟨1 + a * τ - c * τ, b, c, 0, 0⟩ : LinStep).G x ^ 2)
      ((LinStep.continuous_G _).pow 2)
    rw [show (fun ω => G ω ^ 2) = fun ω => (⟨1 + a * τ - c * τ, b, c, 0, 0⟩ : LinStep).G (z ω) ^ 2
      by funext ω; simp only [hG, LinStep.G]; ring, this, LinStep.integral_G2]
    simp only [LinStep.EG2]; ring
  have hGR : ∫ ω, G ω * R ω ∂P = (1 + a * τ) * Pc * τ ^ 2 + b * U * τ ^ 2 + c * V * τ ^ 3 := by
    rw [show (fun ω => G ω * R ω) = fun ω => (1 + a * τ) * R ω + b * (z ω * R ω) +
      c * ((z ω ^ 2 - τ) * R ω) by funext ω; simp only [hG]; ring]
    have i1 : Integrable (fun ω => (1 + a * τ) * R ω + b * (z ω * R ω)) P :=
      (hR.const_mul _).add (hzR.const_mul _)
    rw [integral_add i1 (hz2R.const_mul _),
      integral_add (hR.const_mul _) (hzR.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, hP, hU, hV]; ring
  rw [show (fun ω => (G ω * e ω + R ω) ^ 2) = fun ω => G ω ^ 2 * e ω ^ 2 +
    2 * (G ω * e ω * R ω) + R ω ^ 2 by funext ω; ring]
  have i2 : Integrable (fun ω => G ω ^ 2 * e ω ^ 2 + 2 * (G ω * e ω * R ω)) P :=
    hi1.add (hi2.const_mul 2)
  rw [integral_add i2 hi3, integral_add hi1 (hi2.const_mul 2),
    integral_const_mul, hf1, hf2, hG2, hGR, hQ]
  ring

/-- **Erratum (10.1.42).**  The printed recursion omits the cross term `2(1 + a'τ)Pτ²⟨eₙ⟩`: the
correct right-hand side minus the printed one equals that term, which is nonzero whenever
`(1 + a'τ)P⟨eₙ⟩ ≠ 0`, `τ ≠ 0`. -/
theorem eq_10_1_42_printed_wrong (a b c τ Pc U V Q m m2 : ℝ) :
    (((1 + a * τ) ^ 2 + b ^ 2 * τ + 2 * c ^ 2 * τ ^ 2) * m2 +
      2 * ((1 + a * τ) * Pc * τ ^ 2 + b * U * τ ^ 2 + c * V * τ ^ 3) * m + Q * τ ^ 3) -
    (((1 + a * τ) ^ 2 + b ^ 2 * τ + 2 * c ^ 2 * τ ^ 2) * m2 +
      2 * (b * U * τ ^ 2 + c * V * τ ^ 3) * m + Q * τ ^ 3) =
    2 * (1 + a * τ) * Pc * τ ^ 2 * m := by ring

end MilsteinError

/-! ### Implicit schemes (10.4.1)–(10.4.10) -/

/-- **Expansion of the implicit step (10.4.5)–(10.4.9).**  Let `A, b` have derivatives `A₁, b₁`
and `b₁` a derivative `b₂`, with `|A|, |b| ≤ K₀`, `|A₁|, |b₁| ≤ K₁`, `|b₂| ≤ K₂`, and
`0 ≤ θ ≤ 1`.  If `z = y_{n+1} - yₙ` solves `z = A(y + θz)τ + b(y + θz)ΔW` ((10.4.1)–(10.4.4)), then
`|z - (A(y)τ + b(y)ΔW + θ b(y)b'(y)ΔW²)| ≤ 2K₁K₀ h|τ| + (½K₂K₀² + K₁²K₀) h³`,
`h = |τ| + |ΔW|`.  Since `|τ| ≤ h²` for `h ≤ 1`, the right-hand side is `O(h³)`. -/
theorem implicit_step_expansion {A A1 b b1 b2 : ℝ → ℝ} (hA : ∀ x, HasDerivAt A (A1 x) x)
    (hb : ∀ x, HasDerivAt b (b1 x) x) (hb1 : ∀ x, HasDerivAt b1 (b2 x) x) {K0 K1 K2 : ℝ}
    (hA0 : ∀ x, |A x| ≤ K0) (hb0 : ∀ x, |b x| ≤ K0) (hA1 : ∀ x, |A1 x| ≤ K1)
    (hb1' : ∀ x, |b1 x| ≤ K1) (hb2 : ∀ x, |b2 x| ≤ K2) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {y τ dw z : ℝ} (hz : z = A (y + θ * z) * τ + b (y + θ * z) * dw) :
    |z - (A y * τ + b y * dw + θ * b y * b1 y * dw ^ 2)| ≤
      2 * K1 * K0 * (|τ| + |dw|) * |τ| + (K2 * K0 ^ 2 / 2 + K1 ^ 2 * K0) * (|τ| + |dw|) ^ 3 := by
  set h := |τ| + |dw| with hh
  have hK0 : 0 ≤ K0 := (abs_nonneg _).trans (hA0 0)
  have hK1 : 0 ≤ K1 := (abs_nonneg _).trans (hA1 0)
  have hK2 : 0 ≤ K2 := (abs_nonneg _).trans (hb2 0)
  have hτh : |τ| ≤ h := by simp [hh]
  have hwh : |dw| ≤ h := by simp [hh]
  have h0 : 0 ≤ h := by positivity
  -- `|z| ≤ K₀h`
  have hzb : |z| ≤ K0 * h := by
    rw [hz]
    calc |A (y + θ * z) * τ + b (y + θ * z) * dw| ≤ K0 * |τ| + K0 * |dw| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
          exacts [hA0 _, hb0 _]
      _ = K0 * h := by ring
  have hθz : |θ * z| ≤ K0 * h := by
    rw [abs_mul, abs_of_nonneg hθ0]
    calc θ * |z| ≤ 1 * |z| := by gcongr
      _ ≤ _ := by linarith
  -- first-order Taylor bounds
  have tA := taylor_tower_bound 0 (fun k => if k = 0 then A else A1) y (θ * z) K1
    (fun k hk x => by interval_cases k; simpa using hA x) (fun t _ => by simpa using hA1 _)
  have tb := taylor_tower_bound 0 (fun k => if k = 0 then b else b1) y (θ * z) K1
    (fun k hk x => by interval_cases k; simpa using hb x) (fun t _ => by simpa using hb1' _)
  have tb2 := taylor_tower_bound 1 (fun k => if k = 0 then b else if k = 1 then b1 else b2) y
    (θ * z) K2 (fun k hk x => by
      interval_cases k
      · simpa using hb x
      · simpa using hb1 x) (fun t _ => by simpa using hb2 _)
  simp [taylorTower, Finset.sum_range_succ] at tA tb tb2
  -- tA : |A (y + θz) - A y| ≤ K1 |θz|, tb2 : |b(y+θz) - b y - b1 y θz| ≤ K2 |θz|²/2
  have hθz' : |θ| * |z| ≤ K0 * h := by rw [← abs_mul]; exact hθz
  have eA : |A (y + θ * z) - A y| ≤ K1 * (K0 * h) := by
    calc _ ≤ K1 * (|θ| * |z|) := tA
      _ ≤ _ := by gcongr
  have eb : |b (y + θ * z) - b y| ≤ K1 * (K0 * h) := by
    calc _ ≤ K1 * (|θ| * |z|) := tb
      _ ≤ _ := by gcongr
  have eb2 : |b (y + θ * z) - (b y + b1 y * (θ * z))| ≤ K2 * (K0 * h) ^ 2 / 2 := by
    calc _ ≤ K2 * (|θ| * |z|) ^ 2 / 2 := tb2
      _ ≤ _ := by gcongr
  -- `|z - A y τ - b y ΔW| ≤ K₁K₀h²` and `|z - b y ΔW| ≤ K₁K₀h² + K₀|τ|`
  have e1 : |z - A y * τ - b y * dw| ≤ K1 * K0 * h ^ 2 := by
    have : z - A y * τ - b y * dw = (A (y + θ * z) - A y) * τ + (b (y + θ * z) - b y) * dw := by
      linear_combination hz
    rw [this]
    calc _ ≤ K1 * (K0 * h) * |τ| + K1 * (K0 * h) * |dw| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
      _ = K1 * K0 * h ^ 2 := by rw [hh]; ring
  have e2 : |z - b y * dw| ≤ K1 * K0 * h ^ 2 + K0 * |τ| := by
    have : z - b y * dw = (z - A y * τ - b y * dw) + A y * τ := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add e1 ?_)
    rw [abs_mul]; gcongr; exact hA0 _
  -- assemble
  have key : z - (A y * τ + b y * dw + θ * b y * b1 y * dw ^ 2) =
      (A (y + θ * z) - A y) * τ + (b (y + θ * z) - (b y + b1 y * (θ * z))) * dw +
      θ * b1 y * (z - b y * dw) * dw := by
    linear_combination hz
  rw [key]
  have t3 : |θ * b1 y * (z - b y * dw) * dw| ≤ K1 * (K1 * K0 * h ^ 2 + K0 * |τ|) * h := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hθ0]
    have := hb1' y
    calc θ * |b1 y| * |z - b y * dw| * |dw| ≤ 1 * K1 * (K1 * K0 * h ^ 2 + K0 * |τ|) * h := by
          gcongr
      _ = _ := by ring
  calc _ ≤ |(A (y + θ * z) - A y) * τ| + |(b (y + θ * z) - (b y + b1 y * (θ * z))) * dw| +
        |θ * b1 y * (z - b y * dw) * dw| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K1 * (K0 * h) * |τ| + K2 * (K0 * h) ^ 2 / 2 * h +
        K1 * (K1 * K0 * h ^ 2 + K0 * |τ|) * h := by
        gcongr
        · rw [abs_mul]; gcongr
        · rw [abs_mul]; gcongr
    _ = _ := by ring

/-- The truncated θ-scheme (10.4.9) with drift `A`:
`y + (A + θbb')τ + θbb'(ΔW² - τ) + bΔW`. -/
def thetaTrunc (A b b1 : ℝ → ℝ) (θ τ y dw : ℝ) : ℝ :=
  y + (A y + θ * b y * b1 y) * τ + θ * b y * b1 y * (dw ^ 2 - τ) + b y * dw

/-- The truncated map is the second-order expansion of the implicit step. -/
theorem thetaTrunc_eq (A b b1 : ℝ → ℝ) (θ τ y dw : ℝ) :
    thetaTrunc A b b1 θ τ y dw = y + (A y * τ + b y * dw + θ * b y * b1 y * dw ^ 2) := by
  unfold thetaTrunc; ring

/-- (10.4.10) With `A = a - θbb'`, the truncated θ-scheme is Euler plus `θbb'(ΔW² - τ)`. -/
theorem thetaTrunc_corrected (a b : ℝ → ℝ) (θ τ y dw : ℝ) :
    thetaTrunc (fun x => a x - θ * b x * deriv b x) b (deriv b) θ τ y dw =
      eulerStep a b τ y dw + θ * b y * deriv b y * (dw ^ 2 - τ) := by
  unfold thetaTrunc eulerStep; ring

/-- (10.4.10 a)) For `θ = ½` the corrected truncated scheme *is* the Milstein map. -/
theorem thetaTrunc_half_eq_milstein (a b : ℝ → ℝ) (τ y dw : ℝ) :
    thetaTrunc (fun x => a x - 1 / 2 * b x * deriv b x) b (deriv b) (1 / 2) τ y dw =
      milsteinStep a b τ y dw := by
  unfold thetaTrunc milsteinStep cMil L1; ring

/-! ### Consistency (§10.3.1) as properties of one-step maps -/

/-- The mean increment `⟨Φ_τ(y, ΔW) - y⟩` of a one-step map `Φ τ y ΔW`, `ΔW ~ N(0, τ)`. -/
def meanIncr (Φ : ℝ → ℝ → ℝ → ℝ) (y : ℝ) (τ : ℝ≥0) : ℝ := ∫ z, (Φ τ y z - y) ∂(gaussianReal 0 τ)
/-- The mean-square increment `⟨(Φ(y, ΔW) - y)²⟩`. -/
def sqIncr (Φ : ℝ → ℝ → ℝ → ℝ) (y : ℝ) (τ : ℝ≥0) : ℝ :=
  ∫ z, (Φ τ y z - y) ^ 2 ∂(gaussianReal 0 τ)

/-- **Consistency** at `y` of a one-step map `Φ` with `dx = a dt + b dW`: for `0 < τ ≤ 1`,
`⟨Φ - y⟩ = a(y)τ + O(τ²)` and `⟨(Φ - y)²⟩ = b(y)²τ + O(τ²)`. -/
def IsConsistentAt (Φ : ℝ → ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (y : ℝ) : Prop :=
  ∃ C : ℝ, ∀ τ : ℝ≥0, (τ : ℝ) ≤ 1 →
    |meanIncr Φ y τ - a y * τ| ≤ C * (τ : ℝ) ^ 2 ∧ |sqIncr Φ y τ - b y ^ 2 * τ| ≤ C * (τ : ℝ) ^ 2

/-- Increments of polynomial maps `Φ_τ(y, z) - y = c₀ + c₁z + c₂z²`. -/
lemma poly_incr {Φ : ℝ → ℝ → ℝ → ℝ} {y : ℝ} {τ : ℝ≥0} {c0 c1 c2 : ℝ}
    (hΦ : ∀ z, Φ τ y z - y = c0 + c1 * z + c2 * z ^ 2) :
    meanIncr Φ y τ = c0 + c2 * τ ∧
      sqIncr Φ y τ = c0 ^ 2 + (c1 ^ 2 + 2 * c0 * c2) * τ + 3 * c2 ^ 2 * τ ^ 2 := by
  have e : (fun z => Φ τ y z - y) = (⟨c0, c1, c2, 0, 0⟩ : LinStep).G := by
    funext z; rw [hΦ]; rfl
  constructor
  · rw [meanIncr, e, LinStep.integral_G]; rfl
  · rw [sqIncr, show (fun z => (Φ τ y z - y) ^ 2) = fun z => (⟨c0, c1, c2, 0, 0⟩ : LinStep).G z ^ 2
      by rw [← e], LinStep.integral_G2]; rfl

/-- Increment moments of the truncated θ-scheme: mean `(A + θbb')τ`. -/
theorem thetaTrunc_incr (A b b1 : ℝ → ℝ) (θ y : ℝ) (τ : ℝ≥0) :
    meanIncr (thetaTrunc A b b1 θ) y τ = (A y + θ * b y * b1 y) * τ ∧
    sqIncr (thetaTrunc A b b1 θ) y τ = b y ^ 2 * τ + (A y ^ 2 + 2 * A y * θ * b y * b1 y +
      3 * (θ * b y * b1 y) ^ 2) * τ ^ 2 := by
  obtain ⟨h1, h2⟩ := poly_incr (Φ := thetaTrunc A b b1 θ) (y := y) (τ := τ) (c0 := A y * τ)
    (c1 := b y) (c2 := θ * b y * b1 y) (fun z => by unfold thetaTrunc; ring)
  exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩

/-- A map whose increment moments are `aτ + pτ²` and `b²τ + qτ²` is consistent. -/
lemma consistent_of_moments {Φ : ℝ → ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {y : ℝ} (p q : ℝ)
    (hm : ∀ τ : ℝ≥0, meanIncr Φ y τ = a y * τ + p * τ ^ 2)
    (hs : ∀ τ : ℝ≥0, sqIncr Φ y τ = b y ^ 2 * τ + q * τ ^ 2) : IsConsistentAt Φ a b y := by
  refine ⟨|p| + |q|, fun τ _ => ⟨?_, ?_⟩⟩
  · rw [hm, add_sub_cancel_left, abs_mul, abs_of_nonneg (sq_nonneg (τ : ℝ))]
    gcongr; linarith [abs_nonneg q]
  · rw [hs, add_sub_cancel_left, abs_mul, abs_of_nonneg (sq_nonneg (τ : ℝ))]
    gcongr; linarith [abs_nonneg p]

/-- The Euler map (10.1.15) is consistent: increment moments `aτ` and `b²τ + a²τ²`. -/
theorem euler_consistent (a b : ℝ → ℝ) (y : ℝ) : IsConsistentAt (eulerStep a b) a b y := by
  refine consistent_of_moments 0 (a y ^ 2) (fun τ => ?_) (fun τ => ?_) <;>
  · obtain ⟨h1, h2⟩ := poly_incr (Φ := eulerStep a b) (y := y) (τ := τ) (c0 := a y * τ)
      (c1 := b y) (c2 := 0) (fun z => by unfold eulerStep; ring)
    first | (rw [h1]; ring) | (rw [h2]; ring)

/-- The Milstein map (10.1.32) is consistent: increment moments `aτ` and `b²τ + (a² + 2c²)τ²`. -/
theorem milstein_consistent (a b : ℝ → ℝ) (y : ℝ) : IsConsistentAt (milsteinStep a b) a b y := by
  refine consistent_of_moments 0 (a y ^ 2 + 2 * cMil b y ^ 2) (fun τ => ?_) (fun τ => ?_) <;>
  · obtain ⟨h1, h2⟩ := poly_incr (Φ := milsteinStep a b) (y := y) (τ := τ)
      (c0 := a y * τ - cMil b y * τ) (c1 := b y) (c2 := cMil b y)
      (fun z => by unfold milsteinStep; ring)
    first | (rw [h1]; ring) | (rw [h2]; ring)

/-- **Consistency condition (10.4.10).**  The truncated θ-scheme with drift `A` is consistent with
`dx = a dt + b dW` at `y` iff `A(y) + θb(y)b'(y) = a(y)`. -/
theorem thetaTrunc_consistent_iff (A a b b1 : ℝ → ℝ) (θ y : ℝ) :
    IsConsistentAt (thetaTrunc A b b1 θ) a b y ↔ A y + θ * b y * b1 y = a y := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    have hd : 0 < |A y + θ * b y * b1 y - a y| := abs_pos.mpr (sub_ne_zero.mpr hne)
    -- `|d|τ ≤ Cτ²` for all small `τ`; take `τ = min 1 (|d|/(2(|C|+1)))`
    set d := |A y + θ * b y * b1 y - a y|
    set t : ℝ := min 1 (d / (2 * (|C| + 1))) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ d / (2 * (|C| + 1)) := min_le_right _ _
    have h := (hC ⟨t, ht0.le⟩ ht1).1
    rw [(thetaTrunc_incr A b b1 θ y _).1] at h
    simp only [NNReal.coe_mk] at h
    rw [← sub_mul, abs_mul, abs_of_pos ht0] at h
    have h2 : C * t ^ 2 ≤ (|C| + 1) * t * t := by
      nlinarith [le_abs_self C, sq_nonneg t]
    have h3 : (|C| + 1) * t ≤ d / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      have := mul_le_mul_of_nonneg_left ht2 (by positivity : (0:ℝ) ≤ 2 * (|C| + 1))
      rw [mul_div_cancel₀ _ (by positivity)] at this; linarith
    nlinarith
  · intro h
    refine consistent_of_moments 0 (A y ^ 2 + 2 * A y * θ * b y * b1 y + 3 * (θ * b y * b1 y) ^ 2)
      (fun τ => ?_) (fun τ => ?_)
    · rw [(thetaTrunc_incr A b b1 θ y τ).1, h]; ring
    · rw [(thetaTrunc_incr A b b1 θ y τ).2]

/-- §10.3.1: the naive implicit or semi-implicit scheme (drift `A = a`, `θ > 0`) is
inconsistent wherever `b(y)b'(y) ≠ 0`. -/
theorem naive_implicit_inconsistent (a b b1 : ℝ → ℝ) {θ y : ℝ} (hθ : θ ≠ 0)
    (hb : b y * b1 y ≠ 0) : ¬ IsConsistentAt (thetaTrunc a b b1 θ) a b y := by
  rw [thetaTrunc_consistent_iff]
  intro h
  have : θ * (b y * b1 y) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  exacts [hθ h1, hb h1]

/-- The corrected scheme `A = a - θbb'` (10.4.10) is consistent for every `θ`. -/
theorem thetaTrunc_corrected_consistent (a b b1 : ℝ → ℝ) (θ y : ℝ) :
    IsConsistentAt (thetaTrunc (fun x => a x - θ * b x * b1 x) b b1 θ) a b y :=
  (thetaTrunc_consistent_iff _ a b b1 θ y).mpr (by ring)

/-! ### Instances -/

/-- Instance of `Gardiner.SDE.implicit_step_expansion`: `A = sin`, `b = cos`, `θ = ½`, with
`K₀ = K₁ = K₂ = 1`. -/
example {y τ dw z : ℝ} (hz : z = Real.sin (y + 1 / 2 * z) * τ + Real.cos (y + 1 / 2 * z) * dw) :
    |z - (Real.sin y * τ + Real.cos y * dw + 1 / 2 * Real.cos y * (-Real.sin y) * dw ^ 2)| ≤
      2 * 1 * 1 * (|τ| + |dw|) * |τ| + (1 * 1 ^ 2 / 2 + 1 ^ 2 * 1) * (|τ| + |dw|) ^ 3 :=
  implicit_step_expansion (A1 := Real.cos) (b1 := fun x => -Real.sin x) (b2 := fun x => -Real.cos x)
    (fun x => Real.hasDerivAt_sin x) (fun x => Real.hasDerivAt_cos x)
    (fun x => (Real.hasDerivAt_sin x).neg) (fun x => Real.abs_sin_le_one x)
    (fun x => Real.abs_cos_le_one x) (fun x => Real.abs_cos_le_one x)
    (fun x => by simpa using Real.abs_sin_le_one x) (fun x => by simpa using Real.abs_cos_le_one x)
    (by norm_num) (by norm_num) hz

/-- Instance: for `dx = x dW` (`a = 0`, `b = id`, `bb' = x`) the naive semi-implicit scheme is
inconsistent at `y = 1`, while the corrected one is consistent. -/
example : ¬ IsConsistentAt (thetaTrunc (fun _ => 0) id (fun _ => 1) (1 / 2)) (fun _ => 0) id 1 ∧
    IsConsistentAt (thetaTrunc (fun x => 0 - 1 / 2 * id x * 1) id (fun _ => 1) (1 / 2))
      (fun _ => 0) id 1 :=
  ⟨naive_implicit_inconsistent _ _ _ (by norm_num) (by norm_num),
    thetaTrunc_corrected_consistent (fun _ => 0) id (fun _ => 1) (1 / 2) 1⟩

end Gardiner.SDE
