/-
# Moments and autocorrelation functions in the small noise expansion

Gardiner, *Handbook of Stochastic Methods*, §6.3.1 (equations (6.3.16)–(6.3.35)).

* (6.3.17)–(6.3.18): `Gardiner.smallNoise_moment_hierarchy` derives the moment hierarchy
  from the perturbation hierarchy (6.3.14) by integration by parts (surface terms are
  derived from integrability, not assumed), and `Gardiner.smallNoise_moment_ode` gives the
  time-derivative form; the exchange of `d/dt` with `∫ dy` is the named hypothesis
  `hswap`.
* (6.3.19)–(6.3.24): the first equations of the hierarchy.  The text's (6.3.19)–(6.3.21)
  have `M⁰` where (6.3.18) gives `M¹` in the `Ã₁` terms: (6.3.19) should read
  `dM₀¹/dt = Ã₁ M₀¹`, (6.3.20) `dM₁¹/dt = Ã₁ M₁¹ + Ã₂ M₀²`, (6.3.21)
  `dM₂¹/dt = Ã₁ M₂¹ + Ã₂ M₁² + Ã₃ M₀³` (this is also what the stationary values (6.3.29)
  use).  The corrected equations are formalized.
* (6.3.25)–(6.3.28): normalization.  (6.3.28) should read `M_r⁰ = 0` for `r ≥ 1`
  (the text prints `r ≠ 1`).
* (6.3.29)–(6.3.31): stationary moments.
* (6.3.32)–(6.3.35): the autocorrelation hierarchy.  (6.3.32) holds exactly only when
  `⟨y⟩ₛ = 0`; the general identity carries the cross term `α ε (⟨y(t)⟩ + ⟨y(0)⟩)`.
-/
import SHSLib.Gardiner.Approx.SmallNoise

open MeasureTheory Filter Topology Set
open scoped BigOperators Nat

noncomputable section

namespace Gardiner

/-! ### (6.3.16)–(6.3.18): the moment hierarchy -/

/-- (6.3.17): `M_rⁿ = ∫ yⁿ p̂_r(y) dy`. -/
def snMoment (ph : ℕ → ℝ → ℝ) (r n : ℕ) : ℝ := ∫ y, y ^ n * ph r y

/-- The right-hand side of (6.3.18), as a function of the moments `M m k = M_mᵏ`. -/
def hierMomRHS (At Bt : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (r n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (r + 1), ((n : ℝ) * At (r - m + 1) * M m (n + r - m)
    + ((n : ℝ) * ((n : ℝ) - 1) / 2) * Bt (r - m) * M m (n + r - m - 2))

lemma integral_pow_mul_hierFlux (At : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r i : ℕ)
    (hph : ∀ m ≤ r, Integrable (fun y => y ^ (i + (r - m + 1)) * ph m y)) :
    ∫ y, y ^ i * hierFlux At ph r y
      = ∑ m ∈ Finset.range (r + 1), At (r - m + 1) * snMoment ph m (i + (r - m + 1)) := by
  have e : ∀ y, y ^ i * hierFlux At ph r y
      = ∑ m ∈ Finset.range (r + 1), At (r - m + 1) * (y ^ (i + (r - m + 1)) * ph m y) := by
    intro y
    rw [hierFlux, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [pow_add]; ring
  simp_rw [e]
  rw [integral_finset_sum _ fun m hm =>
    (hph m (by simp at hm; omega)).const_mul _]
  exact Finset.sum_congr rfl fun m _ => by rw [integral_const_mul, snMoment]

lemma integral_pow_mul_hierDiff (Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r i : ℕ)
    (hph : ∀ m ≤ r, Integrable (fun y => y ^ (i + (r - m)) * ph m y)) :
    ∫ y, y ^ i * hierDiff Bt ph r y
      = ∑ m ∈ Finset.range (r + 1), Bt (r - m) * snMoment ph m (i + (r - m)) := by
  have e : ∀ y, y ^ i * hierDiff Bt ph r y
      = ∑ m ∈ Finset.range (r + 1), Bt (r - m) * (y ^ (i + (r - m)) * ph m y) := by
    intro y
    rw [hierDiff, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [pow_add]; ring
  simp_rw [e]
  rw [integral_finset_sum _ fun m hm =>
    (hph m (by simp at hm; omega)).const_mul _]
  exact Finset.sum_congr rfl fun m _ => by rw [integral_const_mul, snMoment]

lemma integrable_pow_mul_hierFlux (At : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r i : ℕ)
    (hph : ∀ m ≤ r, Integrable (fun y => y ^ (i + (r - m + 1)) * ph m y)) :
    Integrable (fun y => y ^ i * hierFlux At ph r y) := by
  have e : ∀ y, y ^ i * hierFlux At ph r y
      = ∑ m ∈ Finset.range (r + 1), At (r - m + 1) * (y ^ (i + (r - m + 1)) * ph m y) := by
    intro y
    rw [hierFlux, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [pow_add]; ring
  simp_rw [e]
  exact integrable_finset_sum _ fun m hm => (hph m (by simp at hm; omega)).const_mul _

lemma integrable_pow_mul_hierDiff (Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r i : ℕ)
    (hph : ∀ m ≤ r, Integrable (fun y => y ^ (i + (r - m)) * ph m y)) :
    Integrable (fun y => y ^ i * hierDiff Bt ph r y) := by
  have e : ∀ y, y ^ i * hierDiff Bt ph r y
      = ∑ m ∈ Finset.range (r + 1), Bt (r - m) * (y ^ (i + (r - m)) * ph m y) := by
    intro y
    rw [hierDiff, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [pow_add]; ring
  simp_rw [e]
  exact integrable_finset_sum _ fun m hm => (hph m (by simp at hm; omega)).const_mul _

/-- **(6.3.18)**: integrating the `r`-th equation (6.3.14) of the hierarchy against `yⁿ`
and integrating by parts gives
`∫ yⁿ RHS_r = Σ_{m ≤ r} [n Ã_{r-m+1} M_m^{n+r-m} + n(n-1)/2 B̃_{r-m} M_m^{n+r-m-2}]`.
The hypotheses are the differentiability of the flux and diffusion terms of (6.3.14) and
the integrability of the integrands; no surface term is assumed to vanish. -/
theorem smallNoise_moment_hierarchy (At Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r n : ℕ)
    (F' G' G'' : ℝ → ℝ)
    (hF : ∀ y, HasDerivAt (hierFlux At ph r) (F' y) y)
    (hG : ∀ y, HasDerivAt (hierDiff Bt ph r) (G' y) y)
    (hG' : ∀ y, HasDerivAt G' (G'' y) y)
    (hph : ∀ m ≤ r, ∀ k ≤ n + r + 1, Integrable (fun y => y ^ k * ph m y))
    (iF' : Integrable (fun y => y ^ n * F' y))
    (iG' : ∀ i ≤ n, Integrable (fun y => y ^ i * G' y))
    (iG'' : Integrable (fun y => y ^ n * G'' y)) :
    ∫ y, y ^ n * hierRHS At Bt ph r y = hierMomRHS At Bt (snMoment ph) r n := by
  have hd1 : deriv (hierFlux At ph r) = F' := funext fun y => (hF y).deriv
  have hd2 : deriv (hierDiff Bt ph r) = G' := funext fun y => (hG y).deriv
  have hd3 : deriv G' = G'' := funext fun y => (hG' y).deriv
  have e : ∀ y, hierRHS At Bt ph r y = -F' y + (1 / 2) * G'' y := by
    intro y; rw [hierRHS, hd1, hd2, hd3]
  simp_rw [e]
  have iF : ∀ i ≤ n, Integrable (fun y => y ^ i * hierFlux At ph r y) := fun i hi =>
    integrable_pow_mul_hierFlux At ph r i fun m hm => hph m hm _ (by omega)
  have iG : ∀ i ≤ n, Integrable (fun y => y ^ i * hierDiff Bt ph r y) := fun i hi =>
    integrable_pow_mul_hierDiff Bt ph r i fun m hm => hph m hm _ (by omega)
  rw [integral_pow_mul_fp n hF hG hG' iF iF' iG iG' iG'',
    integral_pow_mul_hierFlux At ph r (n - 1) (fun m hm => hph m hm _ (by omega)),
    integral_pow_mul_hierDiff Bt ph r (n - 2) (fun m hm => hph m hm _ (by omega)),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, hierMomRHS]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp
    · rw [show 1 - 1 + (r - m + 1) = 1 + r - m by omega]
      ring
  · have h1 : n - 1 + (r - m + 1) = n + r - m := by omega
    have h2 : n - 2 + (r - m) = n + r - m - 2 := by omega
    rw [h1, h2]
    ring

/-- **(6.3.18), time-derivative form.**  If the coefficients `p̂_m(t, ·)` evolve by the
hierarchy (6.3.14) and `d/dt` may be exchanged with `∫ dy` (the named hypothesis `hswap`,
an interchange the text makes silently), then `dM_rⁿ/dt` is given by (6.3.18). -/
theorem smallNoise_moment_ode (At Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ → ℝ) (dph : ℝ → ℝ)
    (r n : ℕ) (t : ℝ) (F' G' G'' : ℝ → ℝ)
    (hswap : HasDerivAt (fun t => ∫ y, y ^ n * ph r t y) (∫ y, y ^ n * dph y) t)
    (hpde : ∀ y, dph y = hierRHS At Bt (fun m => ph m t) r y)
    (hF : ∀ y, HasDerivAt (hierFlux At (fun m => ph m t) r) (F' y) y)
    (hG : ∀ y, HasDerivAt (hierDiff Bt (fun m => ph m t) r) (G' y) y)
    (hG' : ∀ y, HasDerivAt G' (G'' y) y)
    (hph : ∀ m ≤ r, ∀ k ≤ n + r + 1, Integrable (fun y => y ^ k * ph m t y))
    (iF' : Integrable (fun y => y ^ n * F' y))
    (iG' : ∀ i ≤ n, Integrable (fun y => y ^ i * G' y))
    (iG'' : Integrable (fun y => y ^ n * G'' y)) :
    HasDerivAt (fun t => snMoment (fun m => ph m t) r n)
      (hierMomRHS At Bt (snMoment fun m => ph m t) r n) t := by
  have := smallNoise_moment_hierarchy At Bt (fun m => ph m t) r n F' G' G'' hF hG hG' hph iF'
    iG' iG''
  simp_rw [← hpde] at this
  rw [← this]
  exact hswap

/-! ### (6.3.19)–(6.3.24): the first equations, corrected -/

section FirstEquations

variable (At Bt : ℕ → ℝ) (M : ℕ → ℕ → ℝ)

/-- (6.3.19), corrected: `dM₀¹/dt = Ã₁ M₀¹`. -/
theorem hierMomRHS_0_1 : hierMomRHS At Bt M 0 1 = At 1 * M 0 1 := by
  simp only [hierMomRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num

/-- (6.3.20), corrected: `dM₁¹/dt = Ã₁ M₁¹ + Ã₂ M₀²`. -/
theorem hierMomRHS_1_1 : hierMomRHS At Bt M 1 1 = At 1 * M 1 1 + At 2 * M 0 2 := by
  simp only [hierMomRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  ring

/-- (6.3.21), corrected: `dM₂¹/dt = Ã₁ M₂¹ + Ã₂ M₁² + Ã₃ M₀³`. -/
theorem hierMomRHS_2_1 :
    hierMomRHS At Bt M 2 1 = At 1 * M 2 1 + At 2 * M 1 2 + At 3 * M 0 3 := by
  simp only [hierMomRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  ring

/-- (6.3.22): `dM₀²/dt = 2 Ã₁ M₀² + B̃₀`, using `M₀⁰ = 1`. -/
theorem hierMomRHS_0_2 (h00 : M 0 0 = 1) : hierMomRHS At Bt M 0 2 = 2 * At 1 * M 0 2 + Bt 0 := by
  simp only [hierMomRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [h00]

/-- (6.3.23): `dM₁²/dt = 2 Ã₁ M₁² + 2 Ã₂ M₀³ + B̃₁ M₀¹`, using `M₁⁰ = 0`. -/
theorem hierMomRHS_1_2 (h10 : M 1 0 = 0) :
    hierMomRHS At Bt M 1 2 = 2 * At 1 * M 1 2 + 2 * At 2 * M 0 3 + Bt 1 * M 0 1 := by
  simp only [hierMomRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [h10]
  ring

/-- (6.3.24): `dM₀³/dt = 3 Ã₁ M₀³ + 3 B̃₀ M₀¹`. -/
theorem hierMomRHS_0_3 : hierMomRHS At Bt M 0 3 = 3 * At 1 * M 0 3 + 3 * Bt 0 * M 0 1 := by
  simp only [hierMomRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num

/-- The `n = 4`, `r = 0` equation used for (6.3.45): `dM₀⁴/dt = 4 Ã₁ M₀⁴ + 6 B̃₀ M₀²`. -/
theorem hierMomRHS_0_4 : hierMomRHS At Bt M 0 4 = 4 * At 1 * M 0 4 + 6 * Bt 0 * M 0 2 := by
  simp only [hierMomRHS, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num

end FirstEquations

/-! ### (6.3.25)–(6.3.28): normalization -/

/-- (6.3.26)–(6.3.28): the normalization `Σ_r εʳ M_r⁰ = 1`, as an identity of formal power
series, holds iff `M₀⁰ = 1` and `M_r⁰ = 0` for all `r ≥ 1`. -/
theorem normalization_iff (M : ℕ → ℕ → ℝ) :
    PowerSeries.mk (fun r => M r 0) = 1 ↔ M 0 0 = 1 ∧ ∀ r, 1 ≤ r → M r 0 = 0 := by
  constructor
  · intro h
    refine ⟨?_, fun r hr => ?_⟩
    · have := congrArg (PowerSeries.coeff 0) h
      simpa using this
    · have := congrArg (PowerSeries.coeff r) h
      simpa [PowerSeries.coeff_one, show r ≠ 0 by omega] using this
  · rintro ⟨h0, h⟩
    ext r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [h0]
    · simp [PowerSeries.coeff_one, show r ≠ 0 by omega, h r hr]

/-! ### (6.3.29)–(6.3.31): stationary moments -/

/-- **(6.3.29)**: with time-independent coefficients, `Ã₁ ≠ 0`, the normalization, and the
right-hand sides of (6.3.19)–(6.3.24) set to zero, the stationary moments are
`M₀¹ = 0`, `M₀² = -B̃₀/(2Ã₁)`, `M₀³ = 0`, `M₁¹ = Ã₂B̃₀/(2Ã₁²)`, `M₁² = 0`, `M₂¹ = 0`. -/
theorem stationary_moments (At Bt : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (hA : At 1 ≠ 0)
    (h00 : M 0 0 = 1) (h10 : M 1 0 = 0)
    (s01 : hierMomRHS At Bt M 0 1 = 0) (s02 : hierMomRHS At Bt M 0 2 = 0)
    (s03 : hierMomRHS At Bt M 0 3 = 0) (s11 : hierMomRHS At Bt M 1 1 = 0)
    (s12 : hierMomRHS At Bt M 1 2 = 0) (s21 : hierMomRHS At Bt M 2 1 = 0) :
    M 0 1 = 0 ∧ M 0 2 = -(1 / 2) * Bt 0 / At 1 ∧ M 0 3 = 0 ∧
      M 1 1 = (1 / 2) * At 2 * Bt 0 / At 1 ^ 2 ∧ M 1 2 = 0 ∧ M 2 1 = 0 := by
  rw [hierMomRHS_0_1] at s01
  rw [hierMomRHS_0_2 _ _ _ h00] at s02
  rw [hierMomRHS_0_3] at s03
  rw [hierMomRHS_1_1] at s11
  rw [hierMomRHS_1_2 _ _ _ h10] at s12
  rw [hierMomRHS_2_1] at s21
  have m01 : M 0 1 = 0 := by
    rcases mul_eq_zero.1 s01 with h | h
    · exact absurd h hA
    · exact h
  have m03 : M 0 3 = 0 := by
    rw [m01] at s03
    have : 3 * At 1 * M 0 3 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by linarith : At 1 = 0) hA
    · exact h
  have m02 : M 0 2 = -(1 / 2) * Bt 0 / At 1 := by field_simp; linarith
  have m12 : M 1 2 = 0 := by
    rw [m01, m03] at s12
    have : 2 * At 1 * M 1 2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by linarith : At 1 = 0) hA
    · exact h
  refine ⟨m01, m02, m03, ?_, m12, ?_⟩
  · rw [m02] at s11
    field_simp
    field_simp at s11
    linarith
  · rw [m12, m03] at s21
    have : At 1 * M 2 1 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hA
    · exact h

/-- **(6.3.30)**: the stationary mean to order `ε²`,
`⟨x⟩ₛ = α + ε(M₀¹ + ε M₁¹ + ε² M₂¹) = α + ½ ε² Ã₂ B̃₀/Ã₁²`. -/
theorem stationary_mean (At Bt : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (α ε : ℝ) (hA : At 1 ≠ 0)
    (h00 : M 0 0 = 1) (h10 : M 1 0 = 0)
    (s01 : hierMomRHS At Bt M 0 1 = 0) (s02 : hierMomRHS At Bt M 0 2 = 0)
    (s03 : hierMomRHS At Bt M 0 3 = 0) (s11 : hierMomRHS At Bt M 1 1 = 0)
    (s12 : hierMomRHS At Bt M 1 2 = 0) (s21 : hierMomRHS At Bt M 2 1 = 0) :
    α + ε * (M 0 1 + ε * M 1 1 + ε ^ 2 * M 2 1)
      = α + (1 / 2) * ε ^ 2 * At 2 * Bt 0 / At 1 ^ 2 := by
  obtain ⟨h1, -, -, h4, -, h6⟩ :=
    stationary_moments At Bt M hA h00 h10 s01 s02 s03 s11 s12 s21
  rw [h1, h4, h6]
  ring

/-- (6.3.31), first step: `var{α + ε y} = ε² var{y}` for any square-integrable `y`. -/
theorem variance_affine {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ]
    (Y : Ω' → ℝ) (α ε : ℝ) (h1 : Integrable Y μ) (h2 : Integrable (fun ω => Y ω ^ 2) μ) :
    (∫ ω, (α + ε * Y ω) ^ 2 ∂μ) - (∫ ω, (α + ε * Y ω) ∂μ) ^ 2
      = ε ^ 2 * ((∫ ω, Y ω ^ 2 ∂μ) - (∫ ω, Y ω ∂μ) ^ 2) := by
  have e : ∀ ω, (α + ε * Y ω) ^ 2 = α ^ 2 + (2 * α * ε) * Y ω + ε ^ 2 * Y ω ^ 2 := fun ω => by ring
  simp_rw [e]
  have i0 : Integrable (fun _ : Ω' => α ^ 2) μ := integrable_const _
  have i01 : Integrable (fun ω => α ^ 2 + (2 * α * ε) * Y ω) μ := i0.add (h1.const_mul _)
  rw [integral_add i01 (h2.const_mul _), integral_add i0 (h1.const_mul _),
    integral_add (integrable_const _) (h1.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const, integral_const]
  simp
  ring

/-- **(6.3.31)**: to lowest order the stationary variance is `ε² M₀² = -ε² B̃₀/(2Ã₁)`. -/
theorem stationary_variance (At Bt : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (ε : ℝ) (hA : At 1 ≠ 0)
    (h00 : M 0 0 = 1) (h10 : M 1 0 = 0)
    (s01 : hierMomRHS At Bt M 0 1 = 0) (s02 : hierMomRHS At Bt M 0 2 = 0)
    (s03 : hierMomRHS At Bt M 0 3 = 0) (s11 : hierMomRHS At Bt M 1 1 = 0)
    (s12 : hierMomRHS At Bt M 1 2 = 0) (s21 : hierMomRHS At Bt M 2 1 = 0) :
    ε ^ 2 * (M 0 2 - M 0 1 ^ 2) = -(ε ^ 2 / 2) * Bt 0 / At 1 := by
  obtain ⟨h1, h2, -⟩ := stationary_moments At Bt M hA h00 h10 s01 s02 s03 s11 s12 s21
  rw [h1, h2]
  ring

/-! ### (6.3.32)–(6.3.35): the autocorrelation hierarchy -/

section Autocorrelation

variable {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')

/-- (6.3.32), in general: `⟨x(t) x(0)⟩ = α² + α ε (⟨y(t)⟩ + ⟨y(0)⟩) + ε² ⟨y(t) y(0)⟩` for
`x = α + ε y`. -/
theorem autocorr_affine [IsProbabilityMeasure μ] (Y Y₀ : Ω' → ℝ) (α ε : ℝ)
    (h1 : Integrable Y μ) (h0 : Integrable Y₀ μ) (h10 : Integrable (fun ω => Y ω * Y₀ ω) μ) :
    ∫ ω, (α + ε * Y ω) * (α + ε * Y₀ ω) ∂μ
      = α ^ 2 + α * ε * ((∫ ω, Y ω ∂μ) + ∫ ω, Y₀ ω ∂μ) + ε ^ 2 * ∫ ω, Y ω * Y₀ ω ∂μ := by
  have e : ∀ ω, (α + ε * Y ω) * (α + ε * Y₀ ω)
      = α ^ 2 + (α * ε) * Y ω + (α * ε) * Y₀ ω + ε ^ 2 * (Y ω * Y₀ ω) := fun ω => by ring
  simp_rw [e]
  have i0 : Integrable (fun _ : Ω' => α ^ 2) μ := integrable_const _
  have i1 : Integrable (fun ω => α ^ 2 + (α * ε) * Y ω) μ := i0.add (h1.const_mul _)
  have i2 : Integrable (fun ω => α ^ 2 + (α * ε) * Y ω + (α * ε) * Y₀ ω) μ :=
    i1.add (h0.const_mul _)
  rw [integral_add i2 (h10.const_mul _), integral_add i1 (h0.const_mul _),
    integral_add i0 (h1.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const]
  simp
  ring

/-- (6.3.32) as printed: when `⟨y(t)⟩ₛ = ⟨y(0)⟩ₛ = 0`,
`⟨x(t) x(0)⟩ₛ = α² + ε² ⟨y(t) y(0)⟩ₛ`. -/
theorem autocorr_affine_of_mean_zero [IsProbabilityMeasure μ] (Y Y₀ : Ω' → ℝ) (α ε : ℝ)
    (h1 : Integrable Y μ) (h0 : Integrable Y₀ μ) (h10 : Integrable (fun ω => Y ω * Y₀ ω) μ)
    (m1 : ∫ ω, Y ω ∂μ = 0) (m0 : ∫ ω, Y₀ ω ∂μ = 0) :
    ∫ ω, (α + ε * Y ω) * (α + ε * Y₀ ω) ∂μ = α ^ 2 + ε ^ 2 * ∫ ω, Y ω * Y₀ ω ∂μ := by
  rw [autocorr_affine μ Y Y₀ α ε h1 h0 h10, m1, m0]
  ring

/-- The integrand of (6.3.33). -/
def autocorrIntegrand (A B : ℝ → ℝ) (α ε : ℝ) (n : ℕ) (y y₀ : ℝ) : ℝ :=
  ((A (α + ε * y) - A α) / ε * ((n : ℝ) * y ^ (n - 1))
    + (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1)) * B (α + ε * y) * y ^ (n - 2)) * y₀

/-- **(6.3.33) ⟹ (6.3.34)**: when the expansions (6.3.9)–(6.3.10) are finite (polynomial
`A`, `B`), the right-hand side of (6.3.33) equals
`Σ_q ε^q [n Ã_{q+1} ⟨y(t)^{q+n} y(0)⟩ + n(n-1)/2 B̃_q ⟨y(t)^{q+n-2} y(0)⟩]`. -/
theorem autocorr_hierarchy (A B : ℝ → ℝ) (α ε : ℝ) (At Bt : ℕ → ℝ) (N n : ℕ)
    (hA : ∀ y, (A (α + ε * y) - A α) / ε = ∑ q ∈ Finset.range N, ε ^ q * At (q + 1) * y ^ (q + 1))
    (hB : ∀ y, B (α + ε * y) = ∑ q ∈ Finset.range N, ε ^ q * Bt q * y ^ q)
    (Y Y₀ : Ω' → ℝ) (hint : ∀ k ≤ N + n, Integrable (fun ω => Y ω ^ k * Y₀ ω) μ) :
    ∫ ω, autocorrIntegrand A B α ε n (Y ω) (Y₀ ω) ∂μ
      = ∑ q ∈ Finset.range N, ε ^ q * ((n : ℝ) * At (q + 1) * (∫ ω, Y ω ^ (q + n) * Y₀ ω ∂μ)
          + ((n : ℝ) * ((n : ℝ) - 1) / 2) * Bt q * ∫ ω, Y ω ^ (q + n - 2) * Y₀ ω ∂μ) := by
  have hpt : ∀ y y₀ : ℝ, autocorrIntegrand A B α ε n y y₀
      = ∑ q ∈ Finset.range N, (ε ^ q * ((n : ℝ) * At (q + 1)) * (y ^ (q + n) * y₀)
          + ε ^ q * (((n : ℝ) * ((n : ℝ) - 1) / 2) * Bt q) * (y ^ (q + n - 2) * y₀)) := by
    intro y y₀
    simp only [autocorrIntegrand, hA, hB, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have k1 : (n : ℝ) * (y ^ (q + 1) * y ^ (n - 1)) = (n : ℝ) * y ^ (q + n) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [← pow_add, show q + 1 + (n - 1) = q + n by omega]
    have k2 : ((n : ℝ) * ((n : ℝ) - 1)) * (y ^ q * y ^ (n - 2))
        = ((n : ℝ) * ((n : ℝ) - 1)) * y ^ (q + n - 2) := by
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n <;> simp
      · rw [← pow_add, show q + (n - 2) = q + n - 2 by omega]
    linear_combination (ε ^ q * At (q + 1) * y₀) * k1 + (ε ^ q * Bt q * y₀ / 2) * k2
  simp_rw [hpt]
  rw [integral_finset_sum _ fun q hq => ?_]
  · refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_range] at hq
    rw [integral_add ((hint _ (by omega)).const_mul _) ((hint _ (by omega)).const_mul _),
      integral_const_mul, integral_const_mul]
    ring
  · simp only [Finset.mem_range] at hq
    exact ((hint _ (by omega)).const_mul _).add ((hint _ (by omega)).const_mul _)

/-- (6.3.34) in time-derivative form: if `c(t) = ⟨y(t)ⁿ y(0)⟩ₛ` satisfies (6.3.33), then
it satisfies (6.3.34). -/
theorem autocorr_hierarchy_deriv (A B : ℝ → ℝ) (α ε : ℝ) (At Bt : ℕ → ℝ) (N n : ℕ)
    (hA : ∀ y, (A (α + ε * y) - A α) / ε = ∑ q ∈ Finset.range N, ε ^ q * At (q + 1) * y ^ (q + 1))
    (hB : ∀ y, B (α + ε * y) = ∑ q ∈ Finset.range N, ε ^ q * Bt q * y ^ q)
    (Y : ℝ → Ω' → ℝ) (t : ℝ)
    (hint : ∀ k ≤ N + n, Integrable (fun ω => Y t ω ^ k * Y 0 ω) μ)
    (h633 : HasDerivAt (fun t => ∫ ω, Y t ω ^ n * Y 0 ω ∂μ)
      (∫ ω, autocorrIntegrand A B α ε n (Y t ω) (Y 0 ω) ∂μ) t) :
    HasDerivAt (fun t => ∫ ω, Y t ω ^ n * Y 0 ω ∂μ)
      (∑ q ∈ Finset.range N, ε ^ q * ((n : ℝ) * At (q + 1) * (∫ ω, Y t ω ^ (q + n) * Y 0 ω ∂μ)
          + ((n : ℝ) * ((n : ℝ) - 1) / 2) * Bt q * ∫ ω, Y t ω ^ (q + n - 2) * Y 0 ω ∂μ)) t := by
  rw [← autocorr_hierarchy μ A B α ε At Bt N n hA hB (Y t) (Y 0) hint]
  exact h633

/-- (6.3.35): the initial condition `⟨y(0)ⁿ y(0)⟩ₛ = ⟨yⁿ⁺¹⟩ₛ`. -/
theorem autocorr_initial (Y₀ : Ω' → ℝ) (n : ℕ) :
    ∫ ω, Y₀ ω ^ n * Y₀ ω ∂μ = ∫ ω, Y₀ ω ^ (n + 1) ∂μ := by
  simp_rw [pow_succ]

end Autocorrelation

end Gardiner
