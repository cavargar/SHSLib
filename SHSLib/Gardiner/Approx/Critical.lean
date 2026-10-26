/-
# Kurtz's theorem and critical fluctuations

Gardiner, *Handbook of Stochastic Methods*, §7.2.4, equations (7.2.62)–(7.2.67), and §7.2.5,
equations (7.2.68)–(7.2.77).

**§7.2.4.**  Kurtz's strong approximation (7.2.64), `|b(t) - a(t)| ≲ log V`, is taken as a
hypothesis (`hcouple`).  `Gardiner.kurtz_charFun_le` is the deduction (7.2.65)–(7.2.67) with
explicit constant: `|⟨e^{isz}⟩ - ⟨e^{isy}⟩| ≤ |s| C log V / √V`;
`Gardiner.kurtz_charFun_tendsto` shows that this error tends to zero, and
`Gardiner.kurtz_charFun_lna_le` combines it with an `O(V^{-1/2})` approximation of the law of
`y` to give the `O(V^{-1/2} log V)` statement at the end of §7.2.4.

**§7.2.5.**  When `α̃₁(φₛ) = 0` and the first `q - 1` derivatives of `α̃₁` vanish at `φₛ`
(7.2.68), the scaling `a = Ωφₛ + Ω^μ u` (7.2.70) with `μ = q/(q+1)` (7.2.73) and the slow time
`τ = Ω^{-(q-1)/(q+1)} t` (7.2.75) lead to (7.2.74).  `Gardiner.critGen_sub_critLim_le` makes this
quantitative: writing `θ = Ω^{1/(q+1)}`, the slow-time generator of the master equation differs
from the generator `(α̃₁^{(q)}/q!) uᵠ ∂_u + ½ α̃₂(φₛ) ∂_u²` of (7.2.74) by `O(θ⁻¹) = O(Ω^{-1/(q+1)})`,
with explicit constants.  The exponent bookkeeping (7.2.71)–(7.2.77) is
`Gardiner.critical_exponent`, `Gardiner.critical_scales`; (7.2.76) is
`Gardiner.critical_mean_eq`; the cubic case (7.2.69) is `Gardiner.critical_cubic`,
`Gardiner.critical_cubic_solution`, with the non-degenerate instance
`Gardiner.cubic_critGen_sub_critLim_le` built from the reaction of §7.1.3.
-/
import SHSLib.Gardiner.Approx.SystemSize

open MeasureTheory Filter Topology Set Asymptotics
open scoped Nat

noncomputable section

namespace Gardiner

/-! ### §7.2.4: Kurtz's theorem implies van Kampen's lowest order -/

lemma norm_cexp_I_sub_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤ |x - y| := by
  have e : Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)
      = Complex.exp (Complex.I * y) * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

section Kurtz

variable {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ]

/-- **(7.2.65)–(7.2.67) with an explicit constant.**  Let `a = a(t)` be the master-equation
process and `b = b(t)` the diffusion (7.2.63) at a fixed time, coupled on one probability space
with `|b - a| ≤ C log V` almost surely (Kurtz's estimate (7.2.64), taken as hypothesis).  With
`z = (a - Vφ)/√V` (7.2.65) and `y = (b - Vφ)/√V` (7.2.66), the characteristic functions satisfy
`|⟨e^{isz}⟩ - ⟨e^{isy}⟩| ≤ |s| C log V / √V`. -/
theorem kurtz_charFun_le (a b : Ω' → ℝ) (ha : Measurable a) (hb : Measurable b)
    {V : ℝ} (hV : 0 < V) (phi C s : ℝ)
    (hcouple : ∀ᵐ ω ∂μ, |b ω - a ω| ≤ C * Real.log V) :
    ‖(∫ ω, Complex.exp (Complex.I * (s * ((a ω - V * phi) / Real.sqrt V) : ℝ)) ∂μ)
        - ∫ ω, Complex.exp (Complex.I * (s * ((b ω - V * phi) / Real.sqrt V) : ℝ)) ∂μ‖
      ≤ |s| * (C * Real.log V) / Real.sqrt V := by
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hm : ∀ g : Ω' → ℝ, Measurable g →
      Integrable (fun ω => Complex.exp (Complex.I * (s * ((g ω - V * phi) / Real.sqrt V) : ℝ))) μ := by
    intro g hg
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
    · refine (Complex.continuous_exp.measurable.comp ?_).aestronglyMeasurable
      exact measurable_const.mul (Complex.measurable_ofReal.comp
        (measurable_const.mul ((hg.sub measurable_const).div_const _)))
    · rw [Complex.norm_exp_I_mul_ofReal]
  rw [← integral_sub (hm a ha) (hm b hb)]
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => Complex.exp (Complex.I * (s * ((a ω - V * phi) / Real.sqrt V) : ℝ))
      - Complex.exp (Complex.I * (s * ((b ω - V * phi) / Real.sqrt V) : ℝ)))
    (C := |s| * (C * Real.log V) / Real.sqrt V) (by
      filter_upwards [hcouple] with ω hω
      refine (norm_cexp_I_sub_le _ _).trans ?_
      rw [← mul_sub, ← sub_div, abs_mul, abs_div, abs_of_pos hs0, mul_div_assoc]
      gcongr
      rw [show a ω - V * phi - (b ω - V * phi) = -(b ω - a ω) by ring, abs_neg]
      exact hω)
  simpa using this

/-- The error `|s| C log V / √V` of (7.2.67) tends to zero as `V → ∞` (since
`log V = o(V^{1/2})`). -/
theorem kurtz_charFun_tendsto (C s : ℝ) :
    Tendsto (fun V => |s| * (C * Real.log V) / Real.sqrt V) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  have e : ∀ V : ℝ, 0 < V → |s| * (C * Real.log V) / Real.sqrt V
      = |s| * C * (Real.log V / V ^ (1 / 2 : ℝ)) := by
    intro V hV; rw [Real.sqrt_eq_rpow]; ring
  have := h.const_mul (|s| * C)
  rw [mul_zero] at this
  exact this.congr' (by filter_upwards [eventually_gt_atTop 0] with V hV using (e V hV).symm)

/-- **The end of §7.2.4**: if moreover the characteristic function of `y` is within `K/√V` of
that of the linear-noise limit `χ(s)` (the `O(V^{-1/2})` small-noise estimate for (7.2.63)), then
the characteristic function of the fluctuation `z` of the master equation is within
`(K + |s| C log V)/√V` of `χ(s)` — a slightly weaker rate because of the `log V`. -/
theorem kurtz_charFun_lna_le (a b : Ω' → ℝ) (ha : Measurable a) (hb : Measurable b)
    {V : ℝ} (hV : 0 < V) (phi C s K : ℝ) (χ : ℂ)
    (hcouple : ∀ᵐ ω ∂μ, |b ω - a ω| ≤ C * Real.log V)
    (hy : ‖(∫ ω, Complex.exp (Complex.I * (s * ((b ω - V * phi) / Real.sqrt V) : ℝ)) ∂μ) - χ‖
      ≤ K / Real.sqrt V) :
    ‖(∫ ω, Complex.exp (Complex.I * (s * ((a ω - V * phi) / Real.sqrt V) : ℝ)) ∂μ) - χ‖
      ≤ (K + |s| * (C * Real.log V)) / Real.sqrt V := by
  have h := kurtz_charFun_le μ a b ha hb hV phi C s hcouple
  calc _ ≤ ‖(∫ ω, Complex.exp (Complex.I * (s * ((a ω - V * phi) / Real.sqrt V) : ℝ)) ∂μ)
          - ∫ ω, Complex.exp (Complex.I * (s * ((b ω - V * phi) / Real.sqrt V) : ℝ)) ∂μ‖
        + ‖(∫ ω, Complex.exp (Complex.I * (s * ((b ω - V * phi) / Real.sqrt V) : ℝ)) ∂μ) - χ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by rw [add_div]; linarith

/-- The first line of (7.2.67): `e^{isz} = e^{-isV^{1/2}φ} e^{isV^{-1/2}a}`. -/
theorem kurtz_phase (a V phi s : ℝ) (hV : 0 < V) :
    Complex.exp (Complex.I * (s * ((a - V * phi) / Real.sqrt V) : ℝ))
      = Complex.exp (-(Complex.I * (s * Real.sqrt V * phi : ℝ)))
        * Complex.exp (Complex.I * (s * (a / Real.sqrt V) : ℝ)) := by
  rw [← Complex.exp_add]
  congr 1
  have : s * ((a - V * phi) / Real.sqrt V) = -(s * Real.sqrt V * phi) + s * (a / Real.sqrt V) := by
    obtain ⟨σ, hσ, rfl⟩ : ∃ σ : ℝ, 0 < σ ∧ V = σ ^ 2 :=
      ⟨Real.sqrt V, Real.sqrt_pos.2 hV, (Real.sq_sqrt hV.le).symm⟩
    rw [Real.sqrt_sq hσ.le]; field_simp; ring
  rw [this]; push_cast; ring

end Kurtz

/-! ### §7.2.5: critical fluctuations -/

/-- **(7.2.73)**: `(1 - q)(1 - μ) = 1 - 2μ` exactly when `μ = q/(q+1)`. -/
theorem critical_exponent (q μ : ℝ) (hq : q + 1 ≠ 0) :
    (1 - q) * (1 - μ) = 1 - 2 * μ ↔ μ = q / (q + 1) := by
  constructor
  · intro h; field_simp; linarith
  · intro h; subst h; field_simp; ring

/-- (7.2.71)–(7.2.77): with `θ = Ω^{1/(q+1)}` and `μ = q/(q+1)`, the scales of the critical
expansion are `Ω = θ^{q+1}`, `Ω^μ = θ^q`, `Ω^{1-μ} = θ`, and the slow time factor is
`Ω^{-(q-1)/(q+1)} = θ^{-(q-1)}`; for `q = 3` it is `Ω^{-1/2}` (7.2.77). -/
theorem critical_scales {Ω : ℝ} (hΩ : 0 < Ω) (q : ℕ) :
    (Ω ^ (1 / ((q : ℝ) + 1))) ^ (q + 1) = Ω ∧
    Ω ^ ((q : ℝ) / (q + 1)) = (Ω ^ (1 / ((q : ℝ) + 1))) ^ q ∧
    Ω ^ (1 - (q : ℝ) / (q + 1)) = Ω ^ (1 / ((q : ℝ) + 1)) ∧
    Ω ^ (-(((q : ℝ) - 1) / (q + 1))) = ((Ω ^ (1 / ((q : ℝ) + 1))) ^ (q - 1 : ℝ))⁻¹ := by
  have hq : (q : ℝ) + 1 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hΩ.le]; push_cast; rw [one_div_mul_cancel hq]
    exact Real.rpow_one Ω
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hΩ.le]; congr 1; field_simp
  · congr 1; field_simp; ring
  · rw [← Real.rpow_mul hΩ.le, ← Real.rpow_neg hΩ.le]; congr 1; field_simp

theorem critical_slow_time_cubic (Ω : ℝ) :
    Ω ^ (-(((3 : ℕ) : ℝ) - 1) / ((3 : ℕ) + 1)) = Ω ^ (-(1 / 2 : ℝ)) := by
  congr 1; norm_num

variable {ι : Type*} (s : Finset ι) (r : ι → ℝ) (ψ : ι → ℝ → ℝ)

/-- The generator of the master equation in the critical scaling (7.2.70)–(7.2.71), at the
stationary point `φ(t) = φₛ`, on the slow time scale (7.2.75):
`θ^{q-1} Σ_j θ^{q+1} ψ_j(φₛ + u/θ) [f(u + r_j/θ^q) - f(u)]`, with `θ = Ω^{1/(q+1)}` so that
`Ω = θ^{q+1}`, `Ω^μ = θ^q`, `Ω^{μ-1} = θ⁻¹`. -/
def critGen (θ : ℝ) (q : ℕ) (phis : ℝ) (D : ℕ → ℝ → ℝ) (u : ℝ) : ℝ :=
  θ ^ (q - 1) * ∑ j ∈ s, θ ^ (q + 1) * ψ j (phis + u / θ) * (D 0 (u + r j / θ ^ q) - D 0 u)

/-- The generator of the critical Fokker–Planck equation (7.2.74) (on the slow time `τ`):
`(A/q!) uᵠ f' + ½ B f''`, with `A = α̃₁^{(q)}(φₛ)` and `B = α̃₂(φₛ)`. -/
def critLim (A B : ℝ) (q : ℕ) (u f₁ f₂ : ℝ) : ℝ := A / (q ! : ℝ) * u ^ q * f₁ + (1 / 2) * B * f₂

/-- **Critical fluctuations with an explicit error (7.2.71)–(7.2.75).**  Suppose that near
`φₛ`, `α̃₁(φₛ + h) = (A/q!) hᵠ + O(K |h|^{q+1})` (the first `q - 1` derivatives of `α̃₁` vanish at
the stationary point, (7.2.68)) and that `α̃₂` varies by at most `L|h|`.  Then on test functions
with `|f'''| ≤ M`,
`|critGen - critLim| ≤ θ⁻¹ (K |u|^{q+1} |f'| + L |u| |f''|/2) + θ^{-q} M β̃₃(φₛ + u/θ)/6`,
i.e. `O(Ω^{-1/(q+1)})`. -/
theorem critGen_sub_critLim_le {θ : ℝ} (hθ : 0 < θ) {q : ℕ} (hq : 1 ≤ q) (phis u A K L M : ℝ)
    (D : ℕ → ℝ → ℝ) (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y)
    (hM : ∀ y, |D 3 y| ≤ M)
    (hT : |intMoment s r ψ 1 (phis + u / θ) - A / (q ! : ℝ) * (u / θ) ^ q| ≤ K * |u / θ| ^ (q + 1))
    (hL : |intMoment s r ψ 2 (phis + u / θ) - intMoment s r ψ 2 phis| ≤ L * |u / θ|) :
    |critGen s r ψ θ q phis D u - critLim A (intMoment s r ψ 2 phis) q u (D 1 u) (D 2 u)|
      ≤ (K * |u| ^ (q + 1) * |D 1 u| + L * |u| * |D 2 u| / 2) / θ
        + M / 6 * finAbsJumpMoment s r ψ (phis + u / θ) 3 / θ ^ q := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  set x := phis + u / θ
  set c : ι → ℝ → ℝ := fun j _ => θ ^ (p + 1 + 1) * ψ j x
  set r' : ι → ℝ := fun j => r j / θ ^ (p + 1)
  have key := finJumpGen_sub_finKM_le s r' c D 2 u M hD hM
  have hmom : ∀ k, finJumpMoment s r' c u k
      = θ ^ (p + 1 + 1) / (θ ^ (p + 1)) ^ k * intMoment s r ψ k x := by
    intro k
    simp only [finJumpMoment, intMoment, r', c, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [div_pow]; field_simp
  have habs : finAbsJumpMoment s r' c u 3
      = θ ^ (p + 1 + 1) / (θ ^ (p + 1)) ^ 3 * finAbsJumpMoment s r ψ x 3 := by
    simp only [finAbsJumpMoment, r', c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < θ ^ (p + 1 + 1)),
      abs_of_pos (by positivity : (0 : ℝ) < θ ^ (p + 1)), div_pow]
    field_simp
  set E := finJumpGen s r' c (D 0) u - finKM s r' c D 2 u
  have hG : critGen s r ψ θ (p + 1) phis D u = θ ^ p * finJumpGen s r' c (D 0) u := by
    simp only [critGen, finJumpGen, c, r', Nat.add_sub_cancel]; rfl
  have hJ : finJumpGen s r' c (D 0) u = E + finKM s r' c D 2 u := by simp only [E]; ring
  have hsplit : critGen s r ψ θ (p + 1) phis D u
        - critLim A (intMoment s r ψ 2 phis) (p + 1) u (D 1 u) (D 2 u)
      = θ ^ p * E
        + θ ^ (p + 1) * (intMoment s r ψ 1 x - A / ((p + 1)! : ℝ) * (u / θ) ^ (p + 1)) * D 1 u
        + (1 / 2) * (intMoment s r ψ 2 x - intMoment s r ψ 2 phis) * D 2 u := by
    rw [hG, hJ]
    clear_value E
    simp only [finKM, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hmom, critLim]
    rw [div_pow]
    norm_num [Nat.factorial]
    field_simp
    ring
  rw [hsplit]
  have hE : θ ^ p * |E| ≤ M / 6 * finAbsJumpMoment s r ψ x 3 / θ ^ (p + 1) := by
    calc θ ^ p * |E| ≤ θ ^ p * (M / ((2 + 1)! : ℝ) * finAbsJumpMoment s r' c u (2 + 1)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by rw [habs]; norm_num [Nat.factorial]; field_simp; ring
  have hT' : |θ ^ (p + 1) * (intMoment s r ψ 1 x - A / ((p + 1)! : ℝ) * (u / θ) ^ (p + 1))|
      ≤ K * |u| ^ (p + 1 + 1) / θ := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc θ ^ (p + 1) * |intMoment s r ψ 1 x - A / ((p + 1)! : ℝ) * (u / θ) ^ (p + 1)|
        ≤ θ ^ (p + 1) * (K * |u / θ| ^ (p + 1 + 1)) := mul_le_mul_of_nonneg_left hT (by positivity)
      _ = _ := by rw [abs_div, abs_of_pos hθ, div_pow]; field_simp; ring
  have hL' : |intMoment s r ψ 2 x - intMoment s r ψ 2 phis| ≤ L * |u| / θ := by
    calc _ ≤ L * |u / θ| := hL
      _ = _ := by rw [abs_div, abs_of_pos hθ]; ring
  calc |θ ^ p * E + θ ^ (p + 1) * (intMoment s r ψ 1 x - A / ((p + 1)! : ℝ) * (u / θ) ^ (p + 1))
          * D 1 u + 1 / 2 * (intMoment s r ψ 2 x - intMoment s r ψ 2 phis) * D 2 u|
      ≤ θ ^ p * |E| + |θ ^ (p + 1) * (intMoment s r ψ 1 x - A / ((p + 1)! : ℝ)
          * (u / θ) ^ (p + 1))| * |D 1 u|
        + 1 / 2 * |intMoment s r ψ 2 x - intMoment s r ψ 2 phis| * |D 2 u| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [abs_mul, abs_of_pos (by positivity)]
        · rw [abs_mul]
        · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ M / 6 * finAbsJumpMoment s r ψ x 3 / θ ^ (p + 1) + K * |u| ^ (p + 1 + 1) / θ * |D 1 u|
        + 1 / 2 * (L * |u| / θ) * |D 2 u| := by
        gcongr
    _ = _ := by ring

/-- **(7.2.76)**: if `P(τ, u)` solves the critical equation (7.2.74),
`∂_τ P = -(A/q!) ∂_u(uᵠ P) + ½ B ∂_u² P` (given via `F = (A/q!) uᵠ P`, `G = B P` and their
derivatives), and `d/dτ` commutes with `∫ du` (`hswap`), then
`d⟨u⟩/dτ = (A/q!) ⟨uᵠ⟩` — not the linearised deterministic equation. -/
theorem critical_mean_eq (A B : ℝ) (q : ℕ) (P : ℝ → ℝ → ℝ) (τ : ℝ) {F' G' G'' : ℝ → ℝ}
    (hF : ∀ u, HasDerivAt (fun u => A / (q ! : ℝ) * u ^ q * P τ u) (F' u) u)
    (hG : ∀ u, HasDerivAt (fun u => B * P τ u) (G' u) u) (hG' : ∀ u, HasDerivAt G' (G'' u) u)
    (iF : ∀ i ≤ 1, Integrable (fun u => u ^ i * (A / (q ! : ℝ) * u ^ q * P τ u)))
    (iF' : Integrable (fun u => u * F' u))
    (iG : ∀ i ≤ 1, Integrable (fun u => u ^ i * (B * P τ u)))
    (iG' : ∀ i ≤ 1, Integrable (fun u => u ^ i * G' u)) (iG'' : Integrable (fun u => u * G'' u))
    (hswap : HasDerivAt (fun τ => ∫ u, u * P τ u) (∫ u, u * (-F' u + (1 / 2) * G'' u)) τ) :
    HasDerivAt (fun τ => ∫ u, u * P τ u) (A / (q ! : ℝ) * ∫ u, u ^ q * P τ u) τ := by
  have h := integral_pow_mul_fp 1 hF hG hG' iF (by simpa using iF') iG iG' (by simpa using iG'')
  simp only [pow_one, Nat.cast_one, sub_self, mul_zero, zero_div, zero_mul, add_zero, one_mul,
    Nat.sub_self, pow_zero] at h
  rw [h] at hswap
  rw [← integral_const_mul]
  simpa only [mul_assoc] using hswap

/-! ### The cubic critical point (7.2.69) -/

/-- **(7.2.69)**: for the reaction of §7.1.3, `α̃₁(y) = k(B y² + p - y³ - R y)`, at the critical
parameters `B = 3φₛ`, `R = 3φₛ²`, `p = φₛ³` one has `α̃₁(y) = -k(y - φₛ)³`, so that
`α̃₁(φₛ) = α̃₁'(φₛ) = α̃₁''(φₛ) = 0` and `q = 3` with `α̃₁'''(φₛ) = -6k`. -/
theorem critical_cubic (k phis y : ℝ) :
    k * (3 * phis * y ^ 2 + phis ^ 3 - y ^ 3 - 3 * phis ^ 2 * y) = -k * (y - phis) ^ 3 := by
  ring

/-- Critical slowing down: the deterministic equation (7.2.69) `ẏ = -k(y - φₛ)³` is solved by
`y(t) = φₛ + (y₀ - φₛ)/√(1 + 2k(y₀ - φₛ)² t)`, which decays only algebraically. -/
theorem critical_cubic_solution (k phis y₀ t : ℝ) (ht : 0 < 1 + 2 * k * (y₀ - phis) ^ 2 * t) :
    HasDerivAt (fun t => phis + (y₀ - phis) / Real.sqrt (1 + 2 * k * (y₀ - phis) ^ 2 * t))
      (-k * ((y₀ - phis) / Real.sqrt (1 + 2 * k * (y₀ - phis) ^ 2 * t)) ^ 3) t := by
  set w := y₀ - phis
  have hlin : HasDerivAt (fun t => 1 + 2 * k * w ^ 2 * t) (2 * k * w ^ 2) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * k * w ^ 2)).const_add 1
  have hsq := hlin.sqrt ht.ne'
  have hs0 : 0 < Real.sqrt (1 + 2 * k * w ^ 2 * t) := Real.sqrt_pos.2 ht
  have := (hsq.inv hs0.ne').const_mul w |>.const_add phis
  convert this using 1
  field_simp

/-- The intensive rates of the reaction of §7.1.3 (`A + 2X ⇌ 3X`, `A ⇌ X`) at the critical
point: `ψ₊(y) = k(3φₛ y² + φₛ³)` (jump `+1`), `ψ₋(y) = k(y³ + 3φₛ² y)` (jump `-1`). -/
def cubicPsi (k phis : ℝ) : Bool → ℝ → ℝ := fun b y =>
  if b then k * (3 * phis * y ^ 2 + phis ^ 3) else k * (y ^ 3 + 3 * phis ^ 2 * y)

theorem cubic_intMoment_one (k phis y : ℝ) :
    intMoment Finset.univ pmOne (cubicPsi k phis) 1 y = -k * (y - phis) ^ 3 := by
  simp [intMoment, finJumpMoment, cubicPsi, pmOne]; ring

theorem cubic_intMoment_two (k phis y : ℝ) :
    intMoment Finset.univ pmOne (cubicPsi k phis) 2 y = k * (y + phis) ^ 3 := by
  simp [intMoment, finJumpMoment, cubicPsi, pmOne]; ring

/-- **A non-degenerate instance of `critGen_sub_critLim_le`** (`q = 3`, (7.2.77)): for the
critical cubic reaction with `k > 0`, `θ ≥ 1`, the slow-time generator differs from
`-k u³ f' + 4kφₛ³ f''` (the generator of (7.2.74), `α̃₁'''/3! = -k`, `α̃₂(φₛ) = 8kφₛ³`) by at most
`θ⁻¹ · 3k(2|φₛ| + |u|)² |u| |f''|/2 + θ⁻³ M β̃₃/6`. -/
theorem cubic_critGen_sub_critLim_le (k phis : ℝ) (hk : 0 < k) {θ : ℝ} (hθ : 1 ≤ θ) (u M : ℝ)
    (D : ℕ → ℝ → ℝ) (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y)
    (hM : ∀ y, |D 3 y| ≤ M) :
    |critGen Finset.univ pmOne (cubicPsi k phis) θ 3 phis D u
        - critLim (-6 * k) (8 * k * phis ^ 3) 3 u (D 1 u) (D 2 u)|
      ≤ (3 * k * (2 * |phis| + |u|) ^ 2 * |u| * |D 2 u| / 2) / θ
        + M / 6 * finAbsJumpMoment Finset.univ pmOne (cubicPsi k phis) (phis + u / θ) 3 / θ ^ 3 := by
  have hθ0 : 0 < θ := by linarith
  have h := critGen_sub_critLim_le Finset.univ pmOne (cubicPsi k phis) hθ0 (q := 3) (by norm_num)
    phis u (-6 * k) 0 (3 * k * (2 * |phis| + |u|) ^ 2) M D hD hM
    (by rw [cubic_intMoment_one]; norm_num [Nat.factorial]; ring_nf)
    (by
      rw [cubic_intMoment_two, cubic_intMoment_two]
      have hu : |u / θ| ≤ |u| := by
        rw [abs_div, abs_of_pos hθ0]; exact div_le_self (abs_nonneg _) hθ
      have e : k * (phis + u / θ + phis) ^ 3 - k * (phis + phis) ^ 3
          = k * (u / θ) * ((2 * phis + u / θ) ^ 2 + (2 * phis + u / θ) * (2 * phis)
            + (2 * phis) ^ 2) := by ring
      rw [e, abs_mul, abs_mul, abs_of_pos hk]
      have hb : |(2 * phis + u / θ) ^ 2 + (2 * phis + u / θ) * (2 * phis) + (2 * phis) ^ 2|
          ≤ 3 * (2 * |phis| + |u|) ^ 2 := by
        have h1 : |2 * phis + u / θ| ≤ 2 * |phis| + |u| := by
          calc _ ≤ |2 * phis| + |u / θ| := abs_add_le _ _
            _ ≤ _ := by rw [abs_mul, abs_two]; linarith
        have h2 : |2 * phis| ≤ 2 * |phis| + |u| := by rw [abs_mul, abs_two]; linarith [abs_nonneg u]
        calc _ ≤ |(2 * phis + u / θ) ^ 2| + |(2 * phis + u / θ) * (2 * phis)| + |(2 * phis) ^ 2| :=
              abs_add_three _ _ _
          _ = |2 * phis + u / θ| ^ 2 + |2 * phis + u / θ| * |2 * phis| + |2 * phis| ^ 2 := by
              rw [abs_pow, abs_mul, abs_pow]
          _ ≤ (2 * |phis| + |u|) ^ 2 + (2 * |phis| + |u|) * (2 * |phis| + |u|)
              + (2 * |phis| + |u|) ^ 2 := by
              gcongr
          _ = _ := by ring
      calc k * |u / θ| * |(2 * phis + u / θ) ^ 2 + (2 * phis + u / θ) * (2 * phis) + (2 * phis) ^ 2|
          ≤ k * |u / θ| * (3 * (2 * |phis| + |u|) ^ 2) := by gcongr
        _ = _ := by ring)
  rw [cubic_intMoment_two, show k * (phis + phis) ^ 3 = 8 * k * phis ^ 3 by ring] at h
  simpa using h

end Gardiner
