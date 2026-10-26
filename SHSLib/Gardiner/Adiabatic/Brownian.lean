/-
# Brownian motion: Kramers versus Smoluchowski, with rates

Gardiner, *Handbook of Stochastic Methods*, §6.4, (6.4.1)–(6.4.18): free and harmonically bound
Brownian motion with relaxation time `τ = m/β`, `D = kT/β`, and its Smoluchowski limit.

In the variables of (6.4.12) and (6.4.15), with the Smoluchowski drift `F(x) = -V'(x)/β`, the
Kramers backward generator is `v ∂ₓ + ((F(x) - v)/τ) ∂ᵥ + (D/τ²) ∂ᵥ²` and the Smoluchowski
generator (6.4.17)–(6.4.18) is `F ∂ₓ + D ∂ₓ²`.  For `F(x) = -kx` (harmonic potential
`V = ½βk x²`; `k = 0` is free motion) the moment equations close:

`m₁' = m₂`, `τm₂' = -km₁ - m₂`,
`S' = 2X`, `τX' = τV - kS - X`, `τV' = -2kX - 2V + 2D/τ`

for `m₁ = ⟨x⟩`, `m₂ = ⟨v⟩`, `S = ⟨x²⟩`, `X = ⟨xv⟩`, `V = ⟨v²⟩`.  These are taken as hypotheses
(they are the Kramers equation tested against `x, v, x², xv, v²`, the exchange of `d/dt` and
`∫` being the only step not proved here, as in `Gardiner.mlna_exact`).  The initial velocity is
thermalised, (6.4.48)–(6.4.49): `⟨v⟩ = 0`, `⟨xv⟩ = 0`, `⟨v²⟩ = D/τ`.

**Approximation guarantees** (all uniform in `t ≥ 0`):

* `Gardiner.Adiabatic.free_kramers_moments`, `Gardiner.Adiabatic.free_variance_rate`: for free
  motion the mean is exact and `Var_K(t) = Var(0) + 2D(t - τ(1 - e^{-t/τ}))`, so
  `0 ≤ Var_S(t) - Var_K(t) ≤ 2Dτ` with the Smoluchowski value `Var_S(t) = Var(0) + 2Dt`
  (6.4.14).  The same computation is the OU-driven white-noise limit (6.4.6)–(6.4.10), where
  `v = √(2D) η` (`Gardiner.Adiabatic.ouDriven_variance_rate`).
* `Gardiner.Adiabatic.harmonic_mean_rate`: `|⟨x⟩_K(t) - ⟨x⟩(0)e^{-kt}| ≤ 4kτ|⟨x⟩(0)|`
  when `4kτ ≤ 1`.
* `Gardiner.Adiabatic.harmonic_variance_rate`:
  `|Var_K(t) - Var_S(t)| ≤ 8kτ |Var(0) - D/k|` when `4kτ < 1`, where
  `Var_S(t) = D/k + (Var(0) - D/k)e^{-2kt}` is the Smoluchowski (Ornstein–Uhlenbeck) variance.
* `Gardiner.Adiabatic.harmonic_stationary`: the stationary position variance is `D/k` for every
  `τ`, exactly the Smoluchowski value.

The proofs use a comparison lemma (`Gardiner.Adiabatic.decay_compare`), an energy estimate
(`k⟨x⟩² + τ⟨v⟩²` is nonincreasing) and the slaving variable `⟨v⟩ + k⟨x⟩` (the deviation of the
fast variable from its adiabatic value `F(x)`, cf. (6.4.16)).
-/
import SHSLib.Gardiner.Approx.ChemicalLNA

open Filter Topology Set

noncomputable section

namespace Gardiner.Adiabatic

/-! ### A comparison lemma -/

/-- **Comparison principle.**  If `y' - ψ' ≤ -k(y - ψ)` on `[0, ∞)` and `y(0) ≤ ψ(0)`, then
`y ≤ ψ` on `[0, ∞)`. -/
theorem decay_compare {y y' ψ ψ' : ℝ → ℝ} (k : ℝ) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (h : ∀ t, 0 ≤ t → y' t - ψ' t ≤ -k * (y t - ψ t))
    (h0 : y 0 ≤ ψ 0) {t : ℝ} (ht : 0 ≤ t) : y t ≤ ψ t := by
  set φ : ℝ → ℝ := fun t => Real.exp (k * t) * (y t - ψ t)
  have hφ : ∀ t, HasDerivAt φ (Real.exp (k * t) * (k * (y t - ψ t) + (y' t - ψ' t))) t := by
    intro t
    have he : HasDerivAt (fun t => Real.exp (k * t)) (Real.exp (k * t) * k) t := by
      simpa using ((hasDerivAt_id t).const_mul k).exp
    convert he.mul ((hy t).sub (hψ t)) using 1; simp only [Pi.sub_apply]; ring
  have hanti : AntitoneOn φ (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun t _ => (hφ t).continuousAt.continuousWithinAt
    · exact fun t _ => (hφ t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hφ t).deriv]
      have := h t (le_of_lt ht)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have h1 : φ t ≤ φ 0 := hanti self_mem_Ici ht ht
  have h2 : φ 0 = y 0 - ψ 0 := by simp [φ]
  have h3 : Real.exp (k * t) * (y t - ψ t) ≤ 0 := by
    have : φ t ≤ 0 := by linarith
    simpa [φ] using this
  by_contra hc
  push_neg at hc
  have := mul_pos (Real.exp_pos (k * t)) (sub_pos.2 hc)
  linarith

/-- `|y| ≤ ψ` from the two one-sided comparisons. -/
theorem abs_decay_compare {y y' ψ ψ' : ℝ → ℝ} (k : ℝ) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (h₁ : ∀ t, 0 ≤ t → y' t - ψ' t ≤ -k * (y t - ψ t))
    (h₂ : ∀ t, 0 ≤ t → -y' t - ψ' t ≤ -k * (-y t - ψ t))
    (h0 : |y 0| ≤ ψ 0) {t : ℝ} (ht : 0 ≤ t) : |y t| ≤ ψ t := by
  refine abs_le.2 ⟨?_, decay_compare k hy hψ h₁ (abs_le.1 h0).2 ht⟩
  have := decay_compare (y := fun t => -y t) k (fun t => (hy t).neg) hψ h₂
    (by linarith [(abs_le.1 h0).1]) ht
  linarith

/-! ### Free Brownian motion and the OU-driven white-noise limit -/

/-- **Free Brownian motion, exact moments.**  For `k = 0` and thermalised initial velocity, the
Kramers moments are `⟨x⟩(t) = ⟨x⟩(0)`, `⟨v⟩ = 0`, `⟨v²⟩ = D/τ`, `⟨xv⟩ = D(1 - e^{-t/τ})` and
`⟨x²⟩(t) = ⟨x²⟩(0) + 2D(t - τ(1 - e^{-t/τ}))`. -/
theorem free_kramers_moments {τ D : ℝ} (hτ : 0 < τ) (m₁ m₂ S X V : ℝ → ℝ)
    (hm₁ : ∀ t, HasDerivAt m₁ (m₂ t) t) (hm₂ : ∀ t, HasDerivAt m₂ (-m₂ t / τ) t)
    (hS : ∀ t, HasDerivAt S (2 * X t) t) (hX : ∀ t, HasDerivAt X ((τ * V t - X t) / τ) t)
    (hV : ∀ t, HasDerivAt V ((-2 * V t + 2 * D / τ) / τ) t)
    (h₂ : m₂ 0 = 0) (hX0 : X 0 = 0) (hV0 : V 0 = D / τ) (t : ℝ) :
    m₁ t = m₁ 0 ∧ m₂ t = 0 ∧ V t = D / τ ∧ X t = D * (1 - Real.exp (-t / τ)) ∧
      S t = S 0 + 2 * D * (t - τ * (1 - Real.exp (-t / τ))) := by
  have hc : Continuous fun _ : ℝ => -1 / τ := continuous_const
  -- `⟨v⟩ = 0`
  have hm2 : m₂ = fun _ => 0 := linear_ode_unique (fun _ => -1 / τ) (fun _ => 0) hc
    continuous_const m₂ (fun _ => 0) (fun t => by convert hm₂ t using 1; ring)
    (fun t => by simpa using hasDerivAt_const t (0 : ℝ)) h₂
  -- `⟨v²⟩ = D/τ`
  have hVc : V = fun _ => D / τ := linear_ode_unique (fun _ => -2 / τ) (fun _ => 2 * D / τ ^ 2)
    continuous_const continuous_const V (fun _ => D / τ) (fun t => by
      convert hV t using 1; field_simp)
    (fun t => by convert hasDerivAt_const t (D / τ) using 1; field_simp; ring) hV0
  -- `⟨xv⟩`
  have hXd : ∀ t, HasDerivAt (fun t => D * (1 - Real.exp (-t / τ)))
      (D * (Real.exp (-t / τ) / τ)) t := by
    intro t
    have h := ((hasDerivAt_id t).neg.div_const τ).exp
    convert ((hasDerivAt_const t (1 : ℝ)).sub h).const_mul D using 1
    simp; ring
  have hXc : X = fun t => D * (1 - Real.exp (-t / τ)) := linear_ode_unique (fun _ => -1 / τ)
    (fun _ => D / τ) continuous_const continuous_const X _
    (fun t => by
      convert hX t using 1
      rw [show V t = D / τ from congrFun hVc t]; field_simp; ring)
    (fun t => by convert hXd t using 1; field_simp; ring) (by simp [hX0])
  -- `⟨x⟩` and `⟨x²⟩`
  have hm1 : m₁ t = m₁ 0 := by
    have := is_const_of_deriv_eq_zero (f := m₁) (fun t => (hm₁ t).differentiableAt)
      (fun t => by rw [(hm₁ t).deriv, congrFun hm2 t]) t 0
    exact this
  have hSd : ∀ t, HasDerivAt (fun t => S t - 2 * D * (t - τ * (1 - Real.exp (-t / τ)))) 0 t := by
    intro t
    have h := ((hasDerivAt_id t).neg.div_const τ).exp
    have h2 := ((hasDerivAt_id t).sub (((hasDerivAt_const t (1 : ℝ)).sub h).const_mul τ)).const_mul
      (2 * D)
    convert (hS t).sub h2 using 1
    rw [congrFun hXc t]; simp; field_simp; ring
  have hSc := is_const_of_deriv_eq_zero (fun t => (hSd t).differentiableAt)
    (fun t => (hSd t).deriv) t 0
  simp only [neg_zero, zero_div, Real.exp_zero, sub_self, mul_zero, sub_zero] at hSc
  refine ⟨hm1, congrFun hm2 t, congrFun hVc t, congrFun hXc t, ?_⟩
  linarith

/-- `0 ≤ τ(1 - e^{-t/τ}) ≤ τ` for `t ≥ 0`. -/
lemma tau_one_sub_exp_bounds {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    0 ≤ τ * (1 - Real.exp (-t / τ)) ∧ τ * (1 - Real.exp (-t / τ)) ≤ τ := by
  have h1 : Real.exp (-t / τ) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ t / τ := div_nonneg ht hτ.le
    rw [neg_div]; linarith)
  have h2 : 0 < Real.exp (-t / τ) := Real.exp_pos _
  constructor <;> nlinarith

/-- **Free Brownian motion: the Smoluchowski variance with rate `O(τ)`.**  With
`Var(t) = ⟨x²⟩ - ⟨x⟩²`, the Kramers variance and the Smoluchowski variance
`Var(0) + 2Dt` of (6.4.14) satisfy `0 ≤ Var_S(t) - Var_K(t) ≤ 2Dτ` for all `t ≥ 0`. -/
theorem free_variance_rate {τ D : ℝ} (hτ : 0 < τ) (hD : 0 ≤ D) (m₁ m₂ S X V : ℝ → ℝ)
    (hm₁ : ∀ t, HasDerivAt m₁ (m₂ t) t) (hm₂ : ∀ t, HasDerivAt m₂ (-m₂ t / τ) t)
    (hS : ∀ t, HasDerivAt S (2 * X t) t) (hX : ∀ t, HasDerivAt X ((τ * V t - X t) / τ) t)
    (hV : ∀ t, HasDerivAt V ((-2 * V t + 2 * D / τ) / τ) t)
    (h₂ : m₂ 0 = 0) (hX0 : X 0 = 0) (hV0 : V 0 = D / τ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ((S 0 - m₁ 0 ^ 2) + 2 * D * t) - (S t - m₁ t ^ 2) ∧
      ((S 0 - m₁ 0 ^ 2) + 2 * D * t) - (S t - m₁ t ^ 2) ≤ 2 * D * τ := by
  obtain ⟨h1, -, -, -, h5⟩ :=
    free_kramers_moments hτ m₁ m₂ S X V hm₁ hm₂ hS hX hV h₂ hX0 hV0 t
  obtain ⟨b1, b2⟩ := tau_one_sub_exp_bounds hτ ht
  rw [h1, h5]
  constructor <;> nlinarith

/-- **(6.4.6)–(6.4.10): the OU-driven white-noise limit.**  If `dx/dt = √(2D) η(t, τ)` with `η` the
stationary Ornstein–Uhlenbeck process of (6.4.6) (`dη = -η/τ dt + τ⁻¹dW`, `⟨η²⟩ = 1/(2τ)`), then
`v = √(2D) η` obeys the free Kramers moment equations with thermal variance `D/τ`, so the
variance of `x(t)` is within `2Dτ` of the white-noise value `2Dt` of (6.4.10). -/
theorem ouDriven_variance_rate {τ D : ℝ} (hτ : 0 < τ) (hD : 0 ≤ D) (m₁ mη S Xη Vη : ℝ → ℝ)
    (hm₁ : ∀ t, HasDerivAt m₁ (Real.sqrt (2 * D) * mη t) t)
    (hmη : ∀ t, HasDerivAt mη (-mη t / τ) t)
    (hS : ∀ t, HasDerivAt S (2 * (Real.sqrt (2 * D) * Xη t)) t)
    (hX : ∀ t, HasDerivAt Xη ((τ * Real.sqrt (2 * D) * Vη t - Xη t) / τ) t)
    (hV : ∀ t, HasDerivAt Vη ((-2 * Vη t + 1 / τ) / τ) t)
    (h₂ : mη 0 = 0) (hX0 : Xη 0 = 0) (hV0 : Vη 0 = 1 / (2 * τ)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ((S 0 - m₁ 0 ^ 2) + 2 * D * t) - (S t - m₁ t ^ 2) ∧
      ((S 0 - m₁ 0 ^ 2) + 2 * D * t) - (S t - m₁ t ^ 2) ≤ 2 * D * τ := by
  set c := Real.sqrt (2 * D)
  have hc2 : c ^ 2 = 2 * D := Real.sq_sqrt (by linarith)
  refine free_variance_rate hτ hD m₁ (fun t => c * mη t) S (fun t => c * Xη t)
    (fun t => c ^ 2 * Vη t) hm₁ (fun t => by convert (hmη t).const_mul c using 1; ring) hS
    (fun t => by convert (hX t).const_mul c using 1; field_simp)
    (fun t => by convert (hV t).const_mul (c ^ 2) using 1; rw [hc2]; field_simp)
    (by simp [h₂]) (by simp [hX0]) (by show c ^ 2 * Vη 0 = D / τ; rw [hV0, hc2]; field_simp) ht

/-! ### Harmonically bound Brownian motion: the mean -/

section Harmonic

variable {τ k : ℝ} (m₁ m₂ : ℝ → ℝ)

/-- The energy `k⟨x⟩² + τ⟨v⟩²` of the mean motion is nonincreasing, hence `|⟨x⟩(t)| ≤ |⟨x⟩(0)|`
when `⟨v⟩(0) = 0`. -/
theorem harmonic_mean_bounded (hτ : 0 < τ) (hk : 0 < k)
    (hm₁ : ∀ t, HasDerivAt m₁ (m₂ t) t) (hm₂ : ∀ t, HasDerivAt m₂ ((-k * m₁ t - m₂ t) / τ) t)
    (h₂ : m₂ 0 = 0) {t : ℝ} (ht : 0 ≤ t) : |m₁ t| ≤ |m₁ 0| := by
  have hE := decay_compare (y := fun t => k * m₁ t ^ 2 + τ * m₂ t ^ 2)
    (y' := fun t => -2 * m₂ t ^ 2) (ψ := fun _ => k * m₁ 0 ^ 2) (ψ' := fun _ => 0) 0
    (fun t => by
      convert (((hm₁ t).pow 2).const_mul k).add (((hm₂ t).pow 2).const_mul τ) using 1
      field_simp; ring)
    (fun t => hasDerivAt_const t _) (fun t _ => by simp; positivity) (by simp [h₂]) ht
  have : m₁ t ^ 2 ≤ m₁ 0 ^ 2 := by
    have h' : k * m₁ t ^ 2 ≤ k * m₁ 0 ^ 2 := by nlinarith [sq_nonneg (m₂ t)]
    exact le_of_mul_le_mul_left h' hk
  exact sq_le_sq.1 this

/-- **The mean of harmonically bound Brownian motion: Smoluchowski limit with rate `O(kτ)`.**
If `2kτ < 1` and `⟨v⟩(0) = 0` then for `t ≥ 0`
`|⟨x⟩_K(t) - ⟨x⟩(0) e^{-kt}| ≤ kτ (1/(1 - 2kτ) + 1/(1 - kτ)) |⟨x⟩(0)|`;
`⟨x⟩(0)e^{-kt}` is the mean of the Smoluchowski equation (6.4.18). -/
theorem harmonic_mean_rate_exact (hτ : 0 < τ) (hk : 0 < k) (hkτ : 2 * k * τ < 1)
    (hm₁ : ∀ t, HasDerivAt m₁ (m₂ t) t) (hm₂ : ∀ t, HasDerivAt m₂ ((-k * m₁ t - m₂ t) / τ) t)
    (h₂ : m₂ 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    |m₁ t - m₁ 0 * Real.exp (-k * t)|
      ≤ k * τ * (1 / (1 - 2 * k * τ) + 1 / (1 - k * τ)) * |m₁ 0| := by
  set a := (1 - k * τ) / τ with ha
  have ha0 : 0 < a := div_pos (by nlinarith) hτ
  have hak : 0 < a - k := by rw [ha, div_sub' hτ.ne']; exact div_pos (by nlinarith) hτ
  set G := k ^ 2 * |m₁ 0|
  set z0 := |k * m₁ 0|
  have hbd := fun t (ht : 0 ≤ t) => harmonic_mean_bounded m₁ m₂ hτ hk hm₁ hm₂ h₂ ht
  -- the slaving variable `z = ⟨v⟩ + k⟨x⟩` decays like `e^{-at}` up to `G/a`
  have hz : ∀ s, 0 ≤ s → |m₂ s + k * m₁ s| ≤ z0 * Real.exp (-a * s) + G / a := by
    intro s hs
    have hexp : ∀ t, HasDerivAt (fun t => Real.exp (-a * t)) (-a * Real.exp (-a * t)) t := by
      intro t; simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-a)).exp
    refine abs_decay_compare (y := fun t => m₂ t + k * m₁ t)
      (y' := fun t => -a * (m₂ t + k * m₁ t) - k ^ 2 * m₁ t)
      (ψ := fun t => z0 * Real.exp (-a * t) + G / a)
      (ψ' := fun t => z0 * (-a * Real.exp (-a * t))) a
      (fun t => by convert (hm₂ t).add ((hm₁ t).const_mul k) using 1; rw [ha]; field_simp; ring)
      (fun t => ((hexp t).const_mul z0).add_const _)
      (fun t ht => by
        have := hbd t ht
        have h1 : -(k ^ 2 * m₁ t) ≤ G := by
          have := neg_abs_le (m₁ t); have := abs_nonneg (m₁ t); nlinarith
        have h2 : a * (G / a) = G := mul_div_cancel₀ G ha0.ne'
        beta_reduce
        nlinarith)
      (fun t ht => by
        have := hbd t ht
        have h1 : k ^ 2 * m₁ t ≤ G := by
          have := le_abs_self (m₁ t); nlinarith
        have h2 : a * (G / a) = G := mul_div_cancel₀ G ha0.ne'
        beta_reduce
        nlinarith)
      (by simp [h₂, z0]; positivity) hs
  -- the error `e = ⟨x⟩ - ⟨x⟩(0)e^{-kt}` obeys `e' = -ke + z`
  set c₁ := z0 / (a - k)
  set c₂ := G / (a * k)
  have hexpa : ∀ t, HasDerivAt (fun t => Real.exp (-a * t)) (-a * Real.exp (-a * t)) t := by
    intro t; simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-a)).exp
  have hexpk : ∀ t, HasDerivAt (fun t => Real.exp (-k * t)) (-k * Real.exp (-k * t)) t := by
    intro t; simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-k)).exp
  have he := abs_decay_compare (y := fun t => m₁ t - m₁ 0 * Real.exp (-k * t))
    (y' := fun t => -k * (m₁ t - m₁ 0 * Real.exp (-k * t)) + (m₂ t + k * m₁ t))
    (ψ := fun t => c₁ * (1 - Real.exp (-a * t)) + c₂)
    (ψ' := fun t => c₁ * (a * Real.exp (-a * t))) k
    (fun t => by convert (hm₁ t).sub ((hexpk t).const_mul (m₁ 0)) using 1; ring)
    (fun t => by
      convert (((hasDerivAt_const t (1 : ℝ)).sub (hexpa t)).const_mul c₁).add_const c₂ using 1
      ring)
    (fun t ht => by
      have h1 := (abs_le.1 (hz t ht)).2
      have hc1 : c₁ * (a - k) = z0 := div_mul_cancel₀ _ hak.ne'
      have hc2 : k * c₂ = G / a := by simp only [c₂]; field_simp
      have : 0 ≤ k * c₁ := mul_nonneg hk.le (div_nonneg (abs_nonneg _) hak.le)
      nlinarith [Real.exp_pos (-a * t)])
    (fun t ht => by
      have h1 := (abs_le.1 (hz t ht)).1
      have hc1 : c₁ * (a - k) = z0 := div_mul_cancel₀ _ hak.ne'
      have hc2 : k * c₂ = G / a := by simp only [c₂]; field_simp
      have : 0 ≤ k * c₁ := mul_nonneg hk.le (div_nonneg (abs_nonneg _) hak.le)
      nlinarith [Real.exp_pos (-a * t)])
    (by simp only [mul_zero, Real.exp_zero, mul_one, sub_self, abs_zero]; positivity) ht
  refine he.trans ?_
  have hea : 0 < Real.exp (-a * t) := Real.exp_pos _
  have hc10 : 0 ≤ c₁ := div_nonneg (abs_nonneg _) hak.le
  calc c₁ * (1 - Real.exp (-a * t)) + c₂ ≤ c₁ + c₂ := by nlinarith
    _ = k * τ * (1 / (1 - 2 * k * τ) + 1 / (1 - k * τ)) * |m₁ 0| := by
        simp only [c₁, c₂, z0, G, ha, abs_mul, abs_of_pos hk]
        have h1 : 1 - 2 * k * τ ≠ 0 := by linarith
        have h2 : 1 - k * τ ≠ 0 := by nlinarith
        field_simp
        ring

/-- **(6.4.15)–(6.4.18), harmonic case, mean: rate `4kτ`.**  For `4kτ ≤ 1`,
`|⟨x⟩_K(t) - ⟨x⟩(0)e^{-kt}| ≤ 4kτ|⟨x⟩(0)|` for all `t ≥ 0`. -/
theorem harmonic_mean_rate (hτ : 0 < τ) (hk : 0 < k) (hkτ : 4 * k * τ ≤ 1)
    (hm₁ : ∀ t, HasDerivAt m₁ (m₂ t) t) (hm₂ : ∀ t, HasDerivAt m₂ ((-k * m₁ t - m₂ t) / τ) t)
    (h₂ : m₂ 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    |m₁ t - m₁ 0 * Real.exp (-k * t)| ≤ 4 * k * τ * |m₁ 0| := by
  refine (harmonic_mean_rate_exact m₁ m₂ hτ hk (by linarith) hm₁ hm₂ h₂ ht).trans ?_
  have hkt : 0 < k * τ := mul_pos hk hτ
  have h1 : 1 / (1 - 2 * k * τ) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : 1 / (1 - k * τ) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have := abs_nonneg (m₁ 0)
  calc k * τ * (1 / (1 - 2 * k * τ) + 1 / (1 - k * τ)) * |m₁ 0|
      ≤ k * τ * (2 + 2) * |m₁ 0| := by gcongr
    _ = 4 * k * τ * |m₁ 0| := by ring

end Harmonic

/-! ### Harmonically bound Brownian motion: the variance -/

section HarmonicVariance

/-- The mean propagator `μ(t)` (mean position for `⟨x⟩(0) = 1`, `⟨v⟩(0) = 0`), written with the
roots `λ± ` of `τλ² + λ + k = 0`. -/
def harmMu (lp lm t : ℝ) : ℝ := (lp * Real.exp (lm * t) - lm * Real.exp (lp * t)) / (lp - lm)

/-- `ν = μ'`, the mean velocity of the propagator. -/
def harmNu (lp lm t : ℝ) : ℝ := lp * lm * (Real.exp (lm * t) - Real.exp (lp * t)) / (lp - lm)

lemma hasDerivAt_exp_mul (c t : ℝ) :
    HasDerivAt (fun t => Real.exp (c * t)) (c * Real.exp (c * t)) t := by
  simpa [mul_comm] using ((hasDerivAt_id t).const_mul c).exp

/-- The propagator solves the mean equations `μ' = ν`, `τν' = -kμ - ν` whenever
`τ(λ₊ + λ₋) = -1` and `τλ₊λ₋ = k`. -/
lemma harm_mean_sol {τ k lp lm : ℝ} (hτ : 0 < τ) (hne : lp ≠ lm) (hs : τ * (lp + lm) = -1)
    (hp : τ * (lp * lm) = k) (t : ℝ) :
    HasDerivAt (harmMu lp lm) (harmNu lp lm t) t ∧
      HasDerivAt (harmNu lp lm) ((-k * harmMu lp lm t - harmNu lp lm t) / τ) t := by
  have hd : lp - lm ≠ 0 := sub_ne_zero.2 hne
  constructor
  · have := (((hasDerivAt_exp_mul lm t).const_mul lp).sub
      ((hasDerivAt_exp_mul lp t).const_mul lm)).div_const (lp - lm)
    convert this using 1
    simp only [harmNu]; ring
  · have := (((hasDerivAt_exp_mul lm t).sub (hasDerivAt_exp_mul lp t)).const_mul
      (lp * lm)).div_const (lp - lm)
    convert this using 1
    simp only [harmMu, harmNu]
    generalize Real.exp (lm * t) = Em
    generalize Real.exp (lp * t) = Ep
    rw [← hp, div_eq_iff hτ.ne', div_mul_eq_mul_div, eq_div_iff hd]
    field_simp
    linear_combination (-lp * lm * (Em - Ep)) * hs

/-- The linear map of the (co)variance equations
`(S, X, V) ↦ (2X, (τV - kS - X)/τ, (-2kX - 2V)/τ)`. -/
def covOp (τ k : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (2 * p.2.1, (τ * p.2.2 - k * p.1 - p.2.1) / τ,
        (-2 * k * p.2.1 - 2 * p.2.2) / τ)
      map_add' := fun p q => by ext <;> simp <;> ring
      map_smul' := fun r p => by ext <;> simp <;> ring }

@[simp] lemma covOp_apply (τ k : ℝ) (p : ℝ × ℝ × ℝ) :
    covOp τ k p = (2 * p.2.1, (τ * p.2.2 - k * p.1 - p.2.1) / τ,
      (-2 * k * p.2.1 - 2 * p.2.2) / τ) := rfl

/-- **Exact variance of harmonically bound Brownian motion.**  With thermalised initial
velocity, the Kramers variance is `Var(t) = D/k + (Var(0) - D/k) μ(t)²`, where `μ` is the mean
propagator (the covariance deviation is the rank-one matrix `c (μ, ν)(μ, ν)ᵀ`). -/
theorem harmonic_variance_exact {τ k D : ℝ} (hτ : 0 < τ) (hk : 0 < k)
    (lp lm : ℝ) (hne : lp ≠ lm) (hs : τ * (lp + lm) = -1) (hp : τ * (lp * lm) = k)
    (m₁ m₂ S X V : ℝ → ℝ)
    (hm₁ : ∀ t, HasDerivAt m₁ (m₂ t) t) (hm₂ : ∀ t, HasDerivAt m₂ ((-k * m₁ t - m₂ t) / τ) t)
    (hS : ∀ t, HasDerivAt S (2 * X t) t)
    (hX : ∀ t, HasDerivAt X ((τ * V t - k * S t - X t) / τ) t)
    (hV : ∀ t, HasDerivAt V ((-2 * k * X t - 2 * V t + 2 * D / τ) / τ) t)
    (hX0 : X 0 = m₁ 0 * m₂ 0) (hV0 : V 0 = D / τ + m₂ 0 ^ 2) (t : ℝ) :
    S t - m₁ t ^ 2 = D / k + ((S 0 - m₁ 0 ^ 2) - D / k) * harmMu lp lm t ^ 2 := by
  set c := (S 0 - m₁ 0 ^ 2) - D / k
  have hmu := fun t => (harm_mean_sol hτ hne hs hp t).1
  have hnu := fun t => (harm_mean_sol hτ hne hs hp t).2
  have hmu0 : harmMu lp lm 0 = 1 := by
    simp only [harmMu, mul_zero, Real.exp_zero, mul_one]; field_simp [sub_ne_zero.2 hne]
  have hnu0 : harmNu lp lm 0 = 0 := by simp [harmNu]
  -- covariances
  set C : ℝ → ℝ × ℝ × ℝ := fun t => (S t - m₁ t ^ 2, X t - m₁ t * m₂ t, V t - m₂ t ^ 2)
  set Cand : ℝ → ℝ × ℝ × ℝ := fun t => (D / k + c * harmMu lp lm t ^ 2,
    c * (harmMu lp lm t * harmNu lp lm t), D / τ + c * harmNu lp lm t ^ 2)
  have key := vec_linear_ode_unique (covOp τ k) (fun _ => (0, 0, 2 * D / τ ^ 2)) C Cand
    (fun t => by
      refine ((hS t).sub ((hm₁ t).pow 2)).prodMk (((hX t).sub ((hm₁ t).mul (hm₂ t))).prodMk
        ((hV t).sub ((hm₂ t).pow 2))) |>.congr_deriv ?_
      ext <;> simp [C] <;> field_simp <;> ring)
    (fun t => by
      refine ((((hmu t).pow 2).const_mul c).const_add (D / k)).prodMk
        ((((hmu t).mul (hnu t)).const_mul c).prodMk
        ((((hnu t).pow 2).const_mul c).const_add (D / τ))) |>.congr_deriv ?_
      ext <;> simp [Cand] <;> field_simp <;> ring)
    (by
      ext
      · simp [C, Cand, hmu0, c]
      · simp [C, Cand, hnu0, hX0]
      · simp [C, Cand, hnu0, hV0])
  have := congrArg Prod.fst (congrFun key t)
  simpa [C, Cand] using this

/-- The roots of `τλ² + λ + k = 0` for `4kτ < 1`. -/
lemma harm_roots {τ k : ℝ} (hτ : 0 < τ) (hkτ : 4 * k * τ < 1) :
    let lp := (-1 + Real.sqrt (1 - 4 * k * τ)) / (2 * τ)
    let lm := (-1 - Real.sqrt (1 - 4 * k * τ)) / (2 * τ)
    lp ≠ lm ∧ τ * (lp + lm) = -1 ∧ τ * (lp * lm) = k := by
  intro lp lm
  have hs : 0 < Real.sqrt (1 - 4 * k * τ) := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (1 - 4 * k * τ) ^ 2 = 1 - 4 * k * τ := Real.sq_sqrt (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp only [lp, lm] at h
    field_simp at h
    linarith
  · simp only [lp, lm]; field_simp; ring
  · simp only [lp, lm]
    generalize Real.sqrt (1 - 4 * k * τ) = r at hsq ⊢
    field_simp; linear_combination (-1) * hsq

/-- **(6.4.15)–(6.4.18), harmonic case, variance: rate `8kτ`.**  If `4kτ < 1` and the initial
velocity is thermalised, then for all `t ≥ 0`
`|Var_K(t) - Var_S(t)| ≤ 8kτ |Var(0) - D/k|`, where `Var_S(t) = D/k + (Var(0) - D/k)e^{-2kt}`
is the variance of the Smoluchowski (Ornstein–Uhlenbeck) equation (6.4.18). -/
theorem harmonic_variance_rate {τ k D : ℝ} (hτ : 0 < τ) (hk : 0 < k) (hkτ : 4 * k * τ < 1)
    (m₁ m₂ S X V : ℝ → ℝ)
    (hm₁ : ∀ t, HasDerivAt m₁ (m₂ t) t) (hm₂ : ∀ t, HasDerivAt m₂ ((-k * m₁ t - m₂ t) / τ) t)
    (hS : ∀ t, HasDerivAt S (2 * X t) t)
    (hX : ∀ t, HasDerivAt X ((τ * V t - k * S t - X t) / τ) t)
    (hV : ∀ t, HasDerivAt V ((-2 * k * X t - 2 * V t + 2 * D / τ) / τ) t)
    (hX0 : X 0 = m₁ 0 * m₂ 0) (hV0 : V 0 = D / τ + m₂ 0 ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    |(S t - m₁ t ^ 2) - (D / k + ((S 0 - m₁ 0 ^ 2) - D / k) * Real.exp (-2 * k * t))|
      ≤ 8 * k * τ * |(S 0 - m₁ 0 ^ 2) - D / k| := by
  obtain ⟨hne, hs, hp⟩ := harm_roots hτ hkτ
  set lp := (-1 + Real.sqrt (1 - 4 * k * τ)) / (2 * τ)
  set lm := (-1 - Real.sqrt (1 - 4 * k * τ)) / (2 * τ)
  rw [harmonic_variance_exact hτ hk lp lm hne hs hp m₁ m₂ S X V hm₁ hm₂ hS hX hV hX0 hV0 t]
  have hmu := fun t => (harm_mean_sol hτ hne hs hp t).1
  have hnu := fun t => (harm_mean_sol hτ hne hs hp t).2
  have hmu0 : harmMu lp lm 0 = 1 := by
    simp only [harmMu, mul_zero, Real.exp_zero, mul_one]; field_simp [sub_ne_zero.2 hne]
  have hnu0 : harmNu lp lm 0 = 0 := by simp [harmNu]
  have hb := harmonic_mean_bounded (harmMu lp lm) (harmNu lp lm) hτ hk hmu hnu hnu0 ht
  have hr := harmonic_mean_rate (harmMu lp lm) (harmNu lp lm) hτ hk hkτ.le hmu hnu hnu0 ht
  rw [hmu0, abs_one] at hb
  rw [hmu0, one_mul, abs_one, mul_one] at hr
  set μ := harmMu lp lm t
  set e := Real.exp (-k * t)
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hee : Real.exp (-2 * k * t) = e ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hee]
  have : |μ ^ 2 - e ^ 2| ≤ 2 * (4 * k * τ) := by
    rw [show μ ^ 2 - e ^ 2 = (μ + e) * (μ - e) by ring, abs_mul]
    have h1 : |μ + e| ≤ 2 := (abs_add_le _ _).trans (by rw [abs_of_pos he0]; linarith)
    calc |μ + e| * |μ - e| ≤ 2 * (4 * k * τ) := by
          gcongr
      _ = _ := rfl
  calc |D / k + ((S 0 - m₁ 0 ^ 2) - D / k) * μ ^ 2
        - (D / k + ((S 0 - m₁ 0 ^ 2) - D / k) * e ^ 2)|
      = |(S 0 - m₁ 0 ^ 2) - D / k| * |μ ^ 2 - e ^ 2| := by rw [← abs_mul]; ring_nf
    _ ≤ |(S 0 - m₁ 0 ^ 2) - D / k| * (2 * (4 * k * τ)) := by gcongr
    _ = 8 * k * τ * |(S 0 - m₁ 0 ^ 2) - D / k| := by ring

/-- **Stationary statistics**: a stationary solution of the Kramers second-moment equations (with
`⟨x⟩ = ⟨v⟩ = 0`) has `⟨x²⟩ = D/k`, `⟨xv⟩ = 0`, `⟨v²⟩ = D/τ = kT/m`, for every relaxation time `τ`:
the stationary position variance is exactly that of the Smoluchowski equation. -/
theorem harmonic_stationary {τ k D S X V : ℝ} (hτ : 0 < τ) (hk : 0 < k)
    (h1 : 2 * X = 0) (h2 : (τ * V - k * S - X) / τ = 0)
    (h3 : (-2 * k * X - 2 * V + 2 * D / τ) / τ = 0) :
    S = D / k ∧ X = 0 ∧ V = D / τ := by
  have hX : X = 0 := by linarith
  rw [div_eq_zero_iff] at h2 h3
  have h2 := h2.resolve_right hτ.ne'
  have h3 := h3.resolve_right hτ.ne'
  have hV : V = D / τ := by rw [hX] at h3; field_simp at h3 ⊢; linarith
  refine ⟨?_, hX, hV⟩
  rw [hX, hV] at h2
  field_simp at h2 ⊢
  linarith

end HarmonicVariance

end Gardiner.Adiabatic
