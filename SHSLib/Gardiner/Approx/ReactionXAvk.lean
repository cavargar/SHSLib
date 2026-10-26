/-
# The system size expansion of `X ⇌ A`

Gardiner, *Handbook of Stochastic Methods*, §7.2.3 b), equations (7.2.41)–(7.2.58).

Main results:

* `Gardiner.xa_intMoment_one`, `Gardiner.xa_intMoment_two` — (7.2.43)–(7.2.44).
* `Gardiner.xa_vkGen_sub_lnaGen_le` — a non-degenerate instance of
  `Gardiner.vkGen_sub_lnaGen_le`: the rescaled master-equation generator of `X ⇌ A` is within
  `V^{-1/2} [k₁ |z| |f''|/2 + ‖f'''‖ (k₂a₀ + k₁|φ + V^{-1/2}z|)/6]` of the generator of (7.2.47).
* `Gardiner.xa_lna_variance` — (7.2.49); `Gardiner.xa_lna_matches_exact` — (7.2.50)–(7.2.51)
  coincide with (7.1.38)–(7.1.40) when `Vφ(0) = N`.
* `Gardiner.lna_exact_of_linear` — **exactness of the linear noise approximation for linear
  propensities**: if the exact mean and variance obey the closed moment equations that linear
  propensities produce, they equal `Ωφ(t)` and `Ωσ(t)`.
  `Gardiner.xa_lna_exact` applies this to every solution of the master equation (7.1.26).
* `Gardiner.xa_lna_stationary` — (7.2.52); `Gardiner.xa_km_stationary_flux`,
  `Gardiner.xa_km_stationary` — (7.2.53).
* `Gardiner.xa_km_log_expansion` — **(7.2.56), corrected**, with an explicit remainder, and
  `Gardiner.xa_km_log_expansion_z` — (7.2.58), corrected.

**Erratum (7.2.56), (7.2.58).**  Expanding (7.2.55) about `x = V k₂a₀/k₁` gives
`log Pₛ = const - (k₁/(2k₂a₀V)) (δ + δ²) + O(δ²/V², δ³/V²)`; the text prints `k₂` for `k₁`
in the numerator and `δ - δ²` for `δ + δ²`.  Correspondingly (7.2.58) should read
`log Pₛ(z) ≈ const - (k₁/(2k₂a₀)) (z/√V + z²)`, so that the Gaussian has variance `k₂a₀/k₁`
in agreement with (7.2.52); the text has `z/√V - z²`, which is not normalisable.
-/
import SHSLib.Gardiner.Approx.ReactionXA
import SHSLib.Gardiner.Approx.SystemSize

open MeasureTheory Filter Topology Set
open scoped Nat

noncomputable section

namespace Gardiner

/-! ### (7.2.41)–(7.2.46): rates, jump moments and the deterministic equation -/

/-- (7.2.43): the intensive rates of `X ⇌ A`: `ψ₊(x) = k₂a₀` for the jump `+1` and
`ψ₋(x) = k₁x` for the jump `-1` (indexed by `true`/`false`, with directions `pmOne`). -/
def xaPsi (k₂a₀ k₁ : ℝ) : Bool → ℝ → ℝ := fun b x => if b then k₂a₀ else k₁ * x

/-- (7.2.43): `W(x; ±1) = V ψ_±(x/V)`, i.e. the rates `k₂a = k₂a₀V` and `k₁x` of (7.2.41). -/
theorem xa_extRate (k₂a₀ k₁ V x : ℝ) (hV : V ≠ 0) :
    extRate (xaPsi k₂a₀ k₁) V true x = k₂a₀ * V ∧ extRate (xaPsi k₂a₀ k₁) V false x = k₁ * x := by
  simp only [extRate, xaPsi, if_true, Bool.false_eq_true, if_false]
  constructor
  · ring
  · field_simp

/-- (7.2.44): `α̃₁(x) = k₂a₀ - k₁x`. -/
theorem xa_intMoment_one (k₂a₀ k₁ x : ℝ) :
    intMoment Finset.univ pmOne (xaPsi k₂a₀ k₁) 1 x = k₂a₀ - k₁ * x := by
  simp [intMoment, finJumpMoment, xaPsi, pmOne]; ring

/-- (7.2.44): `α̃₂(x) = k₂a₀ + k₁x`. -/
theorem xa_intMoment_two (k₂a₀ k₁ x : ℝ) :
    intMoment Finset.univ pmOne (xaPsi k₂a₀ k₁) 2 x = k₂a₀ + k₁ * x := by
  simp [intMoment, finJumpMoment, xaPsi, pmOne]

/-- The third absolute jump moment `β̃₃(x) = |k₂a₀| + |k₁x|`. -/
theorem xa_absMoment_three (k₂a₀ k₁ x : ℝ) :
    finAbsJumpMoment Finset.univ pmOne (xaPsi k₂a₀ k₁) x 3 = |k₂a₀| + |k₁ * x| := by
  simp [finAbsJumpMoment, xaPsi, pmOne]

/-- (7.2.45)–(7.2.46): `φ(t) = φ(0)e^{-k₁t} + (k₂a₀/k₁)(1 - e^{-k₁t})` solves
`φ' = α̃₁(φ) = k₂a₀ - k₁φ`; it is `xaMean k₂a₀ k₁ φ(0)`. -/
theorem xa_phi_hasDerivAt (k₂a₀ k₁ phi0 t : ℝ) (hk : k₁ ≠ 0) :
    HasDerivAt (xaMean k₂a₀ k₁ phi0)
      (intMoment Finset.univ pmOne (xaPsi k₂a₀ k₁) 1 (xaMean k₂a₀ k₁ phi0 t)) t := by
  rw [xa_intMoment_one]; exact xaMean_hasDerivAt k₂a₀ k₁ phi0 t hk

/-! ### The linear noise approximation of `X ⇌ A` with an explicit error -/

/-- The derivative tower of `α̃₁(x) = k₂a₀ - k₁x`. -/
def xaTower (k₂a₀ k₁ : ℝ) : ℕ → ℝ → ℝ := fun k x =>
  if k = 0 then k₂a₀ - k₁ * x else if k = 1 then -k₁ else 0

/-- **The system size expansion of `X ⇌ A` with explicit error** (instance of
`vkGen_sub_lnaGen_le`): with `φ` on the deterministic trajectory, the generator of the
fluctuation variable differs from the generator `-k₁ z ∂_z + ½ (k₂a₀ + k₁φ) ∂_z²` of (7.2.47) by at
most `V^{-1/2} [|k₁| |z| |f''(z)|/2 + M (|k₂a₀| + |k₁(φ + V^{-1/2}z)|)/6]`. -/
theorem xa_vkGen_sub_lnaGen_le (k₂a₀ k₁ : ℝ) {V : ℝ} (hV : 0 < V) (phi z M : ℝ)
    (D : ℕ → ℝ → ℝ) (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y)
    (hM : ∀ y, |D 3 y| ≤ M) :
    |vkGen Finset.univ pmOne (xaPsi k₂a₀ k₁) V phi (k₂a₀ - k₁ * phi) D z
        - ouGen (-k₁) (k₂a₀ + k₁ * phi) z (D 1 z) (D 2 z)|
      ≤ (Real.sqrt V)⁻¹ * (|k₁| * |z| * |D 2 z| / 2
          + M / 6 * (|k₂a₀| + |k₁ * (phi + (Real.sqrt V)⁻¹ * z)|)) := by
  have h := vkGen_sub_lnaGen_le Finset.univ pmOne (xaPsi k₂a₀ k₁) hV phi z 0 |k₁| M D hD hM
    (xaTower k₂a₀ k₁) (funext fun x => by rw [xa_intMoment_one]; simp [xaTower])
    (fun k hk u => by
      interval_cases k
      · simpa [xaTower] using ((hasDerivAt_id u).const_mul k₁).const_sub k₂a₀
      · simpa [xaTower] using hasDerivAt_const u (-k₁))
    (fun t _ => by simp [xaTower])
    (by rw [xa_intMoment_two, xa_intMoment_two, ← abs_mul]; apply le_of_eq; congr 1; ring)
  rw [xa_intMoment_one, xa_intMoment_two, xa_absMoment_three] at h
  simpa [xaTower] using h

/-! ### (7.2.48)–(7.2.51): mean and variance -/

/-- (7.2.48): the solution of the linear-noise mean equation `m' = a m` is `m(0) e^{at}`. -/
theorem lna_mean_solution (a : ℝ) (m : ℝ → ℝ) (hm : ∀ t, HasDerivAt m (a * m t) t) (t : ℝ) :
    m t = m 0 * Real.exp (a * t) := by
  have := linear_ode_unique (fun _ => a) (fun _ => 0) continuous_const continuous_const m
    (fun t => m 0 * Real.exp (a * t)) (fun t => by simpa using hm t)
    (fun t => by
      have := ((hasDerivAt_id t).const_mul a).exp.const_mul (m 0)
      convert this using 1; simp; ring) (by simp)
  exact congrFun this t

/-- The linear-noise variance (7.2.49): `σ(t) = (k₂a₀/k₁ + φ(0)e^{-k₁t})(1 - e^{-k₁t})`. -/
def xaSigma (k₂a₀ k₁ phi0 t : ℝ) : ℝ :=
  (k₂a₀ / k₁ + phi0 * Real.exp (-k₁ * t)) * (1 - Real.exp (-k₁ * t))

/-- **(7.2.49)**: `σ` solves the variance equation (4.4.85) of the linear noise approximation,
`σ' = 2 α̃₁'(φ) σ + α̃₂(φ) = -2k₁σ + k₂a₀ + k₁φ(t)`, with `σ(0) = 0`. -/
theorem xa_lna_variance (k₂a₀ k₁ phi0 t : ℝ) (hk : k₁ ≠ 0) :
    HasDerivAt (xaSigma k₂a₀ k₁ phi0)
      (2 * (-k₁) * xaSigma k₂a₀ k₁ phi0 t + (k₂a₀ + k₁ * xaMean k₂a₀ k₁ phi0 t)) t := by
  have hp : HasDerivAt (fun t => Real.exp (-k₁ * t)) (-k₁ * Real.exp (-k₁ * t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-k₁)).exp
  have := ((hp.const_mul phi0).const_add (k₂a₀ / k₁)).mul (hp.const_sub 1)
  convert this using 1
  simp only [xaSigma, xaMean]
  field_simp
  ring

theorem xaSigma_zero (k₂a₀ k₁ phi0 : ℝ) : xaSigma k₂a₀ k₁ phi0 0 = 0 := by simp [xaSigma]

/-- **(7.2.50)–(7.2.51) = (7.1.38)–(7.1.40)**: with `a = a₀V` and `Vφ(0) = N`, the
linear-noise mean `Vφ(t)` and variance `Vσ(t)` coincide with the exact ones. -/
theorem xa_lna_matches_exact (k₂a₀ k₁ V : ℝ) (N : ℕ) (phi0 : ℝ) (hN : V * phi0 = N) (t : ℝ) :
    V * xaMean k₂a₀ k₁ phi0 t = xaMean (k₂a₀ * V) k₁ N t ∧
      V * xaSigma k₂a₀ k₁ phi0 t
        = (N * Real.exp (-k₁ * t) + k₂a₀ * V / k₁) * (1 - Real.exp (-k₁ * t)) := by
  rw [← hN]
  constructor
  · simp only [xaMean]; ring
  · simp only [xaSigma]; ring

/-- **Exactness of the linear noise approximation for linear propensities.**  Suppose the
extensive jump moments are affine, `α₁(x) = Ω α̃₁(x/Ω)` with `α̃₁(y) = a + b y` and
`α₂(x) = Ω α̃₂(x/Ω)` with `α̃₂(y) = p + q y`, and that the exact mean `m` and variance `v` obey
the moment equations that the master equation yields for such propensities,
`m' = α₁(m)`, `v' = 2b v + α₂(m)`.  Let `φ` solve the deterministic equation (7.2.33)
`φ' = α̃₁(φ)` and `σ` the linear-noise variance equation (4.4.85) `σ' = 2α̃₁'(φ)σ + α̃₂(φ)`.  If
`m(0) = Ωφ(0)` and `v(0) = Ωσ(0)`, then `m = Ωφ` and `v = Ωσ` for all time: the linear noise
approximation of the mean and variance is exact. -/
theorem lna_exact_of_linear (Ω a b p q : ℝ) (hΩ : Ω ≠ 0) (m v phi σ : ℝ → ℝ)
    (hm : ∀ t, HasDerivAt m (Ω * (a + b * (m t / Ω))) t)
    (hv : ∀ t, HasDerivAt v (2 * b * v t + Ω * (p + q * (m t / Ω))) t)
    (hphi : ∀ t, HasDerivAt phi (a + b * phi t) t)
    (hσ : ∀ t, HasDerivAt σ (2 * b * σ t + (p + q * phi t)) t)
    (hm0 : m 0 = Ω * phi 0) (hv0 : v 0 = Ω * σ 0) :
    ∀ t, m t = Ω * phi t ∧ v t = Ω * σ t := by
  have hmφ : m = fun t => Ω * phi t := by
    refine linear_ode_unique (fun _ => b) (fun _ => Ω * a) continuous_const continuous_const _ _
      (fun t => ?_) (fun t => ?_) hm0
    · convert hm t using 1; field_simp; ring
    · convert (hphi t).const_mul Ω using 1; ring
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun t => (hm t).continuousAt
  have hvσ : v = fun t => Ω * σ t := by
    refine linear_ode_unique (fun _ => 2 * b) (fun t => Ω * (p + q * (m t / Ω)))
      continuous_const (continuous_const.mul (continuous_const.add
        (continuous_const.mul (hmc.div_const Ω)))) _ _ hv (fun t => ?_) hv0
    convert (hσ t).const_mul Ω using 1
    show 2 * b * (Ω * σ t) + Ω * (p + q * (m t / Ω)) = _
    rw [congrFun hmφ t]
    field_simp
  exact fun t => ⟨congrFun hmφ t, congrFun hvσ t⟩

/-- **The linear noise approximation of `X ⇌ A` is exact** for every solution of the master
equation (7.1.26) with `a = a₀V` started at `δ_{x,N}` (under the summability and `hswap`
hypotheses of `xa_mean_variance_exact`): `⟨x(t)⟩ = Vφ(t)` and `var x(t) = Vσ(t)`, where
`φ(0) = N/V` and `σ(0) = 0`. -/
theorem xa_lna_exact (k₂a₀ k₁ V : ℝ) (hk : k₁ ≠ 0) (hV : V ≠ 0) (N : ℕ) (P : ℝ → ℕ → ℝ)
    (hP0 : ∀ x, P 0 x = if x = N then 1 else 0)
    (hP : ∀ t, ∀ k ≤ 3, Summable fun x : ℕ => (x : ℝ) ^ k * P t x)
    (hswap : ∀ t, ∀ k ≤ 2, HasDerivAt (fun t => ∑' x : ℕ, (x : ℝ) ^ k * P t x)
      (∑' x : ℕ, (x : ℝ) ^ k * xaME (k₂a₀ * V) k₁ (P t) x) t) (t : ℝ) :
    ∑' x : ℕ, (x : ℝ) * P t x = V * xaMean k₂a₀ k₁ (N / V) t ∧
      ∑' x : ℕ, (x : ℝ) ^ 2 * P t x - (∑' x : ℕ, (x : ℝ) * P t x) ^ 2
        = V * xaSigma k₂a₀ k₁ (N / V) t := by
  obtain ⟨-, h1, h2⟩ := xa_mean_variance_exact (k₂a₀ * V) k₁ hk N P hP0 hP hswap t
  have hN : V * (N / V) = N := by field_simp
  obtain ⟨e1, e2⟩ := xa_lna_matches_exact k₂a₀ k₁ V N (N / V) hN t
  exact ⟨h1.trans e1.symm, h2.trans e2.symm⟩

/-! ### (7.2.52)–(7.2.53): stationary solutions -/

/-- **(7.2.52)**: `Pₛ(z) = exp(-k₁z²/(2k₂a₀))` is a stationary solution of the linear-noise
equation (7.2.47) at the steady state `φₛ = k₂a₀/k₁` (where `α̃₂(φₛ) = 2k₂a₀`). -/
theorem xa_lna_stationary (k₂a₀ k₁ : ℝ) (hk : k₂a₀ ≠ 0) (z : ℝ) :
    lnaFP (-k₁) (2 * k₂a₀) (fun z => Real.exp (-(k₁ * z ^ 2) / (2 * k₂a₀))) z = 0 := by
  set P : ℝ → ℝ := fun z => Real.exp (-(k₁ * z ^ 2) / (2 * k₂a₀))
  have hP : ∀ z, HasDerivAt P (-(k₁ * z) / k₂a₀ * P z) z := by
    intro z
    have : HasDerivAt (fun z => -(k₁ * z ^ 2) / (2 * k₂a₀)) (-(k₁ * z) / k₂a₀) z := by
      have := (((hasDerivAt_pow 2 z).const_mul k₁).neg).div_const (2 * k₂a₀)
      convert this using 1; field_simp; ring
    convert this.exp using 1; simp only [P]; ring
  have hzP : ∀ z, HasDerivAt (fun z => z * P z) (P z + z * (-(k₁ * z) / k₂a₀ * P z)) z := by
    intro z; simpa using (hasDerivAt_id z).mul (hP z)
  have hP' : ∀ z, HasDerivAt (fun z => -(k₁ * z) / k₂a₀ * P z)
      (-k₁ / k₂a₀ * P z + -(k₁ * z) / k₂a₀ * (-(k₁ * z) / k₂a₀ * P z)) z := by
    intro z
    have := (((hasDerivAt_id z).const_mul k₁).neg.div_const k₂a₀).mul (hP z)
    convert this using 1; simp
  have d1 : deriv P = fun z => -(k₁ * z) / k₂a₀ * P z := funext fun z => (hP z).deriv
  simp only [lnaFP, (hzP z).deriv, d1, (hP' z).deriv]
  field_simp
  ring

/-- The Kramers–Moyal stationary density (7.2.53),
`Pₛ(x) = (k₂a + k₁x)^{-1 + 4k₂a/k₁} e^{-2x}` (unnormalised; `c = k₂a`). -/
def xaKMStationary (c k₁ x : ℝ) : ℝ := (c + k₁ * x) ^ (4 * c / k₁ - 1) * Real.exp (-2 * x)

/-- **(7.2.53), zero flux**: `½ ∂ₓ[α₂ Pₛ] = α₁ Pₛ` with `α₁ = c - k₁x`, `α₂ = c + k₁x`,
wherever `c + k₁x > 0`. -/
theorem xa_km_stationary_flux (c k₁ x : ℝ) (hk : k₁ ≠ 0) (hx : 0 < c + k₁ * x) :
    HasDerivAt (fun x => (c + k₁ * x) * xaKMStationary c k₁ x)
      (2 * ((c - k₁ * x) * xaKMStationary c k₁ x)) x := by
  have e : ∀ y, 0 < c + k₁ * y → (c + k₁ * y) * xaKMStationary c k₁ y
      = (c + k₁ * y) ^ (4 * c / k₁) * Real.exp (-2 * y) := by
    intro y hy
    simp only [xaKMStationary]
    rw [Real.rpow_sub hy, Real.rpow_one]
    field_simp
  have hev : (fun y => (c + k₁ * y) * xaKMStationary c k₁ y)
      =ᶠ[𝓝 x] fun y => (c + k₁ * y) ^ (4 * c / k₁) * Real.exp (-2 * y) := by
    have : ∀ᶠ y in 𝓝 x, 0 < c + k₁ * y :=
      ((continuous_const.add (continuous_const.mul continuous_id)).tendsto x).eventually
        (lt_mem_nhds hx)
    filter_upwards [this] with y hy using e y hy
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hlin : HasDerivAt (fun y => c + k₁ * y) k₁ x := by
    simpa using ((hasDerivAt_id x).const_mul k₁).const_add c
  have h1 := hlin.rpow_const (p := 4 * c / k₁) (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y => Real.exp (-2 * y)) (Real.exp (-2 * x) * -2) x := by
    simpa using ((hasDerivAt_id x).const_mul (-2)).exp
  convert h1.mul h2 using 1
  simp only [xaKMStationary]
  rw [Real.rpow_sub hx, Real.rpow_one]
  field_simp
  ring

/-- **(7.2.53)**: `Pₛ` is a stationary solution of the Kramers–Moyal equation (7.2.36),
`-∂ₓ[α₁Pₛ] + ½∂ₓ²[α₂Pₛ] = 0`, wherever `c + k₁x > 0`. -/
theorem xa_km_stationary (c k₁ x : ℝ) (hk : k₁ ≠ 0) (hx : 0 < c + k₁ * x) :
    kmFP (fun x => c - k₁ * x) (fun x => c + k₁ * x) (xaKMStationary c k₁) x = 0 := by
  have hev : deriv (fun x => (c + k₁ * x) * xaKMStationary c k₁ x)
      =ᶠ[𝓝 x] fun y => 2 * ((c - k₁ * y) * xaKMStationary c k₁ y) := by
    have : ∀ᶠ y in 𝓝 x, 0 < c + k₁ * y :=
      ((continuous_const.add (continuous_const.mul continuous_id)).tendsto x).eventually
        (lt_mem_nhds hx)
    filter_upwards [this] with y hy using (xa_km_stationary_flux c k₁ y hk hy).deriv
  simp only [kmFP]
  rw [hev.deriv_eq, deriv_const_mul_field]
  ring

/-! ### (7.2.54)–(7.2.58): the expansion about the steady state, corrected -/

/-- **(7.2.56), corrected, with an explicit remainder.**  Let `c = k₂a = k₂a₀V > 0`, `k₁ > 0`,
`x = c/k₁ + δ` (7.2.54) and `u = k₁δ/(2c)` with `|u| ≤ 1/2`.  Then
`log Pₛ(x) = log Pₛ(c/k₁) - (k₁/(2c)) (δ + δ²) + R` with
`|R| ≤ u²/2 + 2|4c/k₁ - 1| |u|³`. -/
theorem xa_km_log_expansion (c k₁ δ : ℝ) (hc : 0 < c) (hk : 0 < k₁)
    (hu : |k₁ * δ / (2 * c)| ≤ 1 / 2) :
    |Real.log (xaKMStationary c k₁ (c / k₁ + δ)) - Real.log (xaKMStationary c k₁ (c / k₁))
        + k₁ / (2 * c) * (δ + δ ^ 2)|
      ≤ (k₁ * δ / (2 * c)) ^ 2 / 2 + 2 * |4 * c / k₁ - 1| * |k₁ * δ / (2 * c)| ^ 3 := by
  set u := k₁ * δ / (2 * c) with hu_def
  set q := 4 * c / k₁ with hq
  have hu1 : |u| < 1 := by linarith
  have hb0 : c + k₁ * (c / k₁) = 2 * c := by field_simp; ring
  have hb : c + k₁ * (c / k₁ + δ) = 2 * c * (1 + u) := by rw [hu_def]; field_simp; ring
  have h1u : 0 < 1 + u := by have := neg_abs_le u; linarith
  have hlogP : ∀ y, 0 < c + k₁ * y →
      Real.log (xaKMStationary c k₁ y) = (q - 1) * Real.log (c + k₁ * y) + -2 * y := by
    intro y hy
    simp only [xaKMStationary]
    rw [Real.log_mul (Real.rpow_pos_of_pos hy _).ne' (Real.exp_pos _).ne', Real.log_rpow hy,
      Real.log_exp]
  rw [hlogP _ (by rw [hb]; positivity), hlogP _ (by rw [hb0]; positivity), hb, hb0,
    Real.log_mul (by positivity) h1u.ne']
  -- the logarithmic remainder
  have hR := Real.abs_log_sub_add_sum_range_le (x := -u) (by rwa [abs_neg]) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hR
  set R := Real.log (1 + u) - u + u ^ 2 / 2
  have hR' : |R| ≤ 2 * |u| ^ 3 := by
    have e : R = (-u) ^ (0 + 1) / ((0 : ℕ) + 1) + (-u) ^ (1 + 1) / ((1 : ℕ) + 1)
        + Real.log (1 + u) := by simp only [R]; push_cast; ring
    rw [e]
    calc _ ≤ |u| ^ (2 + 1) / (1 - |u|) := by simpa using hR
      _ ≤ 2 * |u| ^ 3 := by
        rw [div_le_iff₀ (by linarith)]
        have h2 : (1 : ℝ) / 2 ≤ 1 - |u| := by linarith
        calc |u| ^ (2 + 1) = 2 * |u| ^ 3 * (1 / 2) := by ring
          _ ≤ 2 * |u| ^ 3 * (1 - |u|) := by gcongr
  have key : (q - 1) * (Real.log (2 * c) + Real.log (1 + u)) + -2 * (c / k₁ + δ)
      - ((q - 1) * Real.log (2 * c) + -2 * (c / k₁)) + k₁ / (2 * c) * (δ + δ ^ 2)
      = u ^ 2 / 2 + (q - 1) * R := by
    simp only [R, hq, hu_def]; field_simp; ring
  rw [key]
  calc |u ^ 2 / 2 + (q - 1) * R| ≤ |u ^ 2 / 2| + |q - 1| * |R| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ u ^ 2 / 2 + |q - 1| * (2 * |u| ^ 3) := by
        rw [abs_of_nonneg (by positivity)]
        gcongr
    _ = _ := by ring

/-- **(7.2.58), corrected**: in the fluctuation variable `δ = √V z` (7.2.39), with
`c = k₂a₀V`, `log Pₛ = const - (k₁/(2k₂a₀)) (z/√V + z²) + R`, where
`|R| ≤ u²/2 + 2|4k₂a₀V/k₁ - 1||u|³` and `u = k₁z/(2k₂a₀√V) = O(V^{-1/2})`.  In the large-`V`
limit this is the Gaussian (7.2.52) of variance `k₂a₀/k₁`. -/
theorem xa_km_log_expansion_z (k₂a₀ k₁ V z : ℝ) (ha : 0 < k₂a₀) (hk : 0 < k₁) (hV : 0 < V)
    (hu : |k₁ * z / (2 * k₂a₀ * Real.sqrt V)| ≤ 1 / 2) :
    |Real.log (xaKMStationary (k₂a₀ * V) k₁ (k₂a₀ * V / k₁ + Real.sqrt V * z))
        - Real.log (xaKMStationary (k₂a₀ * V) k₁ (k₂a₀ * V / k₁))
        + k₁ / (2 * k₂a₀) * (z / Real.sqrt V + z ^ 2)|
      ≤ (k₁ * z / (2 * k₂a₀ * Real.sqrt V)) ^ 2 / 2
        + 2 * |4 * (k₂a₀ * V) / k₁ - 1| * |k₁ * z / (2 * k₂a₀ * Real.sqrt V)| ^ 3 := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ V = s ^ 2 :=
    ⟨Real.sqrt V, Real.sqrt_pos.2 hV, (Real.sq_sqrt hV.le).symm⟩
  have hu' : k₁ * (Real.sqrt (s ^ 2) * z) / (2 * (k₂a₀ * s ^ 2))
      = k₁ * z / (2 * k₂a₀ * Real.sqrt (s ^ 2)) := by
    rw [Real.sqrt_sq hs0.le]; field_simp
  have hco : k₁ / (2 * (k₂a₀ * s ^ 2)) * (Real.sqrt (s ^ 2) * z + (Real.sqrt (s ^ 2) * z) ^ 2)
      = k₁ / (2 * k₂a₀) * (z / Real.sqrt (s ^ 2) + z ^ 2) := by
    rw [Real.sqrt_sq hs0.le]; field_simp
  have := xa_km_log_expansion (k₂a₀ * s ^ 2) k₁ (Real.sqrt (s ^ 2) * z) (by positivity) hk (by rwa [hu'])
  rwa [hu', hco] at this

end Gardiner
