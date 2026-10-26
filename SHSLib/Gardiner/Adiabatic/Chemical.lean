/-
# Elimination of a short-lived chemical intermediate (Gardiner §6.6.1)

Gardiner, *Handbook of Stochastic Methods*, §6.6.1, (6.6.1)–(6.6.35), for
`X ⇌ Y ⇌ A` with rate equations (6.6.2) `ẋ = -x + γy`, `ẏ = -2γy + x + a` and the SDE (6.6.5)
with `BBᵀ = [[2a, -2a], [-2a, 4a]]` (6.6.6).

* (6.6.8)–(6.6.11): the change of variables `z = 2γy - x - a` transforms drift and diffusion as
  printed (`Gardiner.Adiabatic.chem_transform_drift`, `chem_transform_diffusion`).
* (6.6.12)–(6.6.16): with `α = γ^{-1/2} z` the operator splits as `γL₁ + γ^{1/2}L₂(γ) + L₃`
  (`Gardiner.Adiabatic.chem_alpha_split`); the `γ^{-1/2}∂_α α` term of (6.6.15) has coefficient
  `+½`, not `-1` as printed (erratum).
* (6.6.29)–(6.6.33): the effective diffusion coefficient is
  `¼ · ⟨α²⟩_s · ∫₀^∞ e^{-2t} dt · 4 = ½ε²a` (`Gardiner.Adiabatic.chem_effective_diffusion`),
  hence the reduced equation (6.6.33) `∂ₜp̂ = ∂ₓ((x-a)/2 p̂) + ½ε²a ∂ₓ²p̂`; the deterministic
  reduced equation is `ẋ = (a - x)/2`, not `x/2 - a/2` as printed in (6.6.4) (erratum).
* (6.6.35): the stationary covariance of the full linear system is exactly `ε² diag(a, a/γ)`
  for every `γ`, so the stationary variance of `x` is `ε²a`, which is exactly that of (6.6.33)
  (`Gardiner.Adiabatic.chem_stationary_covariance`, `chem_reduced_stationary`).

**Approximation guarantee** (`Gardiner.Adiabatic.chem_mean_rate`): for every solution of the mean
equations (6.6.2) and all `t ≥ 0`,
`|⟨x⟩(t) - [a + (⟨x⟩(0) - a)e^{-t/2}]| ≤ |z₀|/(4γ) + √((⟨x⟩(0) - a)² + z₀²)/(4γ + 1)`,
`z₀ = 2γ⟨y⟩(0) - ⟨x⟩(0) - a`, i.e. the mean of `x` follows the reduced equation with error
`O(γ⁻¹)` uniformly in time.  `Gardiner.Adiabatic.chem_mean_instance` constructs an explicit
solution (for every `γ > 0`) and applies the bound to it.
-/
import SHSLib.Gardiner.Adiabatic.Brownian

open Set MeasureTheory

noncomputable section

namespace Gardiner.Adiabatic

/-! ### (6.6.8)–(6.6.16): the change of variables -/

/-- **(6.6.9)–(6.6.11), drift.**  With `z = 2γy - x - a`, the drifts of `x` and `z` are
`-((x - a)/2 - z/2)` and `-(2γz - (x - a)/2 + z/2)`. -/
theorem chem_transform_drift (γ a x y : ℝ) (hγ : γ ≠ 0) :
    let z := 2 * γ * y - x - a
    y = (z + x + a) / (2 * γ) ∧
      (-x + γ * y) = -((x - a) / 2 - z / 2) ∧
      (-1) * (-x + γ * y) + 2 * γ * (-2 * γ * y + x + a) = -(2 * γ * z - (x - a) / 2 + z / 2) := by
  intro z
  refine ⟨?_, ?_, ?_⟩ <;> simp only [z] <;> field_simp <;> ring

/-- **(6.6.11), diffusion.**  The diffusion matrix `ε²[[a, -a], [-a, 2a]]` (one half of
`ε²BBᵀ`) becomes, under `(x, y) ↦ (x, z)` with Jacobian `[[1, 0], [-1, 2γ]]`, the matrix
`ε²[[a, -a - 2γa], [-a - 2γa, a + 4γa + 8γ²a]]`, i.e. the coefficients
`ε²a ∂ₓ²`, `(-2ε²a - 4γε²a) ∂ₓ∂_z`, `(8ε²γ²a + ε²a + 4γε²a) ∂_z²` of (6.6.11). -/
theorem chem_transform_diffusion (γ a ε : ℝ) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -1, 2 * γ]
    let Dm : Matrix (Fin 2) (Fin 2) ℝ := !![ε ^ 2 * a, -(ε ^ 2 * a); -(ε ^ 2 * a), 2 * ε ^ 2 * a]
    M * Dm * !![1, -1; 0, 2 * γ] = !![ε ^ 2 * a, -(ε ^ 2 * a) - 2 * γ * ε ^ 2 * a;
      -(ε ^ 2 * a) - 2 * γ * ε ^ 2 * a, 8 * ε ^ 2 * γ ^ 2 * a + ε ^ 2 * a + 4 * γ * ε ^ 2 * a] := by
  intro M Dm
  simp only [M, Dm, Matrix.mul_fin_two]
  congr 1; ring_nf

/-- **(6.6.12)–(6.6.16)**: with `z = γ^{1/2} α` (`g = γ^{1/2}`), the `z`-drift
`-(2γz - (x-a)/2 + z/2)` is `γ^{1/2}` times `-2γα + γ^{-1/2}(x-a)/2 - α/2`, and the `α`-diffusion
`γ⁻¹(8ε²γ²a + ε²a + 4γε²a) = γ·8ε²a + γ^{1/2}·4γ^{-1/2}ε²a + γ^{1/2}·γ^{-3/2}ε²a`: the
`O(γ)` parts form `γL₁` with `L₁ = 2∂_α α + 8ε²a∂_α²` (6.6.14), and the remaining drift
`-α/2` enters `γ^{1/2}L₂` as `+½γ^{-1/2}∂_α α` (the printed (6.6.15) has `-γ^{-1/2}∂_α α`). -/
theorem chem_alpha_split (g a ε x α : ℝ) (hg : 0 < g) :
    let γ := g ^ 2
    let z := g * α
    (-(2 * γ * z - (x - a) / 2 + z / 2)) / g
        = γ * (-2 * α) + g * (g⁻¹ ^ 2 * ((x - a) / 2) + g⁻¹ * (-(1 / 2) * α)) ∧
      (8 * ε ^ 2 * γ ^ 2 * a + ε ^ 2 * a + 4 * γ * ε ^ 2 * a) / g ^ 2
        = γ * (8 * ε ^ 2 * a) + g * (4 * g⁻¹ * ε ^ 2 * a + g⁻¹ ^ 3 * ε ^ 2 * a) ∧
      (-(ε ^ 2 * a) - 2 * γ * ε ^ 2 * a) / g = g * (-4 * ε ^ 2 * a / 2 - g⁻¹ ^ 2 * ε ^ 2 * a) := by
  intro γ z
  have hg0 : g ≠ 0 := hg.ne'
  refine ⟨?_, ?_, ?_⟩ <;> simp only [γ, z] <;> field_simp <;> ring

/-! ### (6.6.29)–(6.6.35): effective diffusion and stationary statistics -/

/-- **(6.6.31)–(6.6.32)**: `L₁ = 2∂_α α + 8ε²a∂_α²` generates an Ornstein–Uhlenbeck process with
`⟨α(t)α(0)⟩_s = 4ε²a e^{-2t}`, and `¼ · ∫₀^∞ ⟨α(t)α(0)⟩_s dt = ½ ε²a`, the effective diffusion
coefficient of (6.6.33). -/
theorem chem_effective_diffusion (a ε : ℝ) :
    (1 / 4) * ∫ t in Ioi (0 : ℝ), 4 * ε ^ 2 * a * Real.exp (-2 * t) = (1 / 2) * ε ^ 2 * a := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
  norm_num
  ring

/-- **(6.6.35), full system.**  The stationary covariance of the linear SDE (6.6.5), the solution
of the Lyapunov equation `JΣ + ΣJᵀ + ε²BBᵀ = 0` with `J = [[-1, γ], [1, -2γ]]` (written with `Jᵀ` explicit), is
`Σ = ε² diag(a, a/γ)` for every `γ > 0`. -/
theorem chem_stationary_covariance (γ a ε : ℝ) (hγ : γ ≠ 0) :
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![-1, γ; 1, -2 * γ]
    let Sg : Matrix (Fin 2) (Fin 2) ℝ := !![ε ^ 2 * a, 0; 0, ε ^ 2 * a / γ]
    let BB : Matrix (Fin 2) (Fin 2) ℝ := !![2 * a, -2 * a; -2 * a, 4 * a]
    J * Sg + Sg * !![-1, 1; γ, -2 * γ] + ε ^ 2 • BB = 0 := by
  intro J Sg BB
  simp only [J, Sg, BB, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-- **(6.6.33)–(6.6.35), reduced system.**  The stationary variance `V` of (6.6.33),
`dx = (a - x)/2 dt + ε√a dW`, solves `2·(-½)V + ε²a = 0`, i.e. `V = ε²a = ε²⟨x⟩_s`: exactly the
stationary variance of `x` in the full system. -/
theorem chem_reduced_stationary (a ε V : ℝ) (h : 2 * (-(1 / 2)) * V + ε ^ 2 * a = 0) :
    V = ε ^ 2 * a := by linarith

/-! ### The mean: reduced dynamics with rate `O(γ⁻¹)` -/

/-- **Mean of `x` in §6.6.1: rate `O(γ⁻¹)`.**  If `⟨x⟩, ⟨y⟩` solve (6.6.2), then for all `t ≥ 0`
`|⟨x⟩(t) - [a + (⟨x⟩(0) - a)e^{-t/2}]| ≤ |z₀|/(4γ) + √((⟨x⟩(0) - a)² + z₀²)/(4γ + 1)` with
`z₀ = 2γ⟨y⟩(0) - ⟨x⟩(0) - a`; `a + (⟨x⟩(0) - a)e^{-t/2}` solves the reduced equation
`ẋ = (a - x)/2`. -/
theorem chem_mean_rate {γ a : ℝ} (hγ : 0 < γ) (mx my : ℝ → ℝ)
    (hx : ∀ t, HasDerivAt mx (-mx t + γ * my t) t)
    (hy : ∀ t, HasDerivAt my (-2 * γ * my t + mx t + a) t) {t : ℝ} (ht : 0 ≤ t) :
    |mx t - (a + (mx 0 - a) * Real.exp (-(1 / 2) * t))|
      ≤ |2 * γ * my 0 - mx 0 - a| / (4 * γ)
        + Real.sqrt ((mx 0 - a) ^ 2 + (2 * γ * my 0 - mx 0 - a) ^ 2) / (4 * γ + 1) := by
  set c := 2 * γ + 1 / 2 with hc
  set u : ℝ → ℝ := fun t => mx t - a
  set z : ℝ → ℝ := fun t => 2 * γ * my t - mx t - a
  have hu : ∀ t, HasDerivAt u (-u t / 2 + z t / 2) t := fun t => by
    convert (hx t).sub_const a using 1; simp only [u, z]; ring
  have hz : ∀ t, HasDerivAt z (-c * z t + u t / 2) t := fun t => by
    convert (((hy t).const_mul (2 * γ)).sub (hx t)).sub_const a using 1
    simp only [u, z, c]; ring
  set z0 := |z 0|
  set R0 := Real.sqrt (u 0 ^ 2 + z 0 ^ 2)
  -- energy estimate
  have hE : ∀ s, 0 ≤ s → u s ^ 2 + z s ^ 2 ≤ u 0 ^ 2 + z 0 ^ 2 := fun s hs =>
    decay_compare (y := fun s => u s ^ 2 + z s ^ 2) (ψ := fun _ => u 0 ^ 2 + z 0 ^ 2)
      (ψ' := fun _ => 0) 0 (fun s => ((hu s).pow 2).add ((hz s).pow 2))
      (fun s => hasDerivAt_const _ _)
      (fun s _ => by
        simp only [c]; push_cast
        nlinarith [sq_nonneg (u s - z s), sq_nonneg (z s), hγ.le]) le_rfl hs
  have hR0 : 0 ≤ R0 := Real.sqrt_nonneg _
  have hus : ∀ s, 0 ≤ s → |u s| ≤ R0 := fun s hs => by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [hE s hs, sq_nonneg (z s)])
  have hc0 : 0 < c := by simp only [c]; linarith
  -- bound on the fast variable
  set ψz : ℝ → ℝ := fun s => z0 * Real.exp (-c * s) + R0 / (2 * c)
  have hψz : ∀ s, HasDerivAt ψz (z0 * (-c * Real.exp (-c * s))) s := fun s => by
    convert ((hasDerivAt_exp_mul (-c) s).const_mul z0).add_const (R0 / (2 * c)) using 1
  have hzb : ∀ s, 0 ≤ s → |z s| ≤ ψz s := fun s hs =>
    abs_decay_compare c hz hψz
      (fun r hr => by
        have := (abs_le.1 (hus r hr)).2
        simp only [ψz]; field_simp; nlinarith)
      (fun r hr => by
        have := (abs_le.1 (hus r hr)).1
        simp only [ψz]; field_simp; nlinarith)
      (by simp only [ψz, z0, mul_zero, Real.exp_zero, mul_one]
          have : 0 ≤ R0 / (2 * c) := by positivity
          linarith) hs
  -- comparison for the slow variable
  set d : ℝ → ℝ := fun s => u s - u 0 * Real.exp (-(1 / 2) * s)
  have hd : ∀ s, HasDerivAt d (-d s / 2 + z s / 2) s := fun s => by
    convert (hu s).sub ((hasDerivAt_exp_mul (-(1 / 2)) s).const_mul (u 0)) using 1
    simp only [d]; ring
  have h2c : 0 < 2 * c - 1 := by simp only [c]; linarith
  set ψd : ℝ → ℝ := fun s =>
    z0 / (2 * c - 1) * (Real.exp (-(1 / 2) * s) - Real.exp (-c * s)) + R0 / (2 * c)
  have hψd : ∀ s, HasDerivAt ψd (z0 / (2 * c - 1) * (-(1 / 2) * Real.exp (-(1 / 2) * s)
      - -c * Real.exp (-c * s))) s := fun s => by
    convert (((hasDerivAt_exp_mul (-(1 / 2)) s).sub (hasDerivAt_exp_mul (-c) s)).const_mul
      (z0 / (2 * c - 1))).add_const (R0 / (2 * c)) using 1
  have hz0 : 0 ≤ z0 := abs_nonneg _
  have key : ∀ s, 0 ≤ s → z0 / (2 * c - 1) * (-(1 / 2) * Real.exp (-(1 / 2) * s)
      - -c * Real.exp (-c * s)) + (1 / 2) * ψd s
      = (1 / 2) * ψz s := fun s _ => by
    simp only [ψd, ψz]; field_simp; ring
  have hdb := abs_decay_compare (1 / 2) hd hψd
    (fun r hr => by
      have h1 := (abs_le.1 (hzb r hr)).2
      have := key r hr
      nlinarith)
    (fun r hr => by
      have h1 := (abs_le.1 (hzb r hr)).1
      have := key r hr
      nlinarith)
    (by simp only [d, ψd, mul_zero, Real.exp_zero, mul_one, sub_self, abs_zero, zero_add]
        positivity) ht
  have hfin : ψd t ≤ z0 / (2 * c - 1) + R0 / (2 * c) := by
    simp only [ψd]
    have h1 : Real.exp (-(1 / 2) * t) - Real.exp (-c * t) ≤ 1 := by
      have := Real.exp_le_one_iff.2 (by nlinarith : -(1 / 2) * t ≤ 0)
      have := Real.exp_pos (-c * t)
      linarith
    have : 0 ≤ z0 / (2 * c - 1) := div_nonneg hz0 h2c.le
    nlinarith
  have e1 : 2 * c - 1 = 4 * γ := by simp only [c]; ring
  have e2 : 2 * c = 4 * γ + 1 := by simp only [c]; ring
  rw [e1, e2] at hfin
  have : mx t - (a + (mx 0 - a) * Real.exp (-(1 / 2) * t)) = d t := by simp only [d, u]; ring
  rw [this]
  exact hdb.trans hfin

/-- **Instance of `chem_mean_rate`.**  For every `γ > 0` and `x₀`, the functions
`⟨x⟩ = a + x₀μ(t)`, `⟨y⟩ = (a + x₀(μ(t) + ν(t)))/γ`, built from the propagator `μ = harmMu` of the
equivalent damped oscillator `τu'' + u' + ku = 0`, `τ = 1/(1+2γ)`, `k = γ/(1+2γ)`, solve the mean
equations (6.6.2) exactly, and the bound of `chem_mean_rate` applies to them. -/
theorem chem_mean_instance {γ a x₀ : ℝ} (hγ : 0 < γ) :
    ∃ mx my : ℝ → ℝ, mx 0 = a + x₀ ∧
      (∀ t, HasDerivAt mx (-mx t + γ * my t) t) ∧
      (∀ t, HasDerivAt my (-2 * γ * my t + mx t + a) t) ∧
      ∀ t, 0 ≤ t → |mx t - (a + (mx 0 - a) * Real.exp (-(1 / 2) * t))|
        ≤ |2 * γ * my 0 - mx 0 - a| / (4 * γ)
          + Real.sqrt ((mx 0 - a) ^ 2 + (2 * γ * my 0 - mx 0 - a) ^ 2) / (4 * γ + 1) := by
  set τ := 1 / (1 + 2 * γ)
  set k := γ / (1 + 2 * γ)
  have hτ : 0 < τ := by positivity
  have h12 : (0 : ℝ) < 1 + 2 * γ := by linarith
  have hkτ : 4 * k * τ < 1 := by
    simp only [k, τ]
    rw [show 4 * (γ / (1 + 2 * γ)) * (1 / (1 + 2 * γ)) = 4 * γ / (1 + 2 * γ) ^ 2 by
      field_simp]
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg γ]
  obtain ⟨hne, hs, hp⟩ := harm_roots hτ hkτ
  set lp := (-1 + Real.sqrt (1 - 4 * k * τ)) / (2 * τ)
  set lm := (-1 - Real.sqrt (1 - 4 * k * τ)) / (2 * τ)
  have hmu := fun t => (harm_mean_sol hτ hne hs hp t).1
  have hnu := fun t => (harm_mean_sol hτ hne hs hp t).2
  have hmu0 : harmMu lp lm 0 = 1 := by
    simp only [harmMu, mul_zero, Real.exp_zero, mul_one]; field_simp [sub_ne_zero.2 hne]
  set mx : ℝ → ℝ := fun t => a + x₀ * harmMu lp lm t
  set my : ℝ → ℝ := fun t => (a + x₀ * (harmMu lp lm t + harmNu lp lm t)) / γ
  have hx : ∀ t, HasDerivAt mx (-mx t + γ * my t) t := fun t => by
    convert ((hmu t).const_mul x₀).const_add a using 1
    simp only [mx, my]; field_simp; ring
  have hy : ∀ t, HasDerivAt my (-2 * γ * my t + mx t + a) t := fun t => by
    convert ((((hmu t).add (hnu t)).const_mul x₀).const_add a).div_const γ using 1
    simp only [mx, my, τ, k]; field_simp; ring
  refine ⟨mx, my, by simp [mx, hmu0], hx, hy, fun t ht => chem_mean_rate hγ mx my hx hy ht⟩

end Gardiner.Adiabatic
