/-
# Boundary conditions and the initial layer (Gardiner §6.4.4, §6.4.5 (b)–(c))

Gardiner, *Handbook of Stochastic Methods*, (6.4.81)–(6.4.89) and (6.4.109)–(6.4.113).

* (6.4.82)–(6.4.83): an absorbing barrier gives `p̂(a) = 0` (`Gardiner.Adiabatic.absorbing_marginal`).
* (6.4.84) ⟺ (6.4.85): for `u ≠ 0`, `p(u, a) = p(-u, a)` iff the normal current leaving at
  `(u, a)` equals the one entering at `(-u, a)` (`Gardiner.Adiabatic.reflecting_iff_current`).
  The current (6.4.85) is printed with the overall sign reversed (`J_y = up` for
  `∂ₜp = -∂_y(up) + …`); this is immaterial for the equivalence.
* (6.4.86)–(6.4.89): a reflecting barrier makes `w = (1 - P)p` even in `u`
  (`Gardiner.Adiabatic.reflecting_w_even`); since the leading part of `w` is proportional to the odd
  function `P₁` (6.4.88), its coefficient `U'p̂ + ∂_y p̂` vanishes at the barrier: the
  Smoluchowski reflecting condition (6.4.89) (`Gardiner.Adiabatic.reflecting_smoluchowski`).
* (6.4.109): the perturbed test function of `Gardiner.Adiabatic.kramers_generator_expansion` has
  Maxwellian average `f - γ⁻² A*f`; dually, the corrected Smoluchowski equation starts from
  `(1 - γ⁻²∂_y(U' + ∂_y)) p̂(y, 0)` (`Gardiner.Adiabatic.kramers_initial_layer`).  The only
  property of the Maxwellian used is its first four moments `0, 1, 0, 3`; the instance
  `Gardiner.Adiabatic.kramers_initial_layer_instance` uses the three-point law on
  `{-√3, 0, √3}` with the same moments.
* (6.4.110): the boundary-layer scaling `z = γy`, `τ = γt` (`Gardiner.Adiabatic.boundary_rescaling`).
* (6.4.112)–(6.4.113): `ψ₀ = e^{-u²/2}` and `ψ₀' = (z - u)e^{-u²/2}` are stationary solutions of
  the zero-order operator `∂ᵤ(u + ∂ᵤ) - u∂_z` (`Gardiner.Adiabatic.psi0_stationary`,
  `Gardiner.Adiabatic.psi0'_stationary`).
-/
import SHSLib.Gardiner.Adiabatic.KramersGenerator

open MeasureTheory

noncomputable section

namespace Gardiner.Adiabatic

/-- **(6.4.82)–(6.4.83)**: if `p(u, a) = 0` for all `u`, then `p̂(a) = ∫ p(u, a) du = 0`. -/
theorem absorbing_marginal (p : ℝ → ℝ) (h : ∀ u, p u = 0) : ∫ u, p u = 0 := by
  simp [h]

/-- **(6.4.84) ⟺ (6.4.85)**: with `J_y(u) = u p(u, a)`, for `u ≠ 0`,
`p(u, a) = p(-u, a)` iff `J_y(u) = -J_y(-u)` (outgoing current at `(u, a)` equals incoming
current at `(-u, a)`). -/
theorem reflecting_iff_current (p : ℝ → ℝ) {u : ℝ} (hu : u ≠ 0) :
    p u = p (-u) ↔ u * p u = -((-u) * p (-u)) := by
  constructor
  · intro h; rw [h]; ring
  · intro h
    have : u * (p u - p (-u)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hu
    · linarith

/-- **(6.4.86)**: if `p(·, a)` is even in `u`, so is `w = p - P p = p - p̂(a) gauss`. -/
theorem reflecting_w_even (p : ℝ → ℝ) (phat : ℝ) (h : ∀ u, p (-u) = p u) (u : ℝ) :
    p (-u) - phat * gauss (-u) = p u - phat * gauss u := by
  simp [h, gauss]

/-- **(6.4.87)–(6.4.89)**: if `w` is even in `u` and equal to `-c P₁(u) ∝ -c u e^{-u²/2}`
(with `c = γ⁻¹[U'p̂ + ∂_y p̂]_{y=a}`, (6.4.88)), then `c = 0`: the reflecting boundary condition
of the Smoluchowski equation. -/
theorem reflecting_smoluchowski (w : ℝ → ℝ) (c : ℝ) (heven : ∀ u, w (-u) = w u)
    (hodd : ∀ u, w u = -c * (u * gauss u)) : c = 0 := by
  have h := heven 1
  rw [hodd, hodd] at h
  have hg : gauss (-1) = gauss 1 := by simp [gauss]
  rw [hg] at h
  have : c * gauss 1 = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact h1
  · exact absurd h1 (Real.exp_pos _).ne'

/-! ### (6.4.109): the initial layer -/

/-- **(6.4.109) in dual form.**  Let `E` be a linear functional on functions of `u` with the
moments of the Maxwellian, `E[1] = 1`, `E[u] = 0`, `E[u²] = 1`, `E[u³] = 0`, `E[u⁴] = 3`.  Then
the perturbed test function of `kramers_generator_expansion` averages to
`E[φ_γ(y, ·)] = f(y) - γ⁻² A*f(y)`: the corrected Smoluchowski dynamics starts from
`(1 - γ⁻²∂_y(U' + ∂_y))p̂(y, 0)` rather than from `p̂(y, 0)`. -/
theorem kramers_initial_layer (Ef : (ℝ → ℝ) →ₗ[ℝ] ℝ) (h0 : Ef (fun _ => 1) = 1)
    (h1 : Ef (fun u => u) = 0) (h2 : Ef (fun u => u ^ 2) = 1) (h3 : Ef (fun u => u ^ 3) = 0)
    (h4 : Ef (fun u => u ^ 4) = 3) (U F : ℕ → ℝ → ℝ) (ε y : ℝ) :
    Ef (fun u => kφ U F ε y u) = F 0 y - ε ^ 2 * smolGen U F y := by
  have e : (fun u => kφ U F ε y u) = ((F 0 y + ε ^ 2 * (-F 2 y / 2 - F 2 y + U 1 y * F 1 y) + ε ^ 4 * (3 * F 4 y / 24
          - kc4 U F y)) • (fun _ : ℝ => (1 : ℝ))
        + (ε * F 1 y + ε ^ 3 * (-3 * F 3 y / 6 + U 2 y * F 1 y)) • (fun u : ℝ => u)
        + (ε ^ 2 * (F 2 y / 2) + ε ^ 4 * (-6 * F 4 y / 24 + kc4 U F y)) • (fun u : ℝ => u ^ 2)
        + (ε ^ 3 * (F 3 y / 6)) • (fun u : ℝ => u ^ 3)
        + (ε ^ 4 * (F 4 y / 24)) • (fun u : ℝ => u ^ 4) : ℝ → ℝ) := by
    funext u
    simp only [kφ, kφ2, kφ3, kφ4, He, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  simp only [map_add, map_smul, h0, h1, h2, h3, h4, smul_eq_mul, smolGen]
  ring

/-- The three-point law `P(u = ±√3) = 1/6`, `P(u = 0) = 2/3`, which shares the first four
moments of the Maxwellian. -/
def threePoint : (ℝ → ℝ) →ₗ[ℝ] ℝ where
  toFun h := h (-Real.sqrt 3) / 6 + 2 * h 0 / 3 + h (Real.sqrt 3) / 6
  map_add' f g := by simp only [Pi.add_apply]; ring
  map_smul' c f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- **Instance of `kramers_initial_layer`**: for the double well `U = y⁴/4 - y²/2` and
`f = sin`, the average of the perturbed test function is `sin y - γ⁻² A* sin (y)`. -/
theorem kramers_initial_layer_instance (ε y : ℝ) :
    threePoint (fun u => kφ dwU sinTower ε y u) = sinTower 0 y - ε ^ 2 * smolGen dwU sinTower y := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h4 : Real.sqrt 3 ^ 4 = 9 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hs]; norm_num
  have h3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, hs]
  refine kramers_initial_layer threePoint ?_ ?_ ?_ ?_ ?_ dwU sinTower ε y
  · simp [threePoint]; norm_num
  · simp [threePoint]; ring
  · simp only [threePoint, LinearMap.coe_mk, AddHom.coe_mk]; rw [neg_sq, hs]; norm_num
  · simp only [threePoint, LinearMap.coe_mk, AddHom.coe_mk]; rw [neg_pow, h3]; norm_num; ring
  · simp only [threePoint, LinearMap.coe_mk, AddHom.coe_mk]; rw [neg_pow, h4]; norm_num

/-! ### (6.4.110)–(6.4.113): the boundary layer -/

/-- **(6.4.110)**: rescaling `z = γy`, `τ = γt`.  If `P(z, τ) = p(z/γ, τ/γ)` then
`∂_τ P = γ⁻¹ ∂ₜ p` and `∂_z P = γ⁻¹ ∂_y p`, so the Kramers equation
`∂ₜp = γ L₁ p - u ∂_y p + U'(y) ∂ᵤ p` becomes `∂_τ P = L₁P - u∂_zP + γ⁻¹U'(z/γ)∂ᵤP`. -/
theorem boundary_rescaling {γ : ℝ} (hγ : γ ≠ 0) {g : ℝ → ℝ} {s g' : ℝ}
    (hg : HasDerivAt g g' (s / γ)) (pt L1p py pu U1 u : ℝ)
    (hK : pt = γ * L1p - u * py + U1 * pu) :
    HasDerivAt (fun s => g (s / γ)) (g' / γ) s ∧
      pt / γ = L1p - u * (py / γ) + γ⁻¹ * U1 * pu := by
  refine ⟨?_, ?_⟩
  · have := hg.comp s ((hasDerivAt_id s).div_const γ)
    simpa [Function.comp, div_eq_mul_inv, mul_comm] using this
  · rw [hK]; field_simp

/-- **(6.4.112)**: `ψ₀ = e^{-u²/2}` is a stationary solution of `∂ᵤ(u + ∂ᵤ) - u∂_z`: its flux
`uψ₀ + ∂ᵤψ₀` vanishes identically and `∂_zψ₀ = 0`. -/
theorem psi0_stationary (u : ℝ) :
    HasDerivAt gauss (-u * gauss u) u ∧ u * gauss u + -u * gauss u = 0 :=
  ⟨hasDerivAt_gauss u, by ring⟩

/-- **(6.4.113)**: `ψ₀' = (z - u)e^{-u²/2}` is a stationary solution of `∂ᵤ(u + ∂ᵤ) - u∂_z`: with
`∂ᵤψ₀' = (-1 - u(z - u))e^{-u²/2}`, the flux `uψ₀' + ∂ᵤψ₀' = -e^{-u²/2}` has `u`-derivative
`u e^{-u²/2} = u ∂_zψ₀'`. -/
theorem psi0'_stationary (z u : ℝ) :
    HasDerivAt (fun u => (z - u) * gauss u) ((-1 - u * (z - u)) * gauss u) u ∧
      HasDerivAt (fun z => (z - u) * gauss u) (gauss u) z ∧
      HasDerivAt (fun u => u * ((z - u) * gauss u) + (-1 - u * (z - u)) * gauss u)
        (u * gauss u) u ∧
      u * gauss u - u * gauss u = 0 := by
  refine ⟨?_, ?_, ?_, by ring⟩
  · convert ((hasDerivAt_const u z).sub (hasDerivAt_id u)).mul (hasDerivAt_gauss u) using 1
    simp; ring
  · convert ((hasDerivAt_id z).sub_const u).mul_const (gauss u) using 1; simp
  · have e : (fun u => u * ((z - u) * gauss u) + (-1 - u * (z - u)) * gauss u)
        = fun u => -gauss u := by funext u; ring
    rw [e]
    convert (hasDerivAt_gauss u).neg using 1; ring

end Gardiner.Adiabatic
