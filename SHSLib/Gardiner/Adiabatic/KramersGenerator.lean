/-
# Kramers' equation: the Smoluchowski generator and its `γ⁻²` correction

Gardiner, *Handbook of Stochastic Methods*, §6.4.1 (6.4.54)–(6.4.66) and §6.4.5
(6.4.100)–(6.4.108), in the units (6.4.56) `½D = k = 1`, with the scaled velocity `u` and
position `y`.  The forward operators are (6.4.55)

`L₁ = ∂ᵤ(u + ∂ᵤ)`,   `L₂ = -u ∂_y + U'(y) ∂ᵤ`,

and the Kramers equation is `∂ₜp = (γL₁ + L₂)p`.  Their adjoints (backward operators) are
`L₁* = ∂ᵤ² - u∂ᵤ` (the Ornstein–Uhlenbeck generator) and `L₂* = u∂_y - U'(y)∂ᵤ`.

## Gaussian weight and Hermite functions

`P_n(u) = (2π)^{-1/2} e^{-u²/2} Q_n(u)` (6.4.57).  The identity
`L₁(q(u) e^{-u²/2}) = (q'' - u q') e^{-u²/2}` (`Gardiner.Adiabatic.L1_gauss`) reduces the
eigenvalue relation (6.4.59) to the Hermite equations `He_n'' - u He_n' = -n He_n`
(`Gardiner.Adiabatic.hermite_eigen`), and the actions (6.4.62), (6.4.64), (6.4.103) of `L₂` to
polynomial identities (`Gardiner.Adiabatic.L2_P0`, `L2_P1`, `L2_P2`).  We use the probabilists'
Hermite polynomials `He₁ = u`, `He₂ = u² - 1`, `He₃ = u³ - 3u`, `He₄ = u⁴ - 6u² + 3`; Gardiner's
`Q_n = He_n / √(n!)`.

## Approximation guarantee: generator form of (6.4.66) and (6.4.108)

`Gardiner.Adiabatic.kramers_generator_expansion`: for every smooth test function `f(y)` and
potential `U` there is an explicit lift `φ_γ(y, u) = f(y) + γ⁻¹ u f'(y) + γ⁻² φ₂ + γ⁻³ φ₃ + γ⁻⁴ φ₄`
(a *perturbed test function*, whose corrections are mean-zero Hermite polynomials in `u`) with

`(γL₁* + L₂*) φ_γ = γ⁻¹ A*f + γ⁻³ (C + DA)* f + γ⁻⁴ R`,

where `A*f = f'' - U'f'` is the backward Smoluchowski operator (adjoint of (6.4.66)),
`(C + DA)* f = U''(f'' - U'f') + U'''f'` is the adjoint of the correction (6.4.107), and the
remainder `R` (`Gardiner.Adiabatic.kRem`) is an explicit polynomial in `u` and the derivatives
`f', …, f⁽⁵⁾`, `U', …, U⁗` that does not depend on `γ`.  There is **no `γ⁻²` term**, which is the
statement `B = 0` of (6.4.104).  `Gardiner.Adiabatic.kRem_le` bounds
`|R| ≤ 9 M (1 + K)² (1 + |u|)⁵` when `|f⁽ᵏ⁾| ≤ M` (`1 ≤ k ≤ 5`) and `|U⁽ᵏ⁾| ≤ K` (`1 ≤ k ≤ 4`);
`Gardiner.Adiabatic.kramers_smoluchowski_bound` and
`Gardiner.Adiabatic.kramers_corrected_bound` are the resulting `O(γ⁻³)` and `O(γ⁻⁴)` bounds on
the distance between the Kramers dynamics and the (corrected) Smoluchowski dynamics.  The choice
`φ₂ = ½He₂ f'' - A*f` of the `u`-independent part of `φ₂` is exactly the one that removes
`(A*)²f` from the `γ⁻³` coefficient; it corresponds to the initial-layer modification
`(1 + γ⁻²D)v(0)` of (6.4.101).

`Gardiner.Adiabatic.kramers_doubleWell` applies the expansion to the concrete double well
`U = y⁴/4 - y²/2` and test function `f = sin`.
-/
import SHSLib.Gardiner.Approx.Calculus

open Set

noncomputable section

namespace Gardiner.Adiabatic

/-! ### Gaussian weight: `L₁` on `q(u) e^{-u²/2}` -/

/-- The (unnormalised) Maxwellian `e^{-u²/2}`. -/
def gauss (u : ℝ) : ℝ := Real.exp (-u ^ 2 / 2)

lemma hasDerivAt_gauss (u : ℝ) : HasDerivAt gauss (-u * gauss u) u := by
  have := ((hasDerivAt_pow 2 u).neg.div_const 2).exp
  convert this using 1
  simp [gauss]; ring

/-- **(6.4.59), reduced to polynomials.**  If `q` has derivatives `q₁, q₂`, then
`∂ᵤ(u (q gauss) + ∂ᵤ(q gauss)) = (q₂ - u q₁) gauss`: on Gaussian-weighted functions the forward
operator `L₁ = ∂ᵤ(u + ∂ᵤ)` acts as the backward operator `L₁* = ∂ᵤ² - u ∂ᵤ` on the weight. -/
theorem L1_gauss {q q₁ q₂ : ℝ → ℝ} (hq : ∀ u, HasDerivAt q (q₁ u) u)
    (hq₁ : ∀ u, HasDerivAt q₁ (q₂ u) u) (u : ℝ) :
    HasDerivAt (fun u => q₁ u * gauss u) ((q₂ u - u * q₁ u) * gauss u) u ∧
      (∀ u, HasDerivAt (fun u => q u * gauss u) ((q₁ u - u * q u) * gauss u) u) := by
  refine ⟨?_, fun u => ?_⟩
  · convert (hq₁ u).mul (hasDerivAt_gauss u) using 1; ring
  · convert (hq u).mul (hasDerivAt_gauss u) using 1; ring

/-- The flux `u p + ∂ᵤp` of `p = q gauss` is `q₁ gauss`, so `L₁ p = ∂ᵤ(q₁ gauss)`. -/
lemma flux_gauss (q q₁ : ℝ → ℝ) (u : ℝ) :
    u * (q u * gauss u) + (q₁ u - u * q u) * gauss u = q₁ u * gauss u := by ring

/-- Probabilists' Hermite polynomials `He₀, …, He₄`. -/
def He : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun u => u
  | 2 => fun u => u ^ 2 - 1
  | 3 => fun u => u ^ 3 - 3 * u
  | 4 => fun u => u ^ 4 - 6 * u ^ 2 + 3
  | _ => fun _ => 0

/-- Derivatives of `He_n`: `He_n' = n He_{n-1}`. -/
lemma hasDerivAt_He (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) (u : ℝ) :
    HasDerivAt (He n) (n * He (n - 1) u) u := by
  interval_cases n
  · simpa [He] using hasDerivAt_id u
  · convert (hasDerivAt_pow 2 u).sub_const 1 using 1; simp [He]
  · convert (hasDerivAt_pow 3 u).sub ((hasDerivAt_id u).const_mul 3) using 1; simp [He]; ring
  · convert ((hasDerivAt_pow 4 u).sub ((hasDerivAt_pow 2 u).const_mul 6)).add_const 3 using 1
    simp [He]; ring

/-- **(6.4.59)**: `He_n'' - u He_n' = -n He_n`, i.e. `L₁ P_n = -n P_n`, for `n ≤ 4`. -/
theorem hermite_eigen (n : ℕ) (hn4 : n ≤ 4) (u : ℝ) :
    (n * ((n - 1 : ℕ) : ℝ) * He (n - 2) u) - u * (n * He (n - 1) u) = -n * He n u := by
  interval_cases n <;> simp [He] <;> ring

/-- **(6.4.60)** (three-term recursion): `u He_n = He_{n+1} + n He_{n-1}`, `1 ≤ n ≤ 3`. -/
theorem hermite_recursion (n : ℕ) (hn : 1 ≤ n) (hn3 : n ≤ 3) (u : ℝ) :
    u * He n u = He (n + 1) u + n * He (n - 1) u := by
  interval_cases n <;> simp [He] <;> ring

/-- The action of `L₂ = -u ∂_y + U' ∂ᵤ` on `q(u) gauss(u) h(y)`, divided by `gauss`:
`-u q h' + U' (q' - u q) h`. -/
def L2poly (U1 q q1 h h1 u : ℝ) : ℝ := -u * q * h1 + U1 * (q1 - u * q) * h

/-- **(6.4.62)**: `L₂(P₀ p̂) = -(U' + ∂_y) p̂ P₁`. -/
theorem L2_P0 (U1 h h1 u : ℝ) :
    L2poly U1 (He 0 u) 0 h h1 u = -(U1 * h + h1) * He 1 u := by
  simp [L2poly, He]; ring

/-- **(6.4.64)**: `L₂(P₁ h) = -(√2 P₂ + P₀) ∂_y h - √2 P₂ U' h`; with `P_n ∝ He_n/√(n!)` this is
`-(He₂ + He₀) h' - He₂ U' h`. -/
theorem L2_P1 (U1 h h1 u : ℝ) :
    L2poly U1 (He 1 u) 1 h h1 u = -(He 2 u + He 0 u) * h1 - He 2 u * U1 * h := by
  simp [L2poly, He]; ring

/-- **(6.4.103)**: `L₂(He₂ h) = -He₃ U' h - (He₃ + 2He₁) h'` (Gardiner:
`L₂P₂ = -√3 U'P₃ - ∂_y(√3 P₃ + √2 P₁)`). -/
theorem L2_P2 (U1 h h1 u : ℝ) :
    L2poly U1 (He 2 u) (2 * u) h h1 u = -He 3 u * U1 * h - (He 3 u + 2 * He 1 u) * h1 := by
  simp [L2poly, He]; ring

/-! ### The backward Kramers generator and the perturbed test function -/

/-- The backward Kramers generator `(γL₁* + L₂*)φ = γ(φ_uu - uφ_u) + uφ_y - U'φ_u`, acting on a
function with partial derivatives `φ_y, φ_u, φ_uu` at `(y, u)`. -/
def kGen (γ U1 u φy φu φuu : ℝ) : ℝ := γ * (φuu - u * φu) + u * φy - U1 * φu

/-- The backward Smoluchowski operator `A*f = f'' - U'f'` (adjoint of (6.4.66)). -/
def smolGen (U F : ℕ → ℝ → ℝ) (y : ℝ) : ℝ := F 2 y - U 1 y * F 1 y

/-- The adjoint `(C + DA)*f = U''(f'' - U'f') + U'''f'` of the correction (6.4.107). -/
def smolCorr (U F : ℕ → ℝ → ℝ) (y : ℝ) : ℝ :=
  U 2 y * (F 2 y - U 1 y * F 1 y) + U 3 y * F 1 y

/-- Second-order corrector `φ₂ = ½He₂ f'' - A*f`. -/
def kφ2 (U F : ℕ → ℝ → ℝ) (y u : ℝ) : ℝ :=
  He 2 u * F 2 y / 2 - F 2 y + U 1 y * F 1 y

/-- Third-order corrector `φ₃ = He₃ f'''/6 + u U'' f'`. -/
def kφ3 (U F : ℕ → ℝ → ℝ) (y u : ℝ) : ℝ := He 3 u * F 3 y / 6 + u * U 2 y * F 1 y

/-- The coefficient of `He₂` in `φ₄`. -/
def kc4 (U F : ℕ → ℝ → ℝ) (y : ℝ) : ℝ :=
  F 4 y / 4 + (U 3 y * F 1 y + U 2 y * F 2 y) / 2 - U 1 y * F 3 y / 4

/-- Fourth-order corrector `φ₄ = He₄ f⁗/24 + He₂ c₄`. -/
def kφ4 (U F : ℕ → ℝ → ℝ) (y u : ℝ) : ℝ := He 4 u * F 4 y / 24 + He 2 u * kc4 U F y

/-- The perturbed test function `φ_γ = f + εuf' + ε²φ₂ + ε³φ₃ + ε⁴φ₄`, `ε = γ⁻¹`. -/
def kφ (U F : ℕ → ℝ → ℝ) (ε y u : ℝ) : ℝ :=
  F 0 y + ε * u * F 1 y + ε ^ 2 * kφ2 U F y u + ε ^ 3 * kφ3 U F y u + ε ^ 4 * kφ4 U F y u

/-- `y`-derivative of `c₄`. -/
def kc4y (U F : ℕ → ℝ → ℝ) (y : ℝ) : ℝ :=
  F 5 y / 4 + (U 4 y * F 1 y + U 3 y * F 2 y + (U 3 y * F 2 y + U 2 y * F 3 y)) / 2
    - (U 2 y * F 3 y + U 1 y * F 4 y) / 4

/-- `∂_y φ_γ`. -/
def kφy (U F : ℕ → ℝ → ℝ) (ε y u : ℝ) : ℝ :=
  F 1 y + ε * u * F 2 y
    + ε ^ 2 * (He 2 u * F 3 y / 2 - F 3 y + (U 2 y * F 1 y + U 1 y * F 2 y))
    + ε ^ 3 * (He 3 u * F 4 y / 6 + u * (U 3 y * F 1 y + U 2 y * F 2 y))
    + ε ^ 4 * (He 4 u * F 5 y / 24 + He 2 u * kc4y U F y)

/-- `∂ᵤ φ_γ`. -/
def kφu (U F : ℕ → ℝ → ℝ) (ε y u : ℝ) : ℝ :=
  ε * F 1 y + ε ^ 2 * (u * F 2 y) + ε ^ 3 * (3 * He 2 u * F 3 y / 6 + U 2 y * F 1 y)
    + ε ^ 4 * (4 * He 3 u * F 4 y / 24 + 2 * u * kc4 U F y)

/-- `∂ᵤ² φ_γ`. -/
def kφuu (U F : ℕ → ℝ → ℝ) (ε y u : ℝ) : ℝ :=
  ε ^ 2 * F 2 y + ε ^ 3 * (u * F 3 y) + ε ^ 4 * (He 2 u * F 4 y / 2 + 2 * kc4 U F y)

/-- The remainder `R = L₂*φ₄ = u ∂_yφ₄ - U' ∂ᵤφ₄`, independent of `γ`. -/
def kRem (U F : ℕ → ℝ → ℝ) (y u : ℝ) : ℝ :=
  u * (He 4 u * F 5 y / 24 + He 2 u * kc4y U F y)
    - U 1 y * (4 * He 3 u * F 4 y / 24 + 2 * u * kc4 U F y)

section Tower

variable {U F : ℕ → ℝ → ℝ}

lemma hasDerivAt_kc4 (hU : ∀ k y, HasDerivAt (U k) (U (k + 1) y) y)
    (hF : ∀ k y, HasDerivAt (F k) (F (k + 1) y) y) (y : ℝ) :
    HasDerivAt (kc4 U F) (kc4y U F y) y := by
  have h := (((hF 4 y).div_const 4).add ((((hU 3 y).mul (hF 1 y)).add
    ((hU 2 y).mul (hF 2 y))).div_const 2)).sub (((hU 1 y).mul (hF 3 y)).div_const 4)
  convert h using 1

/-- `∂_y φ_γ = kφy`. -/
theorem hasDerivAt_kφ_y (hU : ∀ k y, HasDerivAt (U k) (U (k + 1) y) y)
    (hF : ∀ k y, HasDerivAt (F k) (F (k + 1) y) y) (ε y u : ℝ) :
    HasDerivAt (fun y => kφ U F ε y u) (kφy U F ε y u) y := by
  have h2 : HasDerivAt (fun y => kφ2 U F y u)
      (He 2 u * F 3 y / 2 - F 3 y + (U 2 y * F 1 y + U 1 y * F 2 y)) y := by
    have := ((((hF 2 y).const_mul (He 2 u)).div_const 2).sub (hF 2 y)).add
      ((hU 1 y).mul (hF 1 y))
    convert this using 1
  have h3 : HasDerivAt (fun y => kφ3 U F y u)
      (He 3 u * F 4 y / 6 + u * (U 3 y * F 1 y + U 2 y * F 2 y)) y := by
    have := (((hF 3 y).const_mul (He 3 u)).div_const 6).add
      (((hU 2 y).mul (hF 1 y)).const_mul u)
    convert this using 1
    all_goals first | rfl | (funext v; simp only [kφ3, Pi.add_apply, Pi.mul_apply]; ring)
  have h4 : HasDerivAt (fun y => kφ4 U F y u)
      (He 4 u * F 5 y / 24 + He 2 u * kc4y U F y) y := by
    have := (((hF 4 y).const_mul (He 4 u)).div_const 24).add
      ((hasDerivAt_kc4 hU hF y).const_mul (He 2 u))
    convert this using 1
  have := (((((hF 0 y).add ((hF 1 y).const_mul (ε * u))).add (h2.const_mul (ε ^ 2))).add
    (h3.const_mul (ε ^ 3))).add (h4.const_mul (ε ^ 4)))
  convert this using 1

end Tower

/-- `∂ᵤ φ_γ = kφu`. -/
theorem hasDerivAt_kφ_u (U F : ℕ → ℝ → ℝ) (ε y u : ℝ) :
    HasDerivAt (fun u => kφ U F ε y u) (kφu U F ε y u) u := by
  have d2 := hasDerivAt_He 2 (by norm_num) (by norm_num) u
  have d3 := hasDerivAt_He 3 (by norm_num) (by norm_num) u
  have d4 := hasDerivAt_He 4 (by norm_num) (by norm_num) u
  have := ((((hasDerivAt_const u (F 0 y)).add (((hasDerivAt_id u).const_mul ε).mul_const (F 1 y))).add
    ((((d2.mul_const (F 2 y)).div_const 2).sub_const (F 2 y)).add_const (U 1 y * F 1 y)
      |>.const_mul (ε ^ 2))).add
    ((((d3.mul_const (F 3 y)).div_const 6).add ((hasDerivAt_id u).mul_const (U 2 y * F 1 y)))
      |>.const_mul (ε ^ 3))).add
    ((((d4.mul_const (F 4 y)).div_const 24).add (d2.mul_const (kc4 U F y))) |>.const_mul (ε ^ 4))
  convert this using 1
  · funext v; simp only [kφ, kφ2, kφ3, kφ4, id, Pi.add_apply]; ring
  · simp only [kφu, He]; push_cast; ring

/-- `∂ᵤ² φ_γ = kφuu`. -/
theorem hasDerivAt_kφ_uu (U F : ℕ → ℝ → ℝ) (ε y u : ℝ) :
    HasDerivAt (fun u => kφu U F ε y u) (kφuu U F ε y u) u := by
  have d2 := hasDerivAt_He 2 (by norm_num) (by norm_num) u
  have d3 := hasDerivAt_He 3 (by norm_num) (by norm_num) u
  have := ((((hasDerivAt_const u (ε * F 1 y)).add
    (((hasDerivAt_id u).mul_const (F 2 y)).const_mul (ε ^ 2))).add
    ((((d2.const_mul 3).mul_const (F 3 y)).div_const 6).add_const (U 2 y * F 1 y)
      |>.const_mul (ε ^ 3))).add
    (((((d3.const_mul 4).mul_const (F 4 y)).div_const 24).add
      (((hasDerivAt_id u).const_mul 2).mul_const (kc4 U F y))) |>.const_mul (ε ^ 4)))
  convert this using 1
  simp only [kφuu, He]; push_cast; ring

/-- **Generator form of (6.4.66), (6.4.104) and (6.4.108).**  With `ε = γ⁻¹`, the backward
Kramers generator applied to the perturbed test function `φ_γ` is exactly
`ε A*f + ε³ (C + DA)*f + ε⁴ R`: the `ε⁰` and `ε²` terms vanish (`B = 0`), the `ε` term is the
Smoluchowski operator (6.4.66), the `ε³` term is the correction (6.4.107)–(6.4.108), and the
remainder `R = kRem` does not depend on `γ`. -/
theorem kramers_generator_expansion (U F : ℕ → ℝ → ℝ) {ε : ℝ} (hε : ε ≠ 0) (y u : ℝ) :
    kGen ε⁻¹ (U 1 y) u (kφy U F ε y u) (kφu U F ε y u) (kφuu U F ε y u)
      = ε * smolGen U F y + ε ^ 3 * smolCorr U F y + ε ^ 4 * kRem U F y u := by
  simp only [kGen, kφy, kφu, kφuu, smolGen, smolCorr, kRem, kc4, kc4y, He]
  field_simp
  ring

/-- The perturbed test function is close to `f`: `φ_γ - f = ε u f' + O(ε²)` (explicitly). -/
theorem kφ_sub (U F : ℕ → ℝ → ℝ) (ε y u : ℝ) :
    kφ U F ε y u - F 0 y - ε * u * F 1 y
      = ε ^ 2 * (kφ2 U F y u + ε * kφ3 U F y u + ε ^ 2 * kφ4 U F y u) := by
  simp only [kφ]; ring

lemma abs_He2_le (u : ℝ) : |He 2 u| ≤ (1 + |u|) ^ 2 := by
  simp only [He]
  rw [abs_le]; constructor <;> nlinarith [abs_nonneg u, sq_abs u]

lemma abs_He3_le (u : ℝ) : |He 3 u| ≤ 3 * (1 + |u|) ^ 3 := by
  simp only [He]
  have ha := abs_nonneg u
  have e : |u ^ 3 - 3 * u| ≤ |u| ^ 3 + 3 * |u| := by
    calc |u ^ 3 - 3 * u| ≤ |u ^ 3| + |3 * u| := abs_sub _ _
      _ = |u| ^ 3 + 3 * |u| := by rw [abs_pow, abs_mul]; norm_num
  refine e.trans ?_
  nlinarith [pow_nonneg ha 2, pow_nonneg ha 3]

lemma abs_He4_le (u : ℝ) : |He 4 u| ≤ 3 * (1 + |u|) ^ 4 := by
  simp only [He]
  have ha := abs_nonneg u
  have e : |u ^ 4 - 6 * u ^ 2 + 3| ≤ |u| ^ 4 + 6 * |u| ^ 2 + 3 := by
    calc |u ^ 4 - 6 * u ^ 2 + 3| ≤ |u ^ 4 - 6 * u ^ 2| + |(3 : ℝ)| := abs_add_le _ _
      _ ≤ |u ^ 4| + |6 * u ^ 2| + |(3 : ℝ)| := by gcongr; exact abs_sub _ _
      _ = |u| ^ 4 + 6 * |u| ^ 2 + 3 := by rw [abs_pow, abs_mul, abs_pow]; norm_num
  refine e.trans ?_
  nlinarith [pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4]

set_option maxHeartbeats 1000000 in
/-- **Explicit bound on the remainder.**  If `|f⁽ᵏ⁾(y)| ≤ M` for `1 ≤ k ≤ 5` and
`|U⁽ᵏ⁾(y)| ≤ K` for `1 ≤ k ≤ 4`, then `|R(y, u)| ≤ 9M(1 + K)²(1 + |u|)⁵`. -/
theorem kRem_le (U F : ℕ → ℝ → ℝ) (y u M K : ℝ)
    (hF : ∀ k, 1 ≤ k → k ≤ 5 → |F k y| ≤ M) (hU : ∀ k, 1 ≤ k → k ≤ 4 → |U k y| ≤ K) :
    |kRem U F y u| ≤ 9 * M * (1 + K) ^ 2 * (1 + |u|) ^ 5 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hF 1 le_rfl (by norm_num))
  have hK : 0 ≤ K := (abs_nonneg _).trans (hU 1 le_rfl (by norm_num))
  have f1 := hF 1 le_rfl (by norm_num); have f2 := hF 2 (by norm_num) (by norm_num)
  have f3 := hF 3 (by norm_num) (by norm_num); have f4 := hF 4 (by norm_num) (by norm_num)
  have f5 := hF 5 (by norm_num) le_rfl
  have u1 := hU 1 le_rfl (by norm_num); have u2 := hU 2 (by norm_num) (by norm_num)
  have u3 := hU 3 (by norm_num) (by norm_num); have u4 := hU 4 (by norm_num) le_rfl
  set a := |u| with ha_def
  have ha : 0 ≤ a := abs_nonneg u
  have hprod : ∀ {p q P Q : ℝ}, |p| ≤ P → |q| ≤ Q → |p * q| ≤ P * Q := fun hp hq => by
    rw [abs_mul]; exact mul_le_mul hp hq (abs_nonneg _) ((abs_nonneg _).trans hp)
  -- the two coefficients
  have hc4 : |kc4 U F y| ≤ 2 * M * (1 + K) := by
    simp only [kc4]
    have := abs_add_le (F 4 y / 4 + (U 3 y * F 1 y + U 2 y * F 2 y) / 2) (-(U 1 y * F 3 y / 4))
    have h1 := abs_add_le (F 4 y / 4) ((U 3 y * F 1 y + U 2 y * F 2 y) / 2)
    have h2 := abs_add_le (U 3 y * F 1 y) (U 2 y * F 2 y)
    have p1 := hprod u3 f1; have p2 := hprod u2 f2; have p3 := hprod u1 f3
    rw [sub_eq_add_neg]
    simp only [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this h1 ⊢
    nlinarith
  have hc4y : |kc4y U F y| ≤ 3 * M * (1 + K) := by
    simp only [kc4y]
    have p1 := hprod u4 f1; have p2 := hprod u3 f2; have p3 := hprod u2 f3
    have p4 := hprod u1 f4
    have e := abs_add_le (F 5 y / 4 + (U 4 y * F 1 y + U 3 y * F 2 y +
      (U 3 y * F 2 y + U 2 y * F 3 y)) / 2) (-((U 2 y * F 3 y + U 1 y * F 4 y) / 4))
    have e1 := abs_add_le (F 5 y / 4) ((U 4 y * F 1 y + U 3 y * F 2 y +
      (U 3 y * F 2 y + U 2 y * F 3 y)) / 2)
    have e2 := abs_add_le (U 4 y * F 1 y + U 3 y * F 2 y) (U 3 y * F 2 y + U 2 y * F 3 y)
    have e3 := abs_add_le (U 4 y * F 1 y) (U 3 y * F 2 y)
    have e4 := abs_add_le (U 3 y * F 2 y) (U 2 y * F 3 y)
    have e5 := abs_add_le (U 2 y * F 3 y) (U 1 y * F 4 y)
    rw [sub_eq_add_neg]
    simp only [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at e e1 ⊢
    nlinarith
  have H2 := abs_He2_le u; have H3 := abs_He3_le u; have H4 := abs_He4_le u
  rw [← ha_def] at H2 H3 H4
  have hb : 1 ≤ 1 + a := by linarith
  have hb2 : (1 + a) ^ 2 ≤ (1 + a) ^ 4 := pow_le_pow_right₀ hb (by norm_num)
  have hb3 : (1 + a) ^ 3 ≤ (1 + a) ^ 4 := pow_le_pow_right₀ hb (by norm_num)
  have hb1 : (1 + a) ≤ (1 + a) ^ 3 := by
    simpa using pow_le_pow_right₀ hb (by norm_num : 1 ≤ 3)
  have hMK : 0 ≤ M * (1 + K) := by positivity
  have hMMK : M ≤ M * (1 + K) := by nlinarith
  have hb4 : 0 ≤ (1 + a) ^ 4 := by positivity
  have hb3' : 0 ≤ (1 + a) ^ 3 := by positivity
  -- first bracket
  have B1 : |He 4 u * F 5 y / 24 + He 2 u * kc4y U F y| ≤ 4 * M * (1 + K) * (1 + a) ^ 4 := by
    have q1 := hprod H4 f5; have q2 := hprod H2 hc4y
    have := abs_add_le (He 4 u * F 5 y / 24) (He 2 u * kc4y U F y)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 24)] at this
    have e1 := mul_le_mul_of_nonneg_right hb2 (by positivity : 0 ≤ 3 * M * (1 + K))
    have e2 := mul_le_mul_of_nonneg_right hMMK hb4
    nlinarith
  have B2 : |4 * He 3 u * F 4 y / 24 + 2 * u * kc4 U F y| ≤ 5 * M * (1 + K) * (1 + a) ^ 3 := by
    have q1 := hprod H3 f4
    have q2 : |2 * u * kc4 U F y| ≤ 2 * a * (2 * M * (1 + K)) := by
      rw [abs_mul, abs_mul, abs_two, ← ha_def]; gcongr
    have := abs_add_le (4 * He 3 u * F 4 y / 24) (2 * u * kc4 U F y)
    have q1' : |4 * He 3 u * F 4 y / 24| ≤ 3 * (1 + a) ^ 3 * M / 6 := by
      rw [abs_div, mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24),
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith
    have e1 := mul_le_mul_of_nonneg_right hMMK hb3'
    have ha3 : a ≤ (1 + a) ^ 3 := by linarith
    have e2 := mul_le_mul_of_nonneg_right ha3 hMK
    nlinarith
  simp only [kRem]
  have := abs_sub (u * (He 4 u * F 5 y / 24 + He 2 u * kc4y U F y))
    (U 1 y * (4 * He 3 u * F 4 y / 24 + 2 * u * kc4 U F y))
  have r1 := hprod (le_refl |u|) B1
  have r2 := hprod u1 B2
  rw [← ha_def] at r1
  have hb5 : a * (1 + a) ^ 4 ≤ (1 + a) ^ 5 := by
    calc a * (1 + a) ^ 4 ≤ (1 + a) * (1 + a) ^ 4 := by gcongr; linarith
      _ = (1 + a) ^ 5 := by ring
  have hb6 : (1 + a) ^ 3 ≤ (1 + a) ^ 5 := pow_le_pow_right₀ hb (by norm_num)
  calc _ ≤ _ := this
    _ ≤ a * (4 * M * (1 + K) * (1 + a) ^ 4) + K * (5 * M * (1 + K) * (1 + a) ^ 3) := by
        linarith
    _ ≤ 4 * M * (1 + K) ^ 2 * (1 + a) ^ 5 + 5 * M * (1 + K) ^ 2 * (1 + a) ^ 5 := by
        have hK1 : 1 + K ≤ (1 + K) ^ 2 := by nlinarith
        have hK2 : K * (1 + K) ≤ (1 + K) ^ 2 := by nlinarith
        have i1 : a * (4 * M * (1 + K) * (1 + a) ^ 4) ≤ 4 * M * (1 + K) ^ 2 * (1 + a) ^ 5 := by
          calc a * (4 * M * (1 + K) * (1 + a) ^ 4) = 4 * M * (1 + K) * (a * (1 + a) ^ 4) := by
                ring
            _ ≤ 4 * M * (1 + K) * (1 + a) ^ 5 := by gcongr
            _ = 4 * M * (1 + a) ^ 5 * (1 + K) := by ring
            _ ≤ 4 * M * (1 + a) ^ 5 * (1 + K) ^ 2 := by gcongr
            _ = 4 * M * (1 + K) ^ 2 * (1 + a) ^ 5 := by ring
        have i2 : K * (5 * M * (1 + K) * (1 + a) ^ 3) ≤ 5 * M * (1 + K) ^ 2 * (1 + a) ^ 5 := by
          calc K * (5 * M * (1 + K) * (1 + a) ^ 3) = 5 * M * (K * (1 + K)) * (1 + a) ^ 3 := by
                ring
            _ ≤ 5 * M * (1 + K) ^ 2 * (1 + a) ^ 5 := by gcongr
        linarith
    _ = 9 * M * (1 + K) ^ 2 * (1 + a) ^ 5 := by ring

/-- **(6.4.66) as a generator bound, rate `γ⁻³`.**  For `γ ≥ 1`, the backward Kramers generator on
the perturbed test function differs from `γ⁻¹` times the Smoluchowski operator by at most
`γ⁻³ (|(C+DA)*f| + 9M(1+K)²(1+|u|)⁵)`. -/
theorem kramers_smoluchowski_bound (U F : ℕ → ℝ → ℝ) {γ : ℝ} (hγ : 1 ≤ γ) (y u M K : ℝ)
    (hF : ∀ k, 1 ≤ k → k ≤ 5 → |F k y| ≤ M) (hU : ∀ k, 1 ≤ k → k ≤ 4 → |U k y| ≤ K) :
    |kGen γ (U 1 y) u (kφy U F γ⁻¹ y u) (kφu U F γ⁻¹ y u) (kφuu U F γ⁻¹ y u)
        - γ⁻¹ * smolGen U F y|
      ≤ γ⁻¹ ^ 3 * (|smolCorr U F y| + 9 * M * (1 + K) ^ 2 * (1 + |u|) ^ 5) := by
  have hγ0 : γ ≠ 0 := by positivity
  have e := kramers_generator_expansion U F (inv_ne_zero hγ0) y u
  rw [inv_inv] at e
  rw [e]
  have hR := kRem_le U F y u M K hF hU
  have hε : 0 < γ⁻¹ := by positivity
  have hε1 : γ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hγ
  have : |γ⁻¹ ^ 3 * smolCorr U F y + γ⁻¹ ^ 4 * kRem U F y u|
      ≤ γ⁻¹ ^ 3 * |smolCorr U F y| + γ⁻¹ ^ 4 * |kRem U F y u| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < γ⁻¹ ^ 3),
      abs_of_pos (by positivity : 0 < γ⁻¹ ^ 4)]
  have h4 : γ⁻¹ ^ 4 ≤ γ⁻¹ ^ 3 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  calc _ = |γ⁻¹ ^ 3 * smolCorr U F y + γ⁻¹ ^ 4 * kRem U F y u| := by ring_nf
    _ ≤ _ := this
    _ ≤ γ⁻¹ ^ 3 * |smolCorr U F y| + γ⁻¹ ^ 3 * (9 * M * (1 + K) ^ 2 * (1 + |u|) ^ 5) := by
        gcongr
    _ = _ := by ring

/-- **(6.4.108) as a generator bound, rate `γ⁻⁴`.**  Including the correction (6.4.107), the
backward Kramers generator on the perturbed test function is within
`9M(1+K)²(1+|u|)⁵ γ⁻⁴` of the corrected Smoluchowski operator `γ⁻¹A* + γ⁻³(C + DA)*`. -/
theorem kramers_corrected_bound (U F : ℕ → ℝ → ℝ) {γ : ℝ} (hγ : 0 < γ) (y u M K : ℝ)
    (hF : ∀ k, 1 ≤ k → k ≤ 5 → |F k y| ≤ M) (hU : ∀ k, 1 ≤ k → k ≤ 4 → |U k y| ≤ K) :
    |kGen γ (U 1 y) u (kφy U F γ⁻¹ y u) (kφu U F γ⁻¹ y u) (kφuu U F γ⁻¹ y u)
        - (γ⁻¹ * smolGen U F y + γ⁻¹ ^ 3 * smolCorr U F y)|
      ≤ γ⁻¹ ^ 4 * (9 * M * (1 + K) ^ 2 * (1 + |u|) ^ 5) := by
  have e := kramers_generator_expansion U F (inv_ne_zero hγ.ne') y u
  rw [inv_inv] at e
  rw [e, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity)]
  gcongr
  exact kRem_le U F y u M K hF hU

/-! ### A concrete instance: the double well -/

/-- Derivative tower of the double-well potential `U(y) = y⁴/4 - y²/2`. -/
def dwU : ℕ → ℝ → ℝ
  | 0 => fun y => y ^ 4 / 4 - y ^ 2 / 2
  | 1 => fun y => y ^ 3 - y
  | 2 => fun y => 3 * y ^ 2 - 1
  | 3 => fun y => 6 * y
  | 4 => fun _ => 6
  | _ => fun _ => 0

lemma dwU_tower (k : ℕ) (y : ℝ) : HasDerivAt (dwU k) (dwU (k + 1) y) y := by
  match k with
  | 0 => convert ((hasDerivAt_pow 4 y).div_const 4).sub ((hasDerivAt_pow 2 y).div_const 2)
          using 1; simp [dwU]
  | 1 => convert (hasDerivAt_pow 3 y).sub (hasDerivAt_id y) using 1
  | 2 => convert ((hasDerivAt_pow 2 y).const_mul 3).sub_const 1 using 1; simp [dwU]; ring
  | 3 => convert (hasDerivAt_id y).const_mul 6 using 1; simp [dwU]
  | 4 => simpa [dwU] using hasDerivAt_const y (6 : ℝ)
  | k + 5 => simpa [dwU] using hasDerivAt_const y (0 : ℝ)

/-- Derivative tower of `f = sin`. -/
def sinTower (k : ℕ) : ℝ → ℝ :=
  match k % 4 with
  | 0 => Real.sin
  | 1 => Real.cos
  | 2 => fun y => -Real.sin y
  | _ => fun y => -Real.cos y

lemma sinTower_tower (k : ℕ) (y : ℝ) : HasDerivAt (sinTower k) (sinTower (k + 1) y) y := by
  have h : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hk : (k + 1) % 4 = (k % 4 + 1) % 4 := by omega
  unfold sinTower
  rw [hk]
  interval_cases (k % 4)
  · simpa using Real.hasDerivAt_sin y
  · simpa using Real.hasDerivAt_cos y
  · simpa using (Real.hasDerivAt_sin y).neg
  · simpa using (Real.hasDerivAt_cos y).neg

lemma abs_sinTower_le (k : ℕ) (y : ℝ) : |sinTower k y| ≤ 1 := by
  unfold sinTower
  have h : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 4) <;> simp [Real.abs_sin_le_one, Real.abs_cos_le_one]

/-- **Instance: the double well `U = y⁴/4 - y²/2`, `f = sin`, on `|y| ≤ 1`.**  Here
`|U⁽ᵏ⁾| ≤ 6` for `k ≤ 4` and `|f⁽ᵏ⁾| ≤ 1`, so the Kramers generator on the perturbed test
function is within `441 (1 + |u|)⁵ γ⁻⁴` of the corrected Smoluchowski operator; the correction
`(C + DA)*f = U''(f'' - U'f') + U'''f'` is not identically zero (`U''' = 6y`). -/
theorem kramers_doubleWell {γ : ℝ} (hγ : 0 < γ) {y : ℝ} (hy : |y| ≤ 1) (u : ℝ) :
    |kGen γ (dwU 1 y) u (kφy dwU sinTower γ⁻¹ y u) (kφu dwU sinTower γ⁻¹ y u)
        (kφuu dwU sinTower γ⁻¹ y u)
        - (γ⁻¹ * smolGen dwU sinTower y + γ⁻¹ ^ 3 * smolCorr dwU sinTower y)|
      ≤ γ⁻¹ ^ 4 * (441 * (1 + |u|) ^ 5) := by
  have h := kramers_corrected_bound dwU sinTower hγ y u 1 6
    (fun k _ _ => abs_sinTower_le k y) ?_
  · convert h using 2; norm_num
  · intro k hk hk4
    have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_nonneg y, sq_abs y]
    have hy0 : 0 ≤ y ^ 2 := sq_nonneg y
    interval_cases k <;> simp only [dwU]
    · rw [abs_le]; constructor <;> nlinarith [abs_le.1 hy]
    · rw [abs_le]; constructor <;> nlinarith
    · rw [abs_mul]; norm_num; linarith
    · norm_num

/-- The correction is genuinely present in the instance: at `y = 1`,
`(C + DA)*sin = 6 cos 1 - 2 sin 1 > 0`. -/
theorem kramers_doubleWell_corr : 0 < smolCorr dwU sinTower 1 := by
  have hc : 1 / 2 ≤ Real.cos 1 := by
    have := Real.one_sub_sq_div_two_le_cos (x := 1); norm_num at this; linarith
  have hs : Real.sin 1 ≤ 1 := Real.sin_le_one 1
  simp [smolCorr, dwU, sinTower]
  nlinarith

/-- In the instance, `kφy`, `kφu`, `kφuu` are the genuine partial derivatives of the perturbed
test function `φ_γ(y, u)`. -/
theorem kramers_doubleWell_partials (ε y u : ℝ) :
    HasDerivAt (fun y => kφ dwU sinTower ε y u) (kφy dwU sinTower ε y u) y ∧
      HasDerivAt (fun u => kφ dwU sinTower ε y u) (kφu dwU sinTower ε y u) u ∧
      HasDerivAt (fun u => kφu dwU sinTower ε y u) (kφuu dwU sinTower ε y u) u :=
  ⟨hasDerivAt_kφ_y dwU_tower sinTower_tower ε y u, hasDerivAt_kφ_u _ _ ε y u,
    hasDerivAt_kφ_uu _ _ ε y u⟩

end Gardiner.Adiabatic
