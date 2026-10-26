/-
# Adiabatic elimination in the general case (Gardiner §6.6.2–§6.6.4)

Gardiner, *Handbook of Stochastic Methods*, §6.6.2 (Haken's model, (6.6.36)–(6.6.64)),
§6.6.3 (the nonlinear case and its second-order corrections, (6.6.65)–(6.6.106)) and §6.6.4
(arbitrary nonlinear coupling, (6.6.107)–(6.6.123)).  As in `Gardiner.Adiabatic.WhiteNoise`,
all statements are about the backward generator applied to an explicit perturbed test function,
with exact remainders.

## §6.6.2 Haken's model

* (6.6.38)–(6.6.39): `Gardiner.Adiabatic.haken_deterministic`.
* (6.6.43)–(6.6.46): the Itô drift of `β = α - (b/κ)x²` (`Gardiner.Adiabatic.haken_beta_drift`).
  The first term of (6.6.46) should read `∂ₓ aβx`, not `∂_β aβx` (erratum).
* (6.6.51)–(6.6.64): with `a = ε^r ã` the coupling to the fast Ornstein–Uhlenbeck variable `β` has
  strength `s = ε^{r-1/2}` on the time scale `τ = εt`.  `Gardiner.Adiabatic.haken_slave` shows, for
  every `s`, that the generator on the perturbed test function is
  `-(x(1 - s²ã²D²/(2κ²)) + Ax³) f' + (B + s²ã²D²x²/(2κ²)) f'' + O(ε^{1/2})`, i.e. (6.6.64) in backward
  form: `s → 0` (`r > ½`) is the silent slave (6.6.55), `s = 1` (`r = ½`) the noisy slave
  (6.6.62), and `s → ∞` (`r < ½`) the dominant noise of (6.6.63).  (6.6.64) has `∂/∂k` for
  `∂/∂x` (erratum).  The passage (6.6.61) → (6.6.62) is the identity
  `∂ₓ x ∂ₓ x = ∂ₓ² x² - ∂ₓ x` (`Gardiner.Adiabatic.haken_rewrite`).

## §6.6.3 The nonlinear case

* `Gardiner.Adiabatic.nl_generator`: for `dx = (a + bα)dt + c dW₁`,
  `dα = γ²(A(α) - f(x))dt + γ√(2B) dW₂`, let `u(x) = ⟨α⟩_x` (6.6.74) and let `χ` solve
  `𝓛ₓχ = -(α - u)`.  On `φ = F + γ⁻² χ b F'` the generator is
  `(a + bu)F' + ½c²F'' + γ⁻²[(a + bα)∂ₓφ₂ + ½c²∂ₓ²φ₂]`: the lowest-order equation (6.6.86) with an
  explicit `O(γ⁻²)` error (`Gardiner.Adiabatic.nl_generator_bound`).
* `Gardiner.Adiabatic.nl_second_order_order3`: the `γ⁻²` term involves at most third derivatives
  of the test function — the generator form of the statement after (6.6.87) that the
  fourth-order terms cancel (the algebraic identities (6.6.89)–(6.6.105) are in
  `Gardiner.Adiabatic.secondOrder_reduced`).  In (6.6.94) `[a(x)]²` should be `[c(x)]²` (erratum).
* Instance (`Gardiner.Adiabatic.nl_haken_instance`): Haken's model `a = -x`, `b = -x`,
  `A(α) = -κα`, `f(x) = -x²`, for which `u = x²/κ` and the reduced drift is `-x - x³/κ`, the cubic
  of (6.6.39); the partial derivatives of the perturbed test function are genuine.

## §6.6.4 Arbitrary nonlinear coupling

* `Gardiner.Adiabatic.nlc_generator`: with `𝓛 = 𝓛₀ + γ⁻¹𝓛₁` (the expansion (6.6.108)) the generator
  `γ²𝓛 + γψ∂ₓ` on `φ = f + γ⁻¹χf' + γ⁻²(ρ₁f'' + ρ₂f')` equals `E f' + D f'' + O(γ⁻¹)`, where
  `D = ⟨ψχ⟩₀` and `E = ⟨ψ∂ₓχ + 𝓛₁χ⟩₀`; the `𝓛₁χ` part is `b α₀` (the drift `L₃` of (6.6.116)).
  The diffusion is `+D`: the overall sign in (6.6.120)/(6.6.122) as printed would give a negative
  diffusion coefficient (erratum).  Instance: `Gardiner.Adiabatic.nlc_ou_instance`.
-/
import SHSLib.Gardiner.Adiabatic.WhiteNoise

noncomputable section

namespace Gardiner.Adiabatic

/-! ### §6.6.2 Haken's model -/

/-- **(6.6.38)–(6.6.39)**: the stationary point of `α̇ = -κα + bx²` is `α = bx²/κ`, and
substituting it into `ẋ = -εx - axα` gives `ẋ = -εx - (ab/κ)x³`. -/
theorem haken_deterministic (ε a b κ x : ℝ) (hκ : κ ≠ 0) :
    -κ * (b / κ * x ^ 2) + b * x ^ 2 = 0 ∧
      -ε * x - a * x * (b / κ * x ^ 2) = -ε * x - a * b / κ * x ^ 3 := by
  constructor
  · field_simp; ring
  · field_simp

/-- **(6.6.43)–(6.6.46)**: by Itô's formula, `β = α - (b/κ)x²` has drift
`μ_α - (2bx/κ)μ_x - (b/κ)C²`, which in terms of `β` is
`-κβ + (2bx/κ)(εx + (ab/κ)x³ + axβ) - bC²/κ`; the `-bC²/κ` part is the one absorbed by the
symmetric ordering `-C²((bx/κ)∂ₓ∂_β + ∂ₓ∂_β (bx/κ))` of (6.6.46). -/
theorem haken_beta_drift (ε a b κ C x α : ℝ) (hκ : κ ≠ 0) :
    let β := α - b / κ * x ^ 2
    (-κ * α + b * x ^ 2) - (2 * b * x / κ) * (-(ε * x + a * x * α)) - (b / κ) * C ^ 2
      = -κ * β + (2 * b * x / κ) * (ε * x + a * b / κ * x ^ 3 + a * x * β) - b * C ^ 2 / κ := by
  intro β
  simp only [β]
  field_simp
  ring

/-- **(6.6.61) → (6.6.62)**: `∂ₓ x ∂ₓ (x p) = ∂ₓ²(x²p) - ∂ₓ(xp)`, at the level of fluxes:
`x ∂ₓ(xp) = ∂ₓ(x²p) - xp`, where `∂ₓ(xp) = p + xp'` and `∂ₓ(x²p) = 2xp + x²p'` (the case
`b(x) = x` of `strat_ito_flux`). -/
theorem haken_rewrite (x p p' : ℝ) :
    x * (1 * p + x * p') = (2 * x * 1 * p + x ^ 2 * p') - x * p := by ring

/-- **(6.6.51)–(6.6.64), all regimes.**  On the slow time scale, with fast Ornstein–Uhlenbeck
variable `β` (`𝓛 = -κβ∂_β + ½D²∂_β²`), coupling `ψ = s·(-ãβx)` of strength `s = ε^{r-1/2}`,
slow drift `-(x + Ax³)` and slow diffusion `B`, the generator
`δ⁻²𝓛 + δ⁻¹ψ∂ₓ - (x + Ax³)∂ₓ + B∂ₓ²` (`δ = ε^{1/2}`) applied to
`φ = f + δχf' + δ²(ρ₁f'' + ρ₂f')` with `χ = -sãβx/κ`, `ρ₁ = s²ã²x²β²/(2κ²)`,
`ρ₂ = s²ã²xβ²/(2κ²)` is within `δ|R₁ + BT₁| + δ²|R₂ + BT₂|` of
`-(x(1 - s²ã²D²/(2κ²)) + Ax³) f' + (B + s²ã²D²x²/(2κ²)) f''` (backward form of (6.6.62)–(6.6.64)),
where `∂ₓ²φ = f'' + δT₁ + δ²T₂`. -/
theorem haken_slave {δ : ℝ} (hδ : 0 < δ) (ã κ Dn s A B x β f1 f2 f3 T1 T2 : ℝ) (hκ : κ ≠ 0) :
    let ψ := s * (-ã * β * x)
    let χ := -(s * ã * β * x) / κ
    let χx := -(s * ã * β) / κ
    let ρ1 := s ^ 2 * ã ^ 2 * x ^ 2 * β ^ 2 / (2 * κ ^ 2)
    let ρ1x := s ^ 2 * ã ^ 2 * x * β ^ 2 / κ ^ 2
    let ρ2 := s ^ 2 * ã ^ 2 * x * β ^ 2 / (2 * κ ^ 2)
    let ρ2x := s ^ 2 * ã ^ 2 * β ^ 2 / (2 * κ ^ 2)
    let Lφ := δ * f1 * (-κ * β * (-(s * ã * x) / κ))
      + δ ^ 2 * (f2 * (-κ * β * (s ^ 2 * ã ^ 2 * x ^ 2 * β / κ ^ 2)
          + Dn ^ 2 / 2 * (s ^ 2 * ã ^ 2 * x ^ 2 / κ ^ 2))
        + f1 * (-κ * β * (s ^ 2 * ã ^ 2 * x * β / κ ^ 2) + Dn ^ 2 / 2 * (s ^ 2 * ã ^ 2 * x / κ ^ 2)))
    |B * (f2 + δ * T1 + δ ^ 2 * T2) + wnGen δ (-(x + A * x ^ 3)) ψ Lφ
        (wnPhix δ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3)
        - (-(x * (1 - s ^ 2 * ã ^ 2 * Dn ^ 2 / (2 * κ ^ 2)) + A * x ^ 3) * f1
          + (B + s ^ 2 * ã ^ 2 * Dn ^ 2 * x ^ 2 / (2 * κ ^ 2)) * f2)|
      ≤ δ * |wnR1 (-(x + A * x ^ 3)) ψ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3 + B * T1|
        + δ ^ 2 * |wnR2 (-(x + A * x ^ 3)) ρ1 ρ1x ρ2 ρ2x f1 f2 f3 + B * T2| := by
  intro ψ χ χx ρ1 ρ1x ρ2 ρ2x Lφ
  have e := wn_generator_time hδ.ne' (-(x + A * x ^ 3)) ψ χ χx ρ1 ρ1x ρ2 ρ2x
    (s ^ 2 * ã ^ 2 * Dn ^ 2 * x ^ 2 / (2 * κ ^ 2)) (s ^ 2 * ã ^ 2 * Dn ^ 2 * x / (2 * κ ^ 2))
    (-κ * β * (-(s * ã * x) / κ))
    (-κ * β * (s ^ 2 * ã ^ 2 * x ^ 2 * β / κ ^ 2) + Dn ^ 2 / 2 * (s ^ 2 * ã ^ 2 * x ^ 2 / κ ^ 2))
    (-κ * β * (s ^ 2 * ã ^ 2 * x * β / κ ^ 2) + Dn ^ 2 / 2 * (s ^ 2 * ã ^ 2 * x / κ ^ 2))
    Lφ f1 f2 f3 (B * f2) (B * (f2 + δ * T1 + δ ^ 2 * T2)) (B * T1) (B * T2)
    (by simp only [ψ]; field_simp) (by simp only [ψ, χ]; field_simp; ring)
    (by simp only [ψ, χx]; field_simp; ring) rfl (by ring)
  rw [e]
  have h : B * f2 + (-(x + A * x ^ 3) + s ^ 2 * ã ^ 2 * Dn ^ 2 * x / (2 * κ ^ 2)) * f1
      + s ^ 2 * ã ^ 2 * Dn ^ 2 * x ^ 2 / (2 * κ ^ 2) * f2
      = -(x * (1 - s ^ 2 * ã ^ 2 * Dn ^ 2 / (2 * κ ^ 2)) + A * x ^ 3) * f1
          + (B + s ^ 2 * ã ^ 2 * Dn ^ 2 * x ^ 2 / (2 * κ ^ 2)) * f2 := by ring
  rw [h, add_assoc, add_sub_cancel_left]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos hδ, abs_of_pos (by positivity : 0 < δ ^ 2)]

/-- **Instance: the noisy slave (6.6.62)**, `s = 1`, with `ã = κ = D = 1`, `A = B = 1`:
effective drift `-(x/2 + x³)` and diffusion `1 + x²/2`. -/
theorem haken_noisy_instance {δ : ℝ} (hδ : 0 < δ) (x β f1 f2 f3 T1 T2 : ℝ) :
    -(x * (1 - 1 ^ 2 * 1 ^ 2 * 1 ^ 2 / (2 * 1 ^ 2)) + 1 * x ^ 3) * f1
        + (1 + 1 ^ 2 * 1 ^ 2 * 1 ^ 2 * x ^ 2 / (2 * 1 ^ 2)) * f2
      = -(x / 2 + x ^ 3) * f1 + (1 + x ^ 2 / 2) * f2 ∧
    |1 * (f2 + δ * T1 + δ ^ 2 * T2) + wnGen δ (-(x + 1 * x ^ 3)) (1 * (-1 * β * x))
        (δ * f1 * (-1 * β * (-(1 * 1 * x) / 1))
          + δ ^ 2 * (f2 * (-1 * β * (1 ^ 2 * 1 ^ 2 * x ^ 2 * β / 1 ^ 2)
              + 1 ^ 2 / 2 * (1 ^ 2 * 1 ^ 2 * x ^ 2 / 1 ^ 2))
            + f1 * (-1 * β * (1 ^ 2 * 1 ^ 2 * x * β / 1 ^ 2)
              + 1 ^ 2 / 2 * (1 ^ 2 * 1 ^ 2 * x / 1 ^ 2))))
        (wnPhix δ (-(1 * 1 * β * x) / 1) (-(1 * 1 * β) / 1)
          (1 ^ 2 * 1 ^ 2 * x ^ 2 * β ^ 2 / (2 * 1 ^ 2)) (1 ^ 2 * 1 ^ 2 * x * β ^ 2 / 1 ^ 2)
          (1 ^ 2 * 1 ^ 2 * x * β ^ 2 / (2 * 1 ^ 2)) (1 ^ 2 * 1 ^ 2 * β ^ 2 / (2 * 1 ^ 2)) f1 f2 f3)
        - (-(x * (1 - 1 ^ 2 * 1 ^ 2 * 1 ^ 2 / (2 * 1 ^ 2)) + 1 * x ^ 3) * f1
          + (1 + 1 ^ 2 * 1 ^ 2 * 1 ^ 2 * x ^ 2 / (2 * 1 ^ 2)) * f2)|
      ≤ δ * |wnR1 (-(x + 1 * x ^ 3)) (1 * (-1 * β * x)) (-(1 * 1 * β * x) / 1) (-(1 * 1 * β) / 1)
            (1 ^ 2 * 1 ^ 2 * x ^ 2 * β ^ 2 / (2 * 1 ^ 2)) (1 ^ 2 * 1 ^ 2 * x * β ^ 2 / 1 ^ 2)
            (1 ^ 2 * 1 ^ 2 * x * β ^ 2 / (2 * 1 ^ 2)) (1 ^ 2 * 1 ^ 2 * β ^ 2 / (2 * 1 ^ 2))
            f1 f2 f3 + 1 * T1|
        + δ ^ 2 * |wnR2 (-(x + 1 * x ^ 3)) (1 ^ 2 * 1 ^ 2 * x ^ 2 * β ^ 2 / (2 * 1 ^ 2))
            (1 ^ 2 * 1 ^ 2 * x * β ^ 2 / 1 ^ 2) (1 ^ 2 * 1 ^ 2 * x * β ^ 2 / (2 * 1 ^ 2))
            (1 ^ 2 * 1 ^ 2 * β ^ 2 / (2 * 1 ^ 2)) f1 f2 f3 + 1 * T2| :=
  ⟨by ring, haken_slave hδ 1 1 1 1 1 1 x β f1 f2 f3 T1 T2 one_ne_zero⟩

/-! ### §6.6.3 The nonlinear case -/

/-- The backward generator `γ²𝓛ₓ + (a + bα)∂ₓ + ½c²∂ₓ²` of (6.6.70) (`γ = ε⁻¹`), acting on a
function with fast-generator image `Lφ` and `x`-derivatives `φx, φxx`. -/
def nlGen (ε a b c α Lφ φx φxx : ℝ) : ℝ := ε⁻¹ ^ 2 * Lφ + (a + b * α) * φx + (1 / 2) * c ^ 2 * φxx

/-- **(6.6.70)–(6.6.87) as a generator identity.**  Let `u = ⟨α⟩ₓ` (6.6.74), let `χ` solve
`𝓛ₓχ = -(α - u)` (value `Lχ`), and let `φ = F + ε²φ₂` with `φ₂ = χ b F'`, so that
`𝓛ₓφ = ε² b F' 𝓛ₓχ` (`hL`).  Then the generator on `φ` is `(a + bu)F' + ½c²F''` plus
`ε²[(a + bα)∂ₓφ₂ + ½c²∂ₓ²φ₂]`. -/
theorem nl_generator {ε : ℝ} (hε : ε ≠ 0) (a b c α u Lχ Lφ F1 F2 φ2x φ2xx : ℝ)
    (hχ : Lχ = -(α - u)) (hL : Lφ = ε ^ 2 * (b * F1) * Lχ) :
    nlGen ε a b c α Lφ (F1 + ε ^ 2 * φ2x) (F2 + ε ^ 2 * φ2xx)
      = (a + b * u) * F1 + (1 / 2) * c ^ 2 * F2
        + ε ^ 2 * ((a + b * α) * φ2x + (1 / 2) * c ^ 2 * φ2xx) := by
  subst hL hχ
  simp only [nlGen]
  field_simp
  ring

/-- **(6.6.86) with an explicit `O(γ⁻²)` error.** -/
theorem nl_generator_bound {γ : ℝ} (hγ : 0 < γ) (a b c α u Lχ Lφ F1 F2 φ2x φ2xx : ℝ)
    (hχ : Lχ = -(α - u)) (hL : Lφ = γ⁻¹ ^ 2 * (b * F1) * Lχ) :
    |nlGen γ⁻¹ a b c α Lφ (F1 + γ⁻¹ ^ 2 * φ2x) (F2 + γ⁻¹ ^ 2 * φ2xx)
        - ((a + b * u) * F1 + (1 / 2) * c ^ 2 * F2)|
      ≤ γ⁻¹ ^ 2 * |(a + b * α) * φ2x + (1 / 2) * c ^ 2 * φ2xx| := by
  rw [nl_generator (inv_ne_zero hγ.ne') a b c α u Lχ Lφ F1 F2 φ2x φ2xx hχ hL,
    add_sub_cancel_left, abs_mul, abs_of_pos (by positivity)]

/-- **Second-order corrections involve at most third derivatives.**  For `φ₂ = χ b F'`,
`∂ₓφ₂ = (χₓb + χb')F' + χbF''` and `∂ₓ²φ₂ = (χₓₓb + 2χₓb' + χb'')F' + 2(χₓb + χb')F'' + χbF'''`,
so the `γ⁻²` term `(a + bα)∂ₓφ₂ + ½c²∂ₓ²φ₂` is a combination of `F', F'', F'''` only: no fourth
derivative survives (cf. (6.6.88)–(6.6.106)). -/
theorem nl_second_order_order3 (a b b' b'' c α χ χx χxx F1 F2 F3 : ℝ) :
    (a + b * α) * ((χx * b + χ * b') * F1 + χ * b * F2)
        + (1 / 2) * c ^ 2 * ((χxx * b + 2 * χx * b' + χ * b'') * F1
          + 2 * (χx * b + χ * b') * F2 + χ * b * F3)
      = ((a + b * α) * (χx * b + χ * b') + (1 / 2) * c ^ 2 * (χxx * b + 2 * χx * b' + χ * b''))
          * F1
        + ((a + b * α) * χ * b + c ^ 2 * (χx * b + χ * b')) * F2
        + ((1 / 2) * c ^ 2 * χ * b) * F3 := by ring

/-- The perturbed test function for Haken's model in the form of §6.6.3:
`φ = F + ε²χbF'` with `χ = (α - x²/κ)/κ`, `b = -x`. -/
def hakenPhi (κ : ℝ) (F : ℕ → ℝ → ℝ) (ε x α : ℝ) : ℝ :=
  F 0 x + ε ^ 2 * ((α - x ^ 2 / κ) / κ * (-x) * F 1 x)

/-- **Instance of `nl_generator_bound`: Haken's model.**  `dx = (-x - xα)dt + C dW₁`,
`dα = γ²(-κα + x²)dt + γ√(2B₀) dW₂` (`a = -x`, `b = -x`, `A(α) = -κα`, `f(x) = -x²`).  Then
`u = x²/κ`, `χ = (α - u)/κ` solves `𝓛ₓχ = -(α - u)` for `𝓛ₓ = (-κα + x²)∂_α + B₀∂_α²`, and the
generator on `hakenPhi`, with its genuine `x`-derivatives, is within `γ⁻²|R|` of
`(-x - x³/κ)F' + ½C²F''`: the cubic drift of (6.6.39), now with noise. -/
theorem nl_haken_instance (F : ℕ → ℝ → ℝ) (hF : ∀ k y, HasDerivAt (F k) (F (k + 1) y) y)
    {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 < γ) (B₀ C x α : ℝ) :
    ∃ φx φxx φα φαα : ℝ,
      HasDerivAt (fun x => hakenPhi κ F γ⁻¹ x α) φx x ∧
      HasDerivAt (fun x => F 1 x + γ⁻¹ ^ 2 * (-((α - x ^ 2 / κ) / κ * (F 1 x + x * F 2 x))
        + (2 * x / κ) / κ * x * F 1 x)) φxx x ∧
      HasDerivAt (fun α => hakenPhi κ F γ⁻¹ x α) φα α ∧
      φαα = 0 ∧
      φx = F 1 x + γ⁻¹ ^ 2 * (-((α - x ^ 2 / κ) / κ * (F 1 x + x * F 2 x))
        + (2 * x / κ) / κ * x * F 1 x) ∧
      |nlGen γ⁻¹ (-x) (-x) C α ((-κ * α + x ^ 2) * φα + B₀ * φαα) φx φxx
          - ((-x + -x * (x ^ 2 / κ)) * F 1 x + (1 / 2) * C ^ 2 * F 2 x)|
        ≤ γ⁻¹ ^ 2 * |(-x + -x * α) * (-((α - x ^ 2 / κ) / κ * (F 1 x + x * F 2 x))
            + (2 * x / κ) / κ * x * F 1 x)
          + (1 / 2) * C ^ 2 * (-((α - x ^ 2 / κ) / κ * (2 * F 2 x + x * F 3 x))
            + (2 * x / κ) / κ * (2 * F 1 x + 2 * x * F 2 x) + (2 / κ) / κ * x * F 1 x)| := by
  set ε := γ⁻¹
  have hκ0 : κ ≠ 0 := hκ.ne'
  have h0 := hF 0 x; have h1 := hF 1 x; have h2 := hF 2 x
  have hx := hasDerivAt_id x
  refine ⟨F 1 x + ε ^ 2 * (-((α - x ^ 2 / κ) / κ * (F 1 x + x * F 2 x))
      + (2 * x / κ) / κ * x * F 1 x),
    F 2 x + ε ^ 2 * (-((α - x ^ 2 / κ) / κ * (2 * F 2 x + x * F 3 x))
      + (2 * x / κ) / κ * (2 * F 1 x + 2 * x * F 2 x) + (2 / κ) / κ * x * F 1 x),
    ε ^ 2 * (1 / κ * (-x) * F 1 x), 0, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · have := h0.add (((((((hasDerivAt_const x α).sub ((hx.pow 2).div_const κ)).div_const κ).mul
      hx.neg).mul h1)).const_mul (ε ^ 2))
    convert this using 1
    simp only [id, Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, Pi.pow_apply]
    push_cast; field_simp; ring
  · have := h1.add (((((((hasDerivAt_const x α).sub ((hx.pow 2).div_const κ)).div_const κ).mul
      (h1.add (hx.mul h2))).neg).add (((((hx.const_mul 2).div_const κ).div_const κ).mul hx).mul
        h1)).const_mul (ε ^ 2))
    convert this using 1
    simp only [id, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    push_cast; field_simp; ring
  · have hα := hasDerivAt_id α
    have := (hasDerivAt_const α (F 0 x)).add
      (((((hα.sub_const (x ^ 2 / κ)).div_const κ).mul_const (-x)).mul_const (F 1 x)).const_mul
        (ε ^ 2))
    convert this using 1
    ring
  · exact nl_generator_bound hγ (-x) (-x) C α (x ^ 2 / κ) (-(α - x ^ 2 / κ)) _ (F 1 x)
      (F 2 x) _ _ rfl (by simp only [ε]; field_simp; ring)

/-! ### §6.6.4 Arbitrary nonlinear coupling -/

/-- **(6.6.107)–(6.6.123) as a generator identity.**  Fast generator `𝓛₀ + ε𝓛₁` (`ε = γ⁻¹`), slow
generator `γψ∂ₓ` with `ψ = b(x)α`.  Assume the Poisson equations `𝓛₀χ = -ψ`, `𝓛₀ρ₁ = D - ψχ`,
`𝓛₀ρ₂ = E - ψχₓ - 𝓛₁χ` and linearity on the test function (`hL0`, `hL1`).  Then
`(γ²(𝓛₀ + γ⁻¹𝓛₁) + γψ∂ₓ)φ = E f' + D f'' + γ⁻¹(R₁ + f''𝓛₁ρ₁ + f'𝓛₁ρ₂)`; `E` contains the drift
`⟨𝓛₁χ⟩₀ = bα₀` of (6.6.116), and the diffusion coefficient is `+D`. -/
theorem nlc_generator {ε : ℝ} (hε : ε ≠ 0)
    (ψ χ χx ρ1 ρ1x ρ2 ρ2x D E Lχ Lρ1 Lρ2 M1 N1 N2 L0φ L1φ f1 f2 f3 : ℝ)
    (hχ : Lχ = -ψ) (hρ1 : Lρ1 = D - ψ * χ) (hρ2 : Lρ2 = E - ψ * χx - M1)
    (hL0 : L0φ = ε * f1 * Lχ + ε ^ 2 * (f2 * Lρ1 + f1 * Lρ2))
    (hL1 : L1φ = ε * f1 * M1 + ε ^ 2 * (f2 * N1 + f1 * N2)) :
    ε⁻¹ ^ 2 * (L0φ + ε * L1φ) + ε⁻¹ * ψ * wnPhix ε χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3
      = E * f1 + D * f2 + ε * (wnR1 0 ψ χ χx ρ1 ρ1x ρ2 ρ2x f1 f2 f3 + f2 * N1 + f1 * N2) := by
  subst hL0 hL1 hχ hρ1 hρ2
  simp only [wnPhix, wnR1]
  field_simp
  ring

/-- **Instance of `nlc_generator`**: `dx = γ b α dt` with `b = 1` and
`dα = -γ²κ(α - γ⁻¹m(x))dt + γσ dW`, `m(x) = -x`, `κ = σ = 1` (so `A₀ = α`, `A₁ = -m`,
`α₀ = m`).  Here `χ = α`, `ρ₁ = α²/2`, `ρ₂ = 0`, `D = ½`, `E = m = -x`, and the limit operator is
`-x f' + ½ f''` (an Ornstein–Uhlenbeck process with positive diffusion). -/
theorem nlc_ou_instance {ε : ℝ} (hε : ε ≠ 0) (x α f1 f2 f3 : ℝ) :
    ε⁻¹ ^ 2 * ((ε * f1 * (-α) + ε ^ 2 * (f2 * (1 / 2 - α ^ 2) + f1 * 0))
        + ε * (ε * f1 * (-x) + ε ^ 2 * (f2 * (-x * α) + f1 * 0)))
        + ε⁻¹ * α * wnPhix ε α 0 (α ^ 2 / 2) 0 0 0 f1 f2 f3
      = -x * f1 + (1 / 2) * f2 + ε * (wnR1 0 α α 0 (α ^ 2 / 2) 0 0 0 f1 f2 f3
          + f2 * (-x * α) + f1 * 0) :=
  nlc_generator hε α α 0 (α ^ 2 / 2) 0 0 0 (1 / 2) (-x) (-α) (1 / 2 - α ^ 2) 0 (-x) (-x * α) 0
    _ _ f1 f2 f3 rfl (by ring) (by ring) rfl rfl

end Gardiner.Adiabatic
