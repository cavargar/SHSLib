/-
# Small noise expansion of the Fokker–Planck equation

Gardiner, *Handbook of Stochastic Methods*, §6.1 and §6.3 (equations (6.1.6)–(6.1.13) and
(6.3.1)–(6.3.35)).

* §6.1: the Ornstein–Uhlenbeck example (6.1.8), its scaled form (6.1.10)–(6.1.12), and the
  concentration (6.1.9) `p_ε → δ(x - α(t))` (`Gardiner.ouDensity_tendsto_delta`).
* (6.3.1)–(6.3.8): `Gardiner.smallNoise_scaledFP` — the change of variables
  `y = (x - α(t))/ε`, `p̂ = ε p` turns the Fokker–Planck equation (6.3.1) into (6.3.8),
  provided `α` solves the deterministic equation (6.3.2).
* (6.3.9)–(6.3.14): the perturbation hierarchy, obtained by equating coefficients of formal
  power series in `ε` (`Gardiner.formalRHS_eq_hierRHS`, `Gardiner.hierarchy_iff`).
  The second displayed equation of the text is labelled `∂p̂_r/∂s` but is the `r = 1`
  equation `∂p̂₁/∂s`.
* `Gardiner.snGen_sub_ouGen_le`: **an explicit error bound for the small-noise limit**: the
  generator of (6.3.8) is within `|ε| (K y² |f'| + L |y| |f''|)/2` of the generator of the
  time-dependent Ornstein–Uhlenbeck equation (6.3.12).
-/
import SHSLib.Gardiner.Approx.Calculus

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators Nat NNReal

noncomputable section

namespace Gardiner

/-! ### §6.1: the Ornstein–Uhlenbeck example -/

/-- (6.1.6)–(6.1.8): the Gaussian density `p_ε(x, t | c, 0)` with mean `α = α(t)` and
variance `ε² β`, `β = β(t)`. -/
def ouDensity (ε α β : ℝ) (x : ℝ) : ℝ := gaussianPDFReal α (ε ^ 2 * β).toNNReal x

/-- (6.1.10)–(6.1.12): in the scaled variable `y = (x - α)/ε` the density
`p̄_ε(y) = ε p_ε(α + ε y)` is the centred Gaussian of variance `β`, independent of `ε`. -/
theorem ouDensity_scaled {ε : ℝ} (hε : 0 < ε) (α : ℝ) {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    ε * ouDensity ε α β (α + ε * y) = gaussianPDFReal 0 β.toNNReal y := by
  have hv : ((ε ^ 2 * β).toNNReal : ℝ) = ε ^ 2 * β := Real.coe_toNNReal _ (by positivity)
  have hv' : (β.toNNReal : ℝ) = β := Real.coe_toNNReal _ hβ.le
  simp only [ouDensity, gaussianPDFReal_def, hv, hv']
  have h1 : Real.sqrt (2 * Real.pi * (ε ^ 2 * β)) = ε * Real.sqrt (2 * Real.pi * β) := by
    rw [show 2 * Real.pi * (ε ^ 2 * β) = ε ^ 2 * (2 * Real.pi * β) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le]
  rw [h1]
  have h2 : -(α + ε * y - α) ^ 2 / (2 * (ε ^ 2 * β)) = -(y - 0) ^ 2 / (2 * β) := by
    field_simp
    ring
  rw [h2]
  have : Real.sqrt (2 * Real.pi * β) ≠ 0 := by positivity
  field_simp

/-- (6.1.9): as `ε → 0` the density `p_ε` concentrates on the deterministic path,
`p_ε(x, t | c, 0) → δ(x - α(t))`, in the sense that `∫ f p_ε → f(α)` for every bounded
continuous `f`. -/
theorem ouDensity_tendsto_delta (α : ℝ) {β : ℝ} (hβ : 0 < β) (f : ℝ → ℝ) (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Tendsto (fun ε => ∫ x, f x * ouDensity ε α β x) (𝓝[>] 0) (𝓝 (f α)) := by
  set g : ℝ → ℝ := gaussianPDFReal 0 β.toNNReal
  have hβ' : β.toNNReal ≠ 0 := by simpa using hβ
  have hscale : ∀ ε > (0 : ℝ),
      ∫ x, f x * ouDensity ε α β x = ∫ y, f (α + ε * y) * g y := by
    intro ε hε
    have hcv := Measure.integral_comp_mul_left (fun u => f (α + u) * ouDensity ε α β (α + u)) ε
    simp only [smul_eq_mul, abs_inv, abs_of_pos hε] at hcv
    rw [integral_add_left_eq_self (fun x => f x * ouDensity ε α β x)] at hcv
    have : ∀ y, f (α + ε * y) * g y = ε * (f (α + ε * y) * ouDensity ε α β (α + ε * y)) := by
      intro y
      show f (α + ε * y) * gaussianPDFReal 0 β.toNNReal y = _
      rw [← ouDensity_scaled hε α hβ y]
      ring
    simp_rw [this]
    rw [integral_const_mul, hcv]
    field_simp
  have hlim : Tendsto (fun ε => ∫ y, f (α + ε * y) * g y) (𝓝[>] 0) (𝓝 (∫ y, f α * g y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => C * g y) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun ε =>
        ((hf.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable).mul
          (integrable_gaussianPDFReal 0 _).aestronglyMeasurable
    · refine Eventually.of_forall fun ε => Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_right (hC _) (gaussianPDFReal_nonneg _ _ _)
    · exact (integrable_gaussianPDFReal 0 _).const_mul C
    · refine Eventually.of_forall fun y => ?_
      have : Tendsto (fun ε : ℝ => f (α + ε * y)) (𝓝 0) (𝓝 (f α)) := by
        have hc : Continuous (fun ε : ℝ => f (α + ε * y)) := by fun_prop
        simpa using hc.tendsto 0
      exact (this.mono_left nhdsWithin_le_nhds).mul_const _
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 hβ', mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hscale ε hε).symm

/-! ### (6.3.1)–(6.3.8): the scaled Fokker–Planck equation -/

/-- The right-hand side of the Fokker–Planck equation (6.3.1),
`-∂ₓ[A(x) q] + ½ ε² ∂ₓ²[B(x) q]`. -/
def snFP (A B : ℝ → ℝ) (ε : ℝ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (fun x => A x * q x) x + (1 / 2) * ε ^ 2 * deriv (deriv (fun x => B x * q x)) x

/-- (6.3.3)–(6.3.5): the density `p̂(y, s) = ε p(α(s) + ε y, s)` of the scaled variable
`y = (x - α(s))/ε`. -/
def scaledDensity (ε : ℝ) (α : ℝ → ℝ) (p : ℝ → ℝ → ℝ) (s y : ℝ) : ℝ := ε * p (α s + ε * y) s

/-- The right-hand side of (6.3.8), at a fixed time with `a = α(s)`:
`-∂_y{[A(a + εy) - A(a)]/ε · q} + ½ ∂_y²{B(a + εy) q}`. -/
def scaledFP (A B : ℝ → ℝ) (ε a : ℝ) (q : ℝ → ℝ) (y : ℝ) : ℝ :=
  -deriv (fun y => (A (a + ε * y) - A a) / ε * q y) y
    + (1 / 2) * deriv (deriv (fun y => B (a + ε * y) * q y)) y

/-- The chain rule `∂_y g(a + εy) = ε g'(a + εy)` (valid for every `g`). -/
lemma deriv_comp_affine (g : ℝ → ℝ) (a ε y : ℝ) :
    deriv (fun y => g (a + ε * y)) y = ε * deriv g (a + ε * y) := by
  have h := deriv_comp_mul_left (f := fun u => g (a + u)) ε y
  simp only [smul_eq_mul] at h
  rw [h, deriv_comp_const_add (f := g)]

/-- **(6.3.6)–(6.3.8).**  If `p(x, t)` satisfies the Fokker–Planck equation (6.3.1) at the
point `x = α(s) + εy` and `α` solves the deterministic equation (6.3.2) `α' = A(α)`, then
the scaled density `p̂(y, s) = ε p(α(s) + εy, s)` satisfies (6.3.8) at `y`. -/
theorem smallNoise_scaledFP (A B α : ℝ → ℝ) (p : ℝ → ℝ → ℝ) {ε : ℝ} (hε : ε ≠ 0) (s y : ℝ)
    (L : ℝ × ℝ →L[ℝ] ℝ)
    (hα : HasDerivAt α (A (α s)) s)
    (hp : HasFDerivAt (fun q : ℝ × ℝ => p q.1 q.2) L (α s + ε * y, s))
    (hAp : DifferentiableAt ℝ (fun x => A x * p x s) (α s + ε * y))
    (hfpe : L (0, 1) = snFP A B ε (fun x => p x s) (α s + ε * y)) :
    HasDerivAt (fun s' => scaledDensity ε α p s' y)
      (scaledFP A B ε (α s) (scaledDensity ε α p s) y) s := by
  set a := α s
  set x := a + ε * y with hx
  -- the time derivative of `p̂`
  have hγ : HasDerivAt (fun s' => (α s' + ε * y, s')) (A a, (1 : ℝ)) s :=
    (hα.add_const _).prodMk (hasDerivAt_id s)
  have hlhs := (HasFDerivAt.comp_hasDerivAt (f := fun s' => (α s' + ε * y, s')) s hp hγ).const_mul ε
  -- the space derivative of `p`
  have hpx : HasDerivAt (fun x' => p x' s) (L (1, 0)) x := by
    have hσ : HasDerivAt (fun x' : ℝ => (x', s)) ((1 : ℝ), (0 : ℝ)) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x s)
    exact HasFDerivAt.comp_hasDerivAt (f := fun x' : ℝ => (x', s)) x hp hσ
  have hL : L (A a, 1) = A a * L (1, 0) + L (0, 1) := by
    have : ((A a, (1 : ℝ)) : ℝ × ℝ) = A a • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  -- the drift term of (6.3.8)
  have hdrift : deriv (fun y => (A (a + ε * y) - A a) / ε * scaledDensity ε α p s y) y
      = ε * (deriv (fun x => A x * p x s) x - A a * L (1, 0)) := by
    set g : ℝ → ℝ := fun x' => A x' * p x' s - A a * p x' s with hg
    have hfun : (fun y => (A (a + ε * y) - A a) / ε * scaledDensity ε α p s y)
        = fun y => g (a + ε * y) := by
      funext y'
      simp only [scaledDensity, hg]
      field_simp
      rfl
    have hgd : deriv g x = deriv (fun x => A x * p x s) x - A a * L (1, 0) := by
      rw [hg, deriv_fun_sub hAp (hpx.differentiableAt.const_mul _),
        deriv_const_mul _ hpx.differentiableAt, hpx.deriv]
    rw [hfun, deriv_comp_affine, hgd]
  -- the diffusion term of (6.3.8)
  have hdiff : deriv (deriv (fun y => B (a + ε * y) * scaledDensity ε α p s y)) y
      = ε ^ 3 * deriv (deriv (fun x => B x * p x s)) x := by
    set h : ℝ → ℝ := fun x' => B x' * p x' s with hh
    have hfun : (fun y => B (a + ε * y) * scaledDensity ε α p s y)
        = fun y => ε * h (a + ε * y) := by
      funext y'; simp only [scaledDensity, hh]; ring
    have h1 : deriv (fun y => B (a + ε * y) * scaledDensity ε α p s y)
        = fun y => ε * (ε * deriv h (a + ε * y)) := by
      rw [hfun]
      funext y'
      rw [deriv_const_mul_field, deriv_comp_affine]
    set h' := deriv h
    rw [h1, deriv_const_mul_field, deriv_const_mul_field, deriv_comp_affine]
    ring
  have hval : ε * L (A a, 1) = scaledFP A B ε a (scaledDensity ε α p s) y := by
    rw [scaledFP, hdrift, hdiff, hL, hfpe, snFP]
    ring
  rw [← hval]
  exact hlhs

/-! ### (6.3.9)–(6.3.14): the perturbation hierarchy -/

/-- (6.3.9) as a formal power series in `ε` with coefficients functions of `y`:
`[A(α + εy) - A(α)]/ε = Σₙ Ãₙ₊₁ εⁿ yⁿ⁺¹`. -/
def driftSeries (At : ℕ → ℝ) : PowerSeries (ℝ → ℝ) :=
  PowerSeries.mk fun n y => At (n + 1) * y ^ (n + 1)

/-- (6.3.10) as a formal power series: `B(α + εy) = Σₙ B̃ₙ εⁿ yⁿ`. -/
def diffSeries (Bt : ℕ → ℝ) : PowerSeries (ℝ → ℝ) :=
  PowerSeries.mk fun n y => Bt n * y ^ n

/-- (6.3.11): `p̂ = Σₙ p̂ₙ εⁿ`. -/
def densitySeries (ph : ℕ → ℝ → ℝ) : PowerSeries (ℝ → ℝ) := PowerSeries.mk ph

/-- The coefficient of `εʳ` in the formal right-hand side of (6.3.8) after the
substitutions (6.3.9)–(6.3.11). -/
def formalRHS (At Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r : ℕ) (y : ℝ) : ℝ :=
  -deriv (PowerSeries.coeff r (driftSeries At * densitySeries ph)) y
    + (1 / 2) * deriv (deriv (PowerSeries.coeff r (diffSeries Bt * densitySeries ph))) y

/-- The drift flux `Σ_{m ≤ r} y^{r-m+1} Ã_{r-m+1} p̂ₘ` of (6.3.14). -/
def hierFlux (At : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r : ℕ) (y : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (r + 1), y ^ (r - m + 1) * At (r - m + 1) * ph m y

/-- The diffusion term `Σ_{m ≤ r} y^{r-m} B̃_{r-m} p̂ₘ` of (6.3.14). -/
def hierDiff (Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r : ℕ) (y : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (r + 1), y ^ (r - m) * Bt (r - m) * ph m y

/-- The right-hand side of (6.3.14). -/
def hierRHS (At Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r : ℕ) (y : ℝ) : ℝ :=
  -deriv (hierFlux At ph r) y + (1 / 2) * deriv (deriv (hierDiff Bt ph r)) y

lemma coeff_driftSeries_mul (At : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r : ℕ) :
    PowerSeries.coeff r (driftSeries At * densitySeries ph) = hierFlux At ph r := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (driftSeries At) * PowerSeries.coeff j (densitySeries ph))]
  funext y
  simp only [driftSeries, densitySeries, PowerSeries.coeff_mk, hierFlux, Finset.sum_apply,
    Pi.mul_apply]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  rw [show r + 1 - 1 - m = r - m by omega, show r - (r - m) = m by omega]
  ring

lemma coeff_diffSeries_mul (Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r : ℕ) :
    PowerSeries.coeff r (diffSeries Bt * densitySeries ph) = hierDiff Bt ph r := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (diffSeries Bt) * PowerSeries.coeff j (densitySeries ph))]
  funext y
  simp only [diffSeries, densitySeries, PowerSeries.coeff_mk, hierDiff, Finset.sum_apply,
    Pi.mul_apply]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  rw [show r + 1 - 1 - m = r - m by omega, show r - (r - m) = m by omega]
  ring

/-- **(6.3.14)**: equating the coefficient of `εʳ` in (6.3.8), after substituting the
expansions (6.3.9)–(6.3.11), gives the `r`-th equation of the hierarchy. -/
theorem formalRHS_eq_hierRHS (At Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (r : ℕ) :
    formalRHS At Bt ph r = hierRHS At Bt ph r := by
  funext y
  rw [formalRHS, hierRHS, coeff_driftSeries_mul, coeff_diffSeries_mul]

/-- **Equating coefficients**: the formal equation `∂ₛ p̂ = RHS(6.3.8)` holds as an identity
of power series in `ε` if and only if every equation (6.3.14) of the hierarchy holds. -/
theorem hierarchy_iff (At Bt : ℕ → ℝ) (ph dph : ℕ → ℝ → ℝ) :
    densitySeries dph = PowerSeries.mk (formalRHS At Bt ph)
      ↔ ∀ r, dph r = hierRHS At Bt ph r := by
  constructor
  · intro h r
    have := congrArg (PowerSeries.coeff r) h
    simpa [densitySeries, formalRHS_eq_hierRHS] using this
  · intro h
    ext r : 1
    simp [densitySeries, formalRHS_eq_hierRHS, h r]

/-- (6.3.12): the zeroth equation of the hierarchy, a time-dependent Ornstein–Uhlenbeck
equation `∂ₛ p̂₀ = -Ã₁ ∂_y(y p̂₀) + ½ B̃₀ ∂_y² p̂₀`. -/
theorem hierRHS_zero (At Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (y : ℝ) :
    hierRHS At Bt ph 0 y
      = -At 1 * deriv (fun y => y * ph 0 y) y + (1 / 2) * Bt 0 * deriv (deriv (ph 0)) y := by
  have h1 : hierFlux At ph 0 = fun y => At 1 * (y * ph 0 y) := by
    funext y; simp [hierFlux]; ring
  have h2 : hierDiff Bt ph 0 = fun y => Bt 0 * ph 0 y := by
    funext y; simp [hierDiff]
  rw [hierRHS, h1, h2, deriv_const_mul_field, deriv_const_mul_field', deriv_const_mul_field]
  ring

/-- (6.3.13), the `r = 1` equation of the hierarchy:
`∂ₛ p̂₁ = -∂_y[Ã₁ y p̂₁ + Ã₂ y² p̂₀] + ½ ∂_y²[B̃₀ p̂₁ + B̃₁ y p̂₀]`. -/
theorem hierRHS_one (At Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (y : ℝ) :
    hierRHS At Bt ph 1 y
      = -deriv (fun y => At 1 * y * ph 1 y + At 2 * y ^ 2 * ph 0 y) y
        + (1 / 2) * deriv (deriv (fun y => Bt 0 * ph 1 y + Bt 1 * y * ph 0 y)) y := by
  have h1 : hierFlux At ph 1 = fun y => At 1 * y * ph 1 y + At 2 * y ^ 2 * ph 0 y := by
    funext y; simp [hierFlux, Finset.sum_range_succ]; ring
  have h2 : hierDiff Bt ph 1 = fun y => Bt 0 * ph 1 y + Bt 1 * y * ph 0 y := by
    funext y; simp [hierDiff, Finset.sum_range_succ]; ring
  rw [hierRHS, h1, h2]

/-- When `A` (resp. `B`) is a polynomial, the expansions (6.3.9)–(6.3.10) are exact: a
derivative tower whose `(n+1)`-st member vanishes identically has an exact Taylor
expansion of order `n`. -/
theorem taylor_exact_of_tower (n : ℕ) (D : ℕ → ℝ → ℝ) (x h : ℝ)
    (hD : ∀ k ≤ n, ∀ y, HasDerivAt (D k) (D (k + 1) y) y) (h0 : ∀ y, D (n + 1) y = 0) :
    D 0 (x + h) = taylorTower D n x h := by
  have := taylor_tower_bound n D x h 0 hD (fun t _ => by rw [h0]; simp)
  simp only [zero_mul, zero_div] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### The small-noise limit of the generator, with an explicit error -/

/-- The generator (backward operator) of the scaled equation (6.3.8), acting on a test
function with `f'(y) = f₁`, `f''(y) = f₂`. -/
def snGen (A B : ℝ → ℝ) (ε a y f₁ f₂ : ℝ) : ℝ :=
  (A (a + ε * y) - A a) / ε * f₁ + (1 / 2) * B (a + ε * y) * f₂

/-- The generator of the time-dependent Ornstein–Uhlenbeck equation (6.3.12),
`Ã₁ y f' + ½ B̃₀ f''`. -/
def ouGen (A₁ B₀ y f₁ f₂ : ℝ) : ℝ := A₁ * y * f₁ + (1 / 2) * B₀ * f₂

/-- **The small-noise limit with an explicit error.**  Let `A = E 0` have derivatives
`E 1, E 2` with `|A''| ≤ K` between `a` and `a + εy`, and let `B` satisfy
`|B(a + εy) - B(a)| ≤ L |εy|`.  Then the generator of (6.3.8) differs from that of the
Ornstein–Uhlenbeck equation (6.3.12), with `Ã₁ = A'(a)`, `B̃₀ = B(a)`, by at most
`|ε| (K y² |f'| + L |y| |f''|)/2`. -/
theorem snGen_sub_ouGen_le (E : ℕ → ℝ → ℝ) (B : ℝ → ℝ) {ε : ℝ} (hε : ε ≠ 0) (a y f₁ f₂ K L : ℝ)
    (hE : ∀ k ≤ 1, ∀ u, HasDerivAt (E k) (E (k + 1) u) u)
    (hK : ∀ t ∈ uIcc 0 (ε * y), |E 2 (a + t)| ≤ K)
    (hB : |B (a + ε * y) - B a| ≤ L * |ε * y|) :
    |snGen (E 0) B ε a y f₁ f₂ - ouGen (E 1 a) (B a) y f₁ f₂|
      ≤ |ε| * (K * y ^ 2 * |f₁| / 2 + L * |y| * |f₂| / 2) := by
  have hT := taylor_tower_bound 1 E a (ε * y) K hE hK
  simp only [taylorTower, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hT
  norm_num at hT
  have e : snGen (E 0) B ε a y f₁ f₂ - ouGen (E 1 a) (B a) y f₁ f₂
      = (E 0 (a + ε * y) - (E 0 a + E 1 a * (ε * y))) / ε * f₁
        + (1 / 2) * (B (a + ε * y) - B a) * f₂ := by
    simp only [snGen, ouGen]
    field_simp
    ring
  rw [e]
  have hε' : 0 < |ε| := abs_pos.2 hε
  refine (abs_add_le _ _).trans ?_
  have h1 : |(E 0 (a + ε * y) - (E 0 a + E 1 a * (ε * y))) / ε * f₁|
      ≤ |ε| * (K * y ^ 2 * |f₁| / 2) := by
    rw [abs_mul, abs_div]
    have : |E 0 (a + ε * y) - (E 0 a + E 1 a * (ε * y))| ≤ K * |ε * y| ^ 2 / 2 := by
      have e2 : E 0 a + E 1 a * (ε * y) = E 0 a + E 1 a * (ε * y) := rfl
      calc _ = |E 0 (a + ε * y) - (E 0 a + E 1 a * (ε * y))| := rfl
        _ ≤ K * |ε * y| ^ 2 / 2 := by simpa [add_comm, mul_comm, mul_assoc, mul_left_comm] using hT
    calc |E 0 (a + ε * y) - (E 0 a + E 1 a * (ε * y))| / |ε| * |f₁|
        ≤ (K * |ε * y| ^ 2 / 2) / |ε| * |f₁| := by gcongr
      _ = |ε| * (K * y ^ 2 * |f₁| / 2) := by
        rw [abs_mul, mul_pow, sq_abs y]
        field_simp
  have h2 : |(1 / 2) * (B (a + ε * y) - B a) * f₂| ≤ |ε| * (L * |y| * |f₂| / 2) := by
    rw [abs_mul, abs_mul]
    calc |(1 / 2 : ℝ)| * |B (a + ε * y) - B a| * |f₂| ≤ |(1 / 2 : ℝ)| * (L * |ε * y|) * |f₂| := by
          gcongr
      _ = _ := by rw [abs_mul]; norm_num; ring
  linarith

end Gardiner
