/-
# The exactly solvable reaction `X ⇌ A`

Gardiner, *Handbook of Stochastic Methods*, §7.1.2, equations (7.1.24)–(7.1.55).

The master equation (7.1.26) of the immigration–death process with immigration rate
`c = k₂a` and death rate `k₁x` is `∂ₜP = Gardiner.xaME c k₁ P`.  In generating-function form
(7.1.27)–(7.1.28) it reads `∂ₜG = (s - 1)(c G - k₁ ∂ₛ G)`, which is `Gardiner.xaOp` acting on
formal power series (`Gardiner.coeff_xaOp`).

Main results:

* `Gardiner.SolvesXA.mul` — independent superposition: a product of generating functions of
  solutions with immigration rates `c₁`, `c₂` solves the equation with rate `c₁ + c₂`.
* `Gardiner.poisson_solves_xaME`, `Gardiner.solvesXA_poisson` — (7.1.49)–(7.1.55): a Poisson
  law whose mean obeys `α' = k₂a - k₁α` solves the master equation.
* `Gardiner.xa_exact_solution`, `Gardiner.xaGen_zero`, `Gardiner.coeff_xaGen` — the exact
  solution (7.1.36)–(7.1.37) with initial condition `δ_{x,N}` (7.1.34): binomial thinning of
  the `N` initial molecules convolved with a Poisson law.
* `Gardiner.xaGenFun_hasDerivAt_t` — the closed form (7.1.36) of `G(s, t)` solves (7.1.28);
  `Gardiner.xaGenFun_one`, `Gardiner.xaGenFun_deriv_one`, `Gardiner.xaGenFun_deriv2_one`,
  `Gardiner.xa_variance_formula` give (7.1.38)–(7.1.40);
  `Gardiner.xaGenFun_tendsto` is (7.1.44) and `Gardiner.poisson_stationary` is (7.1.45).
* `Gardiner.xaME_tsum_by_parts` and its corollaries — the moment equations
  (7.1.41)–(7.1.43): `Gardiner.xa_factorial_moment_identity` is (7.1.43) for every `n`.
* `Gardiner.xa_mean_variance_exact` — for any solution of the master equation started at
  `δ_{x,N}`, the mean and variance are exactly (7.1.38) and (7.1.40).
-/
import SHSLib.Gardiner.Approx.Calculus

open PowerSeries Filter Topology
open scoped Nat

noncomputable section

namespace Gardiner

/-! ### The master equation and its generating function -/

/-- The right-hand side of the master equation (7.1.26) of `X ⇌ A`: immigration at rate
`c = k₂a` (7.1.24), death at rate `k₁x` (7.1.25),
`c P(x-1) + k₁(x+1) P(x+1) - (k₁x + c) P(x)`, with `P(-1) = 0`. -/
def xaME (c k₁ : ℝ) (P : ℕ → ℝ) (x : ℕ) : ℝ :=
  c * (if x = 0 then 0 else P (x - 1)) + k₁ * ((x : ℝ) + 1) * P (x + 1) - (k₁ * x + c) * P x

/-- The generating-function form (7.1.28) of the operator, `(s - 1)(c G - k₁ ∂ₛ G)`, on formal
power series `G = Σₓ P(x) sˣ` (7.1.27). -/
def xaOp (c k₁ : ℝ) (G : PowerSeries ℝ) : PowerSeries ℝ :=
  (X - 1) * (C c * G - C k₁ * d⁄dX ℝ G)

/-- (7.1.26) ⟺ (7.1.28): the coefficients of `xaOp G` are the master-equation operator applied
to the coefficients of `G`. -/
theorem coeff_xaOp (c k₁ : ℝ) (G : PowerSeries ℝ) (n : ℕ) :
    coeff n (xaOp c k₁ G) = xaME c k₁ (fun x => coeff x G) n := by
  simp only [xaOp, xaME, sub_mul, one_mul, map_sub, coeff_C_mul, coeff_derivative]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul]
    simp only [map_sub, coeff_C_mul, coeff_derivative]
    push_cast
    ring_nf

/-- `G(t)` solves the generating-function equation (7.1.28), coefficient by coefficient. -/
def SolvesXA (c k₁ : ℝ) (G : ℝ → PowerSeries ℝ) : Prop :=
  ∀ t n, HasDerivAt (fun t => coeff n (G t)) (coeff n (xaOp c k₁ (G t))) t

/-- Equivalently, the coefficients `P(x, t)` of `G(t)` solve the master equation (7.1.26). -/
theorem solvesXA_iff (c k₁ : ℝ) (G : ℝ → PowerSeries ℝ) :
    SolvesXA c k₁ G ↔ ∀ t x, HasDerivAt (fun t => coeff x (G t))
      (xaME c k₁ (fun y => coeff y (G t)) x) t := by
  simp only [SolvesXA, coeff_xaOp]

lemma xaOp_mul (c₁ c₂ k₁ : ℝ) (G H : PowerSeries ℝ) :
    xaOp (c₁ + c₂) k₁ (G * H) = xaOp c₁ k₁ G * H + G * xaOp c₂ k₁ H := by
  simp only [xaOp, Derivation.leibniz, smul_eq_mul, map_add]
  ring

/-- **Independent superposition**: the product of generating functions of solutions with
immigration rates `c₁`, `c₂` (and the same death rate `k₁`) solves the equation with
immigration rate `c₁ + c₂`.  For the probabilities this is the convolution of the two laws. -/
theorem SolvesXA.mul {c₁ c₂ k₁ : ℝ} {G H : ℝ → PowerSeries ℝ} (hG : SolvesXA c₁ k₁ G)
    (hH : SolvesXA c₂ k₁ H) : SolvesXA (c₁ + c₂) k₁ (fun t => G t * H t) := by
  intro t n
  show HasDerivAt (fun t => coeff n (G t * H t)) _ t
  rw [xaOp_mul, map_add, coeff_mul, coeff_mul, ← Finset.sum_add_distrib]
  simp only [coeff_mul]
  apply HasDerivAt.fun_sum
  intro p _
  have := (hG t p.1).mul (hH t p.2)
  convert this using 1

theorem solvesXA_one (k₁ : ℝ) : SolvesXA 0 k₁ (fun _ => 1) := by
  intro t n
  simp only [xaOp, map_zero, zero_mul, Derivation.map_one_eq_zero, mul_zero, sub_zero, map_zero]
  exact hasDerivAt_const _ _

theorem SolvesXA.pow {k₁ : ℝ} {G : ℝ → PowerSeries ℝ} (hG : SolvesXA 0 k₁ G) (N : ℕ) :
    SolvesXA 0 k₁ (fun t => G t ^ N) := by
  induction N with
  | zero => simpa using solvesXA_one k₁
  | succ N ih =>
    have := ih.mul hG
    simpa [pow_succ] using this

/-! ### The pure-death part: binomial thinning -/

/-- A single molecule that survives to time `t` with probability `p(t) = e^{-k₁t}`: generating
function `1 - p + p s`. -/
def oneMolecule (k₁ t : ℝ) : PowerSeries ℝ :=
  C (1 - Real.exp (-k₁ * t)) + C (Real.exp (-k₁ * t)) * X

lemma coeff_oneMolecule (k₁ t : ℝ) (n : ℕ) : coeff n (oneMolecule k₁ t)
    = if n = 0 then 1 - Real.exp (-k₁ * t) else if n = 1 then Real.exp (-k₁ * t) else 0 := by
  rcases n with _ | _ | n <;> simp [oneMolecule]

/-- One molecule solves the pure-death equation (`k₂a = 0`). -/
theorem solvesXA_oneMolecule (k₁ : ℝ) : SolvesXA 0 k₁ (oneMolecule k₁) := by
  rw [solvesXA_iff]
  intro t n
  simp only [coeff_oneMolecule, xaME]
  have hp : HasDerivAt (fun t => Real.exp (-k₁ * t)) (-k₁ * Real.exp (-k₁ * t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-k₁)).exp
  have hp' : HasDerivAt (fun t => Real.exp (-(k₁ * t))) (-(k₁ * Real.exp (-(k₁ * t)))) t := by
    simpa [neg_mul] using hp
  rcases n with _ | _ | n
  · simpa using hp'.const_sub 1
  · simpa using hp'
  · simpa using hasDerivAt_const t (0 : ℝ)

/-- The binomial law of the survivors among `N` molecules:
`coeff k ((1 - p + p s)ᴺ) = C(N, k) pᵏ (1 - p)^{N-k}`. -/
theorem coeff_oneMolecule_pow (k₁ t : ℝ) (N k : ℕ) :
    coeff k (oneMolecule k₁ t ^ N)
      = N.choose k * Real.exp (-k₁ * t) ^ k * (1 - Real.exp (-k₁ * t)) ^ (N - k) := by
  rw [oneMolecule]
  set p := Real.exp (-k₁ * t)
  have e : ∀ m, (C p * X) ^ m * C (1 - p) ^ (N - m) * (N.choose m : PowerSeries ℝ)
      = C (N.choose m * p ^ m * (1 - p) ^ (N - m)) * X ^ m := by
    intro m
    simp only [mul_pow, ← map_pow, map_mul, map_natCast]
    ring
  rw [add_comm, add_pow]
  simp_rw [e, map_sum, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simp at h; omega)]
    simp

/-! ### The Poisson part (7.1.49)–(7.1.55) -/

/-- The Poisson law with mean `α`, (7.1.45), (7.1.52). -/
def poissonPMF (α : ℝ) (x : ℕ) : ℝ := Real.exp (-α) * α ^ x / (x ! : ℝ)

/-- **(7.1.52)–(7.1.55)**: a Poisson law whose mean obeys the deterministic equation
`α' = k₂a - k₁α` (7.1.54) solves the master equation (7.1.26). -/
theorem poisson_solves_xaME (c k₁ : ℝ) (α : ℝ → ℝ) (t : ℝ)
    (hα : HasDerivAt α (c - k₁ * α t) t) (x : ℕ) :
    HasDerivAt (fun t => poissonPMF (α t) x) (xaME c k₁ (poissonPMF (α t)) x) t := by
  have h1 : HasDerivAt (fun t => Real.exp (-α t)) (Real.exp (-α t) * -(c - k₁ * α t)) t :=
    hα.neg.exp
  have h2 : HasDerivAt (fun t => α t ^ x) (x * α t ^ (x - 1) * (c - k₁ * α t)) t := hα.pow x
  have h := (h1.mul h2).div_const (x ! : ℝ)
  unfold poissonPMF
  convert h using 1
  rcases x with _ | m
  · simp [xaME]
    ring
  · simp only [xaME, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have h1 : (m ! : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- The generating function of the Poisson law: `Σₓ sˣ e^{-α} αˣ/x! = e^{(s-1)α}` (7.1.50). -/
theorem poisson_hasSum_genFun (α s : ℝ) :
    HasSum (fun x => s ^ x * poissonPMF α x) (Real.exp ((s - 1) * α)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (s * α)).mul_left (Real.exp (-α))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at h
  convert h using 1
  · funext x; simp only [poissonPMF]; rw [mul_pow]; ring
  · ring_nf

/-- (7.1.45): the Poisson law with mean `k₂a/k₁` is stationary. -/
theorem poisson_stationary (c k₁ : ℝ) (hk : k₁ ≠ 0) (x : ℕ) :
    xaME c k₁ (poissonPMF (c / k₁)) x = 0 := by
  have h := poisson_solves_xaME c k₁ (fun _ => c / k₁) 0
    (by convert hasDerivAt_const (0 : ℝ) (c / k₁) using 1; field_simp; ring) x
  exact (h.unique (hasDerivAt_const _ _)).trans rfl

/-- The deterministic mean (7.1.53): `α(t) = α₀ e^{-k₁t} + (k₂a/k₁)(1 - e^{-k₁t})`. -/
def xaMean (c k₁ α₀ t : ℝ) : ℝ := α₀ * Real.exp (-k₁ * t) + c / k₁ * (1 - Real.exp (-k₁ * t))

/-- (7.1.54)–(7.1.55): `α' = k₂a - k₁α`, `α(0) = α₀`. -/
theorem xaMean_hasDerivAt (c k₁ α₀ t : ℝ) (hk : k₁ ≠ 0) :
    HasDerivAt (xaMean c k₁ α₀) (c - k₁ * xaMean c k₁ α₀ t) t := by
  have hp : HasDerivAt (fun t => Real.exp (-k₁ * t)) (-k₁ * Real.exp (-k₁ * t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-k₁)).exp
  have := (hp.const_mul α₀).add ((hp.const_sub 1).const_mul (c / k₁))
  convert this using 1
  simp only [xaMean]
  field_simp
  ring

theorem xaMean_zero (c k₁ α₀ : ℝ) : xaMean c k₁ α₀ 0 = α₀ := by simp [xaMean]

/-- (7.1.51)–(7.1.52): the Poisson solution, as a generating function. -/
theorem solvesXA_poisson (c k₁ : ℝ) (α : ℝ → ℝ) (hα : ∀ t, HasDerivAt α (c - k₁ * α t) t) :
    SolvesXA c k₁ (fun t => mk (poissonPMF (α t))) := by
  rw [solvesXA_iff]
  intro t x
  simpa only [coeff_mk] using poisson_solves_xaME c k₁ α t (hα t) x

/-! ### The exact solution (7.1.36)–(7.1.37) -/

/-- The generating function of the exact solution with initial condition `δ_{x,N}`:
`(1 - p + p s)ᴺ · Σₓ sˣ e^{-α} αˣ/x!` with `p = e^{-k₁t}` and `α = (k₂a/k₁)(1 - e^{-k₁t})`;
cf. (7.1.36). -/
def xaGen (N : ℕ) (c k₁ t : ℝ) : PowerSeries ℝ :=
  oneMolecule k₁ t ^ N * mk (poissonPMF (xaMean c k₁ 0 t))

/-- **(7.1.36)–(7.1.37) solve (7.1.26).** -/
theorem xa_exact_solution (N : ℕ) (c k₁ : ℝ) (hk : k₁ ≠ 0) : SolvesXA c k₁ (xaGen N c k₁) := by
  have h := ((solvesXA_oneMolecule k₁).pow N).mul
    (solvesXA_poisson c k₁ (xaMean c k₁ 0) fun t => xaMean_hasDerivAt c k₁ 0 t hk)
  simpa [xaGen] using h

/-- (7.1.34): the initial condition `P(x, 0) = δ_{x,N}`, i.e. `G(s, 0) = sᴺ` (7.1.35). -/
theorem xaGen_zero (N : ℕ) (c k₁ : ℝ) : xaGen N c k₁ 0 = X ^ N := by
  have h1 : oneMolecule k₁ 0 = X := by simp [oneMolecule]
  have h2 : mk (poissonPMF (xaMean c k₁ 0 0)) = 1 := by
    ext n
    rcases n with _ | n <;> simp [poissonPMF, xaMean_zero, coeff_one]
  rw [xaGen, h1, h2, mul_one]

/-- **(7.1.37)**, the explicit solution:
`P(x, t) = Σ_{k + l = x} C(N,k) pᵏ (1-p)^{N-k} e^{-α} αˡ/l!`. -/
theorem coeff_xaGen (N : ℕ) (c k₁ t : ℝ) (x : ℕ) :
    coeff x (xaGen N c k₁ t) = ∑ q ∈ Finset.antidiagonal x,
      (N.choose q.1 * Real.exp (-k₁ * t) ^ q.1 * (1 - Real.exp (-k₁ * t)) ^ (N - q.1))
        * poissonPMF (xaMean c k₁ 0 t) q.2 := by
  rw [xaGen, coeff_mul]
  simp only [coeff_oneMolecule_pow, coeff_mk]

/-! ### The closed-form generating function (7.1.36) -/

/-- (7.1.36): `G(s, t) = exp[(k₂a/k₁)(s-1)(1 - e^{-k₁t})] [1 + (s-1)e^{-k₁t}]ᴺ`. -/
def xaGenFun (N : ℕ) (c k₁ s t : ℝ) : ℝ :=
  Real.exp (c / k₁ * (s - 1) * (1 - Real.exp (-k₁ * t))) * (1 + (s - 1) * Real.exp (-k₁ * t)) ^ N

/-- `∂ₛ G(s, t)`. -/
def xaGenFunDs (N : ℕ) (c k₁ s t : ℝ) : ℝ :=
  Real.exp (c / k₁ * (s - 1) * (1 - Real.exp (-k₁ * t))) *
    (c / k₁ * (1 - Real.exp (-k₁ * t)) * (1 + (s - 1) * Real.exp (-k₁ * t)) ^ N
      + N * (1 + (s - 1) * Real.exp (-k₁ * t)) ^ (N - 1) * Real.exp (-k₁ * t))

theorem xaGenFun_hasDerivAt_s (N : ℕ) (c k₁ s t : ℝ) :
    HasDerivAt (fun s => xaGenFun N c k₁ s t) (xaGenFunDs N c k₁ s t) s := by
  set p := Real.exp (-k₁ * t)
  have h1 : HasDerivAt (fun s => Real.exp (c / k₁ * (s - 1) * (1 - p)))
      (Real.exp (c / k₁ * (s - 1) * (1 - p)) * (c / k₁ * (1 - p))) s := by
    have : HasDerivAt (fun s => c / k₁ * (s - 1) * (1 - p)) (c / k₁ * (1 - p)) s := by
      simpa using (((hasDerivAt_id s).sub_const 1).const_mul (c / k₁)).mul_const (1 - p)
    exact this.exp
  have h2 : HasDerivAt (fun s => (1 + (s - 1) * p) ^ N) (N * (1 + (s - 1) * p) ^ (N - 1) * p) s := by
    have : HasDerivAt (fun s => 1 + (s - 1) * p) p s := by
      simpa using (((hasDerivAt_id s).sub_const 1).mul_const p).const_add 1
    simpa using this.pow N
  have := h1.mul h2
  convert this using 1
  simp only [xaGenFunDs]
  ring

/-- **(7.1.36) solves (7.1.28)**: `∂ₜG = (s - 1)(k₂a G - k₁ ∂ₛG)`. -/
theorem xaGenFun_hasDerivAt_t (N : ℕ) (c k₁ s t : ℝ) (hk : k₁ ≠ 0) :
    HasDerivAt (fun t => xaGenFun N c k₁ s t)
      ((s - 1) * (c * xaGenFun N c k₁ s t - k₁ * xaGenFunDs N c k₁ s t)) t := by
  have hp : HasDerivAt (fun t => Real.exp (-k₁ * t)) (-k₁ * Real.exp (-k₁ * t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-k₁)).exp
  set p := Real.exp (-k₁ * t)
  have h1 := ((hp.const_sub 1).const_mul (c / k₁ * (s - 1))).exp
  have h2 := ((hp.const_mul (s - 1)).const_add 1).pow N
  have := h1.mul h2
  convert this using 1
  simp only [xaGenFun, xaGenFunDs, Pi.pow_apply]
  have hc : c / k₁ * k₁ = c := div_mul_cancel₀ c hk
  linear_combination (-(s - 1) * Real.exp (c / k₁ * (s - 1) * (1 - p)) * (1 + (s - 1) * p) ^ N) * hc

/-- Normalisation, `G(1, t) = Σₓ P(x, t) = 1`. -/
theorem xaGenFun_one (N : ℕ) (c k₁ t : ℝ) : xaGenFun N c k₁ 1 t = 1 := by
  simp [xaGenFun]

/-- **(7.1.38)**: `⟨x(t)⟩ = ∂ₛG(1, t) = (k₂a/k₁)(1 - e^{-k₁t}) + N e^{-k₁t}`. -/
theorem xaGenFun_deriv_one (N : ℕ) (c k₁ t : ℝ) :
    xaGenFunDs N c k₁ 1 t = xaMean c k₁ N t := by
  simp [xaGenFunDs, xaMean]
  ring

/-- **(7.1.39)**: `⟨x(x-1)⟩ = ∂ₛ²G(1, t) = ⟨x⟩² - N e^{-2k₁t}`. -/
theorem xaGenFun_deriv2_one (N : ℕ) (c k₁ t : ℝ) :
    HasDerivAt (fun s => xaGenFunDs N c k₁ s t)
      (xaMean c k₁ N t ^ 2 - N * Real.exp (-k₁ * t) ^ 2) 1 := by
  unfold xaMean
  set p := Real.exp (-k₁ * t)
  set a := c / k₁ * (1 - p)
  have hE : HasDerivAt (fun s => Real.exp (c / k₁ * (s - 1) * (1 - p)))
      (Real.exp (c / k₁ * (1 - 1) * (1 - p)) * a) 1 := by
    have : HasDerivAt (fun s => c / k₁ * (s - 1) * (1 - p)) a 1 := by
      simpa [a] using (((hasDerivAt_id (1 : ℝ)).sub_const 1).const_mul (c / k₁)).mul_const (1 - p)
    exact this.exp
  have hL : HasDerivAt (fun s => 1 + (s - 1) * p) p 1 := by
    simpa using (((hasDerivAt_id (1 : ℝ)).sub_const 1).mul_const p).const_add 1
  have hP := hL.pow N
  have hQ := hL.pow (N - 1)
  have := hE.mul ((hP.const_mul a).add ((hQ.const_mul (N : ℝ)).mul_const p))
  convert this using 1
  · simp only [sub_self, mul_zero, zero_mul, Real.exp_zero, one_pow, add_zero, one_mul, a]
    rcases N with _ | N
    · simp; ring
    · simp only [Nat.add_sub_cancel, Pi.pow_apply, Pi.add_apply]
      push_cast
      ring

/-- **(7.1.40)**: the factorial moments (7.1.38)–(7.1.39) give
`var x(t) = (N e^{-k₁t} + k₂a/k₁)(1 - e^{-k₁t})`. -/
theorem xa_variance_formula (N : ℕ) (c k₁ t : ℝ) :
    (xaMean c k₁ N t ^ 2 - N * Real.exp (-k₁ * t) ^ 2) + xaMean c k₁ N t - xaMean c k₁ N t ^ 2
      = (N * Real.exp (-k₁ * t) + c / k₁) * (1 - Real.exp (-k₁ * t)) := by
  simp only [xaMean]; ring

/-- **(7.1.44)**: `G(s, t) → exp[(s - 1) k₂a/k₁]` as `t → ∞` (for `k₁ > 0`), the generating
function (7.1.50) of the Poisson law (7.1.45). -/
theorem xaGenFun_tendsto (N : ℕ) (c k₁ s : ℝ) (hk : 0 < k₁) :
    Tendsto (fun t => xaGenFun N c k₁ s t) atTop (𝓝 (Real.exp ((s - 1) * (c / k₁)))) := by
  have hp : Tendsto (fun t => Real.exp (-k₁ * t)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith)
  have h1 : Tendsto (fun t => Real.exp (c / k₁ * (s - 1) * (1 - Real.exp (-k₁ * t)))) atTop
      (𝓝 (Real.exp (c / k₁ * (s - 1) * (1 - 0)))) :=
    (Real.continuous_exp.tendsto _).comp ((hp.const_sub 1).const_mul _)
  have h2 : Tendsto (fun t => (1 + (s - 1) * Real.exp (-k₁ * t)) ^ N) atTop
      (𝓝 ((1 + (s - 1) * 0) ^ N)) := ((hp.const_mul (s - 1)).const_add 1).pow N
  have := h1.mul h2
  simp only [sub_zero, mul_one, mul_zero, add_zero, one_pow] at this
  simpa [xaGenFun, mul_comm] using this

/-! ### The moment equations (7.1.41)–(7.1.43) -/

/-- Summation by parts for the master equation (7.1.26):
`Σₓ f(x) (∂ₜP)(x) = Σₓ P(x) [k₂a (f(x+1) - f(x)) + k₁x (f(x-1) - f(x))]`, under absolute
summability of the four shifted series. -/
theorem xaME_tsum_by_parts (c k₁ : ℝ) (P f : ℕ → ℝ)
    (h1 : Summable fun x : ℕ => f (x + 1) * P x) (h2 : Summable fun x : ℕ => f x * P x)
    (h3 : Summable fun x : ℕ => (x : ℝ) * f x * P x)
    (h4 : Summable fun x : ℕ => (x : ℝ) * f (x - 1) * P x) :
    ∑' x : ℕ, f x * xaME c k₁ P x
      = ∑' x : ℕ, P x * (c * (f (x + 1) - f x) + k₁ * x * (f (x - 1) - f x)) := by
  set g : ℕ → ℝ := fun x : ℕ => f x * (if x = 0 then 0 else P (x - 1))
  have hg1 : (fun x : ℕ => g (x + 1)) = fun x : ℕ => f (x + 1) * P x := by
    funext x; simp [g]
  have hg : Summable g := (summable_nat_add_iff 1).1 (by rw [hg1]; exact h1)
  have hgs : ∑' x : ℕ, g x = ∑' x : ℕ, f (x + 1) * P x := by
    rw [hg.tsum_eq_zero_add, hg1]; simp [g]
  set h : ℕ → ℝ := fun x : ℕ => (x : ℝ) * f (x - 1) * P x
  have hh1 : (fun x : ℕ => h (x + 1)) = fun x : ℕ => f x * ((x : ℝ) + 1) * P (x + 1) := by
    funext x
    show ((x + 1 : ℕ) : ℝ) * f (x + 1 - 1) * P (x + 1) = _
    simp only [Nat.add_sub_cancel]; push_cast; ring
  have hh : Summable fun x : ℕ => f x * ((x : ℝ) + 1) * P (x + 1) := by
    rw [← hh1]; exact (summable_nat_add_iff 1).2 h4
  have hhs : ∑' x : ℕ, f x * ((x : ℝ) + 1) * P (x + 1) = ∑' x : ℕ, (x : ℝ) * f (x - 1) * P x := by
    rw [h4.tsum_eq_zero_add]
    show _ = h 0 + ∑' b, (fun x : ℕ => h (x + 1)) b
    rw [hh1]; simp [h]
  have A : HasSum (fun x : ℕ => f x * xaME c k₁ P x)
      (c * ∑' x : ℕ, g x + k₁ * ∑' x : ℕ, f x * ((x : ℝ) + 1) * P (x + 1)
        - (k₁ * ∑' x : ℕ, (x : ℝ) * f x * P x + c * ∑' x : ℕ, f x * P x)) := by
    convert ((hg.hasSum.mul_left c).add (hh.hasSum.mul_left k₁)).sub
      ((h3.hasSum.mul_left k₁).add (h2.hasSum.mul_left c)) using 1
    funext x; simp only [xaME, g]; ring
  have B : HasSum (fun x : ℕ => P x * (c * (f (x + 1) - f x) + k₁ * x * (f (x - 1) - f x)))
      (c * ∑' x : ℕ, f (x + 1) * P x + k₁ * ∑' x : ℕ, (x : ℝ) * f (x - 1) * P x
        - (k₁ * ∑' x : ℕ, (x : ℝ) * f x * P x + c * ∑' x : ℕ, f x * P x)) := by
    convert ((h1.hasSum.mul_left c).add (h4.hasSum.mul_left k₁)).sub
      ((h3.hasSum.mul_left k₁).add (h2.hasSum.mul_left c)) using 1
    funext x; ring
  rw [A.tsum_eq, B.tsum_eq, hgs, hhs]

lemma descFactorial_succ_cast (x m : ℕ) :
    (x.descFactorial (m + 1) : ℝ) = ((x : ℝ) - m) * x.descFactorial m := by
  rcases lt_or_ge x m with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h, Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]
    simp
  · rw [Nat.descFactorial_succ]; push_cast [h]; ring

lemma mul_descFactorial_pred_cast (x n : ℕ) :
    (x : ℝ) * ((x - 1).descFactorial n : ℝ) = (x.descFactorial (n + 1) : ℝ) := by
  rcases x with _ | y
  · simp
  · rw [Nat.succ_descFactorial_succ]; push_cast; simp

/-- **(7.1.43)**, the factorial-moment hierarchy: for `f(x) = x(x-1)⋯(x-n+1)`,
`Σₓ f(x) (∂ₜP)(x) = n [k₂a ⟨x^{n-1}⟩_f - k₁ ⟨xⁿ⟩_f]` (written with `n + 1` in place of `n`). -/
theorem xa_factorial_moment_identity (c k₁ : ℝ) (P : ℕ → ℝ) (n : ℕ)
    (h1 : Summable fun x : ℕ => ((x + 1).descFactorial (n + 1) : ℝ) * P x)
    (h2 : Summable fun x : ℕ => (x.descFactorial (n + 1) : ℝ) * P x)
    (h3 : Summable fun x : ℕ => (x : ℝ) * (x.descFactorial (n + 1) : ℝ) * P x)
    (h4 : Summable fun x : ℕ => (x : ℝ) * ((x - 1).descFactorial (n + 1) : ℝ) * P x) :
    ∑' x : ℕ, (x.descFactorial (n + 1) : ℝ) * xaME c k₁ P x
      = (n + 1) * (c * ∑' x : ℕ, (x.descFactorial n : ℝ) * P x
          - k₁ * ∑' x : ℕ, (x.descFactorial (n + 1) : ℝ) * P x) := by
  rw [xaME_tsum_by_parts c k₁ P (fun x : ℕ => (x.descFactorial (n + 1) : ℝ)) h1 h2 h3 h4]
  have e1 : ∀ x : ℕ, ((x + 1).descFactorial (n + 1) : ℝ) - (x.descFactorial (n + 1) : ℝ)
      = (n + 1) * (x.descFactorial n : ℝ) := by
    intro x
    rw [Nat.succ_descFactorial_succ, descFactorial_succ_cast]; push_cast; ring
  have e2 : ∀ x : ℕ, (x : ℝ) * (((x - 1).descFactorial (n + 1) : ℝ)
      - (x.descFactorial (n + 1) : ℝ)) = -((n + 1) * (x.descFactorial (n + 1) : ℝ)) := by
    intro x
    rw [mul_sub, mul_descFactorial_pred_cast, descFactorial_succ_cast x (n + 1)]
    push_cast; ring
  have hd : Summable fun x : ℕ => (x.descFactorial n : ℝ) * P x := by
    have := (h1.sub h2).div_const (n + 1 : ℝ)
    refine this.congr fun x : ℕ => ?_
    rw [← sub_mul, e1]; field_simp
  have e : ∀ x, P x * (c * (((x + 1).descFactorial (n + 1) : ℝ) - (x.descFactorial (n + 1) : ℝ))
      + k₁ * x * (((x - 1).descFactorial (n + 1) : ℝ) - (x.descFactorial (n + 1) : ℝ)))
      = ((n + 1) * c) * ((x.descFactorial n : ℝ) * P x)
        - ((n + 1) * k₁) * ((x.descFactorial (n + 1) : ℝ) * P x) := by
    intro x
    rw [e1, mul_assoc k₁, e2]; ring
  simp_rw [e]
  rw [(hd.mul_left _).tsum_sub (h2.mul_left _), tsum_mul_left, tsum_mul_left]
  ring

/-- Moment identities for `f = 1, x, x²` (the `n = 0, 1, 2` cases of (7.1.41) at `s = 1`):
`Σ ∂ₜP = 0`, `Σ x ∂ₜP = k₂a M₀ - k₁ M₁`, `Σ x² ∂ₜP = k₂a(2M₁ + M₀) + k₁(M₁ - 2M₂)`. -/
theorem xa_moment_identities (c k₁ : ℝ) (P : ℕ → ℝ)
    (hP : ∀ k ≤ 3, Summable fun x : ℕ => (x : ℝ) ^ k * P x) :
    ∑' x : ℕ, xaME c k₁ P x = 0 ∧
    ∑' x : ℕ, (x : ℝ) * xaME c k₁ P x = c * (∑' x : ℕ, P x) - k₁ * ∑' x : ℕ, (x : ℝ) * P x ∧
    ∑' x : ℕ, (x : ℝ) ^ 2 * xaME c k₁ P x
      = c * (2 * (∑' x : ℕ, (x : ℝ) * P x) + ∑' x : ℕ, P x)
        + k₁ * ((∑' x : ℕ, (x : ℝ) * P x) - 2 * ∑' x : ℕ, (x : ℝ) ^ 2 * P x) := by
  have s0 : Summable fun x : ℕ => P x := by simpa using hP 0 (by norm_num)
  have s1 : Summable fun x : ℕ => (x : ℝ) * P x := by simpa using hP 1 (by norm_num)
  have s2 : Summable fun x : ℕ => (x : ℝ) ^ 2 * P x := hP 2 (by norm_num)
  have s3 : Summable fun x : ℕ => (x : ℝ) ^ 3 * P x := hP 3 (by norm_num)
  have hpred : ∀ x : ℕ, (x : ℝ) * ((x - 1 : ℕ) : ℝ) = (x : ℝ) ^ 2 - x := by
    intro x; rcases x with _ | y
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · have := xaME_tsum_by_parts c k₁ P (fun _ : ℕ => (1 : ℝ)) (by simpa using s0) (by simpa using s0)
      (by simpa using s1) (by simpa using s1)
    simpa using this
  · have := xaME_tsum_by_parts c k₁ P (fun x : ℕ => (x : ℝ))
      (by refine (s1.add s0).congr fun x : ℕ => ?_; push_cast; ring) s1
      (by refine s2.congr fun x : ℕ => ?_; ring)
      (by refine (s2.sub s1).congr fun x : ℕ => ?_; rw [hpred]; ring)
    rw [this]
    have e : ∀ x : ℕ, P x * (c * (((x + 1 : ℕ) : ℝ) - x) + k₁ * x * (((x - 1 : ℕ) : ℝ) - x))
        = c * P x - k₁ * ((x : ℝ) * P x) := by
      intro x; rw [mul_sub (k₁ * (x : ℝ)), mul_assoc k₁, hpred]; push_cast; ring
    simp_rw [e]
    rw [(s0.mul_left c).tsum_sub (s1.mul_left k₁), tsum_mul_left, tsum_mul_left]
  · have hpred2 : ∀ x : ℕ, (x : ℝ) * ((x - 1 : ℕ) : ℝ) ^ 2 = (x : ℝ) ^ 3 - 2 * x ^ 2 + x := by
      intro x; rcases x with _ | y
      · simp
      · simp only [Nat.add_sub_cancel]; push_cast; ring
    have := xaME_tsum_by_parts c k₁ P (fun x : ℕ => (x : ℝ) ^ 2)
      (by refine ((s2.add (s1.mul_left 2)).add s0).congr fun x : ℕ => ?_; push_cast; ring) s2
      (by refine s3.congr fun x : ℕ => ?_; ring)
      (by refine ((s3.sub (s2.mul_left 2)).add s1).congr fun x : ℕ => ?_; rw [hpred2]; ring)
    rw [this]
    have e : ∀ x : ℕ, P x * (c * (((x + 1 : ℕ) : ℝ) ^ 2 - (x : ℝ) ^ 2)
          + k₁ * x * (((x - 1 : ℕ) : ℝ) ^ 2 - (x : ℝ) ^ 2))
        = (2 * c + k₁) * ((x : ℝ) * P x) + c * P x - (2 * k₁) * ((x : ℝ) ^ 2 * P x) := by
      intro x; rw [mul_sub (k₁ * (x : ℝ)), mul_assoc k₁, hpred2]; push_cast; ring
    simp_rw [e]
    rw [((s1.mul_left _).add (s0.mul_left c)).tsum_sub (s2.mul_left _),
      (s1.mul_left _).tsum_add (s0.mul_left c), tsum_mul_left, tsum_mul_left, tsum_mul_left]
    ring

/-! ### Exact mean and variance of every solution -/

/-- **The exact mean and variance (7.1.38), (7.1.40) from the master equation.**  Let `P(t, x)`
solve (7.1.26) with `P(0, x) = δ_{x,N}` (7.1.34), with finite third moments, and suppose that
`d/dt` commutes with `Σₓ` for the moments of order `≤ 2` (`hswap`).  Then `Σ P = 1`,
`⟨x(t)⟩ = N e^{-k₁t} + (k₂a/k₁)(1 - e^{-k₁t})` and
`var x(t) = (N e^{-k₁t} + k₂a/k₁)(1 - e^{-k₁t})`. -/
theorem xa_mean_variance_exact (c k₁ : ℝ) (hk : k₁ ≠ 0) (N : ℕ) (P : ℝ → ℕ → ℝ)
    (hP0 : ∀ x, P 0 x = if x = N then 1 else 0)
    (hP : ∀ t, ∀ k ≤ 3, Summable fun x : ℕ => (x : ℝ) ^ k * P t x)
    (hswap : ∀ t, ∀ k ≤ 2, HasDerivAt (fun t => ∑' x : ℕ, (x : ℝ) ^ k * P t x)
      (∑' x : ℕ, (x : ℝ) ^ k * xaME c k₁ (P t) x) t) (t : ℝ) :
    ∑' x : ℕ, P t x = 1 ∧ ∑' x : ℕ, (x : ℝ) * P t x = xaMean c k₁ N t ∧
      ∑' x : ℕ, (x : ℝ) ^ 2 * P t x - (∑' x : ℕ, (x : ℝ) * P t x) ^ 2
        = (N * Real.exp (-k₁ * t) + c / k₁) * (1 - Real.exp (-k₁ * t)) := by
  set M : ℕ → ℝ → ℝ := fun k t => ∑' x : ℕ, (x : ℝ) ^ k * P t x with hM
  have hd : ∀ k ≤ 2, ∀ t, HasDerivAt (M k) (∑' x : ℕ, (x : ℝ) ^ k * xaME c k₁ (P t) x) t :=
    fun k hk t => hswap t k hk
  have hMinit : ∀ k, M k 0 = (N : ℝ) ^ k := by
    intro k; simp only [hM, hP0, mul_ite, mul_one, mul_zero]; rw [tsum_ite_eq]
  have e0 : ∀ t, M 0 t = ∑' x : ℕ, P t x := fun t => by simp [hM]
  have e1 : ∀ t, M 1 t = ∑' x : ℕ, (x : ℝ) * P t x := fun t => by simp [hM]
  -- normalisation
  have hM0 : M 0 = fun _ : ℝ => (1 : ℝ) := by
    refine linear_ode_unique (fun _ => 0) (fun _ => 0) continuous_const continuous_const _ _
      (fun t => ?_) (fun t => ?_) (by rw [hMinit]; simp)
    · have := hd 0 (by norm_num) t
      simp only [pow_zero, one_mul] at this
      rw [(xa_moment_identities c k₁ (P t) (hP t)).1] at this
      simpa using this
    · simpa using hasDerivAt_const t (1 : ℝ)
  -- mean
  have hmean : ∀ t, HasDerivAt (M 1) (-k₁ * M 1 t + c) t := by
    intro t
    have := hd 1 (by norm_num) t
    simp only [pow_one] at this
    rw [(xa_moment_identities c k₁ (P t) (hP t)).2.1, ← e0, ← e1, hM0] at this
    convert this using 1; ring
  have hM1 : M 1 = xaMean c k₁ N := by
    refine linear_ode_unique (fun _ => -k₁) (fun _ => c) continuous_const continuous_const _ _
      hmean (fun t => ?_) (by rw [hMinit, xaMean_zero]; simp)
    convert xaMean_hasDerivAt c k₁ N t hk using 1; ring
  -- variance
  set V : ℝ → ℝ := fun t => M 2 t - M 1 t ^ 2
  have hV : ∀ t, HasDerivAt V (-2 * k₁ * V t + (c + k₁ * xaMean c k₁ N t)) t := by
    intro t
    have h2 := hd 2 (by norm_num) t
    rw [(xa_moment_identities c k₁ (P t) (hP t)).2.2, ← e0, ← e1, hM0] at h2
    have := h2.sub ((hmean t).pow 2)
    convert this using 1
    simp only [V, hM1]
    push_cast
    ring
  set W : ℝ → ℝ := fun t => (N * Real.exp (-k₁ * t) + c / k₁) * (1 - Real.exp (-k₁ * t))
  have hW : ∀ t, HasDerivAt W (-2 * k₁ * W t + (c + k₁ * xaMean c k₁ N t)) t := by
    intro t
    have hp : HasDerivAt (fun t => Real.exp (-k₁ * t)) (-k₁ * Real.exp (-k₁ * t)) t := by
      simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-k₁)).exp
    have := ((hp.const_mul (N : ℝ)).add_const (c / k₁)).mul (hp.const_sub 1)
    convert this using 1
    simp only [W, xaMean]
    field_simp
    ring
  have hVW : V = W := by
    refine linear_ode_unique (fun _ => -2 * k₁) (fun t => c + k₁ * xaMean c k₁ N t)
      continuous_const ?_ V W hV hW ?_
    · exact continuous_const.add (continuous_const.mul
        (continuous_iff_continuousAt.2 fun t => (xaMean_hasDerivAt c k₁ N t hk).continuousAt))
    · simp only [V, W, hMinit]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← e0, hM0]
  · rw [← e1, hM1]
  · have := congrFun hVW t
    simp only [V, W, e1] at this
    simpa [hM] using this

end Gardiner
