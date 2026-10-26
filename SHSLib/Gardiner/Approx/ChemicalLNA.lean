/-
# The multivariate linear noise approximation

Gardiner, *Handbook of Stochastic Methods*, §7.5 (linearisation of the chemical Fokker–Planck
equation (7.5.31) about the deterministic solution) with the covariance evolution of §4.4.6 and
§4.4.9, (4.4.51), (4.4.83)–(4.4.85).

* `Gardiner.mvkGen`, `Gardiner.mlnaGen` — the fluctuation generator of van Kampen's expansion of a
  multivariate master equation and the linear-noise (time-dependent Ornstein–Uhlenbeck) generator.
* `Gardiner.mvkGen_sub_mlnaGen_le` — **explicit `O(Ω^{-1/2})` bound** for the difference of the two
  generators on test functions with bounded third derivatives.
* `Gardiner.lyapunov_iff`, `Gardiner.lna_cov_stationary` — the stationary covariance solves the
  Lyapunov equation `Aσ + σAᵀ = BBᵀ` (4.4.51).
* `Gardiner.mlna_exact`, `Gardiner.cme_lna_exact` — **exactness of the linear-noise mean and
  covariance** when drift and diffusion are affine (linear propensities), first for abstract
  closed moment equations, then for solutions of the chemical master equation (7.5.9).
* `Gardiner.xa_chem_affine` — `X ⇌ A` as a chemical network satisfies the affinity hypotheses.
-/
import SHSLib.Gardiner.Approx.ChemicalKM

open Finset Filter Topology Set
open scoped Nat

noncomputable section

namespace Gardiner

variable {n : ℕ}

section LNA

variable {κ : Type*} (s : Finset κ) (ψ : κ → (Fin n → ℝ) → ℝ) (v : κ → Fin n → ℝ)

/-- The generator of the fluctuation variable `z` in `x = Ωφ + Ω^{1/2} z` for a multivariate
master equation with extensive rates `Ω ψ_j(x/Ω)` (the multivariate (7.2.30)–(7.2.32)):
`Σ_j Ω ψ_j(φ + Ω^{-1/2}z) [f(z + Ω^{-1/2}v_j) - f(z)] - Ω^{1/2} Σₐ φ'ₐ ∂ₐf(z)`. -/
def mvkGen (Ω : ℝ) (phi dphi : Fin n → ℝ) (F₀ : (Fin n → ℝ) → ℝ)
    (F₁ : Fin n → (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : ℝ :=
  (∑ j ∈ s, Ω * ψ j (phi + (Real.sqrt Ω)⁻¹ • z) * (F₀ (z + (Real.sqrt Ω)⁻¹ • v j) - F₀ z))
    - Real.sqrt Ω * ∑ a, dphi a * F₁ a z

/-- The multivariate linear-noise generator `Σₐ (Jz)ₐ ∂ₐf + ½ Σ_{ab} B̃_ab ∂ₐ∂_bf`, the generator of
the time-dependent Ornstein–Uhlenbeck process (4.4.83) with `-A = J = ∂Ã/∂x(φ)` and
`BBᵀ = B̃(φ)`. -/
def mlnaGen (J Bt : Fin n → Fin n → ℝ) (F₁ : Fin n → (Fin n → ℝ) → ℝ)
    (F₂ : Fin n → Fin n → (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ a, (∑ b, J a b * z b) * F₁ a z + (1 / 2) * ∑ a, ∑ b, Bt a b * F₂ a b z

/-- **The multivariate linear noise approximation with an explicit error.**  Let `φ` lie on
the deterministic trajectory `φ' = Ã(φ)` (so the transport term uses `φ'ₐ = Ãₐ(φ)`), let
`J` be the Jacobian of the intensive drift `Ã` at `φ` in the sense that
`|Ãₐ(φ + h) - Ãₐ(φ) - (Jh)ₐ| ≤ K ‖h‖₁²` at `h = Ω^{-1/2}z`, and let `B̃` vary by at most `L‖h‖₁`.
Then on test functions with third partial derivatives bounded by `M`, the generator of the
fluctuations differs from the linear-noise generator by
`Ω^{-1/2} [K‖z‖₁² Σₐ|∂ₐf| + (L/2)‖z‖₁ Σ_{ab}|∂ₐ∂_bf| + (M/6) Σ_j |ψ_j| ‖v_j‖₁³]`. -/
theorem mvkGen_sub_mlnaGen_le {Ω : ℝ} (hΩ : 0 < Ω) (phi z : Fin n → ℝ)
    {F₀ F₁ F₂ F₃} (hT : Tower3 (n := n) F₀ F₁ F₂ F₃) (M : ℝ)
    (hM : ∀ a b c y, |F₃ a b c y| ≤ M) (J : Fin n → Fin n → ℝ) (K L : ℝ)
    (hJ : ∀ a, |mjDrift s ψ v a (phi + (Real.sqrt Ω)⁻¹ • z) - mjDrift s ψ v a phi
        - ∑ b, J a b * ((Real.sqrt Ω)⁻¹ * z b)| ≤ K * ((Real.sqrt Ω)⁻¹ * ∑ b, |z b|) ^ 2)
    (hL : ∀ a b, |mjDiff s ψ v a b (phi + (Real.sqrt Ω)⁻¹ • z) - mjDiff s ψ v a b phi|
        ≤ L * ((Real.sqrt Ω)⁻¹ * ∑ b, |z b|)) :
    |mvkGen s ψ v Ω phi (fun a => mjDrift s ψ v a phi) F₀ F₁ z
        - mlnaGen J (fun a b => mjDiff s ψ v a b phi) F₁ F₂ z|
      ≤ (Real.sqrt Ω)⁻¹ * (K * (∑ b, |z b|) ^ 2 * ∑ a, |F₁ a z|
          + L / 2 * (∑ b, |z b|) * ∑ a, ∑ b, |F₂ a b z|
          + M / 6 * mjAbs3 s ψ v (phi + (Real.sqrt Ω)⁻¹ • z)) := by
  have hs0 : 0 < Real.sqrt Ω := Real.sqrt_pos.2 hΩ
  have hs : Real.sqrt Ω ^ 2 = Ω := Real.sq_sqrt hΩ.le
  set ε := (Real.sqrt Ω)⁻¹ with hε
  have hε0 : 0 < ε := inv_pos.2 hs0
  have h4 : Real.sqrt Ω * ε = 1 := by rw [hε]; field_simp
  have h1 : Ω * ε = Real.sqrt Ω := by nth_rewrite 1 [← hs]; rw [sq, mul_assoc, h4, mul_one]
  have h2 : Ω * ε ^ 2 = 1 := by nth_rewrite 1 [← hs]; rw [← mul_pow, h4, one_pow]
  have h3 : Ω * ε ^ 3 = ε := by rw [show Ω * ε ^ 3 = (Ω * ε ^ 2) * ε by ring, h2, one_mul]
  set y := phi + ε • z
  set c' : κ → (Fin n → ℝ) → ℝ := fun j _ => Ω * ψ j y
  set v' : κ → Fin n → ℝ := fun j => ε • v j
  have key := mjGen_sub_mjKM_le s c' v' hT M hM z
  have hDr : ∀ a, mjDrift s c' v' a z = Real.sqrt Ω * mjDrift s ψ v a y := by
    intro a; simp only [mjDrift, c', v', Pi.smul_apply, smul_eq_mul, mul_sum, ← h1]
    exact sum_congr rfl fun j _ => by ring
  have hDf : ∀ a b, mjDiff s c' v' a b z = mjDiff s ψ v a b y := by
    intro a b
    simp only [mjDiff, c', v', Pi.smul_apply, smul_eq_mul]
    refine sum_congr rfl fun j _ => ?_
    linear_combination (ψ j y * v j a * v j b) * h2
  have hAb : mjAbs3 s c' v' z = ε * mjAbs3 s ψ v y := by
    simp only [mjAbs3, c', v', Pi.smul_apply, smul_eq_mul, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [abs_mul, abs_of_pos hΩ, abs_of_pos hε0, ← mul_sum]
    linear_combination (|ψ j y| * (∑ a, |v j a|) ^ 3) * h3
  have hG : mjGen s c' v' F₀ z
      = ∑ j ∈ s, Ω * ψ j y * (F₀ (z + ε • v j) - F₀ z) := rfl
  -- the two linearisation errors
  have eA : ∀ a, Real.sqrt Ω * mjDrift s ψ v a y - Real.sqrt Ω * mjDrift s ψ v a phi
      - ∑ b, J a b * z b = Real.sqrt Ω * (mjDrift s ψ v a y - mjDrift s ψ v a phi
        - ∑ b, J a b * (ε * z b)) := by
    intro a
    rw [mul_sub, mul_sub, mul_sum]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    linear_combination (-(J a b * z b)) * h4
  have hsplit : mvkGen s ψ v Ω phi (fun a => mjDrift s ψ v a phi) F₀ F₁ z
        - mlnaGen J (fun a b => mjDiff s ψ v a b phi) F₁ F₂ z
      = (mjGen s c' v' F₀ z - mjKM s c' v' F₁ F₂ z)
        + ∑ a, (Real.sqrt Ω * (mjDrift s ψ v a y - mjDrift s ψ v a phi
            - ∑ b, J a b * (ε * z b))) * F₁ a z
        + (1 / 2) * ∑ a, ∑ b, (mjDiff s ψ v a b y - mjDiff s ψ v a b phi) * F₂ a b z := by
    have hG' : (∑ j ∈ s, Ω * ψ j (phi + (Real.sqrt Ω)⁻¹ • z)
        * (F₀ (z + (Real.sqrt Ω)⁻¹ • v j) - F₀ z)) = mjGen s c' v' F₀ z := rfl
    simp only [← eA]
    simp only [mvkGen]
    rw [hG']
    simp only [mlnaGen, mjKM, hDr, hDf]
    simp only [sub_mul, sum_sub_distrib, mul_sub, mul_sum]
    ring_nf
  rw [hsplit]
  have bA : ∀ a, |Real.sqrt Ω * (mjDrift s ψ v a y - mjDrift s ψ v a phi
      - ∑ b, J a b * (ε * z b))| ≤ ε * (K * (∑ b, |z b|) ^ 2) := by
    intro a
    rw [abs_mul, abs_of_pos hs0]
    calc Real.sqrt Ω * |mjDrift s ψ v a y - mjDrift s ψ v a phi - ∑ b, J a b * (ε * z b)|
        ≤ Real.sqrt Ω * (K * (ε * ∑ b, |z b|) ^ 2) := mul_le_mul_of_nonneg_left (hJ a) hs0.le
      _ = (Real.sqrt Ω * ε) * ε * (K * (∑ b, |z b|) ^ 2) := by ring
      _ = _ := by rw [h4, one_mul]
  have T1 : |∑ a, (Real.sqrt Ω * (mjDrift s ψ v a y - mjDrift s ψ v a phi
      - ∑ b, J a b * (ε * z b))) * F₁ a z| ≤ ε * (K * (∑ b, |z b|) ^ 2 * ∑ a, |F₁ a z|) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun a _ => ?_
    rw [abs_mul]
    calc _ ≤ ε * (K * (∑ b, |z b|) ^ 2) * |F₁ a z| :=
          mul_le_mul_of_nonneg_right (bA a) (abs_nonneg _)
      _ = _ := by ring
  have T2 : |(1 / 2) * ∑ a, ∑ b, (mjDiff s ψ v a b y - mjDiff s ψ v a b phi) * F₂ a b z|
      ≤ ε * (L / 2 * (∑ b, |z b|) * ∑ a, ∑ b, |F₂ a b z|) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : |∑ a, ∑ b, (mjDiff s ψ v a b y - mjDiff s ψ v a b phi) * F₂ a b z|
        ≤ ∑ a, ∑ b, L * (ε * ∑ c, |z c|) * |F₂ a b z| := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hL a b) (abs_nonneg _)
    calc 1 / 2 * |∑ a, ∑ b, (mjDiff s ψ v a b y - mjDiff s ψ v a b phi) * F₂ a b z|
        ≤ 1 / 2 * ∑ a, ∑ b, L * (ε * ∑ c, |z c|) * |F₂ a b z| := by gcongr
      _ = 1 / 2 * (L * (ε * ∑ c, |z c|) * ∑ a, ∑ b, |F₂ a b z|) := by
          simp only [mul_sum]
      _ = _ := by ring
  have T0 : |mjGen s c' v' F₀ z - mjKM s c' v' F₁ F₂ z| ≤ ε * (M / 6 * mjAbs3 s ψ v y) := by
    calc _ ≤ M / 6 * mjAbs3 s c' v' z := key
      _ = _ := by rw [hAb]; ring
  calc _ ≤ |mjGen s c' v' F₀ z - mjKM s c' v' F₁ F₂ z|
        + |∑ a, (Real.sqrt Ω * (mjDrift s ψ v a y - mjDrift s ψ v a phi
            - ∑ b, J a b * (ε * z b))) * F₁ a z|
        + |(1 / 2) * ∑ a, ∑ b, (mjDiff s ψ v a b y - mjDiff s ψ v a b phi) * F₂ a b z| :=
        abs_add_three _ _ _
    _ ≤ _ := by linarith

end LNA

/-! ### Linear-noise moments: mean, covariance, Lyapunov equation (4.4.51), (4.4.84)–(4.4.85) -/

/-- Uniqueness for linear ODEs `y' = L y + d(t)` in a normed space. -/
theorem vec_linear_ode_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (d : ℝ → E) (y₁ y₂ : ℝ → E)
    (h₁ : ∀ t, HasDerivAt y₁ (L (y₁ t) + d t) t) (h₂ : ∀ t, HasDerivAt y₂ (L (y₂ t) + d t) t)
    (h0 : y₁ 0 = y₂ 0) : y₁ = y₂ :=
  ODE_solution_unique_univ (v := fun t x => L x + d t) (s := fun _ => univ) (K := ‖L‖₊)
    (fun t => (LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_add_right]; exact L.lipschitz.dist_le_mul x y).lipschitzOnWith)
    (fun t => ⟨h₁ t, trivial⟩) (fun t => ⟨h₂ t, trivial⟩) h0

/-- The linear map `m ↦ J m`. -/
def meanLin (J : Fin n → Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun m a => ∑ c, J a c * m c
      map_add' := fun x y => by funext a; simp [mul_add, sum_add_distrib]
      map_smul' := fun r x => by funext a; simp [mul_sum]; exact sum_congr rfl fun c _ => by ring }

/-- The linear map `C ↦ J C + C Jᵀ` of the covariance equation (4.4.85), differential form. -/
def covLin (J : Fin n → Fin n → ℝ) : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun C a b => ∑ c, J a c * C c b + ∑ c, C a c * J b c
      map_add' := fun x y => by
        funext a b; simp only [Pi.add_apply, mul_add, add_mul, sum_add_distrib]; ring
      map_smul' := fun r x => by
        funext a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, mul_sum]
        congr 1 <;> exact sum_congr rfl fun c _ => by ring }

@[simp] lemma meanLin_apply (J : Fin n → Fin n → ℝ) (m : Fin n → ℝ) (a : Fin n) :
    meanLin J m a = ∑ c, J a c * m c := rfl

@[simp] lemma covLin_apply (J C : Fin n → Fin n → ℝ) (a b : Fin n) :
    covLin J C a b = ∑ c, J a c * C c b + ∑ c, C a c * J b c := rfl

/-- **The Lyapunov equation (4.4.51)**: a constant covariance `σ` solves the linear-noise
covariance equation `Σ' = JΣ + ΣJᵀ + B̃` iff `Aσ + σAᵀ = B̃` with `A = -J` (here `B̃ = BBᵀ`). -/
theorem lyapunov_iff (J Bt σ : Fin n → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => σ) (covLin J σ + Bt) t ↔
      ∀ a b, ∑ c, (-J a c) * σ c b + ∑ c, σ a c * (-J b c) = Bt a b := by
  constructor
  · intro h a b
    have h0 := h.unique (hasDerivAt_const t σ)
    have := congrFun (congrFun h0 a) b
    simp only [Pi.add_apply, covLin_apply, Pi.zero_apply] at this
    simp only [neg_mul, mul_neg, sum_neg_distrib]
    linarith
  · intro h
    have : covLin J σ + Bt = 0 := by
      funext a b
      have := h a b
      simp only [neg_mul, mul_neg, sum_neg_distrib] at this
      simp only [Pi.add_apply, covLin_apply, Pi.zero_apply]
      linarith
    rw [this]; exact hasDerivAt_const t σ

/-- A linear-noise covariance started at a solution of the Lyapunov equation stays there. -/
theorem lna_cov_stationary (J Bt σ : Fin n → Fin n → ℝ) (Sig : ℝ → Fin n → Fin n → ℝ)
    (hSig : ∀ t, HasDerivAt Sig (covLin J (Sig t) + Bt) t) (h0 : Sig 0 = σ)
    (hly : ∀ a b, ∑ c, (-J a c) * σ c b + ∑ c, σ a c * (-J b c) = Bt a b) :
    ∀ t, Sig t = σ := fun t => congrFun (vec_linear_ode_unique (covLin J) (fun _ => Bt) Sig
    (fun _ => σ) hSig (fun t => (lyapunov_iff J Bt σ t).2 hly) h0) t

/-- **Exactness of the multivariate linear noise approximation for linear propensities.**
Suppose the drift and diffusion of the master equation are affine, `Aₐ(x) = αₐ + Σ_c J_ac x_c`,
`B_ab(x) = β_ab + Σ_c γ_abc x_c`, so that the exact mean `m` and second moments `S` obey the
closed equations `m' = α + J m` and `S'_ab = ⟨x_a A_b + x_b A_a + B_ab⟩` (as for the chemical master
equation, `Gardiner.cme_mean`, `Gardiner.cme_second_moment`).  Let `φ` solve the deterministic
equation `φ' = α/Ω + Jφ` and `Σ` the linear-noise covariance equation (4.4.85)
`Σ' = JΣ + ΣJᵀ + B̃(φ)`, `B̃(φ) = β/Ω + Σ_c γ φ_c`.  If initially `m = Ωφ` and
`S - m mᵀ = ΩΣ`, then for all times the exact mean is `Ωφ(t)` and the exact covariance is
`ΩΣ(t)`. -/
theorem mlna_exact (Ω : ℝ) (hΩ : Ω ≠ 0) (α : Fin n → ℝ) (J β : Fin n → Fin n → ℝ)
    (γ : Fin n → Fin n → Fin n → ℝ) (m : ℝ → Fin n → ℝ) (S : ℝ → Fin n → Fin n → ℝ)
    (phi : ℝ → Fin n → ℝ) (Sig : ℝ → Fin n → Fin n → ℝ)
    (hm : ∀ t a, HasDerivAt (fun t => m t a) (α a + ∑ c, J a c * m t c) t)
    (hS : ∀ t a b, HasDerivAt (fun t => S t a b)
      ((α b * m t a + ∑ c, J b c * S t a c) + (α a * m t b + ∑ c, J a c * S t c b)
        + (β a b + ∑ c, γ a b c * m t c)) t)
    (hphi : ∀ t a, HasDerivAt (fun t => phi t a) (α a / Ω + ∑ c, J a c * phi t c) t)
    (hSig : ∀ t a b, HasDerivAt (fun t => Sig t a b)
      (∑ c, J a c * Sig t c b + ∑ c, Sig t a c * J b c + (β a b / Ω + ∑ c, γ a b c * phi t c)) t)
    (hm0 : ∀ a, m 0 a = Ω * phi 0 a) (hC0 : ∀ a b, S 0 a b - m 0 a * m 0 b = Ω * Sig 0 a b) :
    ∀ t a b, m t a = Ω * phi t a ∧ S t a b - m t a * m t b = Ω * Sig t a b := by
  -- the mean
  have hmeq : m = fun t a => Ω * phi t a := by
    refine vec_linear_ode_unique (meanLin J) (fun _ => α) m (fun t a => Ω * phi t a)
      (fun t => ?_) (fun t => ?_) (funext hm0)
    · refine hasDerivAt_pi.2 fun a => ?_
      convert hm t a using 1
      simp only [Pi.add_apply, meanLin_apply]; ring
    · refine hasDerivAt_pi.2 fun a => ?_
      convert (hphi t a).const_mul Ω using 1
      simp only [Pi.add_apply, meanLin_apply]
      rw [mul_add, mul_div_cancel₀ _ hΩ, mul_sum, add_comm]
      congr 1
      exact sum_congr rfl fun c _ => by ring
  have hmt : ∀ t a, m t a = Ω * phi t a := fun t a => congrFun (congrFun hmeq t) a
  -- the covariance
  set C : ℝ → Fin n → Fin n → ℝ := fun t a b => S t a b - m t a * m t b
  set d : ℝ → Fin n → Fin n → ℝ := fun t a b => β a b + ∑ c, γ a b c * m t c
  have hCeq : C = fun t a b => Ω * Sig t a b := by
    refine vec_linear_ode_unique (covLin J) d C (fun t a b => Ω * Sig t a b)
      (fun t => ?_) (fun t => ?_) (funext fun a => funext fun b => hC0 a b)
    · refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
      have := (hS t a b).sub ((hm t a).mul (hm t b))
      convert this using 1
      have k1 : ∑ c, J a c * C t c b = ∑ c, J a c * S t c b - (∑ c, J a c * m t c) * m t b := by
        rw [sum_mul, ← sum_sub_distrib]; exact sum_congr rfl fun c _ => by simp only [C]; ring
      have k2 : ∑ c, C t a c * J b c = ∑ c, J b c * S t a c - m t a * ∑ c, J b c * m t c := by
        rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun c _ => by simp only [C]; ring
      simp only [Pi.add_apply, covLin_apply, k1, k2, d]
      ring
    · refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
      convert (hSig t a b).const_mul Ω using 1
      simp only [Pi.add_apply, covLin_apply, d, hmt]
      rw [mul_add, mul_add, mul_add, mul_div_cancel₀ _ hΩ, mul_sum, mul_sum, mul_sum]
      refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (congrArg (β a b + ·) ?_) <;>
        exact sum_congr rfl fun c _ => by ring
  intro t a b
  exact ⟨hmt t a, congrFun (congrFun (congrFun hCeq t) a) b⟩

/-! ### From the chemical master equation to exactness -/

lemma tsum_mul_affine {X : Type*} (P : X → ℝ) (u : Fin n → X → ℝ) (α : ℝ) (J : Fin n → ℝ)
    (hP : Summable P) (hu : ∀ c, Summable fun x => u c x * P x) :
    ∑' x, P x * (α + ∑ c, J c * u c x) = α * ∑' x, P x + ∑ c, J c * ∑' x, u c x * P x := by
  have h := (hP.hasSum.mul_left α).add
    (hasSum_sum (s := Finset.univ) fun c _ => ((hu c).hasSum.mul_left (J c)))
  refine (HasSum.tsum_eq ?_)
  convert h using 1
  funext x
  simp only [mul_add, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun c _ => by ring

variable {ι : Type*} [Fintype ι] (NA MA : ι → Fin n → ℕ) (kp km : ι → ℝ)

/-- **The linear noise approximation is exact for the chemical master equation with linear
propensities.**  Let `P(t, ·)` be a normalised solution of (7.5.9) whose drift and diffusion
(7.5.32) are affine on the lattice, `Aₐ(x) = αₐ + Σ_c J_ac x_c` and
`B_ab(x) = β_ab + Σ_c γ_abc x_c` (e.g. all reactions of first order).  Assume finite second
moments, the summability required by the duality `tsum_mul_latME`, and that `d/dt` commutes with
`Σₓ` for the first and second moments (`hswap₁`, `hswap₂`).  If the linear-noise mean `Ωφ` and
covariance `ΩΣ` agree with the exact ones at `t = 0`, they agree for all `t`. -/
theorem cme_lna_exact (Ω : ℝ) (hΩ : Ω ≠ 0) (α : Fin n → ℝ) (J β : Fin n → Fin n → ℝ)
    (γ : Fin n → Fin n → Fin n → ℝ)
    (hA : ∀ a x, chemDrift NA MA kp km a (castZ x) = α a + ∑ c, J a c * (x c : ℝ))
    (hB : ∀ a b x, chemDiff NA MA kp km a b (castZ x) = β a b + ∑ c, γ a b c * (x c : ℝ))
    (P : ℝ → (Fin n → ℤ) → ℝ) (hnorm : ∀ t, ∑' x, P t x = 1)
    (hs0 : ∀ t, Summable (P t)) (hs1 : ∀ t c, Summable fun x => (x c : ℝ) * P t x)
    (hs2 : ∀ t a c, Summable fun x => (x a : ℝ) * (x c : ℝ) * P t x)
    (hd1 : ∀ t a, ∀ p : ι × Bool, Summable fun x : Fin n → ℤ =>
      ((x + chemJump NA MA p) a : ℝ) * (chemRate NA MA kp km p x * P t x))
    (hd2 : ∀ t a, ∀ p : ι × Bool, Summable fun x : Fin n → ℤ =>
      (x a : ℝ) * (chemRate NA MA kp km p x * P t x))
    (hd3 : ∀ t a b, ∀ p : ι × Bool, Summable fun x : Fin n → ℤ =>
      ((x + chemJump NA MA p) a : ℝ) * ((x + chemJump NA MA p) b : ℝ)
        * (chemRate NA MA kp km p x * P t x))
    (hd4 : ∀ t a b, ∀ p : ι × Bool, Summable fun x : Fin n → ℤ =>
      (x a : ℝ) * (x b : ℝ) * (chemRate NA MA kp km p x * P t x))
    (hswap₁ : ∀ t a, HasDerivAt (fun t => ∑' x, (x a : ℝ) * P t x)
      (∑' x, (x a : ℝ) * cme NA MA kp km (P t) x) t)
    (hswap₂ : ∀ t a b, HasDerivAt (fun t => ∑' x, (x a : ℝ) * (x b : ℝ) * P t x)
      (∑' x, (x a : ℝ) * (x b : ℝ) * cme NA MA kp km (P t) x) t)
    (phi : ℝ → Fin n → ℝ) (Sig : ℝ → Fin n → Fin n → ℝ)
    (hphi : ∀ t a, HasDerivAt (fun t => phi t a) (α a / Ω + ∑ c, J a c * phi t c) t)
    (hSig : ∀ t a b, HasDerivAt (fun t => Sig t a b)
      (∑ c, J a c * Sig t c b + ∑ c, Sig t a c * J b c + (β a b / Ω + ∑ c, γ a b c * phi t c)) t)
    (hm0 : ∀ a, ∑' x, (x a : ℝ) * P 0 x = Ω * phi 0 a)
    (hC0 : ∀ a b, ∑' x, (x a : ℝ) * (x b : ℝ) * P 0 x
      - (∑' x, (x a : ℝ) * P 0 x) * (∑' x, (x b : ℝ) * P 0 x) = Ω * Sig 0 a b) (t : ℝ) (a b : Fin n) :
    ∑' x, (x a : ℝ) * P t x = Ω * phi t a ∧
      ∑' x, (x a : ℝ) * (x b : ℝ) * P t x
        - (∑' x, (x a : ℝ) * P t x) * (∑' x, (x b : ℝ) * P t x) = Ω * Sig t a b := by
  set m : ℝ → Fin n → ℝ := fun t a => ∑' x, (x a : ℝ) * P t x
  set S : ℝ → Fin n → Fin n → ℝ := fun t a b => ∑' x, (x a : ℝ) * (x b : ℝ) * P t x
  have hm : ∀ t a, HasDerivAt (fun t => m t a) (α a + ∑ c, J a c * m t c) t := by
    intro t a
    have h := hswap₁ t a
    rw [cme_mean NA MA kp km (P t) a (hd1 t a) (hd2 t a)] at h
    simp_rw [hA] at h
    rw [tsum_mul_affine (P t) (fun c x => (x c : ℝ)) (α a) (J a) (hs0 t) (hs1 t), hnorm t,
      mul_one] at h
    exact h
  have hS : ∀ t a b, HasDerivAt (fun t => S t a b)
      ((α b * m t a + ∑ c, J b c * S t a c) + (α a * m t b + ∑ c, J a c * S t c b)
        + (β a b + ∑ c, γ a b c * m t c)) t := by
    intro t a b
    have h := hswap₂ t a b
    rw [cme_second_moment NA MA kp km (P t) a b (hd3 t a b) (hd4 t a b)] at h
    simp_rw [hA, hB] at h
    have H := (((hs1 t a).hasSum.mul_left (α b)).add (hasSum_sum (s := Finset.univ)
      fun c _ => (hs2 t a c).hasSum.mul_left (J b c))).add
      (((hs1 t b).hasSum.mul_left (α a)).add (hasSum_sum (s := Finset.univ)
      fun c _ => (hs2 t c b).hasSum.mul_left (J a c))) |>.add
      (((hs0 t).hasSum.mul_left (β a b)).add (hasSum_sum (s := Finset.univ)
      fun c _ => (hs1 t c).hasSum.mul_left (γ a b c)))
    have e : ∑' x, P t x * ((x a : ℝ) * (α b + ∑ c, J b c * (x c : ℝ))
        + (x b : ℝ) * (α a + ∑ c, J a c * (x c : ℝ)) + (β a b + ∑ c, γ a b c * (x c : ℝ)))
        = (α b * m t a + ∑ c, J b c * S t a c) + (α a * m t b + ∑ c, J a c * S t c b)
          + (β a b + ∑ c, γ a b c * m t c) := by
      refine HasSum.tsum_eq ?_
      convert H using 1
      case h.e'_6 => simp only [m, S, hnorm t, mul_one]
      funext x
      simp only [mul_add, mul_sum]
      ring_nf
    rw [e] at h
    exact h
  have := mlna_exact Ω hΩ α J β γ m S phi Sig hm hS hphi hSig hm0 hC0 t a b
  exact this

/-- `X ⇌ A` as a chemical network (`n = 1`, one reaction `∅ ⇌ X` with `k⁺ = k₂a`, `k⁻ = k₁`):
its drift and diffusion (7.5.32) are affine, `A = k₂a - k₁x`, `B = k₂a + k₁x`, so
`cme_lna_exact` applies. -/
theorem xa_chem_affine (c k₁ : ℝ) (x : Fin 1 → ℤ) :
    chemDrift (ι := Unit) (fun _ _ => 0) (fun _ _ => 1) (fun _ => c) (fun _ => k₁) 0 (castZ x)
        = c + (-k₁) * (x 0 : ℝ) ∧
      chemDiff (ι := Unit) (fun _ _ => 0) (fun _ _ => 1) (fun _ => c) (fun _ => k₁) 0 0 (castZ x)
        = c + k₁ * (x 0 : ℝ) := by
  simp [chemDrift, chemDiff, stoich, tplus, tminus, propPoly, castZ]
  ring

end Gardiner
