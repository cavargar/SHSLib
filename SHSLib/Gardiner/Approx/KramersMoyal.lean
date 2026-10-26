/-
# Jump-process approximation of a diffusion and the Kramers–Moyal expansion

Gardiner, *Handbook of Stochastic Methods*, §7.2.1 and §7.2.2.

The master equation (7.2.7) is studied through its *backward generator*
`(L f)(x) = ∫ dx' W(x'|x) [f(x') - f(x)]`, which is the operator appearing in the
derivation (7.2.6) "carried out as in Sect. 3.4": `∂_t ⟨f(z)⟩ = ⟨(L f)(z)⟩`.
The Kramers–Moyal expansion (7.2.25) is the adjoint of the Taylor expansion of `L f`
in powers of the jump, `L f ≈ Σ_{k ≥ 1} αₖ(x) f⁽ᵏ⁾(x)/k!`, where the `αₖ` are the jump
moments (7.2.26).

Main results:

* `Gardiner.jumpGen_sub_kmGen_le`, `Gardiner.finJumpGen_sub_finKM_le`:
  **the Kramers–Moyal truncation error in terms of the next jump moment**,
  `|L f - Σ_{k=1}^{n} αₖ f⁽ᵏ⁾/k!| ≤ ‖f⁽ⁿ⁺¹⁾‖_∞/(n+1)! · ∫ |x'-x|ⁿ⁺¹ W(x'|x) dx'`,
  for a jump density and for a finite set of jumps respectively.
* `Gardiner.integral_mul_scaledW`: the change of variables behind (7.2.4).
* `Gardiner.scaledW_moment_zero/one/two`: the jump moments (7.2.4) of the scaled kernel
  (7.2.1).  The second moment is `∫ y²Φ + δ A² Q`; the text's `α₂ = ∫ y² Φ` holds only
  to leading order in `δ` (it is exact when `A = 0`).
* `Gardiner.scaled_jumpGen_rate`, `Gardiner.scaled_jumpGen_tendsto`:
  **(7.2.6) with an explicit rate**, `O(√δ)`.
* `Gardiner.scaledW_tendsto_zero`: (7.2.5).
* `Gardiner.scaledW_jumpMoment_tendsto_zero`: (7.2.27) — the higher Kramers–Moyal
  coefficients `αₙ`, `n ≥ 3`, vanish as `δ → 0`.
* Examples (7.2.9)–(7.2.18): the random walk, the Poisson process (no Fokker–Planck
  limit), and the birth–death approximation (7.2.16) of a diffusion, each with an
  explicit rate.
* `Gardiner.km_master_change_of_variables`: (7.2.22)–(7.2.23).
-/
import SHSLib.Gardiner.Approx.Calculus

open MeasureTheory Filter Topology Set
open scoped BigOperators Nat

noncomputable section

namespace Gardiner

lemma taylorTower_eq_add (D : ℕ → ℝ → ℝ) (n : ℕ) (x h : ℝ) :
    taylorTower D n x h
      = D 0 x + ∑ k ∈ Finset.range n, D (k + 1) x * h ^ (k + 1) / ((k + 1)! : ℝ) := by
  unfold taylorTower
  rw [Finset.sum_range_succ', add_comm]
  simp

/-! ### Finitely many jumps -/

section Finite

variable {ι : Type*} (s : Finset ι) (r : ι → ℝ) (c : ι → ℝ → ℝ)

/-- The backward generator of a master equation with finitely many jumps
`x → x + r j`, occurring at rate `c j x`: `Σ_j c_j(x) [f(x + r_j) - f(x)]`. -/
def finJumpGen (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑ j ∈ s, c j x * (f (x + r j) - f x)

/-- The jump moments (7.2.26) `αₖ(x) = Σ_j c_j(x) r_jᵏ` of a finite jump kernel. -/
def finJumpMoment (x : ℝ) (k : ℕ) : ℝ := ∑ j ∈ s, c j x * r j ^ k

/-- The absolute jump moments `Σ_j |c_j(x)| |r_j|ᵏ`. -/
def finAbsJumpMoment (x : ℝ) (k : ℕ) : ℝ := ∑ j ∈ s, |c j x| * |r j| ^ k

/-- The Kramers–Moyal operator truncated at order `n`, in backward form:
`Σ_{k=1}^{n} αₖ(x) f⁽ᵏ⁾(x)/k!`, where `D k` is the `k`-th derivative of `f`. -/
def finKM (D : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, finJumpMoment s r c x (k + 1) * D (k + 1) x / ((k + 1)! : ℝ)

lemma finJumpGen_sub_finKM_eq (D : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) :
    finJumpGen s r c (D 0) x - finKM s r c D n x
      = ∑ j ∈ s, c j x * (D 0 (x + r j) - taylorTower D n x (r j)) := by
  simp only [finJumpGen, finKM, finJumpMoment, taylorTower_eq_add, Finset.sum_mul,
    Finset.sum_div]
  rw [Finset.sum_comm (s := Finset.range n), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_sub, mul_sub, mul_add, Finset.mul_sum]
  have : ∀ k ∈ Finset.range n, c j x * r j ^ (k + 1) * D (k + 1) x / ((k + 1)! : ℝ)
      = c j x * (D (k + 1) x * r j ^ (k + 1) / ((k + 1)! : ℝ)) := fun k _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

/-- **Kramers–Moyal truncation error, finitely many jumps.** If `f = D 0` has derivatives
`D 1, …, D (n+1)` with `|f⁽ⁿ⁺¹⁾| ≤ M`, then the master-equation generator differs from the
order-`n` Kramers–Moyal operator by at most `M/(n+1)!` times the `(n+1)`-st absolute jump
moment. -/
theorem finJumpGen_sub_finKM_le (D : ℕ → ℝ → ℝ) (n : ℕ) (x M : ℝ)
    (hD : ∀ k ≤ n, ∀ y, HasDerivAt (D k) (D (k + 1) y) y) (hM : ∀ y, |D (n + 1) y| ≤ M) :
    |finJumpGen s r c (D 0) x - finKM s r c D n x|
      ≤ M / ((n + 1)! : ℝ) * finAbsJumpMoment s r c x (n + 1) := by
  rw [finJumpGen_sub_finKM_eq, finAbsJumpMoment, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have := taylor_tower_bound n D x (r j) M hD (fun t _ => hM _)
  calc |c j x| * |D 0 (x + r j) - taylorTower D n x (r j)|
      ≤ |c j x| * (M * |r j| ^ (n + 1) / ((n + 1)! : ℝ)) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = _ := by ring

end Finite

/-! ### Jump densities -/

section Density

variable (ν : Measure ℝ) (w : ℝ → ℝ)

/-- The backward generator `∫ [f(x') - f(x)] w(x') ν(dx')` of a master equation whose
jump kernel `W(x'|x) dx'` is `w(x') ν(dx')` (the starting point `x` being fixed). -/
def jumpGen (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ x', (f x' - f x) * w x' ∂ν

/-- (7.2.26): the jump moments `αₖ(x) = ∫ (x' - x)ᵏ W(x'|x) dx'`. -/
def jumpMoment (x : ℝ) (k : ℕ) : ℝ := ∫ x', (x' - x) ^ k * w x' ∂ν

/-- The absolute jump moments `∫ |x' - x|ᵏ W(x'|x) dx'`. -/
def absJumpMoment (x : ℝ) (k : ℕ) : ℝ := ∫ x', |x' - x| ^ k * w x' ∂ν

/-- The Kramers–Moyal operator truncated at order `n` (backward form). -/
def kmGen (D : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, jumpMoment ν w x (k + 1) * D (k + 1) x / ((k + 1)! : ℝ)

/-- **Kramers–Moyal truncation error in terms of the next jump moment.**
For a nonnegative jump density `w` with finite jump moments up to order `n + 1`, and
`f = D 0` with `|f⁽ⁿ⁺¹⁾| ≤ M`,
`|L f(x) - Σ_{k=1}^{n} αₖ(x) f⁽ᵏ⁾(x)/k!| ≤ M/(n+1)! · ∫ |x'-x|ⁿ⁺¹ W(x'|x) dx'`. -/
theorem jumpGen_sub_kmGen_le (D : ℕ → ℝ → ℝ) (n : ℕ) (x M : ℝ)
    (hD : ∀ k ≤ n, ∀ y, HasDerivAt (D k) (D (k + 1) y) y) (hM : ∀ y, |D (n + 1) y| ≤ M)
    (hw : ∀ x', 0 ≤ w x')
    (hint : ∀ k ≤ n + 1, Integrable (fun x' => (x' - x) ^ k * w x') ν) :
    |jumpGen ν w (D 0) x - kmGen ν w D n x|
      ≤ M / ((n + 1)! : ℝ) * absJumpMoment ν w x (n + 1) := by
  have hcont : ∀ k ≤ n, Continuous (D k) := fun k hk =>
    continuous_iff_continuousAt.2 fun y => (hD k hk y).continuousAt
  have hw_meas : AEStronglyMeasurable w ν := by
    have := (hint 0 (Nat.zero_le _)).aestronglyMeasurable
    simpa using this
  set R : ℝ → ℝ := fun x' => (D 0 x' - taylorTower D n x (x' - x)) * w x' with hR
  have hRbound : ∀ x', |R x'| ≤ M / ((n + 1)! : ℝ) * (|x' - x| ^ (n + 1) * w x') := by
    intro x'
    have := taylor_tower_bound n D x (x' - x) M hD (fun t _ => hM _)
    rw [add_sub_cancel] at this
    rw [hR, abs_mul, abs_of_nonneg (hw x')]
    calc |D 0 x' - taylorTower D n x (x' - x)| * w x'
        ≤ (M * |x' - x| ^ (n + 1) / ((n + 1)! : ℝ)) * w x' :=
          mul_le_mul_of_nonneg_right this (hw x')
      _ = _ := by ring
  have habs : Integrable (fun x' => |x' - x| ^ (n + 1) * w x') ν := by
    refine (hint (n + 1) le_rfl).abs.congr (Eventually.of_forall fun x' => ?_)
    simp [abs_mul, abs_pow, abs_of_nonneg (hw x')]
  have hRmeas : AEStronglyMeasurable R ν := by
    refine AEStronglyMeasurable.mul ?_ hw_meas
    refine Continuous.aestronglyMeasurable ?_
    refine (hcont 0 (Nat.zero_le _)).sub ?_
    unfold taylorTower
    fun_prop
  have hRint : Integrable R ν :=
    Integrable.mono' (habs.const_mul _) hRmeas (Eventually.of_forall fun x' => by
      simpa [Real.norm_eq_abs] using hRbound x')
  have hterm : ∀ k ∈ Finset.range n, Integrable
      (fun x' => D (k + 1) x / ((k + 1)! : ℝ) * ((x' - x) ^ (k + 1) * w x')) ν :=
    fun k hk => (hint (k + 1) (by simp at hk; omega)).const_mul _
  have hsplit : ∀ x', (D 0 x' - D 0 x) * w x'
      = (∑ k ∈ Finset.range n, D (k + 1) x / ((k + 1)! : ℝ) * ((x' - x) ^ (k + 1) * w x'))
        + R x' := by
    intro x'
    simp only [hR]
    rw [taylorTower_eq_add]
    have : ∑ k ∈ Finset.range n, D (k + 1) x / ((k + 1)! : ℝ) * ((x' - x) ^ (k + 1) * w x')
        = (∑ k ∈ Finset.range n, D (k + 1) x * (x' - x) ^ (k + 1) / ((k + 1)! : ℝ)) * w x' := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    ring
  have hgen : jumpGen ν w (D 0) x = kmGen ν w D n x + ∫ x', R x' ∂ν := by
    rw [jumpGen, integral_congr_ae (Eventually.of_forall hsplit),
      integral_add (integrable_finset_sum _ hterm) hRint, integral_finset_sum _ hterm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, jumpMoment]
    ring
  rw [hgen, add_sub_cancel_left]
  calc |∫ x', R x' ∂ν| ≤ ∫ x', |R x'| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x', M / ((n + 1)! : ℝ) * (|x' - x| ^ (n + 1) * w x') ∂ν :=
        integral_mono hRint.abs (habs.const_mul _) hRbound
    _ = _ := by rw [integral_const_mul, absJumpMoment]

end Density

/-! ### The scaled kernel (7.2.1) -/

section Scaled

variable (Φ : ℝ → ℝ → ℝ) (A : ℝ → ℝ)

/-- (7.2.1): `W_δ(x'|x) = Φ((x' - x - A(x)δ)/√δ, x) δ^{-3/2}`. -/
def scaledW (δ x x' : ℝ) : ℝ := Φ ((x' - x - A x * δ) / Real.sqrt δ) x / (δ * Real.sqrt δ)

/-- The change of variables `x' = x + A(x)δ + √δ y` behind (7.2.4):
`∫ g(x') W_δ(x'|x) dx' = δ⁻¹ ∫ g(x + A(x)δ + √δ y) Φ(y, x) dy`. -/
theorem integral_mul_scaledW (g : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ∫ x', g x' * scaledW Φ A δ x x'
      = δ⁻¹ * ∫ y, g (x + A x * δ + Real.sqrt δ * y) * Φ y x := by
  set c := x + A x * δ
  set s := Real.sqrt δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hδ
  set H : ℝ → ℝ := fun x' => g x' * Φ ((x' - x - A x * δ) / s) x
  have h1 : ∀ y, g (c + s * y) * Φ y x = H (c + s * y) := by
    intro y
    simp only [H]
    congr 3
    field_simp
    ring
  have h2 : ∫ y, H (c + s * y) = s⁻¹ * ∫ u, H u := by
    have := Measure.integral_comp_mul_left (fun u => H (c + u)) s
    simp only [smul_eq_mul, abs_inv, abs_of_pos hs0] at this
    rw [this, integral_add_left_eq_self]
  simp_rw [h1]
  rw [h2]
  have h3 : ∀ x', g x' * scaledW Φ A δ x x' = (δ * s)⁻¹ * H x' := by
    intro x'
    simp only [scaledW, H, ← hs]
    field_simp
  simp_rw [h3]
  rw [integral_const_mul]
  field_simp

/-- Integrability transfers along the change of variables of `integral_mul_scaledW`. -/
theorem integrable_mul_scaledW (g : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ)
    (hg : Integrable (fun y => g (x + A x * δ + Real.sqrt δ * y) * Φ y x)) :
    Integrable (fun x' => g x' * scaledW Φ A δ x x') := by
  set c := x + A x * δ
  set s := Real.sqrt δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hδ
  have h1 := (hg.comp_mul_left' (inv_ne_zero hs0.ne')).comp_sub_right c
  refine (h1.const_mul (δ * s)⁻¹).congr (Eventually.of_forall fun x' => ?_)
  simp only [scaledW, ← hs, c]
  have : x + A x * δ + s * (s⁻¹ * (x' - (x + A x * δ))) = x' := by field_simp; ring
  rw [this]
  have : s⁻¹ * (x' - (x + A x * δ)) = (x' - x - A x * δ) / s := by field_simp; ring
  rw [this]
  field_simp

variable {Φ}

/-- The hypotheses (7.2.2), (7.2.3) on `Φ(·, x)`, together with the integrability of its
moments up to order three. -/
structure ScaledKernelHyp (Φ : ℝ → ℝ → ℝ) (x Q m₂ m₃ : ℝ) : Prop where
  nonneg : ∀ y, 0 ≤ Φ y x
  integrable : ∀ k ≤ 3, Integrable (fun y => y ^ k * Φ y x)
  mass : ∫ y, Φ y x = Q
  mean : ∫ y, y * Φ y x = 0
  second : ∫ y, y ^ 2 * Φ y x = m₂
  third : ∫ y, |y| ^ 3 * Φ y x = m₃

variable {x Q m₂ m₃ : ℝ}

lemma ScaledKernelHyp.integrable_abs3 (h : ScaledKernelHyp Φ x Q m₂ m₃) :
    Integrable (fun y => |y| ^ 3 * Φ y x) := by
  refine (h.integrable 3 le_rfl).abs.congr (Eventually.of_forall fun y => ?_)
  simp [abs_mul, abs_pow, abs_of_nonneg (h.nonneg y)]

lemma ScaledKernelHyp.integrable_poly (h : ScaledKernelHyp Φ x Q m₂ m₃) (a b : ℝ) (k : ℕ)
    (hk : k ≤ 3) : Integrable (fun y => (a + b * y) ^ k * Φ y x) := by
  have hexp : ∀ y, (a + b * y) ^ k * Φ y x
      = ∑ i ∈ Finset.range (k + 1), (a ^ i * b ^ (k - i) * (k.choose i : ℝ))
          * (y ^ (k - i) * Φ y x) := by
    intro y
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hexp]
  exact integrable_finset_sum _ fun i hi =>
    (h.integrable (k - i) (by omega)).const_mul _

/-- (7.2.4), first line: `α₀ = Q/δ`. -/
theorem scaledW_moment_zero (h : ScaledKernelHyp Φ x Q m₂ m₃) {δ : ℝ} (hδ : 0 < δ) :
    jumpMoment volume (scaledW Φ A δ x) x 0 = Q / δ := by
  have := integral_mul_scaledW Φ A (fun _ => 1) hδ x
  simp only [one_mul] at this
  rw [jumpMoment]
  simp only [pow_zero, one_mul]
  rw [this, h.mass]
  field_simp

/-- (7.2.4), second line: `α₁ = A(x) Q`. -/
theorem scaledW_moment_one (h : ScaledKernelHyp Φ x Q m₂ m₃) {δ : ℝ} (hδ : 0 < δ) :
    jumpMoment volume (scaledW Φ A δ x) x 1 = A x * Q := by
  rw [jumpMoment, integral_mul_scaledW Φ A (fun x' => (x' - x) ^ 1) hδ x]
  have e : ∀ y, (x + A x * δ + Real.sqrt δ * y - x) ^ 1 * Φ y x
      = (A x * δ) * Φ y x + Real.sqrt δ * (y * Φ y x) := fun y => by ring
  simp_rw [e]
  have i0 : Integrable (fun y => Φ y x) := by simpa using h.integrable 0 (by norm_num)
  have i1 : Integrable (fun y => y * Φ y x) := by simpa using h.integrable 1 (by norm_num)
  rw [integral_add (i0.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
    h.mass, h.mean, mul_zero, add_zero]
  field_simp

/-- (7.2.4), third line, **corrected**: `α₂ = ∫ y² Φ(y, x) dy + δ A(x)² Q`.
The text omits the `O(δ)` term `δ A² Q`, which vanishes in the limit `δ → 0`. -/
theorem scaledW_moment_two (h : ScaledKernelHyp Φ x Q m₂ m₃) {δ : ℝ} (hδ : 0 < δ) :
    jumpMoment volume (scaledW Φ A δ x) x 2 = m₂ + δ * A x ^ 2 * Q := by
  rw [jumpMoment, integral_mul_scaledW Φ A (fun x' => (x' - x) ^ 2) hδ x]
  have hs : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  have e : ∀ y, (x + A x * δ + Real.sqrt δ * y - x) ^ 2 * Φ y x
      = (A x * δ) ^ 2 * Φ y x + (2 * A x * δ * Real.sqrt δ) * (y * Φ y x)
        + δ * (y ^ 2 * Φ y x) := fun y => by linear_combination (y ^ 2 * Φ y x) * hs
  simp_rw [e]
  have i0 : Integrable (fun y => Φ y x) := by simpa using h.integrable 0 (by norm_num)
  have i1 : Integrable (fun y => y * Φ y x) := by simpa using h.integrable 1 (by norm_num)
  have i2 : Integrable (fun y => y ^ 2 * Φ y x) := h.integrable 2 (by norm_num)
  have i01 : Integrable (fun y => (A x * δ) ^ 2 * Φ y x
      + (2 * A x * δ * Real.sqrt δ) * (y * Φ y x)) := (i0.const_mul _).add (i1.const_mul _)
  rw [integral_add i01 (i2.const_mul _),
    integral_add (i0.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, h.mass, h.mean, h.second]
  field_simp
  ring

/-- The third absolute jump moment of the scaled kernel is `O(√δ)`:
`∫|x'-x|³ W_δ ≤ 4 (δ² |A|³ Q + √δ m₃)`. -/
theorem scaledW_absMoment_three_le (h : ScaledKernelHyp Φ x Q m₂ m₃) {δ : ℝ} (hδ : 0 < δ) :
    absJumpMoment volume (scaledW Φ A δ x) x 3
      ≤ 4 * (δ ^ 2 * |A x| ^ 3 * Q + Real.sqrt δ * m₃) := by
  have hs0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hs : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  rw [absJumpMoment, integral_mul_scaledW Φ A (fun x' => |x' - x| ^ 3) hδ x]
  have i0 : Integrable (fun y => Φ y x) := by simpa using h.integrable 0 (by norm_num)
  have i3 := h.integrable_abs3
  have hle : ∀ y, |x + A x * δ + Real.sqrt δ * y - x| ^ 3 * Φ y x
      ≤ 4 * ((|A x| * δ) ^ 3 * Φ y x + Real.sqrt δ ^ 3 * (|y| ^ 3 * Φ y x)) := by
    intro y
    have e : x + A x * δ + Real.sqrt δ * y - x = A x * δ + Real.sqrt δ * y := by ring
    rw [e]
    have h1 : |A x * δ + Real.sqrt δ * y| ^ 3 ≤ (|A x * δ| + |Real.sqrt δ * y|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 3
    have h2 := add_pow_le (abs_nonneg (A x * δ)) (abs_nonneg (Real.sqrt δ * y)) 3
    rw [abs_mul, abs_mul, abs_of_pos hδ, abs_of_pos hs0] at h1 h2
    have := (h1.trans h2)
    have hΦ := h.nonneg y
    calc |A x * δ + Real.sqrt δ * y| ^ 3 * Φ y x
        ≤ (2 ^ (3 - 1) * ((|A x| * δ) ^ 3 + (Real.sqrt δ * |y|) ^ 3)) * Φ y x :=
          mul_le_mul_of_nonneg_right this hΦ
      _ = _ := by norm_num; ring
  have hint : Integrable (fun y => |x + A x * δ + Real.sqrt δ * y - x| ^ 3 * Φ y x) := by
    have e : ∀ y, |x + A x * δ + Real.sqrt δ * y - x| ^ 3 * Φ y x
        = |(x + A x * δ + Real.sqrt δ * y - x) ^ 3 * Φ y x| := by
      intro y; rw [abs_mul, abs_pow, abs_of_nonneg (h.nonneg y)]
    simp_rw [e]
    have := h.integrable_poly (A x * δ) (Real.sqrt δ) 3 le_rfl
    refine this.abs.congr (Eventually.of_forall fun y => ?_)
    simp only
    congr 3
    ring
  have iS : Integrable (fun y => (|A x| * δ) ^ 3 * Φ y x + Real.sqrt δ ^ 3 * (|y| ^ 3 * Φ y x)) :=
    (i0.const_mul _).add (i3.const_mul _)
  have hmono := integral_mono hint (iS.const_mul 4) hle
  rw [integral_const_mul, integral_add (i0.const_mul _) (i3.const_mul _), integral_const_mul,
    integral_const_mul, h.mass, h.third] at hmono
  have hδ' : δ⁻¹ * (4 * ((|A x| * δ) ^ 3 * Q + Real.sqrt δ ^ 3 * m₃))
      = 4 * (δ ^ 2 * |A x| ^ 3 * Q + Real.sqrt δ * m₃) := by
    have : Real.sqrt δ ^ 3 = δ * Real.sqrt δ := by rw [pow_succ, hs]
    rw [this]
    field_simp
  rw [← hδ']
  exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hδ.le)

/-- **(7.2.6) with an explicit rate.**  For the scaled kernel (7.2.1)–(7.2.3) and a
test function `f = D 0` with `|f'''| ≤ M`, the master-equation generator differs from the
Fokker–Planck generator `α₁ f' + ½ α₂ f''`, `α₁ = A Q`, `α₂ = ∫ y² Φ`, by at most
`δ · ½ A² Q |f''(x)| + (M/6) · 4 (δ² |A|³ Q + √δ m₃)`, which is `O(√δ)`. -/
theorem scaled_jumpGen_rate (h : ScaledKernelHyp Φ x Q m₂ m₃) {δ : ℝ} (hδ : 0 < δ)
    (D : ℕ → ℝ → ℝ) (M : ℝ) (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y)
    (hM : ∀ y, |D 3 y| ≤ M) :
    |jumpGen volume (scaledW Φ A δ x) (D 0) x - (A x * Q * D 1 x + (1 / 2) * m₂ * D 2 x)|
      ≤ δ * ((1 / 2) * A x ^ 2 * Q * |D 2 x|)
        + M / 6 * (4 * (δ ^ 2 * |A x| ^ 3 * Q + Real.sqrt δ * m₃)) := by
  have hw : ∀ x', 0 ≤ scaledW Φ A δ x x' := fun x' =>
    div_nonneg (h.nonneg _) (by positivity)
  have hint : ∀ k ≤ 2 + 1, Integrable (fun x' => (x' - x) ^ k * scaledW Φ A δ x x') := by
    intro k hk
    refine integrable_mul_scaledW Φ A (fun x' => (x' - x) ^ k) hδ x ?_
    have := h.integrable_poly (A x * δ) (Real.sqrt δ) k hk
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only
    congr 2
    ring
  have key := jumpGen_sub_kmGen_le volume (scaledW Φ A δ x) D 2 x M hD hM hw hint
  have hkm : kmGen volume (scaledW Φ A δ x) D 2 x
      = A x * Q * D 1 x + (1 / 2) * m₂ * D 2 x + δ * ((1 / 2) * A x ^ 2 * Q * D 2 x) := by
    simp only [kmGen, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [scaledW_moment_one A h hδ, scaledW_moment_two A h hδ]
    norm_num
    ring
  have h3 := scaledW_absMoment_three_le A h hδ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [hkm] at key
  have hfac : ((2 + 1)! : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at key
  calc _ = |(jumpGen volume (scaledW Φ A δ x) (D 0) x
          - (A x * Q * D 1 x + (1 / 2) * m₂ * D 2 x + δ * ((1 / 2) * A x ^ 2 * Q * D 2 x)))
          + δ * ((1 / 2) * A x ^ 2 * Q * D 2 x)| := by ring_nf
    _ ≤ |jumpGen volume (scaledW Φ A δ x) (D 0) x
          - (A x * Q * D 1 x + (1 / 2) * m₂ * D 2 x + δ * ((1 / 2) * A x ^ 2 * Q * D 2 x))|
        + |δ * ((1 / 2) * A x ^ 2 * Q * D 2 x)| := abs_add_le _ _
    _ ≤ M / 6 * (4 * (δ ^ 2 * |A x| ^ 3 * Q + Real.sqrt δ * m₃))
        + δ * ((1 / 2) * A x ^ 2 * Q * |D 2 x|) := by
        gcongr
        · exact key.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
        · have hQ : 0 ≤ Q := h.mass ▸ integral_nonneg h.nonneg
          rw [abs_mul, abs_of_pos hδ, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * A x ^ 2 * Q)]
    _ = _ := by ring

/-- **(7.2.6)**: as `δ → 0⁺`, the master-equation generator of the scaled kernel
(7.2.1) converges to the Fokker–Planck generator `α₁ f' + ½ α₂ f''`. -/
theorem scaled_jumpGen_tendsto (h : ScaledKernelHyp Φ x Q m₂ m₃)
    (D : ℕ → ℝ → ℝ) (M : ℝ) (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y)
    (hM : ∀ y, |D 3 y| ≤ M) :
    Tendsto (fun δ => jumpGen volume (scaledW Φ A δ x) (D 0) x) (𝓝[>] 0)
      (𝓝 (A x * Q * D 1 x + (1 / 2) * m₂ * D 2 x)) := by
  set L := A x * Q * D 1 x + (1 / 2) * m₂ * D 2 x
  set bound : ℝ → ℝ := fun δ => δ * ((1 / 2) * A x ^ 2 * Q * |D 2 x|)
    + M / 6 * (4 * (δ ^ 2 * |A x| ^ 3 * Q + Real.sqrt δ * m₃))
  have hb : Tendsto bound (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto bound (𝓝 0) (𝓝 (bound 0)) := by
      simp only [bound]
      exact ((continuous_id.mul continuous_const).add (continuous_const.mul
        (continuous_const.mul ((continuous_pow 2 |>.mul continuous_const |>.mul continuous_const).add
          (Real.continuous_sqrt.mul continuous_const))))).tendsto 0
    have h0 : bound 0 = 0 := by simp [bound]
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact scaled_jumpGen_rate A h hδ D M hD hM

/-- **(7.2.5)**: if `|y|³ Φ(y, x) → 0` as `|y| → ∞`, then `W_δ(x'|x) → 0` as `δ → 0⁺`
for every `x' ≠ x`. -/
theorem scaledW_tendsto_zero {x x' : ℝ} (hx : x' ≠ x)
    (hΦ : Tendsto (fun y => |y| ^ 3 * Φ y x) (cocompact ℝ) (𝓝 0)) :
    Tendsto (fun δ => scaledW Φ A δ x x') (𝓝[>] 0) (𝓝 0) := by
  set d : ℝ → ℝ := fun δ => x' - x - A x * δ
  have hd : Tendsto d (𝓝[>] 0) (𝓝 (x' - x)) := by
    have : Tendsto d (𝓝 0) (𝓝 (d 0)) := by
      simp only [d]; exact (continuous_const.sub (continuous_const.mul continuous_id)).tendsto 0
    simpa [d] using this.mono_left nhdsWithin_le_nhds
  have hdne : ∀ᶠ δ in 𝓝[>] 0, d δ ≠ 0 :=
    hd.eventually (isOpen_ne.mem_nhds (sub_ne_zero.2 hx))
  have hsqrt : Tendsto Real.sqrt (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact Real.sqrt_pos.2 hδ
  -- the argument of `Φ` escapes to infinity
  have hy : Tendsto (fun δ => d δ / Real.sqrt δ) (𝓝[>] 0) (cocompact ℝ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    simp only [Real.norm_eq_abs, abs_div]
    have h1 : Tendsto (fun δ => |d δ|) (𝓝[>] 0) (𝓝 |x' - x|) := hd.abs
    have h2 : Tendsto (fun δ => |Real.sqrt δ|) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (tendsto_nhdsWithin_iff.1 hsqrt).1.abs
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact abs_pos.2 (Real.sqrt_pos.2 hδ).ne'
    have := h1.pos_mul_atTop (abs_pos.2 (sub_ne_zero.2 hx)) (tendsto_inv_nhdsGT_zero.comp h2)
    exact this.congr fun δ => (div_eq_mul_inv _ _).symm
  have hnum : Tendsto (fun δ => |d δ / Real.sqrt δ| ^ 3 * Φ (d δ / Real.sqrt δ) x) (𝓝[>] 0)
      (𝓝 0) := hΦ.comp hy
  have hden : Tendsto (fun δ => (|d δ| ^ 3)⁻¹) (𝓝[>] 0) (𝓝 ((|x' - x| ^ 3)⁻¹)) :=
    (hd.abs.pow 3).inv₀ (pow_ne_zero 3 (abs_ne_zero.2 (sub_ne_zero.2 hx)))
  have hprod := hnum.mul hden
  rw [zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hdne] with δ hδ hdδ
  have hs0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hs : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt (le_of_lt hδ)
  simp only [scaledW, d] at hdδ ⊢
  set u := Φ ((x' - x - A x * δ) / Real.sqrt δ) x
  have hne : |x' - x - A x * δ| ≠ 0 := abs_ne_zero.2 hdδ
  rw [abs_div, abs_of_pos hs0, div_pow]
  have hδs : δ * Real.sqrt δ = Real.sqrt δ ^ 3 := by rw [pow_succ, hs]
  rw [hδs]
  field_simp

/-- **(7.2.27)**, corrected and made quantitative: for the scaled kernel,
`|αₙ| ≤ 2ⁿ⁻¹ (δⁿ⁻¹ |A|ⁿ Q + √δⁿ⁻² ∫|y|ⁿ Φ)` (the text's `αₙ = δ^{n/2-1} ∫ yⁿ Φ` is the
exact value when `A = 0`). -/
theorem scaledW_jumpMoment_abs_le (hΦ : ∀ y, 0 ≤ Φ y x) {n : ℕ} (hn : 2 ≤ n)
    (hint : ∀ k ≤ n, Integrable (fun y => y ^ k * Φ y x)) {δ : ℝ} (hδ : 0 < δ) :
    |jumpMoment volume (scaledW Φ A δ x) x n|
      ≤ 2 ^ (n - 1) * (δ ^ (n - 1) * |A x| ^ n * (∫ y, Φ y x)
        + Real.sqrt δ ^ (n - 2) * ∫ y, |y| ^ n * Φ y x) := by
  have hs0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hs : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  rw [jumpMoment, integral_mul_scaledW Φ A (fun x' => (x' - x) ^ n) hδ x]
  have i0 : Integrable (fun y => Φ y x) := by simpa using hint 0 (Nat.zero_le _)
  have iN : Integrable (fun y => |y| ^ n * Φ y x) := by
    refine (hint n le_rfl).abs.congr (Eventually.of_forall fun y => ?_)
    simp [abs_mul, abs_pow, abs_of_nonneg (hΦ y)]
  have hle : ∀ y, |(x + A x * δ + Real.sqrt δ * y - x) ^ n * Φ y x|
      ≤ 2 ^ (n - 1) * ((|A x| * δ) ^ n * Φ y x + Real.sqrt δ ^ n * (|y| ^ n * Φ y x)) := by
    intro y
    have e : x + A x * δ + Real.sqrt δ * y - x = A x * δ + Real.sqrt δ * y := by ring
    rw [e, abs_mul, abs_pow, abs_of_nonneg (hΦ y)]
    have h1 : |A x * δ + Real.sqrt δ * y| ^ n ≤ (|A x * δ| + |Real.sqrt δ * y|) ^ n :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) n
    have h2 := add_pow_le (abs_nonneg (A x * δ)) (abs_nonneg (Real.sqrt δ * y)) n
    rw [abs_mul, abs_mul, abs_of_pos hδ, abs_of_pos hs0] at h1 h2
    calc |A x * δ + Real.sqrt δ * y| ^ n * Φ y x
        ≤ (2 ^ (n - 1) * ((|A x| * δ) ^ n + (Real.sqrt δ * |y|) ^ n)) * Φ y x :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (hΦ y)
      _ = _ := by ring
  have hint' : Integrable (fun y => (x + A x * δ + Real.sqrt δ * y - x) ^ n * Φ y x) := by
    have hexp : ∀ y, (x + A x * δ + Real.sqrt δ * y - x) ^ n * Φ y x
        = ∑ i ∈ Finset.range (n + 1), ((A x * δ) ^ i * Real.sqrt δ ^ (n - i) * (n.choose i : ℝ))
          * (y ^ (n - i) * Φ y x) := by
      intro y
      rw [show x + A x * δ + Real.sqrt δ * y - x = A x * δ + Real.sqrt δ * y by ring, add_pow,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp_rw [hexp]
    exact integrable_finset_sum _ fun i hi => (hint (n - i) (by omega)).const_mul _
  have hmono : |∫ y, (x + A x * δ + Real.sqrt δ * y - x) ^ n * Φ y x|
      ≤ 2 ^ (n - 1) * ((|A x| * δ) ^ n * (∫ y, Φ y x)
        + Real.sqrt δ ^ n * ∫ y, |y| ^ n * Φ y x) := by
    refine (abs_integral_le_integral_abs).trans ?_
    have iS : Integrable (fun y => (|A x| * δ) ^ n * Φ y x
        + Real.sqrt δ ^ n * (|y| ^ n * Φ y x)) := (i0.const_mul _).add (iN.const_mul _)
    refine (integral_mono hint'.abs (iS.const_mul _) hle).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (i0.const_mul _) (iN.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [abs_mul, abs_inv, abs_of_pos hδ]
  have hn1 : n = (n - 1) + 1 := by omega
  have hn2 : n = (n - 2) + 2 := by omega
  calc δ⁻¹ * |∫ y, (x + A x * δ + Real.sqrt δ * y - x) ^ n * Φ y x|
      ≤ δ⁻¹ * (2 ^ (n - 1) * ((|A x| * δ) ^ n * (∫ y, Φ y x)
        + Real.sqrt δ ^ n * ∫ y, |y| ^ n * Φ y x)) :=
        mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hδ.le)
    _ = _ := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
        have e1 : (|A x| * δ) ^ (m + 2) = δ * (δ ^ (m + 1) * |A x| ^ (m + 2)) := by ring
        have e2 : Real.sqrt δ ^ (m + 2) = δ * Real.sqrt δ ^ m := by
          rw [pow_add, hs]; ring
        rw [e1, e2]
        field_simp

/-- **(7.2.27)**: the Kramers–Moyal coefficients of order `n ≥ 3` of the scaled kernel
vanish as `δ → 0⁺`, so that the expansion (7.2.25) terminates at the second term in the
limit. -/
theorem scaledW_jumpMoment_tendsto_zero (hΦ : ∀ y, 0 ≤ Φ y x) {n : ℕ} (hn : 3 ≤ n)
    (hint : ∀ k ≤ n, Integrable (fun y => y ^ k * Φ y x)) :
    Tendsto (fun δ => jumpMoment volume (scaledW Φ A δ x) x n) (𝓝[>] 0) (𝓝 0) := by
  set b : ℝ → ℝ := fun δ => 2 ^ (n - 1) * (δ ^ (n - 1) * |A x| ^ n * (∫ y, Φ y x)
        + Real.sqrt δ ^ (n - 2) * ∫ y, |y| ^ n * Φ y x)
  have hb : Tendsto b (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous b := by simp only [b]; fun_prop
    have h0 : b 0 = 0 := by
      simp only [b]
      rw [zero_pow (by omega), Real.sqrt_zero, zero_pow (by omega)]
      ring
    have := hc.tendsto 0
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact scaledW_jumpMoment_abs_le A hΦ (by omega) hint hδ

end Scaled

/-! ### (7.2.22)–(7.2.23): the master equation in jump variables -/

/-- (7.2.22)–(7.2.23): with `t(y, x) = W(x + y | x)`, the right-hand side of the master
equation (7.2.7) equals `∫ dy [t(y, x - y) P(x - y) - t(y, x) P(x)]`. -/
theorem km_master_change_of_variables (W : ℝ → ℝ → ℝ) (P : ℝ → ℝ) (x : ℝ)
    (h1 : Integrable (fun x' => W x x' * P x')) (h2 : Integrable (fun x' => W x' x * P x)) :
    ∫ x', (W x x' * P x' - W x' x * P x)
      = ∫ y, ((fun y x => W (x + y) x) y (x - y) * P (x - y)
          - (fun y x => W (x + y) x) y x * P x) := by
  have h1' : Integrable (fun y => W x (x - y) * P (x - y)) := h1.comp_sub_left x
  have h2' : Integrable (fun y => W (x + y) x * P x) := h2.comp_add_left x
  simp only [sub_add_cancel]
  rw [integral_sub h1 h2, integral_sub h1' h2']
  congr 1
  · exact (integral_sub_left_eq_self (fun x' => W x x' * P x') volume x).symm
  · exact (integral_add_left_eq_self (fun x' => W x' x * P x) x).symm

/-! ### Examples -/

section Examples

/-- The jump directions `±1` used by the one-step examples. -/
def pmOne : Bool → ℝ := fun b => if b then 1 else -1

/-- (7.2.9)–(7.2.10): the random walk with step `l` and rate `d` in each direction has
`α₀ = 2d`, `α₁ = 0`, `α₂ = 2 l² d`, and `α₃ = 0`. -/
theorem randomWalk_moments (l d x : ℝ) :
    finJumpMoment Finset.univ (fun b => l * pmOne b) (fun _ _ => d) x 0 = 2 * d ∧
    finJumpMoment Finset.univ (fun b => l * pmOne b) (fun _ _ => d) x 1 = 0 ∧
    finJumpMoment Finset.univ (fun b => l * pmOne b) (fun _ _ => d) x 2 = 2 * l ^ 2 * d ∧
    finJumpMoment Finset.univ (fun b => l * pmOne b) (fun _ _ => d) x 3 = 0 := by
  simp only [finJumpMoment, Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, pmOne, if_true]
  norm_num
  refine ⟨by ring, by ring, by ring⟩

/-- (7.2.11)–(7.2.13) **with a rate**: with `δ = l²` and `D = l² d`, the random-walk
generator `d [f(x+l) + f(x-l) - 2 f(x)]` differs from the diffusion generator `D f''` by at
most `M D δ / 12`, where `|f''''| ≤ M`.  Thus the limit is the diffusion equation
`∂_t P = D ∂²_x P`, with error `O(δ)`. -/
theorem randomWalk_rate (l d x M : ℝ) (hd : 0 ≤ d) (D : ℕ → ℝ → ℝ)
    (hD : ∀ k ≤ 3, ∀ y, HasDerivAt (D k) (D (k + 1) y) y) (hM : ∀ y, |D 4 y| ≤ M) :
    |finJumpGen Finset.univ (fun b => l * pmOne b) (fun _ _ => d) (D 0) x
        - (l ^ 2 * d) * D 2 x| ≤ M * (l ^ 2 * d) * l ^ 2 / 12 := by
  have key := finJumpGen_sub_finKM_le Finset.univ (fun b => l * pmOne b) (fun _ _ => d) D 3 x M
    hD hM
  have hkm : finKM Finset.univ (fun b => l * pmOne b) (fun _ _ => d) D 3 x = l ^ 2 * d * D 2 x := by
    obtain ⟨_, h1, h2, h3⟩ := randomWalk_moments l d x
    simp only [finKM, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h1, h2, h3]
    norm_num [Nat.factorial]
    ring
  have habs : finAbsJumpMoment Finset.univ (fun b => l * pmOne b) (fun _ _ => d) x 4
      = 2 * d * l ^ 4 := by
    simp only [finAbsJumpMoment, Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
      not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, pmOne, if_true]
    norm_num
    rw [abs_of_nonneg hd, show |l| ^ 4 = l ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]
    ring
  rw [hkm, habs] at key
  calc _ ≤ M / ((3 + 1)! : ℝ) * (2 * d * l ^ 4) := key
    _ = _ := by norm_num [Nat.factorial]; ring

/-- (7.2.14)–(7.2.15): the Poisson process with step `l` and rate `d` has `αₙ = lⁿ d`. -/
theorem poisson_moments (l d x : ℝ) (n : ℕ) :
    finJumpMoment Finset.univ (fun _ : Unit => l) (fun _ _ => d) x n = l ^ n * d := by
  simp [finJumpMoment, mul_comm]

/-- §7.2.1 b): **the Poisson process has no Fokker–Planck limit.**  For any
parametrization `(lₖ, dₖ)` with `lₖ → 0` along which `α₁ = l d → a₁` and `α₂ = l² d → a₂`,
necessarily `a₂ = 0`: the diffusion coefficient vanishes in the limit. -/
theorem poisson_no_diffusion_limit {ι : Type*} {F : Filter ι} [F.NeBot] (l d : ι → ℝ)
    {a₁ a₂ : ℝ} (hl : Tendsto l F (𝓝 0)) (h1 : Tendsto (fun i => l i * d i) F (𝓝 a₁))
    (h2 : Tendsto (fun i => l i ^ 2 * d i) F (𝓝 a₂)) : a₂ = 0 := by
  have : Tendsto (fun i => l i * (l i * d i)) F (𝓝 (0 * a₁)) := hl.mul h1
  rw [zero_mul] at this
  refine tendsto_nhds_unique h2 (this.congr fun i => by ring)

/-- (7.2.16): the birth–death approximation of a diffusion, jumps `±δ` with rates
`±A/(2δ) + B/(2δ²)`. -/
def bdRate (A B : ℝ → ℝ) (δ : ℝ) : Bool → ℝ → ℝ :=
  fun b x => (if b then 1 else -1) * A x / (2 * δ) + B x / (2 * δ ^ 2)

/-- (7.2.17a–c): the jump moments of the birth–death approximation (7.2.16) are
`α₀ = B/δ²`, `α₁ = A`, `α₂ = B`, exactly. -/
theorem bd_moments (A B : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) (x : ℝ) :
    finJumpMoment Finset.univ (fun b => δ * pmOne b) (bdRate A B δ) x 0 = B x / δ ^ 2 ∧
    finJumpMoment Finset.univ (fun b => δ * pmOne b) (bdRate A B δ) x 1 = A x ∧
    finJumpMoment Finset.univ (fun b => δ * pmOne b) (bdRate A B δ) x 2 = B x := by
  simp only [finJumpMoment, Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, pmOne, bdRate, if_true]
  norm_num
  refine ⟨by field_simp; ring, by field_simp; ring, by field_simp; ring⟩

/-- (7.2.17)–(7.2.18) **with a rate**: the generator of the birth–death approximation
(7.2.16) differs from the Fokker–Planck generator `A f' + ½ B f''` by at most
`(M/6)(|A| δ² + |B| δ)`, where `|f'''| ≤ M`.  Hence the limit `δ → 0` is the
Fokker–Planck equation (7.2.18), with error `O(δ)`. -/
theorem bd_rate (A B : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (x M : ℝ) (D : ℕ → ℝ → ℝ)
    (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y) (hM : ∀ y, |D 3 y| ≤ M) :
    |finJumpGen Finset.univ (fun b => δ * pmOne b) (bdRate A B δ) (D 0) x
        - (A x * D 1 x + (1 / 2) * B x * D 2 x)|
      ≤ M / 6 * (|A x| * δ ^ 2 + |B x| * δ) := by
  have key := finJumpGen_sub_finKM_le Finset.univ (fun b => δ * pmOne b) (bdRate A B δ) D 2 x M
    hD hM
  obtain ⟨_, h1, h2⟩ := bd_moments A B hδ.ne' x
  have hkm : finKM Finset.univ (fun b => δ * pmOne b) (bdRate A B δ) D 2 x
      = A x * D 1 x + (1 / 2) * B x * D 2 x := by
    simp only [finKM, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h1, h2]
    norm_num
    ring
  have habs : finAbsJumpMoment Finset.univ (fun b => δ * pmOne b) (bdRate A B δ) x 3
      ≤ |A x| * δ ^ 2 + |B x| * δ := by
    simp only [finAbsJumpMoment, Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
      not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, pmOne, bdRate, if_true]
    norm_num
    rw [abs_of_pos hδ]
    have e1 : ∀ u : ℝ, |u| * δ ^ 3 = |u * δ ^ 3| := fun u => by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < δ ^ 3)]
    rw [e1, e1]
    have ea : (A x / (2 * δ) + B x / (2 * δ ^ 2)) * δ ^ 3 = A x * δ ^ 2 / 2 + B x * δ / 2 := by
      field_simp
    have eb : (-A x / (2 * δ) + B x / (2 * δ ^ 2)) * δ ^ 3 = -(A x * δ ^ 2 / 2) + B x * δ / 2 := by
      field_simp
    rw [ea, eb]
    have := abs_add_le (A x * δ ^ 2 / 2) (B x * δ / 2)
    have := abs_add_le (-(A x * δ ^ 2 / 2)) (B x * δ / 2)
    rw [abs_neg] at this
    have hA : |A x * δ ^ 2 / 2| = |A x| * δ ^ 2 / 2 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < δ ^ 2)]; norm_num
    have hB : |B x * δ / 2| = |B x| * δ / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hδ]; norm_num
    linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [hkm] at key
  calc _ ≤ M / ((2 + 1)! : ℝ) * finAbsJumpMoment Finset.univ (fun b => δ * pmOne b)
        (bdRate A B δ) x (2 + 1) := key
    _ ≤ M / ((2 + 1)! : ℝ) * (|A x| * δ ^ 2 + |B x| * δ) := by gcongr
    _ = _ := by norm_num [Nat.factorial]

end Examples

end Gardiner
