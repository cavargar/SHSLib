/-
# One-dimensional calculus for the approximation methods of Gardiner Ch. 6–7

Two tools used throughout the formalization of the small-noise expansion (§6.3) and of
the system-size expansion (§7.2):

* `Gardiner.taylor_tower_bound`: Taylor's theorem with an explicit Lagrange-type bound
  `|f(x+h) - Σ_{k≤n} f⁽ᵏ⁾(x) hᵏ/k!| ≤ M |h|ⁿ⁺¹/(n+1)!`, for a *tower* of functions
  `D 0 = f, D 1 = f', …` (each `D (k+1)` is the derivative of `D k`).  Working with a tower
  instead of `iteratedDeriv` lets the examples supply their derivatives explicitly.
* `Gardiner.integral_pow_mul_deriv`: the integration by parts
  `∫ yᵏ⁺¹ g'(y) dy = -(k+1) ∫ yᵏ g(y) dy` on the whole line, which is the only
  manipulation used to pass from a Fokker–Planck equation to its moment equations
  [(6.3.18), (7.2.60), (7.2.76)].  Surface terms are not assumed to vanish; they are
  *derived* from integrability.
-/
import SHSLib.Gardiner.Basic

open MeasureTheory Filter Topology Set
open scoped BigOperators Nat

noncomputable section

namespace Gardiner

/-! ### Taylor's theorem with an explicit remainder bound -/

/-- If `g 0 = 0` and `|g'(t)| ≤ C |t|ᵏ` between `0` and `h`, then
`|g h| ≤ C |h|ᵏ⁺¹ / (k+1)`. -/
lemma abs_le_of_abs_deriv_le_pow {g g' : ℝ → ℝ} {C : ℝ} {k : ℕ} (h : ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t) (h0 : g 0 = 0)
    (hb : ∀ t ∈ uIcc 0 h, |g' t| ≤ C * |t| ^ k) :
    |g h| ≤ C * |h| ^ (k + 1) / (k + 1) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => C * t ^ (k + 1) / (k + 1)) (C * t ^ k) t := by
    intro t
    have := ((hasDerivAt_pow (k + 1) t).const_mul C).div_const ((k : ℝ) + 1)
    convert this using 1
    push_cast
    field_simp
  rcases le_or_gt 0 h with hh | hh
  · have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := h)
      (f := g) (f' := g') (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).hasDerivWithinAt) (B := fun t => C * t ^ (k + 1) / (k + 1))
      (B' := fun t => C * t ^ k) (by simp [h0]) hB
      (fun t ht => by
        have h1 := hb t (by rw [uIcc_of_le hh]; exact Ico_subset_Icc_self ht)
        rwa [abs_of_nonneg ht.1] at h1)
      (show h ∈ Icc 0 h from ⟨hh, le_rfl⟩)
    simpa [Real.norm_eq_abs, abs_of_nonneg hh] using key
  · -- reflect
    set g₁ : ℝ → ℝ := fun t => g (-t)
    have hg₁ : ∀ t, HasDerivAt g₁ (-g' (-t)) t := by
      intro t
      have := (hg (-t)).comp t (hasDerivAt_neg t)
      simpa [g₁, mul_comm] using this
    have hpos : 0 ≤ -h := by linarith
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := -h)
      (f := g₁) (f' := fun t => -g' (-t)) (fun t _ => (hg₁ t).continuousAt.continuousWithinAt)
      (fun t _ => (hg₁ t).hasDerivWithinAt) (B := fun t => C * t ^ (k + 1) / (k + 1))
      (B' := fun t => C * t ^ k) (by simp [g₁, h0]) hB
      (fun t ht => by
        have h1 := hb (-t) (by
          rw [uIcc_of_ge hh.le]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
        rw [abs_neg, abs_of_nonneg ht.1] at h1
        simpa [Real.norm_eq_abs] using h1)
      (show -h ∈ Icc 0 (-h) from ⟨hpos, le_rfl⟩)
    have : |g h| = ‖g₁ (-h)‖ := by simp [g₁, Real.norm_eq_abs]
    rw [this, abs_of_neg hh]
    exact key

lemma hasDerivAt_pow_succ_div_factorial (j : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (j + 1) / ((j + 1)! : ℝ)) (t ^ j / (j ! : ℝ)) t := by
  have := (hasDerivAt_pow (j + 1) t).div_const ((j + 1)! : ℝ)
  convert this using 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The Taylor polynomial `Σ_{k≤n} D k x · hᵏ/k!` of a derivative tower. -/
def taylorTower (D : ℕ → ℝ → ℝ) (n : ℕ) (x h : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), D k x * h ^ k / (k ! : ℝ)

lemma hasDerivAt_taylorTower (D : ℕ → ℝ → ℝ) (n : ℕ) (x t : ℝ) :
    HasDerivAt (fun h => taylorTower D (n + 1) x h) (taylorTower (fun k => D (k + 1)) n x t) t := by
  unfold taylorTower
  have hfun : (fun h => ∑ k ∈ Finset.range (n + 1 + 1), D k x * h ^ k / (k ! : ℝ))
      = fun h => (∑ k ∈ Finset.range (n + 1), D (k + 1) x * (h ^ (k + 1) / ((k + 1)! : ℝ)))
        + D 0 x := by
    funext h
    rw [Finset.sum_range_succ']
    simp [mul_div_assoc]
  rw [hfun]
  apply HasDerivAt.add_const
  have := HasDerivAt.fun_sum (u := Finset.range (n + 1))
    (A := fun k h => D (k + 1) x * (h ^ (k + 1) / ((k + 1)! : ℝ)))
    (A' := fun k => D (k + 1) x * (t ^ k / (k ! : ℝ)))
    (fun k _ => (hasDerivAt_pow_succ_div_factorial k t).const_mul _)
  convert this using 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Taylor's theorem with an explicit remainder bound**, for a derivative tower
`D 0, D 1, …, D (n+1)`: if `|D (n+1)| ≤ M` on the segment from `x` to `x + h`, then
`|D 0 (x+h) - Σ_{k≤n} D k x hᵏ/k!| ≤ M |h|ⁿ⁺¹/(n+1)!`. -/
theorem taylor_tower_bound (n : ℕ) (D : ℕ → ℝ → ℝ) (x h M : ℝ)
    (hD : ∀ k ≤ n, ∀ y, HasDerivAt (D k) (D (k + 1) y) y)
    (hM : ∀ t ∈ uIcc 0 h, |D (n + 1) (x + t)| ≤ M) :
    |D 0 (x + h) - taylorTower D n x h| ≤ M * |h| ^ (n + 1) / ((n + 1)! : ℝ) := by
  induction n generalizing D h with
  | zero =>
    have := abs_le_of_abs_deriv_le_pow (g := fun t => D 0 (x + t) - D 0 x)
      (g' := fun t => D 1 (x + t)) (C := M) (k := 0) h
      (fun t => by
        have := ((hD 0 le_rfl (x + t)).comp t ((hasDerivAt_id t).const_add x)).sub_const (D 0 x)
        simpa using this)
      (by simp) (fun t ht => by simpa using hM t ht)
    simpa [taylorTower] using this
  | succ n ih =>
    have hb : ∀ t ∈ uIcc 0 h, |D 1 (x + t) - taylorTower (fun k => D (k + 1)) n x t|
        ≤ (M / ((n + 1)! : ℝ)) * |t| ^ (n + 1) := by
      intro t ht
      have hsub : uIcc 0 t ⊆ uIcc 0 h := uIcc_subset_uIcc left_mem_uIcc ht
      have := ih (fun k => D (k + 1)) t (fun k hk y => hD (k + 1) (by omega) y)
        (fun s hs => hM s (hsub hs))
      calc _ ≤ M * |t| ^ (n + 1) / ((n + 1)! : ℝ) := this
        _ = _ := by ring
    have key := abs_le_of_abs_deriv_le_pow
      (g := fun t => D 0 (x + t) - taylorTower D (n + 1) x t)
      (g' := fun t => D 1 (x + t) - taylorTower (fun k => D (k + 1)) n x t)
      (C := M / ((n + 1)! : ℝ)) (k := n + 1) h
      (fun t => by
        have h1 := (hD 0 (by omega) (x + t)).comp t ((hasDerivAt_id t).const_add x)
        have h2 := hasDerivAt_taylorTower D n x t
        simpa using h1.sub h2)
      (by simp [taylorTower, Finset.sum_range_succ', zero_pow])
      hb
    calc _ ≤ M / ((n + 1)! : ℝ) * |h| ^ (n + 1 + 1) / ((n + 1 : ℕ) + 1 : ℝ) := key
      _ = M * |h| ^ (n + 1 + 1) / ((n + 1 + 1)! : ℝ) := by
        rw [Nat.factorial_succ (n + 1)]
        push_cast
        field_simp

/-! ### Integration by parts against powers -/

/-- `∫ yᵏ⁺¹ g'(y) dy = -(k+1) ∫ yᵏ g(y) dy` on the whole real line, assuming only the
integrability of the three integrands (the surface terms then vanish automatically). -/
theorem integral_pow_mul_deriv (k : ℕ) {g g' : ℝ → ℝ} (hg : ∀ y, HasDerivAt g (g' y) y)
    (h1 : Integrable (fun y => y ^ (k + 1) * g' y))
    (h2 : Integrable (fun y => y ^ k * g y))
    (h3 : Integrable (fun y => y ^ (k + 1) * g y)) :
    ∫ y, y ^ (k + 1) * g' y = -(((k : ℝ) + 1) * ∫ y, y ^ k * g y) := by
  have hu : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ (k + 1)) (((k : ℝ) + 1) * y ^ k) y := by
    intro y
    simpa using hasDerivAt_pow (k + 1) y
  have h2' : Integrable ((fun y : ℝ => ((k : ℝ) + 1) * y ^ k) * g) := by
    have := h2.const_mul ((k : ℝ) + 1)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [mul_assoc]
  have := integral_mul_deriv_eq_deriv_mul_of_integrable hu hg h1 h2' h3
  rw [this, ← integral_const_mul]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

/-- `∫ g'(y) dy = 0` on the whole real line when `g` and `g'` are integrable. -/
theorem integral_deriv_eq_zero' {g g' : ℝ → ℝ} (hg : ∀ y, HasDerivAt g (g' y) y)
    (h1 : Integrable g') (h2 : Integrable g) : ∫ y, g' y = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable hg h1 h2

/-- `∫ yⁿ g'(y) dy = -n ∫ yⁿ⁻¹ g(y) dy` for every `n` (with the convention that the
right side is `0` for `n = 0`). -/
theorem integral_pow_mul_deriv' (n : ℕ) {g g' : ℝ → ℝ} (hg : ∀ y, HasDerivAt g (g' y) y)
    (hint : ∀ i ≤ n, Integrable (fun y => y ^ i * g y))
    (hint' : Integrable (fun y => y ^ n * g' y)) :
    ∫ y, y ^ n * g' y = -((n : ℝ) * ∫ y, y ^ (n - 1) * g y) := by
  rcases n with _ | k
  · simp only [pow_zero, one_mul, CharP.cast_eq_zero, zero_mul, neg_zero]
    exact integral_deriv_eq_zero' hg (by simpa using hint') (by simpa using hint 0 le_rfl)
  · rw [integral_pow_mul_deriv k hg hint' (hint k (by omega)) (hint (k + 1) le_rfl)]
    simp

/-- **The moment identity of a one-dimensional Fokker–Planck operator.**
For `R = -F' + ½ G''`, `∫ yⁿ R = n ∫ yⁿ⁻¹ F + n(n-1)/2 ∫ yⁿ⁻² G`. -/
theorem integral_pow_mul_fp (n : ℕ) {F F' G G' G'' : ℝ → ℝ}
    (hF : ∀ y, HasDerivAt F (F' y) y) (hG : ∀ y, HasDerivAt G (G' y) y)
    (hG' : ∀ y, HasDerivAt G' (G'' y) y)
    (iF : ∀ i ≤ n, Integrable (fun y => y ^ i * F y))
    (iF' : Integrable (fun y => y ^ n * F' y))
    (iG : ∀ i ≤ n, Integrable (fun y => y ^ i * G y))
    (iG' : ∀ i ≤ n, Integrable (fun y => y ^ i * G' y))
    (iG'' : Integrable (fun y => y ^ n * G'' y)) :
    ∫ y, y ^ n * (-F' y + (1 / 2) * G'' y)
      = (n : ℝ) * (∫ y, y ^ (n - 1) * F y)
        + ((n : ℝ) * ((n : ℝ) - 1) / 2) * ∫ y, y ^ (n - 2) * G y := by
  have e1 : ∀ y, y ^ n * (-F' y + (1 / 2) * G'' y)
      = -(y ^ n * F' y) + (1 / 2) * (y ^ n * G'' y) := fun y => by ring
  simp_rw [e1]
  rw [integral_add (f := fun y => -(y ^ n * F' y)) iF'.neg (iG''.const_mul _), integral_neg,
    integral_const_mul,
    integral_pow_mul_deriv' n hF iF iF', integral_pow_mul_deriv' n hG' iG' iG'']
  rcases n with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [integral_pow_mul_deriv' k hG (fun i hi => iG i (by omega)) (iG' k (by omega))]
    push_cast
    obtain ⟨a, ha⟩ : ∃ a, (∫ y : ℝ, y ^ k * F y) = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, (∫ y : ℝ, y ^ (k - 1) * G y) = b := ⟨_, rfl⟩
    simp only [ha, hb]
    ring

/-- **Iterated integration by parts**: for a derivative tower `G 0, …, G n`,
`∫ yᵏ G n = (-1)ⁿ k(k-1)⋯(k-n+1) ∫ yᵏ⁻ⁿ G 0`; the falling factorial vanishes for `n > k`. -/
theorem integral_pow_mul_tower (n : ℕ) (G : ℕ → ℝ → ℝ) (k : ℕ)
    (hG : ∀ j < n, ∀ y, HasDerivAt (G j) (G (j + 1) y) y)
    (hint : ∀ j ≤ n, ∀ i ≤ k, Integrable (fun y => y ^ i * G j y)) :
    ∫ y, y ^ k * G n y = (-1) ^ n * (k.descFactorial n : ℝ) * ∫ y, y ^ (k - n) * G 0 y := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [integral_pow_mul_deriv' k (hG n (by omega)) (fun i hi => hint n (by omega) i hi)
      (hint (n + 1) le_rfl k le_rfl)]
    rw [ih (k - 1) (fun j hj => hG j (by omega)) (fun j hj i hi => hint j (by omega) i (by omega))]
    rcases k with _ | k
    · simp
    · rw [Nat.succ_descFactorial_succ, show k + 1 - 1 - n = k + 1 - (n + 1) by omega]
      push_cast
      ring

/-- **Linear first-order ODEs**: every solution of `y' = c(t) y + d(t)` with continuous
`c, d` is `y(t) = e^{C(t)} (y(0) + ∫₀ᵗ e^{-C(s)} d(s) ds)`, `C(t) = ∫₀ᵗ c`.  In particular
solutions are determined by their initial value. -/
theorem linear_ode_eq (c d : ℝ → ℝ) (hc : Continuous c) (hd : Continuous d) (y : ℝ → ℝ)
    (hy : ∀ t, HasDerivAt y (c t * y t + d t) t) (t : ℝ) :
    y t = Real.exp (∫ s in (0 : ℝ)..t, c s)
      * (y 0 + ∫ s in (0 : ℝ)..t, Real.exp (-∫ u in (0 : ℝ)..s, c u) * d s) := by
  set C : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, c s with hC
  have hCd : ∀ t, HasDerivAt C (c t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hCc : Continuous C := continuous_iff_continuousAt.2 fun t => (hCd t).continuousAt
  set e : ℝ → ℝ := fun s => Real.exp (-C s) * d s with he
  have hec : Continuous e := (Real.continuous_exp.comp hCc.neg).mul hd
  set F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, e s with hF
  have hFd : ∀ t, HasDerivAt F (e t) t := fun t => (hec.integral_hasStrictDerivAt 0 t).hasDerivAt
  set w : ℝ → ℝ := fun t => y t * Real.exp (-C t) - F t with hw
  have hwd : ∀ t, HasDerivAt w 0 t := by
    intro t
    have h1 := (hy t).mul ((hCd t).neg.exp)
    have h2 := h1.sub (hFd t)
    convert h2 using 1
    simp only [he, Pi.neg_apply]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hwd t).differentiableAt)
    (fun t => (hwd t).deriv) t 0
  have hC0 : C 0 = 0 := by simp [hC]
  have hF0 : F 0 = 0 := by simp [hF]
  simp only [hw, hC0, hF0, neg_zero, Real.exp_zero, mul_one, sub_zero] at hconst
  have : y t = Real.exp (C t) * (y 0 + F t) := by
    rw [← hconst]
    have := Real.exp_pos (C t)
    rw [show Real.exp (-C t) = (Real.exp (C t))⁻¹ from Real.exp_neg _]
    field_simp
    ring
  exact this

/-- Uniqueness for linear first-order ODEs with continuous coefficients. -/
theorem linear_ode_unique (c d : ℝ → ℝ) (hc : Continuous c) (hd : Continuous d) (y₁ y₂ : ℝ → ℝ)
    (h₁ : ∀ t, HasDerivAt y₁ (c t * y₁ t + d t) t) (h₂ : ∀ t, HasDerivAt y₂ (c t * y₂ t + d t) t)
    (h0 : y₁ 0 = y₂ 0) : y₁ = y₂ := by
  funext t
  rw [linear_ode_eq c d hc hd y₁ h₁ t, linear_ode_eq c d hc hd y₂ h₂ t, h0]

end Gardiner
