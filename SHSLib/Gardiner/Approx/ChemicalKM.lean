/-
# Multivariate Kramers–Moyal truncation

Gardiner, *Handbook of Stochastic Methods*, §7.5, (7.5.30)–(7.5.32): the Kramers–Moyal
expansion of the chemical master equation and its second-order truncation, the chemical
Fokker–Planck equation, with an explicit error term.

* `Gardiner.Tower3`, `Gardiner.tower3_taylor` — second-order Taylor formula on `ℝⁿ` with an
  explicit third-order remainder, for test functions given by their partial derivatives.
* `Gardiner.mjGen_sub_mjKM_le` — **the Kramers–Moyal truncation error in terms of the next
  (third) absolute jump moment**, for any master equation on `ℝⁿ` with finitely many jumps.
* `Gardiner.chem_mjDrift`, `Gardiner.chem_mjDiff` — the coefficients (7.5.32) are the first two
  jump moments of (7.5.9); `Gardiner.chem_KM_le` — the truncation error for (7.5.30) → (7.5.31).
* `Gardiner.mjGen_coord`, `Gardiner.mjGen_coord_mul` — the generator on coordinates and their
  products (the source of the moment equations).
-/
import SHSLib.Gardiner.Approx.Chemical

open Finset Filter Topology Set
open scoped Nat

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-- A function `F₀` on `ℝⁿ` with partial derivatives `F₁ a = ∂ₐF₀`, `F₂ a b = ∂_b∂ₐF₀`,
`F₃ a b c = ∂_c∂_b∂ₐF₀`, expressed through directional derivatives along lines. -/
structure Tower3 (F₀ : (Fin n → ℝ) → ℝ) (F₁ : Fin n → (Fin n → ℝ) → ℝ)
    (F₂ : Fin n → Fin n → (Fin n → ℝ) → ℝ) (F₃ : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℝ) :
    Prop where
  d0 : ∀ y v, HasDerivAt (fun s : ℝ => F₀ (y + s • v)) (∑ a, v a * F₁ a y) 0
  d1 : ∀ a y v, HasDerivAt (fun s : ℝ => F₁ a (y + s • v)) (∑ b, v b * F₂ a b y) 0
  d2 : ∀ a b y v, HasDerivAt (fun s : ℝ => F₂ a b (y + s • v)) (∑ c, v c * F₃ a b c y) 0

lemma line_hasDerivAt {g : (Fin n → ℝ) → ℝ} {g' : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (h : ∀ y v, HasDerivAt (fun s : ℝ => g (y + s • v)) (g' y v) 0) (x v : Fin n → ℝ) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => g (x + s • v)) (g' (x + s₀ • v) v) s₀ := by
  have h1 := h (x + s₀ • v) v
  rw [show (0 : ℝ) = s₀ - s₀ by ring] at h1
  have h2 : HasDerivAt (fun s : ℝ => s - s₀) 1 s₀ := (hasDerivAt_id s₀).sub_const s₀
  have := HasDerivAt.comp (h := fun s : ℝ => s - s₀) s₀ h1 h2
  rw [mul_one] at this
  convert this using 1
  funext s
  simp only [Function.comp, sub_smul]
  congr 1
  abel

lemma abs_sum_mul_le (v X : Fin n → ℝ) (B : ℝ) (h : ∀ a, |X a| ≤ B) :
    |∑ a, v a * X a| ≤ (∑ a, |v a|) * B := by
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (h a) (abs_nonneg _)

/-- **Second-order Taylor formula on `ℝⁿ` with explicit remainder**: if all third partial
derivatives are bounded by `M`, then
`|F(x + v) - F(x) - Σₐ vₐ ∂ₐF(x) - ½ Σ_{ab} vₐ v_b ∂ₐ∂_bF(x)| ≤ M (Σₐ|vₐ|)³/6`. -/
theorem tower3_taylor {F₀ F₁ F₂ F₃} (hT : Tower3 (n := n) F₀ F₁ F₂ F₃) (M : ℝ)
    (hM : ∀ a b c y, |F₃ a b c y| ≤ M) (x v : Fin n → ℝ) :
    |F₀ (x + v) - F₀ x - ∑ a, v a * F₁ a x - (1 / 2) * ∑ a, ∑ b, v a * v b * F₂ a b x|
      ≤ M * (∑ a, |v a|) ^ 3 / 6 := by
  set D : ℕ → ℝ → ℝ := fun k s =>
    if k = 0 then F₀ (x + s • v)
    else if k = 1 then ∑ a, v a * F₁ a (x + s • v)
    else if k = 2 then ∑ a, v a * ∑ b, v b * F₂ a b (x + s • v)
    else ∑ a, v a * ∑ b, v b * ∑ c, v c * F₃ a b c (x + s • v) with hD_def
  have hD : ∀ k ≤ 2, ∀ s, HasDerivAt (D k) (D (k + 1) s) s := by
    intro k hk s
    interval_cases k
    · simpa [hD_def] using line_hasDerivAt hT.d0 x v s
    · simp only [hD_def, one_ne_zero, if_false, if_true, show (1 : ℕ) + 1 = 2 from rfl,
        show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num]
      exact HasDerivAt.fun_sum fun a _ => (line_hasDerivAt (hT.d1 a) x v s).const_mul (v a)
    · simp only [hD_def, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
        show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num,
        show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true]
      exact HasDerivAt.fun_sum fun a _ => (HasDerivAt.fun_sum fun b _ =>
        (line_hasDerivAt (hT.d2 a b) x v s).const_mul (v b)).const_mul (v a)
  have hB : ∀ t ∈ uIcc (0 : ℝ) 1, |D (2 + 1) (0 + t)| ≤ M * (∑ a, |v a|) ^ 3 := by
    intro t _
    simp only [hD_def, show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) ≠ 0 by norm_num,
      show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num, if_false]
    have := abs_sum_mul_le v _ _ fun a => abs_sum_mul_le v _ _ fun b =>
      abs_sum_mul_le v _ _ fun c => hM a b c (x + (0 + t) • v)
    calc _ ≤ _ := this
      _ = M * (∑ a, |v a|) ^ 3 := by ring
  have key := taylor_tower_bound 2 D 0 1 _ hD hB
  have e : D 0 (0 + 1) - taylorTower D 2 0 1
      = F₀ (x + v) - F₀ x - ∑ a, v a * F₁ a x - (1 / 2) * ∑ a, ∑ b, v a * v b * F₂ a b x := by
    simp only [taylorTower, sum_range_succ, sum_range_zero, hD_def]
    simp only [zero_add, one_smul, zero_smul, add_zero, if_true, one_ne_zero, if_false,
      show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, one_pow, mul_one,
      Nat.factorial, Nat.cast_one, div_one]
    have hS2 : ∑ a, v a * ∑ b, v b * F₂ a b x = ∑ a, ∑ b, v a * v b * F₂ a b x := by
      simp only [mul_sum, mul_assoc]
    rw [hS2]
    generalize (∑ a, ∑ b, v a * v b * F₂ a b x) = S2
    generalize (∑ a, v a * F₁ a x) = S1
    norm_num
    ring
  rw [← e]
  calc _ ≤ _ := key
    _ = _ := by norm_num [Nat.factorial]

/-! ### Multivariate jump processes: Kramers–Moyal truncation -/

section Jump

variable {κ : Type*} (s : Finset κ) (c : κ → (Fin n → ℝ) → ℝ) (v : κ → Fin n → ℝ)

/-- The backward generator `Σ_j c_j(x) [f(x + v_j) - f(x)]` of a master equation on `ℝⁿ` with
finitely many jumps `v_j` at rates `c_j(x)`. -/
def mjGen (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ j ∈ s, c j x * (f (x + v j) - f x)

/-- First jump moment `Aₐ(x) = Σ_j c_j(x) v_{j,a}`. -/
def mjDrift (a : Fin n) (x : Fin n → ℝ) : ℝ := ∑ j ∈ s, c j x * v j a

/-- Second jump moment `B_ab(x) = Σ_j c_j(x) v_{j,a} v_{j,b}`. -/
def mjDiff (a b : Fin n) (x : Fin n → ℝ) : ℝ := ∑ j ∈ s, c j x * v j a * v j b

/-- Third absolute jump moment `Σ_j |c_j(x)| (Σₐ |v_{j,a}|)³`. -/
def mjAbs3 (x : Fin n → ℝ) : ℝ := ∑ j ∈ s, |c j x| * (∑ a, |v j a|) ^ 3

/-- The second-order Kramers–Moyal (Fokker–Planck) generator
`Σₐ Aₐ ∂ₐf + ½ Σ_{ab} B_ab ∂ₐ∂_bf`, with `F₁ a = ∂ₐf`, `F₂ a b = ∂ₐ∂_bf`. -/
def mjKM (F₁ : Fin n → (Fin n → ℝ) → ℝ) (F₂ : Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ a, mjDrift s c v a x * F₁ a x + (1 / 2) * ∑ a, ∑ b, mjDiff s c v a b x * F₂ a b x

lemma mjKM_eq (F₁ : Fin n → (Fin n → ℝ) → ℝ) (F₂ : Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    mjKM s c v F₁ F₂ x = ∑ j ∈ s, c j x * (∑ a, v j a * F₁ a x
      + (1 / 2) * ∑ a, ∑ b, v j a * v j b * F₂ a b x) := by
  simp only [mjKM, mjDrift, mjDiff, sum_mul, mul_add, sum_add_distrib, mul_sum]
  congr 1
  · rw [sum_comm]; exact sum_congr rfl fun j _ => sum_congr rfl fun a _ => by ring
  · calc ∑ a, ∑ b, ∑ j ∈ s, 1 / 2 * (c j x * v j a * v j b * F₂ a b x)
        = ∑ a, ∑ j ∈ s, ∑ b, 1 / 2 * (c j x * v j a * v j b * F₂ a b x) :=
          sum_congr rfl fun a _ => sum_comm
      _ = ∑ j ∈ s, ∑ a, ∑ b, 1 / 2 * (c j x * v j a * v j b * F₂ a b x) := sum_comm
      _ = _ := sum_congr rfl fun j _ => sum_congr rfl fun a _ =>
          sum_congr rfl fun b _ => by ring

/-- **Kramers–Moyal truncation error on `ℝⁿ`** ((7.5.30) truncated to (7.5.31)): if the third
partial derivatives of the test function are bounded by `M`, the master-equation generator differs
from the Fokker–Planck generator with the first two jump moments by at most
`M/6 · Σ_j |c_j(x)| ‖v_j‖₁³`. -/
theorem mjGen_sub_mjKM_le {F₀ F₁ F₂ F₃} (hT : Tower3 (n := n) F₀ F₁ F₂ F₃) (M : ℝ)
    (hM : ∀ a b c y, |F₃ a b c y| ≤ M) (x : Fin n → ℝ) :
    |mjGen s c v F₀ x - mjKM s c v F₁ F₂ x| ≤ M / 6 * mjAbs3 s c v x := by
  rw [mjKM_eq, mjGen, ← sum_sub_distrib, mjAbs3, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have h := tower3_taylor hT M hM x (v j)
  rw [← mul_sub, abs_mul]
  calc |c j x| * |F₀ (x + v j) - F₀ x - (∑ a, v j a * F₁ a x
        + 1 / 2 * ∑ a, ∑ b, v j a * v j b * F₂ a b x)|
      ≤ |c j x| * (M * (∑ a, |v j a|) ^ 3 / 6) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        convert h using 2; ring
    _ = _ := by ring

/-- The generator applied to a coordinate: `𝓛 xₐ = Aₐ(x)`. -/
theorem mjGen_coord (a : Fin n) (x : Fin n → ℝ) :
    mjGen s c v (fun y => y a) x = mjDrift s c v a x := by
  simp only [mjGen, mjDrift, Pi.add_apply, add_sub_cancel_left]

/-- `𝓛 (xₐ x_b) = xₐ A_b + x_b Aₐ + B_ab`. -/
theorem mjGen_coord_mul (a b : Fin n) (x : Fin n → ℝ) :
    mjGen s c v (fun y => y a * y b) x
      = x a * mjDrift s c v b x + x b * mjDrift s c v a x + mjDiff s c v a b x := by
  simp only [mjGen, mjDrift, mjDiff, Pi.add_apply, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

end Jump

/-! ### The chemical Fokker–Planck coefficients are the first two jump moments -/

section ChemJump

variable {ι : Type*} [Fintype ι] (NA MA : ι → Fin n → ℕ) (kp km : ι → ℝ)

/-- The real jump vectors `±rᴬ` of the chemical master equation. -/
def chemJumpR (p : ι × Bool) : Fin n → ℝ := fun a => (chemJump NA MA p a : ℝ)

/-- The real-state rates `t⁺_A`, `t⁻_A`. -/
def chemRateR (p : ι × Bool) (x : Fin n → ℝ) : ℝ :=
  if p.2 then tplus NA kp p.1 x else tminus MA km p.1 x

theorem chem_mjDrift (a : Fin n) (x : Fin n → ℝ) :
    mjDrift Finset.univ (chemRateR NA MA kp km) (chemJumpR NA MA) a x
      = chemDrift NA MA kp km a x := by
  simp only [mjDrift, chemDrift, chemJumpR, chemJump, chemRateR, Fintype.sum_prod_type,
    Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, Pi.neg_apply, Int.cast_neg]
  exact sum_congr rfl fun j _ => by ring

theorem chem_mjDiff (a b : Fin n) (x : Fin n → ℝ) :
    mjDiff Finset.univ (chemRateR NA MA kp km) (chemJumpR NA MA) a b x
      = chemDiff NA MA kp km a b x := by
  simp only [mjDiff, chemDiff, chemJumpR, chemJump, chemRateR, Fintype.sum_prod_type,
    Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, Pi.neg_apply, Int.cast_neg]
  exact sum_congr rfl fun j _ => by ring

/-- **(7.5.30) → (7.5.31) with explicit error**: the generator of the chemical master equation
(7.5.9) differs from the generator `Σₐ Aₐ ∂ₐ + ½ Σ_{ab} B_ab ∂ₐ∂_b` of the chemical
Fokker–Planck equation, with `A`, `B` from (7.5.32), by at most
`M/6 · Σ_A (|t⁺_A(x)| + |t⁻_A(x)|) ‖rᴬ‖₁³` on test functions with third derivatives bounded by
`M`. -/
theorem chem_KM_le {F₀ F₁ F₂ F₃} (hT : Tower3 (n := n) F₀ F₁ F₂ F₃) (M : ℝ)
    (hM : ∀ a b c y, |F₃ a b c y| ≤ M) (x : Fin n → ℝ) :
    |mjGen Finset.univ (chemRateR NA MA kp km) (chemJumpR NA MA) F₀ x
        - (∑ a, chemDrift NA MA kp km a x * F₁ a x
          + (1 / 2) * ∑ a, ∑ b, chemDiff NA MA kp km a b x * F₂ a b x)|
      ≤ M / 6 * ∑ j, (|tplus NA kp j x| + |tminus MA km j x|)
          * (∑ a, |(stoich NA MA j a : ℝ)|) ^ 3 := by
  have h := mjGen_sub_mjKM_le Finset.univ (chemRateR NA MA kp km) (chemJumpR NA MA) hT M hM x
  simp only [mjKM, chem_mjDrift, chem_mjDiff] at h
  convert h using 2
  simp only [mjAbs3, chemRateR, chemJumpR, chemJump, Fintype.sum_prod_type, Fintype.sum_bool,
    if_true, Bool.false_eq_true, if_false, Pi.neg_apply, Int.cast_neg, abs_neg]
  exact sum_congr rfl fun j _ => by ring

end ChemJump

end Gardiner
