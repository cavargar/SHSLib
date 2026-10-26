/-
# Combinatorial kinetics and the chemical Fokker–Planck equation

Gardiner, *Handbook of Stochastic Methods*, §7.5, equations (7.5.3)–(7.5.9) and
(7.5.30)–(7.5.32).

A reaction network (7.5.3) has species `a : Fin n` and reactions `A : ι` with stoichiometric
vectors `Nᴬ`, `Mᴬ` (7.5.4) and `rᴬ = Mᴬ - Nᴬ` (7.5.5).  The combinatorial propensities (7.5.8)
are `t⁺_A(x) = k⁺_A ∏ₐ xₐ!/(xₐ - Nₐᴬ)!` and `t⁻_A(x) = k⁻_A ∏ₐ xₐ!/(xₐ - Mₐᴬ)!`; we use their
polynomial extension `∏ₐ xₐ(xₐ - 1)⋯(xₐ - Nₐᴬ + 1)` to real states (`Gardiner.propPoly`), which
agrees with the combinatorial expression on lattice points (`Gardiner.propPoly_natCast`).

Main results:

* `Gardiner.propCount_ne_zero_iff`, `Gardiner.orthant_forward`, `Gardiner.orthant_backward` —
  the combinatorial propensities never lead out of the non-negative orthant.
* `Gardiner.cme` and `Gardiner.cme_eq` — the chemical master equation (7.5.9), as an instance
  of a general lattice master equation `Gardiner.latME`.
* `Gardiner.tsum_mul_latME` — duality between the forward master equation and its generator
  (`Σₓ f(x) ∂ₜP(x) = Σₓ P(x) (𝓛f)(x)`), by reindexing along the jumps;
  `Gardiner.latGen_coord`, `Gardiner.latGen_coord_mul` and `Gardiner.chem_latDrift`,
  `Gardiner.chem_latDiff` show that the first two moment equations of (7.5.9) are driven by
  the coefficients (7.5.32).
* `Gardiner.chemDrift`, `Gardiner.chemDiff` — (7.5.32); `Gardiner.chemDiff_nonneg` — the
  diffusion matrix is positive semidefinite; `Gardiner.chemFPE` — the chemical Fokker–Planck
  equation (7.5.31) as an instance of the dCKE-layer `Gardiner.fpRHS`.
-/
import SHSLib.Gardiner.Approx.ReactionXA
import SHSLib.Gardiner.Special

open Finset

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-! ### Combinatorial propensities (7.5.3)–(7.5.8) -/

/-- The combinatorial factor `∏ₐ xₐ!/(xₐ - Nₐ)!` of (7.5.8). -/
def propCount (N : Fin n → ℕ) (x : Fin n → ℕ) : ℝ := ∏ a, ((x a).descFactorial (N a) : ℝ)

/-- The polynomial extension `∏ₐ xₐ(xₐ - 1)⋯(xₐ - Nₐ + 1)` of the combinatorial factor to real
states. -/
def propPoly (N : Fin n → ℕ) (x : Fin n → ℝ) : ℝ := ∏ a, ∏ i ∈ range (N a), (x a - i)

lemma cast_descFactorial_eq_prod (m k : ℕ) :
    (m.descFactorial k : ℝ) = ∏ i ∈ range k, ((m : ℝ) - i) := by
  induction k with
  | zero => simp
  | succ k ih => rw [descFactorial_succ_cast, ih, prod_range_succ]; ring

/-- On lattice points the polynomial propensity is the combinatorial one. -/
theorem propPoly_natCast (N x : Fin n → ℕ) : propPoly N (fun a => (x a : ℝ)) = propCount N x := by
  simp only [propPoly, propCount, cast_descFactorial_eq_prod]

/-- `∏ₐ xₐ!/(xₐ - Nₐ)! ≠ 0` iff `Nₐ ≤ xₐ` for every species. -/
theorem propCount_ne_zero_iff (N x : Fin n → ℕ) : propCount N x ≠ 0 ↔ ∀ a, N a ≤ x a := by
  simp only [propCount, prod_ne_zero_iff, mem_univ, true_implies, Nat.cast_ne_zero, ne_eq,
    Nat.descFactorial_eq_zero_iff_lt, not_lt]

variable {ι : Type*} [Fintype ι] (NA MA : ι → Fin n → ℕ) (kp km : ι → ℝ)

/-- (7.5.5): the stoichiometric change `rᴬ = Mᴬ - Nᴬ`. -/
def stoich (j : ι) (a : Fin n) : ℤ := (MA j a : ℤ) - NA j a

/-- (7.5.8), forward propensity `t⁺_A(x) = k⁺_A ∏ₐ xₐ!/(xₐ - Nₐᴬ)!` (polynomial extension). -/
def tplus (j : ι) (x : Fin n → ℝ) : ℝ := kp j * propPoly (NA j) x

/-- (7.5.8), backward propensity `t⁻_A(x) = k⁻_A ∏ₐ xₐ!/(xₐ - Mₐᴬ)!` (polynomial extension). -/
def tminus (j : ι) (x : Fin n → ℝ) : ℝ := km j * propPoly (MA j) x

omit [Fintype ι] in
/-- (7.5.6): a forward reaction can only fire from `x` if `x - Nᴬ ≥ 0`, and then it leads to
`x + rᴬ = x - Nᴬ + Mᴬ ≥ 0`: the orthant is preserved. -/
theorem orthant_forward (j : ι) (x : Fin n → ℕ) (h : propCount (NA j) x ≠ 0) (a : Fin n) :
    0 ≤ (x a : ℤ) + stoich NA MA j a := by
  have := (propCount_ne_zero_iff _ _).1 h a
  simp only [stoich]; omega

omit [Fintype ι] in
/-- (7.5.7): likewise for the backward reaction `x → x - rᴬ`. -/
theorem orthant_backward (j : ι) (x : Fin n → ℕ) (h : propCount (MA j) x ≠ 0) (a : Fin n) :
    0 ≤ (x a : ℤ) - stoich NA MA j a := by
  have := (propCount_ne_zero_iff _ _).1 h a
  simp only [stoich]; omega

/-! ### (7.5.32): drift and diffusion of the chemical Fokker–Planck equation -/

/-- (7.5.32): `A_a(x) = Σ_A r_aᴬ [t⁺_A(x) - t⁻_A(x)]`. -/
def chemDrift (a : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (stoich NA MA j a : ℝ) * (tplus NA kp j x - tminus MA km j x)

/-- (7.5.32): `B_ab(x) = Σ_A r_aᴬ r_bᴬ [t⁺_A(x) + t⁻_A(x)]`. -/
def chemDiff (a b : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (stoich NA MA j a : ℝ) * (stoich NA MA j b : ℝ) * (tplus NA kp j x + tminus MA km j x)

theorem chemDiff_symm (a b : Fin n) (x : Fin n → ℝ) :
    chemDiff NA MA kp km a b x = chemDiff NA MA kp km b a x := by
  simp only [chemDiff]; exact sum_congr rfl fun j _ => by ring

/-- The diffusion matrix (7.5.32) is positive semidefinite where the propensities are
non-negative: `Σ_{ab} ξ_a B_ab ξ_b = Σ_A (rᴬ·ξ)² (t⁺_A + t⁻_A) ≥ 0`. -/
theorem chemDiff_nonneg (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ tplus NA kp j x + tminus MA km j x)
    (ξ : Fin n → ℝ) : 0 ≤ ∑ a, ∑ b, ξ a * chemDiff NA MA kp km a b x * ξ b := by
  have e : ∑ a, ∑ b, ξ a * chemDiff NA MA kp km a b x * ξ b
      = ∑ j, (∑ a, (stoich NA MA j a : ℝ) * ξ a) ^ 2 * (tplus NA kp j x + tminus MA km j x) := by
    have h1 : ∀ a b, ξ a * chemDiff NA MA kp km a b x * ξ b = ∑ j,
        ((stoich NA MA j a : ℝ) * ξ a) * ((stoich NA MA j b : ℝ) * ξ b)
          * (tplus NA kp j x + tminus MA km j x) := by
      intro a b; simp only [chemDiff, mul_sum, sum_mul]; exact sum_congr rfl fun j _ => by ring
    set g : ι → Fin n → Fin n → ℝ := fun j a b =>
      ((stoich NA MA j a : ℝ) * ξ a) * ((stoich NA MA j b : ℝ) * ξ b)
        * (tplus NA kp j x + tminus MA km j x)
    calc ∑ a, ∑ b, ξ a * chemDiff NA MA kp km a b x * ξ b = ∑ a, ∑ b, ∑ j, g j a b := by
          simp_rw [h1]; rfl
      _ = ∑ a, ∑ j, ∑ b, g j a b := sum_congr rfl fun a _ => sum_comm
      _ = ∑ j, ∑ a, ∑ b, g j a b := sum_comm
      _ = _ := by
          refine sum_congr rfl fun j _ => ?_
          rw [sq, sum_mul_sum, sum_mul]
          refine sum_congr rfl fun a _ => ?_
          rw [sum_mul]
  rw [e]
  exact sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hx j)

/-- **The chemical Fokker–Planck equation (7.5.31)**: the right-hand side
`-Σₐ ∂ₐ[Aₐ P] + ½ Σ_{ab} ∂ₐ∂_b[B_ab P]` with the coefficients (7.5.32), as an instance of the
dCKE-layer Fokker–Planck operator `fpRHS`.  It is the second-order truncation of the
Kramers–Moyal expansion (7.5.30); see `Gardiner.mjGen_sub_mjKM_le` for the truncation error. -/
def chemFPE (p : ℝ → Sp n → ℝ) (t : ℝ) (z : Sp n) : ℝ :=
  fpRHS p (fun w a => chemDrift NA MA kp km a (fun b => w b))
    (fun w a b => chemDiff NA MA kp km a b (fun c => w c)) t z

/-! ### Lattice master equations and the chemical master equation (7.5.9) -/

section Lattice

variable {κ : Type*} (s : Finset κ) (c : κ → (Fin n → ℤ) → ℝ) (w : κ → Fin n → ℤ)

/-- A master equation on the lattice `ℤⁿ` with jumps `x → x + w_j` at rates `c_j(x)`:
`∂ₜP(x) = Σ_j [c_j(x - w_j) P(x - w_j) - c_j(x) P(x)]`. -/
def latME (P : (Fin n → ℤ) → ℝ) (x : Fin n → ℤ) : ℝ :=
  ∑ j ∈ s, (c j (x - w j) * P (x - w j) - c j x * P x)

/-- Its backward generator `(𝓛f)(x) = Σ_j c_j(x) [f(x + w_j) - f(x)]`. -/
def latGen (f : (Fin n → ℤ) → ℝ) (x : Fin n → ℤ) : ℝ := ∑ j ∈ s, c j x * (f (x + w j) - f x)

/-- **Duality**: `Σₓ f(x) (∂ₜP)(x) = Σₓ P(x) (𝓛f)(x)`, by reindexing `x ↦ x - w_j`, assuming
absolute summability of `f(x + w_j) c_j(x) P(x)` and `f(x) c_j(x) P(x)`. -/
theorem tsum_mul_latME (P f : (Fin n → ℤ) → ℝ)
    (h1 : ∀ j ∈ s, Summable fun x => f (x + w j) * (c j x * P x))
    (h2 : ∀ j ∈ s, Summable fun x => f x * (c j x * P x)) :
    ∑' x, f x * latME s c w P x = ∑' x, P x * latGen s c w f x := by
  have hs : ∀ j ∈ s, Summable fun x => f x * (c j (x - w j) * P (x - w j)) := by
    intro j hj
    have := (Equiv.subRight (w j)).summable_iff.2 (h1 j hj)
    refine this.congr fun x => ?_
    simp
  have ht : ∀ j ∈ s, ∑' x, f x * (c j (x - w j) * P (x - w j))
      = ∑' x, f (x + w j) * (c j x * P x) := by
    intro j hj
    rw [← (Equiv.subRight (w j)).tsum_eq (fun x => f (x + w j) * (c j x * P x))]
    simp
  have e1 : ∀ x, f x * latME s c w P x = ∑ j ∈ s, (f x * (c j (x - w j) * P (x - w j))
      - f x * (c j x * P x)) := by
    intro x; simp only [latME, mul_sum]; exact sum_congr rfl fun j _ => by ring
  have e2 : ∀ x, P x * latGen s c w f x = ∑ j ∈ s, (f (x + w j) * (c j x * P x)
      - f x * (c j x * P x)) := by
    intro x; simp only [latGen, mul_sum]; exact sum_congr rfl fun j _ => by ring
  simp_rw [e1, e2]
  rw [Summable.tsum_finsetSum fun j hj => (hs j hj).sub (h2 j hj),
    Summable.tsum_finsetSum fun j hj => (h1 j hj).sub (h2 j hj)]
  refine sum_congr rfl fun j hj => ?_
  rw [(hs j hj).tsum_sub (h2 j hj), (h1 j hj).tsum_sub (h2 j hj), ht j hj]

/-- The first jump moment `Σ_j c_j(x) w_{j,a}` of a lattice master equation. -/
def latDrift (a : Fin n) (x : Fin n → ℤ) : ℝ := ∑ j ∈ s, c j x * (w j a : ℝ)

/-- The second jump moment `Σ_j c_j(x) w_{j,a} w_{j,b}`. -/
def latDiff (a b : Fin n) (x : Fin n → ℤ) : ℝ := ∑ j ∈ s, c j x * (w j a : ℝ) * (w j b : ℝ)

/-- The generator applied to a coordinate is the drift: `𝓛 xₐ = Aₐ(x)`. -/
theorem latGen_coord (a : Fin n) (x : Fin n → ℤ) :
    latGen s c w (fun x => (x a : ℝ)) x = latDrift s c w a x := by
  simp only [latGen, latDrift, Pi.add_apply, Int.cast_add]
  exact sum_congr rfl fun j _ => by ring

/-- The generator applied to a product of coordinates:
`𝓛 (xₐ x_b) = xₐ A_b + x_b Aₐ + B_ab`. -/
theorem latGen_coord_mul (a b : Fin n) (x : Fin n → ℤ) :
    latGen s c w (fun x => (x a : ℝ) * (x b : ℝ)) x
      = (x a : ℝ) * latDrift s c w b x + (x b : ℝ) * latDrift s c w a x
        + latDiff s c w a b x := by
  simp only [latGen, latDrift, latDiff, Pi.add_apply, Int.cast_add, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

end Lattice

/-- The real point of a lattice state. -/
def castZ (x : Fin n → ℤ) : Fin n → ℝ := fun a => (x a : ℝ)

/-- The jumps of the chemical master equation: `+rᴬ` (forward) and `-rᴬ` (backward). -/
def chemJump (p : ι × Bool) : Fin n → ℤ := if p.2 then stoich NA MA p.1 else -stoich NA MA p.1

/-- The rates of the chemical master equation: `t⁺_A` for `+rᴬ`, `t⁻_A` for `-rᴬ`. -/
def chemRate (p : ι × Bool) (x : Fin n → ℤ) : ℝ :=
  if p.2 then tplus NA kp p.1 (castZ x) else tminus MA km p.1 (castZ x)

/-- **The chemical master equation (7.5.9)**. -/
def cme (P : (Fin n → ℤ) → ℝ) (x : Fin n → ℤ) : ℝ :=
  latME Finset.univ (chemRate NA MA kp km) (chemJump NA MA) P x

/-- (7.5.9) written out: `∂ₜP(x) = Σ_A {[t⁻_A(x + rᴬ)P(x + rᴬ) - t⁺_A(x)P(x)]
+ [t⁺_A(x - rᴬ)P(x - rᴬ) - t⁻_A(x)P(x)]}`. -/
theorem cme_eq (P : (Fin n → ℤ) → ℝ) (x : Fin n → ℤ) :
    cme NA MA kp km P x = ∑ j, ((tminus MA km j (castZ (x + stoich NA MA j))
        * P (x + stoich NA MA j) - tplus NA kp j (castZ x) * P x)
      + (tplus NA kp j (castZ (x - stoich NA MA j)) * P (x - stoich NA MA j)
        - tminus MA km j (castZ x) * P x)) := by
  simp only [cme, latME, Fintype.sum_prod_type, Fintype.sum_bool, chemRate, chemJump, if_true,
    Bool.false_eq_true, if_false, sub_neg_eq_add]
  exact sum_congr rfl fun j _ => by ring

/-- The first jump moment of (7.5.9) is the drift (7.5.32). -/
theorem chem_latDrift (a : Fin n) (x : Fin n → ℤ) :
    latDrift Finset.univ (chemRate NA MA kp km) (chemJump NA MA) a x
      = chemDrift NA MA kp km a (castZ x) := by
  simp only [latDrift, chemDrift, Fintype.sum_prod_type, Fintype.sum_bool, chemRate, chemJump,
    if_true, Bool.false_eq_true, if_false, Pi.neg_apply, Int.cast_neg]
  exact sum_congr rfl fun j _ => by ring

/-- The second jump moment of (7.5.9) is the diffusion matrix (7.5.32). -/
theorem chem_latDiff (a b : Fin n) (x : Fin n → ℤ) :
    latDiff Finset.univ (chemRate NA MA kp km) (chemJump NA MA) a b x
      = chemDiff NA MA kp km a b (castZ x) := by
  simp only [latDiff, chemDiff, Fintype.sum_prod_type, Fintype.sum_bool, chemRate, chemJump,
    if_true, Bool.false_eq_true, if_false, Pi.neg_apply, Int.cast_neg]
  exact sum_congr rfl fun j _ => by ring

/-- **The mean equation of the chemical master equation**: under the summability hypotheses of
`tsum_mul_latME`, `Σₓ xₐ ∂ₜP(x) = Σₓ Aₐ(x) P(x)` with `Aₐ` from (7.5.32). -/
theorem cme_mean (P : (Fin n → ℤ) → ℝ) (a : Fin n)
    (h1 : ∀ p : ι × Bool, Summable fun x : Fin n → ℤ =>
      ((x + chemJump NA MA p) a : ℝ) * (chemRate NA MA kp km p x * P x))
    (h2 : ∀ p : ι × Bool, Summable fun x : Fin n → ℤ =>
      (x a : ℝ) * (chemRate NA MA kp km p x * P x)) :
    ∑' x, (x a : ℝ) * cme NA MA kp km P x = ∑' x, P x * chemDrift NA MA kp km a (castZ x) := by
  have := tsum_mul_latME Finset.univ (chemRate NA MA kp km) (chemJump NA MA) P
    (fun x => (x a : ℝ)) (fun p _ => h1 p) (fun p _ => h2 p)
  simp only [cme]
  rw [this]
  simp_rw [latGen_coord, chem_latDrift]

/-- **The second-moment equation of the chemical master equation**:
`Σₓ xₐx_b ∂ₜP(x) = Σₓ [xₐ A_b(x) + x_b Aₐ(x) + B_ab(x)] P(x)`. -/
theorem cme_second_moment (P : (Fin n → ℤ) → ℝ) (a b : Fin n)
    (h1 : ∀ p : ι × Bool, Summable fun x : Fin n → ℤ =>
      ((x + chemJump NA MA p) a : ℝ) * ((x + chemJump NA MA p) b : ℝ)
        * (chemRate NA MA kp km p x * P x))
    (h2 : ∀ p : ι × Bool, Summable fun x : Fin n → ℤ =>
      (x a : ℝ) * (x b : ℝ) * (chemRate NA MA kp km p x * P x)) :
    ∑' x, (x a : ℝ) * (x b : ℝ) * cme NA MA kp km P x
      = ∑' x, P x * ((x a : ℝ) * chemDrift NA MA kp km b (castZ x)
          + (x b : ℝ) * chemDrift NA MA kp km a (castZ x) + chemDiff NA MA kp km a b (castZ x)) := by
  have := tsum_mul_latME Finset.univ (chemRate NA MA kp km) (chemJump NA MA) P
    (fun x => (x a : ℝ) * (x b : ℝ)) (fun p _ => h1 p) (fun p _ => h2 p)
  simp only [cme]
  rw [this]
  simp_rw [latGen_coord_mul, chem_latDrift, chem_latDiff]

end Gardiner
