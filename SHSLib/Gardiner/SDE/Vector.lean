/-
# Vector stochastic differential equations: notation, double integrals and vector algorithms
(Gardiner §10.5.1–§10.5.6)

We work with `d` variables and `m` noises, `x : Fin d → ℝ`, drift `A : (Fin d → ℝ) → Fin d → ℝ`
and noise matrix `B : (Fin d → ℝ) → Fin d → Fin m → ℝ` (time-homogeneous; explicit time dependence
plays no role in the algebra below).

* **Operators (10.5.3), coefficients (10.5.24), commutative noise (10.5.15)–(10.5.18).**
  `Lⱼf = Σₖ B_{kj} ∂ₖf` (`Gardiner.SDE.Lj`, with the true Fréchet partial derivatives),
  `C_{ijj'} = L_{j'}B_{ij}` (`Gardiner.SDE.Ccoef`), and commutative noise
  `C_{ijj'} = C_{ij'j}` (`Gardiner.SDE.IsCommutativeNoise`).  Additive noise has `C = 0`
  (`Gardiner.SDE.additive_C_zero`), a single noise is commutative
  (`Gardiner.SDE.single_noise_commutative`), and `B_{ij} = xᵢG_{ij}` has
  `C_{ijj'} = xᵢG_{ij}G_{ij'}` (10.5.18) (`Gardiner.SDE.diagForm_C`,
  `Gardiner.SDE.diagForm_commutative`).
* **Double integrals (10.5.6)–(10.5.14), Itô-free.**  For arbitrary discrete increments
  `δⁿ_a` of two noise components, the left-point double sums `I_{ab} = Σₙ S^b_n δ^a_n` satisfy
  `I_{ab} + I_{ba} = ΔW_aΔW_b - Σₙ δ^a_n δ^b_n` (`Gardiner.SDE.double_sum_symm`), the discrete
  form of (10.5.8)–(10.5.10), which becomes (10.5.10) given the quadratic covariation
  `Σₙ δ^a_n δ^b_n = δ_{ab}(t - t₀)`.  With `E_{ab} = I_{ab} - I_{ba}` (10.5.13) this gives
  `I_{ab} = ½(ΔW_aΔW_b - Σδ^aδ^b + E_{ab})` (`Gardiner.SDE.double_sum_decomp`), i.e. (10.5.26).
  **Erratum (10.5.14)**: the printed formula omits `-δ_{ij}(t - t₀)`
  (`Gardiner.SDE.eq_10_5_14_printed_wrong`).
* **Vector Euler (10.5.20) and Milstein (10.5.23)** as maps driven by given increments `ΔW` and
  given double integrals `ΔW_{jj'}` (`Gardiner.SDE.vecEuler`, `Gardiner.SDE.vecMilstein`).
  Substituting (10.5.26) splits Milstein into a symmetric part and `½ΣC_{ijj'}E_{jj'}`
  (`Gardiner.SDE.vecMilstein_decomp`); for commutative noise and antisymmetric `E` the `E`-term
  vanishes, so the scheme needs only the increments (`Gardiner.SDE.vecMilstein_commutative`).
* **Strong semi-implicit (10.5.28)–(10.5.34).**  Matching the second-order expansion of the
  midpoint scheme against Milstein requires the coefficient `½` in front of `ΣC̄E`
  (`Gardiner.SDE.strong_semi_matches_milstein`); **erratum (10.5.34)**: the printed coefficient
  is `1` (`Gardiner.SDE.eq_10_5_34_printed_wrong`).
* **Weak semi-implicit (10.5.35)–(10.5.41).**  The two forms of the midpoint scheme — the
  defining form `ȳ = ½(y + y')`, `y' = y + F(ȳ)` and the computer form
  `ȳ = y + ½F(ȳ)`, `y' = 2ȳ - y` of (10.4.16)–(10.4.17) — are equivalent
  (`Gardiner.SDE.midpoint_forms_equiv`).  **Erratum (10.5.40)**: in the computer form the
  left-hand side of (10.5.40) must be `ȳⁿᵢ` and the increments carry a factor `½`, as in
  (10.4.16); as printed, (10.5.40) together with (10.5.41) does not determine `ȳ`.  The omitted
  term has mean zero given `⟨E⟩ = 0` (`Gardiner.SDE.E_term_mean_zero`).
-/
import SHSLib.Gardiner.SDE.Schemes

open MeasureTheory Finset

noncomputable section

namespace Gardiner.SDE

variable {d m : ℕ}

/-! ### Operators and commutative noise -/

/-- The partial derivative `∂ₖf(x)`. -/
def pd (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (k : Fin d) : ℝ := fderiv ℝ f x (Pi.single k 1)

/-- (10.5.3) `Lⱼf = Σₖ B_{kj} ∂ₖf`. -/
def Lj (B : (Fin d → ℝ) → Fin d → Fin m → ℝ) (j : Fin m) (f : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ := ∑ k, B x k j * pd f x k

/-- (10.5.24) `C_{ijj'} = Σₖ B_{kj'} ∂ₖB_{ij} = L_{j'}B_{ij}`. -/
def Ccoef (B : (Fin d → ℝ) → Fin d → Fin m → ℝ) (x : Fin d → ℝ) (i : Fin d) (j j' : Fin m) : ℝ :=
  Lj B j' (fun y => B y i j) x

/-- (10.5.15)–(10.5.16) Commutative noise: `L_{j'}B_{ij} = LⱼB_{ij'}`. -/
def IsCommutativeNoise (B : (Fin d → ℝ) → Fin d → Fin m → ℝ) : Prop :=
  ∀ x i j j', Ccoef B x i j j' = Ccoef B x i j' j

/-- Case i): additive noise (`B` independent of `x`) has `C = 0`. -/
theorem additive_C_zero (G : Fin d → Fin m → ℝ) (x : Fin d → ℝ) (i : Fin d) (j j' : Fin m) :
    Ccoef (fun _ => G) x i j j' = 0 := by
  simp [Ccoef, Lj, pd]

theorem additive_commutative (G : Fin d → Fin m → ℝ) : IsCommutativeNoise (fun _ => G) :=
  fun x i j j' => by rw [additive_C_zero, additive_C_zero]

/-- Case ii): a single noise is commutative. -/
theorem single_noise_commutative (B : (Fin d → ℝ) → Fin d → Fin 1 → ℝ) : IsCommutativeNoise B :=
  fun x i j j' => by rw [Subsingleton.elim j j']

/-- The noise matrix `B_{ij}(x) = xᵢG_{ij}` of (10.5.17). -/
def diagForm (G : Fin d → Fin m → ℝ) (x : Fin d → ℝ) (i : Fin d) (j : Fin m) : ℝ := x i * G i j

/-- (10.5.18) `C_{ijj'} = xᵢG_{ij}G_{ij'}` for `B_{ij} = xᵢG_{ij}`. -/
theorem diagForm_C (G : Fin d → Fin m → ℝ) (x : Fin d → ℝ) (i : Fin d) (j j' : Fin m) :
    Ccoef (diagForm G) x i j j' = x i * G i j * G i j' := by
  have hd : ∀ k, pd (fun y => diagForm G y i j) x k = G i j * Pi.single (M := fun _ => ℝ) k 1 i := by
    intro k
    have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt
      (x := x)).mul_const (G i j)
    simp only [pd, diagForm]
    rw [show (fun y : Fin d → ℝ => y i * G i j) =
      fun y => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) y * G i j from rfl, h.fderiv]
    simp
  simp only [Ccoef, Lj]
  simp only [hd]
  simp only [diagForm]
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro k _ hk; rw [Pi.single_eq_of_ne hk.symm]; ring
  · simp

/-- Case iii): `B_{ij} = xᵢG_{ij}` gives commutative noise. -/
theorem diagForm_commutative (G : Fin d → Fin m → ℝ) : IsCommutativeNoise (diagForm G) :=
  fun x i j j' => by rw [diagForm_C, diagForm_C]; ring

/-! ### Double integrals (10.5.6)–(10.5.14), Itô-free -/

/-- Left-point double sum `I_{ab} = Σ_{n<N} S^b_n δ^a_n` (discrete `∫dW_a ∫dW_b`). -/
def dsum (δa δb : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ range N, psum δb n * δa n

/-- Discrete (10.5.8)–(10.5.10): `I_{ab} + I_{ba} = ΔW_aΔW_b - Σ δ^a δ^b`. -/
theorem double_sum_symm (δa δb : ℕ → ℝ) (N : ℕ) :
    dsum δa δb N + dsum δb δa N = psum δa N * psum δb N - ∑ n ∈ range N, δa n * δb n := by
  induction N with
  | zero => simp [dsum, psum]
  | succ N ih =>
    simp only [dsum, sum_range_succ] at ih ⊢
    simp only [psum, sum_range_succ] at ih ⊢
    linear_combination ih

/-- (10.5.13)–(10.5.14) corrected, = (10.5.26): with `E_{ab} = I_{ab} - I_{ba}`,
`I_{ab} = ½(ΔW_aΔW_b - Σδ^aδ^b + E_{ab})`. -/
theorem double_sum_decomp (δa δb : ℕ → ℝ) (N : ℕ) :
    dsum δa δb N = 1 / 2 * (psum δa N * psum δb N - ∑ n ∈ range N, δa n * δb n +
      (dsum δa δb N - dsum δb δa N)) := by
  linear_combination (1 / 2 : ℝ) * double_sum_symm δa δb N

/-- (10.5.10) given the quadratic covariation `Σδ^aδ^b = q`. -/
theorem double_sum_symm_of_qv (δa δb : ℕ → ℝ) (N : ℕ) {q : ℝ}
    (hq : ∑ n ∈ range N, δa n * δb n = q) :
    dsum δa δb N + dsum δb δa N = psum δa N * psum δb N - q := by
  rw [double_sum_symm, hq]

/-- **Erratum (10.5.14)**: `I_{ij} = ½(ΔWᵢΔWⱼ + E_{ij})` fails for `i = j`: with one step of size
`δ = 1`, `I_{aa} = 0`, `E_{aa} = 0` but `½ΔW_a² = ½`. -/
theorem eq_10_5_14_printed_wrong :
    ¬ ∀ (δa δb : ℕ → ℝ) (N : ℕ),
      dsum δa δb N = 1 / 2 * (psum δa N * psum δb N + (dsum δa δb N - dsum δb δa N)) := by
  intro h
  have := h (fun _ => 1) (fun _ => 1) 1
  norm_num [dsum, psum] at this

/-! ### Vector Euler and Milstein -/

/-- (10.5.20) Vector Euler. -/
def vecEuler (A : (Fin d → ℝ) → Fin d → ℝ) (B : (Fin d → ℝ) → Fin d → Fin m → ℝ) (τ : ℝ)
    (y : Fin d → ℝ) (dW : Fin m → ℝ) (i : Fin d) : ℝ :=
  y i + A y i * τ + ∑ k, B y i k * dW k

/-- (10.5.23) Vector Milstein, driven by given increments `ΔW` and given double integrals
`ΔW_{jj'}` (10.5.25). -/
def vecMilstein (A : (Fin d → ℝ) → Fin d → ℝ) (B : (Fin d → ℝ) → Fin d → Fin m → ℝ) (τ : ℝ)
    (y : Fin d → ℝ) (dW : Fin m → ℝ) (I : Fin m → Fin m → ℝ) (i : Fin d) : ℝ :=
  vecEuler A B τ y dW i + ∑ j, ∑ j', Ccoef B y i j j' * I j j'

/-- (10.5.26) substituted in (10.5.23). -/
theorem vecMilstein_decomp (A : (Fin d → ℝ) → Fin d → ℝ) (B : (Fin d → ℝ) → Fin d → Fin m → ℝ)
    (τ : ℝ) (y : Fin d → ℝ) (dW : Fin m → ℝ) (E : Fin m → Fin m → ℝ) (i : Fin d) :
    vecMilstein A B τ y dW (fun j j' => 1 / 2 * (dW j * dW j' - τ * (if j = j' then 1 else 0) +
      E j j')) i =
    vecEuler A B τ y dW i +
      1 / 2 * ∑ j, ∑ j', Ccoef B y i j j' * (dW j * dW j' - τ * (if j = j' then 1 else 0)) +
      1 / 2 * ∑ j, ∑ j', Ccoef B y i j j' * E j j' := by
  simp only [vecMilstein]
  rw [add_assoc]; congr 1
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun j' _ => by ring

/-- A symmetric array contracted with an antisymmetric one vanishes. -/
lemma sum_symm_antisymm {C E : Fin m → Fin m → ℝ} (hC : ∀ j j', C j j' = C j' j)
    (hE : ∀ j j', E j j' = -E j' j) : ∑ j, ∑ j', C j j' * E j j' = 0 := by
  have h : ∑ j, ∑ j', C j j' * E j j' = -∑ j, ∑ j', C j j' * E j j' := by
    conv_rhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j' _ => ?_
    rw [hC, hE]; ring
  linarith

/-- **Commutative noise**: the vector Milstein scheme needs only the increments. -/
theorem vecMilstein_commutative {A : (Fin d → ℝ) → Fin d → ℝ}
    {B : (Fin d → ℝ) → Fin d → Fin m → ℝ} (hB : IsCommutativeNoise B) (τ : ℝ) (y : Fin d → ℝ)
    (dW : Fin m → ℝ) {E : Fin m → Fin m → ℝ} (hE : ∀ j j', E j j' = -E j' j) (i : Fin d) :
    vecMilstein A B τ y dW (fun j j' => 1 / 2 * (dW j * dW j' - τ * (if j = j' then 1 else 0) +
      E j j')) i =
    vecEuler A B τ y dW i +
      1 / 2 * ∑ j, ∑ j', Ccoef B y i j j' * (dW j * dW j' - τ * (if j = j' then 1 else 0)) := by
  rw [vecMilstein_decomp, sum_symm_antisymm (fun j j' => hB y i j j') hE]; ring

/-! ### Semi-implicit algorithms -/

/-- **Strong semi-implicit vs Milstein (10.5.28)–(10.5.34).**  To second order the midpoint
evaluation `B̄ΔW` contributes `BΔW + ½Σ_{jj'}C_{ijj'}ΔWⱼΔW_{j'}` (symmetric in `j, j'`), and
`Ā̄ = A - ½ΣⱼC_{ijj}` (10.5.31).  The resulting step equals the vector Milstein step with
`ΔW_{jj'} = ½(ΔWⱼΔW_{j'} - τδ_{jj'} + E_{jj'})` **iff** the `E`-term carries the factor `½`. -/
theorem strong_semi_matches_milstein (A : (Fin d → ℝ) → Fin d → ℝ)
    (B : (Fin d → ℝ) → Fin d → Fin m → ℝ) (τ : ℝ) (y : Fin d → ℝ) (dW : Fin m → ℝ)
    (E : Fin m → Fin m → ℝ) (i : Fin d) :
    y i + (A y i - 1 / 2 * ∑ j, Ccoef B y i j j) * τ + (∑ k, B y i k * dW k +
      1 / 2 * ∑ j, ∑ j', Ccoef B y i j j' * (dW j * dW j')) +
      1 / 2 * ∑ j, ∑ j', Ccoef B y i j j' * E j j' =
    vecMilstein A B τ y dW (fun j j' => 1 / 2 * (dW j * dW j' - τ * (if j = j' then 1 else 0) +
      E j j')) i := by
  rw [vecMilstein_decomp]
  simp only [vecEuler, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq,
    mem_univ, if_true]
  rw [← Finset.sum_mul]
  ring

/-- **Erratum (10.5.34)**: with the printed coefficient `1` in front of `ΣC̄E`, the step differs
from Milstein by exactly `½Σ_{jj'}C_{ijj'}E_{jj'}`, which is nonzero in general for
non-commutative noise. -/
theorem eq_10_5_34_printed_wrong (A : (Fin d → ℝ) → Fin d → ℝ)
    (B : (Fin d → ℝ) → Fin d → Fin m → ℝ) (τ : ℝ) (y : Fin d → ℝ) (dW : Fin m → ℝ)
    (E : Fin m → Fin m → ℝ) (i : Fin d) :
    (y i + (A y i - 1 / 2 * ∑ j, Ccoef B y i j j) * τ + (∑ k, B y i k * dW k +
      1 / 2 * ∑ j, ∑ j', Ccoef B y i j j' * (dW j * dW j')) +
      ∑ j, ∑ j', Ccoef B y i j j' * E j j') -
    vecMilstein A B τ y dW (fun j j' => 1 / 2 * (dW j * dW j' - τ * (if j = j' then 1 else 0) +
      E j j')) i = 1 / 2 * ∑ j, ∑ j', Ccoef B y i j j' * E j j' := by
  rw [← strong_semi_matches_milstein]; ring

/-- The two forms of a midpoint scheme with increment map `F`:
`(ȳ = ½(y + y') ∧ y' = y + F ȳ) ↔ (ȳ = y + ½F ȳ ∧ y' = 2ȳ - y)`
((10.4.12)–(10.4.15) ↔ (10.4.16)–(10.4.17), and (10.5.28)–(10.5.40) ↔ corrected
(10.5.40)–(10.5.41)). -/
theorem midpoint_forms_equiv (F : (Fin d → ℝ) → Fin d → ℝ) (y y' ybar : Fin d → ℝ) :
    (ybar = (1 / 2 : ℝ) • (y + y') ∧ y' = y + F ybar) ↔
      (ybar = y + (1 / 2 : ℝ) • F ybar ∧ y' = (2 : ℝ) • ybar - y) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> funext i <;> have a := congrFun h1 i <;> have b := congrFun h2 i <;>
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a b ⊢ <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> funext i <;> have a := congrFun h1 i <;> have b := congrFun h2 i <;>
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a b ⊢ <;> linarith

section WeakSemi

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The term omitted by the weak semi-implicit scheme has mean zero when the antisymmetric
integrals have mean zero (with frozen coefficients `C`). -/
theorem E_term_mean_zero (C : Fin m → Fin m → ℝ) {E : Fin m → Fin m → Ω → ℝ}
    (hEi : ∀ j j', Integrable (E j j') P) (hE0 : ∀ j j', ∫ ω, E j j' ω ∂P = 0) :
    ∫ ω, 1 / 2 * ∑ j, ∑ j', C j j' * E j j' ω ∂P = 0 := by
  rw [integral_const_mul, integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun j' _ => (hEi j j').const_mul _]
  simp only [mul_eq_zero]; right
  refine sum_eq_zero fun j _ => ?_
  rw [integral_finset_sum _ fun j' _ => (hEi j j').const_mul _]
  exact sum_eq_zero fun j' _ => by rw [integral_const_mul, hE0, mul_zero]

end WeakSemi

/-! ### Instances -/

/-- Instance of (10.5.17)–(10.5.18) with `d = m = 2`, `G = [[1, 2], [3, 4]]`, at `x = (1, -1)`:
`C_{1,1,2} = x₁G₁₁G₁₂ = 2`, and the noise is commutative. -/
example : Ccoef (diagForm (m := 2) ![![1, 2], ![3, 4]]) ![1, -1] 0 0 1 = 2 ∧
    IsCommutativeNoise (diagForm (m := 2) ![![1, 2], ![3, 4]]) := by
  refine ⟨?_, diagForm_commutative _⟩
  rw [diagForm_C]; norm_num

/-- Instance of `Gardiner.SDE.vecMilstein_commutative` for `B_{ij} = xᵢG_{ij}` with two noises. -/
example (A : (Fin 2 → ℝ) → Fin 2 → ℝ) (τ : ℝ) (y : Fin 2 → ℝ) (dW : Fin 2 → ℝ) (e : ℝ) (i : Fin 2) :
    vecMilstein A (diagForm ![![1, 2], ![3, 4]]) τ y dW
      (fun j j' => 1 / 2 * (dW j * dW j' - τ * (if j = j' then 1 else 0) + !![0, e; -e, 0] j j')) i =
    vecEuler A (diagForm ![![1, 2], ![3, 4]]) τ y dW i +
      1 / 2 * ∑ j, ∑ j', Ccoef (diagForm ![![1, 2], ![3, 4]]) y i j j' *
        (dW j * dW j' - τ * (if j = j' then 1 else 0)) :=
  vecMilstein_commutative (diagForm_commutative _) τ y dW
    (fun j j' => by fin_cases j <;> fin_cases j' <;> simp) i

end Gardiner.SDE
