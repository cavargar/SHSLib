/-
# Itô stochastic differential equations: definitions and the basic `L²` estimate

Gardiner §4.3.1, (4.3.3)–(4.3.4), (4.3.10)–(4.3.11).  For a Wiener process `W` with respect to a
filtration `𝓕` (`Gardiner.Ito.IsFWiener W 𝓕 P`) and coefficients `a(x, t)`, `b(x, t)`:

* `SDECoeffs a b t₀ T K`: the Lipschitz condition (4.3.10) and the growth condition (4.3.11) on
  `[t₀, T]` (together with joint measurability of `a` and `b`, and `K ≥ 0`);
* `drive t₀ b x`: the Itô integrand `s ↦ 1_{s > t₀} b(x(s), s)`, so that
  `∫_{t₀}^t b(x(s), s) dW(s) = itoInt W 𝓕 P t (drive t₀ b x)`;
* `IsSDESol W 𝓕 P a b t₀ T ξ x`: `x` is a solution of the integral equation (4.3.4) on `[t₀, T]`
  with `x(t₀) = ξ`: jointly measurable, adapted, with almost surely continuous paths, square
  integrable on `(t₀, T] × Ω`, and for every `t ∈ [t₀, T]`, almost surely,
  `x(t) = ξ + ∫_{t₀}^t a(x(s), s) ds + ∫_{t₀}^t b(x(s), s) dW(s)`.

The main estimate is `sup_sq_le`: if `Y(u) = ζ + ∫_{t₀}^u A ds + ∫_{t₀}^u B dW` for all `u`, then
`E sup_{t₀ ≤ u ≤ t} |Y(u)|² ≤ 3 E ζ² + 3 (t - t₀) ∫_{t₀}^t E A² + 12 ∫_{t₀}^t E B²`.
-/
import SHSLib.Gardiner.Ito.StochDE.ContIto
import SHSLib.Gardiner.Ito.StochDE.Gronwall

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-! ### Coefficients -/

/-- **The conditions (4.3.10)–(4.3.11)** on `[t₀, T]`: the Lipschitz condition
`|a(x,t) - a(y,t)| + |b(x,t) - b(y,t)| ≤ K |x - y|` and the growth condition
`|a(x,t)|² + |b(x,t)|² ≤ K² (1 + |x|²)`, with `a`, `b` jointly measurable. -/
structure SDECoeffs (a b : ℝ → ℝ → ℝ) (t₀ T K : ℝ) : Prop where
  measurable_a : Measurable (Function.uncurry a)
  measurable_b : Measurable (Function.uncurry b)
  K_nonneg : 0 ≤ K
  lipschitz : ∀ t ∈ Set.Icc t₀ T, ∀ x y, |a x t - a y t| + |b x t - b y t| ≤ K * |x - y|
  growth : ∀ t ∈ Set.Icc t₀ T, ∀ x, |a x t| ^ 2 + |b x t| ^ 2 ≤ K ^ 2 * (1 + |x| ^ 2)

namespace SDECoeffs

variable {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} (hc : SDECoeffs a b t₀ T K)
include hc

lemma lip_a {t : ℝ} (ht : t ∈ Set.Icc t₀ T) (x y : ℝ) : |a x t - a y t| ≤ K * |x - y| :=
  le_trans (le_add_of_nonneg_right (abs_nonneg _)) (hc.lipschitz t ht x y)

lemma lip_b {t : ℝ} (ht : t ∈ Set.Icc t₀ T) (x y : ℝ) : |b x t - b y t| ≤ K * |x - y| :=
  le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hc.lipschitz t ht x y)

lemma sq_a_le {t : ℝ} (ht : t ∈ Set.Icc t₀ T) (x : ℝ) : a x t ^ 2 ≤ K ^ 2 * (1 + x ^ 2) := by
  have := hc.growth t ht x
  simp only [sq_abs] at this
  nlinarith [sq_nonneg (b x t)]

lemma sq_b_le {t : ℝ} (ht : t ∈ Set.Icc t₀ T) (x : ℝ) : b x t ^ 2 ≤ K ^ 2 * (1 + x ^ 2) := by
  have := hc.growth t ht x
  simp only [sq_abs] at this
  nlinarith [sq_nonneg (a x t)]

omit hc in
lemma abs_le_of_sq_le' {u K x : ℝ} (hK : 0 ≤ K) (h : u ^ 2 ≤ K ^ 2 * (1 + x ^ 2)) :
    |u| ≤ K * (1 + |x|) := by
  have h1 : u ^ 2 ≤ (K * (1 + |x|)) ^ 2 := by
    refine h.trans ?_
    have : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left this (sq_nonneg K)
  have h2 : 0 ≤ K * (1 + |x|) := by positivity
  by_contra hlt
  push_neg at hlt
  nlinarith [sq_abs u, abs_nonneg u]

lemma abs_a_le {t : ℝ} (ht : t ∈ Set.Icc t₀ T) (x : ℝ) : |a x t| ≤ K * (1 + |x|) :=
  abs_le_of_sq_le' hc.K_nonneg (hc.sq_a_le ht x)

lemma abs_b_le {t : ℝ} (ht : t ∈ Set.Icc t₀ T) (x : ℝ) : |b x t| ≤ K * (1 + |x|) :=
  abs_le_of_sq_le' hc.K_nonneg (hc.sq_b_le ht x)

lemma driftCoeff : DriftCoeff a t₀ T K where
  measurable := hc.measurable_a
  cont s hs := by
    refine LipschitzWith.continuous (K := K.toNNReal) (LipschitzWith.of_dist_le_mul fun x y => ?_)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hc.K_nonneg]
    exact hc.lip_a hs x y
  growth s hs y := hc.abs_a_le hs y

lemma mono {T' : ℝ} (hT' : T' ≤ T) : SDECoeffs a b t₀ T' K where
  measurable_a := hc.measurable_a
  measurable_b := hc.measurable_b
  K_nonneg := hc.K_nonneg
  lipschitz t ht := hc.lipschitz t ⟨ht.1, ht.2.trans hT'⟩
  growth t ht := hc.growth t ⟨ht.1, ht.2.trans hT'⟩

end SDECoeffs

/-! ### Solutions -/

/-- The Itô integrand `s ↦ 1_{s > t₀} b(x(s), s)` of the noise term of (4.3.4). -/
def drive (t₀ : ℝ) (b : ℝ → ℝ → ℝ) (x : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  afterInd t₀ s * b (x s ω) s

/-- **A solution of the Itô SDE (4.3.3) on `[t₀, T]`**, i.e. of the integral equation (4.3.4)
`x(t) = x(t₀) + ∫_{t₀}^t a[x(t'), t'] dt' + ∫_{t₀}^t b[x(t'), t'] dW(t')`, with initial value
`x(t₀) = ξ`.  The solution is jointly measurable, nonanticipating (adapted), has almost surely
continuous paths on `[t₀, T]`, and is square integrable on `(t₀, T] × Ω`. -/
structure IsSDESol (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (a b : ℝ → ℝ → ℝ)
    (t₀ T : ℝ) (ξ : Ω → ℝ) (x : ℝ → Ω → ℝ) : Prop where
  measurable : Measurable (Function.uncurry x)
  adapted : ∀ t ∈ Set.Icc t₀ T, StronglyMeasurable[𝓕 t] (x t)
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => x t ω) (Set.Icc t₀ T)
  sq_int : ∫⁻ s in Set.Ioc t₀ T, ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P < ⊤
  eq : ∀ t ∈ Set.Icc t₀ T, x t =ᵐ[P] fun ω =>
    ξ ω + (∫ s in t₀..t, a (x s ω) s) + itoInt W 𝓕 P t (drive t₀ b x) ω

/-! ### Elementary `ℝ≥0∞` inequalities -/

lemma ennreal_add_sq_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp [ENNReal.top_pow, ENNReal.mul_top]
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp [ENNReal.top_pow, ENNReal.mul_top]
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((x : ℝ) - y)]

lemma ennreal_add3_sq_le (x y z : ℝ≥0∞) :
    (x + y + z) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp [ENNReal.top_pow, ENNReal.mul_top]
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp [ENNReal.top_pow, ENNReal.mul_top]
  rcases eq_or_ne z ⊤ with rfl | hz
  · simp [ENNReal.top_pow, ENNReal.mul_top]
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  lift z to ℝ≥0 using hz
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((x : ℝ) - y), sq_nonneg ((y : ℝ) - z), sq_nonneg ((x : ℝ) - z)]

/-- Cauchy–Schwarz: `(∫⁻ f)² ≤ μ(univ) ∫⁻ f²`. -/
lemma lintegral_sq_le_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) : (∫⁻ a, f a ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ a, f a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun _ => 1) (g := f) aemeasurable_const hf
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, ENNReal.rpow_two, one_pow,
    one_mul] at h
  have e : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
    rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
    exact ENNReal.rpow_inv_natCast_pow (by norm_num) x
  calc (∫⁻ a, f a ∂μ) ^ 2 ≤ (μ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = μ Set.univ * ∫⁻ a, f a ^ 2 ∂μ := by rw [mul_pow, e, e]

lemma ofReal_integral_le_lintegral_enorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) : ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ‖f a‖ₑ ∂μ :=
  (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    (by rw [← Real.enorm_eq_ofReal_abs]; exact enorm_integral_le_lintegral_enorm f)

end Gardiner.Ito.StochDE
