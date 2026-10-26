/-
# Laplace's method with explicit error terms

Toolkit for the small-`D` asymptotics of Gardiner, *Handbook of Stochastic Methods*, §5.2.7 c)
and Ch. 9: integrals `∫ exp(-W(z)/D) dz` where `W ≥ 0` vanishes at one point `m` only.  All
statements carry an explicit error term `C·D` (or `C·D²`) valid for every `0 < D ≤ 1`.

* `Gardiner.Escape.laplace_core` — the one-sided Gaussian estimate: if
  `|V(s) - k s²/2| ≤ M s³` on `[0, r]` (`M r ≤ k/4`), then
  `|∫₀ʳ e^{-V(s)/D} ds - ½√(2πD/k)| ≤ 8MD/k² + √(πD/k) e^{-kr²/(4D)}`.
* `Gardiner.Escape.laplace_far` — on a set `S` where `W ≥ η` away from a compact window, the
  window carries everything up to `e^{η} η⁻¹ (∫_S e^{-W}) D`.
* `Gardiner.Escape.laplace_min` — **two-sided Laplace method**:
  `|∫_S e^{-W/D} - √(2πD/k)| ≤ C D`.
* `Gardiner.Escape.laplace_min_half` — the window is cut at the minimum (half Gaussian):
  `|∫_S e^{-W/D} - ½√(2πD/k)| ≤ C D`.
* `Gardiner.Escape.laplace_endpoint` — **endpoint Laplace method** (linear vanishing,
  `W(x₀ - s) ≈ g s`): `|∫_{lo}^{x₀} e^{-W/D} - D/g| ≤ C D²`.
* `Gardiner.Escape.laplace_gauss_tail` — the window is cut at `b - y₀√D`:
  `|∫_{lo}^{b - y₀√D} e^{-W/D} - √D ∫_{y₀}^∞ e^{-k t²/2} dt| ≤ C D`.

The relative errors are therefore `O(√D)` (Gaussian case) and `O(D)` (endpoint case).
-/
import Mathlib

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-! ### Elementary exponential estimates -/

/-- `|e^{-x} - e^{-y}| ≤ |x - y| e^{-m}` for `x, y ≥ m`. -/
lemma abs_exp_neg_sub_le {x y m : ℝ} (hx : m ≤ x) (hy : m ≤ y) :
    |exp (-x) - exp (-y)| ≤ |x - y| * exp (-m) := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this hy hx (le_of_not_ge hxy)
  have h1 : exp (-y) = exp (-x) * exp (-(y - x)) := by rw [← exp_add]; ring_nf
  have h2 : 1 - exp (-(y - x)) ≤ y - x := by linarith [add_one_le_exp (-(y - x))]
  have h3 : 0 ≤ 1 - exp (-(y - x)) := by
    have : exp (-(y - x)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    linarith
  have hd : exp (-x) - exp (-y) = exp (-x) * (1 - exp (-(y - x))) := by rw [h1]; ring
  rw [hd, abs_of_nonneg (mul_nonneg (exp_pos _).le h3), abs_of_nonpos (by linarith)]
  calc exp (-x) * (1 - exp (-(y - x))) ≤ exp (-m) * (y - x) :=
        mul_le_mul (exp_le_exp.mpr (by linarith)) h2 h3 (exp_pos _).le
    _ = -(x - y) * exp (-m) := by ring

/-- `e^{-x} ≤ 1/x` for `x > 0`. -/
lemma exp_neg_le_inv {x : ℝ} (hx : 0 < x) : exp (-x) ≤ x⁻¹ := by
  rw [exp_neg]
  exact inv_anti₀ hx (by linarith [add_one_le_exp x])

/-- `e^{-x} ≤ 2/x²` for `x > 0`. -/
lemma exp_neg_le_two_div_sq {x : ℝ} (hx : 0 < x) : exp (-x) ≤ 2 / x ^ 2 := by
  rw [exp_neg]
  have h := Real.quadratic_le_exp_of_nonneg hx.le
  rw [show (2 : ℝ) / x ^ 2 = (x ^ 2 / 2)⁻¹ by field_simp]
  exact inv_anti₀ (by positivity) (by linarith)

/-- `e^{-c/D} ≤ D/c`. -/
lemma exp_neg_div_le {c D : ℝ} (hc : 0 < c) (hD : 0 < D) : exp (-(c / D)) ≤ D / c := by
  have := exp_neg_le_inv (div_pos hc hD)
  rwa [inv_div] at this

/-- `e^{-c/D} ≤ 2D²/c²`. -/
lemma exp_neg_div_le_sq {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    exp (-(c / D)) ≤ 2 * D ^ 2 / c ^ 2 := by
  have := exp_neg_le_two_div_sq (div_pos hc hD)
  rwa [div_pow, div_div_eq_mul_div] at this

/-! ### Moment integrals by the fundamental theorem of calculus -/

/-- `∫₀ʳ s³ e^{-cs²} ds ≤ 1/(2c²)`. -/
lemma integral_cube_gauss_le {c : ℝ} (r : ℝ) (hc : 0 < c) :
    ∫ s in (0 : ℝ)..r, s ^ 3 * exp (-(c * s ^ 2)) ≤ 1 / (2 * c ^ 2) := by
  have hF : ∀ s ∈ uIcc 0 r, HasDerivAt
      (fun s => -(c * s ^ 2 + 1) * exp (-(c * s ^ 2)) / (2 * c ^ 2))
      (s ^ 3 * exp (-(c * s ^ 2))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -(c * s ^ 2)) (-(c * (2 * s))) s := by
      simpa using ((hasDerivAt_pow 2 s).const_mul c).fun_neg
    have h2 := h1.exp
    have h3 : HasDerivAt (fun s => -(c * s ^ 2 + 1)) (-(c * (2 * s))) s := by
      simpa using (((hasDerivAt_pow 2 s).const_mul c).add_const 1).fun_neg
    convert (h3.mul h2).div_const (2 * c ^ 2) using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have : 0 ≤ (c * r ^ 2 + 1) * exp (-(c * r ^ 2)) / (2 * c ^ 2) := by positivity
  have e : -(c * r ^ 2 + 1) * exp (-(c * r ^ 2)) / (2 * c ^ 2)
      - -(c * 0 ^ 2 + 1) * exp (-(c * 0 ^ 2)) / (2 * c ^ 2)
      = 1 / (2 * c ^ 2) - (c * r ^ 2 + 1) * exp (-(c * r ^ 2)) / (2 * c ^ 2) := by
    simp; ring
  rw [e]; linarith

/-- `∫₀ʳ s² e^{-cs} ds ≤ 2/c³`. -/
lemma integral_sq_exp_le {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    ∫ s in (0 : ℝ)..r, s ^ 2 * exp (-(c * s)) ≤ 2 / c ^ 3 := by
  have hF : ∀ s ∈ uIcc 0 r, HasDerivAt
      (fun s => -exp (-(c * s)) * (s ^ 2 / c + 2 * s / c ^ 2 + 2 / c ^ 3))
      (s ^ 2 * exp (-(c * s))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -(c * s)) (-c) s := by
      simpa using ((hasDerivAt_id s).const_mul c).fun_neg
    have h2 := h1.exp.fun_neg
    have h3 : HasDerivAt (fun s => s ^ 2 / c + 2 * s / c ^ 2 + 2 / c ^ 3)
        (2 * s / c + 2 / c ^ 2) s := by
      have := (((hasDerivAt_pow 2 s).div_const c).add
        (((hasDerivAt_id s).const_mul 2).div_const (c ^ 2))).add_const (2 / c ^ 3)
      convert this using 1; simp
    convert h2.mul h3 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have : 0 ≤ exp (-(c * r)) * (r ^ 2 / c + 2 * r / c ^ 2 + 2 / c ^ 3) := by positivity
  have e : -exp (-(c * r)) * (r ^ 2 / c + 2 * r / c ^ 2 + 2 / c ^ 3)
      - -exp (-(c * 0)) * (0 ^ 2 / c + 2 * 0 / c ^ 2 + 2 / c ^ 3)
      = 2 / c ^ 3 - exp (-(c * r)) * (r ^ 2 / c + 2 * r / c ^ 2 + 2 / c ^ 3) := by
    simp; ring
  rw [e]; linarith

/-- `∫₀ʳ e^{-cs} ds = (1 - e^{-cr})/c`. -/
lemma integral_exp_neg_mul {c r : ℝ} (hc : 0 < c) :
    ∫ s in (0 : ℝ)..r, exp (-(c * s)) = (1 - exp (-(c * r))) / c := by
  have hF : ∀ s ∈ uIcc 0 r, HasDerivAt (fun s => -exp (-(c * s)) / c) (exp (-(c * s))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -(c * s)) (-c) s := by
      simpa using ((hasDerivAt_id s).const_mul c).fun_neg
    convert (h1.exp.fun_neg).div_const c using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, neg_zero, exp_zero]
  ring

/-! ### Gaussian integrals on half-lines -/

lemma integrableOn_gauss {b : ℝ} (hb : 0 < b) (s : Set ℝ) :
    IntegrableOn (fun x => exp (-(b * x ^ 2))) s := by
  have := (integrable_exp_neg_mul_sq hb).integrableOn (s := s)
  simpa [neg_mul] using this

/-- Gaussian tail: `0 ≤ ∫_{r}^∞ e^{-bs²} ≤ e^{-br²/2} √(π/(2b))`. -/
lemma gauss_tail_le {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) :
    0 ≤ ∫ s in Ioi r, exp (-(b * s ^ 2)) ∧
      ∫ s in Ioi r, exp (-(b * s ^ 2)) ≤ exp (-(b * r ^ 2 / 2)) * √(π / (b / 2)) / 2 := by
  refine ⟨setIntegral_nonneg measurableSet_Ioi (fun _ _ => (exp_pos _).le), ?_⟩
  have hb2 : 0 < b / 2 := by positivity
  calc ∫ s in Ioi r, exp (-(b * s ^ 2))
      ≤ ∫ s in Ioi r, exp (-(b * r ^ 2 / 2)) * exp (-(b / 2 * s ^ 2)) := by
        refine setIntegral_mono_on (integrableOn_gauss hb _)
          ((integrableOn_gauss hb2 _).const_mul _) measurableSet_Ioi ?_
        intro s hs
        rw [← exp_add]
        apply exp_le_exp.mpr
        have : r ^ 2 ≤ s ^ 2 := by
          have := le_of_lt (mem_Ioi.mp hs); nlinarith
        nlinarith
    _ = exp (-(b * r ^ 2 / 2)) * ∫ s in Ioi r, exp (-(b / 2 * s ^ 2)) := integral_const_mul _ _
    _ ≤ exp (-(b * r ^ 2 / 2)) * ∫ s in Ioi 0, exp (-(b / 2 * s ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
        exact setIntegral_mono_set (integrableOn_gauss hb2 (Ioi 0))
          (ae_of_all _ (fun _ => (exp_pos _).le))
          (ae_of_all _ (fun x (hx : x ∈ Ioi r) => (lt_of_le_of_lt hr hx : x ∈ Ioi 0)))
    _ = exp (-(b * r ^ 2 / 2)) * √(π / (b / 2)) / 2 := by
        have := integral_gaussian_Ioi (b / 2)
        simp only [neg_mul] at this
        rw [this]; ring

/-- `∫₀ʳ e^{-bs²} ds = ½√(π/b) - ∫_r^∞ e^{-bs²} ds`. -/
lemma integral_gauss_interval {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) :
    ∫ s in (0 : ℝ)..r, exp (-(b * s ^ 2)) = √(π / b) / 2 - ∫ s in Ioi r, exp (-(b * s ^ 2)) := by
  have h := integral_gaussian_Ioi b
  simp only [neg_mul] at h
  rw [← h, ← Ioc_union_Ioi_eq_Ioi hr, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (integrableOn_gauss hb _) (integrableOn_gauss hb _),
    intervalIntegral.integral_of_le hr]
  ring

lemma sqrt_pi_div_half {k D : ℝ} (hk : 0 < k) (hD : 0 < D) :
    √(π / (k / (2 * D) / 2)) / 2 = √(π * D / k) := by
  rw [show π / (k / (2 * D) / 2) = 2 ^ 2 * (π * D / k) by field_simp,
    sqrt_mul (by norm_num), sqrt_sq (by norm_num)]
  ring

/-! ### The one-sided Gaussian estimate -/

/-- **Core one-sided Laplace estimate.**  If `|V(s) - k s²/2| ≤ M s³` on `[0, r]` with
`M r ≤ k/4`, then `∫₀ʳ e^{-V/D}` is `½√(2πD/k)` up to `8MD/k² + √(πD/k) e^{-kr²/(4D)}`. -/
theorem laplace_core {V : ℝ → ℝ} {r k M D : ℝ} (hV : Continuous V) (hr : 0 < r) (hk : 0 < k)
    (hM : 0 ≤ M) (hMr : M * r ≤ k / 4) (hT : ∀ s ∈ Icc 0 r, |V s - k / 2 * s ^ 2| ≤ M * s ^ 3)
    (hD : 0 < D) :
    |(∫ s in (0 : ℝ)..r, exp (-(V s / D))) - √(2 * π * D / k) / 2|
      ≤ 8 * M * D / k ^ 2 + √(π * D / k) * exp (-(k * r ^ 2 / (4 * D))) := by
  set b := k / (2 * D) with hbdef
  have hb : 0 < b := by positivity
  set c := k / (4 * D) with hcdef
  have hc : 0 < c := by positivity
  -- pointwise comparison
  have hpt : ∀ s ∈ Ioc 0 r, ‖exp (-(V s / D)) - exp (-(b * s ^ 2))‖
      ≤ M / D * (s ^ 3 * exp (-(c * s ^ 2))) := by
    intro s hs
    have hs' : s ∈ Icc 0 r := Ioc_subset_Icc_self hs
    have hTs := hT s hs'
    have hlow : k / 4 * s ^ 2 ≤ V s := by
      have : M * s ^ 3 ≤ k / 4 * s ^ 2 := by
        have : M * s ≤ k / 4 := le_trans (mul_le_mul_of_nonneg_left hs'.2 hM) hMr
        nlinarith [sq_nonneg s, hs'.1]
      have := (abs_le.mp hTs).1
      linarith
    have hx : c * s ^ 2 ≤ V s / D := by
      rw [hcdef, le_div_iff₀ hD]; field_simp; linarith
    have hy : c * s ^ 2 ≤ b * s ^ 2 := by
      rw [hcdef, hbdef]; gcongr; linarith
    have := abs_exp_neg_sub_le hx hy
    rw [Real.norm_eq_abs]
    refine le_trans this ?_
    have : |V s / D - b * s ^ 2| = |V s - k / 2 * s ^ 2| / D := by
      rw [← abs_of_pos hD, ← abs_div, abs_of_pos hD]; congr 1; rw [hbdef]; field_simp
    rw [this]
    calc |V s - k / 2 * s ^ 2| / D * exp (-(c * s ^ 2))
        ≤ M * s ^ 3 / D * exp (-(c * s ^ 2)) := by gcongr
      _ = M / D * (s ^ 3 * exp (-(c * s ^ 2))) := by ring
  have hdiff : |(∫ s in (0 : ℝ)..r, exp (-(V s / D))) - ∫ s in (0 : ℝ)..r, exp (-(b * s ^ 2))|
      ≤ 8 * M * D / k ^ 2 := by
    have hsub : (∫ s in (0 : ℝ)..r, exp (-(V s / D))) - ∫ s in (0 : ℝ)..r, exp (-(b * s ^ 2))
        = ∫ s in (0 : ℝ)..r, (exp (-(V s / D)) - exp (-(b * s ^ 2))) :=
      (intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)).symm
    rw [hsub]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hr.le
      (Eventually.of_forall (fun s hs => hpt s hs)) (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [Real.norm_eq_abs] at h1
    refine le_trans h1 ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 := integral_cube_gauss_le r hc
    calc M / D * ∫ s in (0 : ℝ)..r, s ^ 3 * exp (-(c * s ^ 2)) ≤ M / D * (1 / (2 * c ^ 2)) := by
          gcongr
      _ = 8 * M * D / k ^ 2 := by rw [hcdef]; field_simp; ring
  have hgauss := integral_gauss_interval hb hr.le
  obtain ⟨ht0, ht1⟩ := gauss_tail_le hb hr.le
  have hpi : √(π / b) = √(2 * π * D / k) := by rw [hbdef]; congr 1; field_simp
  have hexp : exp (-(b * r ^ 2 / 2)) = exp (-(k * r ^ 2 / (4 * D))) := by
    congr 1; rw [hbdef]; field_simp; ring
  rw [hpi] at hgauss
  have hpi2 : √(π / (b / 2)) / 2 = √(π * D / k) := by rw [hbdef]; exact sqrt_pi_div_half hk hD
  rw [hexp, mul_div_assoc, hpi2, mul_comm (exp _)] at ht1
  rw [abs_le] at hdiff ⊢
  constructor <;> nlinarith [exp_pos (-(k * r ^ 2 / (4 * D))), sqrt_nonneg (π * D / k)]

/-! ### Far region -/

/-- **Far-region estimate.**  If `W ≥ 0` on `S`, `W ≥ η` on `S` outside the window `[p, q]`,
and `e^{-W}` is integrable on `S`, then for `0 < D ≤ 1` the integral of `e^{-W/D}` over `S`
differs from that over the window by at most `e^{η} η⁻¹ (∫_S e^{-W}) D`. -/
theorem laplace_far {W : ℝ → ℝ} {S : Set ℝ} {p q η : ℝ} (hW : Continuous W)
    (hS : MeasurableSet S) (hpq : p ≤ q) (hJ : Icc p q ⊆ S) (hη : 0 < η)
    (hfar : ∀ z ∈ S, z ∉ Icc p q → η ≤ W z) (hnn : ∀ z ∈ S, 0 ≤ W z)
    (hint : IntegrableOn (fun z => exp (-W z)) S) {D : ℝ} (hD : 0 < D) (hD1 : D ≤ 1) :
    IntegrableOn (fun z => exp (-(W z / D))) S ∧
      |(∫ z in S, exp (-(W z / D))) - ∫ z in p..q, exp (-(W z / D))|
        ≤ exp η / η * (∫ z in S, exp (-W z)) * D := by
  have hmeas : AEStronglyMeasurable (fun z => exp (-(W z / D))) (volume.restrict S) :=
    (by fun_prop : Continuous fun z => exp (-(W z / D))).aestronglyMeasurable
  have hle : ∀ z ∈ S, exp (-(W z / D)) ≤ exp (-W z) := by
    intro z hz
    apply exp_le_exp.mpr
    have : W z ≤ W z / D := by
      rw [le_div_iff₀ hD]; nlinarith [hnn z hz]
    linarith
  have hintD : IntegrableOn (fun z => exp (-(W z / D))) S := by
    refine Integrable.mono' hint hmeas ?_
    refine (ae_restrict_iff' hS).mpr (Eventually.of_forall (fun z hz => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact hle z hz
  refine ⟨hintD, ?_⟩
  have hJm : MeasurableSet (Icc p q) := measurableSet_Icc
  have hsplit := integral_diff (μ := volume) (f := fun z => exp (-(W z / D))) hJm hintD hJ
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpq] at hsplit
  have hfarle : ∀ z ∈ S \ Icc p q, exp (-(W z / D)) ≤ exp η * exp (-(η / D)) * exp (-W z) := by
    intro z hz
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    have h1 := hfar z hz.1 hz.2
    have : η / D + W z ≤ W z / D + η := by
      have h2 : (1 / D - 1) * η ≤ (1 / D - 1) * W z := by
        apply mul_le_mul_of_nonneg_left h1
        rw [sub_nonneg, le_div_iff₀ hD]; linarith
      have e1 : η / D = 1 / D * η := by ring
      have e2 : W z / D = 1 / D * W z := by ring
      rw [e1, e2]; linarith
    linarith
  have hnn' : 0 ≤ ∫ z in S \ Icc p q, exp (-(W z / D)) :=
    setIntegral_nonneg (hS.diff hJm) (fun _ _ => (exp_pos _).le)
  have hb : ∫ z in S \ Icc p q, exp (-(W z / D)) ≤ exp η / η * (∫ z in S, exp (-W z)) * D :=
    calc ∫ z in S \ Icc p q, exp (-(W z / D))
        ≤ ∫ z in S \ Icc p q, exp η * exp (-(η / D)) * exp (-W z) :=
          setIntegral_mono_on (hintD.mono_set diff_subset)
            ((hint.mono_set diff_subset).const_mul _) (hS.diff hJm) hfarle
      _ = exp η * exp (-(η / D)) * ∫ z in S \ Icc p q, exp (-W z) := integral_const_mul _ _
      _ ≤ exp η * (D / η) * ∫ z in S, exp (-W z) := by
          have h1 := exp_neg_div_le hη hD
          have h2 : ∫ z in S \ Icc p q, exp (-W z) ≤ ∫ z in S, exp (-W z) :=
            setIntegral_mono_set hint
              ((ae_restrict_iff' hS).mpr (Eventually.of_forall (fun _ _ => (exp_pos _).le)))
              (ae_of_all _ (fun x (hx : x ∈ S \ Icc p q) => (hx.1 : x ∈ S)))
          have h3 : 0 ≤ ∫ z in S \ Icc p q, exp (-W z) :=
            setIntegral_nonneg (hS.diff hJm) (fun _ _ => (exp_pos _).le)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (exp_pos _).le) h2 h3 (by positivity)
      _ = exp η / η * (∫ z in S, exp (-W z)) * D := by ring
  rw [abs_le]
  constructor <;> linarith

/-! ### Two-sided and half Laplace estimates -/

/-- Bound on the near-window error: `8MD/k² + √(πD/k)e^{-kr²/(4D)} ≤ c₀ D` for `D ≤ 1`. -/
lemma near_err_le {r k M D : ℝ} (hr : 0 < r) (hk : 0 < k) (hD : 0 < D)
    (hD1 : D ≤ 1) :
    8 * M * D / k ^ 2 + √(π * D / k) * exp (-(k * r ^ 2 / (4 * D)))
      ≤ (8 * M / k ^ 2 + √(π / k) * (4 / (k * r ^ 2))) * D := by
  have h1 : √(π * D / k) ≤ √(π / k) := by
    apply sqrt_le_sqrt
    rw [mul_div_right_comm]; nlinarith [div_pos pi_pos hk]
  have h2 : exp (-(k * r ^ 2 / (4 * D))) ≤ 4 / (k * r ^ 2) * D := by
    have := exp_neg_div_le (c := k * r ^ 2 / 4) (by positivity) hD
    rw [show k * r ^ 2 / 4 / D = k * r ^ 2 / (4 * D) by field_simp] at this
    rw [show 4 / (k * r ^ 2) * D = D / (k * r ^ 2 / 4) by field_simp]
    exact this
  have h3 : √(π * D / k) * exp (-(k * r ^ 2 / (4 * D))) ≤ √(π / k) * (4 / (k * r ^ 2) * D) :=
    mul_le_mul h1 h2 (exp_pos _).le (sqrt_nonneg _)
  have e : 8 * M * D / k ^ 2 = 8 * M / k ^ 2 * D := by ring
  rw [e]; nlinarith

/-- Lower bound `W ≥ k s²/4` near the minimum, from the Taylor hypothesis. -/
lemma taylor_lower {W : ℝ → ℝ} {m r k M : ℝ} (hM : 0 ≤ M) (hMr : M * r ≤ k / 4)
    (hT : ∀ s, |s| ≤ r → |W (m + s) - k / 2 * s ^ 2| ≤ M * |s| ^ 3) {s : ℝ} (hs : |s| ≤ r) :
    k / 4 * s ^ 2 ≤ W (m + s) := by
  have h1 := (abs_le.mp (hT s hs)).1
  have h2 : M * |s| ^ 3 ≤ k / 4 * s ^ 2 := by
    have : M * |s| ≤ k / 4 := le_trans (mul_le_mul_of_nonneg_left hs hM) hMr
    have hs2 : |s| ^ 3 = |s| * s ^ 2 := by rw [pow_succ', sq_abs]
    rw [hs2]; nlinarith [sq_nonneg s]
  linarith

/-- The right half-window `[m, m + r]`. -/
lemma laplace_right_window {W : ℝ → ℝ} {m r k M D : ℝ} (hW : Continuous W) (hr : 0 < r)
    (hk : 0 < k) (hM : 0 ≤ M) (hMr : M * r ≤ k / 4)
    (hT : ∀ s, |s| ≤ r → |W (m + s) - k / 2 * s ^ 2| ≤ M * |s| ^ 3) (hD : 0 < D) :
    |(∫ z in m..m + r, exp (-(W z / D))) - √(2 * π * D / k) / 2|
      ≤ 8 * M * D / k ^ 2 + √(π * D / k) * exp (-(k * r ^ 2 / (4 * D))) := by
  have h := laplace_core (V := fun s => W (m + s)) (by fun_prop) hr hk hM hMr ?_ hD
  · rw [intervalIntegral.integral_comp_add_left (fun z => exp (-(W z / D))) m, add_zero] at h
    exact h
  · intro s hs
    have := hT s (by rw [abs_of_nonneg hs.1]; exact hs.2)
    rwa [abs_of_nonneg hs.1] at this

/-- The left half-window `[m - r, m]`. -/
lemma laplace_left_window {W : ℝ → ℝ} {m r k M D : ℝ} (hW : Continuous W) (hr : 0 < r)
    (hk : 0 < k) (hM : 0 ≤ M) (hMr : M * r ≤ k / 4)
    (hT : ∀ s, |s| ≤ r → |W (m + s) - k / 2 * s ^ 2| ≤ M * |s| ^ 3) (hD : 0 < D) :
    |(∫ z in m - r..m, exp (-(W z / D))) - √(2 * π * D / k) / 2|
      ≤ 8 * M * D / k ^ 2 + √(π * D / k) * exp (-(k * r ^ 2 / (4 * D))) := by
  have h := laplace_core (V := fun s => W (m - s)) (by fun_prop) hr hk hM hMr ?_ hD
  · rw [intervalIntegral.integral_comp_sub_left (fun z => exp (-(W z / D))) m, sub_zero] at h
    exact h
  · intro s hs
    have := hT (-s) (by rw [abs_neg, abs_of_nonneg hs.1]; exact hs.2)
    rwa [abs_neg, abs_of_nonneg hs.1, neg_sq, ← sub_eq_add_neg] at this

lemma nonneg_of_taylor_far {W : ℝ → ℝ} {S : Set ℝ} {m r k M η : ℝ} (hM : 0 ≤ M)
    (hMr : M * r ≤ k / 4) (hk : 0 < k)
    (hT : ∀ s, |s| ≤ r → |W (m + s) - k / 2 * s ^ 2| ≤ M * |s| ^ 3) (hη : 0 < η)
    (hfar : ∀ z ∈ S, r ≤ |z - m| → η ≤ W z) : ∀ z ∈ S, 0 ≤ W z := by
  intro z hz
  by_cases h : r ≤ |z - m|
  · exact hη.le.trans (hfar z hz h)
  · have := taylor_lower hM hMr hT (s := z - m) (le_of_not_ge h)
    rw [add_sub_cancel] at this
    nlinarith [sq_nonneg (z - m)]

/-- **Laplace's method at an interior minimum, with error `O(D)`.**  Let `W` be continuous with
`|W(m + s) - k s²/2| ≤ M|s|³` for `|s| ≤ r` (`M r ≤ k/4`), let `S ⊇ [m - r, m + r]` be
measurable with `W ≥ η > 0` on `S` at distance `≥ r` from `m`, and `e^{-W}` integrable on `S`.
Then `|∫_S e^{-W/D} - √(2πD/k)| ≤ C D` for all `0 < D ≤ 1`. -/
theorem laplace_min {W : ℝ → ℝ} {S : Set ℝ} {m r k M η : ℝ} (hW : Continuous W)
    (hS : MeasurableSet S) (hr : 0 < r) (hk : 0 < k) (hM : 0 ≤ M) (hMr : M * r ≤ k / 4)
    (hT : ∀ s, |s| ≤ r → |W (m + s) - k / 2 * s ^ 2| ≤ M * |s| ^ 3)
    (hJ : Icc (m - r) (m + r) ⊆ S) (hη : 0 < η) (hfar : ∀ z ∈ S, r ≤ |z - m| → η ≤ W z)
    (hint : IntegrableOn (fun z => exp (-W z)) S) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      IntegrableOn (fun z => exp (-(W z / D))) S ∧
        |(∫ z in S, exp (-(W z / D))) - √(2 * π * D / k)| ≤ C * D := by
  refine ⟨2 * (8 * M / k ^ 2 + √(π / k) * (4 / (k * r ^ 2))) + exp η / η * ∫ z in S, exp (-W z),
    fun D hD hD1 => ?_⟩
  have hnn := nonneg_of_taylor_far hM hMr hk hT hη hfar
  have hfar' : ∀ z ∈ S, z ∉ Icc (m - r) (m + r) → η ≤ W z := by
    intro z hz hz'
    apply hfar z hz
    rw [mem_Icc, not_and_or, not_le, not_le] at hz'
    rcases hz' with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨hint', hfarb⟩ := laplace_far hW hS (by linarith) hJ hη hfar' hnn hint hD hD1
  refine ⟨hint', ?_⟩
  have hL := laplace_left_window hW hr hk hM hMr hT hD
  have hR := laplace_right_window hW hr hk hM hMr hT hD
  have hadd : (∫ z in m - r..m, exp (-(W z / D))) + ∫ z in m..m + r, exp (-(W z / D))
      = ∫ z in m - r..m + r, exp (-(W z / D)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hE := near_err_le (M := M) hr hk hD hD1
  have hs2 : √(2 * π * D / k) = √(2 * π * D / k) / 2 + √(2 * π * D / k) / 2 := by ring
  rw [abs_le] at hL hR hfarb ⊢
  constructor <;> nlinarith

/-- **Laplace's method with the window cut at the minimum (half Gaussian).**  As
`laplace_min`, but `S ⊇ [m - r, m]` and `S` contains no point of `(m, m + r)`; then
`|∫_S e^{-W/D} - ½√(2πD/k)| ≤ C D`. -/
theorem laplace_min_half {W : ℝ → ℝ} {S : Set ℝ} {m r k M η : ℝ} (hW : Continuous W)
    (hS : MeasurableSet S) (hr : 0 < r) (hk : 0 < k) (hM : 0 ≤ M) (hMr : M * r ≤ k / 4)
    (hT : ∀ s, |s| ≤ r → |W (m + s) - k / 2 * s ^ 2| ≤ M * |s| ^ 3)
    (hJ : Icc (m - r) m ⊆ S) (hgap : ∀ z ∈ S, m < z → m + r ≤ z) (hη : 0 < η)
    (hfar : ∀ z ∈ S, r ≤ |z - m| → η ≤ W z) (hint : IntegrableOn (fun z => exp (-W z)) S) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      IntegrableOn (fun z => exp (-(W z / D))) S ∧
        |(∫ z in S, exp (-(W z / D))) - √(2 * π * D / k) / 2| ≤ C * D := by
  refine ⟨(8 * M / k ^ 2 + √(π / k) * (4 / (k * r ^ 2))) + exp η / η * ∫ z in S, exp (-W z),
    fun D hD hD1 => ?_⟩
  have hnn := nonneg_of_taylor_far hM hMr hk hT hη hfar
  have hfar' : ∀ z ∈ S, z ∉ Icc (m - r) m → η ≤ W z := by
    intro z hz hz'
    apply hfar z hz
    rw [mem_Icc, not_and_or, not_le, not_le] at hz'
    rcases hz' with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · have := hgap z hz h
      rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨hint', hfarb⟩ := laplace_far hW hS (by linarith) hJ hη hfar' hnn hint hD hD1
  refine ⟨hint', ?_⟩
  have hL := laplace_left_window hW hr hk hM hMr hT hD
  have hE := near_err_le (M := M) hr hk hD hD1
  rw [abs_le] at hL hfarb ⊢
  constructor <;> nlinarith

/-! ### Endpoint (linear) Laplace estimate -/

/-- **Endpoint Laplace method, error `O(D²)`.**  If `|W(x₀ - s) - g s| ≤ M s²` on `[0, r]`
(`g > 0`, `M r ≤ g/2`) and `W ≥ η > 0` on `[lo, x₀ - r]`, then
`|∫_{lo}^{x₀} e^{-W/D} - D/g| ≤ C D²` for `0 < D ≤ 1`.  This is the estimate behind (9.1.15). -/
theorem laplace_endpoint {W : ℝ → ℝ} {lo x₀ r g M η : ℝ} (hW : Continuous W) (hr : 0 < r)
    (hg : 0 < g) (hM : 0 ≤ M) (hMr : M * r ≤ g / 2)
    (hT : ∀ s ∈ Icc 0 r, |W (x₀ - s) - g * s| ≤ M * s ^ 2) (hlo : lo ≤ x₀ - r) (hη : 0 < η)
    (hfar : ∀ z ∈ Icc lo (x₀ - r), η ≤ W z) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 → |(∫ z in lo..x₀, exp (-(W z / D))) - D / g| ≤ C * D ^ 2 := by
  refine ⟨16 * M / g ^ 3 + 1 / (g ^ 2 * r) + (x₀ - r - lo) * (2 / η ^ 2), fun D hD hD1 => ?_⟩
  set c := g / (2 * D) with hcdef
  have hc : 0 < c := by positivity
  have hpt : ∀ s ∈ Ioc 0 r, ‖exp (-(W (x₀ - s) / D)) - exp (-(g / D * s))‖
      ≤ M / D * (s ^ 2 * exp (-(c * s))) := by
    intro s hs
    have hs' : s ∈ Icc 0 r := Ioc_subset_Icc_self hs
    have hTs := hT s hs'
    have hlow : g / 2 * s ≤ W (x₀ - s) := by
      have : M * s ^ 2 ≤ g / 2 * s := by
        have : M * s ≤ g / 2 := le_trans (mul_le_mul_of_nonneg_left hs'.2 hM) hMr
        nlinarith [hs'.1]
      have := (abs_le.mp hTs).1
      linarith
    have hx : c * s ≤ W (x₀ - s) / D := by
      rw [hcdef, le_div_iff₀ hD]; field_simp; linarith
    have hy : c * s ≤ g / D * s := by
      rw [hcdef]
      apply mul_le_mul_of_nonneg_right _ hs'.1
      rw [div_le_div_iff₀ (by positivity) hD]; nlinarith
    have := abs_exp_neg_sub_le hx hy
    rw [Real.norm_eq_abs]
    refine le_trans this ?_
    have : |W (x₀ - s) / D - g / D * s| = |W (x₀ - s) - g * s| / D := by
      rw [← abs_of_pos hD, ← abs_div, abs_of_pos hD]; congr 1; field_simp
    rw [this]
    calc |W (x₀ - s) - g * s| / D * exp (-(c * s))
        ≤ M * s ^ 2 / D * exp (-(c * s)) := by gcongr
      _ = M / D * (s ^ 2 * exp (-(c * s))) := by ring
  have hdiff : |(∫ s in (0 : ℝ)..r, exp (-(W (x₀ - s) / D))) - ∫ s in (0 : ℝ)..r, exp (-(g / D * s))|
      ≤ 16 * M / g ^ 3 * D ^ 2 := by
    have hsub : (∫ s in (0 : ℝ)..r, exp (-(W (x₀ - s) / D))) - ∫ s in (0 : ℝ)..r, exp (-(g / D * s))
        = ∫ s in (0 : ℝ)..r, (exp (-(W (x₀ - s) / D)) - exp (-(g / D * s))) :=
      (intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)).symm
    rw [hsub]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hr.le
      (Eventually.of_forall (fun s hs => hpt s hs)) (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [Real.norm_eq_abs] at h1
    refine le_trans h1 ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 := integral_sq_exp_le hc hr.le
    calc M / D * ∫ s in (0 : ℝ)..r, s ^ 2 * exp (-(c * s)) ≤ M / D * (2 / c ^ 3) := by gcongr
      _ = 16 * M / g ^ 3 * D ^ 2 := by rw [hcdef]; field_simp; ring
  have hlin := integral_exp_neg_mul (c := g / D) (r := r) (by positivity)
  have hlin2 : exp (-(g / D * r)) ≤ D / (g * r) := by
    have := exp_neg_div_le (c := g * r) (by positivity) hD
    rwa [show g * r / D = g / D * r by ring] at this
  have hnear : ∫ s in (0 : ℝ)..r, exp (-(W (x₀ - s) / D))
      = ∫ z in x₀ - r..x₀, exp (-(W z / D)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun z => exp (-(W z / D))) x₀, sub_zero]
  have hfarb : |∫ z in lo..x₀ - r, exp (-(W z / D))| ≤ (x₀ - r - lo) * (2 / η ^ 2) * D ^ 2 := by
    have hb : ∀ z ∈ uIoc lo (x₀ - r), ‖exp (-(W z / D))‖ ≤ 2 * D ^ 2 / η ^ 2 := by
      intro z hz
      rw [uIoc_of_le hlo] at hz
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      refine le_trans (exp_le_exp.mpr ?_) (exp_neg_div_le_sq hη hD)
      have := hfar z (Ioc_subset_Icc_self hz)
      exact neg_le_neg (div_le_div_of_nonneg_right this hD.le)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x₀ - r - lo)] at this
    calc _ ≤ 2 * D ^ 2 / η ^ 2 * (x₀ - r - lo) := this
      _ = _ := by ring
  have hadd : (∫ z in lo..x₀ - r, exp (-(W z / D))) + ∫ z in x₀ - r..x₀, exp (-(W z / D))
      = ∫ z in lo..x₀, exp (-(W z / D)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [← hadd, ← hnear]
  rw [hlin] at hdiff
  have hgD : (1 - exp (-(g / D * r))) / (g / D) = D / g - D / g * exp (-(g / D * r)) := by
    field_simp
  rw [hgD] at hdiff
  have hsmall : D / g * exp (-(g / D * r)) ≤ 1 / (g ^ 2 * r) * D ^ 2 := by
    calc D / g * exp (-(g / D * r)) ≤ D / g * (D / (g * r)) := by gcongr
      _ = 1 / (g ^ 2 * r) * D ^ 2 := by field_simp
  have hpos : 0 ≤ D / g * exp (-(g / D * r)) := by positivity
  rw [abs_le] at hdiff hfarb ⊢
  constructor <;> nlinarith

/-! ### Gaussian window cut at `b - y₀√D` -/

/-- **Window cut at `b - y₀√D`.**  If `|W(b - s) - k s²/2| ≤ M s³` on `[0, r]` (`M r ≤ k/4`),
`W ≥ η > 0` on `[lo, b - r]` and `y₀ ≥ 0`, then for all sufficiently small `D`,
`|∫_{lo}^{b - y₀√D} e^{-W/D} - √D ∫_{y₀}^∞ e^{-k t²/2} dt| ≤ C D`.  This is the estimate behind
(9.1.20). -/
theorem laplace_gauss_tail {W : ℝ → ℝ} {lo b r k M η y₀ : ℝ} (hW : Continuous W) (hr : 0 < r)
    (hk : 0 < k) (hM : 0 ≤ M) (hMr : M * r ≤ k / 4)
    (hT : ∀ s ∈ Icc 0 r, |W (b - s) - k / 2 * s ^ 2| ≤ M * s ^ 3) (hlo : lo ≤ b - r)
    (hη : 0 < η) (hfar : ∀ z ∈ Icc lo (b - r), η ≤ W z) (hy₀ : 0 ≤ y₀) :
    ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
      |(∫ z in lo..b - y₀ * √D, exp (-(W z / D))) - √D * ∫ t in Ioi y₀, exp (-(k / 2 * t ^ 2))|
        ≤ C * D := by
  refine ⟨8 * M / k ^ 2 + √(π / k) * (4 / (k * r ^ 2)) + (b - r - lo) / η,
    min 1 (r ^ 2 / (y₀ ^ 2 + 1)), lt_min one_pos (by positivity), fun D hD hD0 => ?_⟩
  have hD1 : D ≤ 1 := le_trans hD0 (min_le_left _ _)
  have hcut : y₀ * √D ≤ r := by
    have h1 : D ≤ r ^ 2 / (y₀ ^ 2 + 1) := le_trans hD0 (min_le_right _ _)
    have h2 : (y₀ * √D) ^ 2 ≤ r ^ 2 := by
      rw [mul_pow, sq_sqrt hD.le]
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith [sq_nonneg y₀]
    have h3 : 0 ≤ y₀ * √D := by positivity
    nlinarith
  have ht₀0 : 0 ≤ y₀ * √D := by positivity
  set c := k / (4 * D) with hcdef
  have hc : 0 < c := by positivity
  set bb := k / (2 * D) with hbbdef
  have hbb : 0 < bb := by positivity
  have hpt : ∀ s ∈ Ioc (y₀ * √D) r, ‖exp (-(W (b - s) / D)) - exp (-(bb * s ^ 2))‖
      ≤ M / D * (s ^ 3 * exp (-(c * s ^ 2))) := by
    intro s hs
    have hs' : s ∈ Icc 0 r := ⟨ht₀0.trans hs.1.le, hs.2⟩
    have hTs := hT s hs'
    have hlow : k / 4 * s ^ 2 ≤ W (b - s) := by
      have : M * s ^ 3 ≤ k / 4 * s ^ 2 := by
        have : M * s ≤ k / 4 := le_trans (mul_le_mul_of_nonneg_left hs'.2 hM) hMr
        nlinarith [sq_nonneg s, hs'.1]
      have := (abs_le.mp hTs).1
      linarith
    have hx : c * s ^ 2 ≤ W (b - s) / D := by
      rw [hcdef, le_div_iff₀ hD]; field_simp; linarith
    have hy : c * s ^ 2 ≤ bb * s ^ 2 := by rw [hcdef, hbbdef]; gcongr; linarith
    have := abs_exp_neg_sub_le hx hy
    rw [Real.norm_eq_abs]
    refine le_trans this ?_
    have : |W (b - s) / D - bb * s ^ 2| = |W (b - s) - k / 2 * s ^ 2| / D := by
      rw [← abs_of_pos hD, ← abs_div, abs_of_pos hD]; congr 1; rw [hbbdef]; field_simp
    rw [this]
    calc |W (b - s) - k / 2 * s ^ 2| / D * exp (-(c * s ^ 2))
        ≤ M * s ^ 3 / D * exp (-(c * s ^ 2)) := by gcongr
      _ = M / D * (s ^ 3 * exp (-(c * s ^ 2))) := by ring
  have hdiff : |(∫ s in y₀ * √D..r, exp (-(W (b - s) / D)))
      - ∫ s in y₀ * √D..r, exp (-(bb * s ^ 2))| ≤ 8 * M * D / k ^ 2 := by
    have hsub : (∫ s in y₀ * √D..r, exp (-(W (b - s) / D))) - ∫ s in y₀ * √D..r, exp (-(bb * s ^ 2))
        = ∫ s in y₀ * √D..r, (exp (-(W (b - s) / D)) - exp (-(bb * s ^ 2))) :=
      (intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)).symm
    rw [hsub]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hcut
      (Eventually.of_forall (fun s hs => hpt s hs)) (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [Real.norm_eq_abs] at h1
    refine le_trans h1 ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 : ∫ s in y₀ * √D..r, s ^ 3 * exp (-(c * s ^ 2))
        ≤ ∫ s in (0 : ℝ)..r, s ^ 3 * exp (-(c * s ^ 2)) := by
      have hadd := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := y₀ * √D)
        (c := r) (f := fun s => s ^ 3 * exp (-(c * s ^ 2))) (μ := volume)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      have : 0 ≤ ∫ s in (0 : ℝ)..y₀ * √D, s ^ 3 * exp (-(c * s ^ 2)) :=
        intervalIntegral.integral_nonneg ht₀0 (fun s hs => by
          have := hs.1; positivity)
      linarith
    have h3 := integral_cube_gauss_le r hc
    calc M / D * ∫ s in y₀ * √D..r, s ^ 3 * exp (-(c * s ^ 2))
        ≤ M / D * (1 / (2 * c ^ 2)) := by
          gcongr; linarith
      _ = 8 * M * D / k ^ 2 := by rw [hcdef]; field_simp; ring
  have hsplit : ∫ s in y₀ * √D..r, exp (-(bb * s ^ 2))
      = (∫ s in Ioi (y₀ * √D), exp (-(bb * s ^ 2))) - ∫ s in Ioi r, exp (-(bb * s ^ 2)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hcut, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (integrableOn_gauss hbb _) (integrableOn_gauss hbb _),
      intervalIntegral.integral_of_le hcut]
    ring
  have hscale : ∫ s in Ioi (y₀ * √D), exp (-(bb * s ^ 2))
      = √D * ∫ t in Ioi y₀, exp (-(k / 2 * t ^ 2)) := by
    have hsD : 0 < √D := sqrt_pos.mpr hD
    have h := integral_comp_mul_left_Ioi (fun s => exp (-(bb * s ^ 2))) y₀ hsD
    have e1 : ∀ t : ℝ, exp (-(bb * (√D * t) ^ 2)) = exp (-(k / 2 * t ^ 2)) := by
      intro t; congr 2; rw [mul_pow, sq_sqrt hD.le, hbbdef]; field_simp
    simp only [e1, smul_eq_mul] at h
    rw [mul_comm y₀, h, ← mul_assoc, mul_inv_cancel₀ hsD.ne', one_mul]
  obtain ⟨ht0, ht1⟩ := gauss_tail_le hbb hr.le
  have hexp : exp (-(bb * r ^ 2 / 2)) = exp (-(k * r ^ 2 / (4 * D))) := by
    congr 1; rw [hbbdef]; field_simp; ring
  have hpi2 : √(π / (bb / 2)) / 2 = √(π * D / k) := by rw [hbbdef]; exact sqrt_pi_div_half hk hD
  rw [hexp, mul_div_assoc, hpi2, mul_comm (exp _)] at ht1
  have hE := near_err_le (M := M) hr hk hD hD1
  have hnear : ∫ s in y₀ * √D..r, exp (-(W (b - s) / D))
      = ∫ z in b - r..b - y₀ * √D, exp (-(W z / D)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun z => exp (-(W z / D))) b]
  have hfarb : |∫ z in lo..b - r, exp (-(W z / D))| ≤ (b - r - lo) / η * D := by
    have hb : ∀ z ∈ uIoc lo (b - r), ‖exp (-(W z / D))‖ ≤ D / η := by
      intro z hz
      rw [uIoc_of_le hlo] at hz
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      refine le_trans (exp_le_exp.mpr ?_) (exp_neg_div_le hη hD)
      exact neg_le_neg (div_le_div_of_nonneg_right (hfar z (Ioc_subset_Icc_self hz)) hD.le)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - r - lo)] at this
    calc _ ≤ D / η * (b - r - lo) := this
      _ = _ := by ring
  have hadd : (∫ z in lo..b - r, exp (-(W z / D))) + ∫ z in b - r..b - y₀ * √D, exp (-(W z / D))
      = ∫ z in lo..b - y₀ * √D, exp (-(W z / D)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [← hadd, ← hnear]
  rw [hsplit, hscale] at hdiff
  rw [abs_le] at hdiff hfarb ⊢
  constructor <;> nlinarith [exp_pos (-(k * r ^ 2 / (4 * D))), sqrt_nonneg (π * D / k)]

end Gardiner.Escape

namespace Gardiner.Escape

/-- A rate `|f(D) - L| ≤ C√D` on `(0, D₀]` gives the limit `f(D) → L` as `D → 0⁺`. -/
theorem tendsto_of_sqrt_rate {f : ℝ → ℝ} {L C D₀ : ℝ} (hD₀ : 0 < D₀)
    (h : ∀ D, 0 < D → D ≤ D₀ → |f D - L| ≤ C * √D) : Tendsto f (𝓝[>] 0) (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (g := fun D => C * √D) ?_
  · filter_upwards [Ioo_mem_nhdsGT hD₀] with D hD
    exact h D hD.1 hD.2.le
  · have : Tendsto (fun D : ℝ => C * √D) (𝓝 0) (𝓝 (C * √0)) :=
      (continuous_const.mul continuous_sqrt).tendsto 0
    simpa using tendsto_nhdsWithin_of_tendsto_nhds this

end Gardiner.Escape
