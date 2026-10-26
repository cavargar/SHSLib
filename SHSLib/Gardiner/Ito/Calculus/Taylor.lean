/-
# Pathwise Taylor estimates for Itô's formula

Deterministic ingredients of the proof of Itô's formula (Gardiner §4.3.3):

* `Gardiner.Ito.IsC12`: `F(t, x)` is `C^{1,2}` with explicitly given partial derivatives.
* `Gardiner.Ito.IsC12.taylor2`: second-order Taylor bound in `x`.
* `Gardiner.Ito.IsC12.taylor_pathwise`: for any continuous path `x`, on the uniform partition
  `F(T, x_T) - F(0, x_0) = Σᵢ [F_t Δt + F_x Δxᵢ + ½ F_xx Δxᵢ²] + o(1)·(T + Σᵢ Δxᵢ²)`.
* `Gardiner.Ito.riemannStieltjes_tendsto`: `Σᵢ f(tᵢ) ∫_{tᵢ}^{tᵢ₊₁} a → ∫₀ᵀ f a` for continuous `f, a`.
-/
import SHSLib.Gardiner.Ito.Calculus.Quadratic

open Filter Topology Set MeasureTheory

noncomputable section

namespace Gardiner.Ito

/-- `F(t, x)` is of class `C^{1,2}` with partial derivatives `F_t = Ft`, `F_x = Fx`,
`F_xx = Fxx` (all jointly continuous). -/
structure IsC12 (F Ft Fx Fxx : ℝ → ℝ → ℝ) : Prop where
  cont_Ft : Continuous (Function.uncurry Ft)
  cont_Fx : Continuous (Function.uncurry Fx)
  cont_Fxx : Continuous (Function.uncurry Fxx)
  deriv_t : ∀ t x, HasDerivAt (fun s => F s x) (Ft t x) t
  deriv_x : ∀ t x, HasDerivAt (fun y => F t y) (Fx t x) x
  deriv_xx : ∀ t x, HasDerivAt (fun y => Fx t y) (Fxx t x) x

variable {F Ft Fx Fxx : ℝ → ℝ → ℝ}

/-- Second-order Taylor bound: if `F_xx(t, ·)` varies by at most `η` on `[y - |k|, y + |k|]`, then
`|F(t, y + k) - F(t, y) - F_x(t, y) k - ½ F_xx(t, y) k²| ≤ η k²`. -/
lemma IsC12.taylor2 (hF : IsC12 F Ft Fx Fxx) (t y k η : ℝ)
    (hη : ∀ u, |u| ≤ |k| → |Fxx t (y + u) - Fxx t y| ≤ η) :
    |F t (y + k) - F t y - Fx t y * k - Fxx t y / 2 * k ^ 2| ≤ η * k ^ 2 := by
  have hη0 : 0 ≤ η := by simpa using hη 0 (by simp)
  have hconv : Convex ℝ (uIcc (0 : ℝ) k) := convex_uIcc 0 k
  have hmem : ∀ u ∈ uIcc (0 : ℝ) k, |u| ≤ |k| := fun u hu => by
    simpa using Set.abs_sub_left_of_mem_uIcc hu
  have h0 : (0 : ℝ) ∈ uIcc 0 k := left_mem_uIcc
  have hk : k ∈ uIcc 0 k := right_mem_uIcc
  have hd1 : ∀ u, HasDerivAt (fun u => Fx t (y + u) - Fx t y - Fxx t y * u)
      (Fxx t (y + u) - Fxx t y) u := by
    intro u
    have := (hF.deriv_xx t (y + u)).comp_const_add y u
    convert (this.sub_const (Fx t y)).sub ((hasDerivAt_id u).const_mul (Fxx t y)) using 1
    simp
  have hb1 : ∀ u ∈ uIcc (0 : ℝ) k, |Fx t (y + u) - Fx t y - Fxx t y * u| ≤ η * |k| := by
    intro u hu
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v _ => (hd1 v).hasDerivWithinAt) (fun v hv => by
        rw [Real.norm_eq_abs]; exact hη v (hmem v hv)) h0 hu
    simp only [add_zero, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hmem u hu) hη0)
  have hd2 : ∀ u, HasDerivAt (fun u => F t (y + u) - Fx t y * u - Fxx t y / 2 * u ^ 2)
      (Fx t (y + u) - Fx t y - Fxx t y * u) u := by
    intro u
    have := (hF.deriv_x t (y + u)).comp_const_add y u
    convert (this.sub ((hasDerivAt_id u).const_mul (Fx t y))).sub
      ((hasDerivAt_pow 2 u).const_mul (Fxx t y / 2)) using 1
    simp; ring
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (hd2 v).hasDerivWithinAt) (fun v hv => by
      rw [Real.norm_eq_abs]; exact hb1 v hv) h0 hk
  simp only [add_zero, mul_zero, sub_zero, Real.norm_eq_abs, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at this
  calc |F t (y + k) - F t y - Fx t y * k - Fxx t y / 2 * k ^ 2|
      = |F t (y + k) - Fx t y * k - Fxx t y / 2 * k ^ 2 - F t y| := by ring_nf
    _ ≤ η * |k| * |k| := this
    _ = η * k ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **Pathwise Itô–Taylor estimate.** For a continuous path `x` and `η > 0`, for all fine enough
uniform partitions of `[0, T]`,
`|F(T, x_T) - F(0, x_0) - Σᵢ [F_t(tᵢ, xᵢ) Δt + F_x(tᵢ, xᵢ) Δxᵢ + ½ F_xx(tᵢ, xᵢ) Δxᵢ²]|
  ≤ η (T + Σᵢ Δxᵢ²)`. -/
theorem IsC12.taylor_pathwise (hF : IsC12 F Ft Fx Fxx) {T : ℝ} (hT : 0 ≤ T) {x : ℝ → ℝ}
    (hx : Continuous x) {η : ℝ} (hη : 0 < η) : ∃ N : ℕ, ∀ n ≥ N,
    |F T (x T) - F 0 (x 0) - ∑ i ∈ Finset.range (n + 1),
        (Ft (gridPt T n i) (x (gridPt T n i)) * (T / (n + 1)) +
         Fx (gridPt T n i) (x (gridPt T n i)) * (x (gridPt T n (i + 1)) - x (gridPt T n i)) +
         Fxx (gridPt T n i) (x (gridPt T n i)) / 2 *
           (x (gridPt T n (i + 1)) - x (gridPt T n i)) ^ 2)|
      ≤ η * (T + ∑ i ∈ Finset.range (n + 1),
        (x (gridPt T n (i + 1)) - x (gridPt T n i)) ^ 2) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hx.continuousOn
  set K := Icc (0 : ℝ) T ×ˢ Icc (-(M + 1)) (M + 1) with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ1, hδ1, h1⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hF.cont_Ft.continuousOn) η hη
  obtain ⟨δ2, hδ2, h2⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hF.cont_Fxx.continuousOn) η hη
  set δ := min (min δ1 δ2) 1 with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδ1 hδ2) one_pos
  obtain ⟨δ3, hδ3, h3⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
      hx.continuousOn) δ hδ
  set δ' := min δ1 δ3 with hδ'def
  have hδ' : 0 < δ' := lt_min hδ1 hδ3
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ')
  refine ⟨N, fun n hn => ?_⟩
  set h := T / ((n : ℝ) + 1) with hh
  have hh0 : 0 ≤ h := by positivity
  have hhδ : h < δ' := by
    rw [hh, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ'] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hcell : ∀ i ∈ Finset.range (n + 1),
      |F (gridPt T n (i + 1)) (x (gridPt T n (i + 1))) - F (gridPt T n i) (x (gridPt T n i)) -
        (Ft (gridPt T n i) (x (gridPt T n i)) * h +
         Fx (gridPt T n i) (x (gridPt T n i)) * (x (gridPt T n (i + 1)) - x (gridPt T n i)) +
         Fxx (gridPt T n i) (x (gridPt T n i)) / 2 *
           (x (gridPt T n (i + 1)) - x (gridPt T n i)) ^ 2)| ≤
        η * h + η * (x (gridPt T n (i + 1)) - x (gridPt T n i)) ^ 2 := by
    intro i hi
    have hi' : i + 1 ≤ n + 1 := by simp at hi; omega
    set a := gridPt T n i with ha
    set b := gridPt T n (i + 1) with hb
    have ha0 : 0 ≤ a := gridPt_nonneg hT n i
    have hbT : b ≤ T := gridPt_le hT hi'
    have hab : b = a + h := gridPt_succ T n i
    have haT : a ≤ T := by linarith
    have hb0 : 0 ≤ b := by linarith
    set xa := x a with hxa_def
    set xb := x b with hxb_def
    have hxa : |xa| ≤ M := by have := hM a ⟨ha0, haT⟩; rwa [Real.norm_eq_abs] at this
    have hxb : |xb| ≤ M := by have := hM b ⟨hb0, hbT⟩; rwa [Real.norm_eq_abs] at this
    have hΔ : |xb - xa| < δ := by
      have := h3 b ⟨hb0, hbT⟩ a ⟨ha0, haT⟩ (by
        rw [Real.dist_eq, hab, add_sub_cancel_left, abs_of_nonneg hh0]
        exact hhδ.trans_le (min_le_right _ _))
      rwa [Real.dist_eq] at this
    have hΔ1 : |xb - xa| < δ1 := hΔ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hΔ2 : |xb - xa| < δ2 := hΔ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hΔ3 : |xb - xa| < 1 := hΔ.trans_le (min_le_right _ _)
    have hMK : ∀ z, |z| ≤ M + 1 → z ∈ Icc (-(M + 1)) (M + 1) := fun z hz => abs_le.mp hz
    have hA : |F b xb - F a xb - Ft a xa * h| ≤ η * h := by
      have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => F s xb - Ft a xa * s)
        (f' := fun s => Ft s xb - Ft a xa) (a := a) (b := b) (C := η)
        (fun s _ => (((hF.deriv_t s xb).sub ((hasDerivAt_id s).const_mul (Ft a xa))).congr_deriv
          (by simp)).hasDerivWithinAt) (fun s hs => ?_) b ⟨by linarith, le_rfl⟩
      · simp only [Real.norm_eq_abs] at this
        rw [hab] at this ⊢
        calc |F (a + h) xb - F a xb - Ft a xa * h|
            = |F (a + h) xb - Ft a xa * (a + h) - (F a xb - Ft a xa * a)| := by ring_nf
          _ ≤ η * (a + h - a) := this
          _ = η * h := by ring
      · have hmemK1 : (s, xb) ∈ K := ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
          hMK _ (by linarith)⟩
        have hmemK2 : (a, xa) ∈ K := ⟨⟨ha0, haT⟩, hMK _ (by linarith)⟩
        have hd : dist (s, xb) (a, xa) < δ1 := by
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
          refine ⟨?_, hΔ1⟩
          rw [abs_of_nonneg (by linarith [hs.1])]
          have := hs.2; rw [hab] at this
          linarith [hhδ.trans_le (min_le_left δ1 δ3)]
        have := h1 _ hmemK1 _ hmemK2 hd
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs]; exact this.le
    have hB := hF.taylor2 a xa (xb - xa) η (fun u hu => by
      have hmemK1 : (a, xa + u) ∈ K := ⟨⟨ha0, haT⟩,
        hMK _ (by linarith [abs_add_le xa u])⟩
      have hmemK2 : (a, xa) ∈ K := ⟨⟨ha0, haT⟩, hMK _ (by linarith)⟩
      have hd : dist (a, xa + u) (a, xa) < δ2 := by
        rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
        refine ⟨by simpa using hδ2, ?_⟩
        rw [add_sub_cancel_left]; linarith
      have := h2 _ hmemK1 _ hmemK2 hd
      rw [Real.dist_eq] at this
      exact this.le)
    rw [add_sub_cancel] at hB
    calc _ = |(F b xb - F a xb - Ft a xa * h) +
          (F a xb - F a xa - Fx a xa * (xb - xa) - Fxx a xa / 2 * (xb - xa) ^ 2)| := by ring_nf
      _ ≤ |F b xb - F a xb - Ft a xa * h| +
          |F a xb - F a xa - Fx a xa * (xb - xa) - Fxx a xa / 2 * (xb - xa) ^ 2| := abs_add_le _ _
      _ ≤ _ := add_le_add hA hB
  have htel : F T (x T) - F 0 (x 0) = ∑ i ∈ Finset.range (n + 1),
      (F (gridPt T n (i + 1)) (x (gridPt T n (i + 1))) - F (gridPt T n i) (x (gridPt T n i))) := by
    rw [Finset.sum_range_sub (fun i => F (gridPt T n i) (x (gridPt T n i))), gridPt_last]
    simp [gridPt]
  rw [htel, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hcell).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum,
    hh]
  push_cast
  field_simp

/-- **Riemann–Stieltjes sums with an absolutely continuous integrator**:
`Σᵢ f(tᵢ) ∫_{tᵢ}^{tᵢ₊₁} a(s) ds → ∫₀ᵀ f(s) a(s) ds` for continuous `f`, `a`. -/
theorem riemannStieltjes_tendsto {T : ℝ} (hT : 0 ≤ T) {f a : ℝ → ℝ} (hf : Continuous f)
    (ha : Continuous a) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
      f (gridPt T n i) * ∫ s in gridPt T n i..gridPt T n (i + 1), a s) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, f s * a s)) := by
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    ha.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (2 * ((|A| + 1) * (T + 1))) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous hf.continuousOn)
    η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  refine ⟨N, fun n hn => ?_⟩
  set h := T / ((n : ℝ) + 1) with hh
  have hh0 : 0 ≤ h := by positivity
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hsplit : ∫ s in (0 : ℝ)..T, f s * a s = ∑ i ∈ Finset.range (n + 1),
      ∫ s in gridPt T n i..gridPt T n (i + 1), f s * a s := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := fun s => f s * a s)
      (a := gridPt T n) (n := n + 1) (μ := volume) (fun k _ => (hf.mul ha).intervalIntegrable _ _)
    rw [this, gridPt_last]
    simp [gridPt]
  have hcell : ∀ i ∈ Finset.range (n + 1),
      |f (gridPt T n i) * (∫ s in gridPt T n i..gridPt T n (i + 1), a s) -
        ∫ s in gridPt T n i..gridPt T n (i + 1), f s * a s| ≤ η * |A| * h := by
    intro i hi
    have hi' : i + 1 ≤ n + 1 := by simp at hi; omega
    have ha0 : 0 ≤ gridPt T n i := gridPt_nonneg hT n i
    have hbT : gridPt T n (i + 1) ≤ T := gridPt_le hT hi'
    have hab : gridPt T n (i + 1) = gridPt T n i + h := gridPt_succ T n i
    rw [← intervalIntegral.integral_const_mul]
    have hsub := intervalIntegral.integral_sub (μ := volume) (a := gridPt T n i)
      (b := gridPt T n (i + 1)) (f := fun s => f (gridPt T n i) * a s) (g := fun s => f s * a s)
      ((ha.intervalIntegrable _ _).const_mul _) ((hf.mul ha).intervalIntegrable _ _)
    rw [← hsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := η * |A|)
      (a := gridPt T n i) (b := gridPt T n (i + 1))
      (f := fun s => f (gridPt T n i) * a s - f s * a s) (fun s hs => ?_)
    · have hba : |gridPt T n (i + 1) - gridPt T n i| = h := by
        rw [hab, add_sub_cancel_left, abs_of_nonneg hh0]
      rw [Real.norm_eq_abs, hba] at this
      exact this
    · rw [Set.uIoc_of_le (by linarith)] at hs
      have hs0 : 0 ≤ s := by linarith [hs.1]
      have hsT : s ≤ T := by linarith [hs.2]
      have h1 := hfδ (gridPt T n i) ⟨ha0, by linarith⟩ s ⟨hs0, hsT⟩ (by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]
        linarith [hs.2])
      rw [Real.dist_eq] at h1
      have h2 : |a s| ≤ |A| := by
        have := hA s ⟨hs0, hsT⟩; rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self A)
      show ‖f (gridPt T n i) * a s - f s * a s‖ ≤ η * |A|
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      exact mul_le_mul h1.le h2 (abs_nonneg _) hη.le
  rw [Real.dist_eq, hsplit, ← Finset.sum_sub_distrib]
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hcell)).trans_lt ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh, hηdef]
  push_cast
  have hT1 : (0 : ℝ) < |A| + 1 := by positivity
  have e : ((n : ℝ) + 1) * (ε / (2 * ((|A| + 1) * (T + 1))) * |A| * (T / ((n : ℝ) + 1))) =
      ε / 2 * (|A| / (|A| + 1)) * (T / (T + 1)) := by
    field_simp
  rw [e]
  have h1 : |A| / (|A| + 1) < 1 := by rw [div_lt_one hT1]; linarith
  have h2 : T / (T + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h3 : 0 ≤ |A| / (|A| + 1) := by positivity
  have h4 : 0 ≤ T / (T + 1) := by positivity
  calc ε / 2 * (|A| / (|A| + 1)) * (T / (T + 1)) ≤ ε / 2 * 1 * 1 := by gcongr
    _ < ε := by linarith

/-- Left-point Riemann sums of a continuous function: `Σᵢ g(tᵢ) Δt → ∫₀ᵀ g`. -/
theorem riemannSum_tendsto {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), g (gridPt T n i) * (T / (n + 1))) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, g s)) := by
  have := riemannStieltjes_tendsto hT hg continuous_const (a := fun _ => (1 : ℝ))
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at this
  refine this.congr fun n => Finset.sum_congr rfl fun i _ => ?_
  rw [gridPt_sub]

end Gardiner.Ito
