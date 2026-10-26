/-
# Weighted quadratic variation and `∫₀ᵀ W dW` (Gardiner §4.2.2, §4.2.5)

* `Gardiner.Ito.IsFWiener.integral_wqv_sq`: for nonanticipating square-integrable weights `gᵢ`,
  `⟨(Σᵢ gᵢ((ΔWᵢ)² - Δt))²⟩ = 2 Δt² Σᵢ ⟨gᵢ²⟩` on the uniform partition — the computation behind
  Gardiner's `dW² = dt` ((4.2.24)–(4.2.27)).
* `Gardiner.Ito.IsFWiener.itoInt_W`: `∫₀ᵀ W dW = ½(W(T)² - T)` almost surely, Gardiner (4.2.20),
  as a genuine Itô integral.
-/
import SHSLib.Gardiner.Ito.Calculus.Riemann

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

lemma gridPt_mono {T : ℝ} (hT : 0 ≤ T) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    gridPt T n i ≤ gridPt T n j := by
  unfold gridPt
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

lemma gridPt_sub (T : ℝ) (n i : ℕ) : gridPt T n (i + 1) - gridPt T n i = T / (n + 1) := by
  rw [gridPt_succ]; ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- `⟨(Σᵢ Yᵢ)²⟩ = Σᵢ ⟨Yᵢ²⟩` for pairwise orthogonal square-integrable `Yᵢ`. -/
lemma integral_sq_sum_of_orth {Y : ℕ → Ω → ℝ} (m : ℕ) (hY : ∀ i, MemLp (Y i) 2 P)
    (horth : ∀ i j, i < j → ∫ ω, Y i ω * Y j ω ∂P = 0) :
    ∫ ω, (∑ i ∈ Finset.range m, Y i ω) ^ 2 ∂P = ∑ i ∈ Finset.range m, ∫ ω, Y i ω ^ 2 ∂P := by
  have hint : ∀ i j, Integrable (fun ω => Y i ω * Y j ω) P :=
    fun i j => (hY i).integrable_mul (hY j)
  have e : (fun ω => (∑ i ∈ Finset.range m, Y i ω) ^ 2) =
      fun ω => ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, Y i ω * Y j ω := by
    funext ω; rw [sq, Finset.sum_mul_sum]
  rw [e, integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finset_sum _ (fun j _ => hint i j), Finset.sum_eq_single i]
  · simp only [sq]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [show (fun ω => Y i ω * Y j ω) = fun ω => Y j ω * Y i ω by funext ω; ring]
      exact horth j i h
    · exact horth i j h
  · intro h; exact absurd hi h

omit mΩ in
/-- Algebraic identity for the left-point sums of `∫ W dW`. -/
lemma itoRiemann_W_eq (W : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    itoRiemann W W T n ω = (W T ω ^ 2 - W 0 ω ^ 2) / 2 -
      (∑ i ∈ Finset.range (n + 1), (W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2) / 2 := by
  unfold itoRiemann
  have htel := Finset.sum_range_sub (fun i => W (gridPt T n i) ω ^ 2) (n + 1)
  simp only [gridPt_last] at htel
  have h0 : gridPt T n 0 = 0 := by simp [gridPt]
  rw [h0] at htel
  rw [← htel, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {𝓕 : Filtration ℝ mΩ} {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- `Z((ΔW)² - Δt)` is square integrable with `⟨(Z((ΔW)² - Δt))²⟩ = 2Δt²⟨Z²⟩`. -/
lemma IsFWiener.mul_incr_sq_sub {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 s] Z) (hZ2 : MemLp Z 2 P) :
    MemLp (fun ω => Z ω * ((W t ω - W s ω) ^ 2 - (t - s))) 2 P ∧
    ∫ ω, (Z ω * ((W t ω - W s ω) ^ 2 - (t - s))) ^ 2 ∂P = 2 * (t - s) ^ 2 * ∫ ω, Z ω ^ 2 ∂P := by
  have := hW.isProbabilityMeasure
  have hZm : StronglyMeasurable Z := hZ.mono (𝓕.le s)
  obtain ⟨h1, h2⟩ := hW.mul_incr_fun hs hst (hZ.pow 2) hZ2.integrable_sq
    (g := fun x => (x ^ 2 - (t - s)) ^ 2) (by fun_prop)
    (hW.memLp_incr_sq_sub hs hst).integrable_sq
  have e : (fun ω => (Z ω * ((W t ω - W s ω) ^ 2 - (t - s))) ^ 2) =
      fun ω => Z ω ^ 2 * ((W t ω - W s ω) ^ 2 - (t - s)) ^ 2 := by funext ω; ring
  refine ⟨(memLp_two_iff_integrable_sq ?_).mpr ?_, ?_⟩
  · exact (hZm.measurable.mul
      (((hW.measurable_incr s t).pow_const 2).sub_const _)).aestronglyMeasurable
  · rw [e]; exact h1
  · simp only [Pi.pow_apply] at h2
    rw [e, h2, hW.integral_incr_sq_sub_sq hs hst]; ring

/-- `⟨Z((ΔW)² - Δt)⟩ = 0` for integrable `𝓕 s`-measurable `Z`. -/
lemma IsFWiener.integral_mul_incr_sq_sub {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 s] Z) (hZi : Integrable Z P) :
    ∫ ω, Z ω * ((W t ω - W s ω) ^ 2 - (t - s)) ∂P = 0 := by
  have := hW.isProbabilityMeasure
  obtain ⟨_, h2⟩ := hW.mul_incr_fun hs hst hZ hZi (g := fun x => x ^ 2 - (t - s)) (by fun_prop)
    ((hW.integrable_incr_pow hs hst 2).sub (integrable_const _))
  rw [h2, integral_sub (hW.integrable_incr_pow hs hst 2) (integrable_const _),
    hW.integral_incr_sq hs hst]
  simp

/-- **Weighted quadratic variation.** For weights `gᵢ` measurable at the left grid point and
square integrable, `⟨(Σᵢ gᵢ((ΔWᵢ)² - Δt))²⟩ = 2Δt² Σᵢ ⟨gᵢ²⟩`, `Δt = T/(n+1)`. -/
theorem IsFWiener.integral_wqv_sq {T : ℝ} (hT : 0 ≤ T) (n : ℕ) {g : ℕ → Ω → ℝ}
    (hg : ∀ i, StronglyMeasurable[𝓕 (gridPt T n i)] (g i)) (hg2 : ∀ i, MemLp (g i) 2 P) :
    ∫ ω, (∑ i ∈ Finset.range (n + 1), g i ω *
        ((W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T / (n + 1))) ^ 2 ∂P =
      2 * (T / (n + 1)) ^ 2 * ∑ i ∈ Finset.range (n + 1), ∫ ω, g i ω ^ 2 ∂P := by
  have := hW.isProbabilityMeasure
  set Y : ℕ → Ω → ℝ := fun i ω => g i ω *
    ((W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - (gridPt T n (i + 1) - gridPt T n i))
    with hYdef
  have hle : ∀ i, gridPt T n i ≤ gridPt T n (i + 1) := fun i => gridPt_mono hT n (by omega)
  have h0 : ∀ i, 0 ≤ gridPt T n i := fun i => gridPt_nonneg hT n i
  have hYm : ∀ i, MemLp (Y i) 2 P := fun i => (hW.mul_incr_sq_sub (h0 i) (hle i) (hg i) (hg2 i)).1
  have hYsq : ∀ i, ∫ ω, Y i ω ^ 2 ∂P = 2 * (T / (n + 1)) ^ 2 * ∫ ω, g i ω ^ 2 ∂P := by
    intro i
    rw [(hW.mul_incr_sq_sub (h0 i) (hle i) (hg i) (hg2 i)).2, gridPt_sub]
  have hYsm : ∀ i, StronglyMeasurable[𝓕 (gridPt T n (i + 1))] (Y i) := by
    intro i
    refine ((hg i).mono (𝓕.mono (hle i))).mul ?_
    exact (((hW.adapted _ (h0 _)).sub ((hW.adapted _ (h0 i)).mono (𝓕.mono (hle i)))).pow 2).sub
      stronglyMeasurable_const
  have horth : ∀ i j, i < j → ∫ ω, Y i ω * Y j ω ∂P = 0 := by
    intro i j hij
    have hZ : StronglyMeasurable[𝓕 (gridPt T n j)] (fun ω => Y i ω * g j ω) :=
      ((hYsm i).mono (𝓕.mono (gridPt_mono hT n hij))).mul (hg j)
    have := hW.integral_mul_incr_sq_sub (h0 j) (hle j) hZ ((hYm i).integrable_mul (hg2 j))
    rw [← this]
    congr 1; funext ω; simp only [hYdef]; ring
  have e : (fun ω => (∑ i ∈ Finset.range (n + 1), g i ω *
        ((W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T / (n + 1))) ^ 2) =
      fun ω => (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2 := by
    funext ω; simp only [hYdef, gridPt_sub]
  rw [e, integral_sq_sum_of_orth _ hYm horth, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hYsq i

/-- **Quadratic variation in mean square**: `⟨(Σᵢ (ΔWᵢ)² - T)²⟩ = 2T²/(n+1)`. -/
theorem IsFWiener.integral_qv_sq {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range (n + 1),
        (W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T) ^ 2 ∂P = 2 * T ^ 2 / (n + 1) := by
  have := hW.isProbabilityMeasure
  have h := hW.integral_wqv_sq hT n (g := fun _ _ => 1) (fun _ => stronglyMeasurable_const)
    (fun _ => memLp_const 1)
  have e : (fun ω => (∑ i ∈ Finset.range (n + 1),
        (W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T) ^ 2) =
      fun ω => (∑ i ∈ Finset.range (n + 1), 1 *
        ((W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T / (n + 1))) ^ 2 := by
    funext ω
    congr 1
    simp only [one_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; field_simp
  rw [e, h]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_pow, mul_one, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  push_cast; field_simp

lemma IsFWiener.memLp_sq {t : ℝ} (ht : 0 ≤ t) : MemLp (fun ω => W t ω ^ 2) 2 P := by
  refine (memLp_two_iff_integrable_sq ((hW.measurable t).pow_const 2).aestronglyMeasurable).mpr ?_
  refine (hW.integrable_pow ht 4).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only; ring

/-- **Gardiner (4.2.20)**: `∫₀ᵀ W dW = ½(W(T)² - T)` almost surely. -/
theorem IsFWiener.itoInt_W (hWj : Measurable (Function.uncurry W)) {T : ℝ} (hT : 0 < T) :
    itoInt W 𝓕 P T W =ᵐ[P] fun ω => (W T ω ^ 2 - T) / 2 := by
  have := hW.isProbabilityMeasure
  have hG := hW.isItoIntegrand_W hWj T
  have had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (W t) := fun t ht _ => hW.adapted t ht
  have hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (W t) 2 P := fun t ht _ => hW.memLp ht
  have hX : ∀ n, MemLp (itoRiemann W W T n) 2 P := by
    intro n
    rw [← integral_riemElem hT.le had hL2 W n]
    exact ElemIntegrand.memLp_integral hW _
  have hZ : MemLp (fun ω => (W T ω ^ 2 - T) / 2) 2 P := by
    have := MemLp.const_mul (MemLp.sub (hW.memLp_sq hT.le) (memLp_const T)) (1 / 2 : ℝ)
    convert this using 1
    funext ω; simp only [Pi.sub_apply]; ring
  refine l2_ae_unique hX (memLp_itoInt hW hG) hZ (itoRiemann_W_tendsto hW hWj hT) ?_
  have e : ∀ n, ∫ ω, (itoRiemann W W T n ω - (W T ω ^ 2 - T) / 2) ^ 2 ∂P = T ^ 2 / (2 * (n + 1)) := by
    intro n
    have hae : (fun ω => (itoRiemann W W T n ω - (W T ω ^ 2 - T) / 2) ^ 2) =ᵐ[P]
        fun ω => (∑ i ∈ Finset.range (n + 1),
          (W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T) ^ 2 / 4 := by
      filter_upwards [hW.zero] with ω hω
      rw [itoRiemann_W_eq, hω]; ring
    rw [integral_congr_ae hae, integral_div, hW.integral_qv_sq hT.le n]
    field_simp; ring
  simp_rw [e]
  have : Tendsto (fun n : ℕ => (T ^ 2 / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 ((T ^ 2 / 2) * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  field_simp

end Gardiner.Ito
