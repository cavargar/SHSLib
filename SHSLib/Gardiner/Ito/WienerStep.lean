import SHSLib.Gardiner.Ito.WienerIntegral

/-!
# The Wiener integral of step functions agrees with the simple integral

The Wiener integral `Gardiner.Ito.wienerInt W P f a b` is the mean-square limit of the left-point
Riemann sums of `f` on the uniform partitions of `[a, b]`.  For a step function

  `f = Σⱼ cⱼ 1_{(αⱼ, βⱼ]}`,  `0 ≤ a ≤ αⱼ ≤ βⱼ ≤ b`,

the Riemann sums converge in mean square to the simple stochastic integral
`Σⱼ cⱼ (W(βⱼ) - W(αⱼ))` of the corresponding deterministic simple integrand
(`Gardiner.Ito.stepIntegrand`), so the two integrals agree almost surely
(`Gardiner.Ito.IsWiener.wienerInt_step`).  The proof uses the isometry for simple integrands and
the elementary estimate `∫ (fₙ - 1_{(α,β]})² ≤ 2(b - a)/(n + 1)` for the step approximations
(`Gardiner.Ito.integral_stepFn_ind_sub_sq_le`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

/-- Pointwise estimate for the step approximation of an indicator. -/
lemma stepFn_ind_sub_sq_le {a b α β : ℝ} (hab : a ≤ b) (haα : a ≤ α) (hβb : β ≤ b) (n : ℕ)
    (s : ℝ) :
    (stepFn (ind α β) a b n s - ind α β s) ^ 2 ≤
      ind α (α + (b - a) / (n + 1)) s + ind β (β + (b - a) / (n + 1)) s := by
  have h0 := ind_nonneg α (α + (b - a) / (n + 1)) s
  have h0' := ind_nonneg β (β + (b - a) / (n + 1)) s
  by_cases hs : s ∈ Set.Ioc a b
  · have hs' : s ∈ Set.Ioc (grid a b n 0) (grid a b n (n + 1)) := by
      rwa [grid_zero, grid_last']
    obtain ⟨i, hi, hsi⟩ := exists_cell hs'
    rw [stepFn, sum_ind_eq (grid_mono hab n) hi hsi]
    have hstep := grid_step a b n i
    set x := grid a b n i
    have hx1 : x < s := hsi.1
    have hx2 : s ≤ x + (b - a) / (n + 1) := by linarith [hsi.2]
    by_cases hxα : x ∈ Set.Ioc α β <;> by_cases hsα : s ∈ Set.Ioc α β
    · rw [ind_mem hxα, ind_mem hsα]; simp; positivity
    · rw [ind_mem hxα, ind_notMem hsα]
      have hsβ : β < s := by
        by_contra h; exact hsα ⟨hxα.1.trans hx1, not_lt.mp h⟩
      rw [ind_mem (show s ∈ Set.Ioc β (β + (b - a) / (n + 1)) from ⟨hsβ, by linarith [hxα.2]⟩)]
      norm_num; exact h0
    · rw [ind_notMem hxα, ind_mem hsα]
      have hxa : x ≤ α := by
        by_contra h; exact hxα ⟨not_le.mp h, hx1.le.trans hsα.2⟩
      rw [ind_mem (show s ∈ Set.Ioc α (α + (b - a) / (n + 1)) from ⟨hsα.1, by linarith⟩)]
      norm_num; exact h0'
    · rw [ind_notMem hxα, ind_notMem hsα]; simp; positivity
  · have hs' : s ∉ Set.Ioc (grid a b n 0) (grid a b n (n + 1)) := by
      rwa [grid_zero, grid_last']
    have hsαβ : s ∉ Set.Ioc α β := fun h => hs ⟨haα.trans_lt h.1, h.2.trans hβb⟩
    rw [stepFn, sum_ind_eq_zero (grid_mono hab n) hs', ind_notMem hsαβ]
    simp; positivity

/-- `∫ (fₙ - 1_{(α,β]})² ≤ 2(b - a)/(n + 1)` for the step approximations of an indicator. -/
lemma integral_stepFn_ind_sub_sq_le {a b α β : ℝ} (hab : a ≤ b) (haα : a ≤ α) (hβb : β ≤ b)
    (n : ℕ) :
    ∫ s, (stepFn (ind α β) a b n s - ind α β s) ^ 2 ≤ 2 * ((b - a) / (n + 1)) := by
  have hh : 0 ≤ (b - a) / (n + 1) := div_nonneg (by linarith) (by positivity)
  calc ∫ s, (stepFn (ind α β) a b n s - ind α β s) ^ 2
      ≤ ∫ s, (ind α (α + (b - a) / (n + 1)) s + ind β (β + (b - a) / (n + 1)) s) :=
        integral_mono ((memLp_stepFn _ a b n).sub (memLp_ind α β)).integrable_sq
          ((integrable_ind _ _).add (integrable_ind _ _))
          fun s => stepFn_ind_sub_sq_le hab haα hβb n s
    _ = 2 * ((b - a) / (n + 1)) := by
        rw [integral_add (integrable_ind _ _) (integrable_ind _ _), integral_ind (by linarith),
          integral_ind (by linarith)]
        ring

lemma stepFn_sum_ind {m : ℕ} (c α β : Fin m → ℝ) (a b : ℝ) (n : ℕ) (s : ℝ) :
    stepFn (fun s => ∑ j, c j * ind (α j) (β j) s) a b n s =
      ∑ j, c j * stepFn (ind (α j) (β j)) a b n s := by
  simp only [stepFn, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The step approximations of a step function converge to it in `L²`. -/
lemma stepFn_step_ms {m : ℕ} (c α β : Fin m → ℝ) {a b : ℝ} (hab : a ≤ b)
    (haα : ∀ j, a ≤ α j) (hβb : ∀ j, β j ≤ b) :
    Tendsto (fun n => ∫ s, (stepFn (fun s => ∑ j, c j * ind (α j) (β j) s) a b n s -
      ∑ j, c j * ind (α j) (β j) s) ^ 2) atTop (𝓝 0) := by
  set C := (m : ℝ) * ∑ j, c j ^ 2
  have hC : 0 ≤ C := by positivity
  have hi : ∀ n j, Integrable (fun s => (stepFn (ind (α j) (β j)) a b n s - ind (α j) (β j) s) ^ 2) :=
    fun n j => ((memLp_stepFn _ a b n).sub (memLp_ind _ _)).integrable_sq
  have hbound : ∀ n : ℕ, ∫ s, (stepFn (fun s => ∑ j, c j * ind (α j) (β j) s) a b n s -
      ∑ j, c j * ind (α j) (β j) s) ^ 2 ≤ C * (2 * ((b - a) / (n + 1))) := by
    intro n
    have hpt : ∀ s, (stepFn (fun s => ∑ j, c j * ind (α j) (β j) s) a b n s -
        ∑ j, c j * ind (α j) (β j) s) ^ 2 ≤
        ∑ j, (m : ℝ) * c j ^ 2 * (stepFn (ind (α j) (β j)) a b n s - ind (α j) (β j) s) ^ 2 := by
      intro s
      rw [stepFn_sum_ind, ← Finset.sum_sub_distrib]
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
        (f := fun j => c j * stepFn (ind (α j) (β j)) a b n s - c j * ind (α j) (β j) s)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      refine h.trans (le_of_eq ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    calc _ ≤ ∫ s, ∑ j, (m : ℝ) * c j ^ 2 *
          (stepFn (ind (α j) (β j)) a b n s - ind (α j) (β j) s) ^ 2 :=
          integral_mono (by
              have h1 := ((memLp_stepFn (fun s => ∑ j, c j * ind (α j) (β j) s) a b n).sub
                (memLp_finset_sum' Finset.univ fun j _ => (memLp_ind (α j) (β j)).const_mul (c j)))
              refine h1.integrable_sq.congr (Eventually.of_forall fun s => ?_)
              simp [Finset.sum_apply])
            (integrable_finset_sum _ fun j _ => (hi n j).const_mul _) hpt
      _ = ∑ j, (m : ℝ) * c j ^ 2 *
          ∫ s, (stepFn (ind (α j) (β j)) a b n s - ind (α j) (β j) s) ^ 2 := by
          rw [integral_finset_sum _ fun j _ => (hi n j).const_mul _]
          exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
      _ ≤ ∑ j, (m : ℝ) * c j ^ 2 * (2 * ((b - a) / (n + 1))) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (integral_stepFn_ind_sub_sq_le hab (haα j) (hβb j) n) (by positivity)
      _ = C * (2 * ((b - a) / (n + 1))) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hlim : Tendsto (fun n : ℕ => C * (2 * ((b - a) / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)).const_mul 2
      |>.const_mul C
    simp only [mul_zero] at h
    refine h.congr fun n => ?_
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => integral_nonneg fun s => sq_nonneg _) hbound

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- The deterministic simple integrand `Σⱼ cⱼ 1_{(αⱼ, βⱼ]}`. -/
def stepIntegrand (hW : IsWiener W P) {m : ℕ} (c α β : Fin m → ℝ) (hα : ∀ j, 0 ≤ α j)
    (hαβ : ∀ j, α j ≤ β j) : SimpleIntegrand W hW.measurable P (Fin m) where
  left := α
  right := β
  val j := fun _ => c j
  left_nonneg := hα
  left_le_right := hαβ
  adapted _ := stronglyMeasurable_const
  memLp _ := by haveI := hW.isProbabilityMeasure; exact memLp_const _

lemma stepIntegrand_process (hW : IsWiener W P) {m : ℕ} (c α β : Fin m → ℝ) (hα : ∀ j, 0 ≤ α j)
    (hαβ : ∀ j, α j ≤ β j) (s : ℝ) (ω : Ω) :
    (stepIntegrand hW c α β hα hαβ).process s ω = ∑ j, c j * ind (α j) (β j) s := rfl

lemma stepIntegrand_integral (hW : IsWiener W P) {m : ℕ} (c α β : Fin m → ℝ) (hα : ∀ j, 0 ≤ α j)
    (hαβ : ∀ j, α j ≤ β j) (ω : Ω) :
    (stepIntegrand hW c α β hα hαβ).integral ω = ∑ j, c j * (W (β j) ω - W (α j) ω) := rfl

namespace IsWiener

variable (hW : IsWiener W P)
include hW

/-- **The Wiener integral agrees with the simple integral on step functions.**  For
`f = Σⱼ cⱼ 1_{(αⱼ, βⱼ]}` with `0 ≤ a ≤ αⱼ ≤ βⱼ ≤ b`, the left-point Riemann sums of `f` converge in
mean square to the simple integral `Σⱼ cⱼ (W(βⱼ) - W(αⱼ))`; hence
`∫ₐᵇ f dW = Σⱼ cⱼ (W(βⱼ) - W(αⱼ))` almost surely. -/
theorem wienerInt_step {m : ℕ} (c α β : Fin m → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (haα : ∀ j, a ≤ α j) (hαβ : ∀ j, α j ≤ β j) (hβb : ∀ j, β j ≤ b) :
    wienerInt W P (fun s => ∑ j, c j * ind (α j) (β j) s) a b =ᵐ[P]
      (stepIntegrand hW c α β (fun j => ha.trans (haα j)) hαβ).integral := by
  have := hW.isProbabilityMeasure
  set f := fun s => ∑ j, c j * ind (α j) (β j) s
  set G := stepIntegrand hW c α β (fun j => ha.trans (haα j)) hαβ
  refine msLim_unique (fun n => memLp_riemannSum hW ha hab n)
    (SimpleIntegrand.memLp_integral hW G) ?_
  have key : ∀ n, ∫ ω, (riemannSum W f a b n ω - G.integral ω) ^ 2 ∂P =
      ∫ s, (stepFn f a b n s - f s) ^ 2 := by
    intro n
    set H := (detSimple hW f ha hab n).add (G.smul (-1))
    have h1 : ∀ ω, H.integral ω = riemannSum W f a b n ω - G.integral ω := by
      intro ω
      simp only [H, SimpleIntegrand.integral_add, SimpleIntegrand.integral_smul,
        riemannSum_eq hW ha hab, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ s ω, H.process s ω = stepFn f a b n s - f s := by
      intro s ω
      simp only [H, SimpleIntegrand.process_add, SimpleIntegrand.process_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, process_detSimple, G, stepIntegrand_process, f]
      ring
    have := SimpleIntegrand.integral_sq hW H
    simp only [h1, h2, integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  simp only [key]
  exact stepFn_step_ms c α β hab haα hβb

end IsWiener

/-- **Instance (standard Wiener process).** For `f = 2·1_{(0,1]} - 1_{(1,3]}`,
`∫₀³ f dW = 2(W(1) - W(0)) - (W(3) - W(1))` almost surely. -/
theorem wienerInt_step_stdWiener :
    wienerInt stdWiener stdWienerMeasure (fun s => 2 * ind 0 1 s + -1 * ind 1 3 s) 0 3 =ᵐ[stdWienerMeasure]
      fun ω => 2 * (stdWiener 1 ω - stdWiener 0 ω) - (stdWiener 3 ω - stdWiener 1 ω) := by
  have h := isWiener_stdWiener.wienerInt_step ![2, -1] ![0, 1] ![1, 3] (a := 0) (b := 3) le_rfl (by norm_num)
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun j => by fin_cases j <;> norm_num)
  simp only [Fin.sum_univ_two] at h
  refine h.trans (Eventually.of_forall fun ω => ?_)
  rw [stepIntegrand_integral]
  simp [Fin.sum_univ_two]
  ring

end Gardiner.Ito
