/-
# Instances of Itô's formula for Itô processes

* `Gardiner.Ito.IsFWiener.isItoProcess_W`: `W` itself is an Itô process (`a = 0`, `b = 1`), using
  `∫₀ᵗ dW = W(t) - W(0)` (`Gardiner.Ito.IsFWiener.itoInt_one`).
* `Gardiner.Ito.IsFWiener.ito_formula_sin_W`: (4.3.14) for `f = sin` along `W`, i.e.
  `sin W(T) - sin W(0) = -½ ∫₀ᵀ sin W dt + ∫₀ᵀ cos W dW`.
* `Gardiner.Ito.IsFWiener.isItoProcess_sin_W`: hence `sin W` is an Itô process with the random
  noise coefficient `b = cos W`.
* `Gardiner.Ito.IsFWiener.ito_formula_sin_sin_W`: (4.3.14) for `f = sin` along the Itô process
  `x = sin W`, an instance with a genuinely random, non-constant `b`.
-/
import SHSLib.Gardiner.Ito.Calculus.ItoGeneral
import SHSLib.Gardiner.Ito.Calculus.ItoExamples

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- `∫₀ᵗ dW = W(t) - W(0)` almost surely. -/
theorem IsFWiener.itoInt_one (hWj : Measurable (Function.uncurry W)) {t : ℝ} (ht : 0 ≤ t) :
    itoInt W 𝓕 P t (fun _ _ => 1) =ᵐ[P] fun ω => W t ω - W 0 ω := by
  have := hW.isProbabilityMeasure
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    filter_upwards [itoInt_of_nonpos hW le_rfl (isItoIntegrand_det (𝓕 := 𝓕) (P := P) 0
      (continuous_const (y := (1 : ℝ))))] with ω hω
    rw [hω]; simp
  have hF : IsC12 (fun _ x => x) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0) :=
    ⟨continuous_const, continuous_const, continuous_const, fun _ _ => hasDerivAt_const _ _,
      fun _ x => hasDerivAt_id x, fun _ _ => hasDerivAt_const _ _⟩
  have hb1 : MSBounded P t fun _ _ => (1 : ℝ) :=
    ⟨1, fun _ _ => ⟨memLp_const 1, by simp⟩⟩
  have hc1 : MSUnifCont P t fun _ _ => (1 : ℝ) := fun ε hε =>
    ⟨1, one_pos, fun _ _ _ _ _ _ _ => by simpa using hε⟩
  have hb0 : MSBounded P t fun _ _ => (0 : ℝ) :=
    ⟨0, fun _ _ => ⟨memLp_const 0, by simp⟩⟩
  have h := hW.ito_formula_W hWj hpos hF hb1 hc1 hb0
  filter_upwards [h] with ω hω
  simp only [add_zero, zero_div, intervalIntegral.integral_zero, zero_add] at hω
  exact hω.symm

/-- **The Wiener process is an Itô process** with drift `0` and noise coefficient `1`. -/
theorem IsFWiener.isItoProcess_W (hWj : Measurable (Function.uncurry W)) (T : ℝ) :
    IsItoProcess W 𝓕 P T W (fun _ _ => 0) (fun _ _ => 1) := by
  have := hW.isProbabilityMeasure
  refine ⟨hWj, fun t h0 _ => hW.adapted t h0, hW.cont, ae_of_all _ fun _ => continuous_const,
    isItoIntegrand_det T continuous_const, ae_of_all _ fun _ => continuous_const,
    fun t h0 _ => ?_⟩
  filter_upwards [hW.itoInt_one hWj h0] with ω hω
  rw [hω]; simp

/-- Itô's formula (4.3.14) for `f = sin` along `W`:
`sin W(T) - sin W(0) = ∫₀ᵀ (-½ sin W) dt + ∫₀ᵀ cos W dW`. -/
theorem IsFWiener.ito_formula_sin_W (hWj : Measurable (Function.uncurry W)) {T : ℝ}
    (hT : 0 < T) :
    (fun ω => Real.sin (W T ω) - Real.sin (W 0 ω)) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, -Real.sin (W s ω) / 2) +
        itoInt W 𝓕 P T (fun s ω => Real.cos (W s ω)) ω := by
  have hF : IsC12 (fun _ y => Real.sin y) (fun _ _ => 0) (fun _ y => Real.cos y)
      (fun _ y => -Real.sin y) :=
    ⟨continuous_const, by fun_prop, by fun_prop, fun _ _ => hasDerivAt_const _ _,
      fun _ y => Real.hasDerivAt_sin y, fun _ y => Real.hasDerivAt_cos y⟩
  have h := hW.ito_formula_process hT hF (C1 := 1) (C2 := 1) (fun _ y => Real.abs_cos_le_one y)
    (fun _ y => by rw [abs_neg]; exact Real.abs_sin_le_one y) (hW.isItoProcess_W hWj T)
    zero_le_one (fun _ _ _ => by simp)
  have e : (fun s ω => (fun (_ : ℝ) (_ : Ω) => (1 : ℝ)) s ω * Real.cos (W s ω)) =
      fun s ω => Real.cos (W s ω) := by funext s ω; simp
  rw [e] at h
  filter_upwards [h] with ω hω
  rw [hω]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- `sin W` is an Itô process with drift `-½ sin W` and the random noise coefficient `cos W`. -/
theorem IsFWiener.isItoProcess_sin_W (hWj : Measurable (Function.uncurry W)) (T : ℝ) :
    IsItoProcess W 𝓕 P T (fun t ω => Real.sin (W t ω)) (fun t ω => -Real.sin (W t ω) / 2)
      (fun t ω => Real.cos (W t ω)) := by
  have := hW.isProbabilityMeasure
  have hcos : IsItoIntegrand 𝓕 P T (fun t ω => Real.cos (W t ω)) := by
    have h := isItoIntegrand_mul_bdd (g := fun t ω => Real.cos (W t ω)) (C := 1)
      (isItoIntegrand_det (𝓕 := 𝓕) (P := P) T (continuous_const (y := (1 : ℝ))))
      (Real.continuous_cos.measurable.comp hWj)
      (fun t h0 _ => Real.continuous_cos.comp_stronglyMeasurable (hW.adapted t h0))
      (fun t ω => Real.abs_cos_le_one _)
    simpa using h
  refine ⟨Real.continuous_sin.measurable.comp hWj,
    fun t h0 _ => Real.continuous_sin.comp_stronglyMeasurable (hW.adapted t h0),
    hW.cont.mono fun ω h => Real.continuous_sin.comp h,
    hW.cont.mono fun ω h => (Real.continuous_sin.comp h).neg.div_const 2, hcos,
    hW.cont.mono fun ω h => Real.continuous_cos.comp h, fun t h0 htT => ?_⟩
  rcases h0.eq_or_lt with ht | hpos
  · subst ht
    filter_upwards [itoInt_of_nonpos hW le_rfl (hcos.mono htT)] with ω hω
    rw [hω]; simp
  · filter_upwards [hW.ito_formula_sin_W hWj hpos] with ω hω
    linarith

/-- **Itô's formula along an Itô process with random noise**: (4.3.14) for `f = sin` and
`x = sin W` (drift `-½ sin W`, noise coefficient `cos W`). -/
theorem IsFWiener.ito_formula_sin_sin_W (hWj : Measurable (Function.uncurry W)) {T : ℝ}
    (hT : 0 < T) :
    (fun ω => Real.sin (Real.sin (W T ω)) - Real.sin (Real.sin (W 0 ω))) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, (0 + -Real.sin (W s ω) / 2 * Real.cos (Real.sin (W s ω)) +
        Real.cos (W s ω) ^ 2 / 2 * -Real.sin (Real.sin (W s ω)))) +
        itoInt W 𝓕 P T (fun s ω => Real.cos (W s ω) * Real.cos (Real.sin (W s ω))) ω := by
  have hF : IsC12 (fun _ y => Real.sin y) (fun _ _ => 0) (fun _ y => Real.cos y)
      (fun _ y => -Real.sin y) :=
    ⟨continuous_const, by fun_prop, by fun_prop, fun _ _ => hasDerivAt_const _ _,
      fun _ y => Real.hasDerivAt_sin y, fun _ y => Real.hasDerivAt_cos y⟩
  have h := hW.ito_formula_process hT hF (C1 := 1) (C2 := 1) (fun _ y => Real.abs_cos_le_one y)
    (fun _ y => by rw [abs_neg]; exact Real.abs_sin_le_one y) (hW.isItoProcess_sin_W hWj T)
    zero_le_one (fun _ _ ω => Real.abs_cos_le_one _)
  simp only at h
  exact h

end Gardiner.Ito
