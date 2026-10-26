/-
# Itô's formula for functions of `W(t)` and `t`; worked integrals

* `Gardiner.Ito.IsFWiener.ito_formula_W` — Gardiner (4.2.39):
  `f(T, W(T)) - f(0, W(0)) = ∫₀ᵀ (∂ₜf + ½ ∂²_W f) dt + ∫₀ᵀ ∂_W f dW`, under mean-square conditions,
  and `Gardiner.Ito.IsFWiener.ito_formula_W_growth` under moderate-growth conditions (which allow
  exponentials and polynomials).
* `Gardiner.Ito.IsFWiener.itoInt_pow` — Gardiner (4.2.37):
  `∫₀ᵀ Wⁿ dW = W(T)ⁿ⁺¹/(n+1) - (n/2) ∫₀ᵀ Wⁿ⁻¹ dt`.
* `Gardiner.Ito.IsFWiener.ito_exp` — Gardiner (4.2.38): `e^{W(T)} - 1 = ∫₀ᵀ ½ e^{W} dt + ∫₀ᵀ e^{W} dW`.
-/
import SHSLib.Gardiner.Ito.Calculus.Growth

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

lemma ExpGrowth.const_mul {g : ℝ → ℝ → ℝ} {T C K : ℝ} (hg : ExpGrowth g T C K) (c : ℝ) :
    ExpGrowth (fun t x => c * g t x) T (|c| * C) K := by
  refine ⟨continuous_const.mul hg.cont, fun t ht x => ?_, fun s hs t ht x y => ?_⟩
  · rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg.bound t ht x) (abs_nonneg c)
  · rw [← mul_sub, abs_mul, mul_assoc, mul_assoc]
    rw [← mul_assoc C]
    exact mul_le_mul_of_nonneg_left (hg.lip s hs t ht x y) (abs_nonneg c)

lemma ExpGrowth.congr {g h : ℝ → ℝ → ℝ} {T C K : ℝ} (hg : ExpGrowth g T C K) (e : g = h) :
    ExpGrowth h T C K := e ▸ hg

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **Itô's formula for `f(t, W(t))`** (Gardiner (4.2.39)), under mean-square conditions. -/
theorem IsFWiener.ito_formula_W (hWj : Measurable (Function.uncurry W)) {T : ℝ} (hT : 0 < T)
    {F Ft Fx Fxx : ℝ → ℝ → ℝ} (hF : IsC12 F Ft Fx Fxx)
    (hFxb : MSBounded P T fun t ω => Fx t (W t ω))
    (hFxc : MSUnifCont P T fun t ω => Fx t (W t ω))
    (hFxxb : MSBounded P T fun t ω => Fxx t (W t ω)) :
    (fun ω => F T (W T ω) - F 0 (W 0 ω)) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, (Ft s (W s ω) + Fxx s (W s ω) / 2)) +
        itoInt W 𝓕 P T (fun s ω => Fx s (W s ω)) ω := by
  have h := hW.ito_formula hT hF (x := W) (a := fun _ _ => 0) (x0 := fun _ => 0) (b := 1)
    (ae_of_all _ fun ω t => by simp) (ae_of_all _ fun ω => continuous_const) hWj hW.adapted
    hFxb hFxc hFxxb
  have e : (fun s ω => 1 * Fx s (W s ω)) = fun s ω => Fx s (W s ω) := by
    funext s ω; ring
  rw [e] at h
  filter_upwards [h] with ω hω
  rw [hω]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- **Itô's formula for `f(t, W(t))` under moderate growth** of `∂_W f` and `∂²_W f`. -/
theorem IsFWiener.ito_formula_W_growth (hWj : Measurable (Function.uncurry W)) {T : ℝ}
    (hT : 0 < T) {F Ft Fx Fxx : ℝ → ℝ → ℝ} (hF : IsC12 F Ft Fx Fxx) {C K C' K' : ℝ}
    (hFx : ExpGrowth Fx T C K) (hFxx : ExpGrowth Fxx T C' K') :
    (fun ω => F T (W T ω) - F 0 (W 0 ω)) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, (Ft s (W s ω) + Fxx s (W s ω) / 2)) +
        itoInt W 𝓕 P T (fun s ω => Fx s (W s ω)) ω :=
  hW.ito_formula_W hWj hT hF (hFx.msBounded hW) (hFx.msUnifCont hW) (hFxx.msBounded hW)

omit hW in
lemma isC12_pow (n : ℕ) :
    IsC12 (fun _ x => x ^ (n + 1) / (n + 1)) (fun _ _ => 0) (fun _ x => x ^ n)
      (fun _ x => n * x ^ (n - 1)) := by
  refine ⟨continuous_const, by fun_prop, by fun_prop, fun t x => hasDerivAt_const _ _,
    fun t x => ?_, fun t x => hasDerivAt_pow n x⟩
  have := (hasDerivAt_pow (n + 1) x).div_const ((n : ℝ) + 1)
  convert this using 1
  simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
  field_simp

/-- **Gardiner (4.2.37)**: `∫₀ᵀ W(t)ⁿ dW(t) = W(T)ⁿ⁺¹/(n+1) - (n/2) ∫₀ᵀ W(t)ⁿ⁻¹ dt` a.s.
(here `t₀ = 0`, `W(0) = 0`). -/
theorem IsFWiener.itoInt_pow (hWj : Measurable (Function.uncurry W)) {T : ℝ} (hT : 0 < T)
    (n : ℕ) :
    itoInt W 𝓕 P T (fun s ω => W s ω ^ n) =ᵐ[P] fun ω =>
      W T ω ^ (n + 1) / (n + 1) - n / 2 * ∫ s in (0 : ℝ)..T, W s ω ^ (n - 1) := by
  have hFxx : ExpGrowth (fun _ x => (n : ℝ) * x ^ (n - 1)) T (|(n : ℝ)| * (n - 1 + 1).factorial) 1 :=
    (expGrowth_pow T (n - 1)).const_mul n
  have h := hW.ito_formula_W_growth hWj hT (isC12_pow n) (expGrowth_pow T n) hFxx
  filter_upwards [h, hW.zero] with ω hω h0
  simp only [h0] at hω
  have e : ∫ s in (0 : ℝ)..T, (0 + (n : ℝ) * W s ω ^ (n - 1) / 2) =
      n / 2 * ∫ s in (0 : ℝ)..T, W s ω ^ (n - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  rw [e] at hω
  have h00 : (0 : ℝ) ^ (n + 1) / (n + 1) = 0 := by simp
  rw [h00, sub_zero] at hω
  linarith

/-- Consistency with Gardiner (4.2.20): the case `n = 1` of (4.2.37) is `∫₀ᵀ W dW = ½(W(T)² - T)`. -/
theorem IsFWiener.itoInt_pow_one (hWj : Measurable (Function.uncurry W)) {T : ℝ} (hT : 0 < T) :
    itoInt W 𝓕 P T (fun s ω => W s ω ^ 1) =ᵐ[P] fun ω => (W T ω ^ 2 - T) / 2 := by
  filter_upwards [hW.itoInt_pow hWj hT 1] with ω hω
  rw [hω]
  simp only [Nat.cast_one, tsub_self, pow_zero, intervalIntegral.integral_const, smul_eq_mul,
    mul_one, sub_zero]
  ring

/-- **Gardiner (4.2.38)**: `d e^{W} = e^{W}(dW + ½ dt)`, i.e.
`e^{W(T)} - 1 = ∫₀ᵀ ½ e^{W(t)} dt + ∫₀ᵀ e^{W(t)} dW(t)` a.s. -/
theorem IsFWiener.ito_exp (hWj : Measurable (Function.uncurry W)) {T : ℝ} (hT : 0 < T) :
    (fun ω => Real.exp (W T ω) - 1) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, Real.exp (W s ω) / 2) +
        itoInt W 𝓕 P T (fun s ω => Real.exp (W s ω)) ω := by
  have hF : IsC12 (fun _ x => Real.exp x) (fun _ _ => 0) (fun _ x => Real.exp x)
      (fun _ x => Real.exp x) :=
    ⟨continuous_const, by fun_prop, by fun_prop, fun _ _ => hasDerivAt_const _ _,
      fun _ x => Real.hasDerivAt_exp x, fun _ x => Real.hasDerivAt_exp x⟩
  have hg : ExpGrowth (fun _ x => Real.exp x) T _ _ :=
    (expGrowth_exp 1 1 0 T).congr (by funext t x; simp)
  have h := hW.ito_formula_W_growth hWj hT hF hg hg
  filter_upwards [h, hW.zero] with ω hω h0
  rw [h0, Real.exp_zero] at hω
  rw [hω]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp

end Gardiner.Ito
