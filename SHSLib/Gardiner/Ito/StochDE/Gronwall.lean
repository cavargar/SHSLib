/-
# Integral Gronwall inequalities in `ℝ≥0∞`

* `lintegral_Ioc_pow`: `∫_{(t₀, t]} ((L (s - t₀))ᵏ / k!) ds = (L (t - t₀))^{k+1} / ((k+1)! L)`, in the
  form `L ∫ R_k = R_{k+1}`;
* `gronwall_ennreal`: if `ψ` is monotone and finite on `[t₀, T]` and
  `ψ t ≤ α + L ∫_{t₀}^t ψ`, then `ψ t ≤ α e^{L (t - t₀)}`;
* `iterate_bound_ennreal`: if `Δ₀ ≤ M` and `Δ_{n+1} t ≤ L ∫_{t₀}^t Δ_n`, then
  `Δ_n t ≤ M (L (t - t₀))ⁿ / n!` (the Picard iteration bound).
-/
import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

/-- `R L t₀ k t = (L (t - t₀))ᵏ / k!` as an element of `ℝ≥0∞`. -/
def gronR (L t₀ : ℝ) (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((L * (t - t₀)) ^ k / k.factorial)

lemma measurable_gronR (L t₀ : ℝ) (k : ℕ) : Measurable (gronR L t₀ k) := by
  unfold gronR
  exact ENNReal.measurable_ofReal.comp
    ((((measurable_const.mul (measurable_id.sub_const t₀)).pow_const k)).div_const _)

lemma gronR_zero (L t₀ t : ℝ) : gronR L t₀ 0 t = 1 := by simp [gronR]

lemma integral_Ioc_sub_pow {t₀ t : ℝ} (h : t₀ ≤ t) (k : ℕ) :
    ∫ s in Set.Ioc t₀ t, (s - t₀) ^ k = (t - t₀) ^ (k + 1) / (k + 1) := by
  rw [← intervalIntegral.integral_of_le h,
    intervalIntegral.integral_comp_sub_right (fun s => s ^ k) t₀, sub_self, integral_pow]
  simp

/-- `L ∫_{(t₀, t]} R_k = R_{k+1}(t)`. -/
lemma mul_lintegral_gronR {L t₀ t : ℝ} (hL : 0 ≤ L) (h : t₀ ≤ t) (k : ℕ) :
    ENNReal.ofReal L * ∫⁻ s in Set.Ioc t₀ t, gronR L t₀ k s = gronR L t₀ (k + 1) t := by
  have hint : IntegrableOn (fun s => (L * (s - t₀)) ^ k / k.factorial) (Set.Ioc t₀ t) := by
    refine (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc t₀ t)]
      fun s => (L * (s - t₀)) ^ k / k.factorial := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have : 0 ≤ s - t₀ := sub_nonneg.mpr hs.1.le
    positivity
  unfold gronR
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← ENNReal.ofReal_mul hL]
  congr 1
  have e : ∀ s, (L * (s - t₀)) ^ k / k.factorial = (L ^ k / k.factorial) * (s - t₀) ^ k := by
    intro s; rw [mul_pow]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_Ioc_sub_pow h, Nat.factorial_succ]
  push_cast
  rw [mul_pow]
  field_simp
  ring

/-- **Gronwall's inequality** (integral form, `ℝ≥0∞`-valued, monotone `ψ`). -/
theorem gronwall_ennreal {ψ : ℝ → ℝ≥0∞} {t₀ T L : ℝ} {α : ℝ≥0∞} (hL : 0 ≤ L)
    (hmono : MonotoneOn ψ (Set.Icc t₀ T)) (hfin : ψ T ≠ ⊤)
    (h : ∀ t ∈ Set.Icc t₀ T, ψ t ≤ α + ENNReal.ofReal L * ∫⁻ s in Set.Ioc t₀ t, ψ s) :
    ∀ t ∈ Set.Icc t₀ T, ψ t ≤ α * ENNReal.ofReal (Real.exp (L * (t - t₀))) := by
  -- the iterated bound
  have key : ∀ n : ℕ, ∀ t ∈ Set.Icc t₀ T,
      ψ t ≤ α * (∑ k ∈ Finset.range n, gronR L t₀ k t) + ψ T * gronR L t₀ n t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, gronR_zero, mul_one]
      exact hmono ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2
    | succ n ih =>
      intro t ht
      refine (h t ht).trans ?_
      have hle : ∫⁻ s in Set.Ioc t₀ t, ψ s ≤ ∫⁻ s in Set.Ioc t₀ t,
          (α * (∑ k ∈ Finset.range n, gronR L t₀ k s) + ψ T * gronR L t₀ n s) := by
        refine setLIntegral_mono ?_ fun s hs => ih s ⟨hs.1.le, hs.2.trans ht.2⟩
        exact (measurable_const.mul (Finset.measurable_fun_sum _ fun k _ =>
          measurable_gronR L t₀ k)).add (measurable_const.mul (measurable_gronR L t₀ n))
      have hcomp : ENNReal.ofReal L * ∫⁻ s in Set.Ioc t₀ t,
          (α * (∑ k ∈ Finset.range n, gronR L t₀ k s) + ψ T * gronR L t₀ n s) =
          α * (∑ k ∈ Finset.range n, gronR L t₀ (k + 1) t) + ψ T * gronR L t₀ (n + 1) t := by
        rw [lintegral_add_left (measurable_const.mul (Finset.measurable_fun_sum _ fun k _ =>
            measurable_gronR L t₀ k)), lintegral_const_mul _ (Finset.measurable_fun_sum _
            fun k _ => measurable_gronR L t₀ k), lintegral_const_mul _ (measurable_gronR L t₀ n),
          lintegral_finset_sum _ fun k _ => measurable_gronR L t₀ k, mul_add,
          Finset.mul_sum, Finset.mul_sum]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← mul_assoc, mul_comm (ENNReal.ofReal L) α, mul_assoc,
            mul_lintegral_gronR hL ht.1]
        · rw [← mul_assoc, mul_comm (ENNReal.ofReal L), mul_assoc, mul_lintegral_gronR hL ht.1]
      calc α + ENNReal.ofReal L * ∫⁻ s in Set.Ioc t₀ t, ψ s
          ≤ α + (α * (∑ k ∈ Finset.range n, gronR L t₀ (k + 1) t) +
              ψ T * gronR L t₀ (n + 1) t) := by
            rw [← hcomp]; gcongr
        _ = α * (∑ k ∈ Finset.range (n + 1), gronR L t₀ k t) + ψ T * gronR L t₀ (n + 1) t := by
            rw [Finset.sum_range_succ', gronR_zero, mul_add, mul_one]
            ring
  intro t ht
  set x := L * (t - t₀)
  have hx : 0 ≤ x := mul_nonneg hL (sub_nonneg.mpr ht.1)
  have hsum : ∀ n, ∑ k ∈ Finset.range n, gronR L t₀ k t ≤ ENNReal.ofReal (Real.exp x) := by
    intro n
    unfold gronR
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
    exact ENNReal.ofReal_le_ofReal (Real.sum_le_exp_of_nonneg hx n)
  have hR : Tendsto (fun n => gronR L t₀ n t) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp
      (FloorSemiring.tendsto_pow_div_factorial_atTop x)
    simpa [gronR] using this
  have hlim : Tendsto (fun n => α * ENNReal.ofReal (Real.exp x) + ψ T * gronR L t₀ n t) atTop
      (𝓝 (α * ENNReal.ofReal (Real.exp x))) := by
    simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hR (Or.inr hfin))
  refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  exact (key n t ht).trans (by gcongr; exact hsum n)

/-- **The Picard iteration bound**: `Δ_n t ≤ M (L (t - t₀))ⁿ / n!`. -/
theorem iterate_bound_ennreal {Δ : ℕ → ℝ → ℝ≥0∞} {t₀ T L : ℝ} {M : ℝ≥0∞} (hL : 0 ≤ L)
    (h0 : ∀ t ∈ Set.Icc t₀ T, Δ 0 t ≤ M)
    (hstep : ∀ n, ∀ t ∈ Set.Icc t₀ T,
      Δ (n + 1) t ≤ ENNReal.ofReal L * ∫⁻ s in Set.Ioc t₀ t, Δ n s) :
    ∀ n, ∀ t ∈ Set.Icc t₀ T, Δ n t ≤ M * gronR L t₀ n t := by
  intro n
  induction n with
  | zero => intro t ht; simpa [gronR_zero] using h0 t ht
  | succ n ih =>
    intro t ht
    refine (hstep n t ht).trans ?_
    calc ENNReal.ofReal L * ∫⁻ s in Set.Ioc t₀ t, Δ n s
        ≤ ENNReal.ofReal L * ∫⁻ s in Set.Ioc t₀ t, M * gronR L t₀ n s := by
          refine mul_le_mul' le_rfl ?_
          exact setLIntegral_mono (measurable_const.mul (measurable_gronR L t₀ n))
            fun s (hs : s ∈ Set.Ioc t₀ t) => ih s ⟨hs.1.le, hs.2.trans ht.2⟩
      _ = M * gronR L t₀ (n + 1) t := by
          rw [lintegral_const_mul _ (measurable_gronR L t₀ n), ← mul_assoc,
            mul_comm (ENNReal.ofReal L) M, mul_assoc, mul_lintegral_gronR hL ht.1]

end Gardiner.Ito.StochDE
