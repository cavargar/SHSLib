/-
# Mean-square limits

Helper layer for the Wiener integral: mean-square convergence is convergence in `L²(P)`.
`Gardiner.Ito.msLim X P` is a mean-square limit of a mean-square Cauchy sequence of `L²` random
variables (`Gardiner.Ito.exists_msLim`, `Gardiner.Ito.msLim_spec`); it is unique almost surely
(`Gardiner.Ito.ms_unique`, `Gardiner.Ito.msLim_unique`, `Gardiner.Ito.ms_ae_unique`).
Correlations and means pass to mean-square limits (`Gardiner.Ito.tendsto_integral_mul_of_ms`,
`Gardiner.Ito.tendsto_integral_of_ms`), and so do centred Gaussian laws with converging variances
(`Gardiner.Ito.map_eq_gaussianReal_of_ms`, via characteristic functions).
-/
import SHSLib.Gardiner.Ito.Simple

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma inner_toLp {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    @inner ℝ _ _ (hX.toLp X) (hY.toLp Y) = ∫ ω, X ω * Y ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω h1 h2
  simp [h1, h2, mul_comm]

lemma norm_toLp_sub_sq {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    ‖hX.toLp X - hY.toLp Y‖ ^ 2 = ∫ ω, (X ω - Y ω) ^ 2 ∂P := by
  rw [← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, inner_toLp]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [sq]

/-- Mean-square convergence is convergence in `L²`. -/
lemma tendsto_toLp_of_ms {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hY : MemLp Y 2 P) (h : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hY.toLp Y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun n => Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P)) atTop (𝓝 0) := by
    simpa using h.sqrt
  refine h2.congr fun n => ?_
  rw [← norm_toLp_sub_sq (hX n) hY, Real.sqrt_sq (norm_nonneg _)]

/-- **Existence of mean-square limits** (completeness of `L²`): a mean-square Cauchy sequence has
a mean-square limit. -/
theorem exists_msLim {X : ℕ → Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ ω, (X m ω - X n ω) ^ 2 ∂P < ε) :
    ∃ Y, MemLp Y 2 P ∧ Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
  set F : ℕ → Lp ℝ 2 P := fun n => (hX n).toLp (X n)
  have hF : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hC (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h := hN m hm n hn
    rw [← norm_toLp_sub_sq (hX m) (hX n)] at h
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hF
  refine ⟨L, Lp.memLp L, ?_⟩
  have h1 : Tendsto (fun n => ‖F n - L‖ ^ 2) atTop (𝓝 (0 ^ 2)) :=
    ((tendsto_iff_norm_sub_tendsto_zero.mp hL).pow 2)
  rw [zero_pow two_ne_zero] at h1
  refine h1.congr fun n => ?_
  have := norm_toLp_sub_sq (hX n) (Lp.memLp L)
  rw [Lp.toLp_coeFn] at this
  exact this

open Classical in
/-- The **mean-square limit** `ms-lim Xₙ` (Gardiner §2.9.2), chosen when it exists (and `0`
otherwise).  It is unique up to almost-everywhere equality (`Gardiner.Ito.msLim_unique`). -/
def msLim (X : ℕ → Ω → ℝ) (P : Measure Ω) : Ω → ℝ :=
  if h : ∃ Y, MemLp Y 2 P ∧ Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) then
    h.choose else 0

theorem msLim_spec {X : ℕ → Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ ω, (X m ω - X n ω) ^ 2 ∂P < ε) :
    MemLp (msLim X P) 2 P ∧
      Tendsto (fun n => ∫ ω, (X n ω - msLim X P ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have h := exists_msLim hX hC
  rw [msLim, dif_pos h]
  exact h.choose_spec

/-- Mean-square limits are unique almost everywhere. -/
theorem ms_unique {X : ℕ → Ω → ℝ} {Y Z : Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P)
    (h1 : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫ ω, (X n ω - Z ω) ^ 2 ∂P) atTop (𝓝 0)) : Y =ᵐ[P] Z := by
  have := tendsto_nhds_unique (tendsto_toLp_of_ms hX hY h1) (tendsto_toLp_of_ms hX hZ h2)
  exact (MemLp.toLp_eq_toLp_iff hY hZ).mp this

theorem msLim_unique {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hY : MemLp Y 2 P) (h : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0)) :
    msLim X P =ᵐ[P] Y := by
  have hex : ∃ Y, MemLp Y 2 P ∧ Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) :=
    ⟨Y, hY, h⟩
  have hs : MemLp (msLim X P) 2 P ∧
      Tendsto (fun n => ∫ ω, (X n ω - msLim X P ω) ^ 2 ∂P) atTop (𝓝 0) := by
    rw [msLim, dif_pos hex]; exact hex.choose_spec
  exact ms_unique hX hs.1 hY hs.2 h

/-- Correlations pass to mean-square limits. -/
theorem tendsto_integral_mul_of_ms {X Y : ℕ → Ω → ℝ} {X' Y' : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hY : ∀ n, MemLp (Y n) 2 P) (hX' : MemLp X' 2 P)
    (hY' : MemLp Y' 2 P) (h1 : Tendsto (fun n => ∫ ω, (X n ω - X' ω) ^ 2 ∂P) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫ ω, (Y n ω - Y' ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω * Y n ω ∂P) atTop (𝓝 (∫ ω, X' ω * Y' ω ∂P)) := by
  have h := (tendsto_toLp_of_ms hX hX' h1).inner (𝕜 := ℝ) (tendsto_toLp_of_ms hY hY' h2)
  simp only [inner_toLp] at h
  exact h

/-- Means pass to mean-square limits. -/
theorem tendsto_integral_of_ms [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {X' : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hX' : MemLp X' 2 P)
    (h1 : Tendsto (fun n => ∫ ω, (X n ω - X' ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 (∫ ω, X' ω ∂P)) := by
  have h := tendsto_integral_mul_of_ms hX (fun _ => memLp_const (1 : ℝ)) hX'
    (memLp_const (1 : ℝ)) h1 (by simp)
  simpa using h

lemma norm_toLp_sq {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ‖hX.toLp X‖ ^ 2 = ∫ ω, X ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  simp [sq]

/-- `E|Z| ≤ √(E Z²)` on a probability space. -/
lemma integral_abs_le_sqrt [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    ∫ ω, |Z ω| ∂P ≤ Real.sqrt (∫ ω, Z ω ^ 2 ∂P) := by
  have hA : MemLp (fun ω => |Z ω|) 2 P := hZ.abs
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  have h := real_inner_le_norm (hA.toLp _) (h1.toLp _)
  rw [inner_toLp] at h
  have hn1 : ‖h1.toLp (fun _ : Ω => (1 : ℝ))‖ = 1 := by
    have := norm_toLp_sq h1
    simp only [one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one] at this
    nlinarith [norm_nonneg (h1.toLp (fun _ : Ω => (1 : ℝ))), sq_nonneg
      (‖h1.toLp (fun _ : Ω => (1 : ℝ))‖ - 1)]
  have hnA : ‖hA.toLp (fun ω => |Z ω|)‖ = Real.sqrt (∫ ω, Z ω ^ 2 ∂P) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq hA]
    simp
  rw [hn1, hnA, mul_one] at h
  simpa using h

lemma charFun_map_eq_integral {Z : Ω → ℝ} (hZ : AEMeasurable Z P) (u : ℝ) :
    charFun (P.map Z) u = ∫ ω, Complex.exp (u * Z ω * Complex.I) ∂P := by
  rw [charFun_apply_real, integral_map hZ (by fun_prop)]

lemma norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have h : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I) =
      Complex.exp (b * Complex.I) * (Complex.exp (Complex.I * (a - b : ℝ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; push_cast; ring_nf
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- **Mean-square limits of Gaussian variables are Gaussian**: if `Xₙ ~ N(mₙ, vₙ)`,
`mₙ → m`, `vₙ → v` and `Xₙ → Y` in mean square, then `Y ~ N(m, v)`. -/
theorem map_eq_gaussianReal_of_ms [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hY : MemLp Y 2 P) {m : ℕ → ℝ} {v : ℕ → ℝ≥0} {m' : ℝ}
    {v' : ℝ≥0} (hlaw : ∀ n, P.map (X n) = gaussianReal (m n) (v n))
    (hm : Tendsto m atTop (𝓝 m')) (hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 v'))
    (h : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0)) :
    P.map Y = gaussianReal m' v' := by
  have := Measure.isProbabilityMeasure_map (μ := P) hY.aestronglyMeasurable.aemeasurable
  refine Measure.ext_of_charFun (funext fun u => ?_)
  -- the characteristic functions of `Xₙ` converge to that of `Y`
  have h1 : Tendsto (fun n => charFun (P.map (X n)) u) atTop (𝓝 (charFun (P.map Y) u)) := by
    have hd : ∀ n, ‖charFun (P.map (X n)) u - charFun (P.map Y) u‖ ≤
        |u| * Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P) := by
      intro n
      rw [charFun_map_eq_integral (hX n).aestronglyMeasurable.aemeasurable,
        charFun_map_eq_integral hY.aestronglyMeasurable.aemeasurable,
        ← integral_sub (Integrable.of_bound ((by fun_prop : Continuous fun x : ℝ =>
            Complex.exp (u * x * Complex.I)).comp_aestronglyMeasurable
            (hX n).aestronglyMeasurable) 1 (Eventually.of_forall fun ω => by
          simpa using (Complex.norm_exp_ofReal_mul_I (u * X n ω)).le))
          (Integrable.of_bound ((by fun_prop : Continuous fun x : ℝ =>
            Complex.exp (u * x * Complex.I)).comp_aestronglyMeasurable
            hY.aestronglyMeasurable) 1 (Eventually.of_forall fun ω => by
          simpa using (Complex.norm_exp_ofReal_mul_I (u * Y ω)).le))]
      have hZ : MemLp (fun ω => X n ω - Y ω) 2 P := (hX n).sub hY
      calc ‖∫ ω, (Complex.exp (u * X n ω * Complex.I) - Complex.exp (u * Y ω * Complex.I)) ∂P‖
          ≤ ∫ ω, ‖Complex.exp (u * X n ω * Complex.I) - Complex.exp (u * Y ω * Complex.I)‖ ∂P :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ ω, |u| * |X n ω - Y ω| ∂P := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((hZ.integrable one_le_two).abs.const_mul _) (Eventually.of_forall fun ω => ?_)
            have := norm_exp_sub_exp_le (u * X n ω) (u * Y ω)
            push_cast at this
            calc _ ≤ |u * X n ω - u * Y ω| := this
              _ = |u| * |X n ω - Y ω| := by rw [← mul_sub, abs_mul]
        _ = |u| * ∫ ω, |X n ω - Y ω| ∂P := integral_const_mul _ _
        _ ≤ |u| * Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P) :=
            mul_le_mul_of_nonneg_left (integral_abs_le_sqrt hZ) (abs_nonneg _)
    have hlim : Tendsto (fun n => |u| * Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P)) atTop
        (𝓝 0) := by
      simpa using (h.sqrt).const_mul |u|
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hd hlim
  -- the Gaussian characteristic functions converge
  have h2 : Tendsto (fun n => charFun (P.map (X n)) u) atTop
      (𝓝 (charFun (gaussianReal m' v') u)) := by
    simp only [hlaw, charFun_gaussianReal]
    refine (Complex.continuous_exp.tendsto _).comp ?_
    refine Tendsto.sub ?_ ?_
    · exact ((Complex.continuous_ofReal.tendsto _).comp hm).const_mul _ |>.mul_const _
    · exact (((Complex.continuous_ofReal.tendsto _).comp hv).mul_const _).div_const _
  exact tendsto_nhds_unique h1 h2

/-- A mean-square limit agrees almost surely with an almost-sure limit. -/
theorem ms_ae_unique {X : ℕ → Ω → ℝ} {Y Z : Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hY : MemLp Y 2 P) (h : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0))
    (hZ : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω))) : Y =ᵐ[P] Z := by
  have hL := tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_toLp_of_ms hX hY h)
  have he : Tendsto (fun n => eLpNorm (X n - Y) 2 P) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => ENNReal.ofReal ‖(hX n).toLp (X n) - hY.toLp Y‖) atTop
        (𝓝 (ENNReal.ofReal 0)) := (ENNReal.continuous_ofReal.tendsto 0).comp hL
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr fun n => ?_
    rw [← MemLp.toLp_sub, Lp.norm_toLp, ENNReal.ofReal_toReal ((hX n).sub hY).eLpNorm_ne_top]
  have hm := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    (fun n => (hX n).aestronglyMeasurable) hY.aestronglyMeasurable he
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hae, hZ] with ω h1 h2
  exact tendsto_nhds_unique h1 (h2.comp hns.tendsto_atTop)

end Gardiner.Ito
