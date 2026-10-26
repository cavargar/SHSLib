/-
# Itô's formula in one dimension (Gardiner §4.3.3, (4.3.14); §4.2.6 d, (4.2.39))

Let `x(t) = x(0) + ∫₀ᵗ a(s) ds + b W(t)` be an Itô process with an adapted drift `a` whose paths
are continuous and a constant noise coefficient `b`.  For `F(t, x)` of class `C^{1,2}`
(`Gardiner.Ito.IsC12`) satisfying mean-square moment conditions along the process,

`F(T, x(T)) - F(0, x(0)) = ∫₀ᵀ (F_t + a F_x + ½ b² F_xx)(s, x(s)) ds + ∫₀ᵀ b F_x(s, x(s)) dW(s)`

almost surely (`Gardiner.Ito.IsFWiener.ito_formula`).  No boundedness of `F'`, `F''` is needed —
only the mean-square conditions `MSBounded`/`MSUnifCont`, which hold for exponentials and
polynomials of `W` (see `Gardiner.Ito.ItoExamples`).

The proof: along the uniform partitions, the left-point sums of `F_x` converge in mean square to
the Itô integral (`itoRiemann_tendsto`) and the weighted quadratic variation tends to zero in mean
square (`integral_wqv_sq`).  A subsequence converges almost surely, and on each such path the
deterministic `IsC12.ito_pathwise` applies.
-/
import SHSLib.Gardiner.Ito.Calculus.ItoPath

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- `G` is bounded in mean square on `[0, T]` (and each `G t` is square integrable). -/
def MSBounded (P : Measure Ω) (T : ℝ) (G : ℝ → Ω → ℝ) : Prop :=
  ∃ M, ∀ t ∈ Icc 0 T, MemLp (G t) 2 P ∧ ∫ ω, G t ω ^ 2 ∂P ≤ M

/-- `G` is uniformly continuous in mean square on `[0, T]`. -/
def MSUnifCont (P : Measure Ω) (T : ℝ) (G : ℝ → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ s t, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → |s - t| < δ →
    ∫ ω, (G s ω - G t ω) ^ 2 ∂P < ε

/-- A jointly measurable, adapted process which is bounded in mean square is an Itô integrand. -/
lemma isItoIntegrand_of_msBounded {𝓕 : Filtration ℝ mΩ} [IsFiniteMeasure P] {T : ℝ}
    {G : ℝ → Ω → ℝ} (hm : Measurable (Function.uncurry G))
    (had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (G t)) (hb : MSBounded P T G) :
    IsItoIntegrand 𝓕 P T G := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨hm, had, ?_⟩
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_
  unfold tsMeasure
  refine (integrable_prod_iff ((hm.pow_const 2).aestronglyMeasurable)).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hM t ⟨ht.1.le, ht.2⟩).1.integrable_sq
  · refine Integrable.mono' (g := fun _ => M) (integrable_const M) ?_ ?_
    · have hsm : StronglyMeasurable (fun p : ℝ × Ω => ‖Function.uncurry G p ^ 2‖) :=
        ((hm.pow_const 2).norm).stronglyMeasurable
      exact (hsm.integral_prod_right' (ν := P)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [Function.uncurry_apply_pair, norm_pow, Real.norm_eq_abs, sq_abs]
      rw [abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact (hM t ⟨ht.1.le, ht.2⟩).2

/-- Nonnegative random variables with `E Zₙ → 0` have an almost surely convergent subsequence. -/
lemma exists_subseq_ae_tendsto_zero {Z : ℕ → Ω → ℝ} (hZi : ∀ n, Integrable (Z n) P)
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (h : Tendsto (fun n => ∫ ω, Z n ω ∂P) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, Tendsto (fun k => Z (ns k) ω) atTop (𝓝 0) := by
  have hm : TendstoInMeasure P Z atTop 0 := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      (fun n => (hZi n).aestronglyMeasurable) aestronglyMeasurable_const ?_
    have e : ∀ n, eLpNorm (Z n - 0) 1 P = ENNReal.ofReal (∫ ω, Z n ω ∂P) := by
      intro n
      rw [sub_zero, eLpNorm_one_eq_lintegral_enorm,
        ofReal_integral_eq_lintegral_ofReal (hZi n) (ae_of_all _ (hZ0 n))]
      congr 1; funext ω; exact Real.enorm_eq_ofReal (hZ0 n ω)
    simp_rw [e]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal h
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  exact ⟨ns, hns, by simpa using hae⟩

lemma tendsto_zero_of_sq_le {A Z : ℕ → ℝ} (hA : ∀ k, A k ^ 2 ≤ Z k)
    (hZ : Tendsto Z atTop (𝓝 0)) : Tendsto A atTop (𝓝 0) := by
  have hs : Tendsto (fun k => Real.sqrt (Z k)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hZ
  refine squeeze_zero_norm (fun k => ?_) hs
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (hA k)

variable {𝓕 : Filtration ℝ mΩ} {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- The weighted quadratic-variation sum is square integrable. -/
lemma IsFWiener.memLp_wqv {T : ℝ} (hT : 0 ≤ T) (n : ℕ) {g : ℕ → Ω → ℝ}
    (hg : ∀ i, StronglyMeasurable[𝓕 (gridPt T n i)] (g i)) (hg2 : ∀ i, MemLp (g i) 2 P) :
    MemLp (fun ω => ∑ i ∈ Finset.range (n + 1), g i ω *
        ((W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T / (n + 1))) 2 P := by
  have hs := memLp_finset_sum' (Finset.range (n + 1)) (p := 2) (μ := P)
    (f := fun i ω => g i ω * ((W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T / (n + 1)))
    (fun i _ => by
      have h := (hW.mul_incr_sq_sub (gridPt_nonneg hT n i) (gridPt_mono hT n (Nat.le_succ i))
        (hg i) (hg2 i)).1
      rw [gridPt_sub] at h
      exact h)
  convert hs using 1
  funext ω; simp [Finset.sum_apply]

/-- **Itô's formula** (Gardiner (4.3.14), time-dependent form (4.2.39)) for the Itô process
`x(t) = x(0) + ∫₀ᵗ a ds + b W(t)` and `F ∈ C^{1,2}` with mean-square moment conditions. -/
theorem IsFWiener.ito_formula {T : ℝ} (hT : 0 < T)
    {F Ft Fx Fxx : ℝ → ℝ → ℝ} (hF : IsC12 F Ft Fx Fxx)
    {x a : ℝ → Ω → ℝ} {x0 : Ω → ℝ} {b : ℝ}
    (hx : ∀ᵐ ω ∂P, ∀ t, x t ω = x0 ω + (∫ s in (0 : ℝ)..t, a s ω) + b * W t ω)
    (ha : ∀ᵐ ω ∂P, Continuous fun t => a t ω)
    (hxm : Measurable (Function.uncurry x))
    (hxad : ∀ t, 0 ≤ t → StronglyMeasurable[𝓕 t] (x t))
    (hFxb : MSBounded P T fun t ω => Fx t (x t ω))
    (hFxc : MSUnifCont P T fun t ω => Fx t (x t ω))
    (hFxxb : MSBounded P T fun t ω => Fxx t (x t ω)) :
    (fun ω => F T (x T ω) - F 0 (x 0 ω)) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, (Ft s (x s ω) + a s ω * Fx s (x s ω) + b ^ 2 / 2 * Fxx s (x s ω))) +
        itoInt W 𝓕 P T (fun s ω => b * Fx s (x s ω)) ω := by
  have := hW.isProbabilityMeasure
  set Gx : ℝ → Ω → ℝ := fun t ω => Fx t (x t ω) with hGx
  have hFx_t : ∀ t, Continuous (Fx t) := fun t =>
    hF.cont_Fx.comp (continuous_const.prodMk continuous_id)
  have hFxx_t : ∀ t, Continuous (Fxx t) := fun t =>
    hF.cont_Fxx.comp (continuous_const.prodMk continuous_id)
  have hGxm : Measurable (Function.uncurry Gx) :=
    hF.cont_Fx.measurable.comp (measurable_fst.prodMk hxm)
  have hGxad : ∀ t, 0 ≤ t → StronglyMeasurable[𝓕 t] (Gx t) := fun t ht =>
    (hFx_t t).comp_stronglyMeasurable (hxad t ht)
  have hG : IsItoIntegrand 𝓕 P T Gx :=
    isItoIntegrand_of_msBounded hGxm (fun t ht _ => hGxad t ht) hFxb
  obtain ⟨Mx, hMx⟩ := hFxb
  obtain ⟨Mxx, hMxx⟩ := hFxxb
  have hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (Gx t) 2 P := fun t h0 h1 => (hMx t ⟨h0, h1⟩).1
  set I := itoInt W 𝓕 P T Gx with hI
  -- (1) stochastic Riemann sums
  have E1 := itoRiemann_tendsto hW hT hG hL2 hFxc
  have hR1m : ∀ n, MemLp (itoRiemann W Gx T n) 2 P := by
    intro n
    rw [← integral_riemElem hT.le hG.adapted hL2 W n]
    exact ElemIntegrand.memLp_integral hW _
  have hIm : MemLp I 2 P := memLp_itoInt hW hG
  -- (2) weighted quadratic variation
  set g : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    Fxx (gridPt T n (min i n)) (x (gridPt T n (min i n)) ω) with hg
  have hgsm : ∀ n i, StronglyMeasurable[𝓕 (gridPt T n i)] (g n i) := fun n i =>
    ((hFxx_t _).comp_stronglyMeasurable (hxad _ (gridPt_nonneg hT.le n _))).mono
      (𝓕.mono (gridPt_mono hT.le n (min_le_left i n)))
  have hgmem : ∀ n i, gridPt T n (min i n) ∈ Icc 0 T := fun n i =>
    ⟨gridPt_nonneg hT.le n _, gridPt_le hT.le (by omega)⟩
  have hg2 : ∀ n i, MemLp (g n i) 2 P := fun n i => (hMxx _ (hgmem n i)).1
  set S2 : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (n + 1), g n i ω *
      ((W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T / (n + 1)) with hS2
  have hS2m : ∀ n, MemLp (S2 n) 2 P := fun n => hW.memLp_wqv hT.le n (hgsm n) (hg2 n)
  have E2 : Tendsto (fun n => ∫ ω, S2 n ω ^ 2 ∂P) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, ∫ ω, S2 n ω ^ 2 ∂P ≤ 2 * T ^ 2 * Mxx * (1 / ((n : ℝ) + 1)) := by
      intro n
      rw [hW.integral_wqv_sq hT.le n (hgsm n) (hg2 n)]
      have hs : ∑ i ∈ Finset.range (n + 1), ∫ ω, g n i ω ^ 2 ∂P ≤ (n + 1) * Mxx := by
        have := Finset.sum_le_sum (s := Finset.range (n + 1))
          (fun i _ => (hMxx _ (hgmem n i)).2)
        simpa using this
      calc 2 * (T / (n + 1)) ^ 2 * ∑ i ∈ Finset.range (n + 1), ∫ ω, g n i ω ^ 2 ∂P
          ≤ 2 * (T / (n + 1)) ^ 2 * ((n + 1) * Mxx) := by gcongr
        _ = 2 * T ^ 2 * Mxx * (1 / ((n : ℝ) + 1)) := by field_simp
    have hlim : Tendsto (fun n : ℕ => 2 * T ^ 2 * Mxx * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * T ^ 2 * Mxx)
      rw [mul_zero] at h
      exact h
    exact squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) hb hlim
  -- (3) quadratic variation
  set S3 : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (n + 1), 1 *
      ((W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω) ^ 2 - T / (n + 1)) with hS3
  have hS3m : ∀ n, MemLp (S3 n) 2 P := fun n =>
    hW.memLp_wqv hT.le n (fun _ => stronglyMeasurable_const) (fun _ => memLp_const 1)
  have E3 : Tendsto (fun n => ∫ ω, S3 n ω ^ 2 ∂P) atTop (𝓝 0) := by
    have e : ∀ n : ℕ, ∫ ω, S3 n ω ^ 2 ∂P = 2 * T ^ 2 * (1 / ((n : ℝ) + 1)) := by
      intro n
      rw [hW.integral_wqv_sq hT.le n (fun _ => stronglyMeasurable_const) (fun _ => memLp_const 1)]
      simp only [one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      push_cast; field_simp
    rw [show (fun n => ∫ ω, S3 n ω ^ 2 ∂P) = fun n : ℕ => 2 * T ^ 2 * (1 / ((n : ℝ) + 1)) from
      funext e]
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * T ^ 2)
    rw [mul_zero] at h
    exact h
  -- (4) a.s. subsequence
  set Z : ℕ → Ω → ℝ := fun n ω =>
    (itoRiemann W Gx T n ω - I ω) ^ 2 + S2 n ω ^ 2 + S3 n ω ^ 2 with hZ
  have hZi : ∀ n, Integrable (Z n) P := fun n =>
    (((hR1m n).sub hIm).integrable_sq.add (hS2m n).integrable_sq).add (hS3m n).integrable_sq
  have hZ0 : ∀ n ω, 0 ≤ Z n ω := fun n ω => by positivity
  have hZlim : Tendsto (fun n => ∫ ω, Z n ω ∂P) atTop (𝓝 0) := by
    have e : ∀ n, ∫ ω, Z n ω ∂P = ∫ ω, (itoRiemann W Gx T n ω - I ω) ^ 2 ∂P +
        ∫ ω, S2 n ω ^ 2 ∂P + ∫ ω, S3 n ω ^ 2 ∂P := by
      intro n
      have i1 : Integrable (fun ω => (itoRiemann W Gx T n ω - I ω) ^ 2) P :=
        ((hR1m n).sub hIm).integrable_sq
      have i2 : Integrable (fun ω => S2 n ω ^ 2) P := (hS2m n).integrable_sq
      have i3 : Integrable (fun ω => S3 n ω ^ 2) P := (hS3m n).integrable_sq
      show ∫ ω, ((itoRiemann W Gx T n ω - I ω) ^ 2 + S2 n ω ^ 2) + S3 n ω ^ 2 ∂P = _
      rw [integral_add (f := fun ω => (itoRiemann W Gx T n ω - I ω) ^ 2 + S2 n ω ^ 2) (i1.add i2) i3,
        integral_add i1 i2]
    simp_rw [e]
    simpa using (E1.add E2).add E3
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto_zero hZi hZ0 hZlim
  -- (5) pathwise conclusion
  have hcI := itoInt_const_mul hW hG b
  filter_upwards [hae, hx, ha, hW.cont, hcI] with ω hω hxω haω hWω hcIω
  rw [hcIω]
  have hX : ∀ t, x t ω = x0 ω + (∫ s in (0 : ℝ)..t, a s ω) + b * W t ω := hxω
  have c1 : Tendsto (fun k => itoRiemann W Gx T (ns k) ω - I ω) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (fun k => by
      have := hZ0 (ns k) ω; simp only [hZ]; nlinarith [sq_nonneg (S2 (ns k) ω),
        sq_nonneg (S3 (ns k) ω)]) hω
  have c2 : Tendsto (fun k => S2 (ns k) ω) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (fun k => by
      simp only [hZ]; nlinarith [sq_nonneg (itoRiemann W Gx T (ns k) ω - I ω),
        sq_nonneg (S3 (ns k) ω)]) hω
  have c3 : Tendsto (fun k => S3 (ns k) ω) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (fun k => by
      simp only [hZ]; nlinarith [sq_nonneg (itoRiemann W Gx T (ns k) ω - I ω),
        sq_nonneg (S2 (ns k) ω)]) hω
  have h1 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1),
      Fx (gridPt T (ns k) i) (x (gridPt T (ns k) i) ω) *
        gridIncr (fun t => W t ω) T (ns k) i) atTop (𝓝 (I ω)) := by
    have := c1.add_const (I ω)
    simp only [sub_add_cancel, zero_add] at this
    exact this
  have h2 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1),
      Fxx (gridPt T (ns k) i) (x (gridPt T (ns k) i) ω) *
        (gridIncr (fun t => W t ω) T (ns k) i ^ 2 - T / (ns k + 1))) atTop (𝓝 0) := by
    refine c2.congr fun k => Finset.sum_congr rfl fun i hi => ?_
    have : min i (ns k) = i := min_eq_left (by simp at hi; omega)
    simp only [hg, this, gridIncr]
  have h3 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1),
      gridIncr (fun t => W t ω) T (ns k) i ^ 2) atTop (𝓝 T) := by
    have := c3.add_const T
    rw [zero_add] at this
    refine this.congr fun k => ?_
    simp only [hS3, one_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, gridIncr]
    push_cast; field_simp; ring
  exact hF.ito_pathwise (X := fun t => x t ω) (a := fun t => a t ω) (w := fun t => W t ω)
    hT haω hWω hX hns h1 h2 h3

end Gardiner.Ito
