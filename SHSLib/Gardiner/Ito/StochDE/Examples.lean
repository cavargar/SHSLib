/-
# Examples of Itô SDEs with state-dependent coefficients

Gardiner §4.4.2 and §4.4.4, and a nonlinear example.

* **Geometric Brownian motion**, `dx = λ x dt + μ x dW` (4.4.?): `geomBM λ μ x₀ W` (from the Itô
  calculus) solves the SDE on every `[0, T]` (`isSDESol_geomBM`) and is its unique solution
  (`geomBM_unique`).
* **The Ornstein–Uhlenbeck process**, `dx = -k x dt + √D dW` (§4.4.4): the pathwise formula
  `x(t) = x₀ e^{-kt} + √D (W(t) - k ∫₀ᵗ e^{-k(t-s)} W(s) ds)` (`ouProc`, the integration-by-parts
  form of Gardiner's `x₀ e^{-kt} + √D ∫₀ᵗ e^{-k(t-s)} dW(s)`) solves the SDE (`isSDESol_ouProc`)
  and is its unique solution (`ouProc_unique`).
* **A nonlinear example**, `dx = -sin x dt + σ dW`: the coefficients satisfy (4.3.10)–(4.3.11) and
  the Hölder condition, so the SDE has a unique solution on every `[0, T]` and the Euler scheme
  converges with strong order ½ (`sinSDE_existsUnique`, `sinSDE_euler`).
-/
import SHSLib.Gardiner.Ito.StochDE.Euler

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- Square integrability on `(0, T] × Ω` from membership in `L²(tsMeasure P T)`. -/
lemma sq_int_of_memLp_tsMeasure [SFinite P] {x : ℝ → Ω → ℝ} {T : ℝ}
    (hxm : Measurable (Function.uncurry x)) (h : MemLp (Function.uncurry x) 2 (tsMeasure P T)) :
    ∫⁻ s in Set.Ioc 0 T, ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P < ⊤ := by
  have h2 := h.integrable_sq.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at h2
  simp only [enorm_pow] at h2
  unfold tsMeasure at h2
  rwa [lintegral_prod _ ((hxm.enorm.pow_const 2).aemeasurable)] at h2

/-! ### Geometric Brownian motion -/

section GBM

/-- The coefficients `a(x) = λ x`, `b(x) = μ x` satisfy (4.3.10)–(4.3.11) with `K = |λ| + |μ|`. -/
lemma sdeCoeffs_gbm (lam mu t₀ T : ℝ) :
    SDECoeffs (fun x _ => lam * x) (fun x _ => mu * x) t₀ T (|lam| + |mu|) where
  measurable_a := measurable_const.mul measurable_fst
  measurable_b := measurable_const.mul measurable_fst
  K_nonneg := by positivity
  lipschitz t _ x y := by
    rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, add_mul]
  growth t _ x := by
    rw [abs_mul, abs_mul, mul_pow, mul_pow, sq_abs, sq_abs, sq_abs, ← sq_abs lam, ← sq_abs mu]
    nlinarith [abs_nonneg lam, abs_nonneg mu, mul_nonneg (abs_nonneg lam) (abs_nonneg mu),
      sq_nonneg x, sq_abs lam, sq_abs mu, mul_nonneg (mul_nonneg (abs_nonneg lam) (abs_nonneg mu))
        (sq_nonneg x)]

lemma sdeHolder_autonomous {a b : ℝ → ℝ} {t₀ T K : ℝ} (hK : 0 ≤ K) :
    SDEHolder (fun x _ => a x) (fun x _ => b x) t₀ T K where
  holder s _ t _ x := by simp only [sub_self, abs_zero, add_zero]; positivity

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) (hWj : Measurable (Function.uncurry W))
include hW hWj

/-- **Geometric Brownian motion solves `dx = λ x dt + μ x dW`** on `[0, T]`. -/
theorem isSDESol_geomBM (T lam mu : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) :
    IsSDESol W 𝓕 P (fun x _ => lam * x) (fun x _ => mu * x) 0 T x0 (geomBM lam mu x0 W) := by
  have := hW.isProbabilityMeasure
  have hc := sdeCoeffs_gbm lam mu 0 T
  have hx0m : Measurable x0 := (hx0.mono (𝓕.le 0)).measurable
  have hm : Measurable (Function.uncurry (geomBM lam mu x0 W)) := by
    have hcont : Continuous fun p : ℝ × ℝ => Real.exp ((lam - mu ^ 2 / 2) * p.1 + mu * p.2) := by
      fun_prop
    exact (hx0m.comp measurable_snd).mul (hcont.measurable.comp (measurable_fst.prodMk hWj))
  have had : ∀ t ∈ Set.Icc (0 : ℝ) T, StronglyMeasurable[𝓕 t] (geomBM lam mu x0 W t) :=
    fun t ht => hW.geomBM_sm hx0 ht.1
  have hsq : ∫⁻ s in Set.Ioc 0 T, ∫⁻ ω, ‖geomBM lam mu x0 W s ω‖ₑ ^ 2 ∂P < ⊤ := by
    have h := (hW.isItoIntegrand_geomBM_of_memLp hWj T lam mu 1 hx0 hx02).memLp
    simp only [one_mul] at h
    exact sq_int_of_memLp_tsMeasure hm h
  refine ⟨hm, had, ?_, hsq, fun t ht => ?_⟩
  · filter_upwards [hW.cont] with ω hω
    refine Continuous.continuousOn ?_
    unfold geomBM
    fun_prop
  have hD := isItoIntegrand_drive hc le_rfl hm had hsq
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    filter_upwards [hW.zero, itoInt_of_nonpos hW le_rfl (hD.mono ht.2)] with ω h1 h2
    simp [geomBM, h1, h2]
  · have hG := hW.isItoIntegrand_geomBM_of_memLp hWj t lam mu mu hx0 hx02
    filter_upwards [hW.geomBM_ito_of_memLp hWj hpos lam mu hx0 hx02,
      itoInt_congr_of_eq_on hW (hD.mono ht.2) hG (fun s hs ω => by
        simp [drive, afterInd_of_lt hs.1])] with ω h1 h2
    rw [h2]
    linarith

/-- **Geometric Brownian motion is the unique solution of `dx = λ x dt + μ x dW`**: every
solution on `[0, T]` with initial value `x₀` is indistinguishable from `geomBM λ μ x₀ W`. -/
theorem geomBM_unique {T : ℝ} (hT : 0 ≤ T) (lam mu : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) {y : ℝ → Ω → ℝ}
    (hy : IsSDESol W 𝓕 P (fun x _ => lam * x) (fun x _ => mu * x) 0 T x0 y) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, y t ω = geomBM lam mu x0 W t ω :=
  hy.unique hW (isSDESol_geomBM hW hWj T lam mu hx0 hx02) (sdeCoeffs_gbm lam mu 0 T) le_rfl hT
    hx02

end GBM

/-! ### The Ornstein–Uhlenbeck process -/

section OU

/-- **The Ornstein–Uhlenbeck path** driven by a path `w`:
`x(t) = x₀ e^{-kt} + σ (w(t) - k e^{-kt} ∫₀ᵗ e^{ks} w(s) ds)`.  For `w = W(·, ω)` this is the
integration-by-parts form of Gardiner's `x₀ e^{-kt} + σ ∫₀ᵗ e^{-k(t-s)} dW(s)`. -/
def ouSDEPath (k σ x0 : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  x0 * Real.exp (-k * t) + σ * (w t - k * Real.exp (-k * t) * ∫ s in (0 : ℝ)..t, Real.exp (k * s) * w s)

lemma continuous_ouSDEPath (k σ x0 : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (ouSDEPath k σ x0 w) := by
  have hI : Continuous fun t => ∫ s in (0 : ℝ)..t, Real.exp (k * s) * w s :=
    intervalIntegral.continuous_primitive (fun _ _ => (by fun_prop : Continuous fun s =>
      Real.exp (k * s) * w s).intervalIntegrable _ _) 0
  unfold ouSDEPath
  fun_prop

/-- **The OU path solves the integral equation** `x(t) = x₀ - k ∫₀ᵗ x(s) ds + σ w(t)`, for every
continuous path `w`. -/
theorem ouSDEPath_eq (k σ x0 : ℝ) {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    ouSDEPath k σ x0 w t = x0 + (∫ s in (0 : ℝ)..t, -k * ouSDEPath k σ x0 w s) + σ * w t := by
  set I := fun t => ∫ s in (0 : ℝ)..t, Real.exp (k * s) * w s
  set J := fun t => ∫ s in (0 : ℝ)..t, ouSDEPath k σ x0 w s
  have hIc : Continuous fun s => Real.exp (k * s) * w s := by fun_prop
  have hI : ∀ t, HasDerivAt I (Real.exp (k * t) * w t) t := fun t =>
    (hIc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hJ : ∀ t, HasDerivAt J (ouSDEPath k σ x0 w t) t := fun t =>
    ((continuous_ouSDEPath k σ x0 hw).integral_hasStrictDerivAt 0 t).hasDerivAt
  set G := fun t => x0 * Real.exp (-k * t) - σ * k * Real.exp (-k * t) * I t + k * J t
  have hE : ∀ t, HasDerivAt (fun t => Real.exp (-k * t)) (-k * Real.exp (-k * t)) t := fun t => by
    have := ((hasDerivAt_id t).const_mul (-k)).exp
    simpa [mul_comm] using this
  have hG : ∀ t, HasDerivAt G 0 t := by
    intro t
    have h := (((hE t).const_mul x0).sub (((hE t).const_mul (σ * k)).mul (hI t))).add
      ((hJ t).const_mul k)
    convert h using 1
    have e1 : Real.exp (-k * t) * Real.exp (k * t) = 1 := by
      rw [← Real.exp_add]; simp
    simp only [ouSDEPath, I]
    linear_combination (σ * k * w t) * e1
  have hconst : ∀ t, G t = G 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hG t).differentiableAt) (fun t => (hG t).deriv) t 0
  have h0 : G 0 = x0 := by simp [G, I, J]
  have ht := hconst t
  rw [h0] at ht
  simp only [G] at ht
  rw [intervalIntegral.integral_const_mul]
  simp only [ouSDEPath] at ht ⊢
  simp only [J, ouSDEPath] at ht
  linarith

/-- **Uniqueness for the pathwise OU integral equation**: two functions continuous on `[0, T]` that
satisfy `x(t) = x₀ - k ∫₀ᵗ x + g(t)` there coincide on `[0, T]`. -/
theorem ou_integral_eq_unique {k x0 T : ℝ} {g y z : ℝ → ℝ}
    (hy : ContinuousOn y (Set.Icc 0 T)) (hz : ContinuousOn z (Set.Icc 0 T))
    (hye : ∀ t ∈ Set.Icc 0 T, y t = x0 + (∫ s in (0 : ℝ)..t, -k * y s) + g t)
    (hze : ∀ t ∈ Set.Icc 0 T, z t = x0 + (∫ s in (0 : ℝ)..t, -k * z s) + g t) :
    ∀ t ∈ Set.Icc 0 T, y t = z t := by
  set d := fun t => y t - z t
  have hd : ContinuousOn d (Set.Icc 0 T) := hy.sub hz
  have hde : ∀ t ∈ Set.Icc 0 T, d t = -k * ∫ s in (0 : ℝ)..t, d s := by
    intro t ht
    have hyi : IntervalIntegrable y volume 0 t :=
      (hy.mono (by rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc_right ht.2)).intervalIntegrable
    have hzi : IntervalIntegrable z volume 0 t :=
      (hz.mono (by rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc_right ht.2)).intervalIntegrable
    simp only [d]
    rw [hye t ht, hze t ht, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hyi hzi]
    ring
  set ψ : ℝ → ℝ≥0∞ := fun t => ⨆ s ∈ Set.Icc 0 t, ‖d s‖ₑ
  have hle : ∀ t, ∀ s ∈ Set.Icc 0 t, ‖d s‖ₑ ≤ ψ t := fun t s hs =>
    le_iSup₂ (f := fun s (_ : s ∈ Set.Icc 0 t) => ‖d s‖ₑ) s hs
  have hfin : ψ T ≠ ⊤ := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hd
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top
      (iSup₂_le fun s hs => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hC s hs)
  have hg := gronwall_ennreal (ψ := ψ) (α := 0) (abs_nonneg k)
    (fun s _ t _ hst => biSup_mono fun u hu => ⟨hu.1, hu.2.trans hst⟩) hfin (fun t ht => by
      refine iSup₂_le fun s hs => ?_
      have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
      rw [hde s hsT, zero_add, enorm_mul]
      have h1 : ‖-k‖ₑ = ENNReal.ofReal |k| := by
        rw [Real.enorm_eq_ofReal_abs, abs_neg]
      rw [h1]
      gcongr
      rw [intervalIntegral.integral_of_le hs.1]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      refine (lintegral_mono_set (Set.Ioc_subset_Ioc_right hs.2)).trans ?_
      exact setLIntegral_mono' measurableSet_Ioc fun u hu => hle u u ⟨hu.1.le, le_rfl⟩) 
  intro t ht
  have h := (hle t t ⟨ht.1, le_rfl⟩).trans (hg t ht)
  simp only [zero_mul, nonpos_iff_eq_zero, enorm_eq_zero] at h
  simpa [d, sub_eq_zero] using h

/-- The OU coefficients `a(x) = -k x`, `b = σ` satisfy (4.3.10)–(4.3.11) with `K = |k| + |σ|`. -/
lemma sdeCoeffs_ou (k σ t₀ T : ℝ) :
    SDECoeffs (fun x _ => -k * x) (fun _ _ => σ) t₀ T (|k| + |σ|) where
  measurable_a := measurable_const.mul measurable_fst
  measurable_b := measurable_const
  K_nonneg := by positivity
  lipschitz t _ x y := by
    rw [show -k * x - -k * y = -k * (x - y) by ring, sub_self, abs_zero, add_zero, abs_mul,
      abs_neg]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg σ)) (abs_nonneg _)
  growth t _ x := by
    have e1 : |-k * x| ^ 2 = |k| ^ 2 * x ^ 2 := by rw [sq_abs, sq_abs]; ring
    rw [e1, sq_abs x]
    nlinarith [abs_nonneg k, abs_nonneg σ, mul_nonneg (abs_nonneg k) (abs_nonneg σ),
      sq_nonneg x, mul_nonneg (mul_nonneg (abs_nonneg k) (abs_nonneg σ)) (sq_nonneg x)]

/-- Functions continuous on `[a, b]` (`a < b`) that agree at the rational points agree. -/
lemma eqOn_Icc_of_rat {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b)) (h : ∀ q : ℚ, (q : ℝ) ∈ Set.Icc a b → f q = g q) :
    Set.EqOn f g (Set.Icc a b) := by
  refine Set.EqOn.of_subset_closure (s := Set.Icc a b ∩ Set.range ((↑) : ℚ → ℝ)) ?_ hf hg
    Set.inter_subset_left ?_
  · rintro _ ⟨hx, q, rfl⟩; exact h q hx
  · calc Set.Icc a b = closure (Set.Ioo a b) := (closure_Ioo hab.ne).symm
      _ ⊆ closure (closure (Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ))) :=
          closure_mono (Dense.open_subset_closure_inter (Rat.denseRange_cast (𝕜 := ℝ)) isOpen_Ioo)
      _ = closure (Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ)) := closure_closure
      _ ⊆ closure (Set.Icc a b ∩ Set.range ((↑) : ℚ → ℝ)) :=
          closure_mono (Set.inter_subset_inter_left _ Set.Ioo_subset_Icc_self)

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) (hWj : Measurable (Function.uncurry W))
include hW hWj

/-- Every solution of the OU SDE satisfies, almost surely and simultaneously for all
`t ∈ [0, T]`, the pathwise integral equation `x(t) = x₀ - k ∫₀ᵗ x(s) ds + σ W(t)`. -/
theorem IsSDESol.ou_pathwise {T k σ : ℝ} (hT : 0 < T) {x0 : Ω → ℝ} {y : ℝ → Ω → ℝ}
    (hy : IsSDESol W 𝓕 P (fun x _ => -k * x) (fun _ _ => σ) 0 T x0 y) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, y t ω = x0 ω + (∫ s in (0 : ℝ)..t, -k * y s ω) + σ * W t ω := by
  have := hW.isProbabilityMeasure
  have hD := hy.isItoIntegrand (sdeCoeffs_ou k σ 0 T) le_rfl
  have hrep : ∀ t ∈ Set.Icc 0 T, ∀ᵐ ω ∂P,
      y t ω = x0 ω + (∫ s in (0 : ℝ)..t, -k * y s ω) + σ * (W t ω - W 0 ω) := by
    intro t ht
    have h1 := itoInt_congr_of_eq_on hW (hD.mono ht.2)
      ((isItoIntegrand_det (𝓕 := 𝓕) (P := P) t (continuous_const (y := (1 : ℝ)))).const_mul σ)
      (fun s hs ω => by simp [drive, afterInd_of_lt hs.1])
    have h2 := itoInt_const_mul hW
      (isItoIntegrand_det (𝓕 := 𝓕) (P := P) t (continuous_const (y := (1 : ℝ)))) σ
    filter_upwards [hy.eq t ht, h1, h2, hW.itoInt_one hWj ht.1] with ω e1 e2 e3 e4
    rw [e1, e2, e3, e4]
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc 0 T →
      y q ω = x0 ω + (∫ s in (0 : ℝ)..q, -k * y s ω) + σ * (W q ω - W 0 ω) := by
    refine ae_all_iff.mpr fun q => ?_
    by_cases h : (q : ℝ) ∈ Set.Icc 0 T
    · exact (hrep q h).mono fun ω h' _ => h'
    · exact Eventually.of_forall fun ω h' => absurd h' h
  filter_upwards [hq, hy.cont, hW.cont, hW.zero] with ω h1 h2 h3 h4
  have hint : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, -k * y s ω) (Set.Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
      (μ := volume) (f := fun s => -k * y s ω)
    rw [Set.uIcc_of_le hT.le] at this
    exact this ((continuousOn_const.mul h2).integrableOn_Icc)
  have hg : ContinuousOn (fun t => x0 ω + (∫ s in (0 : ℝ)..t, -k * y s ω) + σ * W t ω)
      (Set.Icc 0 T) := (continuousOn_const.add hint).add (continuousOn_const.mul h3.continuousOn)
  have heq := eqOn_Icc_of_rat hT h2 hg (fun q hq => by rw [h1 q hq, h4, sub_zero])
  exact fun t ht => heq ht

/-- **The Ornstein–Uhlenbeck process is the unique solution of `dx = -k x dt + σ dW`**
(Gardiner §4.4.4, with `σ = √D`): the SDE has a solution on `[0, T]`, and every solution is,
almost surely and simultaneously for all `t ∈ [0, T]`, equal to the OU path
`x₀ e^{-kt} + σ (W(t) - k e^{-kt} ∫₀ᵗ e^{ks} W(s) ds)`. -/
theorem ou_unique_solution {T : ℝ} (hT : 0 < T) (k σ : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) :
    (∃ x, IsSDESol W 𝓕 P (fun x _ => -k * x) (fun _ _ => σ) 0 T x0 x) ∧
      ∀ y, IsSDESol W 𝓕 P (fun x _ => -k * x) (fun _ _ => σ) 0 T x0 y →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, y t ω = ouSDEPath k σ (x0 ω) (fun s => W s ω) t := by
  refine ⟨⟨_, isSDESol_sdeSol hW (sdeCoeffs_ou k σ 0 T) le_rfl hT.le hx0 hx02⟩, fun y hy => ?_⟩
  filter_upwards [hy.ou_pathwise hW hWj hT, hy.cont, hW.cont] with ω h1 h2 h3
  exact ou_integral_eq_unique h2 (continuous_ouSDEPath k σ (x0 ω) h3).continuousOn h1
    (fun t _ => ouSDEPath_eq k σ (x0 ω) h3 t)

/-- The OU SDE in Gardiner's form `dx = -k x dt + √D dW`. -/
theorem ou_unique_solution_sqrt {T : ℝ} (hT : 0 < T) (k D : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) :
    (∃ x, IsSDESol W 𝓕 P (fun x _ => -k * x) (fun _ _ => Real.sqrt D) 0 T x0 x) ∧
      ∀ y, IsSDESol W 𝓕 P (fun x _ => -k * x) (fun _ _ => Real.sqrt D) 0 T x0 y →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T,
          y t ω = ouSDEPath k (Real.sqrt D) (x0 ω) (fun s => W s ω) t :=
  ou_unique_solution hW hWj hT k (Real.sqrt D) hx0 hx02

end OU

/-! ### A nonlinear example: `dx = -sin x dt + σ dW` -/

section Sin

/-- The coefficients `a(x) = -sin x`, `b = σ` satisfy (4.3.10)–(4.3.11) with `K = 1 + |σ|`. -/
lemma sdeCoeffs_sin (σ t₀ T : ℝ) :
    SDECoeffs (fun x _ => -Real.sin x) (fun _ _ => σ) t₀ T (1 + |σ|) where
  measurable_a := (Real.continuous_sin.measurable.comp measurable_fst).neg
  measurable_b := measurable_const
  K_nonneg := by positivity
  lipschitz t _ x y := by
    rw [sub_self, abs_zero, add_zero, neg_sub_neg, abs_sub_comm]
    calc |Real.sin x - Real.sin y| ≤ |x - y| := Real.abs_sin_sub_sin_le x y
      _ ≤ (1 + |σ|) * |x - y| := le_mul_of_one_le_left (abs_nonneg _) (by linarith [abs_nonneg σ])
  growth t _ x := by
    rw [abs_neg, sq_abs, sq_abs, ← sq_abs σ]
    have h1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
    nlinarith [abs_nonneg σ, sq_nonneg x, mul_nonneg (sq_nonneg (1 + |σ|)) (sq_nonneg x)]

lemma sdeHolder_sin (σ t₀ T : ℝ) :
    SDEHolder (fun x _ => -Real.sin x) (fun _ _ => σ) t₀ T (1 + |σ|) :=
  sdeHolder_autonomous (a := fun x => -Real.sin x) (b := fun _ => σ) (by positivity)

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **Existence and uniqueness for `dx = -sin x dt + σ dW`** on every `[0, T]`. -/
theorem sinSDE_existsUnique {T : ℝ} (hT : 0 ≤ T) (σ : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) :
    ∃ x, IsSDESol W 𝓕 P (fun x _ => -Real.sin x) (fun _ _ => σ) 0 T x0 x ∧
      ∀ y, IsSDESol W 𝓕 P (fun x _ => -Real.sin x) (fun _ _ => σ) 0 T x0 y →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, y t ω = x t ω :=
  existsUnique_sdeSol hW (sdeCoeffs_sin σ 0 T) le_rfl hT hx0 hx02

/-- **Strong order ½ of the Euler scheme for `dx = -sin x dt + σ dW`**:
`E |x(T) - x_N|² ≤ C(1 + |σ|, T, E x₀²) τ` on the uniform grid with `t_N = T`. -/
theorem sinSDE_euler {T τ : ℝ} {N : ℕ} (σ : ℝ) (hτ : 0 < τ) (hTN : eulerGrid 0 τ N = T)
    {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) {x : ℝ → Ω → ℝ}
    (hx : IsSDESol W 𝓕 P (fun x _ => -Real.sin x) (fun _ _ => σ) 0 T x0 x) :
    ∫ ω, (x T ω - eulerSeq W (fun x _ => -Real.sin x) (fun _ _ => σ) 0 τ x0 N ω) ^ 2 ∂P ≤
      eulerErrConst (1 + |σ|) (T - 0) (∫ ω, x0 ω ^ 2 ∂P) * τ :=
  euler_strong_order_half hW (sdeCoeffs_sin σ 0 T) (sdeHolder_sin σ 0 T) le_rfl hτ hTN hx0 hx02 hx

/-- **Convergence of the Cauchy–Euler approximations for `dx = -sin x dt + σ dW`.** -/
theorem sinSDE_tendsto_euler {T : ℝ} (hT : 0 < T) (σ : ℝ) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) {x : ℝ → Ω → ℝ}
    (hx : IsSDESol W 𝓕 P (fun x _ => -Real.sin x) (fun _ _ => σ) 0 T x0 x) :
    Tendsto (fun N : ℕ => ∫ ω, (x T ω - eulerSeq W (fun x _ => -Real.sin x) (fun _ _ => σ) 0
      ((T - 0) / (N + 1 : ℕ)) x0 (N + 1) ω) ^ 2 ∂P) atTop (𝓝 0) :=
  tendsto_euler hW (sdeCoeffs_sin σ 0 T) (sdeHolder_sin σ 0 T) le_rfl hT hx0 hx02 hx

end Sin

end Gardiner.Ito.StochDE
