/-
# Strong convergence of the Euler–Maruyama scheme: order ½

Gardiner §10.1.4, (10.1.15)–(10.1.26), and the Cauchy–Euler construction §4.3.1 (4.3.5)–(4.3.9).

Under the Lipschitz and growth conditions (4.3.10)–(4.3.11) and the additional Hölder-½ condition
in time (`SDEHolder`)
`|a(x, t) - a(x, s)| + |b(x, t) - b(x, s)| ≤ K (1 + |x|) |t - s|^{1/2}`,
the Euler scheme on the uniform grid `t_i = t₀ + i τ` satisfies (`euler_strong_order_half`)
`E |x(T) - x_N|² ≤ C τ` with the explicit constant `C = eulerErrConst K (T - t₀) (E ξ²)`.

* `IsSDESol.lintegral_incr_sq_le`: the mean-square Hölder-½ continuity of solutions,
  `E |x(s) - x(r)|² ≤ 2 K² (1 + E sup |x|²) (s - r) ((s - r) + 1)`;
* `supSq_sub_eulerInterp_le`: the uniform bound
  `E sup_{[t₀, T]} |x - X|² ≤ C₀ (1 + E sup |x|²) τ` for the continuous Euler interpolation;
* `euler_strong_order_half`: the strong order-½ estimate (10.1.26);
* `tendsto_euler`: the Cauchy–Euler approximations converge in mean square to the solution.
-/
import SHSLib.Gardiner.Ito.StochDE.EulerDef

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- **The Hölder-½ condition in time** on `[t₀, T]`:
`|a(x, t) - a(x, s)| + |b(x, t) - b(x, s)| ≤ K (1 + |x|) √|t - s|`. -/
structure SDEHolder (a b : ℝ → ℝ → ℝ) (t₀ T K : ℝ) : Prop where
  holder : ∀ s ∈ Set.Icc t₀ T, ∀ t ∈ Set.Icc t₀ T, ∀ x,
    |a x t - a x s| + |b x t - b x s| ≤ K * (1 + |x|) * Real.sqrt |t - s|

lemma SDECoeffs.mono_left {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} (hc : SDECoeffs a b t₀ T K) {r : ℝ}
    (hr : t₀ ≤ r) : SDECoeffs a b r T K where
  measurable_a := hc.measurable_a
  measurable_b := hc.measurable_b
  K_nonneg := hc.K_nonneg
  lipschitz t ht := hc.lipschitz t ⟨hr.trans ht.1, ht.2⟩
  growth t ht := hc.growth t ⟨hr.trans ht.1, ht.2⟩

lemma lintegral_one_add_sq_le_supSq [IsProbabilityMeasure P] {x : ℝ → Ω → ℝ}
    {t₀ T u : ℝ} (hu : u ∈ Set.Icc t₀ T) :
    ∫⁻ ω, (1 + ‖x u ω‖ₑ ^ 2) ∂P ≤ 1 + supSq P x t₀ T := by
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  gcongr
  exact lintegral_mono fun ω => pow_le_pow_left' (enorm_le_iSup_Icc hu ω) 2

/-- `E (∫_r^s |A|)² ≤ (s - r) ∫_r^s E A²` (Cauchy–Schwarz in time). -/
lemma lintegral_sq_lintegral_le [SFinite P] {A : ℝ → Ω → ℝ} (hA : Measurable (Function.uncurry A)) (r s : ℝ) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc r s, ‖A u ω‖ₑ) ^ 2 ∂P ≤ ENNReal.ofReal (s - r) * tsSq P A r s := by
  have hAs : Measurable fun q : Ω × ℝ => ‖A q.2 q.1‖ₑ :=
    (Measurable.comp (g := Function.uncurry A) (f := fun q : Ω × ℝ => (q.2, q.1)) hA
      measurable_swap).enorm
  calc ∫⁻ ω, (∫⁻ u in Set.Ioc r s, ‖A u ω‖ₑ) ^ 2 ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (s - r) * (∫⁻ u in Set.Ioc r s, ‖A u ω‖ₑ ^ 2) ∂P := by
        refine lintegral_mono fun ω => ?_
        have := lintegral_sq_le_mul (μ := (volume : Measure ℝ).restrict (Set.Ioc r s))
          (f := fun u => ‖A u ω‖ₑ)
          ((hAs.comp (measurable_const.prodMk measurable_id)).aemeasurable)
        simpa [Real.volume_Ioc] using this
    _ = ENNReal.ofReal (s - r) * tsSq P A r s := by
        rw [lintegral_const_mul _ ((hAs.pow_const 2).lintegral_prod_right')]
        congr 1
        exact lintegral_lintegral_swap ((hAs.pow_const 2).aemeasurable)

namespace IsSDESol

variable {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ}

/-- **Mean-square Hölder-½ continuity of solutions**: for `t₀ ≤ r ≤ s ≤ T`,
`E |x(s) - x(r)|² ≤ 2 K² (1 + E sup |x|²) (s - r) ((s - r) + 1)`. -/
theorem lintegral_incr_sq_le (hW : IsFWiener W 𝓕 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x)
    (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) {r s : ℝ} (hr : t₀ ≤ r) (hrs : r ≤ s)
    (hsT : s ≤ T) :
    ∫⁻ ω, ‖x s ω - x r ω‖ₑ ^ 2 ∂P ≤ 2 * ENNReal.ofReal (K ^ 2) * (1 + supSq P x t₀ T) *
      ENNReal.ofReal (s - r) * (ENNReal.ofReal (s - r) + 1) := by
  have := hW.isProbabilityMeasure
  set D := drive t₀ b x
  have hD := hx.isItoIntegrand hc ht₀
  set S := supSq P x t₀ T
  have hAm := measurable_comp_coeff hc.measurable_a hx.measurable
  set U : Ω → ℝ≥0∞ := fun ω => ∫⁻ u in Set.Ioc r s, ‖a (x u ω) u‖ₑ
  have hUm : Measurable U := by
    have hAs : Measurable fun q : Ω × ℝ => ‖a (x q.2 q.1) q.2‖ₑ :=
      (Measurable.comp (g := Function.uncurry fun s ω => a (x s ω) s)
        (f := fun q : Ω × ℝ => (q.2, q.1)) hAm measurable_swap).enorm
    exact hAs.lintegral_prod_right'
  set V : Ω → ℝ := fun ω => itoInt W 𝓕 P s D ω - itoInt W 𝓕 P r D ω
  have hVm : Measurable V :=
    ((itoInt_stronglyMeasurable hW (hD.mono hsT)).mono (𝓕.le _)).measurable.sub
      ((itoInt_stronglyMeasurable hW (hD.mono (hrs.trans hsT))).mono (𝓕.le _)).measurable
  have hpt : ∀ᵐ ω ∂P, ‖x s ω - x r ω‖ₑ ≤ U ω + ‖V ω‖ₑ := by
    filter_upwards [hx.eq s ⟨hr.trans hrs, hsT⟩, hx.eq r ⟨hr, hrs.trans hsT⟩, hx.cont]
      with ω h1 h2 h3
    have hint := hc.driftCoeff.integrableOn hx.measurable h3
    have hi : ∀ v ∈ Set.Icc t₀ T, IntervalIntegrable (fun u => a (x u ω) u) volume t₀ v :=
      fun v hv => (hint.mono_set (by rw [Set.uIcc_of_le hv.1]; exact Set.Icc_subset_Icc_right hv.2)).intervalIntegrable
    have e : x s ω - x r ω = (∫ u in r..s, a (x u ω) u) + V ω := by
      rw [h1, h2, ← intervalIntegral.integral_interval_sub_left (hi s ⟨hr.trans hrs, hsT⟩)
        (hi r ⟨hr, hrs.trans hsT⟩)]
      simp only [V]; ring
    rw [e]
    refine (enorm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [intervalIntegral.integral_of_le hrs]
    exact enorm_integral_le_lintegral_enorm _
  have hone : ∫⁻ u in Set.Ioc r s, ∫⁻ ω, (1 + ‖x u ω‖ₑ ^ 2) ∂P ≤ ENNReal.ofReal (s - r) * (1 + S) :=
    calc ∫⁻ u in Set.Ioc r s, ∫⁻ ω, (1 + ‖x u ω‖ₑ ^ 2) ∂P ≤ ∫⁻ _ in Set.Ioc r s, (1 + S) :=
          setLIntegral_mono' measurableSet_Ioc fun u hu =>
            lintegral_one_add_sq_le_supSq ⟨hr.trans hu.1.le, hu.2.trans hsT⟩
      _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, mul_comm]
  have hUterm : ∫⁻ ω, U ω ^ 2 ∂P ≤ ENNReal.ofReal (s - r) *
      (ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal (s - r) * (1 + S))) := by
    refine (lintegral_sq_lintegral_le hAm r s).trans ?_
    gcongr
    exact (tsSq_a_le (hc.mono_left hr) hsT).trans (by gcongr)
  have hVterm : ∫⁻ ω, ‖V ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal (s - r) * (1 + S)) := by
    refine (lintegral_itoInt_sub_sq_le hW (ht₀.trans hr) hrs hsT hD).trans ?_
    refine le_trans ?_ (mul_le_mul_right hone _)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc fun u hu => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    have h := enorm_drive_sq_le hc (x := x) (hu.2.trans hsT) ω
    rwa [Set.indicator_of_mem (show u ∈ Set.Ioc t₀ T from
      ⟨hr.trans_lt hu.1, hu.2.trans hsT⟩)] at h
  calc ∫⁻ ω, ‖x s ω - x r ω‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, (2 * U ω ^ 2 + 2 * ‖V ω‖ₑ ^ 2) ∂P :=
        lintegral_mono_ae (hpt.mono fun ω h => (pow_le_pow_left' h 2).trans (ennreal_add_sq_le _ _))
    _ = 2 * ∫⁻ ω, U ω ^ 2 ∂P + 2 * ∫⁻ ω, ‖V ω‖ₑ ^ 2 ∂P := by
        rw [lintegral_add_left ((hUm.pow_const 2).const_mul 2),
          lintegral_const_mul _ (hUm.pow_const 2), lintegral_const_mul _ (hVm.enorm.pow_const 2)]
    _ ≤ 2 * (ENNReal.ofReal (s - r) * (ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal (s - r) * (1 + S))))
          + 2 * (ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal (s - r) * (1 + S))) := by gcongr
    _ = _ := by ring

end IsSDESol

/-! ### The coefficient error on a cell -/

lemma sq_coeff_err_le {F : ℝ → ℝ → ℝ} {K τ u z y s r : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (h1 : |F u s - F z s| ≤ K * |u - z|) (h2 : |F z s - F z r| ≤ K * (1 + |z|) * Real.sqrt τ)
    (h3 : |F z r - F y r| ≤ K * |z - y|) :
    (F u s - F y r) ^ 2 ≤ 3 * K ^ 2 * (u - z) ^ 2 + 6 * K ^ 2 * τ * (1 + z ^ 2) +
      3 * K ^ 2 * (z - y) ^ 2 := by
  have htri : |F u s - F y r| ≤ K * |u - z| + K * (1 + |z|) * Real.sqrt τ + K * |z - y| := by
    calc |F u s - F y r| = |(F u s - F z s) + (F z s - F z r) + (F z r - F y r)| := by ring_nf
      _ ≤ |F u s - F z s| + |F z s - F z r| + |F z r - F y r| := abs_add_three _ _ _
      _ ≤ _ := by gcongr
  set p := K * |u - z|
  set q := K * (1 + |z|) * Real.sqrt τ
  set w := K * |z - y|
  have hp : p ^ 2 = K ^ 2 * (u - z) ^ 2 := by simp only [p]; rw [mul_pow, sq_abs]
  have hw : w ^ 2 = K ^ 2 * (z - y) ^ 2 := by simp only [w]; rw [mul_pow, sq_abs]
  have hq : q ^ 2 ≤ 2 * K ^ 2 * τ * (1 + z ^ 2) := by
    simp only [q]
    rw [mul_pow, mul_pow, Real.sq_sqrt hτ]
    have : (1 + |z|) ^ 2 ≤ 2 * (1 + z ^ 2) := by nlinarith [sq_abs z, sq_nonneg (|z| - 1)]
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ K ^ 2 * τ)]
  have h0 : 0 ≤ p + q + w := by positivity
  calc (F u s - F y r) ^ 2 = |F u s - F y r| ^ 2 := (sq_abs _).symm
    _ ≤ (p + q + w) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) htri 2
    _ ≤ 3 * p ^ 2 + 3 * q ^ 2 + 3 * w ^ 2 := by
        nlinarith [sq_nonneg (p - q), sq_nonneg (q - w), sq_nonneg (p - w)]
    _ ≤ _ := by rw [hp, hw]; nlinarith

/-- The mean-square error of a coefficient evaluated at a grid point instead of the current
point:
`E |F(x(s), s) - F(X(r), r)|² ≤ 3K² E|x(s) - x(r)|² + 6K²τ E(1 + |x(r)|²) + 3K² E|x(r) - X(r)|²`
whenever `0 ≤ s - r ≤ τ`. -/
lemma lintegral_coeff_err_le [IsFiniteMeasure P] {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) {t₀ T K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ y z, |F y t - F z t| ≤ K * |y - z|)
    (hhol : ∀ s ∈ Set.Icc t₀ T, ∀ t ∈ Set.Icc t₀ T, ∀ y,
      |F y t - F y s| ≤ K * (1 + |y|) * Real.sqrt |t - s|)
    {x X : ℝ → Ω → ℝ} (hxm : ∀ u, Measurable (x u))
    {r s : ℝ} (hr : t₀ ≤ r) (hrs : r ≤ s) (hsT : s ≤ T) (hsr : s - r ≤ τ) :
    ∫⁻ ω, ‖F (x s ω) s - F (X r ω) r‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (3 * K ^ 2) * ∫⁻ ω, ‖x s ω - x r ω‖ₑ ^ 2 ∂P +
      ENNReal.ofReal (6 * K ^ 2 * τ) * ∫⁻ ω, (1 + ‖x r ω‖ₑ ^ 2) ∂P +
      ENNReal.ofReal (3 * K ^ 2) * ∫⁻ ω, ‖x r ω - X r ω‖ₑ ^ 2 ∂P := by
  have hsI : s ∈ Set.Icc t₀ T := ⟨hr.trans hrs, hsT⟩
  have hrI : r ∈ Set.Icc t₀ T := ⟨hr, hrs.trans hsT⟩
  have hpt : ∀ ω, ‖F (x s ω) s - F (X r ω) r‖ₑ ^ 2 ≤
      ENNReal.ofReal (3 * K ^ 2) * ‖x s ω - x r ω‖ₑ ^ 2 +
      ENNReal.ofReal (6 * K ^ 2 * τ) * (1 + ‖x r ω‖ₑ ^ 2) +
      ENNReal.ofReal (3 * K ^ 2) * ‖x r ω - X r ω‖ₑ ^ 2 := by
    intro ω
    have h2 : |F (x r ω) s - F (x r ω) r| ≤ K * (1 + |x r ω|) * Real.sqrt τ := by
      refine (hhol r hrI s hsI (x r ω)).trans ?_
      gcongr
      rw [abs_of_nonneg (sub_nonneg.mpr hrs)]; exact hsr
    have h := sq_coeff_err_le hK hτ (hlip s hsI (x s ω) (x r ω)) h2 (hlip r hrI (x r ω) (X r ω))
    simp only [enorm_sq_eq_ofReal]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have m1 : Measurable fun ω => ENNReal.ofReal (3 * K ^ 2) * ‖x s ω - x r ω‖ₑ ^ 2 :=
    (((hxm s).sub (hxm r)).enorm.pow_const 2).const_mul _
  have m2 : Measurable fun ω => ENNReal.ofReal (6 * K ^ 2 * τ) * (1 + ‖x r ω‖ₑ ^ 2) :=
    (measurable_const.add ((hxm r).enorm.pow_const 2)).const_mul _
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_add_left (m1.add m2), lintegral_add_left m1,
    lintegral_const_mul _ (((hxm s).sub (hxm r)).enorm.pow_const 2),
    lintegral_const_mul _ (measurable_const.add ((hxm r).enorm.pow_const 2)),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

namespace SDEHolder

variable {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ}

lemma hol_a (hH : SDEHolder a b t₀ T K) (s : ℝ) (hs : s ∈ Set.Icc t₀ T) (t : ℝ)
    (ht : t ∈ Set.Icc t₀ T) (y : ℝ) : |a y t - a y s| ≤ K * (1 + |y|) * Real.sqrt |t - s| :=
  le_trans (le_add_of_nonneg_right (abs_nonneg _)) (hH.holder s hs t ht y)

lemma hol_b (hH : SDEHolder a b t₀ T K) (s : ℝ) (hs : s ∈ Set.Icc t₀ T) (t : ℝ)
    (ht : t ∈ Set.Icc t₀ T) (y : ℝ) : |b y t - b y s| ≤ K * (1 + |y|) * Real.sqrt |t - s| :=
  le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hH.holder s hs t ht y)

end SDEHolder

/-! ### Finiteness for the Euler interpolation -/

section Step

variable {t₀ τ : ℝ} {N : ℕ}

lemma measurable_stepFun {v : ℕ → Ω → ℝ} (hv : ∀ i, Measurable (v i)) :
    Measurable (Function.uncurry fun s ω =>
      ∑ i : Fin N, v i ω * cellInd (eulerGrid t₀ τ i) (eulerGrid t₀ τ (i + 1)) s) := by
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((hv i).comp measurable_snd).mul ((measurable_cellInd _ _).comp measurable_fst)

omit [MeasurableSpace Ω] in
lemma stepFun_of_le (hτ : 0 ≤ τ) (v : ℕ → Ω → ℝ) {s : ℝ} (hs : s ≤ t₀) (ω : Ω) :
    ∑ i : Fin N, v i ω * cellInd (eulerGrid t₀ τ i) (eulerGrid t₀ τ (i + 1)) s = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cellInd_notMem, mul_zero]
  exact fun h => absurd (hs.trans (le_eulerGrid hτ i)) (not_le.mpr h.1)

/-- `∫_{t₀}^{t_N} E (Σ_i v_i 1_{(t_i, t_{i+1}]})² < ∞` for square-integrable `v_i`. -/
lemma tsSq_stepFun_lt_top [IsFiniteMeasure P] (hτ : 0 < τ) {v : ℕ → Ω → ℝ}
    (hvm : ∀ i, Measurable (v i)) (hv : ∀ i < N, MemLp (v i) 2 P) :
    tsSq P (fun s ω => ∑ i : Fin N, v i ω * cellInd (eulerGrid t₀ τ i)
      (eulerGrid t₀ τ (i + 1)) s) t₀ (eulerGrid t₀ τ N) < ⊤ := by
  set M := ∑ i : Fin N, ∫⁻ ω, ‖v i ω‖ₑ ^ 2 ∂P
  have hM : M < ⊤ := by
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    rw [lintegral_enorm_sq_eq (hv i i.isLt)]; exact ENNReal.ofReal_lt_top
  have hle : tsSq P (fun s ω => ∑ i : Fin N, v i ω * cellInd (eulerGrid t₀ τ i)
      (eulerGrid t₀ τ (i + 1)) s) t₀ (eulerGrid t₀ τ N) ≤ ∫⁻ _ in Set.Ioc t₀ (eulerGrid t₀ τ N), M := by
    refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
    obtain ⟨k, hk, h1, h2⟩ := exists_gridCell hτ hs
    calc _ ≤ ∫⁻ ω, ∑ i : Fin N, ‖v i ω‖ₑ ^ 2 ∂P := lintegral_mono fun ω => by
            simp only
            rw [sum_cellInd_eq hτ hk h1 h2 (fun i => v i ω)]
            exact Finset.single_le_sum (f := fun i : Fin N => ‖v i ω‖ₑ ^ 2) (fun _ _ => zero_le _)
              (Finset.mem_univ (⟨k, hk⟩ : Fin N))
      _ = M := lintegral_finset_sum _ fun i _ => ((hvm i).enorm.pow_const 2)
  refine hle.trans_lt ?_
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top hM (by simp)

end Step

/-- The constant `C₀(K, d) = (3d + 12) d · 6K² (K² (d + 1) + 1)` of the Euler error bound. -/
def eulerC (K d : ℝ) : ℝ := (3 * d + 12) * d * (6 * K ^ 2 * (K ^ 2 * (d + 1) + 1))

section Main

variable {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ τ K : ℝ} {N : ℕ} {ξ : Ω → ℝ}
  (hW : IsFWiener W 𝓕 P) (hc : SDECoeffs a b t₀ (eulerGrid t₀ τ N) K) (ht₀ : 0 ≤ t₀)
  (hτ : 0 < τ) (hξm : StronglyMeasurable[𝓕 t₀] ξ) (hξ : MemLp ξ 2 P)
include hW hc ht₀ hτ hξm hξ

lemma measurable_eulerSeq (i : ℕ) : Measurable (eulerSeq W a b t₀ τ ξ i) :=
  ((eulerSeq_adapted hW hc.measurable_a hc.measurable_b ht₀ hτ.le hξm i).mono (𝓕.le _)).measurable

lemma eulerInterp_regular :
    IsItoIntegrand 𝓕 P (eulerGrid t₀ τ N) (eulerNoise W a b t₀ τ ξ N) ∧
    Measurable (Function.uncurry (eulerDrift W a b t₀ τ ξ N)) ∧
    (∀ s ω, s ≤ t₀ → eulerNoise W a b t₀ τ ξ N s ω = 0) ∧
    (∀ᵐ ω ∂P, ContinuousOn (fun u => eulerInterp W a b t₀ τ ξ N u ω)
      (Set.Icc t₀ (eulerGrid t₀ τ N))) := by
  have := hW.isProbabilityMeasure
  obtain ⟨H, hp, -, -⟩ := exists_eulerElem hW hc ht₀ hτ hξm hξ
  refine ⟨hp ▸ H.isItoIntegrand _, ?_, fun s ω hs => stepFun_of_le hτ.le
    (fun i ω => b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i)) hs ω, ?_⟩
  · exact measurable_stepFun (v := fun i ω => a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i))
      fun i => (stronglyMeasurable_comp_coeff hc.measurable_a
        (measurable_eulerSeq hW hc ht₀ hτ hξm hξ i).stronglyMeasurable _).measurable
  · filter_upwards [hW.cont] with ω hω
    exact (continuous_eulerInterp hω).continuousOn

/-- The continuous Euler interpolation has `E sup_{[t₀, t_N]} |X|² < ∞`. -/
lemma supSq_eulerInterp_lt_top :
    supSq P (eulerInterp W a b t₀ τ ξ N) t₀ (eulerGrid t₀ τ N) < ⊤ := by
  have := hW.isProbabilityMeasure
  obtain ⟨hB, hAm, hB0, hXc⟩ := eulerInterp_regular hW hc ht₀ hτ hξm hξ
  have hT : t₀ ≤ eulerGrid t₀ τ N := le_eulerGrid hτ.le N
  have h := sup_sq_le hW (A := eulerDrift W a b t₀ τ ξ N) ht₀ ⟨hT, le_rfl⟩ hB hB0 hAm
    hξ.aestronglyMeasurable.aemeasurable hXc (eulerInterp_eq hW hc ht₀ hτ hξm hξ)
  have hmem := eulerSeq_memLp hW hc ht₀ hτ.le hξm hξ le_rfl
  have hxm := measurable_eulerSeq hW hc ht₀ hτ hξm hξ
  have hgrid : ∀ i < N, eulerGrid t₀ τ i ∈ Set.Icc t₀ (eulerGrid t₀ τ N) := fun i hi =>
    ⟨le_eulerGrid hτ.le i, eulerGrid_mono hτ.le hi.le⟩
  refine h.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩)
  · rw [lintegral_enorm_sq_eq hξ]; exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
  · refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) ?_
    exact tsSq_stepFun_lt_top hτ (v := fun i ω => a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i))
      (fun i => (stronglyMeasurable_comp_coeff hc.measurable_a (hxm i).stronglyMeasurable _).measurable)
      (fun i hi => memLp_coeff_of_growth hc.measurable_a (hmem i hi.le) (hxm i)
        (hc.abs_a_le (hgrid i hi)))
  · refine ENNReal.mul_lt_top (by norm_num) ?_
    exact tsSq_stepFun_lt_top hτ (v := fun i ω => b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i))
      (fun i => (stronglyMeasurable_comp_coeff hc.measurable_b (hxm i).stronglyMeasurable _).measurable)
      (fun i hi => memLp_coeff_of_growth hc.measurable_b (hmem i hi.le) (hxm i)
        (hc.abs_b_le (hgrid i hi)))

omit hW hc ht₀ hτ hξm hξ in
lemma ofReal_eulerC {K d : ℝ} (hd : 0 ≤ d) : ENNReal.ofReal (eulerC K d) =
    (3 * ENNReal.ofReal d + 12) * ENNReal.ofReal d *
      (6 * ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal d + 1) + 1)) := by
  unfold eulerC
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add hd zero_le_one]
  simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one]

/-- **The uniform mean-square error of the Euler interpolation**:
`E sup_{[t₀, T]} |x - X|² ≤ C₀(K, T - t₀) (1 + E sup |x|²) τ e^{3 L (T - t₀)}`,
`L = sdeRate K (T - t₀)`, for the solution `x` of (4.3.4) and `T = t₀ + N τ`. -/
theorem supSq_sub_eulerInterp_le (hH : SDEHolder a b t₀ (eulerGrid t₀ τ N) K)
    {x : ℝ → Ω → ℝ} (hx : IsSDESol W 𝓕 P a b t₀ (eulerGrid t₀ τ N) ξ x) :
    supSq P (fun s ω => x s ω - eulerInterp W a b t₀ τ ξ N s ω) t₀ (eulerGrid t₀ τ N) ≤
      ENNReal.ofReal (eulerC K (eulerGrid t₀ τ N - t₀)) *
        (1 + supSq P x t₀ (eulerGrid t₀ τ N)) * ENNReal.ofReal τ *
        ENNReal.ofReal (Real.exp (3 * sdeRate K (eulerGrid t₀ τ N - t₀) *
          (eulerGrid t₀ τ N - t₀))) := by
  have := hW.isProbabilityMeasure
  have hT : t₀ ≤ eulerGrid t₀ τ N := le_eulerGrid hτ.le N
  set T := eulerGrid t₀ τ N with hTdef
  set d := T - t₀
  have hd : 0 ≤ d := sub_nonneg.mpr hT
  set X := eulerInterp W a b t₀ τ ξ N with hXdef
  set S := supSq P x t₀ T
  set ψ : ℝ → ℝ≥0∞ := fun t => supSq P (fun s ω => x s ω - X s ω) t₀ t
  obtain ⟨hB, hAm, hB0, hXc⟩ := eulerInterp_regular hW hc ht₀ hτ hξm hξ
  have hXeq := eulerInterp_eq hW hc ht₀ hτ hξm hξ
  have hxm := measurable_of_uncurry hx.measurable
  set c := ENNReal.ofReal (3 * K ^ 2)
  set β := c * (2 * ENNReal.ofReal (K ^ 2) * (1 + S) * ENNReal.ofReal τ * (ENNReal.ofReal d + 1)) +
    ENNReal.ofReal (6 * K ^ 2 * τ) * (1 + S)
  have hcell : ∀ F : ℝ → ℝ → ℝ, Measurable (Function.uncurry F) →
      (∀ t ∈ Set.Icc t₀ T, ∀ y z, |F y t - F z t| ≤ K * |y - z|) →
      (∀ s ∈ Set.Icc t₀ T, ∀ t ∈ Set.Icc t₀ T, ∀ y,
        |F y t - F y s| ≤ K * (1 + |y|) * Real.sqrt |t - s|) →
      ∀ s r, t₀ ≤ r → r ≤ s → s ≤ T → s - r ≤ τ →
      ∫⁻ ω, ‖F (x s ω) s - F (X r ω) r‖ₑ ^ 2 ∂P ≤ β + c * ψ s := by
    intro F hF hlip hhol s r hr hrs hsT hsr
    refine (lintegral_coeff_err_le hF hc.K_nonneg hτ.le hlip hhol hxm hr hrs hsT hsr).trans ?_
    have h1 := hx.lintegral_incr_sq_le hW hc ht₀ hr hrs hsT
    have h2 : ∫⁻ ω, (1 + ‖x r ω‖ₑ ^ 2) ∂P ≤ 1 + S :=
      lintegral_one_add_sq_le_supSq ⟨hr, hrs.trans hsT⟩
    have h3 : ∫⁻ ω, ‖x r ω - X r ω‖ₑ ^ 2 ∂P ≤ ψ s :=
      lintegral_mono fun ω => pow_le_pow_left'
        (enorm_le_iSup_Icc (Y := fun s ω => x s ω - X s ω) ⟨hr, hrs⟩ ω) 2
    have h1' : ∫⁻ ω, ‖x s ω - x r ω‖ₑ ^ 2 ∂P ≤
        2 * ENNReal.ofReal (K ^ 2) * (1 + S) * ENNReal.ofReal τ * (ENNReal.ofReal d + 1) := by
      refine h1.trans ?_
      gcongr
      · simp only [d]; linarith
    calc c * ∫⁻ ω, ‖x s ω - x r ω‖ₑ ^ 2 ∂P +
          ENNReal.ofReal (6 * K ^ 2 * τ) * ∫⁻ ω, (1 + ‖x r ω‖ₑ ^ 2) ∂P +
          c * ∫⁻ ω, ‖x r ω - X r ω‖ₑ ^ 2 ∂P
        ≤ c * (2 * ENNReal.ofReal (K ^ 2) * (1 + S) * ENNReal.ofReal τ * (ENNReal.ofReal d + 1)) +
          ENNReal.ofReal (6 * K ^ 2 * τ) * (1 + S) + c * ψ s := by gcongr
      _ = β + c * ψ s := rfl
  have hint : ∀ t ∈ Set.Icc t₀ T, ∫⁻ s in Set.Ioc t₀ t, (β + c * ψ s) ≤
      ENNReal.ofReal d * β + c * ∫⁻ s in Set.Ioc t₀ t, ψ s := by
    intro t ht
    rw [lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Ioc, mul_comm,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    simp only [d]; linarith [ht.2]
  have hgridX : ∀ k ≤ N, ∀ ω, eulerSeq W a b t₀ τ ξ k ω = X (eulerGrid t₀ τ k) ω :=
    fun k hk ω => (eulerInterp_grid hτ hk ω).symm
  have hdrift : ∀ t ∈ Set.Icc t₀ T, tsSq P (fun s ω => a (x s ω) s -
      eulerDrift W a b t₀ τ ξ N s ω) t₀ t ≤ ENNReal.ofReal d * β + c * ∫⁻ s in Set.Ioc t₀ t, ψ s := by
    intro t ht
    refine le_trans (setLIntegral_mono' measurableSet_Ioc fun s hs => ?_) (hint t ht)
    obtain ⟨k, hk, h1, h2⟩ := exists_gridCell hτ (show s ∈ Set.Ioc t₀ T from ⟨hs.1, hs.2.trans ht.2⟩)
    have e : ∀ ω, eulerDrift W a b t₀ τ ξ N s ω = a (X (eulerGrid t₀ τ k) ω) (eulerGrid t₀ τ k) :=
      fun ω => by
        rw [← hgridX k hk.le ω]
        exact sum_cellInd_eq hτ hk h1 h2 (fun i => a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i))
    simp_rw [e]
    exact hcell a hc.measurable_a (fun t ht => hc.lip_a ht) hH.hol_a s _ (le_eulerGrid hτ.le k)
      h1.le (hs.2.trans ht.2) (by rw [eulerGrid_succ] at h2; linarith)
  have hnoise : ∀ t ∈ Set.Icc t₀ T, tsSq P (fun s ω => drive t₀ b x s ω -
      eulerNoise W a b t₀ τ ξ N s ω) t₀ t ≤ ENNReal.ofReal d * β + c * ∫⁻ s in Set.Ioc t₀ t, ψ s := by
    intro t ht
    refine le_trans (setLIntegral_mono' measurableSet_Ioc fun s hs => ?_) (hint t ht)
    obtain ⟨k, hk, h1, h2⟩ := exists_gridCell hτ (show s ∈ Set.Ioc t₀ T from ⟨hs.1, hs.2.trans ht.2⟩)
    have e : ∀ ω, drive t₀ b x s ω - eulerNoise W a b t₀ τ ξ N s ω =
        b (x s ω) s - b (X (eulerGrid t₀ τ k) ω) (eulerGrid t₀ τ k) := fun ω => by
      rw [drive_of_lt hc hs.1, ← hgridX k hk.le ω]
      congr 1
      exact sum_cellInd_eq hτ hk h1 h2 (fun i => b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i))
    simp_rw [e]
    exact hcell b hc.measurable_b (fun t ht => hc.lip_b ht) hH.hol_b s _ (le_eulerGrid hτ.le k)
      h1.le (hs.2.trans ht.2) (by rw [eulerGrid_succ] at h2; linarith)
  have hrate : ENNReal.ofReal (3 * sdeRate K d) = (3 * ENNReal.ofReal d + 12) * c := by
    rw [show 3 * sdeRate K d = (3 * d + 12) * (3 * K ^ 2) by unfold sdeRate; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_mul (by norm_num)]
    simp only [ENNReal.ofReal_ofNat, c]
  have hmain : ∀ t ∈ Set.Icc t₀ T, ψ t ≤ (3 * ENNReal.ofReal d + 12) * (ENNReal.ofReal d * β) +
      ENNReal.ofReal (3 * sdeRate K d) * ∫⁻ s in Set.Ioc t₀ t, ψ s := by
    intro t ht
    have h := sup_sq_sub_le hW (A₁ := fun s ω => a (x s ω) s) (A₂ := eulerDrift W a b t₀ τ ξ N)
      ht₀ ht (hx.isItoIntegrand hc ht₀) hB (fun s ω hs => drive_of_le hc hs ω) hB0
      (measurable_comp_coeff hc.measurable_a hx.measurable) hAm
      (hx.cont.mono fun ω hω => hc.driftCoeff.integrableOn hx.measurable hω)
      (Eventually.of_forall fun ω => (integrable_eulerDrift N ω).integrableOn)
      hξ.aestronglyMeasurable.aemeasurable hξ.aestronglyMeasurable.aemeasurable hx.cont hXc
      hx.eq hXeq
    refine h.trans ?_
    simp only [sub_self, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      lintegral_zero, mul_zero, zero_add]
    set I := ∫⁻ s in Set.Ioc t₀ t, ψ s
    calc 3 * ENNReal.ofReal (t - t₀) *
          tsSq P (fun s ω => a (x s ω) s - eulerDrift W a b t₀ τ ξ N s ω) t₀ t +
          12 * tsSq P (fun s ω => drive t₀ b x s ω - eulerNoise W a b t₀ τ ξ N s ω) t₀ t
        ≤ 3 * ENNReal.ofReal d * (ENNReal.ofReal d * β + c * I) +
            12 * (ENNReal.ofReal d * β + c * I) := by
          gcongr
          · simp only [d]; linarith [ht.2]
          · exact hdrift t ht
          · exact hnoise t ht
      _ = _ := by rw [hrate]; ring
  have hfin : ψ T ≠ ⊤ := ((IsSDESol.supSq_sub_le_two hT hx.measurable hx.cont).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (hx.supSq_lt_top hW hc ht₀ hT hξ),
      ENNReal.mul_lt_top (by norm_num) (supSq_eulerInterp_lt_top hW hc ht₀ hτ hξm hξ)⟩)).ne
  have hg := gronwall_ennreal (ψ := ψ) (L := 3 * sdeRate K d) (by have := sdeRate_nonneg (K := K) hd; positivity)
    (fun s _ t _ hst => supSq_mono_right hst) hfin hmain T ⟨hT, le_rfl⟩
  refine hg.trans (le_of_eq ?_)
  have ec : c = 3 * ENNReal.ofReal (K ^ 2) := by
    show ENNReal.ofReal (3 * K ^ 2) = _
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have e6 : ENNReal.ofReal (6 * K ^ 2 * τ) = 6 * ENNReal.ofReal (K ^ 2) * ENNReal.ofReal τ := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  simp only [β, ec, e6, ofReal_eulerC hd]
  ring

end Main

/-- **The explicit constant of the strong order-½ bound**:
`C(K, d, m) = C₀(K, d) (1 + C_mom(K, d) (1 + m)) e^{3 L d}` with `C₀ = eulerC`,
`C_mom = sdeMomentConst`, `L = sdeRate K d`, `d = T - t₀` and `m = E ξ²`. -/
def eulerErrConst (K d m : ℝ) : ℝ :=
  eulerC K d * (1 + sdeMomentConst K d * (1 + m)) * Real.exp (3 * sdeRate K d * d)

lemma eulerC_nonneg {K d : ℝ} (hd : 0 ≤ d) : 0 ≤ eulerC K d := by unfold eulerC; positivity

lemma sdeMomentConst_nonneg {K d : ℝ} (hd : 0 ≤ d) : 0 ≤ sdeMomentConst K d := by
  unfold sdeMomentConst; have := sdeRate_nonneg (K := K) hd; positivity

/-- **Strong convergence of order ½ of the Euler–Maruyama scheme (10.1.26)**: on the uniform grid
`t_i = t₀ + i τ` with `t_N = T`, under the Lipschitz, growth and Hölder-½ conditions,
`E |x(T) - x_N|² ≤ C(K, T - t₀, E ξ²) τ`, where `x` is the solution of (4.3.4) and `x_N` the
`N`-th Euler iterate. -/
theorem euler_strong_order_half {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ T τ K : ℝ} {N : ℕ}
    {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) (hc : SDECoeffs a b t₀ T K)
    (hH : SDEHolder a b t₀ T K) (ht₀ : 0 ≤ t₀) (hτ : 0 < τ) (hTN : eulerGrid t₀ τ N = T)
    (hξm : StronglyMeasurable[𝓕 t₀] ξ) (hξ : MemLp ξ 2 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x) :
    ∫ ω, (x T ω - eulerSeq W a b t₀ τ ξ N ω) ^ 2 ∂P ≤
      eulerErrConst K (T - t₀) (∫ ω, ξ ω ^ 2 ∂P) * τ := by
  subst hTN
  have := hW.isProbabilityMeasure
  set T := eulerGrid t₀ τ N
  have hT : t₀ ≤ T := le_eulerGrid hτ.le N
  have hd : 0 ≤ T - t₀ := sub_nonneg.mpr hT
  set m := ∫ ω, ξ ω ^ 2 ∂P
  have hm : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  have h1 := supSq_sub_eulerInterp_le hW hc ht₀ hτ hξm hξ hH hx
  have h2 := hx.supSq_le_const hW hc ht₀ hT hξ
  rw [lintegral_enorm_sq_eq hξ] at h2
  have hpt : ∫⁻ ω, ‖x T ω - eulerSeq W a b t₀ τ ξ N ω‖ₑ ^ 2 ∂P ≤
      supSq P (fun s ω => x s ω - eulerInterp W a b t₀ τ ξ N s ω) t₀ T := by
    refine lintegral_mono fun ω => ?_
    rw [← eulerInterp_grid hτ le_rfl ω]
    exact pow_le_pow_left' (enorm_le_iSup_Icc (Y := fun s ω => x s ω - eulerInterp W a b t₀ τ ξ N s ω)
      ⟨hT, le_rfl⟩ ω) 2
  have hbound : ∫⁻ ω, ‖x T ω - eulerSeq W a b t₀ τ ξ N ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (eulerErrConst K (T - t₀) m * τ) := by
    refine hpt.trans (h1.trans ?_)
    calc ENNReal.ofReal (eulerC K (T - t₀)) * (1 + supSq P x t₀ T) * ENNReal.ofReal τ *
          ENNReal.ofReal (Real.exp (3 * sdeRate K (T - t₀) * (T - t₀)))
        ≤ ENNReal.ofReal (eulerC K (T - t₀)) *
            (1 + ENNReal.ofReal (sdeMomentConst K (T - t₀)) * (1 + ENNReal.ofReal m)) *
            ENNReal.ofReal τ * ENNReal.ofReal (Real.exp (3 * sdeRate K (T - t₀) * (T - t₀))) := by
          gcongr
      _ = ENNReal.ofReal (eulerErrConst K (T - t₀) m * τ) := by
          have h0 := eulerC_nonneg (K := K) hd
          have h0' := sdeMomentConst_nonneg (K := K) hd
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hm,
            ← ENNReal.ofReal_mul h0', ← ENNReal.ofReal_add zero_le_one (by positivity),
            ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          unfold eulerErrConst; ring
  have hmeas : AEStronglyMeasurable (fun ω => (x T ω - eulerSeq W a b t₀ τ ξ N ω) ^ 2) P :=
    (((measurable_of_uncurry hx.measurable T).sub
      (measurable_eulerSeq hW hc ht₀ hτ hξm hξ N)).pow_const 2).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _) hmeas]
  have e : ∀ ω, ENNReal.ofReal ((x T ω - eulerSeq W a b t₀ τ ξ N ω) ^ 2) =
      ‖x T ω - eulerSeq W a b t₀ τ ξ N ω‖ₑ ^ 2 := fun ω => (enorm_sq_eq_ofReal _).symm
  simp_rw [e]
  have hC : 0 ≤ eulerErrConst K (T - t₀) m * τ := by
    unfold eulerErrConst
    have := eulerC_nonneg (K := K) hd
    have := sdeMomentConst_nonneg (K := K) hd
    positivity
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hC)

lemma eulerGrid_div (t₀ T : ℝ) (N : ℕ) :
    eulerGrid t₀ ((T - t₀) / (N + 1 : ℕ)) (N + 1) = T := by
  unfold eulerGrid
  have : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **Convergence of the Cauchy–Euler approximations (Gardiner §4.3.1)**: with `N + 1` uniform
steps of size `τ_N = (T - t₀)/(N + 1)`, the Euler approximations converge to the solution in mean
square at the final time: `E |x(T) - x^{(N)}_{N+1}|² ≤ C (T - t₀)/(N + 1) → 0`. -/
theorem tendsto_euler {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ}
    {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) (hc : SDECoeffs a b t₀ T K)
    (hH : SDEHolder a b t₀ T K) (ht₀ : 0 ≤ t₀) (htT : t₀ < T)
    (hξm : StronglyMeasurable[𝓕 t₀] ξ) (hξ : MemLp ξ 2 P) (hx : IsSDESol W 𝓕 P a b t₀ T ξ x) :
    Tendsto (fun N : ℕ => ∫ ω, (x T ω - eulerSeq W a b t₀ ((T - t₀) / (N + 1 : ℕ)) ξ (N + 1) ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  set C := eulerErrConst K (T - t₀) (∫ ω, ξ ω ^ 2 ∂P)
  have hup : Tendsto (fun N : ℕ => C * ((T - t₀) / (N + 1 : ℕ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (C * (T - t₀))
    simp only [mul_zero] at h
    refine h.congr fun N => ?_
    push_cast; ring
  refine squeeze_zero (fun N => integral_nonneg fun _ => sq_nonneg _) (fun N => ?_) hup
  exact euler_strong_order_half hW hc hH ht₀ (div_pos (sub_pos.mpr htT) (by positivity))
    (eulerGrid_div t₀ T N) hξm hξ hx

end Gardiner.Ito.StochDE
