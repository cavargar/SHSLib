/-
# Left-point Riemann sums converge to the Itô integral (Gardiner §4.2.1, (4.2.8)–(4.2.10))

Gardiner *defines* `∫₀ᵀ G dW` as the mean-square limit of the left-point sums
`Σᵢ G(tᵢ₋₁)(W(tᵢ) - W(tᵢ₋₁))`.  For an Itô integrand which is (uniformly) continuous in mean
square on `[0, T]` — e.g. a continuous deterministic function, `W` itself, or `f(W(t))` for
`f` of moderate growth — these sums on the uniform partitions `tᵢ = iT/(n+1)` converge in mean
square to `itoInt` (`Gardiner.Ito.itoRiemann_tendsto`).  So the general integral agrees with
Gardiner's definition wherever the latter applies, in particular with the Wiener integral
(`Gardiner.Ito.itoInt_det_tendsto`).

`W` itself is an Itô integrand when it is jointly measurable (`Gardiner.Ito.IsFWiener.isItoIntegrand_W`).
-/
import SHSLib.Gardiner.Ito.Calculus.Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

/-- The uniform grid point `tᵢ = i T/(n+1)`. -/
def gridPt (T : ℝ) (n i : ℕ) : ℝ := i * (T / (n + 1))

lemma gridPt_nonneg {T : ℝ} (hT : 0 ≤ T) (n i : ℕ) : 0 ≤ gridPt T n i := by
  unfold gridPt; positivity

lemma gridPt_le {T : ℝ} (hT : 0 ≤ T) {n i : ℕ} (hi : i ≤ n + 1) : gridPt T n i ≤ T := by
  unfold gridPt
  have h1 : (i : ℝ) ≤ n + 1 := by exact_mod_cast hi
  have h2 : (i : ℝ) * (T / (n + 1)) ≤ (n + 1) * (T / (n + 1)) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  rwa [mul_div_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)] at h2

lemma gridPt_succ (T : ℝ) (n i : ℕ) : gridPt T n (i + 1) = gridPt T n i + T / (n + 1) := by
  unfold gridPt; push_cast; ring

lemma gridPt_last (T : ℝ) (n : ℕ) : gridPt T n (n + 1) = T := by
  unfold gridPt; push_cast; field_simp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- **The left-point Riemann sum** `Σᵢ G(tᵢ)(W(tᵢ₊₁) - W(tᵢ))` on the uniform partition of
`[0, T]` into `n + 1` cells (Gardiner (4.2.8) with `τᵢ = tᵢ₋₁`). -/
def itoRiemann (W G : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), G (gridPt T n i) ω * (W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω)

section Elem

variable {T : ℝ} {G : ℝ → Ω → ℝ}

/-- The elementary integrand of the left-point Riemann sum. -/
def riemElem (hT : 0 ≤ T) (had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (G t))
    (hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (G t) 2 P) (n : ℕ) : ElemIntegrand 𝓕 P (Fin (n + 1)) where
  left i := gridPt T n i
  right i := gridPt T n (i + 1)
  val i := G (gridPt T n i)
  left_nonneg i := gridPt_nonneg hT n i
  left_le_right i := by rw [gridPt_succ]; linarith [(by positivity : (0 : ℝ) ≤ T / (n + 1))]
  adapted i := had _ (gridPt_nonneg hT n i) (gridPt_le hT (by omega))
  memLp i := hL2 _ (gridPt_nonneg hT n i) (gridPt_le hT (by omega))

variable (hT : 0 ≤ T) (had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (G t))
  (hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (G t) 2 P)

lemma riemElem_supportedIn (n : ℕ) : (riemElem hT had hL2 n).SupportedIn T :=
  fun i => gridPt_le hT (by omega)

lemma integral_riemElem (W : ℝ → Ω → ℝ) (n : ℕ) :
    (riemElem hT had hL2 n).integral W = itoRiemann W G T n := by
  funext ω
  simp only [ElemIntegrand.integral, riemElem, itoRiemann]
  exact Fin.sum_univ_eq_sum_range
    (fun i => G (gridPt T n i) ω * (W (gridPt T n (i + 1)) ω - W (gridPt T n i) ω)) (n + 1)

omit hT in
/-- On `(0, T]` the Riemann integrand is `G` at the left end of the cell containing `t`. -/
lemma riemElem_process (hT : 0 < T) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (ω : Ω) :
    (riemElem hT.le had hL2 n).process t ω = G (cellLeft (T / (n + 1)) 0 t) ω := by
  set h := T / (n + 1) with hh
  have hh0 : 0 < h := by positivity
  unfold ElemIntegrand.process
  simp only [riemElem]
  set k := ⌈(t - 0) / h⌉ with hk
  have hk1 : 1 ≤ k := Int.one_le_ceil_iff.mpr (div_pos (by linarith [ht.1]) hh0)
  set j₀ := (k - 1).toNat with hj₀
  have hj₀r : (j₀ : ℝ) = (k : ℝ) - 1 := by
    have : ((j₀ : ℤ) : ℝ) = ((k - 1 : ℤ) : ℝ) := by
      rw [hj₀, Int.toNat_of_nonneg (by omega)]
    push_cast at this; exact this
  have hklt : (k : ℝ) < (t - 0) / h + 1 := Int.ceil_lt_add_one _
  have hkge : (t - 0) / h ≤ k := Int.le_ceil _
  have hgp : ∀ j : ℕ, gridPt T n j = j * h := fun j => rfl
  have hlo : (j₀ : ℝ) * h < t := by
    rw [hj₀r]
    have := (lt_div_iff₀ hh0).mp (by linarith : (k : ℝ) - 1 < (t - 0) / h)
    linarith
  have hhi : t ≤ ((j₀ : ℝ) + 1) * h := by
    rw [hj₀r]
    have := (div_le_iff₀ hh0).mp hkge
    linarith
  have hj₀N : j₀ < n + 1 := by
    have h1 : (j₀ : ℝ) * h < (n + 1) * h := by
      calc (j₀ : ℝ) * h < t := hlo
        _ ≤ T := ht.2
        _ = (n + 1) * h := by rw [hh]; field_simp
    have : (j₀ : ℝ) < n + 1 := lt_of_mul_lt_mul_right h1 hh0.le
    exact_mod_cast this
  have hmem : ∀ j : Fin (n + 1),
      t ∈ Set.Ioc (gridPt T n j) (gridPt T n ((j : ℕ) + 1)) ↔ (j : ℕ) = j₀ := by
    intro j
    rw [hgp, hgp]
    constructor
    · intro hm
      have hceil : k = (j : ℕ) + 1 := by
        rw [hk, Int.ceil_eq_iff]
        push_cast
        constructor
        · rw [lt_div_iff₀ hh0]; push_cast at hm; linarith [hm.1]
        · rw [div_le_iff₀ hh0]; push_cast at hm; linarith [hm.2]
      rw [hj₀, hceil]; simp
    · intro hj
      rw [hj]; push_cast
      exact ⟨hlo, hhi⟩
  rw [Finset.sum_eq_single ⟨j₀, hj₀N⟩]
  · rw [cellInd_mem ((hmem ⟨j₀, hj₀N⟩).mpr rfl), mul_one]
    congr 1
    rw [hgp]; unfold cellLeft; rw [hj₀r, ← hk]; ring
  · intro j _ hj
    rw [cellInd_notMem (fun hm => hj (Fin.ext ((hmem j).mp hm))), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma cellLeft_zero_mem {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 ≤ cellLeft h 0 t ∧ cellLeft h 0 t < t ∧ t - cellLeft h 0 t ≤ h := by
  unfold cellLeft
  simp only [sub_zero, zero_add]
  have hk1 : (1 : ℝ) ≤ ⌈t / h⌉ := by
    exact_mod_cast Int.one_le_ceil_iff.mpr (div_pos ht hh)
  have hklt : (⌈t / h⌉ : ℝ) < t / h + 1 := Int.ceil_lt_add_one _
  have hkge : t / h ≤ ⌈t / h⌉ := Int.le_ceil _
  have e1 := (lt_div_iff₀ hh).mp (by linarith : (⌈t / h⌉ : ℝ) - 1 < t / h)
  have e2 := (div_le_iff₀ hh).mp hkge
  refine ⟨by nlinarith, by linarith, by nlinarith⟩

end Elem

/-- A process all of whose paths are continuous, with measurable time slices, is jointly
measurable (e.g. `Gardiner.Ito.stdWiener`). -/
lemma measurable_uncurry_of_continuous_paths {X : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => X t ω) (hm : ∀ t, Measurable (X t)) :
    Measurable (Function.uncurry X) :=
  measurable_uncurry_of_continuous_of_measurable hc hm

section Main

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) {T : ℝ} {G : ℝ → Ω → ℝ}
include hW

/-- **Left-point Riemann sums converge to the Itô integral in mean square** (Gardiner §4.2.1), for
an Itô integrand which is uniformly continuous in mean square on `[0, T]`. -/
theorem itoRiemann_tendsto (hT : 0 < T) (hG : IsItoIntegrand 𝓕 P T G)
    (hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (G t) 2 P)
    (hcont : ∀ ε > 0, ∃ δ > 0, ∀ s t, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → |s - t| < δ →
      ∫ ω, (G s ω - G t ω) ^ 2 ∂P < ε) :
    Tendsto (fun n => ∫ ω, (itoRiemann W G T n ω - itoInt W 𝓕 P T G ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  set H := fun n => riemElem (P := P) hT.le hG.adapted hL2 n
  have h := itoInt_tendsto hW hG H (fun n => riemElem_supportedIn hT.le hG.adapted hL2 n) ?_
  · refine h.congr fun n => ?_
    simp only [H, integral_riemElem]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := hcont (ε / (2 * (T + 1))) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hhδ : T / (n + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hint := ((H n).memLp_process (P := P) T).sub hG.memLp
  have hint2 : Integrable (fun p => (Function.uncurry (H n).process p - Function.uncurry G p) ^ 2)
      (tsMeasure P T) := hint.integrable_sq
  have e : ∫ p, (Function.uncurry (H n).process p - Function.uncurry G p) ^ 2 ∂(tsMeasure P T) =
      ∫ t in Set.Ioc 0 T, ∫ ω, ((H n).process t ω - G t ω) ^ 2 ∂P := by
    unfold tsMeasure at hint2 ⊢
    rw [integral_prod _ hint2]; rfl
  have hbound : ∫ t in Set.Ioc 0 T, ∫ ω, ((H n).process t ω - G t ω) ^ 2 ∂P ≤
      ∫ t in Set.Ioc 0 T, ε / (2 * (T + 1)) := by
    refine setIntegral_mono_on ?_ (integrableOn_const (by simp [Real.volume_Ioc]))
      measurableSet_Ioc fun t ht => ?_
    · unfold tsMeasure at hint2
      exact hint2.integral_prod_left
    · have hcl := cellLeft_zero_mem (by positivity : (0 : ℝ) < T / (n + 1)) ht.1
      have e2 : (fun ω => ((H n).process t ω - G t ω) ^ 2) =
          fun ω => (G (cellLeft (T / (n + 1)) 0 t) ω - G t ω) ^ 2 := by
        funext ω; simp only [H]; rw [riemElem_process hG.adapted hL2 hT n ht ω]
      rw [e2]
      refine (hδc _ _ hcl.1 (hcl.2.1.le.trans ht.2) ht.1.le ht.2 ?_).le
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hcl.2.1])]
      linarith [hcl.2.2]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _), e]
  refine hbound.trans_lt ?_
  rw [setIntegral_const, smul_eq_mul]
  have hvol : volume.real (Set.Ioc (0 : ℝ) T) = T := by
    simp [measureReal_def, Real.volume_Ioc, hT.le]
  rw [hvol]
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  nlinarith

omit hW in
/-- A continuous deterministic function is an Itô integrand on `[0, T]`. -/
lemma isItoIntegrand_det [IsFiniteMeasure P] (T : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    IsItoIntegrand 𝓕 P T (fun t _ => f t) := by
  refine ⟨hf.measurable.comp measurable_fst, fun t _ _ => stronglyMeasurable_const, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound (hf.measurable.comp measurable_fst).aestronglyMeasurable C ?_
  filter_upwards [ae_mem_Ioc_tsMeasure (P := P) T] with p hp
  exact hC p.1 (Set.Ioc_subset_Icc_self hp)

/-- The left-point Riemann sums are square integrable. -/
lemma memLp_itoRiemann (hT : 0 ≤ T) (had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (G t))
    (hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (G t) 2 P) (n : ℕ) :
    MemLp (itoRiemann W G T n) 2 P := by
  rw [← integral_riemElem hT had hL2 W n]
  exact ElemIntegrand.memLp_integral hW _

/-- **Continuous deterministic integrands**: for continuous `f`, the left-point Riemann sums
`Σ f(tᵢ)(W(tᵢ₊₁) - W(tᵢ))` (whose mean-square limit is the Wiener integral) converge in mean
square to `∫₀ᵀ f dW`. -/
theorem itoInt_det_tendsto (hT : 0 < T) {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun n => ∫ ω, (itoRiemann W (fun t _ => f t) T n ω -
      itoInt W 𝓕 P T (fun t _ => f t) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  have hG : IsItoIntegrand 𝓕 P T (fun t _ => f t) := isItoIntegrand_det T hf
  refine itoRiemann_tendsto hW hT hG (fun t _ _ => memLp_const _) fun ε hε => ?_
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous hf.continuousOn)
    (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨δ, hδ, fun s t hs hsT ht htT hst => ?_⟩
  have h1 := hδc s ⟨hs, hsT⟩ t ⟨ht, htT⟩ (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  calc (f s - f t) ^ 2 = |f s - f t| ^ 2 := (sq_abs _).symm
    _ < Real.sqrt ε ^ 2 := pow_lt_pow_left₀ h1 (abs_nonneg _) two_ne_zero
    _ = ε := Real.sq_sqrt hε.le

/-- `W` is an Itô integrand on `[0, T]` as soon as it is jointly measurable (e.g. when all its
paths are continuous). -/
theorem IsFWiener.isItoIntegrand_W (hWj : Measurable (Function.uncurry W)) (T : ℝ) :
    IsItoIntegrand 𝓕 P T W := by
  have := hW.isProbabilityMeasure
  refine ⟨hWj, fun t ht _ => hW.adapted t ht, ?_⟩
  refine (memLp_two_iff_integrable_sq hWj.aestronglyMeasurable).mpr ?_
  unfold tsMeasure
  refine (integrable_prod_iff ((hWj.pow_const 2).aestronglyMeasurable)).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hW.integrable_pow ht.1.le 2
  · have e : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
        ∫ ω, ‖Function.uncurry W (t, ω) ^ 2‖ ∂P = t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [Function.uncurry_apply_pair, norm_pow, Real.norm_eq_abs, sq_abs]
      exact hW.integral_sq ht.1.le
    refine (integrable_congr e).mpr ?_
    exact (continuous_id.integrableOn_Icc (a := 0) (b := T)).mono_set Set.Ioc_subset_Icc_self

/-- `W` is uniformly continuous in mean square: `⟨(W s - W t)²⟩ = |s - t|`. -/
lemma IsFWiener.integral_sub_sq_abs {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∫ ω, (W s ω - W t ω) ^ 2 ∂P = |s - t| := by
  rcases le_total s t with hst | hts
  · rw [show (fun ω => (W s ω - W t ω) ^ 2) = fun ω => (W t ω - W s ω) ^ 2 by
      funext ω; ring, hW.integral_incr_sq hs hst, abs_of_nonpos (by linarith)]
    ring
  · rw [hW.integral_incr_sq ht hts, abs_of_nonneg (by linarith)]

/-- **Riemann sums for `∫ W dW`**: `Σ W(tᵢ)(W(tᵢ₊₁) - W(tᵢ)) → ∫₀ᵀ W dW` in mean square. -/
theorem itoRiemann_W_tendsto (hWj : Measurable (Function.uncurry W)) (hT : 0 < T) :
    Tendsto (fun n => ∫ ω, (itoRiemann W W T n ω - itoInt W 𝓕 P T W ω) ^ 2 ∂P) atTop (𝓝 0) := by
  refine itoRiemann_tendsto hW hT (hW.isItoIntegrand_W hWj T) (fun t ht _ => hW.memLp ht)
    fun ε hε => ⟨ε, hε, fun s t hs _ ht _ hst => ?_⟩
  rw [hW.integral_sub_sq_abs hs ht]; exact hst

end Main

end Gardiner.Ito
