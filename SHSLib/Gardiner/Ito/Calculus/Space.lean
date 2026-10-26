/-
# The space of Itô integrands on `[0, T]` (Gardiner §4.2.4, §4.2.6)

* `Gardiner.Ito.tsMeasure P T = (Lebesgue on (0, T]) ⊗ P`, the time–space measure: the squared
  norm of an integrand is `∫ G² d(tsMeasure P T) = ⟨∫₀ᵀ G(t)² dt⟩`
  (`Gardiner.Ito.integral_sq_tsMeasure`);
* `Gardiner.Ito.IsItoIntegrand 𝓕 P T G`: `G` is jointly measurable, nonanticipating (`G t` is
  `𝓕 t`-measurable for `0 ≤ t ≤ T`) and `⟨∫₀ᵀ G² dt⟩ < ∞` (`G ∈ L²(tsMeasure P T)`);
* the process of an elementary integrand supported in `(0, T]` is an Itô integrand
  (`Gardiner.Ito.ElemIntegrand.isItoIntegrand`), and its integral satisfies the isometry in the
  form `⟨∫G dW ∫H dW⟩ = ∫ G H d(tsMeasure P T)` (`Gardiner.Ito.ElemIntegrand.integral_mul_ts`).

Mean-square helpers (`Gardiner.Ito.l2Lim`, …) are also collected here.
-/
import SHSLib.Gardiner.Ito.Calculus.Elementary

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Mean-square helpers -/

section MS

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma l2_inner_toLp {X Y : α → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    @inner ℝ _ _ (hX.toLp X) (hY.toLp Y) = ∫ a, X a * Y a ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with a h1 h2
  simp [h1, h2, mul_comm]

lemma l2_norm_toLp_sq {X : α → ℝ} (hX : MemLp X 2 μ) :
    ‖hX.toLp X‖ ^ 2 = ∫ a, X a ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, l2_inner_toLp]
  simp [sq]

lemma l2_norm_toLp_sub_sq {X Y : α → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ‖hX.toLp X - hY.toLp Y‖ ^ 2 = ∫ a, (X a - Y a) ^ 2 ∂μ := by
  rw [← MemLp.toLp_sub, l2_norm_toLp_sq]
  rfl

/-- Mean-square convergence is convergence in `L²`. -/
lemma l2_tendsto_toLp {X : ℕ → α → ℝ} {Y : α → ℝ} (hX : ∀ n, MemLp (X n) 2 μ)
    (hY : MemLp Y 2 μ) (h : Tendsto (fun n => ∫ a, (X n a - Y a) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hY.toLp Y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun n => Real.sqrt (∫ a, (X n a - Y a) ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa using h.sqrt
  refine h2.congr fun n => ?_
  rw [← l2_norm_toLp_sub_sq (hX n) hY, Real.sqrt_sq (norm_nonneg _)]

/-- Convergence in `L²` is mean-square convergence. -/
lemma l2_tendsto_of_toLp {X : ℕ → α → ℝ} {Y : α → ℝ} (hX : ∀ n, MemLp (X n) 2 μ)
    (hY : MemLp Y 2 μ) (h : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hY.toLp Y))) :
    Tendsto (fun n => ∫ a, (X n a - Y a) ^ 2 ∂μ) atTop (𝓝 0) := by
  have h1 := ((tendsto_iff_norm_sub_tendsto_zero.mp h).pow 2)
  rw [zero_pow two_ne_zero] at h1
  exact h1.congr fun n => l2_norm_toLp_sub_sq (hX n) hY

/-- A mean-square limit, chosen when it exists (`0` otherwise). -/
def l2Lim (X : ℕ → α → ℝ) (μ : Measure α) : α → ℝ :=
  open Classical in
  if h : ∃ Y, MemLp Y 2 μ ∧ Tendsto (fun n => ∫ a, (X n a - Y a) ^ 2 ∂μ) atTop (𝓝 0) then
    h.choose else 0

lemma l2Lim_spec {X : ℕ → α → ℝ} {Y : α → ℝ} (hY : MemLp Y 2 μ)
    (h : Tendsto (fun n => ∫ a, (X n a - Y a) ^ 2 ∂μ) atTop (𝓝 0)) :
    MemLp (l2Lim X μ) 2 μ ∧ Tendsto (fun n => ∫ a, (X n a - l2Lim X μ a) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hex : ∃ Y, MemLp Y 2 μ ∧ Tendsto (fun n => ∫ a, (X n a - Y a) ^ 2 ∂μ) atTop (𝓝 0) :=
    ⟨Y, hY, h⟩
  rw [l2Lim, dif_pos hex]
  exact hex.choose_spec

/-- Mean-square limits are unique almost everywhere. -/
lemma l2_ae_unique {X : ℕ → α → ℝ} {Y Z : α → ℝ} (hX : ∀ n, MemLp (X n) 2 μ)
    (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ)
    (h1 : Tendsto (fun n => ∫ a, (X n a - Y a) ^ 2 ∂μ) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫ a, (X n a - Z a) ^ 2 ∂μ) atTop (𝓝 0)) : Y =ᵐ[μ] Z := by
  have := tendsto_nhds_unique (l2_tendsto_toLp hX hY h1) (l2_tendsto_toLp hX hZ h2)
  exact (MemLp.toLp_eq_toLp_iff hY hZ).mp this

/-- Correlations pass to mean-square limits. -/
lemma l2_tendsto_integral_mul {X Y : ℕ → α → ℝ} {X' Y' : α → ℝ}
    (hX : ∀ n, MemLp (X n) 2 μ) (hY : ∀ n, MemLp (Y n) 2 μ) (hX' : MemLp X' 2 μ)
    (hY' : MemLp Y' 2 μ) (h1 : Tendsto (fun n => ∫ a, (X n a - X' a) ^ 2 ∂μ) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫ a, (Y n a - Y' a) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, X n a * Y n a ∂μ) atTop (𝓝 (∫ a, X' a * Y' a ∂μ)) := by
  have h := (l2_tendsto_toLp hX hX' h1).inner (𝕜 := ℝ) (l2_tendsto_toLp hY hY' h2)
  simp only [l2_inner_toLp] at h
  exact h

/-- Means pass to mean-square limits. -/
lemma l2_tendsto_integral [IsFiniteMeasure μ] {X : ℕ → α → ℝ} {X' : α → ℝ}
    (hX : ∀ n, MemLp (X n) 2 μ) (hX' : MemLp X' 2 μ)
    (h1 : Tendsto (fun n => ∫ a, (X n a - X' a) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, X n a ∂μ) atTop (𝓝 (∫ a, X' a ∂μ)) := by
  have h := l2_tendsto_integral_mul hX (fun _ => memLp_const (1 : ℝ)) hX'
    (memLp_const (1 : ℝ)) h1 (by simp)
  simpa using h

/-- `∫ |f| ≤ δ + (∫ f²)/δ` on a probability space. -/
lemma integral_abs_le_of_sq [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) {δ : ℝ}
    (hδ : 0 < δ) : ∫ a, |f a| ∂μ ≤ δ + (∫ a, f a ^ 2 ∂μ) / δ := by
  have hle : ∀ a, |f a| ≤ δ + f a ^ 2 / δ := fun a => by
    rcases le_total (|f a|) δ with h | h
    · have : 0 ≤ f a ^ 2 / δ := by positivity
      linarith
    · have : |f a| ≤ f a ^ 2 / δ := by
        rw [le_div_iff₀ hδ, ← sq_abs]
        nlinarith [abs_nonneg (f a)]
      linarith [hδ.le]
  have hi : Integrable (fun a => δ + f a ^ 2 / δ) μ :=
    (integrable_const δ).add (hf.integrable_sq.div_const δ)
  calc ∫ a, |f a| ∂μ ≤ ∫ a, (δ + f a ^ 2 / δ) ∂μ :=
        integral_mono (hf.integrable one_le_two).abs hi hle
    _ = δ + (∫ a, f a ^ 2 ∂μ) / δ := by
        rw [integral_add (integrable_const δ) (hf.integrable_sq.div_const δ), integral_div]
        simp

/-- Mean-square convergence implies `L¹` convergence on a probability space. -/
lemma tendsto_integral_abs_of_l2 [IsProbabilityMeasure μ] {X : ℕ → α → ℝ} {Y : α → ℝ}
    (hX : ∀ n, MemLp (X n) 2 μ) (hY : MemLp Y 2 μ)
    (h : Tendsto (fun n => ∫ a, (X n a - Y a) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, |X n a - Y a| ∂μ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (ε / 2 * (ε / 3)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := integral_abs_le_of_sq ((hX n).sub hY) (δ := ε / 3) (by positivity)
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h2
  have h0 : 0 ≤ ∫ a, |X n a - Y a| ∂μ := integral_nonneg fun _ => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  have h3 : (∫ a, ((X n - Y) a) ^ 2 ∂μ) / (ε / 3) < ε / 2 := by
    rw [div_lt_iff₀ (by positivity)]; simpa using h2
  simp only [Pi.sub_apply] at h1 h3
  linarith

end MS

/-- If `Y` is an `L¹`-limit of `m`-measurable functions, then `E[Y | 𝓕 T] = Y` a.e. -/
lemma condExp_eq_of_tendsto_l1 {𝓕 : Filtration ℝ mΩ} {μ : Measure Ω} (T : ℝ)
    [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hXm : ∀ n, StronglyMeasurable[𝓕 T] (X n))
    (hXi : ∀ n, Integrable (X n) μ) (hYi : Integrable Y μ)
    (h : Tendsto (fun n => ∫ a, |X n a - Y a| ∂μ) atTop (𝓝 0)) : μ[Y | 𝓕 T] =ᵐ[μ] Y := by
  have hm := 𝓕.le T
  have hbound : ∀ n, ∫ a, |μ[Y | 𝓕 T] a - Y a| ∂μ ≤ 2 * ∫ a, |X n a - Y a| ∂μ := fun n => by
    have hc : μ[Y | 𝓕 T] - X n =ᵐ[μ] μ[Y - X n | 𝓕 T] := by
      have := condExp_sub hYi (hXi n) (𝓕 T)
      rw [condExp_of_stronglyMeasurable hm (hXm n) (hXi n)] at this
      exact this.symm
    have h1 : ∫ a, |μ[Y | 𝓕 T] a - X n a| ∂μ ≤ ∫ a, |X n a - Y a| ∂μ := by
      calc ∫ a, |μ[Y | 𝓕 T] a - X n a| ∂μ = ∫ a, |μ[Y - X n | 𝓕 T] a| ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hc] with a ha
            simp only [Pi.sub_apply] at ha ⊢
            rw [ha]
        _ ≤ ∫ a, |(Y - X n) a| ∂μ := integral_abs_condExp_le _
        _ = ∫ a, |X n a - Y a| ∂μ := by
            congr 1; funext a; simp [abs_sub_comm]
    have hi1 : Integrable (fun a => |μ[Y | 𝓕 T] a - X n a|) μ :=
      (integrable_condExp.sub (hXi n)).abs
    have hi2 : Integrable (fun a => |X n a - Y a|) μ := ((hXi n).sub hYi).abs
    calc ∫ a, |μ[Y | 𝓕 T] a - Y a| ∂μ ≤ ∫ a, (|μ[Y | 𝓕 T] a - X n a| + |X n a - Y a|) ∂μ :=
          integral_mono (integrable_condExp.sub hYi).abs (hi1.add hi2) fun a => by
            have := abs_sub_le (μ[Y | 𝓕 T] a) (X n a) (Y a)
            simpa using this
      _ = ∫ a, |μ[Y | 𝓕 T] a - X n a| ∂μ + ∫ a, |X n a - Y a| ∂μ := integral_add hi1 hi2
      _ ≤ 2 * ∫ a, |X n a - Y a| ∂μ := by linarith
  have h0 : ∫ a, |μ[Y | 𝓕 T] a - Y a| ∂μ = 0 := by
    refine le_antisymm (ge_of_tendsto (h.const_mul 2) (Eventually.of_forall fun n => ?_) |>.trans
      (by simp)) (integral_nonneg fun _ => abs_nonneg _)
    exact hbound n
  have hz := (integral_eq_zero_iff_of_nonneg (fun a => abs_nonneg _)
    (integrable_condExp.sub hYi).abs).mp h0
  filter_upwards [hz] with a ha
  simpa [sub_eq_zero] using ha


/-! ### The time–space measure and Itô integrands -/

/-- The time–space measure `(Lebesgue on (0, T]) ⊗ P` on `ℝ × Ω`. -/
def tsMeasure (P : Measure Ω) (T : ℝ) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Ioc 0 T)).prod P

instance (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) : IsFiniteMeasure (tsMeasure P T) := by
  unfold tsMeasure; infer_instance

lemma tsMeasure_mono (P : Measure Ω) [SFinite P] {S T : ℝ} (hST : S ≤ T) :
    tsMeasure P S ≤ tsMeasure P T := by
  refine Measure.le_iff.mpr fun s hs => ?_
  unfold tsMeasure
  rw [Measure.prod_apply hs, Measure.prod_apply hs]
  exact lintegral_mono_set (Set.Ioc_subset_Ioc_right hST)

/-- **Itô integrands on `[0, T]`** (Gardiner §4.2.4): jointly measurable, nonanticipating with
respect to `𝓕`, and `⟨∫₀ᵀ G(t)² dt⟩ < ∞`. -/
structure IsItoIntegrand (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ) (G : ℝ → Ω → ℝ) :
    Prop where
  measurable : Measurable (Function.uncurry G)
  adapted : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (G t)
  memLp : MemLp (Function.uncurry G) 2 (tsMeasure P T)

variable {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- `∫ G² d(tsMeasure P T) = ⟨∫₀ᵀ G(t)² dt⟩` for an Itô integrand. -/
lemma integral_sq_tsMeasure [SFinite P] {T : ℝ} {G : ℝ → Ω → ℝ}
    (hG : MemLp (Function.uncurry G) 2 (tsMeasure P T)) :
    ∫ p, Function.uncurry G p ^ 2 ∂(tsMeasure P T) = ∫ t in Set.Ioc 0 T, ∫ ω, G t ω ^ 2 ∂P := by
  unfold tsMeasure
  rw [integral_prod _ hG.integrable_sq]
  rfl

lemma IsItoIntegrand.mono [SFinite P] {T S : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) (hST : S ≤ T) :
    IsItoIntegrand 𝓕 P S G where
  measurable := hG.measurable
  adapted t ht htS := hG.adapted t ht (htS.trans hST)
  memLp := hG.memLp.mono_measure (tsMeasure_mono P hST)

lemma IsItoIntegrand.add {T : ℝ} {G H : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G)
    (hH : IsItoIntegrand 𝓕 P T H) : IsItoIntegrand 𝓕 P T (fun t ω => G t ω + H t ω) where
  measurable := hG.measurable.add hH.measurable
  adapted t ht htT := (hG.adapted t ht htT).add (hH.adapted t ht htT)
  memLp := hG.memLp.add hH.memLp

lemma IsItoIntegrand.const_mul {T : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) (c : ℝ) :
    IsItoIntegrand 𝓕 P T (fun t ω => c * G t ω) where
  measurable := hG.measurable.const_mul c
  adapted t ht htT := (hG.adapted t ht htT).const_mul c
  memLp := hG.memLp.const_mul c

lemma IsItoIntegrand.sub {T : ℝ} {G H : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G)
    (hH : IsItoIntegrand 𝓕 P T H) : IsItoIntegrand 𝓕 P T (fun t ω => G t ω - H t ω) where
  measurable := hG.measurable.sub hH.measurable
  adapted t ht htT := (hG.adapted t ht htT).sub (hH.adapted t ht htT)
  memLp := hG.memLp.sub hH.memLp

namespace ElemIntegrand

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma memLp_process [IsFiniteMeasure P] (H : ElemIntegrand 𝓕 P ι) (T : ℝ) :
    MemLp (Function.uncurry H.process) 2 (tsMeasure P T) := by
  unfold process
  have : Function.uncurry (fun s ω => ∑ i, H.val i ω * cellInd (H.left i) (H.right i) s) =
      ∑ i, fun p : ℝ × Ω => H.val i p.2 * cellInd (H.left i) (H.right i) p.1 := by
    funext ⟨s, ω⟩; simp
  rw [this]
  refine memLp_finset_sum' _ fun i _ => ?_
  have h1 : MemLp (fun p : ℝ × Ω => H.val i p.2) 2 (tsMeasure P T) :=
    (H.memLp i).comp_snd _
  refine h1.of_le (((H.adapted i).mono (𝓕.le _)).measurable.comp measurable_snd |>.mul
    ((measurable_cellInd _ _).comp measurable_fst)).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  calc |H.val i p.2| * |cellInd (H.left i) (H.right i) p.1| ≤ |H.val i p.2| * 1 := by
        gcongr
        rw [abs_of_nonneg (cellInd_nonneg _ _ _)]; exact cellInd_le_one _ _ _
    _ = |H.val i p.2| := mul_one _

/-- The process of an elementary integrand is an Itô integrand. -/
lemma isItoIntegrand [IsFiniteMeasure P] (H : ElemIntegrand 𝓕 P ι) (T : ℝ) :
    IsItoIntegrand 𝓕 P T H.process where
  measurable := H.measurable_process
  adapted t _ _ := H.process_adapted t
  memLp := H.memLp_process T

/-- The pieces of `H` minus those of `K`. -/
def sub (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) : ElemIntegrand 𝓕 P (ι ⊕ κ) :=
  H.add (K.smul (-1))

@[simp] lemma integral_sub (W : ℝ → Ω → ℝ) (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) :
    (H.sub K).integral W = fun ω => H.integral W ω - K.integral W ω := by
  funext ω; simp [sub]; ring

@[simp] lemma process_sub (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) :
    (H.sub K).process = fun s ω => H.process s ω - K.process s ω := by
  funext s ω; simp [sub]; ring

@[simp] lemma running_sub (W : ℝ → Ω → ℝ) (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) :
    (H.sub K).running W = fun t ω => H.running W t ω - K.running W t ω := by
  funext t ω; simp [sub]; ring

/-- Supported in `(0, T]`. -/
def SupportedIn (H : ElemIntegrand 𝓕 P ι) (T : ℝ) : Prop := ∀ i, H.right i ≤ T

lemma SupportedIn.sub {H : ElemIntegrand 𝓕 P ι} {K : ElemIntegrand 𝓕 P κ} {T : ℝ}
    (hH : H.SupportedIn T) (hK : K.SupportedIn T) : (H.sub K).SupportedIn T := by
  intro i
  cases i with
  | inl i => exact hH i
  | inr i => exact hK i

/-- **The isometry for elementary integrands in time–space form**:
`⟨∫ G dW ∫ H dW⟩ = ∫ G H d(tsMeasure P T)` for `G` supported in `(0, T]`. -/
theorem integral_mul_ts {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) (H : ElemIntegrand 𝓕 P ι)
    (K : ElemIntegrand 𝓕 P κ) {T : ℝ} (hH : H.SupportedIn T) :
    ∫ ω, H.integral W ω * K.integral W ω ∂P =
      ∫ p, Function.uncurry H.process p * Function.uncurry K.process p ∂(tsMeasure P T) := by
  have := hW.isProbabilityMeasure
  have hint : Integrable (fun p => Function.uncurry H.process p * Function.uncurry K.process p)
      (tsMeasure P T) := (H.memLp_process T).integrable_mul (K.memLp_process T)
  unfold tsMeasure at hint ⊢
  rw [integral_mul hW H K, integral_prod _ hint]
  simp only [Function.uncurry_apply_pair]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro s hs
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
  rcases hs with hs | hs
  · simp [H.process_eq_zero_of_le hs]
  · simp [H.process_eq_zero_of_ge hH hs]

/-- `⟨(∫ H dW - ∫ K dW)²⟩ = ∫ (H - K)² d(tsMeasure P T)`. -/
theorem integral_sub_sq_ts {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) (H : ElemIntegrand 𝓕 P ι)
    (K : ElemIntegrand 𝓕 P κ) {T : ℝ} (hH : H.SupportedIn T) (hK : K.SupportedIn T) :
    ∫ ω, (H.integral W ω - K.integral W ω) ^ 2 ∂P =
      ∫ p, (Function.uncurry H.process p - Function.uncurry K.process p) ^ 2 ∂(tsMeasure P T) := by
  have h := integral_mul_ts hW (H.sub K) (H.sub K) (hH.sub hK)
  simp only [integral_sub, process_sub] at h
  simp_rw [sq]
  exact h

end ElemIntegrand

end Gardiner.Ito
