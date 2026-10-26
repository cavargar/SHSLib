/-
# The running Itô integral is a martingale (Gardiner §4.2.6 f)

For an Itô integrand `G` on `[0, t]` and `s ≤ t`, `E[∫₀ᵗ G dW | 𝓕 s] = ∫₀ˢ G dW` a.s.
(`Gardiner.Ito.condExp_itoInt`).  Consequently `t ↦ ∫₀ᵗ G dW` is an `𝓕`-martingale
(`Gardiner.Ito.martingale_itoInt`), and so is the process stopped at a horizon `T` for an integrand
given on `[0, T]` only (`Gardiner.Ito.martingale_itoInt_min`).
-/
import SHSLib.Gardiner.Ito.Calculus.Integral

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

namespace ElemIntegrand

variable {ι : Type*} [Fintype ι]

/-- The elementary integrand restricted to `(0, u]`. -/
def restrictTo (H : ElemIntegrand 𝓕 P ι) (u : ℝ) (hu : 0 ≤ u) : ElemIntegrand 𝓕 P ι where
  left i := min (H.left i) u
  right i := min (H.right i) u
  val i := if H.left i ≤ u then H.val i else 0
  left_nonneg i := le_min (H.left_nonneg i) hu
  left_le_right i := min_le_min_right u (H.left_le_right i)
  adapted i := by
    split_ifs with h
    · rw [min_eq_left h]; exact H.adapted i
    · exact stronglyMeasurable_zero
  memLp i := by
    split_ifs
    · exact H.memLp i
    · exact MemLp.zero

lemma restrictTo_supportedIn (H : ElemIntegrand 𝓕 P ι) {u : ℝ} (hu : 0 ≤ u) :
    (H.restrictTo u hu).SupportedIn u := fun _ => min_le_right _ _

lemma integral_restrictTo (W : ℝ → Ω → ℝ) (H : ElemIntegrand 𝓕 P ι) {u : ℝ} (hu : 0 ≤ u) :
    (H.restrictTo u hu).integral W = H.running W u := by
  funext ω
  simp only [integral, running, restrictTo]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · push_neg at h
    rw [min_eq_right h.le, min_eq_right (h.le.trans (H.left_le_right i))]
    simp

lemma process_restrictTo (H : ElemIntegrand 𝓕 P ι) {u : ℝ} (hu : 0 ≤ u) {s : ℝ} (hs : s ≤ u)
    (ω : Ω) : (H.restrictTo u hu).process s ω = H.process s ω := by
  simp only [process, restrictTo]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [min_eq_left h]
    congr 1
    by_cases hm : s ∈ Set.Ioc (H.left i) (H.right i)
    · rw [cellInd_mem hm, cellInd_mem ⟨hm.1, le_min hm.2 hs⟩]
    · rw [cellInd_notMem hm, cellInd_notMem fun h' => hm ⟨h'.1, h'.2.trans (min_le_left _ _)⟩]
  · push_neg at h
    rw [cellInd_notMem fun h' => absurd (hs.trans h.le) (not_le.mpr h'.1)]
    simp

/-- Restricting to `(0, u]` does not increase the distance to `G` (measured on `(0, u]`). -/
lemma dist_restrictTo_le [IsFiniteMeasure P] (H : ElemIntegrand 𝓕 P ι) {u t : ℝ} (hu : 0 ≤ u)
    (hut : u ≤ t) {G : ℝ → Ω → ℝ} (hG : MemLp (Function.uncurry G) 2 (tsMeasure P t)) :
    ∫ p, (Function.uncurry (H.restrictTo u hu).process p - Function.uncurry G p) ^ 2
        ∂(tsMeasure P u) ≤
      ∫ p, (Function.uncurry H.process p - Function.uncurry G p) ^ 2 ∂(tsMeasure P t) := by
  have e : ∫ p, (Function.uncurry (H.restrictTo u hu).process p - Function.uncurry G p) ^ 2
      ∂(tsMeasure P u) =
      ∫ p, (Function.uncurry H.process p - Function.uncurry G p) ^ 2 ∂(tsMeasure P u) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Ioc_tsMeasure (P := P) u] with p hp
    simp only [Function.uncurry]
    rw [process_restrictTo H hu hp.2]
  rw [e]
  exact integral_mono_measure (tsMeasure_mono P hut)
    (Eventually.of_forall fun _ => sq_nonneg _) ((H.memLp_process t).sub hG).integrable_sq

end ElemIntegrand

/-- Passing a conditional-expectation identity to `L¹` limits. -/
lemma condExp_eq_of_tendsto_l1_pair [IsFiniteMeasure P] (s : ℝ) {X Y : ℕ → Ω → ℝ} {A B : Ω → ℝ}
    (hcond : ∀ k, P[X k | 𝓕 s] =ᵐ[P] Y k) (hXi : ∀ k, Integrable (X k) P)
    (hYi : ∀ k, Integrable (Y k) P) (hA : Integrable A P) (hB : Integrable B P)
    (hX : Tendsto (fun k => ∫ ω, |X k ω - A ω| ∂P) atTop (𝓝 0))
    (hY : Tendsto (fun k => ∫ ω, |Y k ω - B ω| ∂P) atTop (𝓝 0)) : P[A | 𝓕 s] =ᵐ[P] B := by
  have hbound : ∀ k, ∫ ω, |P[A | 𝓕 s] ω - B ω| ∂P ≤
      ∫ ω, |X k ω - A ω| ∂P + ∫ ω, |Y k ω - B ω| ∂P := fun k => by
    have hc : P[A | 𝓕 s] - Y k =ᵐ[P] P[A - X k | 𝓕 s] := by
      have h1 := condExp_sub hA (hXi k) (𝓕 s)
      filter_upwards [h1, hcond k] with ω h1 h2
      simp only [Pi.sub_apply] at h1 ⊢
      rw [h1, h2]
    have h1 : ∫ ω, |P[A | 𝓕 s] ω - Y k ω| ∂P ≤ ∫ ω, |X k ω - A ω| ∂P := by
      calc ∫ ω, |P[A | 𝓕 s] ω - Y k ω| ∂P = ∫ ω, |P[A - X k | 𝓕 s] ω| ∂P := by
            refine integral_congr_ae ?_
            filter_upwards [hc] with ω hω
            simp only [Pi.sub_apply] at hω ⊢
            rw [hω]
        _ ≤ ∫ ω, |(A - X k) ω| ∂P := integral_abs_condExp_le _
        _ = ∫ ω, |X k ω - A ω| ∂P := by
            congr 1; funext ω; simp [abs_sub_comm]
    have hi1 : Integrable (fun ω => |P[A | 𝓕 s] ω - Y k ω|) P :=
      (integrable_condExp.sub (hYi k)).abs
    have hi2 : Integrable (fun ω => |Y k ω - B ω|) P := ((hYi k).sub hB).abs
    calc ∫ ω, |P[A | 𝓕 s] ω - B ω| ∂P ≤ ∫ ω, (|P[A | 𝓕 s] ω - Y k ω| + |Y k ω - B ω|) ∂P :=
          integral_mono (integrable_condExp.sub hB).abs (hi1.add hi2) fun ω => by
            have := abs_sub_le (P[A | 𝓕 s] ω) (Y k ω) (B ω)
            simpa using this
      _ = ∫ ω, |P[A | 𝓕 s] ω - Y k ω| ∂P + ∫ ω, |Y k ω - B ω| ∂P := integral_add hi1 hi2
      _ ≤ _ := by linarith
  have h0 : ∫ ω, |P[A | 𝓕 s] ω - B ω| ∂P = 0 := by
    refine le_antisymm (ge_of_tendsto (by simpa using hX.add hY)
      (Eventually.of_forall hbound)) (integral_nonneg fun _ => abs_nonneg _)
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _)
    (integrable_condExp.sub hB).abs).mp h0
  filter_upwards [hz] with ω hω
  simpa [sub_eq_zero] using hω

section Wiener

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) {G : ℝ → Ω → ℝ}
include hW

/-- `∫₀ᵀ G dW = 0` a.s. for `T ≤ 0`. -/
lemma itoInt_of_nonpos {T : ℝ} (hT : T ≤ 0) (hG : IsItoIntegrand 𝓕 P T G) :
    itoInt W 𝓕 P T G =ᵐ[P] 0 := by
  have := hW.isProbabilityMeasure
  have h0 : tsMeasure P T = 0 := by
    unfold tsMeasure
    rw [Set.Ioc_eq_empty (not_lt.mpr hT), Measure.restrict_empty, Measure.zero_prod]
  have h := itoInt_sub_sq hW hG (ElemIntegrand.zero (𝓕 := 𝓕) (P := P))
    (fun i => Fin.elim0 i)
  rw [h0] at h
  simp only [ElemIntegrand.integral_zero, Pi.zero_apply, zero_sub, even_two, Even.neg_pow,
    integral_zero_measure] at h
  have := ae_eq_zero_of_integral_sq (memLp_itoInt hW hG) h
  exact this

/-- **Martingale property of the running Itô integral**, nonnegative times. -/
lemma condExp_itoInt_of_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hG : IsItoIntegrand 𝓕 P t G) :
    P[itoInt W 𝓕 P t G | 𝓕 s] =ᵐ[P] itoInt W 𝓕 P s G := by
  have := hW.isProbabilityMeasure
  set A := approxSeq 𝓕 P t G
  have hAs := fun k => (approxSeq_spec hG k).1
  have hGs := hG.mono hst
  -- elementary integrals of the restrictions converge to `∫₀ˢ G dW`
  have hR := itoInt_tendsto hW hGs (fun k => (A k).2.restrictTo s hs)
    (fun k => (A k).2.restrictTo_supportedIn hs)
    (squeeze_zero (fun k => integral_nonneg fun _ => sq_nonneg _)
      (fun k => (A k).2.dist_restrictTo_le hs hst hG.memLp) (approxSeq_tendsto_ts hW hG))
  simp only [ElemIntegrand.integral_restrictTo] at hR
  have hX := approxSeq_tendsto hW hG
  refine condExp_eq_of_tendsto_l1_pair s (X := fun k => (A k).2.integral W)
    (Y := fun k => (A k).2.running W s) (fun k => ?_)
    (fun k => ((A k).2.memLp_integral hW).integrable one_le_two)
    (fun k => ((A k).2.memLp_running hW s).integrable one_le_two)
    ((memLp_itoInt hW hG).integrable one_le_two) ((memLp_itoInt hW hGs).integrable one_le_two)
    (tendsto_integral_abs_of_l2 (fun k => (A k).2.memLp_integral hW) (memLp_itoInt hW hG) hX)
    (tendsto_integral_abs_of_l2 (fun k => (A k).2.memLp_running hW s) (memLp_itoInt hW hGs) hR)
  show P[(A k).2.integral W | 𝓕 s] =ᵐ[P] (A k).2.running W s
  rw [← (A k).2.running_eq_integral W (hAs k)]
  exact ((A k).2.martingale_running hW).2 s t hst

/-- **Martingale property of the running Itô integral**: `E[∫₀ᵗ G dW | 𝓕 s] = ∫₀ˢ G dW` a.s.
for `s ≤ t`. -/
theorem condExp_itoInt {s t : ℝ} (hst : s ≤ t) (hG : IsItoIntegrand 𝓕 P t G) :
    P[itoInt W 𝓕 P t G | 𝓕 s] =ᵐ[P] itoInt W 𝓕 P s G := by
  have := hW.isProbabilityMeasure
  rcases le_or_gt 0 s with hs | hs
  · exact condExp_itoInt_of_nonneg hW hs hst hG
  have hzs := itoInt_of_nonpos hW hs.le (hG.mono hst)
  refine EventuallyEq.trans ?_ hzs.symm
  rcases le_or_gt t 0 with ht | ht
  · calc P[itoInt W 𝓕 P t G | 𝓕 s] =ᵐ[P] P[(0 : Ω → ℝ) | 𝓕 s] :=
          condExp_congr_ae (itoInt_of_nonpos hW ht hG)
      _ = 0 := condExp_zero
  · have h0 := condExp_itoInt_of_nonneg hW le_rfl ht.le hG
    have hz0 := itoInt_of_nonpos hW le_rfl (hG.mono ht.le)
    calc P[itoInt W 𝓕 P t G | 𝓕 s] =ᵐ[P] P[P[itoInt W 𝓕 P t G | 𝓕 0] | 𝓕 s] :=
          (condExp_condExp_of_le (𝓕.mono hs.le) (𝓕.le 0)).symm
      _ =ᵐ[P] P[itoInt W 𝓕 P 0 G | 𝓕 s] := condExp_congr_ae h0
      _ =ᵐ[P] P[(0 : Ω → ℝ) | 𝓕 s] := condExp_congr_ae hz0
      _ = 0 := condExp_zero

/-- **The running Itô integral `t ↦ ∫₀ᵗ G dW` is an `𝓕`-martingale** (for an integrand that is an
Itô integrand on every `[0, T]`). -/
theorem martingale_itoInt (hG : ∀ T, IsItoIntegrand 𝓕 P T G) :
    Martingale (fun t => itoInt W 𝓕 P t G) 𝓕 P :=
  ⟨fun t => itoInt_stronglyMeasurable hW (hG t), fun _ _ hst => condExp_itoInt hW hst (hG _)⟩

/-- For an integrand on `[0, T]`, the running integral stopped at `T`, `t ↦ ∫₀^{t ∧ T} G dW`, is an
`𝓕`-martingale. -/
theorem martingale_itoInt_min {T : ℝ} (hG : IsItoIntegrand 𝓕 P T G) :
    Martingale (fun t => itoInt W 𝓕 P (min t T) G) 𝓕 P := by
  have := hW.isProbabilityMeasure
  refine ⟨fun t => (itoInt_stronglyMeasurable hW (hG.mono (min_le_right t T))).mono
    (𝓕.mono (min_le_left t T)), fun s t hst => ?_⟩
  show P[itoInt W 𝓕 P (min t T) G | 𝓕 s] =ᵐ[P] itoInt W 𝓕 P (min s T) G
  rcases le_total s T with hsT | hTs
  · rw [min_eq_left hsT]
    exact condExp_itoInt hW (le_min hst hsT) (hG.mono (min_le_right t T))
  · rw [min_eq_right hTs, min_eq_right (hTs.trans hst)]
    exact (condExp_of_stronglyMeasurable (𝓕.le s)
      ((itoInt_stronglyMeasurable hW hG).mono (𝓕.mono hTs))
      ((memLp_itoInt hW hG).integrable one_le_two)).eventuallyEq

end Wiener

end Gardiner.Ito
