/-
# The Itô integral of a general nonanticipating integrand (Gardiner §4.2.1, §4.2.4, §4.2.6)

For an Itô integrand `G` on `[0, T]` (`Gardiner.Ito.IsItoIntegrand`) and a Wiener process `W` with
respect to `𝓕` (`Gardiner.Ito.IsFWiener`), `Gardiner.Ito.itoInt W 𝓕 P T G` is the Itô integral
`∫₀ᵀ G(t') dW(t')`: the extension by continuity of the elementary integral, which is an isometry
from elementary integrands (norm `⟨∫₀ᵀ G² dt⟩^{1/2}`) into `L²(P)`, to their closure, which by
`Gardiner.Ito.exists_elem_approx` contains every Itô integrand.  Concretely it is the conditional
expectation onto `𝓕 T` of the mean-square limit of the elementary integrals of a fixed
approximating sequence, so that it is exactly (not only a.e.) `𝓕 T`-measurable.

* `itoInt_sub_sq`: `⟨(∫ H dW - ∫ G dW)²⟩ = ⟨∫₀ᵀ (H - G)² dt⟩` for every elementary `H`; hence
  every approximating sequence of elementary integrals converges to `∫ G dW` in mean square
  (`itoInt_tendsto`), and `∫ H dW` agrees with the elementary integral (`itoInt_elem`);
* linearity (`itoInt_add`, `itoInt_const_mul`, `itoInt_sub`);
* (4.2.40) mean value `⟨∫ G dW⟩ = 0` (`itoInt_mean`);
* (4.2.42) correlation formula `⟨∫ G dW ∫ H dW⟩ = ∫₀ᵀ dt ⟨G(t)H(t)⟩` (`itoInt_mul`,
  `itoInt_mul_iter`, `itoInt_sq`);
* martingale property of `t ↦ ∫₀ᵗ G dW` (`itoInt_condExp`, `martingale_itoInt`).
-/
import SHSLib.Gardiner.Ito.Calculus.Density

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- A fixed sequence of elementary integrands approximating `G` on `[0, T]` to within `1/(k+1)`
(in squared norm). -/
def approxSeq (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ) (G : ℝ → Ω → ℝ) (k : ℕ) :
    Σ n, ElemIntegrand 𝓕 P (Fin n) :=
  open Classical in
  if h : IsFiniteMeasure P ∧ IsItoIntegrand 𝓕 P T G then
    (@exists_elem_approx Ω mΩ 𝓕 P h.1 T G h.2 (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat).choose
  else ⟨0, ElemIntegrand.zero⟩

lemma approxSeq_spec [hP : IsFiniteMeasure P] {T : ℝ} {G : ℝ → Ω → ℝ}
    (hG : IsItoIntegrand 𝓕 P T G) (k : ℕ) :
    (approxSeq 𝓕 P T G k).2.SupportedIn T ∧
      ∫ p, (Function.uncurry (approxSeq 𝓕 P T G k).2.process p - Function.uncurry G p) ^ 2
        ∂(tsMeasure P T) < 1 / ((k : ℝ) + 1) := by
  rw [approxSeq, dif_pos ⟨hP, hG⟩]
  exact (@exists_elem_approx Ω mΩ 𝓕 P hP T G hG (1 / ((k : ℝ) + 1))
    Nat.one_div_pos_of_nat).choose_spec

/-- **The Itô integral** `∫₀ᵀ G(t') dW(t')` of an Itô integrand (Gardiner (4.2.8)–(4.2.10),
§4.2.6). -/
def itoInt (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ) (G : ℝ → Ω → ℝ) :
    Ω → ℝ :=
  P[l2Lim (fun k => (approxSeq 𝓕 P T G k).2.integral W) P | 𝓕 T]

namespace ElemIntegrand

variable {ι : Type*} [Fintype ι]

/-- The elementary integral of an integrand supported in `(0, T]` is `𝓕 T`-measurable. -/
lemma integral_sm {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) (H : ElemIntegrand 𝓕 P ι) {T : ℝ}
    (hH : H.SupportedIn T) : StronglyMeasurable[𝓕 T] (H.integral W) := by
  rw [← H.running_eq_integral W hH]
  exact (H.martingale_running hW).1 T

end ElemIntegrand

lemma tendsto_of_lt_one_div {f : ℕ → ℝ} (h0 : ∀ k, 0 ≤ f k) (h : ∀ k, f k < 1 / ((k : ℝ) + 1)) :
    Tendsto f atTop (𝓝 0) :=
  squeeze_zero h0 (fun k => (h k).le) tendsto_one_div_add_atTop_nhds_zero_nat


lemma ae_eq_zero_of_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 P) (h : ∫ ω, f ω ^ 2 ∂P = 0) :
    f =ᵐ[P] 0 := by
  have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (f ω)) hf.integrable_sq).mp h
  filter_upwards [this] with ω hω
  simpa using hω


/-- Mean-square convergence of sums. -/
lemma l2_tendsto_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {X Y : ℕ → α → ℝ}
    {X' Y' : α → ℝ} (hX : ∀ n, MemLp (X n) 2 μ) (hY : ∀ n, MemLp (Y n) 2 μ) (hX' : MemLp X' 2 μ)
    (hY' : MemLp Y' 2 μ) (h1 : Tendsto (fun n => ∫ a, (X n a - X' a) ^ 2 ∂μ) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫ a, (Y n a - Y' a) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, ((X n a + Y n a) - (X' a + Y' a)) ^ 2 ∂μ) atTop (𝓝 0) := by
  have h := (l2_tendsto_toLp hX hX' h1).add (l2_tendsto_toLp hY hY' h2)
  simp only [← MemLp.toLp_add] at h
  exact l2_tendsto_of_toLp (fun n => (hX n).add (hY n)) (hX'.add hY') h

lemma l2_tendsto_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : ℕ → α → ℝ}
    {X' : α → ℝ} (c : ℝ)
    (h1 : Tendsto (fun n => ∫ a, (X n a - X' a) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, (c * X n a - c * X' a) ^ 2 ∂μ) atTop (𝓝 0) := by
  have h := h1.const_mul (c ^ 2)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [← integral_const_mul]; congr 1; funext a; ring

section Main

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) {T : ℝ} {G : ℝ → Ω → ℝ}
include hW

/-- The approximating elementary integrals converge in mean square to `itoInt`, which is
`𝓕 T`-measurable, square integrable, and satisfies the isometry against every elementary
integrand. -/
theorem itoInt_spec (hG : IsItoIntegrand 𝓕 P T G) :
    MemLp (itoInt W 𝓕 P T G) 2 P ∧ StronglyMeasurable[𝓕 T] (itoInt W 𝓕 P T G) ∧
    (∀ (ι : Type) [Fintype ι] (H : ElemIntegrand 𝓕 P ι), H.SupportedIn T →
      ∫ ω, (H.integral W ω - itoInt W 𝓕 P T G ω) ^ 2 ∂P =
        ∫ p, (Function.uncurry H.process p - Function.uncurry G p) ^ 2 ∂(tsMeasure P T)) := by
  have := hW.isProbabilityMeasure
  set A := approxSeq 𝓕 P T G with hA
  have hAs := fun k => (approxSeq_spec hG k).1
  have hAd := fun k => (approxSeq_spec hG k).2
  set I : ℕ → Ω → ℝ := fun k => (A k).2.integral W with hI
  have hIm : ∀ k, MemLp (I k) 2 P := fun k => (A k).2.memLp_integral hW
  have hpm : ∀ k, MemLp (Function.uncurry (A k).2.process) 2 (tsMeasure P T) :=
    fun k => (A k).2.memLp_process T
  set pL : ℕ → Lp ℝ 2 (tsMeasure P T) := fun k => (hpm k).toLp _ with hpL
  set gL := hG.memLp.toLp _ with hgL
  set JL : ℕ → Lp ℝ 2 P := fun k => (hIm k).toLp _ with hJL
  -- `pL → gL`
  have hp : Tendsto pL atTop (𝓝 gL) := l2_tendsto_toLp hpm hG.memLp
    (tendsto_of_lt_one_div (fun k => integral_nonneg fun _ => sq_nonneg _) hAd)
  -- isometry between the sequences
  have hiso : ∀ k m, ‖JL k - JL m‖ = ‖pL k - pL m‖ := fun k m => by
    have h1 := l2_norm_toLp_sub_sq (hIm k) (hIm m)
    have h2 := l2_norm_toLp_sub_sq (hpm k) (hpm m)
    have h3 := (A k).2.integral_sub_sq_ts hW (A m).2 (hAs k) (hAs m)
    have : ‖JL k - JL m‖ ^ 2 = ‖pL k - pL m‖ ^ 2 := by
      simp only [hJL, hpL]; rw [h1, h2]; exact h3
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
  have hJc : CauchySeq JL := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hp.cauchySeq ε hε
    exact ⟨N, fun m hm n hn => by rw [dist_eq_norm, hiso, ← dist_eq_norm]; exact hN m hm n hn⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hJc
  -- the mean-square limit
  have hLm : MemLp (⇑L) 2 P := Lp.memLp L
  have hIL : Tendsto (fun k => ∫ ω, (I k ω - L ω) ^ 2 ∂P) atTop (𝓝 0) := by
    refine l2_tendsto_of_toLp hIm hLm ?_
    rw [Lp.toLp_coeFn]; exact hL
  obtain ⟨hYm, hYt⟩ := l2Lim_spec hLm hIL
  set Y := l2Lim I P with hY
  -- `itoInt = Y` a.e.
  have hae : itoInt W 𝓕 P T G =ᵐ[P] Y := by
    refine condExp_eq_of_tendsto_l1 T (fun k => (A k).2.integral_sm hW (hAs k))
      (fun k => (hIm k).integrable one_le_two) (hYm.integrable one_le_two) ?_
    exact tendsto_integral_abs_of_l2 hIm hYm hYt
  have hYL : hYm.toLp Y = L := by
    refine tendsto_nhds_unique (l2_tendsto_toLp hIm hYm hYt) ?_
    exact hL
  refine ⟨hYm.ae_eq hae.symm, stronglyMeasurable_condExp, fun ι _ H hH => ?_⟩
  have hHm := H.memLp_integral hW
  have hHp := H.memLp_process (P := P) T
  have hcongr : ∫ ω, (H.integral W ω - itoInt W 𝓕 P T G ω) ^ 2 ∂P =
      ∫ ω, (H.integral W ω - Y ω) ^ 2 ∂P :=
    integral_congr_ae (hae.mono fun ω hω => by simp only [hω])
  rw [hcongr]
  rw [← l2_norm_toLp_sub_sq hHm hYm, ← l2_norm_toLp_sub_sq hHp hG.memLp, hYL]
  congr 1
  -- both sides are limits of the same sequence
  have h1 : Tendsto (fun k => ‖hHm.toLp _ - JL k‖) atTop (𝓝 ‖hHm.toLp _ - L‖) :=
    (tendsto_const_nhds.sub hL).norm
  have h2 : Tendsto (fun k => ‖hHp.toLp _ - pL k‖) atTop (𝓝 ‖hHp.toLp _ - gL‖) :=
    (tendsto_const_nhds.sub hp).norm
  refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
  have e1 := l2_norm_toLp_sub_sq hHm (hIm k)
  have e2 := l2_norm_toLp_sub_sq hHp (hpm k)
  have e3 := H.integral_sub_sq_ts hW (A k).2 hH (hAs k)
  have : ‖hHp.toLp _ - pL k‖ ^ 2 = ‖hHm.toLp _ - JL k‖ ^ 2 := by
    simp only [hJL, hpL]; rw [e1, e2]; exact e3.symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

theorem memLp_itoInt (hG : IsItoIntegrand 𝓕 P T G) : MemLp (itoInt W 𝓕 P T G) 2 P :=
  (itoInt_spec hW hG).1

/-- `∫₀ᵀ G dW` is `𝓕 T`-measurable. -/
theorem itoInt_stronglyMeasurable (hG : IsItoIntegrand 𝓕 P T G) :
    StronglyMeasurable[𝓕 T] (itoInt W 𝓕 P T G) :=
  (itoInt_spec hW hG).2.1

/-- **The isometry against elementary integrands**:
`⟨(∫ H dW - ∫ G dW)²⟩ = ⟨∫₀ᵀ (H - G)² dt⟩`. -/
theorem itoInt_sub_sq (hG : IsItoIntegrand 𝓕 P T G) {ι : Type} [Fintype ι]
    (H : ElemIntegrand 𝓕 P ι) (hH : H.SupportedIn T) :
    ∫ ω, (H.integral W ω - itoInt W 𝓕 P T G ω) ^ 2 ∂P =
      ∫ p, (Function.uncurry H.process p - Function.uncurry G p) ^ 2 ∂(tsMeasure P T) :=
  (itoInt_spec hW hG).2.2 ι H hH

/-- Any sequence of elementary integrands converging to `G` gives elementary integrals
converging to `∫ G dW` in mean square. -/
theorem itoInt_tendsto (hG : IsItoIntegrand 𝓕 P T G) {ι : ℕ → Type} [∀ k, Fintype (ι k)]
    (H : ∀ k, ElemIntegrand 𝓕 P (ι k)) (hH : ∀ k, (H k).SupportedIn T)
    (hconv : Tendsto (fun k => ∫ p, (Function.uncurry (H k).process p -
      Function.uncurry G p) ^ 2 ∂(tsMeasure P T)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, ((H k).integral W ω - itoInt W 𝓕 P T G ω) ^ 2 ∂P) atTop (𝓝 0) :=
  hconv.congr fun k => (itoInt_sub_sq hW hG (H k) (hH k)).symm

/-- **The Itô integral of an elementary integrand is its elementary integral.** -/
theorem itoInt_elem {ι : Type} [Fintype ι] (H : ElemIntegrand 𝓕 P ι) (hH : H.SupportedIn T) :
    itoInt W 𝓕 P T H.process =ᵐ[P] H.integral W := by
  have := hW.isProbabilityMeasure
  have hG := H.isItoIntegrand (P := P) T
  have h := itoInt_sub_sq hW hG H hH
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integral_zero] at h
  have := ae_eq_zero_of_integral_sq ((H.memLp_integral hW).sub (memLp_itoInt hW hG)) h
  filter_upwards [this] with ω hω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hω
  exact hω.symm

/-- The approximating sequence converges to the Itô integral in mean square. -/
lemma approxSeq_tendsto (hG : IsItoIntegrand 𝓕 P T G) :
    Tendsto (fun k => ∫ ω, ((approxSeq 𝓕 P T G k).2.integral W ω - itoInt W 𝓕 P T G ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  exact itoInt_tendsto hW hG (fun k => (approxSeq 𝓕 P T G k).2)
    (fun k => (approxSeq_spec hG k).1)
    (tendsto_of_lt_one_div (fun k => integral_nonneg fun _ => sq_nonneg _)
      (fun k => (approxSeq_spec hG k).2))

lemma approxSeq_tendsto_ts (hG : IsItoIntegrand 𝓕 P T G) :
    Tendsto (fun k => ∫ p, (Function.uncurry (approxSeq 𝓕 P T G k).2.process p -
      Function.uncurry G p) ^ 2 ∂(tsMeasure P T)) atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  exact tendsto_of_lt_one_div (fun k => integral_nonneg fun _ => sq_nonneg _)
    (fun k => (approxSeq_spec hG k).2)

/-- **(4.2.40): the mean value of the Itô integral vanishes**, `⟨∫₀ᵀ G dW⟩ = 0`. -/
theorem itoInt_mean (hG : IsItoIntegrand 𝓕 P T G) : ∫ ω, itoInt W 𝓕 P T G ω ∂P = 0 := by
  have := hW.isProbabilityMeasure
  have h := l2_tendsto_integral (fun k => (approxSeq 𝓕 P T G k).2.memLp_integral hW)
    (memLp_itoInt hW hG) (approxSeq_tendsto hW hG)
  simp only [ElemIntegrand.integral_mean hW] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **(4.2.42): the correlation formula**, time–space form:
`⟨∫₀ᵀ G dW ∫₀ᵀ H dW⟩ = ∫ G H d(tsMeasure P T)`. -/
theorem itoInt_mul {K : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) (hK : IsItoIntegrand 𝓕 P T K) :
    ∫ ω, itoInt W 𝓕 P T G ω * itoInt W 𝓕 P T K ω ∂P =
      ∫ p, Function.uncurry G p * Function.uncurry K p ∂(tsMeasure P T) := by
  have := hW.isProbabilityMeasure
  have h1 := l2_tendsto_integral_mul (fun k => (approxSeq 𝓕 P T G k).2.memLp_integral hW)
    (fun k => (approxSeq 𝓕 P T K k).2.memLp_integral hW) (memLp_itoInt hW hG)
    (memLp_itoInt hW hK) (approxSeq_tendsto hW hG) (approxSeq_tendsto hW hK)
  have h2 := l2_tendsto_integral_mul (fun k => (approxSeq 𝓕 P T G k).2.memLp_process T)
    (fun k => (approxSeq 𝓕 P T K k).2.memLp_process T) hG.memLp hK.memLp
    (approxSeq_tendsto_ts hW hG) (approxSeq_tendsto_ts hW hK)
  refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
  exact ((approxSeq 𝓕 P T G k).2.integral_mul_ts hW (approxSeq 𝓕 P T K k).2
    (approxSeq_spec hG k).1).symm

/-- **(4.2.42): the correlation formula**, `⟨∫₀ᵀ G dW ∫₀ᵀ H dW⟩ = ∫₀ᵀ dt ⟨G(t) H(t)⟩`. -/
theorem itoInt_mul_iter {K : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G)
    (hK : IsItoIntegrand 𝓕 P T K) :
    ∫ ω, itoInt W 𝓕 P T G ω * itoInt W 𝓕 P T K ω ∂P =
      ∫ t in Set.Ioc 0 T, ∫ ω, G t ω * K t ω ∂P := by
  have := hW.isProbabilityMeasure
  rw [itoInt_mul hW hG hK]
  have hint : Integrable (fun p => Function.uncurry G p * Function.uncurry K p)
      (tsMeasure P T) := hG.memLp.integrable_mul hK.memLp
  unfold tsMeasure at hint ⊢
  rw [integral_prod _ hint]
  rfl

/-- **The Itô isometry**, `⟨(∫₀ᵀ G dW)²⟩ = ∫₀ᵀ dt ⟨G(t)²⟩`. -/
theorem itoInt_sq (hG : IsItoIntegrand 𝓕 P T G) :
    ∫ ω, itoInt W 𝓕 P T G ω ^ 2 ∂P = ∫ t in Set.Ioc 0 T, ∫ ω, G t ω ^ 2 ∂P := by
  simp_rw [sq]; exact itoInt_mul_iter hW hG hG

/-! ### Linearity -/

/-- **Linearity**: `∫ (G + K) dW = ∫ G dW + ∫ K dW` a.s. -/
theorem itoInt_add {K : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) (hK : IsItoIntegrand 𝓕 P T K) :
    itoInt W 𝓕 P T (fun t ω => G t ω + K t ω) =ᵐ[P]
      fun ω => itoInt W 𝓕 P T G ω + itoInt W 𝓕 P T K ω := by
  have := hW.isProbabilityMeasure
  set A := approxSeq 𝓕 P T G
  set B := approxSeq 𝓕 P T K
  have hGK := hG.add hK
  have hts := l2_tendsto_add (fun k => (A k).2.memLp_process T) (fun k => (B k).2.memLp_process T)
    hG.memLp hK.memLp (approxSeq_tendsto_ts hW hG) (approxSeq_tendsto_ts hW hK)
  have h1 := itoInt_tendsto hW hGK (fun k => (A k).2.add (B k).2)
    (fun k => by
      intro i
      cases i with
      | inl i => exact (approxSeq_spec hG k).1 i
      | inr i => exact (approxSeq_spec hK k).1 i)
    (by simpa using hts)
  have h2 := l2_tendsto_add (fun k => (A k).2.memLp_integral hW)
    (fun k => (B k).2.memLp_integral hW) (memLp_itoInt hW hG) (memLp_itoInt hW hK)
    (approxSeq_tendsto hW hG) (approxSeq_tendsto hW hK)
  simp only [ElemIntegrand.integral_add] at h1
  exact l2_ae_unique (fun k => ((A k).2.memLp_integral hW).add ((B k).2.memLp_integral hW))
    (memLp_itoInt hW hGK) ((memLp_itoInt hW hG).add (memLp_itoInt hW hK)) h1 h2

/-- **Linearity**: `∫ c G dW = c ∫ G dW` a.s. -/
theorem itoInt_const_mul (hG : IsItoIntegrand 𝓕 P T G) (c : ℝ) :
    itoInt W 𝓕 P T (fun t ω => c * G t ω) =ᵐ[P] fun ω => c * itoInt W 𝓕 P T G ω := by
  have := hW.isProbabilityMeasure
  set A := approxSeq 𝓕 P T G
  have hcG := hG.const_mul c
  have hts := l2_tendsto_const_mul c
    (approxSeq_tendsto_ts hW hG)
  have h1 := itoInt_tendsto hW hcG (fun k => (A k).2.smul c) (fun k => (approxSeq_spec hG k).1)
    (by simpa using hts)
  have h2 := l2_tendsto_const_mul c
    (approxSeq_tendsto hW hG)
  simp only [ElemIntegrand.integral_smul] at h1
  exact l2_ae_unique (fun k => ((A k).2.memLp_integral hW).const_mul c)
    (memLp_itoInt hW hcG) ((memLp_itoInt hW hG).const_mul c) h1 h2

/-- **Linearity**: `∫ (G - K) dW = ∫ G dW - ∫ K dW` a.s. -/
theorem itoInt_sub {K : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) (hK : IsItoIntegrand 𝓕 P T K) :
    itoInt W 𝓕 P T (fun t ω => G t ω - K t ω) =ᵐ[P]
      fun ω => itoInt W 𝓕 P T G ω - itoInt W 𝓕 P T K ω := by
  have e : (fun t ω => G t ω - K t ω) = fun t ω => G t ω + (-1) * K t ω := by
    funext t ω; ring
  rw [e]
  filter_upwards [itoInt_add hW hG (hK.const_mul (-1)), itoInt_const_mul hW hK (-1)] with ω h1 h2
  rw [h1, h2]; ring

/-- Integrands that agree almost everywhere on `(0, T] × Ω` have the same Itô integral. -/
theorem itoInt_congr {K : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) (hK : IsItoIntegrand 𝓕 P T K)
    (h : Function.uncurry G =ᵐ[tsMeasure P T] Function.uncurry K) :
    itoInt W 𝓕 P T G =ᵐ[P] itoInt W 𝓕 P T K := by
  have := hW.isProbabilityMeasure
  have hsq := itoInt_sq hW (hG.sub hK)
  have h0 : ∫ t in Set.Ioc 0 T, ∫ ω, (G t ω - K t ω) ^ 2 ∂P = 0 := by
    rw [← integral_sq_tsMeasure (hG.sub hK).memLp]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h] with p hp
    simp only [Function.uncurry] at hp ⊢
    rw [hp, sub_self]; simp
  rw [h0] at hsq
  have := ae_eq_zero_of_integral_sq (memLp_itoInt hW (hG.sub hK)) hsq
  filter_upwards [this, itoInt_sub hW hG hK] with ω h1 h2
  simp only [Pi.zero_apply] at h1
  rw [h1] at h2
  linarith

end Main

end Gardiner.Ito
