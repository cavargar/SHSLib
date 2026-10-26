/-
# The Wiener integral of deterministic functions (Gardiner §4.2.1, §4.2.6)

For `f : ℝ → ℝ` and `0 ≤ a ≤ b`, `Gardiner.Ito.wienerInt W P f a b = ∫ₐᵇ f(s) dW(s)` is the
mean-square limit of the left-point Riemann sums `Σᵢ f(tᵢ)(W(tᵢ₊₁) - W(tᵢ))` on the uniform
partitions of `[a, b]` (`Gardiner.Ito.riemannSum`, (4.2.8) with `τᵢ = tᵢ₋₁`).  Each Riemann sum is
the simple integral of a deterministic simple integrand (`Gardiner.Ito.riemannSum_eq`).  For
continuous `f`:

* the limit exists (`Gardiner.Ito.IsWiener.wienerInt_spec`);
* mean zero (4.2.40) and covariance `⟨∫ₐᵇ f dW ∫_c^d g dW⟩ = ∫ f g 1_{(a,b]∩(c,d]}`, in particular
  `∫ₐ^{min(b,d)} f g` for a common left endpoint and the isometry `⟨(∫ₐᵇ f dW)²⟩ = ∫ₐᵇ f²`
  (`Gardiner.Ito.IsWiener.wienerInt_mean`, `…wienerInt_mul`, `…wienerInt_mul_same`,
  `…wienerInt_sq`);
* Gaussian: `∫ₐᵇ f dW ~ N(0, ∫ₐᵇ f²)` (`Gardiner.Ito.IsWiener.wienerInt_map`), and pairs on a
  common interval are jointly Gaussian (`Gardiner.Ito.IsWiener.wienerInt_hasGaussianLaw_pair`,
  from `Gardiner.Ito.hasGaussianLaw_pair`);
* linear (`Gardiner.Ito.IsWiener.wienerInt_add_smul`, `…wienerInt_lin_ae`), and `∫ₐᵇ dW = W(b) - W(a)`
  (`Gardiner.Ito.IsWiener.wienerInt_one`);
* **integration by parts** for `C¹` `f`: `∫ₐᵇ f dW = f(b)W(b) - f(a)W(a) - ∫ₐᵇ f'(s)W(s) ds`
  almost surely, linking the integral to the pathwise layer (`Gardiner.Ito.IsWiener.wienerInt_ibp`).

For step functions the same definition gives the simple integral
(`SHSLib.Gardiner.Ito.WienerStep`).  Instances for `stdWiener`: `SHSLib.Gardiner.Ito.WienerInstances`.
-/
import SHSLib.Gardiner.Ito.MSLimit

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

/-! ### Cells of a partition -/

lemma exists_cell {p : ℕ → ℝ} {N : ℕ} {s : ℝ} (hs : s ∈ Set.Ioc (p 0) (p N)) :
    ∃ i < N, s ∈ Set.Ioc (p i) (p (i + 1)) := by
  induction N with
  | zero => exact absurd hs.2 (not_le.mpr hs.1)
  | succ N ih =>
    by_cases h : s ≤ p N
    · obtain ⟨i, hi, hs'⟩ := ih ⟨hs.1, h⟩
      exact ⟨i, Nat.lt_succ_of_lt hi, hs'⟩
    · exact ⟨N, Nat.lt_succ_self N, not_le.mp h, hs.2⟩

lemma sum_ind_eq {p : ℕ → ℝ} (hp : Monotone p) {N i₀ : ℕ} (hi₀ : i₀ < N) {s : ℝ}
    (hs : s ∈ Set.Ioc (p i₀) (p (i₀ + 1))) (c : ℕ → ℝ) :
    ∑ i ∈ range N, c i * ind (p i) (p (i + 1)) s = c i₀ := by
  rw [Finset.sum_eq_single i₀]
  · simp [ind, Set.indicator_of_mem hs]
  · intro j _ hj
    have : s ∉ Set.Ioc (p j) (p (j + 1)) := by
      rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have := hp (Nat.succ_le_of_lt hlt); linarith [hs.1]
      · have := hp (Nat.succ_le_of_lt hgt); linarith [hs.2]
    simp [ind, Set.indicator_of_notMem this]
  · intro h; exact absurd (mem_range.mpr hi₀) h

lemma sum_ind_eq_zero {p : ℕ → ℝ} (hp : Monotone p) {N : ℕ} {s : ℝ}
    (hs : s ∉ Set.Ioc (p 0) (p N)) (c : ℕ → ℝ) :
    ∑ i ∈ range N, c i * ind (p i) (p (i + 1)) s = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have : s ∉ Set.Ioc (p i) (p (i + 1)) := by
    rintro ⟨h1, h2⟩
    have h3 := hp (Nat.zero_le i)
    have h4 := hp (Nat.succ_le_of_lt (mem_range.mp hi))
    exact hs ⟨by linarith, by linarith⟩
  simp [ind, Set.indicator_of_notMem this]

/-! ### Uniform partitions -/

/-- The uniform partition of `[a, b]` into `n + 1` cells. -/
abbrev grid (a b : ℝ) (n : ℕ) : ℕ → ℝ := unifPart a b (n + 1)

lemma grid_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) : Monotone (grid a b n) :=
  (isPartition_unifPart hab n.succ_pos).mono

lemma grid_zero (a b : ℝ) (n : ℕ) : grid a b n 0 = a := by simp [grid, unifPart]

lemma grid_last' {a b : ℝ} (n : ℕ) : grid a b n (n + 1) = b := by
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [grid, unifPart]; field_simp; ring

lemma grid_step (a b : ℝ) (n i : ℕ) : grid a b n (i + 1) - grid a b n i = (b - a) / (n + 1) := by
  simp only [grid, unifPart]; push_cast; ring

lemma grid_mem {a b : ℝ} (hab : a ≤ b) {n i : ℕ} (hi : i ≤ n + 1) :
    grid a b n i ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · have := grid_mono hab n (Nat.zero_le i); rwa [grid_zero] at this
  · have := grid_mono hab n hi; rwa [grid_last'] at this

/-- **Uniform continuity on the cells**: for `g` continuous on `[a, b]` and `n` large, `g`
oscillates by at most `ε` on every cell of the uniform partition. -/
lemma cells_osc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Set.Icc a b)) {ε : ℝ}
    (hε : 0 < ε) : ∃ N, ∀ n ≥ N, ∀ i < n + 1, ∀ s ∈ Set.Icc (grid a b n i) (grid a b n (i + 1)),
      ∀ s' ∈ Set.Icc (grid a b n i) (grid a b n (i + 1)), |g s - g s'| ≤ ε := by
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc).uniformContinuousOn_of_continuous hg) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N, fun n hn i hi s hs s' hs' => ?_⟩
  have hi1 := grid_mem hab (n := n) hi.le
  have hi2 := grid_mem hab (n := n) (Nat.succ_le_of_lt hi)
  have hsI : s ∈ Set.Icc a b := ⟨hi1.1.trans hs.1, hs.2.trans hi2.2⟩
  have hs'I : s' ∈ Set.Icc a b := ⟨hi1.1.trans hs'.1, hs'.2.trans hi2.2⟩
  have hstep := grid_step a b n i
  have hh : (b - a) / (n + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hd : dist s s' < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2, hs'.1, hs'.2]
  exact (le_of_lt (by simpa [Real.dist_eq] using hδg s hsI s' hs'I hd))

/-! ### Step approximations and Riemann sums -/

/-- The left-point step approximation of `f` on the uniform partition of `[a, b]`,
`fₙ(s) = Σᵢ f(tᵢ) 1_{(tᵢ, tᵢ₊₁]}(s)`. -/
def stepFn (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), f (grid a b n i) * ind (grid a b n i) (grid a b n (i + 1)) s

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- The left-point Riemann sum `Σᵢ f(tᵢ)(W(tᵢ₊₁) - W(tᵢ))` on the uniform partition of `[a, b]`
into `n + 1` cells (Gardiner (4.2.8) with `τᵢ = tᵢ₋₁`). -/
def riemannSum (W : ℝ → Ω → ℝ) (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range (n + 1), f (grid a b n i) * (W (grid a b n (i + 1)) ω - W (grid a b n i) ω)

lemma ind_mem {a b s : ℝ} (hs : s ∈ Set.Ioc a b) : ind a b s = 1 := by
  simp [ind, Set.indicator_of_mem hs]

lemma ind_notMem {a b s : ℝ} (hs : s ∉ Set.Ioc a b) : ind a b s = 0 := by
  simp [ind, Set.indicator_of_notMem hs]

lemma ind_nonneg (a b s : ℝ) : 0 ≤ ind a b s := by
  by_cases hs : s ∈ Set.Ioc a b
  · rw [ind_mem hs]; exact zero_le_one
  · rw [ind_notMem hs]

lemma ind_le_one (a b s : ℝ) : ind a b s ≤ 1 := by
  by_cases hs : s ∈ Set.Ioc a b
  · rw [ind_mem hs]
  · rw [ind_notMem hs]; exact zero_le_one

lemma measurable_ind (a b : ℝ) : Measurable (ind a b) :=
  measurable_const.indicator measurableSet_Ioc

lemma integrable_ind (a b : ℝ) : Integrable (ind a b) := by
  have := integrable_ind_mul_ind a b a b
  refine this.congr (Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Set.Ioc a b
  · simp [ind_mem hs]
  · simp [ind_notMem hs]

lemma integral_ind {a b : ℝ} (hab : a ≤ b) : ∫ s, ind a b s = b - a := by
  have := integral_ind_mul_ind a b a b
  rw [overlap, max_self, min_self, max_eq_left (by linarith)] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Set.Ioc a b
  · simp [ind_mem hs]
  · simp [ind_notMem hs]

/-- **The step approximation converges uniformly**: for continuous `f` and large `n`,
`|fₙ(s) - f(s) 1_{(a,b]}(s)| ≤ ε 1_{(a,b]}(s)` for every `s`. -/
lemma stepFn_approx {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) {ε : ℝ}
    (hε : 0 < ε) : ∃ N, ∀ n ≥ N, ∀ s, |stepFn f a b n s - f s * ind a b s| ≤ ε * ind a b s := by
  obtain ⟨N, hN⟩ := cells_osc hab hf.continuousOn hε
  refine ⟨N, fun n hn s => ?_⟩
  by_cases hs : s ∈ Set.Ioc a b
  · have hs' : s ∈ Set.Ioc (grid a b n 0) (grid a b n (n + 1)) := by
      rwa [grid_zero, grid_last']
    obtain ⟨i, hi, hsi⟩ := exists_cell hs'
    rw [stepFn, sum_ind_eq (grid_mono hab n) hi hsi, ind_mem hs, mul_one, mul_one]
    exact hN n hn i hi _ ⟨le_rfl, (grid_mono hab n (Nat.le_succ i))⟩ s ⟨hsi.1.le, hsi.2⟩
  · have hs' : s ∉ Set.Ioc (grid a b n 0) (grid a b n (n + 1)) := by
      rwa [grid_zero, grid_last']
    rw [stepFn, sum_ind_eq_zero (grid_mono hab n) hs', ind_notMem hs]
    simp

lemma measurable_stepFn (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : Measurable (stepFn f a b n) :=
  Finset.measurable_fun_sum _ fun _ _ => (measurable_ind _ _).const_mul _

lemma integrable_stepFn_mul (f g : ℝ → ℝ) (a b c d : ℝ) (n m : ℕ) :
    Integrable (fun s => stepFn f a b n s * stepFn g c d m s) := by
  simp only [stepFn, Finset.sum_mul_sum]
  refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => ?_
  have := (integrable_ind_mul_ind (grid a b n i) (grid a b n (i + 1)) (grid c d m j)
    (grid c d m (j + 1))).const_mul (f (grid a b n i) * g (grid c d m j))
  refine this.congr (Eventually.of_forall fun s => ?_)
  simp only; ring

lemma memLp_ind (a b : ℝ) : MemLp (ind a b) 2 (volume : Measure ℝ) :=
  memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr (by simp [Real.volume_Ioc]))

lemma memLp_stepFn (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    MemLp (stepFn f a b n) 2 (volume : Measure ℝ) := by
  have := memLp_finset_sum' (range (n + 1)) fun i _ =>
    (memLp_ind (grid a b n i) (grid a b n (i + 1))).const_mul (f (grid a b n i))
  convert this using 1
  funext s; simp [stepFn]

/-- `f 1_{(a,b]}` is square integrable for continuous `f`. -/
lemma memLp_cut {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    MemLp (fun s => f s * ind a b s) 2 (volume : Measure ℝ) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_le ((memLp_ind a b).const_mul M)
    (hf.measurable.mul (measurable_ind a b)).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Set.Ioc a b
  · have := hM s ⟨hs.1.le, hs.2⟩
    simp only [ind_mem hs, mul_one, Real.norm_eq_abs] at this ⊢
    exact this.trans (le_abs_self M)
  · simp [ind_notMem hs]

/-- `fₙ → f 1_{(a,b]}` in `L²(ds)`. -/
lemma stepFn_ms {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => ∫ s, (stepFn f a b n s - f s * ind a b s) ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := Real.sqrt (ε / (2 * (b - a + 1))) with hδ
  have hba : 0 < b - a + 1 := by linarith
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨N, hN⟩ := stepFn_approx hf hab hδ0
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun s => sq_nonneg _)]
  have hb : ∀ s, (stepFn f a b n s - f s * ind a b s) ^ 2 ≤ δ ^ 2 * ind a b s := by
    intro s
    have h1 := hN n hn s
    have h2 := ind_nonneg a b s
    have h3 := ind_le_one a b s
    calc (stepFn f a b n s - f s * ind a b s) ^ 2 = |stepFn f a b n s - f s * ind a b s| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (δ * ind a b s) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ δ ^ 2 * ind a b s := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  calc ∫ s, (stepFn f a b n s - f s * ind a b s) ^ 2
      ≤ ∫ s, δ ^ 2 * ind a b s :=
        integral_mono_of_nonneg (Eventually.of_forall fun s => sq_nonneg _)
          ((integrable_ind a b).const_mul _) (Eventually.of_forall hb)
    _ = δ ^ 2 * (b - a) := by rw [integral_const_mul, integral_ind hab]
    _ < ε := by
        rw [hδ, Real.sq_sqrt (by positivity)]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-! ### Riemann sums as simple integrals -/

section Riemann

variable (hW : IsWiener W P)

/-- The deterministic simple integrand `Σᵢ f(tᵢ) 1_{(tᵢ, tᵢ₊₁]}` on the uniform partition. -/
def detSimple (f : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    SimpleIntegrand W hW.measurable P (Fin (n + 1)) where
  left i := grid a b n i
  right i := grid a b n (i + 1)
  val i := fun _ => f (grid a b n i)
  left_nonneg i := ha.trans (grid_mem hab i.isLt.le).1
  left_le_right i := grid_mono hab n (Nat.le_succ _)
  adapted _ := stronglyMeasurable_const
  memLp _ := by haveI := hW.isProbabilityMeasure; exact memLp_const _

variable {f g : ℝ → ℝ} {a b c d : ℝ}
include hW

lemma riemannSum_eq (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    riemannSum W f a b n = (detSimple hW f ha hab n).integral := by
  funext ω
  simp only [riemannSum, SimpleIntegrand.integral, detSimple]
  exact (Fin.sum_univ_eq_sum_range (fun i => f (grid a b n i) *
    (W (grid a b n (i + 1)) ω - W (grid a b n i) ω)) (n + 1)).symm

lemma process_detSimple (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) (s : ℝ) (ω : Ω) :
    (detSimple hW f ha hab n).process s ω = stepFn f a b n s := by
  simp only [SimpleIntegrand.process, detSimple, stepFn]
  exact Fin.sum_univ_eq_sum_range (fun i => f (grid a b n i) *
    ind (grid a b n i) (grid a b n (i + 1)) s) (n + 1)

lemma memLp_riemannSum (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    MemLp (riemannSum W f a b n) 2 P := by
  rw [riemannSum_eq hW ha hab]; exact SimpleIntegrand.memLp_integral hW _

/-- **The isometry for Riemann sums of deterministic functions**:
`⟨Rₙ(f; a, b) Rₘ(g; c, d)⟩ = ∫ fₙ gₘ ds`. -/
lemma riemannSum_mul (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) (n m : ℕ) :
    ∫ ω, riemannSum W f a b n ω * riemannSum W g c d m ω ∂P =
      ∫ s, stepFn f a b n s * stepFn g c d m s := by
  have := hW.isProbabilityMeasure
  rw [riemannSum_eq hW ha hab, riemannSum_eq hW hc hcd, SimpleIntegrand.integral_mul hW]
  simp [process_detSimple]

lemma riemannSum_sub_sq (ha : 0 ≤ a) (hab : a ≤ b) (n m : ℕ) :
    ∫ ω, (riemannSum W f a b n ω - riemannSum W f a b m ω) ^ 2 ∂P =
      ∫ s, (stepFn f a b n s - stepFn f a b m s) ^ 2 := by
  have := hW.isProbabilityMeasure
  set H := (detSimple hW f ha hab n).add ((detSimple hW f ha hab m).smul (-1))
  have h1 : ∀ ω, H.integral ω = riemannSum W f a b n ω - riemannSum W f a b m ω := by
    intro ω
    simp only [H, SimpleIntegrand.integral_add, SimpleIntegrand.integral_smul,
      riemannSum_eq hW ha hab, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : ∀ s ω, H.process s ω = stepFn f a b n s - stepFn f a b m s := by
    intro s ω
    simp only [H, SimpleIntegrand.process_add, SimpleIntegrand.process_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, process_detSimple]
    ring
  have := SimpleIntegrand.integral_sq hW H
  simp only [h1, h2, integral_const, probReal_univ, smul_eq_mul, one_mul] at this
  exact this

/-- The Riemann sums of a continuous function form a mean-square Cauchy sequence. -/
lemma riemannSum_cauchy (hf : Continuous f) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ ω, (riemannSum W f a b m ω - riemannSum W f a b n ω) ^ 2 ∂P < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (stepFn_ms hf hab) (ε / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [riemannSum_sub_sq hW ha hab]
  have hm' := hN m hm
  have hn' := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun s => sq_nonneg _)] at hm' hn'
  have hi : ∀ k, Integrable (fun s => (stepFn f a b k s - f s * ind a b s) ^ 2) := fun k =>
    ((memLp_stepFn f a b k).sub (memLp_cut hf a b)).integrable_sq
  have e := integral_add ((hi m).const_mul 2) ((hi n).const_mul 2)
  rw [integral_const_mul, integral_const_mul] at e
  calc ∫ s, (stepFn f a b m s - stepFn f a b n s) ^ 2
      ≤ ∫ s, (2 * (stepFn f a b m s - f s * ind a b s) ^ 2 +
          2 * (stepFn f a b n s - f s * ind a b s) ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun s => sq_nonneg _)
          (((hi m).const_mul 2).add ((hi n).const_mul 2)) (Eventually.of_forall fun s => ?_)
        nlinarith [sq_nonneg (stepFn f a b m s + stepFn f a b n s - 2 * (f s * ind a b s))]
    _ = _ := e
    _ < ε := by linarith

/-- A linear combination of Wiener increments over a partition is centred Gaussian. -/
lemma exists_gauss_sum {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (c : ℕ → ℝ) (N : ℕ) :
    ∃ v : ℝ≥0, P.map (fun ω => ∑ i ∈ range N, c i * dW W p i ω) = gaussianReal 0 v := by
  have := hW.isProbabilityMeasure
  set ξ : ℕ → Ω → ℝ := fun i ω => c i * dW W p i ω with hξ
  have hξm : ∀ i, Measurable (ξ i) := fun i => (hW.dW_measurable p i).const_mul _
  have hind : iIndepFun ξ P := (hW.dW_iIndepFun hp h0).comp (fun i x => c i * x)
    (fun i => measurable_const.mul measurable_id)
  induction N with
  | zero => exact ⟨0, by simp [Measure.map_const, gaussianReal_zero_var]⟩
  | succ N ih =>
    obtain ⟨v, hv⟩ := ih
    have hI := hind.indepFun_finset_sum_of_notMem hξm (s := range N) (i := N) (by simp)
    have hS : (fun ω => ∑ i ∈ range (N + 1), c i * dW W p i ω) = (∑ j ∈ range N, ξ j) + ξ N := by
      funext ω; simp [hξ, Finset.sum_range_succ]
    have hY : P.map (ξ N) = gaussianReal 0 (⟨c N ^ 2, sq_nonneg _⟩ *
        (p (N + 1) - p N).toNNReal) := by
      have : ξ N = (fun x => c N * x) ∘ dW W p N := rfl
      rw [this, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => c N * x)
        (hW.dW_measurable p N),
        hW.dW_map hp h0 N, gaussianReal_map_const_mul, mul_zero]
    have hsum : (∑ j ∈ range N, ξ j) = fun ω => ∑ i ∈ range N, c i * dW W p i ω := by
      funext ω; simp [hξ]
    refine ⟨v + ⟨c N ^ 2, sq_nonneg _⟩ * (p (N + 1) - p N).toNNReal, ?_⟩
    rw [hS, hI.map_add_eq_map_conv_map
      (by rw [Finset.sum_fn]; exact Finset.measurable_sum _ fun i _ => hξm i) (hξm N),
      hsum, hv, hY, gaussianReal_conv_gaussianReal, add_zero]

lemma exists_gauss_riemannSum (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    ∃ v : ℝ≥0, P.map (riemannSum W f a b n) = gaussianReal 0 v := by
  obtain ⟨v, hv⟩ := exists_gauss_sum hW (grid_mono hab n) (by rw [grid_zero]; exact ha)
    (fun i => f (grid a b n i)) (n + 1)
  exact ⟨v, by rw [← hv]; rfl⟩

end Riemann

/-! ### The Wiener integral -/

/-- **The Wiener integral** `∫ₐᵇ f(s) dW(s)` of a deterministic function: the mean-square limit of
the left-point Riemann sums on the uniform partitions of `[a, b]` (Gardiner (4.2.8), (4.2.10)).
For continuous `f` and `0 ≤ a ≤ b` the limit exists (`Gardiner.Ito.IsWiener.wienerInt_spec`). -/
def wienerInt (W : ℝ → Ω → ℝ) (P : Measure Ω) (f : ℝ → ℝ) (a b : ℝ) : Ω → ℝ :=
  msLim (riemannSum W f a b) P

lemma cut_mul_cut_eq_indicator (f g : ℝ → ℝ) (a b d s : ℝ) :
    f s * ind a b s * (g s * ind a d s) =
      (Set.Ioc a (min b d)).indicator (fun s => f s * g s) s := by
  by_cases h1 : s ∈ Set.Ioc a b <;> by_cases h2 : s ∈ Set.Ioc a d
  · have : s ∈ Set.Ioc a (min b d) := ⟨h1.1, le_min h1.2 h2.2⟩
    rw [ind_mem h1, ind_mem h2, Set.indicator_of_mem this]; ring
  · have : s ∉ Set.Ioc a (min b d) := fun h => h2 ⟨h.1, h.2.trans (min_le_right _ _)⟩
    rw [ind_notMem h2, Set.indicator_of_notMem this]; ring
  · have : s ∉ Set.Ioc a (min b d) := fun h => h1 ⟨h.1, h.2.trans (min_le_left _ _)⟩
    rw [ind_notMem h1, Set.indicator_of_notMem this]; ring
  · have : s ∉ Set.Ioc a (min b d) := fun h => h1 ⟨h.1, h.2.trans (min_le_left _ _)⟩
    rw [ind_notMem h1, Set.indicator_of_notMem this]; ring

lemma integral_cut_mul_cut {f g : ℝ → ℝ} {a b d : ℝ} (hb : a ≤ b) (hd : a ≤ d) :
    ∫ s, f s * ind a b s * (g s * ind a d s) = ∫ s in a..min b d, f s * g s := by
  simp_rw [cut_mul_cut_eq_indicator f g a b d]
  rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le (le_min hb hd)]

namespace IsWiener

variable (hW : IsWiener W P) {f g : ℝ → ℝ} {a b c d : ℝ}
include hW

/-- The Wiener integral of a continuous function exists: it is square integrable and the Riemann
sums converge to it in mean square. -/
theorem wienerInt_spec (hf : Continuous f) (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (wienerInt W P f a b) 2 P ∧
      Tendsto (fun n => ∫ ω, (riemannSum W f a b n ω - wienerInt W P f a b ω) ^ 2 ∂P) atTop
        (𝓝 0) :=
  msLim_spec (fun n => memLp_riemannSum hW ha hab n) (riemannSum_cauchy hW hf ha hab)

/-- **The mean of the Wiener integral vanishes** (4.2.40). -/
theorem wienerInt_mean (hf : Continuous f) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, wienerInt W P f a b ω ∂P = 0 := by
  have := hW.isProbabilityMeasure
  obtain ⟨h1, h2⟩ := hW.wienerInt_spec hf ha hab
  have h := tendsto_integral_of_ms (fun n => memLp_riemannSum hW ha hab n) h1 h2
  have h0 : ∀ n, ∫ ω, riemannSum W f a b n ω ∂P = 0 := fun n => by
    rw [riemannSum_eq hW ha hab]; exact SimpleIntegrand.integral_mean hW _
  simp only [h0] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **The covariance of two Wiener integrals** (Gardiner §4.4.1, via (4.2.42)):
`⟨∫ₐᵇ f dW ∫_c^d g dW⟩ = ∫ f 1_{(a,b]} g 1_{(c,d]} ds`. -/
theorem wienerInt_mul (hf : Continuous f) (hg : Continuous g) (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) :
    ∫ ω, wienerInt W P f a b ω * wienerInt W P g c d ω ∂P =
      ∫ s, f s * ind a b s * (g s * ind c d s) := by
  obtain ⟨hf1, hf2⟩ := hW.wienerInt_spec hf ha hab
  obtain ⟨hg1, hg2⟩ := hW.wienerInt_spec hg hc hcd
  have h1 := tendsto_integral_mul_of_ms (fun n => memLp_riemannSum hW ha hab n)
    (fun n => memLp_riemannSum hW hc hcd n) hf1 hg1 hf2 hg2
  have h2 := tendsto_integral_mul_of_ms (P := volume) (fun n => memLp_stepFn f a b n)
    (fun n => memLp_stepFn g c d n) (memLp_cut hf a b) (memLp_cut hg c d) (stepFn_ms hf hab)
    (stepFn_ms hg hcd)
  simp only [← riemannSum_mul hW ha hab hc hcd] at h2
  exact tendsto_nhds_unique h1 h2

/-- The covariance for a common left endpoint:
`⟨∫ₐᵇ f dW ∫ₐᵈ g dW⟩ = ∫ₐ^{min(b,d)} f g ds`. -/
theorem wienerInt_mul_same (hf : Continuous f) (hg : Continuous g) (ha : 0 ≤ a) (hab : a ≤ b)
    (had : a ≤ d) :
    ∫ ω, wienerInt W P f a b ω * wienerInt W P g a d ω ∂P = ∫ s in a..min b d, f s * g s := by
  rw [hW.wienerInt_mul hf hg ha hab ha had, integral_cut_mul_cut hab had]

/-- **The Itô isometry for the Wiener integral**: `⟨(∫ₐᵇ f dW)²⟩ = ∫ₐᵇ f² ds`. -/
theorem wienerInt_sq (hf : Continuous f) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, wienerInt W P f a b ω ^ 2 ∂P = ∫ s in a..b, f s ^ 2 := by
  have := hW.wienerInt_mul_same hf hf ha hab hab
  simp only [min_self, ← sq] at this
  exact this

lemma measurable_riemannSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    Measurable (riemannSum W f a b n) :=
  Finset.measurable_fun_sum _ fun _ _ => (hW.measurable_sub _ _).const_mul _

/-- **The Wiener integral is Gaussian**: `∫ₐᵇ f dW ~ N(0, ∫ₐᵇ f² ds)`. -/
theorem wienerInt_map (hf : Continuous f) (ha : 0 ≤ a) (hab : a ≤ b) :
    P.map (wienerInt W P f a b) = gaussianReal 0 (∫ s in a..b, f s ^ 2).toNNReal := by
  have := hW.isProbabilityMeasure
  obtain ⟨hI1, hI2⟩ := hW.wienerInt_spec hf ha hab
  choose v hv using fun n => exists_gauss_riemannSum (f := f) hW ha hab n
  have hvn : ∀ n, (v n : ℝ) = ∫ ω, riemannSum W f a b n ω * riemannSum W f a b n ω ∂P := by
    intro n
    have h := Gardiner.SDE.integral_comp_gauss (P := P) (hW.measurable_riemannSum f a b n) (hv n)
      (continuous_pow 2)
    rw [Gardiner.SDE.gauss_m2] at h
    rw [← h]; simp [sq]
  have hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (∫ s in a..b, f s ^ 2)) := by
    have h := tendsto_integral_mul_of_ms (fun n => memLp_riemannSum hW ha hab n)
      (fun n => memLp_riemannSum hW ha hab n) hI1 hI1 hI2 hI2
    simp only [← sq, hW.wienerInt_sq hf ha hab] at h
    simp only [hvn, ← sq]; exact h
  have hnn : 0 ≤ ∫ s in a..b, f s ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
  exact map_eq_gaussianReal_of_ms (fun n => memLp_riemannSum hW ha hab n) hI1 hv
    tendsto_const_nhds (by rw [Real.coe_toNNReal _ hnn]; exact hlim) hI2

/-- The mean square of a linear combination of Wiener integrals is the `L²(ds)` norm of the
corresponding combination of integrands. -/
theorem wienerInt_lin_sq {ι : Type*} [Fintype ι] (c : ι → ℝ) (F : ι → ℝ → ℝ) (A B : ι → ℝ)
    (hF : ∀ i, Continuous (F i)) (hA : ∀ i, 0 ≤ A i) (hAB : ∀ i, A i ≤ B i) :
    ∫ ω, (∑ i, c i * wienerInt W P (F i) (A i) (B i) ω) ^ 2 ∂P =
      ∫ s, (∑ i, c i * (F i s * ind (A i) (B i) s)) ^ 2 := by
  have hm : ∀ i, MemLp (wienerInt W P (F i) (A i) (B i)) 2 P := fun i =>
    (hW.wienerInt_spec (hF i) (hA i) (hAB i)).1
  simp only [sq, Finset.sum_mul_sum]
  have h1 : ∀ i j, Integrable (fun ω => c i * wienerInt W P (F i) (A i) (B i) ω *
      (c j * wienerInt W P (F j) (A j) (B j) ω)) P := fun i j =>
    ((hm i).const_mul (c i)).integrable_mul ((hm j).const_mul (c j))
  have h2 : ∀ i j, Integrable (fun s => c i * (F i s * ind (A i) (B i) s) *
      (c j * (F j s * ind (A j) (B j) s))) := fun i j =>
    ((memLp_cut (hF i) (A i) (B i)).const_mul (c i)).integrable_mul
      ((memLp_cut (hF j) (A j) (B j)).const_mul (c j))
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => h1 i j,
    integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => h2 i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => h1 i j, integral_finset_sum _ fun j _ => h2 i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (fun ω => c i * wienerInt W P (F i) (A i) (B i) ω *
      (c j * wienerInt W P (F j) (A j) (B j) ω)) = fun ω => (c i * c j) *
      (wienerInt W P (F i) (A i) (B i) ω * wienerInt W P (F j) (A j) (B j) ω) := by
    funext ω; ring
  have e2 : (fun s => c i * (F i s * ind (A i) (B i) s) * (c j * (F j s * ind (A j) (B j) s))) =
      fun s => (c i * c j) * (F i s * ind (A i) (B i) s * (F j s * ind (A j) (B j) s)) := by
    funext s; ring
  rw [e1, e2, integral_const_mul, integral_const_mul,
    hW.wienerInt_mul (hF i) (hF j) (hA i) (hAB i) (hA j) (hAB j)]

/-- **Linear relations transfer from integrands to Wiener integrals**: if
`Σᵢ cᵢ Fᵢ 1_{(Aᵢ, Bᵢ]} = 0` pointwise, then `Σᵢ cᵢ ∫_{Aᵢ}^{Bᵢ} Fᵢ dW = 0` almost surely. -/
theorem wienerInt_lin_ae {ι : Type*} [Fintype ι] (c : ι → ℝ) (F : ι → ℝ → ℝ) (A B : ι → ℝ)
    (hF : ∀ i, Continuous (F i)) (hA : ∀ i, 0 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (h : ∀ s, ∑ i, c i * (F i s * ind (A i) (B i) s) = 0) :
    (fun ω => ∑ i, c i * wienerInt W P (F i) (A i) (B i) ω) =ᵐ[P] 0 := by
  have h0 := hW.wienerInt_lin_sq c F A B hF hA hAB
  simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero] at h0
  have hm : MemLp (fun ω => ∑ i, c i * wienerInt W P (F i) (A i) (B i) ω) 2 P := by
    have := memLp_finset_sum' (Finset.univ : Finset ι) fun i _ =>
      (hW.wienerInt_spec (hF i) (hA i) (hAB i)).1.const_mul (c i)
    convert this using 1; funext ω; simp
  have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hm.integrable_sq).mp h0
  filter_upwards [this] with ω hω
  simpa using hω

/-- **Linearity of the Wiener integral**: `∫ (αf + βg) dW = α ∫ f dW + β ∫ g dW` a.s. -/
theorem wienerInt_add_smul (hf : Continuous f) (hg : Continuous g) (ha : 0 ≤ a) (hab : a ≤ b)
    (α β : ℝ) :
    wienerInt W P (fun s => α * f s + β * g s) a b =ᵐ[P]
      fun ω => α * wienerInt W P f a b ω + β * wienerInt W P g a b ω := by
  have h := hW.wienerInt_lin_ae (ι := Fin 3) ![1, -α, -β]
    ![fun s => α * f s + β * g s, f, g] (fun _ => a) (fun _ => b)
    (fun i => by fin_cases i <;> simp <;> fun_prop) (fun _ => ha) (fun _ => hab)
    (fun s => by simp [Fin.sum_univ_three]; ring)
  filter_upwards [h] with ω hω
  simp [Fin.sum_univ_three] at hω
  linarith

/-- The Wiener integral of the constant `1` is the increment: `∫ₐᵇ dW = W(b) - W(a)`. -/
theorem wienerInt_one (ha : 0 ≤ a) (hab : a ≤ b) :
    wienerInt W P (fun _ => 1) a b =ᵐ[P] fun ω => W b ω - W a ω := by
  have hR : ∀ n, riemannSum W (fun _ => 1) a b n = fun ω => W b ω - W a ω := by
    intro n; funext ω
    simp only [riemannSum, one_mul]
    rw [Finset.sum_range_sub (fun i => W (grid a b n i) ω), grid_last', grid_zero]
  refine msLim_unique (fun n => memLp_riemannSum hW ha hab n) (hW.memLp_incr ha hab) ?_
  simp [hR]

end IsWiener

/-- A pair of random variables is jointly Gaussian as soon as every linear combination is
Gaussian. -/
theorem hasGaussianLaw_pair {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : ∀ α β : ℝ, ∃ m : ℝ, ∃ v : ℝ≥0,
      P.map (fun ω => α * X ω + β * Y ω) = gaussianReal m v) :
    HasGaussianLaw (fun ω => (X ω, Y ω)) P := by
  refine ⟨isGaussian_of_isGaussian_map fun L => ?_⟩
  have hpair : AEMeasurable (fun ω => (X ω, Y ω)) P := hX.prodMk hY
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hpair]
  have hL : (L ∘ fun ω => (X ω, Y ω)) = fun ω => L (1, 0) * X ω + L (0, 1) * Y ω := by
    funext ω
    have : ((X ω, Y ω) : ℝ × ℝ) = X ω • ((1 : ℝ), (0 : ℝ)) + Y ω • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    simp only [Function.comp_apply]
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  obtain ⟨m, v, hmv⟩ := h (L (1, 0)) (L (0, 1))
  rw [hL, hmv]
  infer_instance

namespace IsWiener

variable (hW : IsWiener W P) {f g : ℝ → ℝ} {a b : ℝ}
include hW

/-- **Joint law**: Wiener integrals over a common interval are jointly Gaussian. -/
theorem wienerInt_hasGaussianLaw_pair (hf : Continuous f) (hg : Continuous g) (ha : 0 ≤ a)
    (hab : a ≤ b) :
    HasGaussianLaw (fun ω => (wienerInt W P f a b ω, wienerInt W P g a b ω)) P := by
  refine hasGaussianLaw_pair (hW.wienerInt_spec hf ha hab).1.aestronglyMeasurable.aemeasurable
    (hW.wienerInt_spec hg ha hab).1.aestronglyMeasurable.aemeasurable fun α β => ?_
  refine ⟨0, (∫ s in a..b, (α * f s + β * g s) ^ 2).toNNReal, ?_⟩
  rw [← Measure.map_congr (hW.wienerInt_add_smul hf hg ha hab α β)]
  exact hW.wienerInt_map (f := fun s => α * f s + β * g s) (by fun_prop) ha hab

end IsWiener

/-! ### Integration by parts -/

/-- Summation by parts: `Σᵢ fᵢ(wᵢ₊₁ - wᵢ) = fₙwₙ - f₀w₀ - Σᵢ (fᵢ₊₁ - fᵢ)wᵢ₊₁`. -/
lemma sum_by_parts (f w : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, f i * (w (i + 1) - w i) =
      f N * w N - f 0 * w 0 - ∑ i ∈ range N, (f (i + 1) - f i) * w (i + 1) := by
  rw [← Finset.sum_range_sub (fun i => f i * w i), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Pathwise integration by parts for Riemann sums**: for a `C¹` function `f` and a continuous
path `w`, `Σᵢ f(tᵢ)(w(tᵢ₊₁) - w(tᵢ)) → f(b)w(b) - f(a)w(a) - ∫ₐᵇ f'(s) w(s) ds`. -/
theorem riemann_ibp_tendsto {f f' w : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf' : Continuous f') (hw : Continuous w) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => ∑ i ∈ range (n + 1),
        f (grid a b n i) * (w (grid a b n (i + 1)) - w (grid a b n i))) atTop
      (𝓝 (f b * w b - f a * w a - ∫ s in a..b, f' s * w s)) := by
  have habel : ∀ n, ∑ i ∈ range (n + 1),
      f (grid a b n i) * (w (grid a b n (i + 1)) - w (grid a b n i)) =
      f b * w b - f a * w a - ∑ i ∈ range (n + 1),
        (f (grid a b n (i + 1)) - f (grid a b n i)) * w (grid a b n (i + 1)) := by
    intro n
    have := sum_by_parts (fun i => f (grid a b n i)) (fun i => w (grid a b n i)) (n + 1)
    simp only [grid_last', grid_zero] at this
    exact this
  refine Tendsto.congr (fun n => (habel n).symm) (tendsto_const_nhds.sub ?_)
  -- the Stieltjes sums of `w` against `df` converge to `∫ f' w`
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hf'.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (2 * (M + 1) * (b - a + 1)) with hε'
  have hba : 0 < b - a + 1 := by linarith
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨N, hN⟩ := cells_osc hab hw.continuousOn hε'0
  refine ⟨N, fun n hn => ?_⟩
  set t := grid a b n
  have hint : ∀ i, IntervalIntegrable (fun s => f' s * w s) volume (t i) (t (i + 1)) :=
    fun i => (hf'.mul hw).intervalIntegrable _ _
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (n := n + 1) (a := t)
    (fun k _ => hint k)
  rw [show t 0 = a from grid_zero a b n, show t (n + 1) = b from grid_last' n] at hsplit
  have hcell : ∀ i, (f (t (i + 1)) - f (t i)) * w (t (i + 1)) =
      ∫ s in t i..t (i + 1), f' s * w (t (i + 1)) := by
    intro i
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hf s) (hf'.intervalIntegrable _ _)]
  rw [Real.dist_eq, ← hsplit]
  simp_rw [hcell]
  rw [← Finset.sum_sub_distrib]
  have hD : ∀ i ∈ range (n + 1), |(∫ s in t i..t (i + 1), f' s * w (t (i + 1))) -
      ∫ s in t i..t (i + 1), f' s * w s| ≤ M * ε' * (t (i + 1) - t i) := by
    intro i hi
    have hi' : i < n + 1 := mem_range.mp hi
    have hle : t i ≤ t (i + 1) := grid_mono hab n (Nat.le_succ i)
    have hc : IntervalIntegrable (fun s => f' s * w (t (i + 1))) volume (t i) (t (i + 1)) :=
      (hf'.mul continuous_const).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hc (hint i)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t i) (b := t (i + 1))
      (C := M * ε') (f := fun s => f' s * w (t (i + 1)) - f' s * w s) (fun s hs => by
        rw [Set.uIoc_of_le hle] at hs
        have hsI : s ∈ Set.Icc (t i) (t (i + 1)) := ⟨hs.1.le, hs.2⟩
        have h1 : |w (t (i + 1)) - w s| ≤ ε' :=
          hN n hn i hi' _ ⟨hle, le_rfl⟩ s hsI
        have hmem := grid_mem hab (n := n) hi'.le
        have hmem2 := grid_mem hab (n := n) (Nat.succ_le_of_lt hi')
        have h2 : ‖f' s‖ ≤ M := hM s ⟨hmem.1.trans hsI.1, hsI.2.trans hmem2.2⟩
        rw [Real.norm_eq_abs] at h2 ⊢
        simp only
        rw [← mul_sub, abs_mul]
        exact mul_le_mul h2 h1 (abs_nonneg _) hM0)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] at this
    exact this
  calc |∑ i ∈ range (n + 1), ((∫ s in t i..t (i + 1), f' s * w (t (i + 1))) -
        ∫ s in t i..t (i + 1), f' s * w s)|
      ≤ ∑ i ∈ range (n + 1), |(∫ s in t i..t (i + 1), f' s * w (t (i + 1))) -
        ∫ s in t i..t (i + 1), f' s * w s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (n + 1), M * ε' * (t (i + 1) - t i) := Finset.sum_le_sum hD
    _ = M * ε' * (b - a) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (f := t), show t 0 = a from grid_zero a b n,
          show t (n + 1) = b from grid_last' n]
    _ < ε := by
        rw [hε']
        have h1 : M * (ε / (2 * (M + 1) * (b - a + 1))) * (b - a) =
            ε * (M / (M + 1)) * ((b - a) / (b - a + 1)) / 2 := by
          field_simp
        rw [h1]
        have h2 : M / (M + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
        have h3 : (b - a) / (b - a + 1) < 1 := (div_lt_one hba).mpr (by linarith)
        have h4 : 0 ≤ M / (M + 1) := by positivity
        have h5 : 0 ≤ (b - a) / (b - a + 1) := div_nonneg (by linarith) hba.le
        have : M / (M + 1) * ((b - a) / (b - a + 1)) < 1 := by nlinarith
        nlinarith

namespace IsWiener

variable (hW : IsWiener W P) {f f' : ℝ → ℝ} {a b : ℝ}
include hW

/-- **Integration by parts for the Wiener integral of a `C¹` function**:
`∫ₐᵇ f dW = f(b)W(b) - f(a)W(a) - ∫ₐᵇ f'(s) W(s) ds` almost surely.  This identifies the
mean-square integral with an expression in the paths of `W`. -/
theorem wienerInt_ibp (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : Continuous f') (ha : 0 ≤ a)
    (hab : a ≤ b) :
    wienerInt W P f a b =ᵐ[P]
      fun ω => f b * W b ω - f a * W a ω - ∫ s in a..b, f' s * W s ω := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  obtain ⟨h1, h2⟩ := hW.wienerInt_spec hfc ha hab
  refine ms_ae_unique (fun n => memLp_riemannSum hW ha hab n) h1 h2 ?_
  filter_upwards [hW.cont] with ω hω
  exact riemann_ibp_tendsto hf hf' hω hab

end IsWiener

end Gardiner.Ito
