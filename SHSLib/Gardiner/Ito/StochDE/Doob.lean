/-
# Doob's `L²` maximal inequality (discrete time and on dyadic grids)

* `Gardiner.Ito.StochDE.doob_L2_nat`: for a square integrable martingale `(f k)_{k ∈ ℕ}`,
  `E[(max_{k ≤ n} |f k|)²] ≤ 4 E[f n ²]`.
-/
import SHSLib.Gardiner.Ito.Calculus

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- The running maximum `max_{k ≤ n} |f k ω|`. -/
def runMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => |f k ω|)

lemma runMax_nonneg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ runMax f n ω :=
  (abs_nonneg _).trans (Finset.le_sup' (fun k => |f k ω|) (Finset.mem_range.mpr n.lt_succ_self))

lemma le_runMax (f : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ≤ n) (ω : Ω) : |f k ω| ≤ runMax f n ω :=
  Finset.le_sup' (fun k => |f k ω|) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

lemma runMax_le_sum (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    runMax f n ω ≤ ∑ k ∈ Finset.range (n + 1), |f k ω| :=
  Finset.sup'_le _ _ fun _ hk =>
    Finset.single_le_sum (f := fun k => |f k ω|) (fun _ _ => abs_nonneg _) hk

lemma measurable_runMax {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f k)) (n : ℕ) :
    Measurable (runMax f n) := by
  have : runMax f n = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k ω => |f k ω|) := by
    funext ω; simp [runMax, Finset.sup'_apply]
  rw [this]
  exact Finset.measurable_sup' _ fun k _ => (hf k).abs

/-- **Doob's `L²` maximal inequality, discrete time.** -/
theorem doob_L2_nat [IsFiniteMeasure μ] {𝒢 : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f 𝒢 μ) (n : ℕ) (hn : MemLp (f n) 2 μ) :
    MemLp (runMax f n) 2 μ ∧ ∫ ω, runMax f n ω ^ 2 ∂μ ≤ 4 * ∫ ω, f n ω ^ 2 ∂μ := by
  -- measurable representatives
  have hfm : ∀ k, Measurable (f k) := fun k =>
    ((hf.stronglyMeasurable k).mono (𝒢.le k)).measurable
  have hfk : ∀ k ≤ n, MemLp (f k) 2 μ := fun k hk =>
    (hn.condExp (m := 𝒢 k)).ae_eq (hf.condExp_ae_eq hk)
  set S := runMax f n with hS
  have hSm : Measurable S := measurable_runMax hfm n
  have hS2 : MemLp S 2 μ := by
    refine (memLp_finset_sum' _ fun k hk => (hfk k (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk))).abs).mono hSm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (runMax_nonneg f n ω), Finset.sum_apply]
    exact (runMax_le_sum f n ω).trans (le_abs_self _)
  refine ⟨hS2, ?_⟩
  -- the absolute value is a nonnegative submartingale
  set g : ℕ → Ω → ℝ := fun k ω => |f k ω| with hg
  have hgsub : Submartingale g 𝒢 μ := by
    have h := hf.submartingale.sup hf.neg.submartingale
    have e : f ⊔ -f = g := by
      funext k ω; simp [hg, abs_eq_max_neg]
    rwa [e] at h
  have hg0 : 0 ≤ g := fun k ω => abs_nonneg _
  have hgn : MemLp (g n) 2 μ := hn.abs
  set A := ∫ ω, S ω ^ 2 ∂μ
  set B := ∫ ω, f n ω ^ 2 ∂μ
  -- `A ≤ 2 E[g n S]`
  have hmain : A ≤ 2 * ∫ ω, g n ω * S ω ∂μ := by
    have hgS : Integrable (fun ω => g n ω * S ω) μ := hgn.integrable_mul hS2
    have hgSnn : 0 ≤ ∫ ω, g n ω * S ω ∂μ :=
      integral_nonneg fun ω => mul_nonneg (hg0 n ω) (runMax_nonneg f n ω)
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
    -- layer cake for `S²`
    have h1 : ENNReal.ofReal A = ∫⁻ t in Set.Ioi 0, μ {ω | t ≤ S ω} * ENNReal.ofReal (2 * t) := by
      have := lintegral_comp_eq_lintegral_meas_le_mul μ (f := S) (g := fun t => 2 * t)
        (Eventually.of_forall fun ω => runMax_nonneg f n ω) hSm.aemeasurable
        (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable _ _)
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg zero_le_two (le_of_lt ht))
      rw [← this, ofReal_integral_eq_lintegral_ofReal hS2.integrable_sq
        (Eventually.of_forall fun ω => sq_nonneg _)]
      refine lintegral_congr fun ω => ?_
      congr 1
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    -- the density measure `g n · μ`
    set ν := μ.withDensity (fun ω => ENNReal.ofReal (g n ω))
    have hgnm : Measurable (g n) := (hfm n).abs
    have h2 : ∀ t > (0 : ℝ), μ {ω | t ≤ S ω} * ENNReal.ofReal (2 * t) ≤
        ENNReal.ofReal 2 * ν {ω | t ≤ S ω} := by
      intro t ht
      have hmax := maximal_ineq hgsub hg0 (ε := t.toNNReal) n
      have ht' : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
      simp only [ht'] at hmax
      have hset : {ω | t ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => g k ω)} = {ω | t ≤ S ω} := rfl
      rw [hset] at hmax
      have hmeas : MeasurableSet {ω | t ≤ S ω} := measurableSet_le measurable_const hSm
      rw [withDensity_apply _ hmeas, ← ofReal_integral_eq_lintegral_ofReal
        (hgn.integrable one_le_two).integrableOn (Eventually.of_forall fun ω => hg0 n ω)]
      rw [ENNReal.ofReal_mul zero_le_two, mul_comm, mul_assoc]
      refine mul_le_mul_right ?_ _
      refine le_trans (le_of_eq ?_) hmax
      simp only [ENNReal.smul_def, smul_eq_mul]; rfl
    have h3 : ∫⁻ t in Set.Ioi 0, ν {ω | t ≤ S ω} =
        ENNReal.ofReal (∫ ω, g n ω * S ω ∂μ) := by
      rw [← lintegral_eq_lintegral_meas_le ν (Eventually.of_forall fun ω => runMax_nonneg f n ω)
        hSm.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ hgnm.ennreal_ofReal
        hSm.ennreal_ofReal, ofReal_integral_eq_lintegral_ofReal hgS
        (Eventually.of_forall fun ω => mul_nonneg (hg0 n ω) (runMax_nonneg f n ω))]
      refine lintegral_congr fun ω => ?_
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul (hg0 n ω)]
    have hmon : Measurable fun t => ν {ω | t ≤ S ω} :=
      Antitone.measurable fun s t hst => measure_mono fun ω (h : t ≤ S ω) =>
        (show s ≤ S ω from hst.trans h)
    rw [h1, ENNReal.ofReal_mul zero_le_two, ← h3, ← lintegral_const_mul _ hmon]
    exact setLIntegral_mono' measurableSet_Ioi fun t ht => h2 t ht
  -- `2 g S ≤ 2 g² + S²/2`
  have hAM : ∫ ω, g n ω * S ω ∂μ ≤ ∫ ω, (g n ω ^ 2 + S ω ^ 2 / 4) ∂μ := by
    refine integral_mono (hgn.integrable_mul hS2) (hgn.integrable_sq.add
      (hS2.integrable_sq.div_const 4)) fun ω => ?_
    nlinarith [sq_nonneg (g n ω - S ω / 2)]
  rw [integral_add hgn.integrable_sq (hS2.integrable_sq.div_const 4), integral_div] at hAM
  have hgsq : ∫ ω, g n ω ^ 2 ∂μ = B := by simp [hg, sq_abs, B]
  rw [hgsq] at hAM
  linarith

/-! ### Dyadic grids and the continuous-time inequality -/

lemma enorm_sq_eq_ofReal (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

lemma lintegral_enorm_sq_eq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ ω, X ω ^ 2 ∂μ) := by
  simp_rw [enorm_sq_eq_ofReal]
  rw [ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
    (Eventually.of_forall fun ω => sq_nonneg _)]

/-- The dyadic grid point `t₀ + (k / 2ⁿ)(t - t₀)`. -/
def gridPt (t₀ t : ℝ) (n k : ℕ) : ℝ := t₀ + ((k : ℝ) / 2 ^ n) * (t - t₀)

lemma gridPt_mem {t₀ t : ℝ} (ht : t₀ ≤ t) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    gridPt t₀ t n k ∈ Set.Icc t₀ t := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) / 2 ^ n := by positivity
  have h1 : (k : ℝ) / 2 ^ n ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hk
  have hd : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  constructor
  · unfold gridPt; nlinarith
  · unfold gridPt; nlinarith

lemma gridPt_mono {t₀ t : ℝ} (ht : t₀ ≤ t) (n : ℕ) : Monotone (gridPt t₀ t n) := by
  intro i j hij
  unfold gridPt
  have : (i : ℝ) / 2 ^ n ≤ (j : ℝ) / 2 ^ n :=
    div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  nlinarith [sub_nonneg.mpr ht]

lemma gridPt_double (t₀ t : ℝ) (n k : ℕ) : gridPt t₀ t (n + 1) (2 * k) = gridPt t₀ t n k := by
  unfold gridPt; push_cast; rw [pow_succ]; field_simp

lemma gridPt_last (t₀ t : ℝ) (n : ℕ) : gridPt t₀ t n (2 ^ n) = t := by
  unfold gridPt; push_cast; rw [div_self (by positivity)]; ring

lemma gridPt_zero (t₀ t : ℝ) (n : ℕ) : gridPt t₀ t n 0 = t₀ := by
  simp [gridPt]

/-- The supremum of `|X|` over the dyadic points of `[t₀, t]` (an `ℝ≥0∞`-valued random variable). -/
def dsup (X : ℝ → Ω → ℝ) (t₀ t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ k : Fin (2 ^ n + 1), ‖X (gridPt t₀ t n k) ω‖ₑ

/-- The maximum over the `n`-th dyadic grid. -/
def gridMax (X : ℝ → Ω → ℝ) (t₀ t : ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ k : Fin (2 ^ n + 1), ‖X (gridPt t₀ t n k) ω‖ₑ

lemma gridMax_mono (X : ℝ → Ω → ℝ) (t₀ t : ℝ) (ω : Ω) :
    Monotone fun n => gridMax X t₀ t n ω := by
  refine monotone_nat_of_le_succ fun n => iSup_le fun k => ?_
  have hk : 2 * (k : ℕ) < 2 ^ (n + 1) + 1 := by
    have := k.isLt; rw [pow_succ]; omega
  refine le_trans (le_of_eq ?_) (le_iSup _ (⟨2 * k, hk⟩ : Fin (2 ^ (n + 1) + 1)))
  simp only
  rw [gridPt_double]

lemma measurable_gridMax {X : ℝ → Ω → ℝ} (hX : ∀ u, Measurable (X u)) (t₀ t : ℝ) (n : ℕ) :
    Measurable (gridMax X t₀ t n) :=
  Measurable.iSup fun _ => (hX _).enorm

lemma measurable_dsup {X : ℝ → Ω → ℝ} (hX : ∀ u, Measurable (X u)) (t₀ t : ℝ) :
    Measurable (dsup X t₀ t) :=
  Measurable.iSup fun n => measurable_gridMax hX t₀ t n

lemma dsup_le_iSup {X : ℝ → Ω → ℝ} {t₀ t : ℝ} (ht : t₀ ≤ t) (ω : Ω) :
    dsup X t₀ t ω ≤ ⨆ u ∈ Set.Icc t₀ t, ‖X u ω‖ₑ :=
  iSup_le fun n => iSup_le fun k =>
    le_biSup (fun u => ‖X u ω‖ₑ) (gridPt_mem ht (Nat.lt_succ_iff.mp k.isLt))

lemma tendsto_floor_div_pow {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => ((⌊s * 2 ^ n⌋₊ : ℕ) : ℝ) / 2 ^ n) atTop (𝓝 s) := by
  have hlim : Tendsto (fun n : ℕ => s - (1 / 2) ^ n) atTop (𝓝 s) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have := Nat.lt_floor_add_one (s * 2 ^ n)
    rw [le_div_iff₀ h2, sub_mul, one_div_pow, div_mul_cancel₀ _ h2.ne']
    linarith
  · have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_le_iff₀ h2]
    exact Nat.floor_le (by positivity)

lemma iSup_le_dsup {X : ℝ → Ω → ℝ} {t₀ t : ℝ} {ω : Ω}
    (hc : ContinuousOn (fun u => X u ω) (Set.Icc t₀ t)) :
    ⨆ u ∈ Set.Icc t₀ t, ‖X u ω‖ₑ ≤ dsup X t₀ t ω := by
  refine iSup₂_le fun u hu => ?_
  have ht : t₀ ≤ t := hu.1.trans hu.2
  rcases eq_or_lt_of_le ht with h | h
  · have hu' : u = t₀ := le_antisymm (h ▸ hu.2) hu.1
    rw [hu']
    refine le_trans ?_ (le_iSup (fun n : ℕ => ⨆ k : Fin (2 ^ n + 1),
      ‖X (gridPt t₀ t n k) ω‖ₑ) 0)
    refine le_trans ?_ (le_iSup (fun k : Fin (2 ^ 0 + 1) => ‖X (gridPt t₀ t 0 k) ω‖ₑ) 0)
    simp [gridPt]
  set s := (u - t₀) / (t - t₀)
  have hd : 0 < t - t₀ := sub_pos.mpr h
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr hu.1) hd.le
  have hs1 : s ≤ 1 := (div_le_one hd).mpr (by linarith [hu.2])
  set k : ℕ → ℕ := fun n => ⌊s * 2 ^ n⌋₊
  have hk : ∀ n, k n ≤ 2 ^ n := fun n => by
    refine Nat.floor_le_of_le ?_
    push_cast; nlinarith [show (0 : ℝ) < 2 ^ n by positivity]
  have hg : Tendsto (fun n => gridPt t₀ t n (k n)) atTop (𝓝 u) := by
    have := ((tendsto_floor_div_pow hs0).mul_const (t - t₀)).const_add t₀
    convert this using 2
    simp only [s]; field_simp; ring
  have hg' : Tendsto (fun n => gridPt t₀ t n (k n)) atTop (𝓝[Set.Icc t₀ t] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hg, Eventually.of_forall fun n => gridPt_mem ht (hk n)⟩
  have hX := ((hc u hu).tendsto.comp hg').enorm
  refine le_of_tendsto' hX fun n => ?_
  refine le_trans ?_ (le_iSup _ n)
  exact le_trans (le_of_eq rfl) (le_iSup (fun j : Fin (2 ^ n + 1) =>
    ‖X (gridPt t₀ t n j) ω‖ₑ) ⟨k n, Nat.lt_succ_of_le (hk n)⟩)

lemma dsup_eq_iSup {X : ℝ → Ω → ℝ} {t₀ t : ℝ} (ht : t₀ ≤ t) {ω : Ω}
    (hc : ContinuousOn (fun u => X u ω) (Set.Icc t₀ t)) :
    dsup X t₀ t ω = ⨆ u ∈ Set.Icc t₀ t, ‖X u ω‖ₑ :=
  le_antisymm (dsup_le_iSup ht ω) (iSup_le_dsup hc)

/-- The filtration `k ↦ 𝓕 (τ k)` along a monotone sequence of times. -/
def seqFiltration (𝓕 : Filtration ℝ mΩ) (τ : ℕ → ℝ) (hτ : Monotone τ) : Filtration ℕ mΩ where
  seq k := 𝓕 (τ k)
  mono' _ _ hij := 𝓕.mono (hτ hij)
  le' _ := 𝓕.le _

lemma martingale_seq {𝓕 : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ} (hM : Martingale M 𝓕 μ)
    (τ : ℕ → ℝ) (hτ : Monotone τ) :
    Martingale (fun k => M (τ k)) (seqFiltration 𝓕 τ hτ) μ :=
  ⟨fun k => hM.1 (τ k), fun _ _ hij => hM.2 _ _ (hτ hij)⟩

lemma iSup_fin_enorm_eq_runMax (f : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    ⨆ k : Fin (N + 1), ‖f k ω‖ₑ = ENNReal.ofReal (runMax f N ω) := by
  refine le_antisymm (iSup_le fun k => ?_) ?_
  · rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_runMax f (Nat.lt_succ_iff.mp k.isLt) ω)
  · obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun k => |f k ω|)
    have : runMax f N ω = |f k ω| := he
    rw [this, ← Real.enorm_eq_ofReal_abs]
    exact le_iSup (fun j : Fin (N + 1) => ‖f j ω‖ₑ) ⟨k, Finset.mem_range.mp hk⟩

/-- **Doob's `L²` maximal inequality on a dyadic grid**, for a process that agrees at each time
with a square integrable martingale. -/
theorem doob_L2_dsup [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) {t₀ t : ℝ} (ht : t₀ ≤ t) (hMt : MemLp (M t) 2 μ)
    {X : ℝ → Ω → ℝ} (hX : ∀ u ∈ Set.Icc t₀ t, X u =ᵐ[μ] M u) :
    ∫⁻ ω, dsup X t₀ t ω ^ 2 ∂μ ≤ 4 * ∫⁻ ω, ‖M t ω‖ₑ ^ 2 ∂μ := by
  have hMm : ∀ u, Measurable (M u) := fun u => ((hM.1 u).mono (𝓕.le u)).measurable
  have hpow : ∀ ω, dsup X t₀ t ω ^ 2 = ⨆ n, gridMax X t₀ t n ω ^ 2 := fun ω =>
    ENNReal.iSup_pow _ _
  simp only [hpow]
  have hae : ∀ n, ∀ᵐ ω ∂μ, ∀ k : Fin (2 ^ n + 1),
      X (gridPt t₀ t n k) ω = M (gridPt t₀ t n k) ω := fun n =>
    ae_all_iff.mpr fun k => hX _ (gridPt_mem ht (Nat.lt_succ_iff.mp k.isLt))
  have hae' : ∀ᵐ ω ∂μ, ∀ n, ∀ k : Fin (2 ^ n + 1),
      X (gridPt t₀ t n k) ω = M (gridPt t₀ t n k) ω := ae_all_iff.mpr hae
  have heq : (fun ω => ⨆ n, gridMax X t₀ t n ω ^ 2) =ᵐ[μ]
      fun ω => ⨆ n, gridMax M t₀ t n ω ^ 2 := by
    filter_upwards [hae'] with ω hω
    simp only [gridMax, hω]
  rw [lintegral_congr_ae heq, lintegral_iSup (fun n => (measurable_gridMax hMm t₀ t n).pow_const 2)
    (fun i j hij ω => pow_le_pow_left' (gridMax_mono M t₀ t ω hij) 2)]
  refine iSup_le fun n => ?_
  set N := 2 ^ n
  set τ : ℕ → ℝ := fun k => gridPt t₀ t n (min k N)
  have hτ : Monotone τ := fun i j hij => gridPt_mono ht n (min_le_min_right N hij)
  have hmart := martingale_seq hM τ hτ
  have hτN : τ N = t := by simp [τ, N, gridPt_last]
  have hL2 : MemLp ((fun k => M (τ k)) N) 2 μ := by simp only [hτN]; exact hMt
  obtain ⟨hS2, hineq⟩ := doob_L2_nat hmart N hL2
  have hgm : ∀ ω, gridMax M t₀ t n ω = ENNReal.ofReal (runMax (fun k => M (τ k)) N ω) := by
    intro ω
    rw [← iSup_fin_enorm_eq_runMax]
    refine iSup_congr fun k => ?_
    simp only [τ]
    rw [min_eq_left (Nat.lt_succ_iff.mp k.isLt)]
  simp_rw [hgm, ← ENNReal.ofReal_pow (runMax_nonneg _ _ _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hS2.integrable_sq
    (Eventually.of_forall fun ω => sq_nonneg _), lintegral_enorm_sq_eq hMt]
  calc ENNReal.ofReal (∫ ω, runMax (fun k => M (τ k)) N ω ^ 2 ∂μ)
      ≤ ENNReal.ofReal (4 * ∫ ω, M t ω ^ 2 ∂μ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simpa [hτN] using hineq
    _ = 4 * ENNReal.ofReal (∫ ω, M t ω ^ 2 ∂μ) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

/-- **Doob's `L²` maximal inequality in continuous time**: if `X` agrees at each time with a square
integrable martingale `M` and has continuous paths on `[t₀, t]` almost surely, then
`E[sup_{t₀ ≤ u ≤ t} |X u|²] ≤ 4 E[M t ²]`. -/
theorem doob_L2_contin [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) {t₀ t : ℝ} (ht : t₀ ≤ t) (hMt : MemLp (M t) 2 μ)
    {X : ℝ → Ω → ℝ} (hX : ∀ u ∈ Set.Icc t₀ t, X u =ᵐ[μ] M u)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun u => X u ω) (Set.Icc t₀ t)) :
    ∫⁻ ω, (⨆ u ∈ Set.Icc t₀ t, ‖X u ω‖ₑ) ^ 2 ∂μ ≤ 4 * ∫⁻ ω, ‖M t ω‖ₑ ^ 2 ∂μ := by
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (doob_L2_dsup hM ht hMt hX)
  filter_upwards [hc] with ω hω
  rw [dsup_eq_iSup ht hω]

end Gardiner.Ito.StochDE
