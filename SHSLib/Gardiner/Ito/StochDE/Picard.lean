/-
# Existence of solutions of Itô SDEs: Picard iteration

Gardiner §4.3.1, (4.3.10)–(4.3.11).  Under the Lipschitz and growth conditions on `[t₀, T]`
(`SDECoeffs a b t₀ T K`), for every horizon `T` and every square integrable, `𝓕 t₀`-measurable
initial value `ξ`, the Picard iterates
`x₀ = ξ`, `x_{n+1}(t) = ξ + ∫_{t₀}^t a(x_n(s), s) ds + ∫_{t₀}^t b(x_n(s), s) dW(s)`
(taken in continuous adapted versions) converge almost surely uniformly on `[t₀, T]`, and in
`E sup |·|²`, to a solution of (4.3.4).

* `picardStep`, `picardSeq`, `sdeSol`: the iteration and its limit;
* `IsRegProc`: jointly measurable, adapted, a.s. continuous on `[t₀, T]`, with
  `E sup_{[t₀, T]} |x|² < ∞`;
* `isSDESol_sdeSol`: **existence**: `sdeSol` is a solution of (4.3.4) on `[t₀, T]`.
-/
import SHSLib.Gardiner.Ito.StochDE.Wellposed

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- A regular process on `[t₀, T]`: jointly measurable, adapted on `[t₀, T]`, almost surely
continuous on `[t₀, T]`, with `E sup_{t₀ ≤ t ≤ T} |x(t)|² < ∞`. -/
structure IsRegProc (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (t₀ T : ℝ) (x : ℝ → Ω → ℝ) :
    Prop where
  measurable : Measurable (Function.uncurry x)
  adapted : ∀ t ∈ Set.Icc t₀ T, StronglyMeasurable[𝓕 t] (x t)
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => x t ω) (Set.Icc t₀ T)
  supSq_lt_top : supSq P x t₀ T < ⊤

lemma lintegral_supSq_le {Y : ℝ → Ω → ℝ} {t₀ t T : ℝ} (htT : t ≤ T) :
    ∫⁻ s in Set.Ioc t₀ t, supSq P Y t₀ s ≤ ENNReal.ofReal (t - t₀) * supSq P Y t₀ T := by
  calc ∫⁻ s in Set.Ioc t₀ t, supSq P Y t₀ s ≤ ∫⁻ _ in Set.Ioc t₀ t, supSq P Y t₀ T :=
        setLIntegral_mono' measurableSet_Ioc fun s hs => supSq_mono_right (hs.2.trans htT)
    _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, mul_comm]

lemma IsRegProc.sq_int {t₀ T : ℝ} {x : ℝ → Ω → ℝ} (hx : IsRegProc 𝓕 P t₀ T x) :
    ∫⁻ s in Set.Ioc t₀ T, ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P < ⊤ :=
  ((tsSq_le_lintegral_supSq x t₀ T).trans (lintegral_supSq_le le_rfl)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx.supSq_lt_top)

/-- Processes with `E sup |x - y|² = 0` are indistinguishable. -/
lemma ae_eq_of_supSq_sub_eq_zero {x y : ℝ → Ω → ℝ} {t₀ T : ℝ} (htT : t₀ ≤ T)
    (hxm : Measurable (Function.uncurry x)) (hym : Measurable (Function.uncurry y))
    (hxc : ∀ᵐ ω ∂P, ContinuousOn (fun t => x t ω) (Set.Icc t₀ T))
    (hyc : ∀ᵐ ω ∂P, ContinuousOn (fun t => y t ω) (Set.Icc t₀ T))
    (h : supSq P (fun s ω => x s ω - y s ω) t₀ T = 0) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc t₀ T, x t ω = y t ω := by
  have hm : AEMeasurable (fun ω => (⨆ u ∈ Set.Icc t₀ T, ‖x u ω - y u ω‖ₑ) ^ 2) P :=
    (aemeasurable_iSup_Icc (Y := fun s ω => x s ω - y s ω)
      (fun u => (measurable_of_uncurry hxm u).sub (measurable_of_uncurry hym u))
      htT ((hxc.and hyc).mono fun ω hω => hω.1.sub hω.2)).pow_const 2
  rw [supSq, lintegral_eq_zero_iff' hm] at h
  filter_upwards [h] with ω hω t ht
  simp only [Pi.zero_apply, pow_eq_zero_iff (n := 2) (by norm_num)] at hω
  have := (enorm_le_iSup_Icc (Y := fun s ω => x s ω - y s ω) ht ω).trans_eq hω
  simpa [sub_eq_zero] using this

/-- `E sup |x - z|² ≤ 2 E sup |x - y|² + 2 E sup |y - z|²`. -/
lemma supSq_sub_triangle {x y z : ℝ → Ω → ℝ} {t₀ T : ℝ} (htT : t₀ ≤ T)
    (hxm : Measurable (Function.uncurry x)) (hym : Measurable (Function.uncurry y))
    (hxc : ∀ᵐ ω ∂P, ContinuousOn (fun t => x t ω) (Set.Icc t₀ T))
    (hyc : ∀ᵐ ω ∂P, ContinuousOn (fun t => y t ω) (Set.Icc t₀ T)) :
    supSq P (fun s ω => x s ω - z s ω) t₀ T ≤
      2 * supSq P (fun s ω => x s ω - y s ω) t₀ T + 2 * supSq P (fun s ω => z s ω - y s ω) t₀ T := by
  have h := IsSDESol.supSq_sub_le_two (P := P) (x := fun s ω => x s ω - y s ω)
    (y := fun s ω => z s ω - y s ω) htT (hxm.sub hym)
    ((hxc.and hyc).mono fun ω hω => hω.1.sub hω.2)
  convert h using 3
  ring

/-! ### Elementary series bounds -/

/-- A weighted Cauchy–Schwarz inequality: `(∑ f k)² ≤ 2 ∑ 2ᵏ (f k)²`. -/
lemma tsum_sq_le_two_mul (f : ℕ → ℝ≥0∞) : (∑' k, f k) ^ 2 ≤ 2 * ∑' k, 2 ^ k * f k ^ 2 := by
  set μ : Measure ℕ := (Measure.count : Measure ℕ).withDensity fun k => (2⁻¹ : ℝ≥0∞) ^ k
  have hw : ∀ k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k * 2 ^ k = 1 := fun k => by
    rw [← ENNReal.inv_pow]
    exact ENNReal.inv_mul_cancel (pow_ne_zero _ (by norm_num)) (ENNReal.pow_ne_top (by norm_num))
  have h := lintegral_sq_le_mul (μ := μ) (f := fun k => 2 ^ k * f k) (measurable_of_countable _).aemeasurable
  have e1 : ∫⁻ k, 2 ^ k * f k ∂μ = ∑' k, f k := by
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), lintegral_count]
    congr 1; funext k
    simp only [Pi.mul_apply]
    rw [← mul_assoc, hw, one_mul]
  have e2 : μ Set.univ = 2 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
      ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  have e3 : ∫⁻ k, (2 ^ k * f k) ^ 2 ∂μ = ∑' k, 2 ^ k * f k ^ 2 := by
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), lintegral_count]
    congr 1; funext k
    simp only [Pi.mul_apply]
    rw [mul_pow, ← mul_assoc, sq (2 ^ k : ℝ≥0∞), ← mul_assoc, hw, one_mul]
  rwa [e1, e2, e3] at h

lemma pow_div_factorial_add_le {c : ℝ} (hc : 0 ≤ c) (k n : ℕ) :
    c ^ (k + n) / ((k + n).factorial : ℝ) ≤ c ^ k / k.factorial * (c ^ n / n.factorial) := by
  rw [div_mul_div_comm, ← pow_add]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add k n)

lemma tsum_two_pow_mul_le_exp {c : ℝ} (hc : 0 ≤ c) :
    ∑' k : ℕ, (2 : ℝ≥0∞) ^ k * ENNReal.ofReal (c ^ k / k.factorial) ≤
      ENNReal.ofReal (Real.exp (2 * c)) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  have e : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k * ENNReal.ofReal (c ^ k / k.factorial) =
      ENNReal.ofReal ((2 * c) ^ k / k.factorial) := fun k => by
    rw [mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow
      (by norm_num), ENNReal.ofReal_ofNat]
  simp_rw [e]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
  exact ENNReal.ofReal_le_ofReal (Real.sum_le_exp_of_nonneg (by positivity) n)

lemma tendsto_ofReal_pow_div_factorial (c : ℝ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (c ^ n / n.factorial)) atTop (𝓝 0) := by
  simpa using (ENNReal.continuous_ofReal.tendsto 0).comp
    (FloorSemiring.tendsto_pow_div_factorial_atTop c)

/-- Uniform convergence along increments with finite total sup-variation, with a tail bound. -/
lemma limUnder_tail_of_tsum_ne_top {f : ℕ → ℝ → ℝ} {s : Set ℝ} (hf : ∀ j, ContinuousOn (f j) s)
    (hsum : ∑' j, (⨆ u ∈ s, ‖f (j + 1) u - f j u‖ₑ) ≠ ⊤) :
    ContinuousOn (fun x => limUnder atTop fun j => f j x) s ∧
      ∀ x ∈ s, ∀ n, ‖(limUnder atTop fun j => f j x) - f n x‖ₑ ≤
        ∑' k, ⨆ u ∈ s, ‖f (k + n + 1) u - f (k + n) u‖ₑ := by
  set g : ℕ → ℝ≥0∞ := fun j => ⨆ u ∈ s, ‖f (j + 1) u - f j u‖ₑ
  have hg : ∀ j, g j ≠ ⊤ := fun j => ne_top_of_le_ne_top hsum (ENNReal.le_tsum j)
  have hle : ∀ j, ∀ x ∈ s, ‖f (j + 1) x - f j x‖ₑ ≤ g j := fun j x hx =>
    le_iSup₂ (f := fun u (_ : u ∈ s) => ‖f (j + 1) u - f j u‖ₑ) x hx
  obtain ⟨hcont, htend⟩ := limUnder_of_summable_incr hf (u := fun j => (g j).toReal)
    (ENNReal.summable_toReal hsum) (fun j x hx => by
      rw [← Real.norm_eq_abs, ← toReal_enorm]
      exact ENNReal.toReal_mono (hg j) (hle j x hx))
  refine ⟨hcont, fun x hx n => ?_⟩
  have hfin : ∀ j, ‖f (j + n) x - f n x‖ₑ ≤ ∑ k ∈ Finset.range j, g (k + n) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      calc ‖f (j + 1 + n) x - f n x‖ₑ
          = ‖(f (j + n + 1) x - f (j + n) x) + (f (j + n) x - f n x)‖ₑ := by
            rw [show j + 1 + n = j + n + 1 by ring]; ring_nf
        _ ≤ ‖f (j + n + 1) x - f (j + n) x‖ₑ + ‖f (j + n) x - f n x‖ₑ := enorm_add_le _ _
        _ ≤ g (j + n) + ∑ k ∈ Finset.range j, g (k + n) := add_le_add (hle _ x hx) ih
        _ = _ := add_comm _ _
  have hlim : Tendsto (fun j => ‖f (j + n) x - f n x‖ₑ) atTop
      (𝓝 ‖(limUnder atTop fun j => f j x) - f n x‖ₑ) :=
    (continuous_enorm.tendsto _).comp
      (((tendsto_add_atTop_iff_nat n).mpr (htend x hx)).sub_const _)
  exact le_of_tendsto' hlim fun j => (hfin j).trans (ENNReal.sum_le_tsum _)

/-! ### The Picard step -/

/-- **The Picard map**: `x ↦ ξ + ∫_{t₀}^· a(x(s), s) ds + ∫_{t₀}^· b(x(s), s) dW(s)`, taken in its
adapted, continuous version. -/
def picardStep (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (a b : ℝ → ℝ → ℝ)
    (t₀ T : ℝ) (ξ : Ω → ℝ) (x : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ξ ω + driftVer a x t₀ t ω + itoCont W 𝓕 P T (drive t₀ b x) t ω

/-- **The Picard iterates** `x₀ = ξ`, `x_{n+1} = picardStep x_n`. -/
def picardSeq (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (a b : ℝ → ℝ → ℝ)
    (t₀ T : ℝ) (ξ : Ω → ℝ) : ℕ → ℝ → Ω → ℝ
  | 0 => fun _ ω => ξ ω
  | n + 1 => picardStep W 𝓕 P a b t₀ T ξ (picardSeq W 𝓕 P a b t₀ T ξ n)

/-- **The solution of the SDE (4.3.4)**: the pointwise limit of the Picard iterates. -/
def sdeSol (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (a b : ℝ → ℝ → ℝ)
    (t₀ T : ℝ) (ξ : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => picardSeq W 𝓕 P a b t₀ T ξ n t ω

section Step

variable {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} {ξ : Ω → ℝ}
  (hW : IsFWiener W 𝓕 P) (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
  (hξm : StronglyMeasurable[𝓕 t₀] ξ) (hξ : MemLp ξ 2 P)
include hW hc ht₀ htT hξm hξ

lemma measurable_xi : Measurable ξ := (hξm.mono (𝓕.le t₀)).measurable

/-- The Picard step of a regular process is regular and satisfies the integral equation. -/
theorem IsRegProc.picard {x : ℝ → Ω → ℝ} (hx : IsRegProc 𝓕 P t₀ T x) :
    IsRegProc 𝓕 P t₀ T (picardStep W 𝓕 P a b t₀ T ξ x) ∧
      ∀ u ∈ Set.Icc t₀ T, picardStep W 𝓕 P a b t₀ T ξ x u =ᵐ[P] fun ω =>
        ξ ω + (∫ s in t₀..u, a (x s ω) s) + itoInt W 𝓕 P u (drive t₀ b x) ω := by
  have := hW.isProbabilityMeasure
  have hT : 0 ≤ T := ht₀.trans htT
  have hB := isItoIntegrand_drive hc ht₀ hx.measurable hx.adapted hx.sq_int
  have hI := isContItoVersion_itoCont hW hB hT
  have hξ' := measurable_xi hW hc ht₀ htT hξm hξ
  have hrep : ∀ u ∈ Set.Icc t₀ T, picardStep W 𝓕 P a b t₀ T ξ x u =ᵐ[P] fun ω =>
      ξ ω + (∫ s in t₀..u, a (x s ω) s) + itoInt W 𝓕 P u (drive t₀ b x) ω := by
    intro u hu
    filter_upwards [hx.cont, hI.eq u ⟨ht₀.trans hu.1, hu.2⟩] with ω h1 h2
    simp only [StochDE.picardStep]
    rw [driftVer_eq hc.driftCoeff hx.measurable h1 hu, ← h2]
  have hm : Measurable (Function.uncurry (StochDE.picardStep W 𝓕 P a b t₀ T ξ x)) :=
    ((hξ'.comp measurable_snd).add (measurable_driftVer hc.measurable_a
      (measurable_of_uncurry hx.measurable) t₀)).add hI.measurable
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => StochDE.picardStep W 𝓕 P a b t₀ T ξ x t ω)
      (Set.Icc t₀ T) := by
    filter_upwards [hx.cont, hI.cont] with ω h1 h2
    refine (continuousOn_const.add ((continuousOn_drift hc.driftCoeff htT hx.measurable h1).congr
      fun t ht => driftVer_eq hc.driftCoeff hx.measurable h1 ht)).add
      (h2.mono (Set.Icc_subset_Icc_left ht₀))
  refine ⟨⟨hm, fun t ht => ?_, hcont, ?_⟩, hrep⟩
  · exact ((hξm.mono (𝓕.mono ht.1)).add (driftVer_adapted hc.measurable_a hx.adapted ht.1 ht.2)).add
      (hI.adapted t (ht₀.trans ht.1))
  · have h := sup_sq_le hW (A := fun s ω => a (x s ω) s) ht₀ ⟨htT, le_rfl⟩ hB
      (fun s ω hs => drive_of_le hc hs ω) (measurable_comp_coeff hc.measurable_a hx.measurable)
      hξ.aestronglyMeasurable.aemeasurable hcont hrep
    refine h.trans_lt ?_
    have hfin := lintegral_one_add_lt_top hx.measurable hx.sq_int
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [lintegral_enorm_sq_eq hξ]
      exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
    · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
        ((tsSq_a_le hc le_rfl).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin))
    · exact ENNReal.mul_lt_top (by norm_num)
        ((tsSq_drive_le hc le_rfl).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin))

/-- The Picard step is Lipschitz for the `E sup |·|²` distance (with Gronwall rate). -/
theorem supSq_picardStep_sub_le {x y : ℝ → Ω → ℝ} (hx : IsRegProc 𝓕 P t₀ T x)
    (hy : IsRegProc 𝓕 P t₀ T y) :
    ∀ t ∈ Set.Icc t₀ T, supSq P (fun s ω => picardStep W 𝓕 P a b t₀ T ξ x s ω -
        picardStep W 𝓕 P a b t₀ T ξ y s ω) t₀ t ≤
      ENNReal.ofReal (sdeRate K (T - t₀)) *
        ∫⁻ s in Set.Ioc t₀ t, supSq P (fun s ω => x s ω - y s ω) t₀ s := by
  intro t ht
  have := hW.isProbabilityMeasure
  have hd : 0 ≤ T - t₀ := sub_nonneg.mpr htT
  have hx' := hx.picard hW hc ht₀ htT hξm hξ
  have hy' := hy.picard hW hc ht₀ htT hξm hξ
  have h := sup_sq_sub_le hW (A₁ := fun s ω => a (x s ω) s) (A₂ := fun s ω => a (y s ω) s)
    ht₀ ht (isItoIntegrand_drive hc ht₀ hx.measurable hx.adapted hx.sq_int)
    (isItoIntegrand_drive hc ht₀ hy.measurable hy.adapted hy.sq_int)
    (fun s ω hs => drive_of_le hc hs ω) (fun s ω hs => drive_of_le hc hs ω)
    (measurable_comp_coeff hc.measurable_a hx.measurable)
    (measurable_comp_coeff hc.measurable_a hy.measurable)
    (hx.cont.mono fun ω hω => hc.driftCoeff.integrableOn hx.measurable hω)
    (hy.cont.mono fun ω hω => hc.driftCoeff.integrableOn hy.measurable hω)
    hξ.aestronglyMeasurable.aemeasurable hξ.aestronglyMeasurable.aemeasurable
    hx'.1.cont hy'.1.cont hx'.2 hy'.2
  refine h.trans ?_
  simp only [sub_self, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    lintegral_zero, mul_zero, zero_add]
  set X := ∫⁻ s in Set.Ioc t₀ t, supSq P (fun s ω => x s ω - y s ω) t₀ s
  have hX : tsSq P (fun s ω => x s ω - y s ω) t₀ t ≤ X := tsSq_le_lintegral_supSq _ t₀ t
  calc 3 * ENNReal.ofReal (t - t₀) *
        tsSq P (fun s ω => a (x s ω) s - a (y s ω) s) t₀ t +
        12 * tsSq P (fun s ω => drive t₀ b x s ω - drive t₀ b y s ω) t₀ t
      ≤ 3 * ENNReal.ofReal (T - t₀) * (ENNReal.ofReal (K ^ 2) * X) +
          12 * (ENNReal.ofReal (K ^ 2) * X) := by
        gcongr
        · linarith [ht.2]
        · exact (tsSq_a_sub_le hc ht.2).trans (by gcongr)
        · exact (tsSq_drive_sub_le hc ht.2).trans (by gcongr)
    _ = ENNReal.ofReal (sdeRate K (T - t₀)) * X := by
        rw [sdeRate, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity)
          (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num
        ring

/-- The initial iterate `x₀ = ξ` is regular. -/
lemma isRegProc_const : IsRegProc 𝓕 P t₀ T (fun _ ω => ξ ω) where
  measurable := (measurable_xi hW hc ht₀ htT hξm hξ).comp measurable_snd
  adapted t ht := hξm.mono (𝓕.mono ht.1)
  cont := Eventually.of_forall fun _ => continuousOn_const
  supSq_lt_top := by
    have := hW.isProbabilityMeasure
    have e : supSq P (fun _ ω => ξ ω) t₀ T = ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P := by
      unfold supSq
      congr 1; funext ω
      have hne : (Set.Icc t₀ T).Nonempty := Set.nonempty_Icc.mpr htT
      rw [show (⨆ u ∈ Set.Icc t₀ T, ‖ξ ω‖ₑ) = ‖ξ ω‖ₑ from
        le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le t₀ ⟨le_rfl, htT⟩ le_rfl)]
    rw [e, lintegral_enorm_sq_eq hξ]
    exact ENNReal.ofReal_lt_top

/-- All Picard iterates are regular. -/
theorem isRegProc_picardSeq (n : ℕ) : IsRegProc 𝓕 P t₀ T (picardSeq W 𝓕 P a b t₀ T ξ n) := by
  induction n with
  | zero => exact isRegProc_const hW hc ht₀ htT hξm hξ
  | succ n ih => exact (ih.picard hW hc ht₀ htT hξm hξ).1

end Step

/-! ### Convergence of the Picard iterates -/

/-- `sup_{t₀ ≤ u ≤ T} |x_{n+1}(u) - x_n(u)|`. -/
def picardGap (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (a b : ℝ → ℝ → ℝ)
    (t₀ T : ℝ) (ξ : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ u ∈ Set.Icc t₀ T, ‖picardSeq W 𝓕 P a b t₀ T ξ (n + 1) u ω - picardSeq W 𝓕 P a b t₀ T ξ n u ω‖ₑ

/-- `E sup |x₁ - x₀|²`. -/
def picardM (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (a b : ℝ → ℝ → ℝ)
    (t₀ T : ℝ) (ξ : Ω → ℝ) : ℝ≥0∞ :=
  supSq P (fun s ω => picardSeq W 𝓕 P a b t₀ T ξ 1 s ω - picardSeq W 𝓕 P a b t₀ T ξ 0 s ω) t₀ T

section Converge

variable {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ T K : ℝ} {ξ : Ω → ℝ}
  (hW : IsFWiener W 𝓕 P) (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
  (hξm : StronglyMeasurable[𝓕 t₀] ξ) (hξ : MemLp ξ 2 P)
include hW hc ht₀ htT hξm hξ

lemma picardM_lt_top : picardM W 𝓕 P a b t₀ T ξ < ⊤ := by
  have h1 := isRegProc_picardSeq hW hc ht₀ htT hξm hξ 1
  have h0 := isRegProc_picardSeq hW hc ht₀ htT hξm hξ 0
  exact (IsSDESol.supSq_sub_le_two htT h1.measurable h1.cont).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) h1.supSq_lt_top,
      ENNReal.mul_lt_top (by norm_num) h0.supSq_lt_top⟩)

/-- **The Picard bound** `E sup_{[t₀, t]} |x_{n+1} - x_n|² ≤ M (L (t - t₀))ⁿ / n!`. -/
theorem supSq_picardSeq_succ_sub_le :
    ∀ n, ∀ t ∈ Set.Icc t₀ T, supSq P (fun s ω => picardSeq W 𝓕 P a b t₀ T ξ (n + 1) s ω -
      picardSeq W 𝓕 P a b t₀ T ξ n s ω) t₀ t ≤
        picardM W 𝓕 P a b t₀ T ξ * gronR (sdeRate K (T - t₀)) t₀ n t :=
  iterate_bound_ennreal (Δ := fun n t => supSq P (fun s ω => picardSeq W 𝓕 P a b t₀ T ξ (n + 1) s ω -
      picardSeq W 𝓕 P a b t₀ T ξ n s ω) t₀ t) (sdeRate_nonneg (sub_nonneg.mpr htT))
    (fun _ ht => supSq_mono_right ht.2)
    (fun n t ht => supSq_picardStep_sub_le hW hc ht₀ htT hξm hξ
      (isRegProc_picardSeq hW hc ht₀ htT hξm hξ (n + 1))
      (isRegProc_picardSeq hW hc ht₀ htT hξm hξ n) t ht)

lemma aemeasurable_picardGap (n : ℕ) : AEMeasurable (picardGap W 𝓕 P a b t₀ T ξ n) P := by
  have h1 := isRegProc_picardSeq hW hc ht₀ htT hξm hξ (n + 1)
  have h0 := isRegProc_picardSeq hW hc ht₀ htT hξm hξ n
  exact aemeasurable_iSup_Icc (Y := fun s ω => picardSeq W 𝓕 P a b t₀ T ξ (n + 1) s ω -
      picardSeq W 𝓕 P a b t₀ T ξ n s ω)
    (fun u => (measurable_of_uncurry h1.measurable u).sub (measurable_of_uncurry h0.measurable u))
    htT ((h1.cont.and h0.cont).mono fun ω hω => hω.1.sub hω.2)

/-- `E (∑_{k ≥ n} sup |x_{k+1} - x_k|)² ≤ 2 M e^{2 L (T - t₀)} (L (T - t₀))ⁿ / n!`. -/
theorem lintegral_tsum_picardGap_sq_le (n : ℕ) :
    ∫⁻ ω, (∑' k, picardGap W 𝓕 P a b t₀ T ξ (k + n) ω) ^ 2 ∂P ≤
      2 * picardM W 𝓕 P a b t₀ T ξ *
        ENNReal.ofReal (Real.exp (2 * (sdeRate K (T - t₀) * (T - t₀)))) *
        ENNReal.ofReal ((sdeRate K (T - t₀) * (T - t₀)) ^ n / n.factorial) := by
  set c := sdeRate K (T - t₀) * (T - t₀)
  have hc0 : 0 ≤ c := mul_nonneg (sdeRate_nonneg (sub_nonneg.mpr htT)) (sub_nonneg.mpr htT)
  set M := picardM W 𝓕 P a b t₀ T ξ
  have hg := aemeasurable_picardGap hW hc ht₀ htT hξm hξ
  have hk : ∀ m, ∫⁻ ω, picardGap W 𝓕 P a b t₀ T ξ m ω ^ 2 ∂P ≤
      M * ENNReal.ofReal (c ^ m / m.factorial) :=
    fun m => supSq_picardSeq_succ_sub_le hW hc ht₀ htT hξm hξ m T ⟨htT, le_rfl⟩
  calc ∫⁻ ω, (∑' k, picardGap W 𝓕 P a b t₀ T ξ (k + n) ω) ^ 2 ∂P
      ≤ ∫⁻ ω, 2 * ∑' k, 2 ^ k * picardGap W 𝓕 P a b t₀ T ξ (k + n) ω ^ 2 ∂P :=
        lintegral_mono fun ω => tsum_sq_le_two_mul _
    _ = 2 * ∑' k, 2 ^ k * ∫⁻ ω, picardGap W 𝓕 P a b t₀ T ξ (k + n) ω ^ 2 ∂P := by
        rw [lintegral_const_mul' _ _ (by norm_num),
          lintegral_tsum fun k => ((hg (k + n)).pow_const 2).const_mul _]
        congr 1
        refine tsum_congr fun k => ?_
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (by norm_num))]
    _ ≤ 2 * ∑' k : ℕ, 2 ^ k * (M * (ENNReal.ofReal (c ^ k / k.factorial) *
          ENNReal.ofReal (c ^ n / n.factorial))) := by
        gcongr with k
        refine (hk (k + n)).trans ?_
        gcongr
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (pow_div_factorial_add_le hc0 k n)
    _ = 2 * M * ENNReal.ofReal (c ^ n / n.factorial) *
          ∑' k : ℕ, 2 ^ k * ENNReal.ofReal (c ^ k / k.factorial) := by
        have e : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k * (M * (ENNReal.ofReal (c ^ k / k.factorial) *
            ENNReal.ofReal (c ^ n / n.factorial))) = (M * ENNReal.ofReal (c ^ n / n.factorial)) *
            (2 ^ k * ENNReal.ofReal (c ^ k / k.factorial)) := fun k => by ring
        simp_rw [e, ENNReal.tsum_mul_left]
        ring
    _ ≤ 2 * M * ENNReal.ofReal (c ^ n / n.factorial) * ENNReal.ofReal (Real.exp (2 * c)) := by
        gcongr
        exact tsum_two_pow_mul_le_exp hc0
    _ = _ := by ring

omit hc ht₀ htT hξm hξ in
lemma sdeSol_def (t : ℝ) (ω : Ω) : sdeSol W 𝓕 P a b t₀ T ξ t ω =
    limUnder atTop fun n => picardSeq W 𝓕 P a b t₀ T ξ n t ω := rfl

/-- Almost surely, the Picard iterates converge uniformly on `[t₀, T]` to `sdeSol`, which is
continuous there, with the tail bound `|x(t) - x_n(t)| ≤ ∑_{k ≥ n} sup |x_{k+1} - x_k|`. -/
theorem ae_sdeSol_spec : ∀ᵐ ω ∂P, ContinuousOn (fun t => sdeSol W 𝓕 P a b t₀ T ξ t ω)
    (Set.Icc t₀ T) ∧ ∀ t ∈ Set.Icc t₀ T, ∀ n,
      ‖sdeSol W 𝓕 P a b t₀ T ξ t ω - picardSeq W 𝓕 P a b t₀ T ξ n t ω‖ₑ ≤
        ∑' k, picardGap W 𝓕 P a b t₀ T ξ (k + n) ω := by
  have hg := aemeasurable_picardGap hW hc ht₀ htT hξm hξ
  have hS : AEMeasurable (fun ω => (∑' k, picardGap W 𝓕 P a b t₀ T ξ (k + 0) ω) ^ 2) P :=
    (AEMeasurable.ennreal_tsum fun k => hg (k + 0)).pow_const 2
  have hfin := (lintegral_tsum_picardGap_sq_le hW hc ht₀ htT hξm hξ 0).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
      (picardM_lt_top hW hc ht₀ htT hξm hξ)) ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)
  have hcont : ∀ᵐ ω ∂P, ∀ n, ContinuousOn (fun t => picardSeq W 𝓕 P a b t₀ T ξ n t ω)
      (Set.Icc t₀ T) := ae_all_iff.mpr fun n => (isRegProc_picardSeq hW hc ht₀ htT hξm hξ n).cont
  filter_upwards [ae_lt_top' hS hfin.ne, hcont] with ω h1 h2
  have hne : ∑' k, picardGap W 𝓕 P a b t₀ T ξ k ω ≠ ⊤ := by
    intro h
    simp only [add_zero, h] at h1
    simp at h1
  exact limUnder_tail_of_tsum_ne_top (f := fun n t => picardSeq W 𝓕 P a b t₀ T ξ n t ω) h2 hne

/-- **Mean-square convergence of the Picard iterates**:
`E sup_{[t₀, T]} |x - x_n|² ≤ 2 M e^{2 L (T - t₀)} (L (T - t₀))ⁿ / n!`. -/
theorem supSq_sdeSol_sub_le (n : ℕ) :
    supSq P (fun s ω => sdeSol W 𝓕 P a b t₀ T ξ s ω - picardSeq W 𝓕 P a b t₀ T ξ n s ω) t₀ T ≤
      2 * picardM W 𝓕 P a b t₀ T ξ *
        ENNReal.ofReal (Real.exp (2 * (sdeRate K (T - t₀) * (T - t₀)))) *
        ENNReal.ofReal ((sdeRate K (T - t₀) * (T - t₀)) ^ n / n.factorial) := by
  refine le_trans ?_ (lintegral_tsum_picardGap_sq_le hW hc ht₀ htT hξm hξ n)
  refine lintegral_mono_ae ?_
  filter_upwards [ae_sdeSol_spec hW hc ht₀ htT hξm hξ] with ω hω
  exact pow_le_pow_left' (iSup₂_le fun t ht => hω.2 t ht n) 2

/-- The limit of the Picard iterates is a regular process. -/
theorem isRegProc_sdeSol : IsRegProc 𝓕 P t₀ T (sdeSol W 𝓕 P a b t₀ T ξ) := by
  have hreg := isRegProc_picardSeq hW hc ht₀ htT hξm hξ
  have hm : Measurable (Function.uncurry (sdeSol W 𝓕 P a b t₀ T ξ)) :=
    (StronglyMeasurable.limUnder (l := atTop)
      fun n => (hreg n).measurable.stronglyMeasurable).measurable
  refine ⟨hm, fun t ht => stronglyMeasurable_limUnder_nat fun n => (hreg n).adapted t ht,
    (ae_sdeSol_spec hW hc ht₀ htT hξm hξ).mono fun ω hω => hω.1, ?_⟩
  have h := IsSDESol.supSq_sub_le_two (P := P) (x := picardSeq W 𝓕 P a b t₀ T ξ 0)
    (y := fun s ω => picardSeq W 𝓕 P a b t₀ T ξ 0 s ω - sdeSol W 𝓕 P a b t₀ T ξ s ω)
    htT (hreg 0).measurable (hreg 0).cont
  have e : (fun s ω => picardSeq W 𝓕 P a b t₀ T ξ 0 s ω -
      (fun s ω => picardSeq W 𝓕 P a b t₀ T ξ 0 s ω - sdeSol W 𝓕 P a b t₀ T ξ s ω) s ω) =
      sdeSol W 𝓕 P a b t₀ T ξ := by funext s ω; ring
  rw [e] at h
  refine h.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (hreg 0).supSq_lt_top,
    ENNReal.mul_lt_top (by norm_num) ?_⟩)
  have h0 := supSq_sdeSol_sub_le hW hc ht₀ htT hξm hξ 0
  have e2 : supSq P (fun s ω => picardSeq W 𝓕 P a b t₀ T ξ 0 s ω - sdeSol W 𝓕 P a b t₀ T ξ s ω)
      t₀ T = supSq P (fun s ω => sdeSol W 𝓕 P a b t₀ T ξ s ω - picardSeq W 𝓕 P a b t₀ T ξ 0 s ω)
      t₀ T := by
    unfold supSq; simp_rw [enorm_sub_rev]
  rw [e2]
  exact h0.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
      (picardM_lt_top hW hc ht₀ htT hξm hξ)) ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)

/-- The limit is a fixed point of the Picard map, up to indistinguishability. -/
theorem sdeSol_fixed : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc t₀ T, sdeSol W 𝓕 P a b t₀ T ξ t ω =
    picardStep W 𝓕 P a b t₀ T ξ (sdeSol W 𝓕 P a b t₀ T ξ) t ω := by
  have hreg := isRegProc_picardSeq hW hc ht₀ htT hξm hξ
  have hx := isRegProc_sdeSol hW hc ht₀ htT hξm hξ
  have hx' := hx.picard hW hc ht₀ htT hξm hξ
  set x := sdeSol W 𝓕 P a b t₀ T ξ
  set c := sdeRate K (T - t₀) * (T - t₀)
  set C := 2 * picardM W 𝓕 P a b t₀ T ξ *
    ENNReal.ofReal (Real.exp (2 * (sdeRate K (T - t₀) * (T - t₀))))
  have hC : C ≠ ⊤ := (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
    (picardM_lt_top hW hc ht₀ htT hξm hξ)) ENNReal.ofReal_lt_top).ne
  have hbound : ∀ n, supSq P (fun s ω => x s ω - picardStep W 𝓕 P a b t₀ T ξ x s ω) t₀ T ≤
      2 * (C * ENNReal.ofReal (c ^ (n + 1) / (n + 1).factorial)) +
      2 * (ENNReal.ofReal (sdeRate K (T - t₀)) * (ENNReal.ofReal (T - t₀) *
        (C * ENNReal.ofReal (c ^ n / n.factorial)))) := by
    intro n
    refine (supSq_sub_triangle (y := picardSeq W 𝓕 P a b t₀ T ξ (n + 1)) htT hx.measurable
      (hreg (n + 1)).measurable hx.cont (hreg (n + 1)).cont).trans ?_
    gcongr
    · exact supSq_sdeSol_sub_le hW hc ht₀ htT hξm hξ (n + 1)
    · refine (supSq_picardStep_sub_le hW hc ht₀ htT hξm hξ hx (hreg n) T ⟨htT, le_rfl⟩).trans ?_
      gcongr
      exact (lintegral_supSq_le le_rfl).trans
        (mul_le_mul_right (supSq_sdeSol_sub_le hW hc ht₀ htT hξm hξ n) _)
  have hlim : Tendsto (fun n : ℕ => 2 * (C * ENNReal.ofReal (c ^ (n + 1) / (n + 1).factorial)) +
      2 * (ENNReal.ofReal (sdeRate K (T - t₀)) * (ENNReal.ofReal (T - t₀) *
        (C * ENNReal.ofReal (c ^ n / n.factorial))))) atTop (𝓝 0) := by
    have h1 := tendsto_ofReal_pow_div_factorial c
    have h2 := (tendsto_add_atTop_iff_nat 1).mpr h1
    have hA := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h2 (Or.inr hC))
      (a := 2) (Or.inr (by norm_num))
    have hB := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h1 (Or.inr hC))
        (a := ENNReal.ofReal (T - t₀)) (Or.inr ENNReal.ofReal_ne_top))
        (a := ENNReal.ofReal (sdeRate K (T - t₀))) (Or.inr ENNReal.ofReal_ne_top))
      (a := 2) (Or.inr (by norm_num))
    simpa using hA.add hB
  have h0 : supSq P (fun s ω => x s ω - picardStep W 𝓕 P a b t₀ T ξ x s ω) t₀ T = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) (zero_le _)
  exact ae_eq_of_supSq_sub_eq_zero htT hx.measurable hx'.1.measurable hx.cont hx'.1.cont h0

/-- **Existence (Gardiner §4.3.1)**: under the Lipschitz and growth conditions (4.3.10)–(4.3.11)
on `[t₀, T]`, for every horizon `T ≥ t₀ ≥ 0` and every square integrable, `𝓕 t₀`-measurable
initial value `ξ`, the limit `sdeSol` of the Picard iterates is a continuous adapted solution of
(4.3.4) on `[t₀, T]`. -/
theorem isSDESol_sdeSol : IsSDESol W 𝓕 P a b t₀ T ξ (sdeSol W 𝓕 P a b t₀ T ξ) := by
  have hx := isRegProc_sdeSol hW hc ht₀ htT hξm hξ
  have hx' := hx.picard hW hc ht₀ htT hξm hξ
  refine ⟨hx.measurable, hx.adapted, hx.cont, hx.sq_int, fun t ht => ?_⟩
  filter_upwards [sdeSol_fixed hW hc ht₀ htT hξm hξ, hx'.2 t ht] with ω h1 h2
  rw [h1 t ht, h2]

/-- **Existence and uniqueness (Gardiner §4.3.1)**: there is a continuous adapted solution of
(4.3.4) on `[t₀, T]`, and any two solutions are indistinguishable. -/
theorem existsUnique_sdeSol : ∃ x, IsSDESol W 𝓕 P a b t₀ T ξ x ∧
    ∀ y, IsSDESol W 𝓕 P a b t₀ T ξ y → ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc t₀ T, y t ω = x t ω :=
  ⟨_, isSDESol_sdeSol hW hc ht₀ htT hξm hξ, fun _ hy =>
    hy.unique hW (isSDESol_sdeSol hW hc ht₀ htT hξm hξ) hc ht₀ htT hξ⟩

end Converge

end Gardiner.Ito.StochDE
