/-
# The Euler–Maruyama (Cauchy–Euler) scheme

Gardiner §4.3.1 (4.3.5)–(4.3.9) and §10.1.4 (10.1.13)–(10.1.17).  On the uniform grid
`t_i = t₀ + i τ`, the Euler scheme is
`x_{i+1} = x_i + a(x_i, t_i) τ + b(x_i, t_i) (W(t_{i+1}) - W(t_i))`, `x_0 = ξ`  (`eulerSeq`).

For the error analysis we use the continuous-time interpolation (`eulerInterp`)
`X(u) = ξ + ∫_{t₀}^u a(x_{k(s)}, t_{k(s)}) ds + Σ_i b(x_i, t_i) (W(t_{i+1} ∧ u) - W(t_i ∧ u))`,
which satisfies `X(t_k) = x_k` (`eulerInterp_grid`) and is the Itô process with the step
coefficients (`eulerInterp_eq`).
-/
import SHSLib.Gardiner.Ito.StochDE.Picard
import SHSLib.Gardiner.Ito.StochDE.ItoIncr

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- The uniform grid `t_i = t₀ + i τ`. -/
def eulerGrid (t₀ τ : ℝ) (i : ℕ) : ℝ := t₀ + i * τ

/-- **The Euler–Maruyama scheme (4.3.6) / (10.1.15)**:
`x_{i+1} = x_i + a(x_i, t_i) τ + b(x_i, t_i) ΔW_i`, `x_0 = ξ`. -/
def eulerSeq (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ → ℝ) (t₀ τ : ℝ) (ξ : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => ξ
  | i + 1 => fun ω => eulerSeq W a b t₀ τ ξ i ω +
      a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) * τ +
      b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) *
        (W (eulerGrid t₀ τ (i + 1)) ω - W (eulerGrid t₀ τ i) ω)

/-- The step drift `s ↦ a(x_{k(s)}, t_{k(s)})` on `(t₀, t_N]`. -/
def eulerDrift (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ → ℝ) (t₀ τ : ℝ) (ξ : Ω → ℝ) (N : ℕ) (s : ℝ)
    (ω : Ω) : ℝ :=
  ∑ i : Fin N, a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) *
    cellInd (eulerGrid t₀ τ i) (eulerGrid t₀ τ (i + 1)) s

/-- The step diffusion `s ↦ b(x_{k(s)}, t_{k(s)})` on `(t₀, t_N]`. -/
def eulerNoise (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ → ℝ) (t₀ τ : ℝ) (ξ : Ω → ℝ) (N : ℕ) (s : ℝ)
    (ω : Ω) : ℝ :=
  ∑ i : Fin N, b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) *
    cellInd (eulerGrid t₀ τ i) (eulerGrid t₀ τ (i + 1)) s

/-- The running sum `Σ_i b(x_i, t_i) (W(t_{i+1} ∧ u) - W(t_i ∧ u))`. -/
def eulerNoiseRun (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ → ℝ) (t₀ τ : ℝ) (ξ : Ω → ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω) : ℝ :=
  ∑ i : Fin N, b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) *
    (W (min (eulerGrid t₀ τ (i + 1)) u) ω - W (min (eulerGrid t₀ τ i) u) ω)

/-- **The continuous Euler interpolation**
`X(u) = ξ + ∫_{t₀}^u a(x_{k(s)}, t_{k(s)}) ds + Σ_i b(x_i, t_i) (W(t_{i+1} ∧ u) - W(t_i ∧ u))`. -/
def eulerInterp (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ → ℝ) (t₀ τ : ℝ) (ξ : Ω → ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω) : ℝ :=
  ξ ω + (∫ s in t₀..u, eulerDrift W a b t₀ τ ξ N s ω) + eulerNoiseRun W a b t₀ τ ξ N u ω

/-! ### Grid arithmetic -/

section Grid

variable {t₀ τ : ℝ}

lemma eulerGrid_succ (t₀ τ : ℝ) (i : ℕ) : eulerGrid t₀ τ (i + 1) = eulerGrid t₀ τ i + τ := by
  unfold eulerGrid; push_cast; ring

lemma eulerGrid_mono (hτ : 0 ≤ τ) {i j : ℕ} (h : i ≤ j) : eulerGrid t₀ τ i ≤ eulerGrid t₀ τ j := by
  unfold eulerGrid
  have : (i : ℝ) ≤ j := by exact_mod_cast h
  nlinarith

lemma le_eulerGrid (hτ : 0 ≤ τ) (i : ℕ) : t₀ ≤ eulerGrid t₀ τ i := by
  simpa [eulerGrid] using eulerGrid_mono (t₀ := t₀) hτ (Nat.zero_le i)

lemma eulerGrid_zero : eulerGrid t₀ τ 0 = t₀ := by simp [eulerGrid]

end Grid

/-! ### Measurability and integrability of the scheme -/

section Scheme

variable {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ τ K : ℝ} {N : ℕ} {ξ : Ω → ℝ}

omit [MeasurableSpace Ω] in
lemma eulerSeq_zero (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ → ℝ) (t₀ τ : ℝ) (ξ : Ω → ℝ) :
    eulerSeq W a b t₀ τ ξ 0 = ξ := rfl

omit [MeasurableSpace Ω] in
lemma eulerSeq_succ (W : ℝ → Ω → ℝ) (a b : ℝ → ℝ → ℝ) (t₀ τ : ℝ) (ξ : Ω → ℝ) (i : ℕ) (ω : Ω) :
    eulerSeq W a b t₀ τ ξ (i + 1) ω = eulerSeq W a b t₀ τ ξ i ω +
      a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) * τ +
      b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) *
        (W (eulerGrid t₀ τ (i + 1)) ω - W (eulerGrid t₀ τ i) ω) := rfl

lemma stronglyMeasurable_comp_coeff {m : MeasurableSpace Ω} {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) {X : Ω → ℝ} (hX : StronglyMeasurable[m] X) (t : ℝ) :
    StronglyMeasurable[m] (fun ω => F (X ω) t) :=
  (Measurable.comp (g := Function.uncurry F) (f := fun ω => (X ω, t)) hF
    (hX.measurable.prodMk measurable_const)).stronglyMeasurable

/-- The Euler iterates are adapted: `x_i` is `𝓕 t_i`-measurable. -/
lemma eulerSeq_adapted (hW : IsFWiener W 𝓕 P) (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) (ht₀ : 0 ≤ t₀) (hτ : 0 ≤ τ)
    (hξm : StronglyMeasurable[𝓕 t₀] ξ) :
    ∀ i, StronglyMeasurable[𝓕 (eulerGrid t₀ τ i)] (eulerSeq W a b t₀ τ ξ i) := by
  intro i
  induction i with
  | zero => simpa [eulerGrid_zero] using hξm
  | succ i ih =>
    have hle : eulerGrid t₀ τ i ≤ eulerGrid t₀ τ (i + 1) := eulerGrid_mono hτ (Nat.le_succ i)
    have h0 : 0 ≤ eulerGrid t₀ τ i := ht₀.trans (le_eulerGrid hτ i)
    have ih' := ih.mono (𝓕.mono hle)
    have e : eulerSeq W a b t₀ τ ξ (i + 1) = fun ω => eulerSeq W a b t₀ τ ξ i ω +
        a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) * τ +
        b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) *
          (W (eulerGrid t₀ τ (i + 1)) ω - W (eulerGrid t₀ τ i) ω) := rfl
    rw [e]
    exact (ih'.add ((stronglyMeasurable_comp_coeff ha ih' _).mul_const τ)).add
      ((stronglyMeasurable_comp_coeff hb ih' _).mul ((hW.adapted _ (h0.trans hle)).sub
        ((hW.adapted _ h0).mono (𝓕.mono hle))))

lemma memLp_coeff_of_growth [IsFiniteMeasure P] {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) {X : Ω → ℝ} (hX : MemLp X 2 P)
    (hXm : Measurable X) {t C : ℝ} (hg : ∀ y, |F y t| ≤ C * (1 + |y|)) :
    MemLp (fun ω => F (X ω) t) 2 P := by
  have hC : 0 ≤ C := by have := hg 0; simp at this; linarith [abs_nonneg (F 0 t)]
  have hG : MemLp (fun ω => C * (1 + |X ω|)) 2 P := by
    have h1 : MemLp (fun ω => |X ω|) 2 P := hX.abs
    exact ((memLp_const (1 : ℝ)).add h1).const_mul C
  refine hG.of_le (stronglyMeasurable_comp_coeff hF hXm.stronglyMeasurable t).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * (1 + |X ω|))]
  exact hg _

/-- The Euler iterates are square integrable (up to the final time `t_N ≤ T`). -/
lemma eulerSeq_memLp {T : ℝ} (hW : IsFWiener W 𝓕 P) (hc : SDECoeffs a b t₀ T K) (ht₀ : 0 ≤ t₀)
    (hτ : 0 ≤ τ) (hξm : StronglyMeasurable[𝓕 t₀] ξ) (hξ : MemLp ξ 2 P) {n : ℕ}
    (hn : eulerGrid t₀ τ n ≤ T) : ∀ i ≤ n, MemLp (eulerSeq W a b t₀ τ ξ i) 2 P := by
  have := hW.isProbabilityMeasure
  have had := eulerSeq_adapted hW hc.measurable_a hc.measurable_b ht₀ hτ hξm
  intro i
  induction i with
  | zero => intro _; exact hξ
  | succ i ih =>
    intro hi
    have hX := ih (Nat.le_of_succ_le hi)
    have hmem : eulerGrid t₀ τ i ∈ Set.Icc t₀ T :=
      ⟨le_eulerGrid hτ i, (eulerGrid_mono hτ (Nat.le_of_succ_le hi)).trans hn⟩
    have hXm : Measurable (eulerSeq W a b t₀ τ ξ i) := ((had i).mono (𝓕.le _)).measurable
    have h1 := memLp_coeff_of_growth hc.measurable_a hX hXm (hc.abs_a_le hmem)
    have hle : eulerGrid t₀ τ i ≤ eulerGrid t₀ τ (i + 1) := eulerGrid_mono hτ (Nat.le_succ i)
    have h2 := hW.memLp_mul_incr (ht₀.trans (le_eulerGrid hτ i)) hle
      (stronglyMeasurable_comp_coeff hc.measurable_b (had i) _)
      (memLp_coeff_of_growth hc.measurable_b hX hXm (hc.abs_b_le hmem))
    exact (hX.add (h1.mul_const τ)).add h2

end Scheme

/-! ### Cells of the grid -/

section Cells

variable {t₀ τ : ℝ}

/-- Every `s ∈ (t₀, t_N]` lies in a cell `(t_k, t_{k+1}]` with `k < N`. -/
lemma exists_gridCell (hτ : 0 < τ) {N : ℕ} {s : ℝ} (hs : s ∈ Set.Ioc t₀ (eulerGrid t₀ τ N)) :
    ∃ k : ℕ, k < N ∧ eulerGrid t₀ τ k < s ∧ s ≤ eulerGrid t₀ τ (k + 1) := by
  set q := (s - t₀) / τ
  have hq : 0 < q := div_pos (sub_pos.mpr hs.1) hτ
  have hqN : q ≤ N := by
    rw [div_le_iff₀ hτ]; have := hs.2; unfold eulerGrid at this; linarith
  set m := ⌈q⌉₊
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨m - 1, by have := Nat.ceil_le.mpr hqN; omega, ?_, ?_⟩
  · have h1 : ((m - 1 : ℕ) : ℝ) < q := by
      have := Nat.ceil_lt_add_one hq.le
      rw [Nat.cast_sub hm1]; push_cast; linarith
    unfold eulerGrid
    have : ((m - 1 : ℕ) : ℝ) * τ < q * τ := mul_lt_mul_of_pos_right h1 hτ
    rw [div_mul_cancel₀ _ hτ.ne'] at this
    linarith
  · have h1 : q ≤ ((m - 1 + 1 : ℕ) : ℝ) := by
      rw [Nat.sub_add_cancel hm1]; exact Nat.le_ceil q
    unfold eulerGrid
    have : q * τ ≤ ((m - 1 + 1 : ℕ) : ℝ) * τ := mul_le_mul_of_nonneg_right h1 hτ.le
    rw [div_mul_cancel₀ _ hτ.ne'] at this
    push_cast at this ⊢
    linarith

/-- On the cell `(t_k, t_{k+1}]`, a step function `Σ_i v_i 1_{(t_i, t_{i+1}]}` equals `v_k`. -/
lemma sum_cellInd_eq (hτ : 0 < τ) {N k : ℕ} (hk : k < N) {s : ℝ} (hs1 : eulerGrid t₀ τ k < s)
    (hs2 : s ≤ eulerGrid t₀ τ (k + 1)) (v : ℕ → ℝ) :
    ∑ i : Fin N, v i * cellInd (eulerGrid t₀ τ i) (eulerGrid t₀ τ (i + 1)) s = v k := by
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin N)]
  · simp [cellInd_mem (show s ∈ Set.Ioc _ _ from ⟨hs1, hs2⟩)]
  · intro i _ hik
    have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
    rw [cellInd_notMem, mul_zero]
    rintro ⟨h1, h2⟩
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := eulerGrid_mono (t₀ := t₀) hτ.le (show (i : ℕ) + 1 ≤ k by omega)
      linarith
    · have := eulerGrid_mono (t₀ := t₀) hτ.le (show k + 1 ≤ (i : ℕ) by omega)
      linarith
  · simp

lemma integral_cellInd_grid (hτ : 0 < τ) (i k : ℕ) :
    ∫ s in t₀..eulerGrid t₀ τ k, cellInd (eulerGrid t₀ τ i) (eulerGrid t₀ τ (i + 1)) s =
      if i < k then τ else 0 := by
  rw [intervalIntegral.integral_of_le (le_eulerGrid hτ.le k)]
  unfold cellInd
  rw [setIntegral_indicator measurableSet_Ioc]
  split_ifs with h
  · rw [Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc (le_eulerGrid hτ.le i)
      (eulerGrid_mono hτ.le (show i + 1 ≤ k by omega)))]
    simp [Real.volume_real_Ioc, eulerGrid_succ, hτ.le]
  · have hki : eulerGrid t₀ τ k ≤ eulerGrid t₀ τ i := eulerGrid_mono hτ.le (by omega)
    rw [Set.Ioc_inter_Ioc, Set.Ioc_eq_empty]
    · simp
    · have : eulerGrid t₀ τ i ≤ max t₀ (eulerGrid t₀ τ i) := le_max_right _ _
      intro hlt
      have := min_le_left (eulerGrid t₀ τ k) (eulerGrid t₀ τ (i + 1))
      linarith

lemma sum_fin_ite_lt {N k : ℕ} (hk : k ≤ N) (f : ℕ → ℝ) :
    ∑ i : Fin N, (if (i : ℕ) < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then f i else 0) N, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega

end Cells

/-! ### The interpolation on the grid -/

section Interp

variable {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ → ℝ} {t₀ τ K : ℝ} {N : ℕ} {ξ : Ω → ℝ}

omit [MeasurableSpace Ω] in
lemma eulerSeq_eq_sum (k : ℕ) (ω : Ω) : eulerSeq W a b t₀ τ ξ k ω = ξ ω +
    ∑ i ∈ Finset.range k, (a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) * τ +
      b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) *
        (W (eulerGrid t₀ τ (i + 1)) ω - W (eulerGrid t₀ τ i) ω)) := by
  induction k with
  | zero => simp [eulerSeq_zero]
  | succ k ih => rw [eulerSeq_succ, Finset.sum_range_succ]; linarith

omit [MeasurableSpace Ω] in
lemma integrable_eulerDrift (N : ℕ) (ω : Ω) :
    Integrable (fun s => eulerDrift W a b t₀ τ ξ N s ω) := by
  unfold eulerDrift
  exact integrable_finset_sum _ fun i _ => (integrable_cellInd _ _).const_mul _

omit [MeasurableSpace Ω] in
/-- **The interpolation agrees with the Euler scheme on the grid**: `X(t_k) = x_k` for `k ≤ N`. -/
theorem eulerInterp_grid (hτ : 0 < τ) {k : ℕ} (hk : k ≤ N) (ω : Ω) :
    eulerInterp W a b t₀ τ ξ N (eulerGrid t₀ τ k) ω = eulerSeq W a b t₀ τ ξ k ω := by
  have hD : ∫ s in t₀..eulerGrid t₀ τ k, eulerDrift W a b t₀ τ ξ N s ω =
      ∑ i ∈ Finset.range k, a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) * τ := by
    unfold eulerDrift
    rw [intervalIntegral.integral_finset_sum fun i _ =>
      ((integrable_cellInd _ _).const_mul _).intervalIntegrable]
    simp_rw [intervalIntegral.integral_const_mul, integral_cellInd_grid hτ, mul_ite, mul_zero]
    exact sum_fin_ite_lt hk (fun i => a (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) * τ)
  have hR : eulerNoiseRun W a b t₀ τ ξ N (eulerGrid t₀ τ k) ω =
      ∑ i ∈ Finset.range k, b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i) *
        (W (eulerGrid t₀ τ (i + 1)) ω - W (eulerGrid t₀ τ i) ω) := by
    rw [← sum_fin_ite_lt hk]
    unfold eulerNoiseRun
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [min_eq_left (eulerGrid_mono hτ.le (show (i : ℕ) + 1 ≤ k by omega)),
        min_eq_left (eulerGrid_mono hτ.le (show (i : ℕ) ≤ k by omega))]
    · rw [min_eq_right (eulerGrid_mono hτ.le (show k ≤ (i : ℕ) + 1 by omega)),
        min_eq_right (eulerGrid_mono hτ.le (show k ≤ (i : ℕ) by omega)), sub_self, mul_zero]
  rw [eulerInterp, hD, hR, eulerSeq_eq_sum, Finset.sum_add_distrib]
  ring

/-- The step diffusion is the process of an elementary integrand, whose running sum is
`eulerNoiseRun`. -/
lemma exists_eulerElem (hW : IsFWiener W 𝓕 P) (hc : SDECoeffs a b t₀ (eulerGrid t₀ τ N) K)
    (ht₀ : 0 ≤ t₀) (hτ : 0 < τ) (hξm : StronglyMeasurable[𝓕 t₀] ξ) (hξ : MemLp ξ 2 P) :
    ∃ H : ElemIntegrand 𝓕 P (Fin N), H.process = eulerNoise W a b t₀ τ ξ N ∧
      H.running W = eulerNoiseRun W a b t₀ τ ξ N ∧ H.SupportedIn (eulerGrid t₀ τ N) := by
  have := hW.isProbabilityMeasure
  have had := eulerSeq_adapted hW hc.measurable_a hc.measurable_b ht₀ hτ.le hξm
  have hmem := eulerSeq_memLp hW hc ht₀ hτ.le hξm hξ le_rfl
  refine ⟨{ left := fun i => eulerGrid t₀ τ i
            right := fun i => eulerGrid t₀ τ (i + 1)
            val := fun i ω => b (eulerSeq W a b t₀ τ ξ i ω) (eulerGrid t₀ τ i)
            left_nonneg := fun i => ht₀.trans (le_eulerGrid hτ.le _)
            left_le_right := fun i => eulerGrid_mono hτ.le (Nat.le_succ _)
            adapted := fun i => stronglyMeasurable_comp_coeff hc.measurable_b (had i) _
            memLp := fun i => memLp_coeff_of_growth hc.measurable_b (hmem i i.isLt.le)
              ((had i).mono (𝓕.le _)).measurable
              (hc.abs_b_le ⟨le_eulerGrid hτ.le _, eulerGrid_mono hτ.le i.isLt.le⟩) },
    rfl, rfl, fun i => eulerGrid_mono hτ.le i.isLt⟩

/-- **The interpolation is the Itô process with the step coefficients**:
`X(u) = ξ + ∫_{t₀}^u a(x_{k(s)}, t_{k(s)}) ds + ∫_{t₀}^u b(x_{k(s)}, t_{k(s)}) dW(s)`. -/
theorem eulerInterp_eq (hW : IsFWiener W 𝓕 P) (hc : SDECoeffs a b t₀ (eulerGrid t₀ τ N) K)
    (ht₀ : 0 ≤ t₀) (hτ : 0 < τ) (hξm : StronglyMeasurable[𝓕 t₀] ξ) (hξ : MemLp ξ 2 P) :
    ∀ u ∈ Set.Icc t₀ (eulerGrid t₀ τ N), eulerInterp W a b t₀ τ ξ N u =ᵐ[P] fun ω =>
      ξ ω + (∫ s in t₀..u, eulerDrift W a b t₀ τ ξ N s ω) +
        itoInt W 𝓕 P u (eulerNoise W a b t₀ τ ξ N) ω := by
  intro u hu
  obtain ⟨H, hp, hr, hs⟩ := exists_eulerElem hW hc ht₀ hτ hξm hξ
  have h := itoInt_process_eq_running hW H hs hu.2
  rw [hp, hr] at h
  filter_upwards [h] with ω hω
  rw [hω]; rfl

omit [MeasurableSpace Ω] in
lemma continuous_eulerInterp {ω : Ω} (hω : Continuous fun t => W t ω) :
    Continuous fun u => eulerInterp W a b t₀ τ ξ N u ω := by
  unfold eulerInterp eulerNoiseRun
  refine (continuous_const.add (intervalIntegral.continuous_primitive
    (fun _ _ => (integrable_eulerDrift N ω).intervalIntegrable) t₀)).add ?_
  refine continuous_finset_sum _ fun i _ => continuous_const.mul ?_
  exact (hω.comp (continuous_const.min continuous_id)).sub
    (hω.comp (continuous_const.min continuous_id))

end Interp

end Gardiner.Ito.StochDE
