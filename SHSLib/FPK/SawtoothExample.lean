/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 3.2 of Bect (2010): where the initial law comes into play

The hybrid dynamics on `E = [0;1]`: the state moves to the right at constant speed
`v > 0` while it is in `E⁰ = [0;1)`, and jumps instantaneously back to `0` as soon as
it hits the guard `G = {1}`.  Starting from `x ∈ [0;1)`, the `k`-th jump occurs at time
`(k - x) / v` and the pre-jump state is always `1`, so the jump measure of Eq. (7) is

  `R = Σ_{k ≥ 1} (law of ((1, (k - X₀)/v)))`.

Two initial laws are considered.

* `μ₀ = δ₀`: the jumps occur deterministically at the times `k / v`, so
  `R = Σ_{k ≥ 1} δ_{(1, k/v)}` and **no mean jump intensity exists**
  (`GSHS.Sawtooth.not_exists_meanJumpIntensity_dirac`).

* `μ₀ =` the uniform law on `[0;1]`: then, by Eqs. (9)–(11),
  `R(Γ × (0;t]) = v t δ₁(Γ)` (`GSHS.Sawtooth.uniform_apply`) and the mean jump
  intensity exists and equals `v δ₁`
  (`GSHS.Sawtooth.meanJumpIntensity_uniform`), with global mean jump intensity
  `r_t(E) = v`.

The state space is modelled inside the ambient real line; all the mass of the process
lives in `[0;1]`.
-/
import SHSLib.FPK.MeanJumpIntensity

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GSHS.Sawtooth

/-- The jump measure `R` of Eq. (7) for the constant-speed sawtooth process of
Section 3.2, started with initial law `μ₀` on `[0;1)`: the `(k+1)`-st jump happens at
time `((k+1) - x)/v` when the process starts at `x`, and the pre-jump state is `1`. -/
def jumpMeasure (v : ℝ) (μ₀ : Measure ℝ) : Measure (ℝ × ℝ) :=
  Measure.sum fun k : ℕ => Measure.map (fun x : ℝ => ((1 : ℝ), ((k : ℝ) + 1 - x) / v)) μ₀

theorem measurable_jumpMap (v : ℝ) (k : ℕ) :
    Measurable fun x : ℝ => ((1 : ℝ), ((k : ℝ) + 1 - x) / v) := by
  fun_prop

/-! ### The uniform initial law -/

/-- Eqs. (9)–(11): the expected number of jumps of the sawtooth process during `(0;t]`,
when started from the uniform law on `[0;1]`, equals `v t`.

Each summand is the length of `{x ∈ (0;1) : (k+1) - v t ≤ x}`, namely
`min 1 (max 0 (v t - k))`, and these clamped values add up to `v t`. -/
theorem tsum_clamp (y : ℝ) (hy : 0 ≤ y) :
    ∑' k : ℕ, ENNReal.ofReal (min 1 (max 0 (y - k))) = ENNReal.ofReal y := by
  classical
  set n := ⌊y⌋₊ with hn
  have hny : (n : ℝ) ≤ y := Nat.floor_le hy
  have hyn : y < n + 1 := Nat.lt_floor_add_one y
  have hzero : ∀ k ∉ Finset.range (n + 1), ENNReal.ofReal (min 1 (max 0 (y - k))) = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have hk' : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
    have hle : y - (k : ℝ) ≤ 0 := by linarith
    simp [hle]
  rw [tsum_eq_sum hzero]
  rw [← ENNReal.ofReal_sum_of_nonneg (by
    intro i _
    have : (0 : ℝ) ≤ max 0 (y - i) := le_max_left _ _
    exact le_min (by norm_num) this)]
  congr 1
  rw [Finset.sum_range_succ]
  have hpre : ∀ k ∈ Finset.range n, min 1 (max 0 (y - (k : ℝ))) = 1 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hk' : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
    have h1 : (1 : ℝ) ≤ y - k := by linarith
    have h2 : max 0 (y - (k : ℝ)) = y - k := max_eq_right (by linarith)
    rw [h2, min_eq_left h1]
  rw [Finset.sum_congr rfl hpre]
  have hlast : min 1 (max 0 (y - (n : ℝ))) = y - n := by
    have h2 : max 0 (y - (n : ℝ)) = y - n := max_eq_right (by linarith)
    rw [h2, min_eq_right (by linarith)]
  rw [hlast]
  simp

/-- The value of the jump measure on the rectangles `Γ × (0;t]`, for the uniform
initial law: `R(Γ × (0;t]) = v t · δ₁(Γ)` (Eq. (11)). -/
theorem uniform_apply {v : ℝ} (hv : 0 < v) {Γ : Set ℝ} (hΓ : MeasurableSet Γ)
    {t : ℝ} (ht : 0 ≤ t) :
    jumpMeasure v (volume.restrict (Ioo (0 : ℝ) 1)) (Γ ×ˢ Ioc (0 : ℝ) t)
      = ENNReal.ofReal (v * t) * Measure.dirac (1 : ℝ) Γ := by
  classical
  have hmeasSet : MeasurableSet (Γ ×ˢ Ioc (0 : ℝ) t) := hΓ.prod measurableSet_Ioc
  rw [jumpMeasure, Measure.sum_apply _ hmeasSet]
  have hterm : ∀ k : ℕ,
      (Measure.map (fun x : ℝ => ((1 : ℝ), ((k : ℝ) + 1 - x) / v))
        (volume.restrict (Ioo (0 : ℝ) 1))) (Γ ×ˢ Ioc (0 : ℝ) t)
        = (Measure.dirac (1 : ℝ) Γ) * ENNReal.ofReal (min 1 (max 0 (v * t - k))) := by
    intro k
    rw [Measure.map_apply (measurable_jumpMap v k) hmeasSet]
    by_cases h1 : (1 : ℝ) ∈ Γ
    · have hpre : (fun x : ℝ => ((1 : ℝ), ((k : ℝ) + 1 - x) / v)) ⁻¹' (Γ ×ˢ Ioc (0 : ℝ) t)
          ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 ∩ Ici ((k : ℝ) + 1 - v * t) := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Ioc, mem_Ioo, mem_Ici, h1,
          true_and]
        constructor
        · rintro ⟨⟨_, hle⟩, hx0, hx1⟩
          refine ⟨⟨hx0, hx1⟩, ?_⟩
          rw [div_le_iff₀ hv] at hle
          nlinarith
        · rintro ⟨⟨hx0, hx1⟩, hxge⟩
          have hkx : 0 < (k : ℝ) + 1 - x := by
            have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
            linarith
          refine ⟨⟨by positivity, ?_⟩, hx0, hx1⟩
          rw [div_le_iff₀ hv]
          nlinarith
      rw [Measure.restrict_apply' measurableSet_Ioo, hpre]
      have hvol : volume (Ioo (0 : ℝ) 1 ∩ Ici ((k : ℝ) + 1 - v * t))
          = ENNReal.ofReal (min 1 (max 0 (v * t - k))) := by
        rcases le_or_gt ((k : ℝ) + 1 - v * t) 0 with hle | hgt
        · have hset : Ioo (0 : ℝ) 1 ∩ Ici ((k : ℝ) + 1 - v * t) = Ioo (0 : ℝ) 1 := by
            ext x
            simp only [mem_inter_iff, mem_Ioo, mem_Ici, and_iff_left_iff_imp]
            rintro ⟨hx0, _⟩
            linarith
          rw [hset, Real.volume_Ioo]
          congr 1
          have h1' : (1 : ℝ) ≤ v * t - k := by linarith
          rw [max_eq_right (by linarith), min_eq_left h1']
          ring
        · have hset : Ioo (0 : ℝ) 1 ∩ Ici ((k : ℝ) + 1 - v * t)
              = Ico ((k : ℝ) + 1 - v * t) 1 := by
            ext x
            simp only [mem_inter_iff, mem_Ioo, mem_Ici, mem_Ico]
            constructor
            · rintro ⟨⟨_, hx1⟩, hxge⟩
              exact ⟨hxge, hx1⟩
            · rintro ⟨hxge, hx1⟩
              exact ⟨⟨by linarith, hx1⟩, hxge⟩
          rw [hset, Real.volume_Ico]
          rcases le_or_gt (v * t - (k : ℝ)) 0 with hle2 | hgt2
          · have e1 : (1 : ℝ) - ((k : ℝ) + 1 - v * t) ≤ 0 := by linarith
            have e2 : min 1 (max 0 (v * t - (k : ℝ))) = 0 := by
              rw [max_eq_left hle2]
              exact min_eq_right (by norm_num)
            rw [e2, ENNReal.ofReal_eq_zero.mpr e1, ENNReal.ofReal_zero]
          · congr 1
            rw [max_eq_right hgt2.le, min_eq_right (by linarith)]
            ring
      rw [hvol]
      simp [MeasureTheory.Measure.dirac_apply' _ hΓ, h1]
    · have hpre : (fun x : ℝ => ((1 : ℝ), ((k : ℝ) + 1 - x) / v)) ⁻¹' (Γ ×ˢ Ioc (0 : ℝ) t)
          = ∅ := by
        ext x
        simp [h1]
      rw [hpre]
      simp [MeasureTheory.Measure.dirac_apply' _ hΓ, h1]
  simp only [hterm]
  rw [ENNReal.tsum_mul_left, tsum_clamp (v * t) (by positivity)]
  ring

/-- **Section 3.2, uniform initial law.** The mean jump intensity of the sawtooth
process started from the uniform law on `[0;1]` exists and is the time-independent
measure `v δ₁`; in particular the global mean jump intensity is `r_t(E) = v`. -/
theorem meanJumpIntensity_uniform {v : ℝ} (hv : 0 < v) :
    MeanJumpIntensity (jumpMeasure v (volume.restrict (Ioo (0 : ℝ) 1)))
      (fun _ : ℝ => (ENNReal.ofReal v) • Measure.dirac (1 : ℝ)) where
  isFiniteMeasure := by
    intro t
    constructor
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ]
    simp [ENNReal.ofReal_lt_top]
  measurable_apply := by
    intro Γ hΓ
    simp only [Measure.smul_apply, smul_eq_mul]
    exact measurable_const
  lintegral_eq := by
    intro Γ hΓ t ht
    rw [uniform_apply hv hΓ ht]
    simp only [Measure.smul_apply, smul_eq_mul, lintegral_const, Measure.restrict_apply,
      MeasurableSet.univ, univ_inter, Real.volume_Ioc]
    rw [ENNReal.ofReal_mul hv.le]
    ring_nf

/-! ### The Dirac initial law: no mean jump intensity -/

/-- Expected number of jumps in `(0;t]` when the process starts deterministically at
`0`: it is `⌊v t⌋`, a genuinely discontinuous function of `t`. -/
theorem dirac_apply {v : ℝ} (hv : 0 < v) {t : ℝ} (ht : 0 ≤ t) :
    jumpMeasure v (Measure.dirac (0 : ℝ)) (univ ×ˢ Ioc (0 : ℝ) t) = (⌊v * t⌋₊ : ℕ) := by
  classical
  have hmeasSet : MeasurableSet ((univ : Set ℝ) ×ˢ Ioc (0 : ℝ) t) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  rw [jumpMeasure, Measure.sum_apply _ hmeasSet]
  have hterm : ∀ k : ℕ,
      (Measure.map (fun x : ℝ => ((1 : ℝ), ((k : ℝ) + 1 - x) / v)) (Measure.dirac (0 : ℝ)))
        ((univ : Set ℝ) ×ˢ Ioc (0 : ℝ) t)
        = if k < ⌊v * t⌋₊ then 1 else 0 := by
    intro k
    rw [Measure.map_apply (measurable_jumpMap v k) hmeasSet]
    rw [Measure.dirac_apply' _ ((measurable_jumpMap v k) hmeasSet)]
    have hiff : ((0 : ℝ) ∈ (fun x : ℝ => ((1 : ℝ), ((k : ℝ) + 1 - x) / v)) ⁻¹'
        ((univ : Set ℝ) ×ˢ Ioc (0 : ℝ) t)) ↔ k < ⌊v * t⌋₊ := by
      simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_Ioc, sub_zero]
      constructor
      · rintro ⟨_, hle⟩
        rw [div_le_iff₀ hv] at hle
        have : ((k : ℝ) + 1) ≤ v * t := by linarith
        have hk : (k : ℕ) + 1 ≤ ⌊v * t⌋₊ := by
          rw [Nat.le_floor_iff (by positivity)]
          push_cast
          linarith
        omega
      · intro hk
        have hk' : ((k : ℝ) + 1) ≤ v * t := by
          have h1 : ((k : ℕ) + 1 : ℕ) ≤ ⌊v * t⌋₊ := hk
          have := Nat.floor_le (show (0:ℝ) ≤ v * t by positivity)
          have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ (⌊v * t⌋₊ : ℝ) := by exact_mod_cast h1
          push_cast at h2
          linarith
        refine ⟨by positivity, ?_⟩
        · rw [div_le_iff₀ hv]
          linarith
    by_cases hk : k < ⌊v * t⌋₊
    · simp [hk, Set.indicator_of_mem (hiff.mpr hk)]
    · simp [hk, Set.indicator_of_notMem (fun h => hk (hiff.mp h))]
  simp only [hterm]
  rw [tsum_eq_sum (s := Finset.range ⌊v * t⌋₊) (by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [hk])]
  simp [Finset.filter_true_of_mem (fun x hx => Finset.mem_range.mp hx)]

/-- **Section 3.2, deterministic initial law.** When the sawtooth process starts at
`x = 0`, the jumps occur deterministically at the times `k / v`, and the process admits
**no** mean jump intensity: the expected jump count jumps by `1` at `t = 1/v`, whereas
Definition 6 forces it to be continuous. -/
theorem not_exists_meanJumpIntensity_dirac {v : ℝ} (hv : 0 < v) :
    ¬ ∃ r : ℝ → Measure ℝ, MeanJumpIntensity (jumpMeasure v (Measure.dirac (0 : ℝ))) r := by
  rintro ⟨r, hr⟩
  have hzero : ∀ u : ℝ, 0 ≤ u → u < 1 / v →
      jumpMeasure v (Measure.dirac (0 : ℝ)) (univ ×ˢ Ioc (0 : ℝ) u) = 0 := by
    intro u hu0 hu
    rw [dirac_apply hv hu0]
    have : v * u < 1 := by
      rw [lt_div_iff₀ hv] at hu
      linarith
    have : ⌊v * u⌋₊ = 0 := by
      apply Nat.floor_eq_zero.mpr this
    simp [this]
  have hlim := hr.eq_of_lt_of_forall MeasurableSet.univ (by positivity : (0 : ℝ) < 1 / v) hzero
  rw [dirac_apply hv (by positivity)] at hlim
  have hone : v * (1 / v) = 1 := by field_simp
  rw [hone] at hlim
  simp at hlim

end GSHS.Sawtooth
