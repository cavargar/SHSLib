/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The probability integral transform for order statistics

Batches 187–189 established that the `(j+1)`-st order statistic of
`n = j+m+1` independent uniforms on `[0,1]` has the `Beta(j+1, m+1)` law.  This
module removes the restriction to uniform samples.

The mechanism is the *probability integral transform*: if `g` is a monotone
map and `U₁, …, U_n` are uniform, then `g(U₁), …, g(U_n)` is a sample from the
law `g_* Unif[0,1]`, and — because sorting commutes with a monotone map —

  `(j+1)`-st order statistic of `g(U)`  =  `g` (`(j+1)`-st order statistic of `U`).

Consequently the law of the `(j+1)`-st order statistic of *any* sample obtained
by an increasing transform of uniforms is the pushforward under `g` of the
`Beta(j+1, m+1)` law.

Specialising `g` to the Beta quantile function of batch 178 gives the classical
statement for a Beta sample:

  `orderStat (Beta(a,b) sample) ~ Q_{a,b} (Beta(j+1, m+1))`,

where `Q_{a,b}` is the quantile function of `Beta(a,b)`.
-/
import SHSLib.Foundations.UniformOrderStatisticLaw
import SHSLib.Foundations.BetaInverseTransform

open MeasureTheory Set ENNReal

namespace SHSLib.Trigamma

/-! ### Sorting commutes with a monotone map -/

/-- **Order statistics are equivariant under monotone maps.**  Sorting the
tuple `g ∘ w` and then reading off the `j`-th entry is the same as sorting `w`,
reading off the `j`-th entry, and applying `g`. -/
theorem orderStat_comp_of_monotone {n : ℕ} {g : ℝ → ℝ} (hg : Monotone g) (w : Fin n → ℝ)
    (j : Fin n) : orderStat n (fun i => g (w i)) j = g (orderStat n w j) := by
  have hmono : Monotone ((fun i => g (w i)) ∘ Tuple.sort w) :=
    hg.comp (Tuple.monotone_sort w)
  have h := (Tuple.comp_sort_eq_comp_iff_monotone (f := fun i => g (w i))
    (σ := Tuple.sort w)).2 hmono
  have := congrFun h j
  simpa [orderStat, Function.comp] using this.symm

/-! ### The law of the transformed order statistic -/

/-- The `(j+1)`-st order statistic of `g(U₁), …, g(U_n)`, for `g` monotone and
measurable, has the law `g_* Beta(j+1, m+1)`. -/
theorem map_orderStat_comp (j m : ℕ) {g : ℝ → ℝ} (hg : Monotone g) (hgm : Measurable g) :
    (unifPi (j + m + 1)).map
        (fun w : Fin (j + m + 1) → ℝ =>
          orderStat (j + m + 1) (fun i => g (w i)) ⟨j, by omega⟩)
      = (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map g := by
  set jj : Fin (j + m + 1) := ⟨j, by omega⟩ with hjj
  have hfun : (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) (fun i => g (w i)) jj)
      = g ∘ (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w jj) := by
    funext w
    simpa using orderStat_comp_of_monotone hg w jj
  rw [hfun, ← Measure.map_map hgm (measurable_orderStat _ jj), map_orderStat j m]

/-- The product of `n` copies of the transformed law is the pushforward of the
uniform product under the coordinatewise transform. -/
theorem pi_map_unifIcc (n : ℕ) {g : ℝ → ℝ} (hgm : Measurable g) :
    (unifPi n).map (fun w : Fin n → ℝ => fun i => g (w i))
      = Measure.pi (fun _ : Fin n => unifIcc.map g) := by
  haveI : IsProbabilityMeasure (unifIcc.map g) :=
    Measure.isProbabilityMeasure_map hgm.aemeasurable
  exact Measure.pi_map_pi (fun _ => hgm.aemeasurable)

/-- **The order statistic of a transformed sample.**  If `ν = g_* Unif[0,1]`
for a monotone measurable `g`, then the `(j+1)`-st order statistic of an
independent sample of size `n = j+m+1` from `ν` has the law
`g_* Beta(j+1, m+1)`. -/
theorem map_orderStat_of_monotone (j m : ℕ) {g : ℝ → ℝ} (hg : Monotone g) (hgm : Measurable g) :
    (Measure.pi (fun _ : Fin (j + m + 1) => unifIcc.map g)).map
        (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w ⟨j, by omega⟩)
      = (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map g := by
  set jj : Fin (j + m + 1) := ⟨j, by omega⟩ with hjj
  have hmg : Measurable (fun w : Fin (j + m + 1) → ℝ => fun i => g (w i)) :=
    measurable_pi_lambda _ (fun i => hgm.comp (measurable_pi_apply i))
  rw [← pi_map_unifIcc (j + m + 1) hgm,
    Measure.map_map (measurable_orderStat _ jj) hmg]
  have hcomp : (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w jj)
      ∘ (fun w : Fin (j + m + 1) → ℝ => fun i => g (w i))
      = fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) (fun i => g (w i)) jj := rfl
  rw [hcomp, map_orderStat_comp j m hg hgm]

/-! ### The Beta sample -/

/-- The clamped Beta quantile function is monotone on all of `ℝ`. -/
theorem monotone_betaQuantileClamp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Monotone (betaQuantileClamp a b) := by
  intro p q hpq
  have hmem : ∀ r : ℝ, max 0 (min 1 r) ∈ Set.Icc (0:ℝ) 1 := fun r =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hle : max 0 (min 1 p) ≤ max 0 (min 1 q) :=
    max_le_max le_rfl (min_le_min le_rfl hpq)
  exact (betaQuantile_strictMonoOn ha hb).monotoneOn (hmem p) (hmem q) hle

/-- The pushforward of the uniform law under the clamped Beta quantile is the
Beta law. -/
theorem map_betaQuantileClamp_unifIcc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    unifIcc.map (betaQuantileClamp a b) = betaMeasure a b := by
  have hae : betaQuantileClamp a b =ᵐ[unifIcc] betaQuantile a b := by
    rw [unifIcc]
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards with p hp using betaQuantileClamp_eq_of_mem hp
  rw [Measure.map_congr hae, unifIcc, map_betaQuantile_uniform ha hb]

/-- **Order statistics of a Beta sample.**  The `(j+1)`-st order statistic of
`n = j+m+1` independent `Beta(a,b)` variables is distributed as
`Q_{a,b}(B)` with `B ~ Beta(j+1, m+1)`, where `Q_{a,b}` is the `Beta(a,b)`
quantile function. -/
theorem map_orderStat_betaSample {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j m : ℕ) :
    (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b)).map
        (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w ⟨j, by omega⟩)
      = (betaMeasure ((j : ℝ) + 1) ((m : ℝ) + 1)).map (betaQuantileClamp a b) := by
  have h := map_orderStat_of_monotone j m (monotone_betaQuantileClamp ha hb)
    (continuous_betaQuantileClamp ha hb).measurable
  rwa [map_betaQuantileClamp_unifIcc ha hb] at h

/-! ### The distribution function of the Beta order statistic -/

/-- The Beta law lives on `[0,1]`, so intersecting with `[0,1]` does not change
the measure of a set. -/
theorem betaMeasure_inter_Icc (a b : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    betaMeasure a b (s ∩ Set.Icc 0 1) = betaMeasure a b s := by
  have hset : Set.Ioo (0:ℝ) 1 ∩ (s ∩ Set.Icc 0 1) = Set.Ioo (0:ℝ) 1 ∩ s := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h1.1.le, h1.2.le⟩
  rw [betaMeasure_apply a b (hs.inter measurableSet_Icc), betaMeasure_apply a b hs, hset]

/-- The preimage of a half-line under the clamped quantile, intersected with
`[0,1]`. -/
theorem preimage_betaQuantileClamp_Iic_inter {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    betaQuantileClamp a b ⁻¹' Set.Iic x ∩ Set.Icc (0:ℝ) 1
      = Set.Icc (0:ℝ) (regBetaFn a b x) := by
  rw [← preimage_betaQuantile_Iic_inter ha hb hx0 hx1]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, and_congr_left_iff]
  intro hp
  rw [betaQuantileClamp_eq_of_mem hp]

/-- **The distribution function of an order statistic of a Beta sample.**  For a
sample of `n = j+m+1` independent `Beta(a,b)` variables, the `(j+1)`-st order
statistic is `≤ x` with probability `I_{I_x(a,b)}(j+1, m+1)`. -/
theorem measure_orderStat_betaSample_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j m : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (Measure.pi (fun _ : Fin (j + m + 1) => betaMeasure a b))
        {w : Fin (j + m + 1) → ℝ | orderStat (j + m + 1) w ⟨j, by omega⟩ ≤ x}
      = ENNReal.ofReal (regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1) (regBetaFn a b x)) := by
  set jj : Fin (j + m + 1) := ⟨j, by omega⟩ with hjj
  have hpre : {w : Fin (j + m + 1) → ℝ | orderStat (j + m + 1) w jj ≤ x}
      = (fun w : Fin (j + m + 1) → ℝ => orderStat (j + m + 1) w jj) ⁻¹' Set.Iic x := rfl
  have hmap := map_orderStat_betaSample ha hb j m
  have hIcc := regBetaFn_mem_Icc ha hb hx0 hx1
  rw [hpre, ← Measure.map_apply (measurable_orderStat _ jj) measurableSet_Iic, hmap,
    Measure.map_apply (continuous_betaQuantileClamp ha hb).measurable measurableSet_Iic,
    ← betaMeasure_inter_Icc _ _
      ((continuous_betaQuantileClamp ha hb).measurable measurableSet_Iic),
    preimage_betaQuantileClamp_Iic_inter ha hb hx0 hx1]
  have hIic : Set.Icc (0:ℝ) (regBetaFn a b x) = Set.Iic (regBetaFn a b x) ∩ Set.Icc 0 1 := by
    ext t
    simp only [Set.mem_Icc, Set.mem_inter_iff, Set.mem_Iic]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨h1, h0, h1.trans hIcc.2⟩
    · rintro ⟨h1, h0, -⟩; exact ⟨h0, h1⟩
  rw [hIic, betaMeasure_inter_Icc _ _ measurableSet_Iic,
    betaMeasure_Iic (by positivity) (by positivity) hIcc.1 hIcc.2]

end SHSLib.Trigamma
