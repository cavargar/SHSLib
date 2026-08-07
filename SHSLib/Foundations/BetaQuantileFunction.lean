/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Beta quantile function

Batch 173 proved that for every level `p ∈ [0,1]` there is a unique `x ∈ [0,1]`
with `I_x(a,b) = p`.  This module packages that solution as a function,

  `betaQuantile a b p`,

and records its defining properties: it lands in `[0,1]`, it is a two-sided
inverse of the Beta CDF on `[0,1]`, it is strictly increasing, it maps the
endpoints to the endpoints, and it sends `½` to `½` for the symmetric law.

The pair (`regBetaFn`, `betaQuantile`) is the inverse-transform interface: if
`U` is uniform on `[0,1]` then `betaQuantile a b U` has the Beta law with
parameters `a, b`.
-/
import SHSLib.Foundations.BetaQuantile

open Real Set Filter Topology MeasureTheory

namespace SHSLib.Trigamma

open Classical in
/-- The **Beta quantile function**: the inverse of the Beta CDF.  For
`p ∈ [0,1]` and `a, b > 0` it is the unique `x ∈ [0,1]` with `I_x(a,b) = p`;
outside that range the value is a junk `0`. -/
noncomputable def betaQuantile (a b p : ℝ) : ℝ :=
  if h : ∃ x, x ∈ Set.Icc (0:ℝ) 1 ∧ regBetaFn a b x = p then h.choose else 0

/-- The defining property of the quantile. -/
theorem betaQuantile_spec {a b p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    betaQuantile a b p ∈ Set.Icc (0:ℝ) 1
      ∧ regBetaFn a b (betaQuantile a b p) = p := by
  classical
  have hex : ∃ x, x ∈ Set.Icc (0:ℝ) 1 ∧ regBetaFn a b x = p :=
    (existsUnique_regBetaFn_eq ha hb hp0 hp1).exists
  simp only [betaQuantile, dif_pos hex]
  exact hex.choose_spec

/-- The quantile lies in `[0,1]`. -/
theorem betaQuantile_mem_Icc {a b p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : betaQuantile a b p ∈ Set.Icc (0:ℝ) 1 :=
  (betaQuantile_spec ha hb hp0 hp1).1

/-- **Right inverse**: `I_{Q(p)}(a,b) = p`. -/
theorem regBetaFn_betaQuantile {a b p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    regBetaFn a b (betaQuantile a b p) = p :=
  (betaQuantile_spec ha hb hp0 hp1).2

/-- **Left inverse**: `Q(I_x(a,b)) = x` for `x ∈ [0,1]`. -/
theorem betaQuantile_regBetaFn {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    betaQuantile a b (regBetaFn a b x) = x := by
  obtain ⟨hp0, hp1⟩ := regBetaFn_mem_Icc ha hb hx0 hx1
  have huniq := existsUnique_regBetaFn_eq ha hb hp0 hp1
  obtain ⟨w, -, hu⟩ := huniq
  have h1 := hu _ ⟨betaQuantile_mem_Icc ha hb hp0 hp1,
    regBetaFn_betaQuantile ha hb hp0 hp1⟩
  have h2 := hu x ⟨⟨hx0, hx1⟩, rfl⟩
  rw [h1, h2]

@[simp] theorem betaQuantile_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaQuantile a b 0 = 0 := by
  have := betaQuantile_regBetaFn ha hb (le_refl (0:ℝ)) zero_le_one
  rwa [regBetaFn_zero] at this

@[simp] theorem betaQuantile_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaQuantile a b 1 = 1 := by
  have := betaQuantile_regBetaFn ha hb (zero_le_one' ℝ) (le_refl (1:ℝ))
  rwa [regBetaFn_one ha hb] at this

/-- The quantile function is strictly increasing on `[0,1]`. -/
theorem betaQuantile_strictMonoOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (betaQuantile a b) (Set.Icc (0:ℝ) 1) := by
  intro p hp q hq hpq
  by_contra hcon
  push_neg at hcon
  have hmono := regBetaFn_strictMonoOn ha hb
  have hQp := betaQuantile_mem_Icc ha hb hq.1 hq.2
  have hQq := betaQuantile_mem_Icc ha hb hp.1 hp.2
  rcases eq_or_lt_of_le hcon with heq | hlt
  · have : p = q := by
      rw [← regBetaFn_betaQuantile ha hb hp.1 hp.2,
        ← regBetaFn_betaQuantile ha hb hq.1 hq.2, heq]
    exact absurd this hpq.ne
  · have := hmono hQp hQq hlt
    rw [regBetaFn_betaQuantile ha hb hq.1 hq.2,
      regBetaFn_betaQuantile ha hb hp.1 hp.2] at this
    linarith

/-- **The median of the symmetric Beta law**, in quantile form:
`Q_{1/2}(a,a) = ½`. -/
theorem betaQuantile_half_self {a : ℝ} (ha : 0 < a) :
    betaQuantile a a (1/2) = 1/2 := by
  have h := betaQuantile_regBetaFn ha ha (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1)
  rwa [regBetaFn_half_self ha] at h

end SHSLib.Trigamma
