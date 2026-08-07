/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuity of the Beta quantile and the CDF/quantile bijection

The Beta CDF `regBetaFn a b` restricted to `[0,1]` is a continuous bijection of
a compact space onto a Hausdorff one, hence a homeomorphism; its inverse, the
quantile `betaQuantile a b` of batch 174, is therefore continuous on `[0,1]`
too.  This module records that, together with the packaging of the pair as
mutually inverse bijections of `[0,1]` and the Galois-style characterisation

  `Q(p) ≤ x  ↔  p ≤ I_x(a,b)`   (`p, x ∈ [0,1]`),

which is the form in which a quantile is used to convert a statement about a
uniform variate into a statement about a Beta variate.
-/
import SHSLib.Foundations.BetaQuantileFunction

open Real Set Filter Topology MeasureTheory

namespace SHSLib.Trigamma

/-- **The Beta quantile is continuous on `[0,1]`.**  The CDF is a continuous
bijection from the compact `[0,1]` onto itself, hence a homeomorphism. -/
theorem continuousOn_betaQuantile {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (betaQuantile a b) (Set.Icc (0:ℝ) 1) := by
  set S : Set ℝ := Set.Icc (0:ℝ) 1 with hS
  have hCDF : ∀ x : S, regBetaFn a b (x : ℝ) ∈ S := fun x =>
    regBetaFn_mem_Icc ha hb x.2.1 x.2.2
  have hQ : ∀ p : S, betaQuantile a b (p : ℝ) ∈ S := fun p =>
    betaQuantile_mem_Icc ha hb p.2.1 p.2.2
  let e : S ≃ S :=
  { toFun := fun x => ⟨regBetaFn a b (x : ℝ), hCDF x⟩
    invFun := fun p => ⟨betaQuantile a b (p : ℝ), hQ p⟩
    left_inv := fun x => by
      ext; exact betaQuantile_regBetaFn ha hb x.2.1 x.2.2
    right_inv := fun p => by
      ext; exact regBetaFn_betaQuantile ha hb p.2.1 p.2.2 }
  have hcont : Continuous e := by
    rw [continuous_induced_rng]
    exact (continuousOn_regBetaFn ha hb).restrict
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_Icc
  let h : S ≃ₜ S := Continuous.homeoOfEquivCompactToT2 hcont
  rw [continuousOn_iff_continuous_restrict]
  exact h.symm.continuous.subtype_val

/-- The CDF and the quantile are mutually inverse on `[0,1]`. -/
theorem invOn_betaQuantile_regBetaFn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Set.InvOn (betaQuantile a b) (regBetaFn a b) (Set.Icc (0:ℝ) 1)
      (Set.Icc (0:ℝ) 1) :=
  ⟨fun _ hx => betaQuantile_regBetaFn ha hb hx.1 hx.2,
    fun _ hp => regBetaFn_betaQuantile ha hb hp.1 hp.2⟩

/-- The Beta CDF is a bijection of `[0,1]` onto itself. -/
theorem bijOn_regBetaFn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Set.BijOn (regBetaFn a b) (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := by
  refine ⟨fun x hx => regBetaFn_mem_Icc ha hb hx.1 hx.2,
    (regBetaFn_strictMonoOn ha hb).injOn, fun p hp => ?_⟩
  exact ⟨betaQuantile a b p, betaQuantile_mem_Icc ha hb hp.1 hp.2,
    regBetaFn_betaQuantile ha hb hp.1 hp.2⟩

/-- The Beta quantile is a bijection of `[0,1]` onto itself. -/
theorem bijOn_betaQuantile {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Set.BijOn (betaQuantile a b) (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := by
  refine ⟨fun p hp => betaQuantile_mem_Icc ha hb hp.1 hp.2,
    (betaQuantile_strictMonoOn ha hb).injOn, fun x hx => ?_⟩
  exact ⟨regBetaFn a b x, regBetaFn_mem_Icc ha hb hx.1 hx.2,
    betaQuantile_regBetaFn ha hb hx.1 hx.2⟩

/-- **The quantile/CDF adjunction**: for `p, x ∈ [0,1]`,
`Q(p) ≤ x ↔ p ≤ I_x(a,b)`. -/
theorem betaQuantile_le_iff {a b p x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    betaQuantile a b p ≤ x ↔ p ≤ regBetaFn a b x := by
  have hQp := betaQuantile_mem_Icc ha hb hp0 hp1
  have hIx := regBetaFn_mem_Icc ha hb hx0 hx1
  constructor
  · intro hle
    have := (regBetaFn_strictMonoOn ha hb).monotoneOn hQp ⟨hx0, hx1⟩ hle
    rwa [regBetaFn_betaQuantile ha hb hp0 hp1] at this
  · intro hle
    have := (betaQuantile_strictMonoOn ha hb).monotoneOn ⟨hp0, hp1⟩ hIx hle
    rwa [betaQuantile_regBetaFn ha hb hx0 hx1] at this

end SHSLib.Trigamma
