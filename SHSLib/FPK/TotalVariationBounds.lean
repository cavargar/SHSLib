/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Appendix B of Bect (2010): the total-variation bounds (39) and (41)

The proof of Theorem 8 rests, besides the differentiation of Eq. (13), on the elementary
comparison of the three terms of the generalized FPK equation (14),

  `μ'_t = L*μ_t + r_t(K − I)`,

through the bound `|r_t(K − I)| ≤ 2 r_t`.  Integrating it in time gives the two
symmetric estimates of Appendix B: for every relatively compact `Γ`,

  `∫₀ᵗ |L*μ_s|(Γ) ds ≤ ∫₀ᵗ |μ'_s|(Γ) ds + 2 E{N_t}`,                        (39)
  `∫₀ᵗ |μ'_s|(Γ) ds ≤ ∫₀ᵗ |L*μ_s|(Γ) ds + 2 E{N_t}`,                        (41)

`E{N_t} = R(E × (0;t])` being the expected number of jumps before time `t`.  They are
what turns the local integrability of one side of Eq. (14) into the local integrability
of the other, i.e. condition 8(b) into condition 8(c) and conversely.

This file formalizes these bounds in the tested formulation of `GSHS.FPKData` used for
Theorem 8, the measure `|ν|(Γ)` being replaced by `|ν φ|` for a test function `φ`:

* `GSHS.FPKData.abs_jumpPair_le` — `|r_t(K − I)φ| ≤ 2 ‖φ‖ r_t(E)`, the pointwise bound;
* `GSHS.FPKData.integral_r_univ_eq_expectedJumps` — `∫₀ᵗ r_s(E) ds = E{N_t}`, from
  Definition 6 applied to `Γ = E`;
* `GSHS.FPKData.eq39_genPair` and `GSHS.FPKData.eq41_derivPair` — Eqs. (39) and (41);
* `GSHS.FPKData.integrableOn_jumpPair`, `GSHS.FPKData.integrableOn_genPair_of_fpk` and
  `GSHS.FPKData.integrableOn_derivPair_of_fpk` — the corresponding local-integrability
  transfers used in the proof of Theorem 8.
-/
import SHSLib.FPK.DynkinFormula
import SHSLib.FPK.MeanJumpIntensity

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

namespace FPKData

variable {E : Type*} [MeasurableSpace E] {T : Type*} (D : FPKData E T)

/-! ### The pointwise bound `|r_t(K − I)φ| ≤ 2 ‖φ‖ r_t(E)` -/

/-- The jump term of Eq. (14) is bounded by twice the total mass of the mean jump
intensity: `|r_t(K − I)φ| ≤ 2 ‖φ‖ r_t(E)`.  This is the inequality
`|r_t(K − I)| ≤ 2 r_t` of Appendix B, tested against a test function. -/
theorem abs_jumpPair_le (t : ℝ) (φ : T) :
    |D.jumpPair t φ| ≤ 2 * |D.ev_bound φ| * (D.r t univ).toReal := by
  have hbd : ∀ x : E, ‖(∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x‖ ≤ 2 * |D.ev_bound φ| := by
    intro x
    calc ‖(∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x‖
        = |(∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x| := Real.norm_eq_abs _
      _ ≤ |∫ y, D.ev φ y ∂(D.K x)| + |D.ev φ x| := abs_sub _ _
      _ ≤ |D.ev_bound φ| + |D.ev_bound φ| :=
          add_le_add (D.abs_kernelAverage_le φ x) ((D.ev_le φ x).trans (le_abs_self _))
      _ = 2 * |D.ev_bound φ| := by ring
  have h := norm_integral_le_of_norm_le_const (μ := D.r t)
    (f := fun x => (∫ y, D.ev φ y ∂(D.K x)) - D.ev φ x)
    (C := 2 * |D.ev_bound φ|) (Filter.Eventually.of_forall hbd)
  simpa [jumpPair, Real.norm_eq_abs] using h

/-- The mean jump intensity is integrable in time on `(0;t]` as soon as its total mass
is; combined with `GSHS.FPKData.abs_jumpPair_le` this gives the integrability of the
jump term of Eq. (14). -/
theorem integrableOn_jumpPair {t : ℝ} {φ : T}
    (hmeas : AEStronglyMeasurable (fun s => D.jumpPair s φ) (volume.restrict (Ioc (0 : ℝ) t)))
    (hr : IntegrableOn (fun s => (D.r s univ).toReal) (Ioc (0 : ℝ) t)) :
    IntegrableOn (fun s => D.jumpPair s φ) (Ioc (0 : ℝ) t) := by
  refine Integrable.mono' (hr.const_mul (2 * |D.ev_bound φ|)) hmeas ?_
  exact Filter.Eventually.of_forall fun s => by
    simpa [Real.norm_eq_abs] using D.abs_jumpPair_le s φ

/-! ### `∫₀ᵗ r_s(E) ds = E{N_t}` -/

/-- Definition 6 applied to `Γ = E`: the time integral of the total mass of the mean
jump intensity is the expected number of jumps `E{N_t} = R(E × (0;t])`. -/
theorem integral_r_univ_eq_expectedJumps {R : Measure (E × ℝ)}
    (hR : MeanJumpIntensity R D.r) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Ioc (0 : ℝ) t, (D.r s univ).toReal = (R (univ ×ˢ Ioc (0 : ℝ) t)).toReal := by
  have hmeas : Measurable fun s : ℝ => D.r s univ := hR.measurable_apply univ MeasurableSet.univ
  have hfin : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) t)), D.r s univ < ⊤ :=
    Filter.Eventually.of_forall fun s => measure_lt_top (D.r s) univ
  rw [integral_toReal hmeas.aemeasurable hfin, hR.lintegral_eq univ MeasurableSet.univ t ht]

/-! ### Eqs. (39) and (41) -/

/-- **Eq. (39)** (Bect, 2010, Appendix B).  Under the generalized FPK equation (14), the
time integral of `|L*μ_s φ|` is bounded by that of `|μ'_s φ|` plus `2 ‖φ‖ E{N_t}`; in
particular `s ↦ L*μ_s` is locally integrable as soon as `s ↦ μ'_s` is. -/
theorem eq39_genPair {μ' : ℝ → SignedFin E} {t : ℝ} {φ : T}
    (hfpk : ∀ s ∈ Ioc (0 : ℝ) t,
      (μ' s).pair (D.ev φ) = D.genPair s φ + D.jumpPair s φ)
    (hgen : IntegrableOn (fun s => D.genPair s φ) (Ioc (0 : ℝ) t))
    (hmu : IntegrableOn (fun s => (μ' s).pair (D.ev φ)) (Ioc (0 : ℝ) t))
    (hr : IntegrableOn (fun s => (D.r s univ).toReal) (Ioc (0 : ℝ) t)) :
    ∫ s in Ioc (0 : ℝ) t, |D.genPair s φ|
      ≤ (∫ s in Ioc (0 : ℝ) t, |(μ' s).pair (D.ev φ)|)
        + 2 * |D.ev_bound φ| * ∫ s in Ioc (0 : ℝ) t, (D.r s univ).toReal := by
  have hbd : ∀ s ∈ Ioc (0 : ℝ) t,
      |D.genPair s φ| ≤ |(μ' s).pair (D.ev φ)| + 2 * |D.ev_bound φ| * (D.r s univ).toReal := by
    intro s hs
    have h1 : D.genPair s φ = (μ' s).pair (D.ev φ) - D.jumpPair s φ := by
      rw [hfpk s hs]; ring
    calc |D.genPair s φ| = |(μ' s).pair (D.ev φ) - D.jumpPair s φ| := by rw [h1]
      _ ≤ |(μ' s).pair (D.ev φ)| + |D.jumpPair s φ| := abs_sub _ _
      _ ≤ |(μ' s).pair (D.ev φ)| + 2 * |D.ev_bound φ| * (D.r s univ).toReal := by
          linarith [D.abs_jumpPair_le s φ]
  have hle : ∫ s in Ioc (0 : ℝ) t, |D.genPair s φ|
      ≤ ∫ s in Ioc (0 : ℝ) t,
          (|(μ' s).pair (D.ev φ)| + 2 * |D.ev_bound φ| * (D.r s univ).toReal) := by
    refine setIntegral_mono_on hgen.abs (hmu.abs.add (hr.const_mul _)) measurableSet_Ioc hbd
  rwa [integral_add hmu.abs (hr.const_mul _), integral_const_mul] at hle

/-- **Eq. (41)** (Bect, 2010, Appendix B), the estimate symmetric to Eq. (39): the time
integral of `|μ'_s φ|` is bounded by that of `|L*μ_s φ|` plus `2 ‖φ‖ E{N_t}`. -/
theorem eq41_derivPair {μ' : ℝ → SignedFin E} {t : ℝ} {φ : T}
    (hfpk : ∀ s ∈ Ioc (0 : ℝ) t,
      (μ' s).pair (D.ev φ) = D.genPair s φ + D.jumpPair s φ)
    (hgen : IntegrableOn (fun s => D.genPair s φ) (Ioc (0 : ℝ) t))
    (hmu : IntegrableOn (fun s => (μ' s).pair (D.ev φ)) (Ioc (0 : ℝ) t))
    (hr : IntegrableOn (fun s => (D.r s univ).toReal) (Ioc (0 : ℝ) t)) :
    ∫ s in Ioc (0 : ℝ) t, |(μ' s).pair (D.ev φ)|
      ≤ (∫ s in Ioc (0 : ℝ) t, |D.genPair s φ|)
        + 2 * |D.ev_bound φ| * ∫ s in Ioc (0 : ℝ) t, (D.r s univ).toReal := by
  have hbd : ∀ s ∈ Ioc (0 : ℝ) t,
      |(μ' s).pair (D.ev φ)| ≤ |D.genPair s φ| + 2 * |D.ev_bound φ| * (D.r s univ).toReal := by
    intro s hs
    calc |(μ' s).pair (D.ev φ)| = |D.genPair s φ + D.jumpPair s φ| := by rw [hfpk s hs]
      _ ≤ |D.genPair s φ| + |D.jumpPair s φ| := abs_add_le _ _
      _ ≤ |D.genPair s φ| + 2 * |D.ev_bound φ| * (D.r s univ).toReal := by
          linarith [D.abs_jumpPair_le s φ]
  have hle : ∫ s in Ioc (0 : ℝ) t, |(μ' s).pair (D.ev φ)|
      ≤ ∫ s in Ioc (0 : ℝ) t,
          (|D.genPair s φ| + 2 * |D.ev_bound φ| * (D.r s univ).toReal) := by
    refine setIntegral_mono_on hmu.abs (hgen.abs.add (hr.const_mul _)) measurableSet_Ioc hbd
  rwa [integral_add hgen.abs (hr.const_mul _), integral_const_mul] at hle

/-- **Eq. (39) with the expected number of jumps.**  The right-hand side of Eq. (39) is
`∫₀ᵗ |μ'_s φ| ds + 2 ‖φ‖ E{N_t}`, where `E{N_t} = R(E × (0;t])`. -/
theorem eq39_genPair_expectedJumps {R : Measure (E × ℝ)} (hR : MeanJumpIntensity R D.r)
    {μ' : ℝ → SignedFin E} {t : ℝ} (ht : 0 ≤ t) {φ : T}
    (hfpk : ∀ s ∈ Ioc (0 : ℝ) t,
      (μ' s).pair (D.ev φ) = D.genPair s φ + D.jumpPair s φ)
    (hgen : IntegrableOn (fun s => D.genPair s φ) (Ioc (0 : ℝ) t))
    (hmu : IntegrableOn (fun s => (μ' s).pair (D.ev φ)) (Ioc (0 : ℝ) t))
    (hr : IntegrableOn (fun s => (D.r s univ).toReal) (Ioc (0 : ℝ) t)) :
    ∫ s in Ioc (0 : ℝ) t, |D.genPair s φ|
      ≤ (∫ s in Ioc (0 : ℝ) t, |(μ' s).pair (D.ev φ)|)
        + 2 * |D.ev_bound φ| * (R (univ ×ˢ Ioc (0 : ℝ) t)).toReal := by
  rw [← D.integral_r_univ_eq_expectedJumps hR ht]
  exact D.eq39_genPair hfpk hgen hmu hr

/-- **Eq. (41) with the expected number of jumps.** -/
theorem eq41_derivPair_expectedJumps {R : Measure (E × ℝ)} (hR : MeanJumpIntensity R D.r)
    {μ' : ℝ → SignedFin E} {t : ℝ} (ht : 0 ≤ t) {φ : T}
    (hfpk : ∀ s ∈ Ioc (0 : ℝ) t,
      (μ' s).pair (D.ev φ) = D.genPair s φ + D.jumpPair s φ)
    (hgen : IntegrableOn (fun s => D.genPair s φ) (Ioc (0 : ℝ) t))
    (hmu : IntegrableOn (fun s => (μ' s).pair (D.ev φ)) (Ioc (0 : ℝ) t))
    (hr : IntegrableOn (fun s => (D.r s univ).toReal) (Ioc (0 : ℝ) t)) :
    ∫ s in Ioc (0 : ℝ) t, |(μ' s).pair (D.ev φ)|
      ≤ (∫ s in Ioc (0 : ℝ) t, |D.genPair s φ|)
        + 2 * |D.ev_bound φ| * (R (univ ×ˢ Ioc (0 : ℝ) t)).toReal := by
  rw [← D.integral_r_univ_eq_expectedJumps hR ht]
  exact D.eq41_derivPair hfpk hgen hmu hr

/-! ### Local integrability transfers (conditions 8(b) ⟷ 8(c)) -/

/-- **Condition 8(b) ⇒ the integrability part of 8(c)**: under Eq. (14), local
integrability of `t ↦ μ'_t` transfers to `t ↦ L*μ_t`. -/
theorem integrableOn_genPair_of_fpk {μ' : ℝ → SignedFin E} {t : ℝ} {φ : T}
    (hfpk : ∀ s ∈ Ioc (0 : ℝ) t,
      (μ' s).pair (D.ev φ) = D.genPair s φ + D.jumpPair s φ)
    (hmu : IntegrableOn (fun s => (μ' s).pair (D.ev φ)) (Ioc (0 : ℝ) t))
    (hmeas : AEStronglyMeasurable (fun s => D.jumpPair s φ) (volume.restrict (Ioc (0 : ℝ) t)))
    (hr : IntegrableOn (fun s => (D.r s univ).toReal) (Ioc (0 : ℝ) t)) :
    IntegrableOn (fun s => D.genPair s φ) (Ioc (0 : ℝ) t) := by
  have hjump : IntegrableOn (fun s => D.jumpPair s φ) (Ioc (0 : ℝ) t) :=
    D.integrableOn_jumpPair hmeas hr
  refine (hmu.sub hjump).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [Pi.sub_apply]
  rw [hfpk s hs]; ring

/-- **Condition 8(c) ⇒ the integrability part of 8(b)**: under Eq. (14), local
integrability of `t ↦ L*μ_t` transfers to `t ↦ μ'_t`. -/
theorem integrableOn_derivPair_of_fpk {μ' : ℝ → SignedFin E} {t : ℝ} {φ : T}
    (hfpk : ∀ s ∈ Ioc (0 : ℝ) t,
      (μ' s).pair (D.ev φ) = D.genPair s φ + D.jumpPair s φ)
    (hgen : IntegrableOn (fun s => D.genPair s φ) (Ioc (0 : ℝ) t))
    (hmeas : AEStronglyMeasurable (fun s => D.jumpPair s φ) (volume.restrict (Ioc (0 : ℝ) t)))
    (hr : IntegrableOn (fun s => (D.r s univ).toReal) (Ioc (0 : ℝ) t)) :
    IntegrableOn (fun s => (μ' s).pair (D.ev φ)) (Ioc (0 : ℝ) t) := by
  have hjump : IntegrableOn (fun s => D.jumpPair s φ) (Ioc (0 : ℝ) t) :=
    D.integrableOn_jumpPair hmeas hr
  refine (hgen.add hjump).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [Pi.add_apply]
  rw [hfpk s hs]

end FPKData

end GSHS
