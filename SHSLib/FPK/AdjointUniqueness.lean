/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eq. (15) and Definition 7(d) of Bect (2010): the adjoint `L*μ` and the FPK equation
as an equality between measures

The distributional adjoint of the differential generator is defined by duality,

  `(L*ν)(φ) = ν(Lφ)`,      for all `φ ∈ C²_c(E)`,                               (15)

and Definition 7(c)–(d) requires that `L*μ_t` be (represented by) a Radon measure and
that the generalized FPK equation

  `μ'_t(Γ) = (L*μ_t)(Γ) + r_t(K − I)(Γ)`                                        (14)

hold *as an equality between measures*, i.e. on every relatively compact `Γ`, and not
merely when tested against test functions.  Theorem 8 is proved in the tested form; this
file upgrades it to the measure form, the missing ingredient — the "standard
approximation techniques" of Appendix B — being that a finite signed measure is
determined by its action on `C²_c(E)`.

## Main results

* `GSHS.SignedFin.Eqv` — equality of the finite signed measures `ν = ν⁺ − ν⁻`, written
  without subtraction as `ν₁⁺ + ν₂⁻ = ν₂⁺ + ν₁⁻`; it is an equivalence relation and
  implies equality of the set functions (`GSHS.SignedFin.Eqv.setFun_eq`) and of the
  pairings (`GSHS.SignedFin.Eqv.pair_eq`).
* `GSHS.ext_of_forall_integral_contDiff_eq` — two finite Borel measures on a
  finite-dimensional real normed space that integrate every `C²` compactly supported
  function identically are equal.
* `GSHS.SignedFin.eqv_of_forall_pair_eq` and
  `GSHS.SignedFin.eqv_of_forall_pair_contDiff_eq` — a finite signed measure is
  determined by its pairing with bounded continuous functions, resp. with `C²_c`
  functions.
* `GSHS.FPKData.SeparatesSignedFin` — the property of a family of test functions of
  separating finite signed measures, with the two sufficient conditions above.
* `GSHS.FPKData.IsAdjointAt` — Eq. (15) and Definition 7(c): the finite signed measure
  `lstar` represents `L*μ_t`; `GSHS.FPKData.isAdjointAt_unique` is its uniqueness,
  which is what makes Definition 7(d) well posed.
* `GSHS.FPKData.fpk_eqv_of_pair` and `GSHS.FPKData.definition7d_setFun` — **Definition
  7(d)**: `μ'_t = L*μ_t + r_t(K − I)` as an equality between measures, evaluated on an
  arbitrary measurable set.
-/
import SHSLib.FPK.GeneralizedFPK

open MeasureTheory Set Filter Topology ProbabilityTheory

noncomputable section

namespace GSHS

/-! ### Finite measures are determined by their integrals of `C²_c` functions -/

/-- Two finite Borel measures on a finite-dimensional real normed space which integrate
every compactly supported `C²` function identically are equal.  This is the
approximation argument used repeatedly in Appendix B of the paper: the compactly
supported *continuous* functions, which determine a regular measure, are uniform limits
of smooth ones. -/
theorem ext_of_forall_integral_contDiff_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (A B : Measure E) [IsFiniteMeasure A] [IsFiniteMeasure B]
    (h : ∀ g : E → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      ∫ x, g x ∂A = ∫ x, g x ∂B) : A = B := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  set M := (A univ).toReal + (B univ).toReal with hM
  have hM0 : 0 ≤ M := by positivity
  have hf : Continuous (f : E → ℝ) := f.continuous
  have hfcs : HasCompactSupport (f : E → ℝ) := f.hasCompactSupport'
  have key : ∀ ε : ℝ, 0 < ε → |(∫ x, f x ∂A) - ∫ x, f x ∂B| ≤ ε * M := by
    intro ε hε
    obtain ⟨g, hgsm, hgd, hgsupp⟩ :=
      hf.exists_contDiff_approx (n := ⊤) (ε := fun _ => ε) continuous_const (fun _ => hε)
    have hgcs : HasCompactSupport g :=
      HasCompactSupport.of_support_subset_isCompact hfcs.isCompact
        (hgsupp.trans (subset_tsupport _))
    have hg2 : ContDiff ℝ 2 g := hgsm.of_le ENat.LEInfty.out
    have hgc : Continuous g := hgsm.continuous
    have hbd : ∀ x, ‖f x - g x‖ ≤ ε := by
      intro x
      have hx := hgd x
      rw [dist_eq_norm] at hx
      rw [← norm_neg]
      simpa [neg_sub] using hx.le
    have hA : |(∫ x, f x ∂A) - ∫ x, g x ∂A| ≤ ε * (A univ).toReal := by
      rw [← Real.norm_eq_abs, ← integral_sub (hf.integrable_of_hasCompactSupport hfcs)
        (hgc.integrable_of_hasCompactSupport hgcs)]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbd)
    have hB : |(∫ x, f x ∂B) - ∫ x, g x ∂B| ≤ ε * (B univ).toReal := by
      rw [← Real.norm_eq_abs, ← integral_sub (hf.integrable_of_hasCompactSupport hfcs)
        (hgc.integrable_of_hasCompactSupport hgcs)]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbd)
    rw [← h g hg2 hgcs] at hB
    have habs := abs_sub_le (∫ x, f x ∂A) (∫ x, g x ∂A) (∫ x, f x ∂B)
    rw [abs_sub_comm (∫ x, g x ∂A) (∫ x, f x ∂B)] at habs
    rw [hM]
    nlinarith [habs, hA, hB]
  by_contra hne
  have hpos : 0 < |(∫ x, f x ∂A) - ∫ x, f x ∂B| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set d := |(∫ x, f x ∂A) - ∫ x, f x ∂B|
  have hkey := key (d / (M + 1)) (by positivity)
  have hlt : d / (M + 1) * M < d := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

namespace SignedFin

variable {E : Type*} [MeasurableSpace E]

/-- Equality of two finite signed measures presented as differences: `ν₁ = ν₂` means
`ν₁⁺ + ν₂⁻ = ν₂⁺ + ν₁⁻`. -/
def Eqv (ν₁ ν₂ : SignedFin E) : Prop := ν₁.pos + ν₂.neg = ν₂.pos + ν₁.neg

theorem Eqv.refl (ν : SignedFin E) : Eqv ν ν := rfl

theorem Eqv.symm {ν₁ ν₂ : SignedFin E} (h : Eqv ν₁ ν₂) : Eqv ν₂ ν₁ := Eq.symm h

theorem Eqv.trans {ν₁ ν₂ ν₃ : SignedFin E} (h₁ : Eqv ν₁ ν₂) (h₂ : Eqv ν₂ ν₃) : Eqv ν₁ ν₃ := by
  ext s hs
  have e₁ : ν₁.pos s + ν₂.neg s = ν₂.pos s + ν₁.neg s := by
    simpa [Measure.coe_add, Pi.add_apply] using congrArg (fun m : Measure E => m s) h₁
  have e₂ : ν₂.pos s + ν₃.neg s = ν₃.pos s + ν₂.neg s := by
    simpa [Measure.coe_add, Pi.add_apply] using congrArg (fun m : Measure E => m s) h₂
  have hfin : ν₂.pos s + ν₂.neg s ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  have hsum : (ν₁.pos s + ν₃.neg s) + (ν₂.pos s + ν₂.neg s)
      = (ν₃.pos s + ν₁.neg s) + (ν₂.pos s + ν₂.neg s) := by
    calc (ν₁.pos s + ν₃.neg s) + (ν₂.pos s + ν₂.neg s)
        = (ν₁.pos s + ν₂.neg s) + (ν₂.pos s + ν₃.neg s) := by ring
      _ = (ν₂.pos s + ν₁.neg s) + (ν₃.pos s + ν₂.neg s) := by rw [e₁, e₂]
      _ = (ν₃.pos s + ν₁.neg s) + (ν₂.pos s + ν₂.neg s) := by ring
  simpa [Measure.coe_add, Pi.add_apply] using (ENNReal.add_left_inj hfin).mp hsum

/-- Two equal finite signed measures have the same set function `Γ ↦ ν(Γ)`. -/
theorem Eqv.setFun_eq {ν₁ ν₂ : SignedFin E} (h : Eqv ν₁ ν₂) {Γ : Set E} :
    ν₁.setFun Γ = ν₂.setFun Γ := by
  have h' : ν₁.pos Γ + ν₂.neg Γ = ν₂.pos Γ + ν₁.neg Γ := by
    simpa [Measure.coe_add, Pi.add_apply] using congrArg (fun m : Measure E => m Γ) h
  have h'' : (ν₁.pos Γ).toReal + (ν₂.neg Γ).toReal = (ν₂.pos Γ).toReal + (ν₁.neg Γ).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h']
  simp only [setFun]
  linarith

/-- Two equal finite signed measures pair identically with every bounded measurable
function. -/
theorem Eqv.pair_eq {ν₁ ν₂ : SignedFin E} (h : Eqv ν₁ ν₂) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : ν₁.pair f = ν₂.pair f := by
  have h' : ∫ x, f x ∂(ν₁.pos + ν₂.neg) = ∫ x, f x ∂(ν₂.pos + ν₁.neg) := by rw [h]
  rw [integral_add_measure (integrable_of_bounded hf hC _) (integrable_of_bounded hf hC _),
    integral_add_measure (integrable_of_bounded hf hC _) (integrable_of_bounded hf hC _)] at h'
  simp only [pair]
  linarith

/-- **A finite signed measure is determined by its pairing with bounded continuous
functions.** -/
theorem eqv_of_forall_pair_eq [TopologicalSpace E] [HasOuterApproxClosed E] [BorelSpace E]
    {ν₁ ν₂ : SignedFin E}
    (h : ∀ f : BoundedContinuousFunction E ℝ, ν₁.pair f = ν₂.pair f) : Eqv ν₁ ν₂ := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hint : ∀ m : Measure E, IsFiniteMeasure m → Integrable (⇑f) m := by
    intro m _
    refine integrable_of_bounded (C := ‖f‖) f.continuous.measurable (fun x => ?_) m
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  rw [integral_add_measure (hint _ ν₁.pos_isFiniteMeasure) (hint _ ν₂.neg_isFiniteMeasure),
    integral_add_measure (hint _ ν₂.pos_isFiniteMeasure) (hint _ ν₁.neg_isFiniteMeasure)]
  have := h f
  simp only [pair] at this
  linarith

/-- **A finite signed measure is determined by its pairing with `C²` compactly supported
functions**, the test functions `C²_c(E)` of the paper. -/
theorem eqv_of_forall_pair_contDiff_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν₁ ν₂ : SignedFin E}
    (h : ∀ g : E → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → ν₁.pair g = ν₂.pair g) :
    Eqv ν₁ ν₂ := by
  refine GSHS.ext_of_forall_integral_contDiff_eq _ _ fun g hg hgcs => ?_
  have hint : ∀ m : Measure E, IsFiniteMeasure m → Integrable g m := fun m _ =>
    hg.continuous.integrable_of_hasCompactSupport hgcs
  rw [integral_add_measure (hint _ ν₁.pos_isFiniteMeasure) (hint _ ν₂.neg_isFiniteMeasure),
    integral_add_measure (hint _ ν₂.pos_isFiniteMeasure) (hint _ ν₁.neg_isFiniteMeasure)]
  have := h g hg hgcs
  simp only [pair] at this
  linarith

end SignedFin

namespace FPKData

variable {E : Type*} [MeasurableSpace E] {T : Type*} (D : FPKData E T)

/-- The test functions of `D` separate finite signed measures: two finite signed
measures with the same pairing against every test function are equal.  This is the
property behind the "standard approximation techniques" of Appendix B; see
`GSHS.FPKData.separatesSignedFin_of_contDiff` for the case of the test functions
`C²_c(E)` of the paper. -/
def SeparatesSignedFin : Prop :=
  ∀ ν₁ ν₂ : SignedFin E, (∀ φ : T, ν₁.pair (D.ev φ) = ν₂.pair (D.ev φ)) → SignedFin.Eqv ν₁ ν₂

/-- If the test functions include all bounded continuous functions, they separate finite
signed measures. -/
theorem separatesSignedFin_of_boundedContinuous [TopologicalSpace E] [HasOuterApproxClosed E]
    [BorelSpace E] (hsep : ∀ f : BoundedContinuousFunction E ℝ, ∃ φ : T, D.ev φ = ⇑f) :
    D.SeparatesSignedFin := by
  intro ν₁ ν₂ h
  refine SignedFin.eqv_of_forall_pair_eq fun f => ?_
  obtain ⟨φ, hφ⟩ := hsep f
  rw [← hφ]
  exact h φ

/-- If the test functions include all `C²` compactly supported functions — the class
`C²_c(E)` of the paper — they separate finite signed measures. -/
theorem separatesSignedFin_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (D : FPKData E T)
    (hsep : ∀ g : E → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → ∃ φ : T, D.ev φ = g) :
    D.SeparatesSignedFin := by
  intro ν₁ ν₂ h
  refine SignedFin.eqv_of_forall_pair_contDiff_eq fun g hg hgcs => ?_
  obtain ⟨φ, hφ⟩ := hsep g hg hgcs
  rw [← hφ]
  exact h φ

/-- **Eq. (15)** and Definition 7(c): the finite signed measure `lstar` *is* `L*μ_t`,
i.e. it satisfies `(L*μ_t)(φ) = μ_t(Lφ)` for every test function `φ`. -/
def IsAdjointAt (t : ℝ) (lstar : SignedFin E) : Prop :=
  ∀ φ : T, lstar.pair (D.ev φ) = D.genPair t φ

/-- **Uniqueness in Eq. (15)**: if the test functions separate finite signed measures,
at most one of them represents `L*μ_t`.  Definition 7(d) is therefore an unambiguous
requirement. -/
theorem isAdjointAt_unique {t : ℝ} {l₁ l₂ : SignedFin E} (hsep : D.SeparatesSignedFin)
    (h₁ : D.IsAdjointAt t l₁) (h₂ : D.IsAdjointAt t l₂) : SignedFin.Eqv l₁ l₂ :=
  hsep l₁ l₂ fun φ => by rw [h₁ φ, h₂ φ]

/-- **Definition 7(d) as an equality between measures.**  If `lstar` represents `L*μ_t`
(Eq. (15)) and the tested FPK equation (14) holds for every test function, then `μ'_t`
and `L*μ_t + r_t(K − I)` are equal as finite signed measures. -/
theorem fpk_eqv_of_pair {t : ℝ} {μ' lstar : SignedFin E} (hsep : D.SeparatesSignedFin)
    (hadj : D.IsAdjointAt t lstar)
    (hfpk : ∀ φ : T, μ'.pair (D.ev φ) = D.genPair t φ + D.jumpPair t φ) :
    SignedFin.Eqv μ' (D.addJump lstar t) :=
  hsep _ _ fun φ => by rw [hfpk φ, D.addJump_pair lstar t φ, hadj φ]

/-- The set function of the right-hand side of Eq. (14):
`(L*μ_t + r_t(K − I))(Γ) = (L*μ_t)(Γ) + r_t^{src}(Γ) − r_t(Γ)`. -/
theorem addJump_setFun (lstar : SignedFin E) (t : ℝ) (Γ : Set E) :
    (D.addJump lstar t).setFun Γ
      = lstar.setFun Γ + ((D.K ∘ₘ D.r t) Γ).toReal - (D.r t Γ).toReal := by
  have h1 : ((lstar.pos + (D.K ∘ₘ D.r t)) Γ).toReal
      = (lstar.pos Γ).toReal + ((D.K ∘ₘ D.r t) Γ).toReal := by
    rw [Measure.coe_add, Pi.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have h2 : ((lstar.neg + D.r t) Γ).toReal = (lstar.neg Γ).toReal + (D.r t Γ).toReal := by
    rw [Measure.coe_add, Pi.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [SignedFin.setFun, addJump]
  rw [h1, h2]
  ring

/-- **Definition 7(d)** (Bect, 2010): the generalized FPK equation as an equality
between measures,

  `μ'_t(Γ) = (L*μ_t)(Γ) + r_t^{src}(Γ) − r_t(Γ)`,

for *every* measurable set `Γ` — not only when tested against test functions. -/
theorem definition7d_setFun {t : ℝ} {μ' lstar : SignedFin E} (Γ : Set E)
    (hsep : D.SeparatesSignedFin) (hadj : D.IsAdjointAt t lstar)
    (hfpk : ∀ φ : T, μ'.pair (D.ev φ) = D.genPair t φ + D.jumpPair t φ) :
    μ'.setFun Γ = lstar.setFun Γ + ((D.K ∘ₘ D.r t) Γ).toReal - (D.r t Γ).toReal := by
  rw [(D.fpk_eqv_of_pair hsep hadj hfpk).setFun_eq (Γ := Γ), D.addJump_setFun lstar t Γ]

end FPKData

end GSHS
