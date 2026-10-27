/-
# Itô diffusions as Bect FPK data: the weak Dynkin formula (13) without jumps

Bect's generalized Fokker–Planck–Kolmogorov framework (`GSHS.FPKData`, `SHSLib/FPK/`) packages a
family of laws `μ_t`, a generator on test functions and a jump part, and states the generalized
Dynkin formula (13) as `FPKData.WeakDynkin`. A one-dimensional time-homogeneous Itô diffusion
`dx = a(x) dt + b(x) dW` is the jump-free special case: mean jump intensity `r = 0`, generator
`L φ = a φ′ + ½ b² φ″` (Gardiner's `Gardiner.Ito.Generator.itoGen`), laws `μ_t = P ∘ x(t)⁻¹`.

This file builds that `FPKData` and proves `WeakDynkin` for solutions of Lipschitz SDEs that
exist on every horizon, from the weak Fokker–Planck equation of job E5
(`Gardiner.Ito.Generator.IsSDESol.weakFP_integrated`). Instance: the standard Wiener process,
whose weak Dynkin formula is the weak heat equation.

| Lean | content |
| --- | --- |
| `C2cTest` | test functions: `C²` with compact support |
| `fpkData` | the `FPKData ℝ C2cTest` of a 1-D diffusion (no jumps) |
| `weakDynkin_of_isSDESol` | Bect (13) for global solutions of Lipschitz SDEs with bounded noise |
| `weakDynkin_stdWiener` | instance: the standard Wiener process (`a = 0`, `b = 1`) |
-/
import SHSLib.FPK.GeneralizedFPK
import SHSLib.Gardiner.Ito.SDEBridge

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GSHS.ItoDiffusion

open Gardiner.Ito Gardiner.Ito.StochDE Gardiner.Ito.Generator Gardiner.Ito.SDEBridge

/-- Test functions for the weak Dynkin formula: `C²` functions with compact support. -/
def C2cTest : Type := {φ : ℝ → ℝ // IsC2c φ}

lemma exists_bound (φ : C2cTest) : ∃ C, ∀ y, ‖φ.1 y‖ ≤ C :=
  φ.2.contDiff.continuous.bounded_above_of_compact_support φ.2.hasCompactSupport

/-- The `FPKData` of the one-dimensional time-homogeneous diffusion `dx = a(x) dt + b(x) dW`
with paths `x`: laws `μ_t = P ∘ x(t)⁻¹`, generator `a φ′ + ½ b² φ″`, and no jumps
(`r = 0`; the reset kernel is the identity and plays no role). -/
def fpkData (a b : ℝ → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hP : IsProbabilityMeasure P) (x : ℝ → Ω → ℝ) (hx : ∀ t, Measurable (x t)) :
    FPKData ℝ C2cTest where
  ev φ := φ.1
  gen φ y := itoGen (fun z _ => a z) (fun z _ => b z) φ.1 0 y
  law t := lawAt P x t
  r _ := 0
  K := Kernel.id
  markov := inferInstance
  ev_measurable φ := φ.2.contDiff.continuous.measurable
  ev_bound φ := Classical.choose (exists_bound φ)
  ev_le φ y := by
    have := Classical.choose_spec (exists_bound φ) y
    rwa [Real.norm_eq_abs] at this
  law_isProbabilityMeasure t := Measure.isProbabilityMeasure_map (hx t).aemeasurable
  r_isFiniteMeasure _ := inferInstance

/-- **Bect's generalized Dynkin formula (13) for Itô diffusions.** Let `x` solve
`dx = a(x) dt + b(x) dW` on every horizon `[0, T]`, with continuous coefficients satisfying the
Lipschitz and growth conditions on each `[0, T]` and bounded noise coefficient. Then its FPK data
satisfy `FPKData.WeakDynkin`: `μ_t φ − μ_0 φ = ∫₀ᵗ μ_s(Lφ) ds` (the jump term vanishes). -/
theorem weakDynkin_of_isSDESol {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ ‹_›}
    {P : Measure Ω} {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P) {a b : ℝ → ℝ} {ξ : Ω → ℝ}
    {x : ℝ → Ω → ℝ} {B : ℝ}
    (hx : ∀ T, IsSDESol W 𝓕 P (fun y _ => a y) (fun y _ => b y) 0 T ξ x)
    (hc : ∀ T, ∃ K, SDECoeffs (fun y _ => a y) (fun y _ => b y) 0 T K)
    (ha : Continuous a) (hb : Continuous b) (hB : ∀ y, |b y| ≤ B) :
    (fpkData a b P hW.isProbabilityMeasure x
      (fun _ => (hx 0).measurable.of_uncurry_left)).WeakDynkin := by
  intro φ t ht
  obtain ⟨K, hcK⟩ := hc t
  have h := Generator.IsSDESol.weakFP_integrated hW (hx t) hcK (ha.comp continuous_fst)
    (hb.comp continuous_fst) (fun y _ => hB y) φ.2 ht le_rfl
  simp only [FPKData.lawPair, FPKData.genPair, FPKData.jumpPair, fpkData,
    integral_zero_measure, intervalIntegral.integral_zero, add_zero, itoGen] at h ⊢
  exact h

/-- **Instance: the standard Wiener process.** Its FPK data (`a = 0`, `b = 1`) satisfy Bect's
weak Dynkin formula; this is the weak form of the heat equation `∂ₜμ = ½ ∂²_y μ`. -/
theorem weakDynkin_stdWiener :
    (fpkData (fun _ => 0) (fun _ => 1) stdWienerMeasure inferInstance stdWiener
      measurable_stdWiener).WeakDynkin :=
  weakDynkin_of_isSDESol isFWiener_stdWiener
    (fun T => isSDESol_wiener isFWiener_stdWiener measurable_uncurry_stdWiener T)
    (fun T => ⟨1, sdeCoeffs_wiener 0 T⟩) continuous_const continuous_const (B := 1)
    (fun _ => by simp)

end GSHS.ItoDiffusion
