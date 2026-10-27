/-
# Dynkin's formula and the martingale problem for solutions of Lipschitz SDEs

For a solution `x` of `dx = a(x, t) dt + b(x, t) dW` on `[0, T]` in the sense of job E4
(`Gardiner.Ito.StochDE.IsSDESol`, coefficients satisfying the Lipschitz and growth conditions
`SDECoeffs`), we show that the process stopped outside `[0, T]`,
`clampProc x T t = x((t ∨ 0) ∧ T)`, is an Itô process with coefficients `a(x(t), t)`,
`b(x(t), t)` (`IsSDESol.isItoDiffusion_clampProc`), and deduce

* `IsSDESol.dynkin`: `E f(x(t)) = E f(x(s)) + E ∫ₛᵗ L f(x(u), u) du`, `0 ≤ s ≤ t ≤ T`;
* `IsSDESol.isMartingaleOn_itoDynkinProc`: the martingale problem on `[0, T]`;
* `IsSDESol.martingale_itoDynkinProc_clamp`: the Mathlib-`Martingale` form, for a solution
  whose paths are continuous on `[0, T]` for every `ω`.

Extra hypotheses (beyond `SDECoeffs` and `E ξ² < ∞`): `a`, `b` are jointly continuous and `b` is
bounded.  They come from the Itô formula of job E3 (`ito_formula_process_C2`), which needs
continuous drift and noise paths and a bounded noise coefficient; see the plan for the
localisation that would remove the boundedness of `b`.
-/
import SHSLib.Gardiner.Ito.Generator.Dynkin
import SHSLib.Gardiner.Ito.StochDE.Restart

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.Generator

open Gardiner.Ito Gardiner.Ito.StochDE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ}

/-- The process `x` stopped outside `[0, T]`: `clampProc x T t = x((t ∨ 0) ∧ T)`. -/
def clampProc (x : ℝ → Ω → ℝ) (T t : ℝ) (ω : Ω) : ℝ := x (max 0 (min t T)) ω

lemma clamp_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : max 0 (min t T) ∈ Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma clamp_eq {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : max 0 (min t T) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

omit mΩ in
lemma clampProc_eq {x : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    clampProc x T t = x t := by
  funext ω; simp only [clampProc, clamp_eq ht]

lemma continuous_clamp (T : ℝ) : Continuous fun t : ℝ => max 0 (min t T) := by fun_prop

omit mΩ in
/-- The stopped process has continuous paths wherever `x` is continuous on `[0, T]`. -/
lemma continuous_clampProc {x : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (h : ContinuousOn (fun t => x t ω) (Icc 0 T)) : Continuous fun t => clampProc x T t ω :=
  h.comp_continuous (continuous_clamp T) (clamp_mem hT)

/-- Equal processes on `[0, T]` have the same martingale property on `[0, T]`. -/
lemma IsMartingaleOn.congr {M M' : ℝ → Ω → ℝ} {T : ℝ} (hM : IsMartingaleOn M 𝓕 P T)
    (h : ∀ t ∈ Icc (0 : ℝ) T, M t = M' t) : IsMartingaleOn M' 𝓕 P T where
  integrable t ht := h t ht ▸ hM.integrable t ht
  aestronglyMeasurable t ht := h t ht ▸ hM.aestronglyMeasurable t ht
  condExp_eq s t hs hst htT := by
    rw [← h t ⟨hs.trans hst, htT⟩, ← h s ⟨hs, hst.trans htT⟩]
    exact hM.condExp_eq s t hs hst htT

omit mΩ in
/-- The Dynkin processes of `x` and of the stopped process agree on `[0, T]`. -/
lemma itoDynkinProc_clampProc {a b : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {x : ℝ → Ω → ℝ} {T t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : itoDynkinProc a b f (clampProc x T) t = itoDynkinProc a b f x t := by
  funext ω
  simp only [itoDynkinProc]
  rw [clampProc_eq ht, clampProc_eq ⟨le_rfl, ht.1.trans ht.2⟩]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le ht.1] at hu
  simp only [clampProc, clamp_eq ⟨hu.1, hu.2.trans ht.2⟩]

variable (hW : IsFWiener W 𝓕 P)
include hW

namespace IsSDESol

variable {a b : ℝ → ℝ → ℝ} {T K B : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ}

/-- **A solution of a Lipschitz SDE with continuous coefficients and bounded `b` is an Itô
process** with coefficients `a(x(t), t)`, `b(x(t), t)` (after stopping outside `[0, T]`). -/
theorem isItoDiffusion_clampProc (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hT : 0 ≤ T)
    (hc : SDECoeffs a b 0 T K) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) (hB : ∀ y t, |b y t| ≤ B) :
    IsItoDiffusion W 𝓕 P T a b (clampProc x T) := by
  have := hW.isProbabilityMeasure
  have hcm : Measurable fun t : ℝ => max 0 (min t T) := (continuous_clamp T).measurable
  have hxm : Measurable (Function.uncurry (clampProc x T)) :=
    hx.measurable.comp ((hcm.comp measurable_fst).prodMk measurable_snd)
  have had : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (clampProc x T t) := fun t h0 h1 => by
    rw [clampProc_eq ⟨h0, h1⟩]; exact hx.adapted t ⟨h0, h1⟩
  have hbm : Measurable (Function.uncurry fun t ω => b (clampProc x T t ω) t) :=
    hb.measurable.comp (hxm.prodMk measurable_fst)
  have hG : IsItoIntegrand 𝓕 P T (fun t ω => b (clampProc x T t ω) t) := by
    refine ⟨hbm, fun t h0 h1 => ?_, ?_⟩
    · exact (hb.comp (continuous_id.prodMk continuous_const)).comp_stronglyMeasurable
        (had t h0 h1)
    · refine MemLp.of_bound hbm.aestronglyMeasurable B (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs]; exact hB _ _
  have hcont : ∀ᵐ ω ∂P, Continuous fun t => clampProc x T t ω :=
    hx.cont.mono fun ω h => continuous_clampProc hT h
  have hD := hx.isItoIntegrand hc le_rfl
  have hx0 : x 0 =ᵐ[P] ξ := by
    filter_upwards [hx.eq 0 ⟨le_rfl, hT⟩, itoInt_of_nonpos hW le_rfl (hD.mono hT)] with ω h1 h2
    rw [h1, h2]; simp
  refine ⟨hxm, had, hcont, ?_, hG, ?_, fun t h0 h1 => ?_⟩
  · filter_upwards [hcont] with ω h
    exact ha.comp (h.prodMk continuous_id)
  · filter_upwards [hcont] with ω h
    exact hb.comp (h.prodMk continuous_id)
  · have hI := itoInt_congr_of_eq_on hW (hD.mono h1) (hG.mono h1) (fun s hs ω => by
      simp only [drive, afterInd_of_lt hs.1, one_mul]
      rw [clampProc_eq ⟨hs.1.le, hs.2.trans h1⟩])
    rw [clampProc_eq ⟨h0, h1⟩, clampProc_eq ⟨le_rfl, hT⟩]
    filter_upwards [hx.eq t ⟨h0, h1⟩, hx0, hI] with ω e1 e2 e3
    rw [e1, e2, e3]
    congr 2
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le h0] at hu
    simp only [clampProc, clamp_eq ⟨hu.1, hu.2.trans h1⟩]

/-- `f(x(t))` is integrable for a test function `f` with bounded derivative. -/
lemma integrable_comp (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hc : SDECoeffs a b 0 T K)
    (hξ : MemLp ξ 2 P) {f : ℝ → ℝ} {C1 C2 : ℝ} (hf : C2BddDeriv f C1 C2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : Integrable (fun ω => f (x t ω)) P := by
  have := hW.isProbabilityMeasure
  have hm := hx.memLp_apply hW hc le_rfl hξ ht
  have hi : Integrable (x t) P := hm.integrable one_le_two
  refine Integrable.mono' ((integrable_const |f 0|).add (hi.abs.const_mul C1))
    (hf.continuous.comp_aestronglyMeasurable hi.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hf.abs_le _

/-- **Dynkin's formula for solutions of Lipschitz SDEs** (integrated (4.3.18)): for
`0 ≤ s ≤ t ≤ T` and `f ∈ C²` with bounded `f'`, `f''`,
`E f(x(t)) = E f(x(s)) + E ∫ₛᵗ L f(x(u), u) du`. -/
theorem dynkin (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hc : SDECoeffs a b 0 T K)
    (hξ : MemLp ξ 2 P) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) (hB : ∀ y t, |b y t| ≤ B) {f : ℝ → ℝ} {C1 C2 : ℝ}
    (hf : C2BddDeriv f C1 C2) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ∫ ω, f (x t ω) ∂P =
      ∫ ω, f (x s ω) ∂P + ∫ ω, (∫ u in s..t, itoGen a b f u (x u ω)) ∂P := by
  have hT : 0 ≤ T := (hs0.trans hst).trans htT
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  have hy := isItoDiffusion_clampProc hW hx hT hc ha hb hB
  have hmem : ∀ r ∈ Icc (0 : ℝ) T, Integrable (fun ω => f (clampProc x T r ω)) P := fun r hr => by
    rw [clampProc_eq hr]; exact integrable_comp hW hx hc hξ hf hr
  have h := Generator.dynkin hW hy hB0 (fun u _ ω => hB _ _) hf hs0 hst htT (hmem 0 ⟨le_rfl, hT⟩)
    (hmem s ⟨hs0, hst.trans htT⟩) (hmem t ⟨hs0.trans hst, htT⟩)
  rw [clampProc_eq ⟨hs0.trans hst, htT⟩, clampProc_eq ⟨hs0, hst.trans htT⟩] at h
  rw [h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hst] at hu
  simp only [clampProc, clamp_eq ⟨hs0.trans hu.1, hu.2.trans htT⟩]

/-- **The martingale problem for solutions of Lipschitz SDEs**:
`f(x(t)) - f(x(0)) - ∫₀ᵗ L f(x(u), u) du` is a martingale on `[0, T]`. -/
theorem isMartingaleOn_itoDynkinProc (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hT : 0 ≤ T)
    (hc : SDECoeffs a b 0 T K) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) (hB : ∀ y t, |b y t| ≤ B) {f : ℝ → ℝ} {C1 C2 : ℝ}
    (hf : C2BddDeriv f C1 C2) : IsMartingaleOn (itoDynkinProc a b f x) 𝓕 P T := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  exact (Generator.isMartingaleOn_itoDynkinProc hW (isItoDiffusion_clampProc hW hx hT hc ha hb hB)
    hB0 (fun u _ ω => hB _ _) hf).congr fun t ht => itoDynkinProc_clampProc ht

/-- **The martingale problem, Mathlib form, for SDE solutions**: if every path of the solution
is continuous on `[0, T]`, then `t ↦ f(x(t∧T)) - f(x(0)) - ∫₀^{t∧T} L f(x(u), u) du` (frozen at
`0` for `t < 0`) is an `𝓕`-martingale. -/
theorem martingale_itoDynkinProc_clamp (hx : IsSDESol W 𝓕 P a b 0 T ξ x) (hT : 0 ≤ T)
    (hc : SDECoeffs a b 0 T K) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) (hB : ∀ y t, |b y t| ≤ B) {f : ℝ → ℝ} {C1 C2 : ℝ}
    (hf : C2BddDeriv f C1 C2) (hxc : ∀ ω, ContinuousOn (fun t => x t ω) (Icc 0 T)) :
    Martingale (fun t => itoDynkinProc a b f x (max 0 (min t T))) 𝓕 P := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  have h := Generator.martingale_itoDynkinProc_clamp hW hT
    (isItoDiffusion_clampProc hW hx hT hc ha hb hB) hB0 (fun u _ ω => hB _ _) hf
    (fun ω => continuous_clampProc hT (hxc ω)) ha hb
  convert h using 2 with t
  exact (itoDynkinProc_clampProc (clamp_mem hT t)).symm

end IsSDESol

end Gardiner.Ito.Generator
