/-
# The generator of an Itô diffusion; test functions (Gardiner §4.3.4)

* `itoGen a b f t y = a(y, t) f'(y) + ½ b(y, t)² f''(y)`: the generator `L` of the Itô SDE
  `dx = a(x, t) dt + b(x, t) dW` acting on a test function `f`, evaluated at time `t` and point `y`
  (the right-hand side of (4.3.18)).  Derivatives are Mathlib's `deriv f`, `deriv (deriv f)`.
* `itoDynkinProc a b f x t ω = f(x(t)) - f(x(0)) - ∫₀ᵗ L f(x(u), u) du`, the compensated process
  of the martingale problem.
* `IsMartingaleOn M 𝓕 P T`: the martingale property on the time interval `[0, T]`
  (integrability, a.e. adaptedness, `E[M t | 𝓕 s] = M s` a.s. for `0 ≤ s ≤ t ≤ T`).
* `C2BddDeriv f C1 C2`: `f ∈ C²` with `|f'| ≤ C1`, `|f''| ≤ C2`; every `C²` function with
  compact support is such a test function and is bounded (`exists_c2BddDeriv_of_hasCompactSupport`).
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set

noncomputable section

namespace Gardiner.Ito.Generator

/-- **The generator** of the Itô SDE `dx = a(x, t) dt + b(x, t) dW` (Gardiner (4.3.18)):
`L f (y, t) = a(y, t) ∂_y f(y) + ½ b(y, t)² ∂²_y f(y)`.  Arguments: the coefficients, the test
function, the time, the point. -/
def itoGen (a b : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (t y : ℝ) : ℝ :=
  a y t * deriv f y + b y t ^ 2 / 2 * deriv (deriv f) y

lemma contDiff_one_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) :=
  hf.deriv'

lemma continuous_deriv2_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (deriv (deriv f)) := by
  have h : ContDiff ℝ (0 + 1) (deriv f) := by simpa using contDiff_one_deriv hf
  exact ((contDiff_succ_iff_deriv.mp h).2.2).continuous

/-- The generator is additive in the test function (for differentiable test functions). -/
lemma itoGen_add (a b : ℝ → ℝ → ℝ) {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (t y : ℝ) : itoGen a b (f + g) t y = itoGen a b f t y + itoGen a b g t y := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (deriv f) := (contDiff_one_deriv hf).differentiable one_ne_zero
  have hg2 : Differentiable ℝ (deriv g) := (contDiff_one_deriv hg).differentiable one_ne_zero
  have e1 : deriv (f + g) = deriv f + deriv g := by
    funext z; exact deriv_add (hf1 z) (hg1 z)
  have e2 : deriv (deriv (f + g)) y = deriv (deriv f) y + deriv (deriv g) y := by
    rw [e1]; exact deriv_add (hf2 y) (hg2 y)
  simp only [itoGen, e2]
  rw [e1, Pi.add_apply]
  ring

/-- The generator kills constants. -/
@[simp] lemma itoGen_const (a b : ℝ → ℝ → ℝ) (c t y : ℝ) : itoGen a b (fun _ => c) t y = 0 := by
  simp [itoGen]

/-- The generator of an autonomous SDE does not depend on time. -/
lemma itoGen_autonomous (a b : ℝ → ℝ) (f : ℝ → ℝ) (t s y : ℝ) :
    itoGen (fun y _ => a y) (fun y _ => b y) f t y = itoGen (fun y _ => a y) (fun y _ => b y) f s y :=
  rfl

/-- **The compensated (Dynkin) process** of the martingale problem:
`f(x(t)) - f(x(0)) - ∫₀ᵗ L f(x(u), u) du`. -/
def itoDynkinProc {Ω : Type*} (a b : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    ℝ :=
  f (x t ω) - f (x 0 ω) - ∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω)

@[simp] lemma itoDynkinProc_zero {Ω : Type*} (a b : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x : ℝ → Ω → ℝ)
    (ω : Ω) : itoDynkinProc a b f x 0 ω = 0 := by
  simp [itoDynkinProc]

/-- **Martingale on `[0, T]`**: `M t` is integrable and almost everywhere equal to an
`𝓕 t`-measurable function, and `E[M t | 𝓕 s] = M s` almost surely for `0 ≤ s ≤ t ≤ T`. -/
structure IsMartingaleOn {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : ℝ → Ω → ℝ)
    (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ) : Prop where
  integrable : ∀ t ∈ Icc (0 : ℝ) T, Integrable (M t) P
  aestronglyMeasurable : ∀ t ∈ Icc (0 : ℝ) T, AEStronglyMeasurable[𝓕 t] (M t) P
  condExp_eq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → P[M t | 𝓕 s] =ᵐ[P] M s

/-- **Test functions** for Dynkin's formula: `f ∈ C²` with `|f'| ≤ C1` and `|f''| ≤ C2`. -/
structure C2BddDeriv (f : ℝ → ℝ) (C1 C2 : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  bdd1 : ∀ y, |deriv f y| ≤ C1
  bdd2 : ∀ y, |deriv (deriv f) y| ≤ C2

namespace C2BddDeriv

variable {f : ℝ → ℝ} {C1 C2 : ℝ} (hf : C2BddDeriv f C1 C2)
include hf

lemma hasDerivAt (y : ℝ) : HasDerivAt f (deriv f y) y :=
  ((hf.contDiff.differentiable (by norm_num)) y).hasDerivAt

lemma hasDerivAt_deriv (y : ℝ) : HasDerivAt (deriv f) (deriv (deriv f) y) y :=
  (((contDiff_one_deriv hf.contDiff).differentiable one_ne_zero) y).hasDerivAt

lemma continuous : Continuous f := hf.contDiff.continuous

lemma continuous_deriv : Continuous (deriv f) := (contDiff_one_deriv hf.contDiff).continuous

lemma continuous_deriv2 : Continuous (deriv (deriv f)) :=
  continuous_deriv2_of_contDiff hf.contDiff

lemma C1_nonneg : 0 ≤ C1 := (abs_nonneg _).trans (hf.bdd1 0)

lemma C2_nonneg : 0 ≤ C2 := (abs_nonneg _).trans (hf.bdd2 0)

/-- A `C²` function with bounded first derivative grows at most linearly. -/
lemma abs_le (y : ℝ) : |f y| ≤ |f 0| + C1 * |y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f) (C := C1)
    (s := univ) (fun z _ => (hf.hasDerivAt z).differentiableAt)
    (fun z _ => by rw [Real.norm_eq_abs]; exact hf.bdd1 z) convex_univ (mem_univ 0) (mem_univ y)
  simp only [Real.norm_eq_abs, sub_zero] at h
  have := abs_sub_abs_le_abs_sub (f y) (f 0)
  linarith

end C2BddDeriv

/-- **Compactly supported `C²` functions are test functions**: they are bounded and have bounded
first and second derivatives. -/
lemma exists_c2BddDeriv_of_hasCompactSupport {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ∃ C0 C1 C2 : ℝ, (∀ y, |f y| ≤ C0) ∧ C2BddDeriv f C1 C2 := by
  have h1 : ContDiff ℝ 1 (deriv f) := contDiff_one_deriv hf
  have h2c : Continuous (deriv (deriv f)) := continuous_deriv2_of_contDiff hf
  obtain ⟨C0, hC0⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨C1, hC1⟩ := h1.continuous.bounded_above_of_compact_support hfc.deriv
  obtain ⟨C2, hC2⟩ := h2c.bounded_above_of_compact_support hfc.deriv.deriv
  exact ⟨C0, C1, C2, fun y => by simpa using hC0 y,
    ⟨hf, fun y => by simpa using hC1 y, fun y => by simpa using hC2 y⟩⟩

end Gardiner.Ito.Generator
