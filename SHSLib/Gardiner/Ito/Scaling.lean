/-
# Brownian scaling (Gardiner (6.2.39)–(6.2.44))

Gardiner reduces the cubic process `dx = -x³dt + ε dW(t)` to the parameterless form
`dy = -y³dτ + dW(τ)` (6.2.41) by the change of variables `x = √ε y`, `t = τ/ε` (6.2.39) and the
rule (6.2.40) `dW(τ/ε) = dW(τ)/√ε`.  The rule is a statement about **laws**: the rescaled
process `W̃(τ) = √ε W(τ/ε)` is again a standard Wiener process.

* `Gardiner.Ito.IsWiener.scale`: if `W` is a Wiener process (`Gardiner.Ito.IsWiener`) and
  `ε > 0`, then `τ ↦ √ε W(τ/ε)` is a Wiener process on the same probability space, including
  the independence of its future increments from its own natural filtration.  This is the
  law-level form of (6.2.40) (all finite-dimensional laws of `W̃` are those of a standard Wiener
  process).
* `Gardiner.Ito.IsWiener.scale_law_sub`: the law of the rescaled increments explicitly,
  `√ε (W(t/ε) - W(s/ε)) ~ N(0, t - s)`.
* `Gardiner.Ito.cubic_scaling_wiener`: combined with the pathwise change of variables
  `Gardiner.SDE.cubic_scaling` of the Itô-free layer, a pathwise solution of
  `dx = -x³c(x)dt + εb dW` (6.2.33), (6.2.43) driven by a Wiener path becomes, almost surely, a
  pathwise solution of (6.2.44) `dy = -y³c(√εy)dτ + b dW̃` driven by a path of the **Wiener
  process** `W̃`; for `c ≡ 1, b = 1` this is (6.2.41)–(6.2.42).
* Instances: `Gardiner.Ito.stdWiener_scale` (the standard Wiener process, any `ε > 0`), the
  explicit variance check `Gardiner.Ito.stdWiener_scale_two_var` (`⟨(√2 W(τ/2))²⟩ = τ`), and
  `Gardiner.Ito.cubic_scaling_stdWiener` (`c(z) = 1/(1 + z⁴)`, where pathwise solutions exist for
  every Brownian path).
-/
import SHSLib.Gardiner.Ito.Brownian
import SHSLib.Gardiner.SDE.Cubic
import SHSLib.Gardiner.SDE.SchemeMoments

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- The rescaled process `W̃(τ) = √ε W(τ/ε)` of (6.2.40). -/
def scaleW (ε : ℝ) (W : ℝ → Ω → ℝ) (τ : ℝ) (ω : Ω) : ℝ := Real.sqrt ε * W (τ / ε) ω

omit [MeasurableSpace Ω] in
lemma scaleW_sub (ε : ℝ) (W : ℝ → Ω → ℝ) (s t : ℝ) :
    scaleW ε W t - scaleW ε W s = (fun x => Real.sqrt ε * x) ∘ (W (t / ε) - W (s / ε)) := by
  funext ω; simp [scaleW]; ring

namespace IsWiener

variable (hW : IsWiener W P)
include hW

/-- The rescaled increments: `√ε (W(t/ε) - W(s/ε)) ~ N(0, t - s)` for `0 ≤ s ≤ t`. -/
theorem scale_law_sub {ε : ℝ} (hε : 0 < ε) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    P.map (scaleW ε W t - scaleW ε W s) = gaussianReal 0 (t - s).toNNReal := by
  rw [scaleW_sub, ← Measure.map_map (by fun_prop) (hW.measurable_sub _ _),
    hW.law_sub (s / ε) (t / ε) (div_nonneg hs hε.le) (div_le_div_of_nonneg_right hst hε.le),
    gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  have htsε : 0 ≤ t / ε - s / ε := by rw [← sub_div]; exact div_nonneg hts hε.le
  simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hts, Real.coe_toNNReal _ htsε,
    Real.sq_sqrt hε.le]
  field_simp

/-- **(6.2.40), law-level: Brownian scaling.**  If `W` is a standard Wiener process and `ε > 0`,
then `W̃(τ) = √ε W(τ/ε)` is again a standard Wiener process. -/
theorem scale {ε : ℝ} (hε : 0 < ε) : IsWiener (scaleW ε W) P where
  isProbabilityMeasure := hW.isProbabilityMeasure
  measurable τ := (hW.measurable _).const_mul _
  zero := by
    filter_upwards [hW.zero] with ω hω
    simp [scaleW, hω]
  cont := by
    filter_upwards [hW.cont] with ω hω
    exact continuous_const.mul (hω.comp (continuous_id.div_const ε))
  law_sub s t hs hst := hW.scale_law_sub hε s t hs hst
  indep_incr n t ht h0 := by
    have h := (hW.indep_incr n (fun i => t i / ε)
      (fun a b hab => div_le_div_of_nonneg_right (ht hab) hε.le) (div_nonneg h0 hε.le)).comp
      (fun _ x => Real.sqrt ε * x) (fun _ => by fun_prop)
    convert h using 1
    funext i
    exact scaleW_sub ε W _ _
  indep_past s t hs hst := by
    have h := hW.indep_past (s / ε) (t / ε) (div_nonneg hs hε.le)
      (div_le_div_of_nonneg_right hst hε.le)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
    · rw [scaleW_sub, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (by fun_prop : Measurable fun x : ℝ => Real.sqrt ε * x).comap_le
    · refine iSup₂_le fun r hr => ?_
      have hcomp : scaleW ε W r = (fun x => Real.sqrt ε * x) ∘ W (r / ε) := rfl
      rw [hcomp, ← MeasurableSpace.comap_comp]
      refine le_trans (MeasurableSpace.comap_mono
        (by fun_prop : Measurable fun x : ℝ => Real.sqrt ε * x).comap_le) ?_
      exact comap_le_wienerFiltration W hW.measurable (div_nonneg hr.1 hε.le)
        (div_le_div_of_nonneg_right hr.2 hε.le)

end IsWiener

/-- **(6.2.39)–(6.2.44) with a genuine Wiener process.**  Let `W` be a Wiener process and `ε > 0`.
If, almost surely, `x ω` is a pathwise solution of `dx = -x³c(x)dt + εb dW` driven by the path of
`W`, then `W̃(τ) = √ε W(τ/ε)` is again a Wiener process and, almost surely, `y(τ) = x(τ/ε)/√ε`
solves `dy = -y³c(√εy)dτ + b dW̃` on `[0, εT]`, driven by the path of `W̃`. -/
theorem cubic_scaling_wiener (hW : IsWiener W P) {ε : ℝ} (hε : 0 < ε) {c : ℝ → ℝ} {b T : ℝ}
    {x : Ω → ℝ → ℝ}
    (hx : ∀ᵐ ω ∂P, Gardiner.SDE.IsPathSol (fun z => -z ^ 3 * c z) (ε * b) (fun t => W t ω)
      (x ω) T) :
    IsWiener (scaleW ε W) P ∧
      ∀ᵐ ω ∂P, Gardiner.SDE.IsPathSol (fun y => -y ^ 3 * c (Real.sqrt ε * y)) b
        (fun τ => scaleW ε W τ ω) (fun τ => x ω (τ / ε) / Real.sqrt ε) (ε * T) := by
  refine ⟨hW.scale hε, ?_⟩
  filter_upwards [hx] with ω hω
  exact Gardiner.SDE.cubic_scaling hε hω

/-- Instance: every rescaling of the standard Wiener process is a Wiener process. -/
theorem stdWiener_scale {ε : ℝ} (hε : 0 < ε) : IsWiener (scaleW ε stdWiener) stdWienerMeasure :=
  isWiener_stdWiener.scale hε

/-- Explicit check for `ε = 2`: `⟨(√2 W(τ/2))²⟩ = τ` for `τ ≥ 0`. -/
theorem stdWiener_scale_two_var {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ ω, scaleW 2 stdWiener τ ω ^ 2 ∂stdWienerMeasure = τ := by
  have hW := stdWiener_scale (ε := 2) two_pos
  have h := hW.law_sub 0 τ le_rfl hτ
  have h0 := hW.zero
  have hm : Measurable (scaleW 2 stdWiener τ - scaleW 2 stdWiener 0) := hW.measurable_sub _ _
  have hcongr : ∫ ω, scaleW 2 stdWiener τ ω ^ 2 ∂stdWienerMeasure =
      ∫ ω, (fun x : ℝ => x ^ 2) ((scaleW 2 stdWiener τ - scaleW 2 stdWiener 0) ω)
        ∂stdWienerMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [h0] with ω hω
    simp [hω]
  rw [hcongr, Gardiner.SDE.integral_comp_gauss hm h (f := fun x : ℝ => x ^ 2) (continuous_pow 2),
    Gardiner.SDE.gauss_m2, sub_zero, Real.coe_toNNReal _ hτ]

/-! ### Instance of `cubic_scaling_wiener` with an existing solution

For `c(z) = 1/(1 + z⁴)` (so `c(0) = 1 ≠ 0`, as (6.2.43) requires) the drift `-z³c(z)` is bounded
and Lipschitz, so pathwise solutions driven by Brownian paths exist and the rescaling applies. -/

/-- The saturating factor `c(z) = 1/(1 + z⁴)`. -/
def cubicSat (z : ℝ) : ℝ := 1 / (1 + z ^ 4)

lemma cubicSat_drift_bound (z : ℝ) : |-z ^ 3 * cubicSat z| ≤ (1 : ℝ≥0) := by
  have hp : 0 < 1 + z ^ 4 := by positivity
  rw [cubicSat, abs_mul, abs_neg, abs_div, abs_one, abs_of_pos hp, abs_pow, mul_one_div,
    NNReal.coe_one, div_le_one hp]
  have ha := abs_nonneg z
  have h4 : z ^ 4 = |z| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [h4]
  rcases le_total |z| 1 with h | h
  · nlinarith [pow_le_one₀ ha h (n := 3), pow_nonneg ha 4]
  · nlinarith [pow_le_pow_right₀ h (show 3 ≤ 4 by norm_num), pow_nonneg ha 3]

lemma cubicSat_drift_lipschitz : LipschitzWith 4 (fun z : ℝ => -z ^ 3 * cubicSat z) := by
  have hd : ∀ z : ℝ, HasDerivAt (fun z : ℝ => -z ^ 3 * cubicSat z)
      (-(3 * z ^ 2 - z ^ 6) / (1 + z ^ 4) ^ 2) z := by
    intro z
    have hp : (1 + z ^ 4) ≠ 0 := by positivity
    have h1 := ((hasDerivAt_pow 3 z).neg).mul ((hasDerivAt_const z (1 : ℝ)).div
      ((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_pow 4 z)) hp)
    convert h1 using 1
    simp only [Pi.neg_apply, Pi.div_apply, Pi.add_apply]
    push_cast
    field_simp
    ring
  refine lipschitzWith_of_nnnorm_deriv_le (fun z => (hd z).differentiableAt) fun z => ?_
  rw [(hd z).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  have hp : 0 < (1 + z ^ 4) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_neg]
  set u := z ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg z
  have h6 : z ^ 6 = u ^ 3 := by rw [hu]; ring
  have h4 : z ^ 4 = u ^ 2 := by rw [hu]; ring
  rw [h6, h4]
  have hu3 : u ^ 3 ≤ 1 + u ^ 4 := by
    rcases le_total u 1 with h | h
    · nlinarith [pow_le_one₀ hu0 h (n := 3), pow_nonneg hu0 4]
    · nlinarith [pow_le_pow_right₀ h (show 3 ≤ 4 by norm_num), pow_nonneg hu0 3]
  rw [abs_le]
  push_cast
  constructor <;> nlinarith [sq_nonneg (u - 1), pow_nonneg hu0 3, pow_nonneg hu0 4, sq_nonneg u]

/-- **Instance of (6.2.39)–(6.2.44) with the standard Wiener process**, `c(z) = 1/(1 + z⁴)`: for
every `ε > 0` the rescaled process `√ε W(τ/ε)` is a Wiener process, and for every sample point the
equation `dx = -x³c(x)dt + εb dW` has a pathwise solution with `x(0) = 0` whose rescaling
`y(τ) = x(τ/ε)/√ε` solves `dy = -y³c(√εy)dτ + b dW̃` driven by the rescaled Brownian path. -/
theorem cubic_scaling_stdWiener {ε : ℝ} (hε : 0 < ε) (b : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsWiener (scaleW ε stdWiener) stdWienerMeasure ∧
      ∀ ω : StdWienerSpace, ∃ x : ℝ → ℝ, x 0 = 0 ∧
        Gardiner.SDE.IsPathSol (fun z => -z ^ 3 * cubicSat z) (ε * b)
          (fun t => stdWiener t ω) x T ∧
        Gardiner.SDE.IsPathSol (fun y => -y ^ 3 * cubicSat (Real.sqrt ε * y)) b
          (fun τ => scaleW ε stdWiener τ ω) (fun τ => x (τ / ε) / Real.sqrt ε) (ε * T) := by
  refine ⟨stdWiener_scale hε, fun ω => ?_⟩
  obtain ⟨x, hx0, hx⟩ := Gardiner.SDE.exists_pathSol cubicSat_drift_lipschitz
    cubicSat_drift_bound (ε * b) (continuous_stdWiener ω) hT 0
  exact ⟨x, hx0, hx, Gardiner.SDE.cubic_scaling hε hx⟩

end Gardiner.Ito
