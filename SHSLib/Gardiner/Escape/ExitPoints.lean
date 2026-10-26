/-
# Bistability in several dimensions, I: exit points and the mean exit time, §9.3.1–9.3.3

The Matkowsky–Schuss construction of §9.3.1–9.3.2 consists of three exact one-dimensional
layer problems, glued together by a Green's-theorem identity over the region `R` and its
boundary `S`.  We formalise the layer problems exactly and take the Green identity (the
`d`-dimensional integration by parts (9.3.24)–(9.3.25) with the leading-order boundary-layer
gradients inserted) as a **named hypothesis**, from which the formulae for `C₀` follow exactly.
The surface `S` is modelled by an arbitrary measure space `(α, μ)` with integrable weights.

* `interior_layer`, `interior_layer_unbounded` — **(9.3.12)–(9.3.14)**: the inner solution
  `π = C₁∫₀^ξ e^{t²/2H} + π₀` solves `-ξπ' + Hπ'' = 0`, and it is bounded only if `C₁ = 0`;
* `boundary_layer`, `boundary_layer_tendsto` — **(9.3.18)–(9.3.22), corrected sign**:
  `f'' = (v·ν) f'`, `f = g + C₁(1 - e^{(v·ν)ρ})`, which tends to `g + C₁` because `v·ν < 0`;
  `boundary_layer_printed_unbounded` — the printed solution blows up when `v·ν < 0`;
* `exit_C0` — **(9.3.25)–(9.3.28), corrected**: `C₀ = -∫ e^{-φ/ε} g ν·∇φ / ∫ e^{-φ/ε} v·ν`;
  `exit_C0_potential` — in the potential case `ν·∇φ = -v·ν` (9.3.30) this is the printed
  (9.3.28)/(9.3.31) value; `exit_C0_printed_wrong` — without (9.3.30) the printed (9.3.28) fails;
* `separatrix_layer`, `separatrix_layer_tendsto` — **(9.3.33)–(9.3.35)** (correct as printed);
  `separatrix_C0` — **(9.3.36), corrected**;
* `meanExit_C0` — **(9.3.40)–(9.3.43), corrected**:
  `T = ∫_R e^{-φ/ε} / ∫_S e^{-φ/ε} |v·ν|` (positive);
* `kramers_multi_integrated`, `kramers_multi_relaxation` — **(9.3.59)** exactly and
  **(9.3.59) ⇒ (9.3.63)** under the named peak-evaluation hypothesis.
* `exitPoints_instance` — concrete layers and a one-point exit set.

**Errata recorded.**
(9.3.18) the normal derivative enters with the opposite sign: `x = u - ερν` gives
`ν·∇ = -ε⁻¹∂_ρ`, hence `-(v·ν)∂_ρ f + ∂²_ρ f = 0`; the printed (9.3.19) `1 - e^{-(v·ν)ρ}` is
unbounded for the inward flow `v·ν < 0` assumed in §9.3.1 (correct: `1 - e^{(v·ν)ρ}`).
(9.3.26) the right-hand side lacks the factor `ε⁻¹` and has the wrong sign: correctly
`ε ν·∇f = (v·ν)(C₀ - g)`.  The printed (9.3.28) (numerator `2v·ν + ν·∇φ`) is what the sign slip
produces; it agrees with the correct `-ν·∇φ` exactly when `(v + ∇φ)·ν = 0`, in particular in
the potential case (9.3.30), which is the only case the text goes on to use.
(9.3.36) on a separatrix `v·ν = 0`, so the printed factors `v·ν(b)`, `v·ν(x)` vanish; the
correct statement is `C₀ ∫ e^{-φ/ε} √(2εκ/π) = ∫ e^{-φ/ε}[√(2εκ/π) + ν·∇φ] g`.
(9.3.40) the right-hand side has the wrong sign (`+∫ e^{-φ/ε} C₀ v·ν`), so (9.3.41) as printed is
negative; the correct denominator is `∫_S e^{-φ/ε}|v·ν|`.  (9.3.43) `e^{φ/ε}` must be `e^{-φ/ε}`,
and the left-hand side is `T(x) = e^{K/ε}τ(x)`, not `τ(x)`.
-/
import SHSLib.Gardiner.Escape.FirstPassage

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-! ### (9.3.12)–(9.3.14): the interior layer near the stable point -/

/-- The inner solution (9.3.13): `π(ξ) = C₁ ∫₀^ξ e^{t²/2H} dt + π₀`. -/
def innerSol (H C₁ π₀ ξ : ℝ) : ℝ := C₁ * (∫ t in (0 : ℝ)..ξ, exp (t ^ 2 / (2 * H))) + π₀

/-- **(9.3.12)–(9.3.13)**: `π = C₁∫₀^ξ e^{t²/2H} + π₀` solves `-ξ π' + H π'' = 0`. -/
theorem interior_layer {H : ℝ} (hH : H ≠ 0) (C₁ π₀ ξ : ℝ) :
    HasDerivAt (innerSol H C₁ π₀) (C₁ * exp (ξ ^ 2 / (2 * H))) ξ ∧
    HasDerivAt (fun ξ => C₁ * exp (ξ ^ 2 / (2 * H)))
      (C₁ * (exp (ξ ^ 2 / (2 * H)) * (ξ / H))) ξ ∧
    -ξ * (C₁ * exp (ξ ^ 2 / (2 * H))) + H * (C₁ * (exp (ξ ^ 2 / (2 * H)) * (ξ / H))) = 0 := by
  have hc : Continuous fun t : ℝ => exp (t ^ 2 / (2 * H)) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · unfold innerSol
    exact ((hc.integral_hasStrictDerivAt 0 ξ).hasDerivAt.const_mul C₁).add_const π₀
  · have h1 : HasDerivAt (fun ξ : ℝ => ξ ^ 2 / (2 * H)) (ξ / H) ξ := by
      convert ((hasDerivAt_pow 2 ξ).div_const (2 * H)) using 1
      field_simp; ring
    exact h1.exp.const_mul C₁
  · field_simp; ring

/-- **(9.3.14)**: because `H > 0` the inner solution is unbounded unless `C₁ = 0`
(`|π(ξ) - π₀| ≥ |C₁| ξ`), so matching to the bounded outer solution forces `π ≡ π₀`. -/
theorem interior_layer_unbounded {H : ℝ} (hH : 0 < H) {C₁ : ℝ} (hC : C₁ ≠ 0) (π₀ : ℝ) :
    ¬ ∃ M, ∀ ξ, 0 ≤ ξ → |innerSol H C₁ π₀ ξ| ≤ M := by
  rintro ⟨M, hM⟩
  have key : ∀ ξ, 0 ≤ ξ → ξ ≤ ∫ t in (0 : ℝ)..ξ, exp (t ^ 2 / (2 * H)) := by
    intro ξ hξ
    have : ∫ t in (0 : ℝ)..ξ, (1 : ℝ) ≤ ∫ t in (0 : ℝ)..ξ, exp (t ^ 2 / (2 * H)) := by
      apply intervalIntegral.integral_mono_on hξ (by simp)
        ((by fun_prop : Continuous fun t : ℝ => exp (t ^ 2 / (2 * H))).intervalIntegrable _ _)
      intro t _
      exact one_le_exp (by positivity)
    simpa using this
  set ξ := (|M| + |π₀| + 1) / |C₁| with hξ
  have hCpos : 0 < |C₁| := abs_pos.mpr hC
  have hξ0 : 0 ≤ ξ := by positivity
  have h1 := hM ξ hξ0
  have h2 := key ξ hξ0
  unfold innerSol at h1
  have h3 : |C₁| * ξ ≤ |C₁ * ∫ t in (0 : ℝ)..ξ, exp (t ^ 2 / (2 * H))| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h2.trans (le_abs_self _)) hCpos.le
  have h4 : |C₁| * ξ = |M| + |π₀| + 1 := by rw [hξ]; field_simp
  have h5 := abs_add_le (C₁ * (∫ t in (0 : ℝ)..ξ, exp (t ^ 2 / (2 * H))) + π₀) (-π₀)
  simp only [add_neg_cancel_right, abs_neg] at h5
  linarith [le_abs_self M]

/-! ### (9.3.18)–(9.3.22): the boundary layer -/

/-- The boundary-layer profile (9.3.19), corrected: `f(ρ) = g + C₁(1 - e^{cρ})`, `c = v·ν`. -/
def bdryLayer (c g C₁ ρ : ℝ) : ℝ := g + C₁ * (1 - exp (c * ρ))

/-- **(9.3.18), corrected**: with `x = u - ερν` the leading-order equation is
`-(v·ν) f' + f'' = 0`, solved by `f = g + C₁(1 - e^{(v·ν)ρ})` with `f(0) = g`. -/
theorem boundary_layer (c g C₁ ρ : ℝ) :
    HasDerivAt (bdryLayer c g C₁) (-(C₁ * c * exp (c * ρ))) ρ ∧
    HasDerivAt (fun ρ => -(C₁ * c * exp (c * ρ))) (-(C₁ * c * (c * exp (c * ρ)))) ρ ∧
    -c * (-(C₁ * c * exp (c * ρ))) + -(C₁ * c * (c * exp (c * ρ))) = 0 ∧
    bdryLayer c g C₁ 0 = g := by
  have he : HasDerivAt (fun ρ => exp (c * ρ)) (c * exp (c * ρ)) ρ := by
    simpa [mul_comm] using ((hasDerivAt_id ρ).const_mul c).exp
  refine ⟨?_, ?_, by ring, by simp [bdryLayer]⟩
  · unfold bdryLayer
    convert ((he.const_sub 1).const_mul C₁).const_add g using 1; ring
  · convert (he.const_mul (C₁ * c)).neg using 1

/-- **(9.3.20)–(9.3.22)**: for the inward flow `v·ν < 0` the profile tends to `g + C₁`, so
matching with the interior constant `C₀` gives `C₁ = C₀ - g`. -/
theorem boundary_layer_tendsto {c : ℝ} (hc : c < 0) (g C₁ : ℝ) :
    Tendsto (bdryLayer c g C₁) atTop (𝓝 (g + C₁)) := by
  have h : Tendsto (fun ρ => exp (c * ρ)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)
  have := ((h.const_sub 1).const_mul C₁).const_add g
  simpa [bdryLayer] using this

/-- **(9.3.19) as printed** (`1 - e^{-(v·ν)ρ}`) is unbounded for the inward flow `v·ν < 0`
whenever `C₁ ≠ 0`, so it cannot be matched to the interior. -/
theorem boundary_layer_printed_unbounded {c : ℝ} (hc : c < 0) (g : ℝ) {C₁ : ℝ}
    (hC : C₁ ≠ 0) : Tendsto (fun ρ => |g + C₁ * (1 - exp (-c * ρ))|) atTop atTop := by
  have h : Tendsto (fun ρ => exp (-c * ρ)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
  have h2 : Tendsto (fun ρ => |C₁| * (exp (-c * ρ) - (1 + |g| / |C₁|))) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ h).const_mul_atTop (abs_pos.mpr hC)
  refine tendsto_atTop_mono (fun ρ => ?_) h2
  have hCpos : 0 < |C₁| := abs_pos.mpr hC
  have e : |C₁| * (exp (-c * ρ) - (1 + |g| / |C₁|)) = |C₁| * (exp (-c * ρ) - 1) - |g| := by
    field_simp; ring
  rw [e]
  have h3 : |C₁ * (1 - exp (-c * ρ))| ≤ |g + C₁ * (1 - exp (-c * ρ))| + |g| := by
    have := abs_sub (g + C₁ * (1 - exp (-c * ρ))) g
    simpa using this
  have h4 : |C₁ * (1 - exp (-c * ρ))| = |C₁| * |exp (-c * ρ) - 1| := by
    rw [abs_mul, abs_sub_comm]
  have h5 : exp (-c * ρ) - 1 ≤ |exp (-c * ρ) - 1| := le_abs_self _
  nlinarith

/-! ### (9.3.25)–(9.3.31): the constant `C₀` -/

section C0

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **(9.3.25)–(9.3.28), corrected.**  The surface integrand of (9.3.25) at the boundary, with
the correct leading-order gradients `ε ν·∇f = (v·ν)(C₀ - g)` [(9.3.26) corrected] and
`ε ν·∇p_s = -(ν·∇φ) e^{-φ/ε}` (9.3.27), is `e^{-φ/ε}[(v·ν)g + (v·ν)(C₀ - g) + g ν·∇φ]`.  If its
integral vanishes (the Green identity, a named hypothesis) then
`C₀ = -∫ e^{-φ/ε} g ν·∇φ / ∫ e^{-φ/ε} v·ν`. -/
theorem exit_C0 {w vn dphi g : α → ℝ} {C₀ : ℝ}
    (hi1 : Integrable (fun u => w u * vn u) μ) (hi2 : Integrable (fun u => w u * g u * dphi u) μ)
    (hden : ∫ u, w u * vn u ∂μ ≠ 0)
    (hgreen : ∫ u, w u * (vn u * g u + vn u * (C₀ - g u) + g u * dphi u) ∂μ = 0) :
    C₀ = -(∫ u, w u * g u * dphi u ∂μ) / ∫ u, w u * vn u ∂μ := by
  have e : (fun u => w u * (vn u * g u + vn u * (C₀ - g u) + g u * dphi u))
      = fun u => C₀ * (w u * vn u) + w u * g u * dphi u := by ext u; ring
  rw [e, integral_add (hi1.const_mul C₀) hi2, integral_const_mul] at hgreen
  rw [eq_div_iff hden]; linarith

/-- **(9.3.28)/(9.3.31) in the potential case (9.3.30)** `v = -∇φ` (`ν·∇φ = -v·ν`):
`C₀ = ∫ e^{-φ/ε} (v·ν) g / ∫ e^{-φ/ε} v·ν`, which is also the value of the printed (9.3.28),
since then `2v·ν + ν·∇φ = v·ν`. -/
theorem exit_C0_potential {w vn dphi g : α → ℝ} {C₀ : ℝ}
    (hpot : ∀ u, dphi u = -vn u)
    (hi1 : Integrable (fun u => w u * vn u) μ) (hi3 : Integrable (fun u => w u * vn u * g u) μ)
    (hden : ∫ u, w u * vn u ∂μ ≠ 0)
    (hgreen : ∫ u, w u * (vn u * g u + vn u * (C₀ - g u) + g u * dphi u) ∂μ = 0) :
    C₀ = (∫ u, w u * vn u * g u ∂μ) / ∫ u, w u * vn u ∂μ ∧
    C₀ = (∫ u, w u * (2 * vn u + dphi u) * g u ∂μ) / ∫ u, w u * vn u ∂μ := by
  have e1 : (fun u => w u * g u * dphi u) = fun u => -(w u * vn u * g u) := by
    ext u; rw [hpot]; ring
  have hi2 : Integrable (fun u => w u * g u * dphi u) μ := by rw [e1]; exact hi3.neg
  have h := exit_C0 hi1 hi2 hden hgreen
  rw [e1, integral_neg, neg_neg] at h
  refine ⟨h, ?_⟩
  have e2 : (fun u => w u * (2 * vn u + dphi u) * g u) = fun u => w u * vn u * g u := by
    ext u; rw [hpot]; ring
  rw [e2]; exact h

/-- **(9.3.28) as printed is wrong without the potential condition (9.3.30)**: for a single
boundary point (`μ = δ`) with `v·ν = -1`, `ν·∇φ = 0`, `g = 1` the Green identity forces
`C₀ = 0`, while the printed formula gives `2`. -/
theorem exit_C0_printed_wrong :
    let μ : Measure ℝ := Measure.dirac 0
    let w : ℝ → ℝ := fun _ => 1
    let vn : ℝ → ℝ := fun _ => -1
    let dphi : ℝ → ℝ := fun _ => 0
    let g : ℝ → ℝ := fun _ => 1
    (∫ u, w u * (vn u * g u + vn u * (0 - g u) + g u * dphi u) ∂μ = 0) ∧
    (∫ u, w u * (2 * vn u + dphi u) * g u ∂μ) / ∫ u, w u * vn u ∂μ = 2 := by
  simp only
  constructor <;> simp

end C0

/-! ### (9.3.33)–(9.3.36): the separatrix layer -/

/-- The separatrix-layer profile (9.3.34): `f(ρ) = g + C₁ ∫₀^ρ e^{-κs²/2} ds`. -/
def sepLayer (κ g C₁ ρ : ℝ) : ℝ := g + C₁ * ∫ s in (0 : ℝ)..ρ, exp (-(κ / 2) * s ^ 2)

/-- **(9.3.33)–(9.3.34)**: `f = g + C₁∫₀^ρ e^{-κs²/2}` solves `κ ρ f' + f'' = 0`, `f(0) = g`. -/
theorem separatrix_layer (κ g C₁ ρ : ℝ) :
    HasDerivAt (sepLayer κ g C₁) (C₁ * exp (-(κ / 2) * ρ ^ 2)) ρ ∧
    HasDerivAt (fun ρ => C₁ * exp (-(κ / 2) * ρ ^ 2))
      (C₁ * (exp (-(κ / 2) * ρ ^ 2) * (-κ * ρ))) ρ ∧
    κ * ρ * (C₁ * exp (-(κ / 2) * ρ ^ 2)) + C₁ * (exp (-(κ / 2) * ρ ^ 2) * (-κ * ρ)) = 0 ∧
    sepLayer κ g C₁ 0 = g := by
  have hc : Continuous fun s : ℝ => exp (-(κ / 2) * s ^ 2) := by fun_prop
  refine ⟨?_, ?_, by ring, by simp [sepLayer]⟩
  · exact ((hc.integral_hasStrictDerivAt 0 ρ).hasDerivAt.const_mul C₁).const_add g
  · have h1 : HasDerivAt (fun ρ : ℝ => -(κ / 2) * ρ ^ 2) (-κ * ρ) ρ := by
      convert ((hasDerivAt_pow 2 ρ).const_mul (-(κ / 2))) using 1; ring
    exact h1.exp.const_mul C₁

/-- **(9.3.35)**: for `κ > 0`, `f → g + C₁ √(π/(2κ))` as `ρ → ∞`, so matching with `C₀` gives
`C₁ = (C₀ - g)√(2κ/π)`. -/
theorem separatrix_layer_tendsto {κ : ℝ} (hκ : 0 < κ) (g C₁ : ℝ) :
    Tendsto (sepLayer κ g C₁) atTop (𝓝 (g + C₁ * √(π / (2 * κ)))) ∧
    ∀ C₀, g + C₁ * √(π / (2 * κ)) = C₀ → C₁ = (C₀ - g) * √(2 * κ / π) := by
  constructor
  · have hint : IntegrableOn (fun s : ℝ => exp (-(κ / 2) * s ^ 2)) (Ioi 0) :=
      (integrable_exp_neg_mul_sq (by linarith)).integrableOn
    have h := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    rw [integral_gaussian_Ioi] at h
    have e : √(π / (κ / 2)) / 2 = √(π / (2 * κ)) := by
      rw [show π / (κ / 2) = 4 * (π / (2 * κ)) by field_simp; ring, sqrt_mul (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
      ring
    rw [e] at h
    exact (h.const_mul C₁).const_add g
  · intro C₀ h
    have hp : 0 < π / (2 * κ) := by positivity
    have e : √(π / (2 * κ)) * √(2 * κ / π) = 1 := by
      rw [← sqrt_mul hp.le, show π / (2 * κ) * (2 * κ / π) = 1 by field_simp, sqrt_one]
    calc C₁ = C₁ * (√(π / (2 * κ)) * √(2 * κ / π)) := by rw [e, mul_one]
      _ = (C₀ - g) * √(2 * κ / π) := by rw [← h]; ring

/-- **(9.3.36), corrected.**  On a separatrix `v·ν = 0`, so the only surface terms in (9.3.25) are
`ε p_s ν·∇f = -√ε C₁ e^{-φ/ε}` with `C₁ = (C₀ - g)√(2κ/π)` (9.3.35), and `-ε f ν·∇p_s =
g (ν·∇φ) e^{-φ/ε}`.  If the integral vanishes (Green identity, named hypothesis) then
`C₀ ∫ e^{-φ/ε}√(2εκ/π) = ∫ e^{-φ/ε}[√(2εκ/π) + ν·∇φ] g`; in the potential case (`ν·∇φ = 0` on
the separatrix) `C₀` is the `e^{-φ/ε}√κ`-weighted mean of `g`. -/
theorem separatrix_C0 {α : Type*} [MeasurableSpace α] {μ : Measure α} {w k dphi g : α → ℝ}
    {C₀ : ℝ} (hi1 : Integrable (fun u => w u * k u) μ)
    (hi2 : Integrable (fun u => w u * (k u + dphi u) * g u) μ)
    (hgreen : ∫ u, w u * (-(k u * (C₀ - g u)) + g u * dphi u) ∂μ = 0) :
    C₀ * ∫ u, w u * k u ∂μ = ∫ u, w u * (k u + dphi u) * g u ∂μ := by
  have e : (fun u => w u * (-(k u * (C₀ - g u)) + g u * dphi u))
      = fun u => w u * (k u + dphi u) * g u - C₀ * (w u * k u) := by ext u; ring
  rw [e, integral_sub hi2 (hi1.const_mul C₀), integral_const_mul] at hgreen
  linarith

/-! ### (9.3.38)–(9.3.43): the mean exit time -/

/-- **(9.3.40)–(9.3.43), corrected.**  With `τ = C₀(1 - e^{(v·ν)ρ})` near `S` (so
`ε ν·∇τ = (v·ν) C₀` on `S`), Green's identity reads
`-e^{-K/ε} ∫_R e^{-φ/ε} = ∫_S e^{-φ/ε} (v·ν) C₀` (named hypothesis).  For inward flow
`v·ν < 0` this gives `C₀ = e^{-K/ε}∫_R e^{-φ/ε} / ∫_S e^{-φ/ε}|v·ν| > 0`, i.e. the mean exit
time `T = e^{K/ε} C₀ = ∫_R e^{-φ/ε} / ∫_S e^{-φ/ε}|v·ν|`. -/
theorem meanExit_C0 {α : Type*} [MeasurableSpace α] {μ : Measure α} [NeZero μ]
    {w vn : α → ℝ} {IR K ε C₀ : ℝ}
    (hw : ∀ u, 0 < w u) (hvn : ∀ u, vn u < 0) (hi : Integrable (fun u => w u * vn u) μ)
    (hIR : 0 < IR)
    (hgreen : -(exp (-K / ε) * IR) = ∫ u, w u * vn u * C₀ ∂μ) :
    C₀ = exp (-K / ε) * IR / ∫ u, w u * |vn u| ∂μ ∧ 0 < C₀ ∧
    exp (K / ε) * C₀ = IR / ∫ u, w u * |vn u| ∂μ := by
  have habs : (fun u => w u * |vn u|) = fun u => -(w u * vn u) := by
    ext u; rw [abs_of_neg (hvn u)]; ring
  have hpos : 0 < ∫ u, w u * |vn u| ∂μ := by
    rw [habs]
    have h0 : 0 < ∫ u, -(w u * vn u) ∂μ := by
      refine integral_pos_iff_support_of_nonneg (fun u => ?_) hi.neg |>.mpr ?_
      · have := mul_neg_of_pos_of_neg (hw u) (hvn u); simp; linarith
      · have : Function.support (-fun u => w u * vn u) = univ := by
          ext u; simp [(hw u).ne', (hvn u).ne]
        rw [this]; simpa using NeZero.ne μ
    exact h0
  have e2 : ∫ u, w u * vn u * C₀ ∂μ = -(C₀ * ∫ u, w u * |vn u| ∂μ) := by
    rw [habs, integral_neg, integral_mul_const]; ring
  rw [e2] at hgreen
  have hC : C₀ = exp (-K / ε) * IR / ∫ u, w u * |vn u| ∂μ := by
    rw [eq_div_iff hpos.ne']; linarith
  refine ⟨hC, by rw [hC]; positivity, ?_⟩
  rw [hC, ← mul_div_assoc, ← mul_assoc, ← exp_add]
  simp [neg_div]

/-! ### (9.3.59)–(9.3.64): Kramers' method in several dimensions -/

/-- **(9.3.59)**, exact: if (9.3.55)–(9.3.58) give `∂_w β(u(w)) = Ṁ(w)/(ε p(w) d(w))`, then
`ε⁻¹ ∫_a^{w₀} Ṁ/(p d) = β(w₀) - β(a)`. -/
theorem kramers_multi_integrated {β Mdot p d : ℝ → ℝ} {ε : ℝ} (hε : ε ≠ 0)
    (hβ : ∀ w, HasDerivAt β (Mdot w / (ε * (p w * d w))) w)
    (hc : Continuous fun w => Mdot w / (p w * d w)) (a w₀ : ℝ) :
    ε⁻¹ * ∫ w in a..w₀, Mdot w / (p w * d w) = β w₀ - β a := by
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hβ w)]
  · congr 1; ext w; field_simp
  · have e : (fun w => Mdot w / (ε * (p w * d w))) = fun w => ε⁻¹ * (Mdot w / (p w * d w)) := by
      ext w; field_simp
    rw [e]; exact (continuous_const.mul hc).intervalIntegrable _ _

/-- **(9.3.59) ⇒ (9.3.63)**: under the peak-evaluation hypotheses (`Ṁ ≈ Ṅ_a` and `d ≈ d(w₀)`
across `[a, w₀]`, i.e. `∫ Ṁ/(pd) = Ṅ_a κ(w₀)/d(w₀)`) and (9.3.52),
`κ(w₀) Ṅ_a = ε d(w₀)[N₀/n₀ - N_a/n_a]`. -/
theorem kramers_multi_relaxation {Iint κ NaDot d ε βw βa N₀ n₀ Na na : ℝ} (hd : d ≠ 0)
    (h59 : ε⁻¹ * Iint = βw - βa) (hpeak : Iint = NaDot * κ / d)
    (hw : βw = N₀ / n₀) (ha : βa = Na / na) (hε : ε ≠ 0) :
    κ * NaDot = ε * d * (N₀ / n₀ - Na / na) := by
  rw [← hw, ← ha, ← h59, hpeak]; field_simp

/-! ### A concrete instance -/

/-- **Instance**: the boundary layer with `v·ν = -1` tends to `g + C₁` (9.3.20); the interior
layer with `H = C₁ = 1` is unbounded (9.3.14); the separatrix layer with `κ = 2` tends to
`√(π/4)` (9.3.35); and for a single exit point with `|v·ν| = 2` and `∫_R e^{-φ/ε} = 3`
(`K = 0`, `ε = 1`) the corrected (9.3.41) gives `C₀ = 3/2`. -/
theorem exitPoints_instance :
    Tendsto (bdryLayer (-1) 0 1) atTop (𝓝 1) ∧
    (¬ ∃ M, ∀ ξ, 0 ≤ ξ → |innerSol 1 1 0 ξ| ≤ M) ∧
    Tendsto (sepLayer 2 0 1) atTop (𝓝 (√(π / 4))) ∧
    ∀ C₀ : ℝ, -(exp (-0 / 1) * 3) = ∫ _u, (1 : ℝ) * (-2) * C₀ ∂(Measure.dirac (0 : ℝ)) →
      C₀ = 3 / 2 := by
  refine ⟨?_, interior_layer_unbounded one_pos one_ne_zero 0, ?_, fun C₀ h => ?_⟩
  · simpa using boundary_layer_tendsto (c := -1) (by norm_num) 0 1
  · have := (separatrix_layer_tendsto (κ := 2) (by norm_num) 0 1).1
    simpa [show (2 : ℝ) * 2 = 4 by norm_num] using this
  · obtain ⟨h1, -, -⟩ := meanExit_C0 (μ := Measure.dirac (0 : ℝ)) (w := fun _ => 1)
      (vn := fun _ => -2) (fun _ => one_pos) (fun _ => by norm_num) (integrable_const _)
      (by norm_num : (0 : ℝ) < 3) h
    rw [h1]; simp

end Gardiner.Escape
