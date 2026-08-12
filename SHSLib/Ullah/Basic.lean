/-
Formalization of §8.2, "Derivation of the dCKE", of
M. Ullah and O. Wolkenhauer, *Stochastic Approaches for Systems Biology*, Chapter 8.

This file sets up the objects of the derivation: the time difference quotient (8.4),
the gain–loss integrand of (8.5), the region-restricted quantity `I_R` of (8.5), and
the splitting (8.6) of the state space into the near region `‖y - y'‖ < ε` and the
far region `‖y - y'‖ ≥ ε`.  It also contains the two changes of variables used in the
text: `y' = y - q`, and the reflection `q ↦ -q` responsible for the cancellation of
the first two terms of the Taylor expansion.

The state space, partial derivatives and Taylor remainder are those of
`SHSLib.Gardiner.Basic`.
-/
import SHSLib.Gardiner.Basic

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Ullah

open Gardiner

variable {n : ℕ}

/-! ### Changes of variables on a ball -/

/-- Translation invariance of Lebesgue measure: the substitution `y' = y + q`. -/
lemma setIntegral_ball_shift (y : Sp n) (ε : ℝ) (g : Sp n → ℝ) :
    ∫ x in ball y ε, g x = ∫ q in ball (0 : Sp n) ε, g (y + q) := by
  have h := (measurePreserving_add_left (volume : Measure (Sp n)) y).setIntegral_preimage_emb
    (measurableEmbedding_addLeft y) g (ball y ε)
  rw [← h]
  have hpre : (fun x => y + x) ⁻¹' ball y ε = ball (0 : Sp n) ε := by
    ext q; simp [dist_eq_norm]
  rw [hpre]

/-- Reflection invariance of Lebesgue measure on a ball centred at the origin: the
symmetry `∫ f(y; q) dq = ∫ f(y; -q) dq` used in the text. -/
lemma setIntegral_ball_neg (ε : ℝ) (g : Sp n → ℝ) :
    ∫ q in ball (0 : Sp n) ε, g (-q) = ∫ q in ball (0 : Sp n) ε, g q := by
  have h := (Measure.measurePreserving_neg (volume : Measure (Sp n))).setIntegral_preimage_emb
    measurableEmbedding_neg g (ball 0 ε)
  rw [← h]
  have hpre : (fun x : Sp n => -x) ⁻¹' ball 0 ε = ball (0 : Sp n) ε := by ext q; simp
  rw [hpre]

/-- The reflected function is again integrable on a ball centred at the origin. -/
lemma integrableOn_ball_neg {ε : ℝ} {g : Sp n → ℝ}
    (hg : IntegrableOn g (ball (0 : Sp n) ε)) :
    IntegrableOn (fun q => g (-q)) (ball (0 : Sp n) ε) := by
  have h := ((Measure.measurePreserving_neg (volume : Measure (Sp n))).integrableOn_comp_preimage
    measurableEmbedding_neg (f := g) (s := ball (0 : Sp n) ε)).2 hg
  have hpre : (fun x : Sp n => -x) ⁻¹' ball 0 ε = ball (0 : Sp n) ε := by ext q; simp
  rwa [hpre] at h

/-! ### The quantities of the derivation

Throughout, `p t y` is the state probability density `p(y, t)` and
`k dt y' y` is the transition density `p(y, t + Δt | y', t)`.
-/

/-- (8.4): the difference quotient whose limit as `Δt → 0` is `∂p(y, t)/∂t`. -/
def timeQuot (p : ℝ → Sp n → ℝ) (t dt : ℝ) (y : Sp n) : ℝ := (p (t + dt) y - p t y) / dt

/-- The gain-minus-loss integrand of (8.5),
`p(y, t + Δt | y', t) p(y', t) - p(y', t + Δt | y, t) p(y, t)`. -/
def flux (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (t dt : ℝ) (y y' : Sp n) : ℝ :=
  k dt y' y * p t y' - k dt y y' * p t y

/-- The quantity of (8.5) before the limit `Δt → 0` is taken:
`(1/Δt) ∫_R dy' {p(y, t+Δt|y',t) p(y',t) - p(y', t+Δt|y,t) p(y,t)}`. -/
def IQuot (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (t dt : ℝ) (y : Sp n)
    (R : Set (Sp n)) : ℝ :=
  (1 / dt) * ∫ y' in R, flux p k t dt y y'

variable {p : ℝ → Sp n → ℝ} {k : ℝ → Sp n → Sp n → ℝ} {t dt ε : ℝ} {y : Sp n}

/-- The passage from (8.4) to the integral form below (8.4): the Chapman–Kolmogorov
equation (8.3) together with the normalization `∫ dy' p(y', t+Δt|y,t) = 1` turns the
time difference quotient into `I_R` over the whole state space. -/
theorem timeQuot_eq_IQuot_univ
    (hCK : p (t + dt) y = ∫ y', k dt y' y * p t y')
    (hnorm : ∫ y', k dt y y' = 1)
    (hgain : Integrable fun y' => k dt y' y * p t y')
    (hloss : Integrable fun y' => k dt y y') :
    timeQuot p t dt y = IQuot p k t dt y univ := by
  have hloss' : Integrable fun y' => k dt y y' * p t y := hloss.mul_const _
  simp only [timeQuot, IQuot, flux, Measure.restrict_univ]
  rw [integral_sub hgain hloss', integral_mul_const, hnorm, ← hCK]
  ring

/-- (8.6): the splitting of the state space at `‖y - y'‖ = ε`.  The first region
contributes the continuous part of the process, the second the jump part. -/
theorem IQuot_split (hint : Integrable (flux p k t dt y)) :
    IQuot p k t dt y univ =
      IQuot p k t dt y (ball y ε) + IQuot p k t dt y (ball y ε)ᶜ := by
  simp only [IQuot, ← mul_add]
  congr 1
  rw [Measure.restrict_univ,
    ← integral_add_compl (measurableSet_ball (x := y) (ε := ε)) hint]

end Ullah
