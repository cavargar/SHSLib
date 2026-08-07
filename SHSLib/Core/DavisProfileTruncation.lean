import SHSLib.Core.DavisProfileLinearGrowth
import SHSLib.Core.DavisProfileTruncationCore

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Truncating a profile at an age horizon

The conditional laws of a segment bound the hazard average of a profile by a
constant that bounds the profile *everywhere*.  Only ages inside the age window
ever enter such an average, so a bound below an age horizon should suffice.

This module makes that precise by truncating the age: `Φ̃(z, r) = Φ(z, r ⊓ T)`
agrees with `Φ` below the horizon `T`, inherits its continuity, joint
measurability and Lipschitz constant, and is bounded everywhere as soon as `Φ`
is bounded below the horizon.  Because a hazard window integral over a window
lying below the horizon is the same for `Φ` and for `Φ̃`, every bound proved for
globally bounded profiles transfers to profiles bounded only below the horizon.

Combined with the linear growth of the centered reset profile, this gives
quantitative bounds on the conditional completed mean of a bounded test
function under a bounded intensity — with no hypothesis on the accumulated
hazard, which the vacuity module showed to be unavailable.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The quantitative bound for the centered reset profile -/

/-- **The conditional completed mean of a bounded test function is bounded
below an age horizon**, by `2·Cg·(1 + Λ·T)`, under a bounded intensity alone.
This is the non-vacuous replacement for the bound obtained from a uniformly
bounded accumulated hazard. -/
theorem abs_davisSegmentConditionalCompletedMean_le_of_age_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hEcont : ∀ z : DavisState Q n,
      Continuous fun s : ℝ => davisExpectedResetIncrement S g
        (davisFlow S hflow s.toNNReal z))
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (Tmax : ℝ) (hTmax0 : 0 ≤ Tmax) (z : DavisState Q n) (u T : ℝ≥0)
    (hTmax : ((u + T : ℝ≥0) : ℝ) ≤ Tmax) :
    |davisSegmentConditionalCompletedMean S hflow g z u (u + T)| ≤
      2 * Cg * (1 + Lam * Tmax) := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC (davisFlow S hflow 0 z))
  have hLam0 : 0 ≤ Lam := le_trans (totalIntensity_nonneg S z) (hLam z)
  set K : ℝ := 2 * Cg * (1 + Lam * Tmax) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : ∀ w r, r ≤ Tmax →
      |davisSegmentCenteredResetProfile S hflow g w r| ≤ K := fun w r hr =>
    abs_davisSegmentCenteredResetProfile_le_of_age_le S hflow hcont hgcont Cg
      hgC Lam hLam Tmax hTmax0 w r hr
  have hPhicont := continuous_davisSegmentCenteredResetProfile S hflow hgcont
    hEcont
  have hwin := abs_davisHazardWindowIntegral_le_mul_survivor_sub_of_age_le S
    hflow hcont (davisSegmentCenteredResetProfile S hflow g) hPhicont hK z u T
    hTmax
  have hpos : 0 < davisSegmentSurvivor S hflow z u :=
    davisSegmentSurvivor_pos S hflow z u
  have hposv : 0 < davisSegmentSurvivor S hflow z (u + T) :=
    davisSegmentSurvivor_pos S hflow z (u + T)
  rw [davisSegmentConditionalCompletedMean_eq_windowIntegral, abs_mul,
    abs_of_pos (inv_pos.2 hpos)]
  have hK1 : |davisHazardWindowIntegral S hflow
      (davisSegmentCenteredResetProfile S hflow g) z u T| ≤
      K * davisSegmentSurvivor S hflow z u := by
    refine le_trans hwin ?_
    have hle : davisSegmentSurvivor S hflow z u -
        davisSegmentSurvivor S hflow z (u + T) ≤
        davisSegmentSurvivor S hflow z u := by linarith
    exact mul_le_mul_of_nonneg_left hle hK0
  calc (davisSegmentSurvivor S hflow z u)⁻¹ *
        |davisHazardWindowIntegral S hflow
          (davisSegmentCenteredResetProfile S hflow g) z u T|
      ≤ (davisSegmentSurvivor S hflow z u)⁻¹ *
          (K * davisSegmentSurvivor S hflow z u) :=
        mul_le_mul_of_nonneg_left hK1 (le_of_lt (inv_pos.2 hpos))
    _ = K := by field_simp

end SHS
