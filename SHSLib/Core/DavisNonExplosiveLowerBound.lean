import SHSLib.Core.DavisConstruction

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Non-explosion from a deterministic dead time

The model-level martingale and Dynkin statements are proved in the regime where
the holding times are bounded below by a deterministic dead time `d > 0`.  Such
a bound already excludes explosion: the `k`-th jump time is at least `k · d`,
which tends to infinity.  This module records that implication, so that a
concrete instance with a refractory window does not have to assume
non-explosion separately.
-/

namespace SHS

variable {m : ℕ} {Ω : Type*}

/-- The `k`-th cumulative jump time is at least `k` dead times. -/
theorem DavisJumpNoise.nsmul_le_jumpTime (ξ : DavisJumpNoise m Ω) (d : ℝ≥0)
    (hd : ∀ i ω, d ≤ ξ.holdingTime i ω) (k : ℕ) (ω : Ω) :
    (k : ℝ≥0) * d ≤ ξ.jumpTime k ω := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [DavisJumpNoise.jumpTime_succ]
      have hstep : ((k : ℝ≥0) + 1) * d = (k : ℝ≥0) * d + d := by ring
      calc ((k + 1 : ℕ) : ℝ≥0) * d = (k : ℝ≥0) * d + d := by push_cast; rw [hstep]
        _ ≤ ξ.jumpTime k ω + ξ.holdingTime k ω := add_le_add ih (hd k ω)

/-- **A strictly positive deterministic lower bound on the holding times
excludes explosion.** -/
theorem DavisJumpNoise.nonExplosive_of_holdingTime_ge (ξ : DavisJumpNoise m Ω)
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω) :
    ξ.NonExplosive := by
  intro ω
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge (b / d)
  filter_upwards [Filter.eventually_ge_atTop N] with k hk
  refine le_trans ?_ (ξ.nsmul_le_jumpTime d hd k ω)
  have hb : b = (b / d) * d := by
    rw [div_mul_cancel₀ _ (ne_of_gt hdpos)]
  calc b = (b / d) * d := hb
    _ ≤ (N : ℝ≥0) * d := by gcongr
    _ ≤ (k : ℝ≥0) * d := by
        have : (N : ℝ≥0) ≤ (k : ℝ≥0) := by exact_mod_cast hk
        gcongr

end SHS
