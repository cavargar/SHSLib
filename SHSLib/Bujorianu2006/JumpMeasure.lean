/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The jump counting measures `p`, `p*` of a Markov string

Formalization of the counting processes appearing in the proof of Theorem 2 of

  M.L. Bujorianu and J. Lygeros, "Toward a General Theory of Stochastic Hybrid
  Systems", LNCIS 337, Springer, 2006.

Section 4 introduces, for `A ∈ B(X̄)`,

  `p(t, A)  = Σ_{k ≥ 1} I_{t ≥ T_k} I_{x_{T_k} ∈ A}`,
  `p*(t)    = Σ_{k ≥ 1} I_{t ≥ T_k} I_{x_{T_k^-} ∈ ∂X}`,

the random measure of the jumps and the counting process of the jumps *from
the boundary*.  Both are instances of the same construction, counting the jumps
whose (pre- or post-jump) state lies in a prescribed set; this is what
`countJumps` below formalizes, with `jumpMeasure = p` and
`boundaryJumpCount = p*` as the two specializations used by the paper.

The basic structural facts used in the proof of Theorem 2 are proved here:
these are genuine counting measures (monotone in time and in the set,
countably additive over disjoint sets), they vanish before the first jump, and
under the non-Zeno Assumption 6 they are finite at every finite time.
-/
import SHSLib.Bujorianu2006.MarkovString

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Classical

noncomputable section

namespace Bujorianu2006

namespace PiecedProcess

variable {Ω X : Type*} (P : PiecedProcess Ω X)

/-- The state reached at the `k`-th jump, `x_{T_k}`. -/
def jumpState (k : ℕ) (ω : Ω) : X := P.x (P.jumpTime k ω).toReal ω

/-- The counting process of the jumps in `[0, t]` whose state (recorded by the
family `xm`, which is `x_{T_k}` for `p` and `x_{T_k^-}` for `p*`) lies in `A`:
`Σ_{k ≥ 1} I_{t ≥ T_k} I_{xm_k ∈ A}`. -/
def countJumps (xm : ℕ → Ω → X) (A : Set X) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' k : ℕ, if P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t ∧ xm (k + 1) ω ∈ A then (1 : ℝ≥0∞) else 0

/-- The jump measure `p(t, A) = Σ_{k ≥ 1} I_{t ≥ T_k} I_{x_{T_k} ∈ A}`. -/
def jumpMeasure (A : Set X) (t : ℝ) (ω : Ω) : ℝ≥0∞ := P.countJumps P.jumpState A t ω

/-- The counting process of the jumps from a set `B` (in the paper, `B = ∂X`),
`p*(t) = Σ_{k ≥ 1} I_{t ≥ T_k} I_{x_{T_k^-} ∈ B}`, where the family `xleft`
records the pre-jump states `x_{T_k^-}`. -/
def boundaryJumpCount (xleft : ℕ → Ω → X) (B : Set X) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  P.countJumps xleft B t ω

variable {P}

variable {xm : ℕ → Ω → X}

/-- `p(t, ∅) = 0`. -/
@[simp] theorem countJumps_empty (t : ℝ) (ω : Ω) : P.countJumps xm ∅ t ω = 0 := by
  simp [countJumps]

/-- The jump counting process is nondecreasing in time. -/
theorem countJumps_mono_time (A : Set X) (ω : Ω) :
    Monotone fun t : ℝ => P.countJumps xm A t ω := by
  intro s t hst
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases h : P.jumpTime (k + 1) ω ≤ ENNReal.ofReal s ∧ xm (k + 1) ω ∈ A
  · have h' : P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t ∧ xm (k + 1) ω ∈ A :=
      ⟨h.1.trans (ENNReal.ofReal_le_ofReal hst), h.2⟩
    simp [h, h']
  · simp [h]

/-- The jump counting process is monotone in the set. -/
theorem countJumps_mono_set {A B : Set X} (hAB : A ⊆ B) (t : ℝ) (ω : Ω) :
    P.countJumps xm A t ω ≤ P.countJumps xm B t ω := by
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases h : P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t ∧ xm (k + 1) ω ∈ A
  · have h' : P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t ∧ xm (k + 1) ω ∈ B :=
      ⟨h.1, hAB h.2⟩
    simp [h, h']
  · simp [h]

/-- Every jump counting process is dominated by the total number of jumps. -/
theorem countJumps_le_univ (A : Set X) (t : ℝ) (ω : Ω) :
    P.countJumps xm A t ω ≤ P.countJumps xm univ t ω :=
  countJumps_mono_set (subset_univ A) t ω

/-- Additivity of `p(t, ·)` over disjoint sets. -/
theorem countJumps_union {A B : Set X} (hAB : Disjoint A B) (t : ℝ) (ω : Ω) :
    P.countJumps xm (A ∪ B) t ω = P.countJumps xm A t ω + P.countJumps xm B t ω := by
  rw [countJumps, countJumps, countJumps, ← ENNReal.tsum_add]
  refine tsum_congr fun k => ?_
  by_cases hT : P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t
  · by_cases hA : xm (k + 1) ω ∈ A
    · have hB : xm (k + 1) ω ∉ B := fun hB => (hAB.le_bot ⟨hA, hB⟩).elim
      simp [hT, hA, hB]
    · by_cases hB : xm (k + 1) ω ∈ B <;> simp [hT, hA, hB]
  · simp [hT]

/-- No jump has occurred before the first sojourn time: `p(t, A) = 0` for
`t < S(ω) = T_1(ω)`. -/
theorem countJumps_eq_zero_of_lt_S {t : ℝ} {ω : Ω} (A : Set X)
    (ht : ENNReal.ofReal t < P.S ω) : P.countJumps xm A t ω = 0 := by
  have hzero : ∀ k : ℕ,
      (if P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t ∧ xm (k + 1) ω ∈ A then (1 : ℝ≥0∞) else 0)
        = 0 := by
    intro k
    have hnot : ¬ (P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t) := fun hle =>
      absurd (le_trans (P.S_le_jumpTime_succ k ω) hle) (not_le.mpr ht)
    simp [hnot]
  simp [countJumps, hzero]

/-- Under the non-Zeno Assumption 6 only finitely many jumps occur up to a
finite time, so `p(t, A)` is finite. -/
theorem countJumps_ne_top (h : P.NonZeno) (A : Set X) (t : ℝ) (ω : Ω) :
    P.countJumps xm A t ω ≠ ⊤ := by
  obtain ⟨K, hK⟩ := (explosionTime_eq_top_iff ω).mp (h ω) t
  have hzero : ∀ k ∉ Finset.range K,
      (if P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t ∧ xm (k + 1) ω ∈ A then (1 : ℝ≥0∞) else 0)
        = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have hKk : P.jumpTime K ω ≤ P.jumpTime (k + 1) ω :=
      P.jumpTime_mono ω (by omega)
    have : ¬ (P.jumpTime (k + 1) ω ≤ ENNReal.ofReal t) := fun hle =>
      absurd (hKk.trans hle) (not_le.mpr hK)
    simp [this]
  rw [countJumps, tsum_eq_sum hzero]
  refine (ENNReal.sum_lt_top.mpr fun i _ => ?_).ne
  split <;> simp

end PiecedProcess

end Bujorianu2006

end
