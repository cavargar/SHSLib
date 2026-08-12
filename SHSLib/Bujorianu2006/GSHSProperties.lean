/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Properties of GSHS: executions, sojourn times and the renewal kernel

Formalization of Definition 2 (Section 2.3) and of the verification steps of
Proposition 5 (Section 4) of

  M.L. Bujorianu and J. Lygeros, "Toward a General Theory of Stochastic Hybrid
  Systems", LNCIS 337, Springer, 2006.

Proposition 5 states that a GSHS is a strong Markov process; its proof consists
in checking that a GSHS is a Markov string, i.e. that it satisfies
Assumptions 4–6.  The only steps of that verification that carry mathematical
content are

  (b) the memoryless property of the sojourn times `S^i = min(t_*, S'^i)`, and
  (a) the memoryless property of the renewal kernel
      `Ψ(ω^i, ·) = R(x^i_{S^i(ω^i)}, ·)`, which the paper deduces from (b);

both are proved here (`sojournTime_isTerminalTime` and
`renewalKernel_shift_invariant`).
-/
import SHSLib.Bujorianu2006.MarkovString
import SHSLib.Bujorianu2006.Generator

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Bujorianu2006

/-! ## Proposition 5: the sojourn time of a GSHS is a terminal time -/

section Sojourn

variable {Ω X : Type*} (M : ShiftSystem Ω X)

/-- The sojourn time `S^i = min(t_*, S'^i)` of Section 2.2: the minimum of the
boundary hitting time `t_*` of `B = ∂X^i` and of the rate-driven time `S'`. -/
def sojournTime (B : Set X) (S' : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  min (hittingTime M B ω) (S' ω)

variable {M}

/-- **Proposition 5, step (b)**: the sojourn time `S^i = min(t_*, S'^i)` is a
terminal time, i.e. it has the memoryless property (5).  The boundary hitting
time is a terminal time, the rate-driven time is a terminal time by the
memoryless property of the exponential threshold, and the minimum of two
terminal times is a terminal time. -/
theorem sojournTime_isTerminalTime (B : Set X) {S' : Ω → ℝ≥0∞}
    (hS' : IsTerminalTime M S') : IsTerminalTime M (sojournTime M B S') :=
  (isTerminalTime_hittingTime B).min hS'

/-- **Proposition 5, step (a)**: the renewal kernel `Ψ(ω) = R(x_{S(ω)}(ω), ·)`
inherits the memoryless property from the sojourn time: if `t < S(ω)` then
`Ψ(θ_t ω) = Ψ(ω)`.  This is Assumption 5(ii)(b) for a GSHS. -/
theorem renewalKernel_shift_invariant {Y : Type*} (Psi : X → Y) {S : Ω → ℝ≥0∞}
    (hS : IsTerminalTime M S) (t : ℝ) (ω : Ω) (ht : 0 ≤ t)
    (hlt : ENNReal.ofReal t < S ω) (hfin : S ω ≠ ⊤) :
    Psi (M.x (S (M.θ t ω)).toReal (M.θ t ω)) = Psi (M.x (S ω).toReal ω) := by
  have hshift : S (M.θ t ω) = S ω - ENNReal.ofReal t := hS t ω ht hlt
  have hlt' : t < (S ω).toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal ht hfin).mp hlt
    exact this
  have htoReal : (S (M.θ t ω)).toReal = (S ω).toReal - t := by
    rw [hshift, ENNReal.toReal_sub_of_le hlt.le hfin, ENNReal.toReal_ofReal ht]
  rw [htoReal, M.x_shift ((S ω).toReal - t) t ω (by linarith) ht]
  congr 2
  ring

end Sojourn

/-! ## Definition 2: GSHS executions

A stochastic process `x_t = (q(t), x(t))` is a GSHS execution when it is
started from `Init`, evolves continuously in a fixed mode between the jump
times `T_k`, and jumps at `T_{k+1}` to a state distributed according to
`R(x_{T_{k+1}^-}, ·)`.

The clause "`x(t)` solves the SDE `dx = b dt + σ dW`" of Definition 2 is
represented here by continuity of the path between jumps; its full
probabilistic content is the martingale characterization through the
continuous part `L_cont` of the generator (Eq. (29)), which is the subject of
Theorem 2 in `SHSLib.Bujorianu2006.Generator`. -/

namespace GSHS

open HybridStateSpace

variable (H : GSHS)

/-- **Definition 2** (GSHS execution).  The data of a process on a probability
space `(Ω, P)` together with its jump times, the pre-jump states, and the
increasing family of pre-jump σ-algebras. -/
structure Execution (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The jump times `T_0 = 0 < T_1 < T_2 < …`. -/
  T : ℕ → Ω → ℝ
  /-- The hybrid state process `x_t = (q(t), x(t))`. -/
  x : ℝ → Ω → Hyb H.toHybridStateSpace
  /-- The pre-jump states `x_{T_k^-}`, which may lie on the boundary `∂X`. -/
  preJump : ℕ → Ω → Cl H.toHybridStateSpace
  /-- The information available just before the `k`-th jump. -/
  info : ℕ → MeasurableSpace Ω
  /-- The pre-jump σ-algebras are sub-σ-algebras of the ambient one. -/
  info_le : ∀ k, info k ≤ ‹MeasurableSpace Ω›
  /-- `T_0 = 0`. -/
  T_zero : ∀ ω, T 0 ω = 0
  /-- The jump times increase strictly. -/
  T_lt : ∀ k ω, T k ω < T (k + 1) ω
  /-- `x_0` is distributed according to `Init`. -/
  init_law : Measure.map (x 0) P = H.Init
  /-- The discrete component is constant between two jumps. -/
  mode_const : ∀ k ω, ∀ t ∈ Set.Ico (T k ω) (T (k + 1) ω), (x t ω).1 = (x (T k ω) ω).1
  /-- The continuous component evolves continuously between two jumps. -/
  cont_between : ∀ k ω, ContinuousOn (fun t => x t ω) (Set.Ico (T k ω) (T (k + 1) ω))
  /-- The post-jump state is distributed according to `R(x_{T_{k+1}^-}, ·)`:
  the conditional expectation of `g(x_{T_{k+1}})` given the pre-jump
  information is `∫ g dR(x_{T_{k+1}^-}, ·)`. -/
  jump_law : ∀ (k : ℕ) (g : Hyb H.toHybridStateSpace → ℝ), Measurable g →
    (∃ C, ∀ y, |g y| ≤ C) →
    P[fun ω => g (x (T (k + 1) ω) ω) | info (k + 1)]
      =ᵐ[P] fun ω => ∫ y, g y ∂(H.R (preJump (k + 1) ω))

variable {H} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The jump times of an execution are strictly increasing. -/
theorem Execution.T_strictMono (e : H.Execution Ω P) (ω : Ω) : StrictMono fun k => e.T k ω :=
  strictMono_nat_of_lt_succ fun k => e.T_lt k ω

/-- The jump times of an execution are nonnegative. -/
theorem Execution.T_nonneg (e : H.Execution Ω P) (k : ℕ) (ω : Ω) : 0 ≤ e.T k ω := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_of_eq (e.T_zero ω).symm
  · have h : e.T 0 ω < e.T k ω := e.T_strictMono ω hk
    rw [e.T_zero ω] at h
    exact h.le

/-- Between two jumps the mode is constant, so the hybrid state stays in the
same component of `X`. -/
theorem Execution.mode_eq (e : H.Execution Ω P) (k : ℕ) (ω : Ω) {s t : ℝ}
    (hs : s ∈ Set.Ico (e.T k ω) (e.T (k + 1) ω))
    (ht : t ∈ Set.Ico (e.T k ω) (e.T (k + 1) ω)) :
    (e.x s ω).1 = (e.x t ω).1 := by
  rw [e.mode_const k ω s hs, e.mode_const k ω t ht]

/-- **Proposition 3** for an execution: the path of an execution is right
continuous at every time strictly inside an inter-jump interval, because it is
continuous there. -/
theorem Execution.rightContinuousWithinAt (e : H.Execution Ω P) (k : ℕ) (ω : Ω) {t : ℝ}
    (ht : t ∈ Set.Ico (e.T k ω) (e.T (k + 1) ω)) :
    ContinuousWithinAt (fun s => e.x s ω) (Set.Ici t) t := by
  have hIco : Set.Ico (e.T k ω) (e.T (k + 1) ω) ∈ 𝓝[Set.Ici t] t := by
    refine mem_nhdsWithin.mpr ⟨Set.Iio (e.T (k + 1) ω), isOpen_Iio, ht.2, ?_⟩
    rintro y ⟨hyb, hyt⟩
    exact ⟨le_trans ht.1 hyt, hyb⟩
  have hwithin := (e.cont_between k ω t ht)
  exact hwithin.mono_of_mem_nhdsWithin hIco

end GSHS

end Bujorianu2006

end
