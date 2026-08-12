/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Additive and multiplicative functionals, terminal times

Formalization of the analytic core of Sections 2.2, 3.2 and 4 of

  M.L. Bujorianu and J. Lygeros, "Toward a General Theory of Stochastic Hybrid
  Systems", LNCIS 337, Springer, 2006.

The jump mechanism of a GSHS is described by

* the additive functional `Λ_t(ω) = ∫₀ᵗ λ(x_s(ω)) ds`,
* the continuous multiplicative functional `M(t, ω) = exp(-Λ_t(ω))`,
* the boundary hitting time `t_*`,
* the survivor function `F(t, ω) = I_{t < t_*(ω)} exp(-Λ_t(ω))`  (Eq. (2)),

and the sojourn time `S^i = min(t_*, S'^i)` where `S'^i` is driven by an
exponentially distributed random variable `m` through `Λ` (Eq. (3)).

This file proves, in the abstract setting of a *shift system* (a family of
translation operators `θ_t` acting on a path space, together with the
coordinate process `x_t`, as in Lemma 1 of the paper):

* `Λ` is an additive functional: `Λ_{t+u}(ω) = Λ_t(ω) + Λ_u(θ_t ω)`;
* `M` is a multiplicative functional: `M(t+u, ω) = M(t, ω) · M(u, θ_t ω)`;
* the boundary hitting time is a *terminal time* (Eq. (5));
* the minimum of two terminal times is a terminal time (used in the proof of
  Proposition 5);
* the survivor function `F` of Eq. (2) is a right-continuous multiplicative
  functional;
* the memoryless identity `P(S' > t + u | S' > t) = P_{x_t}(S' > u)` of Eq. (26)
  and the exponential computation `P[m > Λ_t] = exp(-Λ_t)` of Eq. (3).
-/
import Mathlib

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace Bujorianu2006

/-! ## Shift systems -/

/-- A *shift system*: a path space `Ω` carrying a family of translation
operators `(θ_t)` and a process `(x_t)` with values in `X`, subject to the two
identities of Lemma 1 of the paper,
`θ_s ∘ θ_t = θ_{s+t}` and `x_s ∘ θ_t = x_{s+t}`. -/
structure ShiftSystem (Ω : Type*) (X : Type*) where
  /-- The translation operators `θ_t`. -/
  θ : ℝ → Ω → Ω
  /-- The coordinate process `x_t`. -/
  x : ℝ → Ω → X
  /-- `θ_0 = id`. -/
  θ_zero : ∀ ω, θ 0 ω = ω
  /-- `θ_s ∘ θ_t = θ_{s+t}` (Lemma 1). -/
  θ_add : ∀ s t ω, 0 ≤ s → 0 ≤ t → θ s (θ t ω) = θ (s + t) ω
  /-- `x_s ∘ θ_t = x_{s+t}` (Lemma 1). -/
  x_shift : ∀ s t ω, 0 ≤ s → 0 ≤ t → x s (θ t ω) = x (s + t) ω

namespace ShiftSystem

variable {Ω X : Type*} (M : ShiftSystem Ω X)

/-- Iterating the shift: `θ_r ∘ θ_s ∘ θ_t = θ_{r+s+t}`. -/
theorem θ_add_add (r s t : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (ω : Ω) :
    M.θ r (M.θ s (M.θ t ω)) = M.θ (r + s + t) ω := by
  rw [M.θ_add s t ω hs ht, M.θ_add r (s + t) ω hr (by linarith), add_assoc]

/-! ## The additive functional `Λ` -/

/-- The additive functional `Λ_t(ω) = ∫₀ᵗ λ(x_s(ω)) ds` of Section 2.2. -/
def addFunctional (lam : X → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, lam (M.x s ω)

variable {M}

@[simp] theorem addFunctional_zero (lam : X → ℝ) (ω : Ω) :
    M.addFunctional lam 0 ω = 0 := by
  simp [addFunctional]

/-- **`Λ` is an additive functional**: `Λ_{t+u}(ω) = Λ_t(ω) + Λ_u(θ_t ω)`.

This is the additivity used in the proof of Proposition 5 (Eq. (26)). -/
theorem addFunctional_add (lam : X → ℝ) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (ω : Ω)
    (hint : ∀ a b : ℝ, IntervalIntegrable (fun s => lam (M.x s ω)) volume a b) :
    M.addFunctional lam (t + u) ω
      = M.addFunctional lam t ω + M.addFunctional lam u (M.θ t ω) := by
  have hshift : ∀ s : ℝ, 0 ≤ s → lam (M.x s (M.θ t ω)) = lam (M.x (s + t) ω) := by
    intro s hs; rw [M.x_shift s t ω hs ht]
  have h2 : (∫ s in (0 : ℝ)..u, lam (M.x s (M.θ t ω)))
      = ∫ s in (0 : ℝ)..u, lam (M.x (s + t) ω) := by
    refine intervalIntegral.integral_congr ?_
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact hshift s hs.1
  rw [addFunctional, addFunctional, addFunctional, h2,
    intervalIntegral.integral_comp_add_right (fun s => lam (M.x s ω)) t, zero_add,
    intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (u + t)),
    add_comm t u]

/-- For a nonnegative rate, `Λ_t ≥ 0` for `t ≥ 0`. -/
theorem addFunctional_nonneg {lam : X → ℝ} (hlam : ∀ y, 0 ≤ lam y) {t : ℝ} (ht : 0 ≤ t)
    (ω : Ω) : 0 ≤ M.addFunctional lam t ω :=
  intervalIntegral.integral_nonneg ht fun _ _ => hlam _

/-! ## The multiplicative functional `M(t, ω) = exp(-Λ_t(ω))` -/

/-- The continuous multiplicative functional `M(t, ω) = exp(-∫₀ᵗ λ(x_s(ω)) ds)`
of Section 2.2, i.e. the survivor function of the rate-driven sojourn time. -/
def _root_.Bujorianu2006.ShiftSystem.multFunctional (M : ShiftSystem Ω X) (lam : X → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(M.addFunctional lam t ω))

@[simp] theorem multFunctional_zero (lam : X → ℝ) (ω : Ω) :
    M.multFunctional lam 0 ω = 1 := by
  simp [ShiftSystem.multFunctional]

theorem multFunctional_pos (lam : X → ℝ) (t : ℝ) (ω : Ω) :
    0 < M.multFunctional lam t ω := Real.exp_pos _

/-- **`M` is a multiplicative functional**:
`M(t + u, ω) = M(t, ω) · M(u, θ_t ω)`. -/
theorem multFunctional_mul (lam : X → ℝ) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (ω : Ω)
    (hint : ∀ a b : ℝ, IntervalIntegrable (fun s => lam (M.x s ω)) volume a b) :
    M.multFunctional lam (t + u) ω
      = M.multFunctional lam t ω * M.multFunctional lam u (M.θ t ω) := by
  rw [ShiftSystem.multFunctional, ShiftSystem.multFunctional, ShiftSystem.multFunctional,
    addFunctional_add lam t u ht hu ω hint, ← Real.exp_add]
  ring_nf

/-- For a nonnegative rate, `M(t, ω) ≤ 1` for `t ≥ 0`. -/
theorem multFunctional_le_one {lam : X → ℝ} (hlam : ∀ y, 0 ≤ lam y) {t : ℝ} (ht : 0 ≤ t)
    (ω : Ω) : M.multFunctional lam t ω ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (addFunctional_nonneg hlam ht ω))

/-- **Memoryless property of the rate-driven sojourn time** (Eq. (26)):
`P(S' > t + u ∣ S' > t) = P_{x_t}(S' > u)`, written in terms of the survivor
function `M(·, ·)` of `S'`. -/
theorem multFunctional_memoryless (lam : X → ℝ) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (ω : Ω)
    (hint : ∀ a b : ℝ, IntervalIntegrable (fun s => lam (M.x s ω)) volume a b) :
    M.multFunctional lam (t + u) ω / M.multFunctional lam t ω
      = M.multFunctional lam u (M.θ t ω) := by
  rw [multFunctional_mul lam t u ht hu ω hint, mul_comm, mul_div_assoc,
    div_self (ne_of_gt (M.multFunctional_pos lam t ω)), mul_one]

end ShiftSystem

/-! ## Terminal times -/

section TerminalTime

variable {Ω X : Type*} (M : ShiftSystem Ω X)

/-- **Equation (5)**: a `[0, ∞]`-valued random time `S` is a *terminal time*
(a stopping time with the memoryless property) if
`S(θ_t ω) = S(ω) - t` for every `t < S(ω)`. -/
def IsTerminalTime (S : Ω → ℝ≥0∞) : Prop :=
  ∀ (t : ℝ) (ω : Ω), 0 ≤ t → ENNReal.ofReal t < S ω →
    S (M.θ t ω) = S ω - ENNReal.ofReal t

variable {M}

/-- **The minimum of two terminal times is a terminal time.**  This is the
final step in the proof of Proposition 5: `S^i = min(t_*, S'^i)`. -/
theorem IsTerminalTime.min {S₁ S₂ : Ω → ℝ≥0∞} (h₁ : IsTerminalTime M S₁)
    (h₂ : IsTerminalTime M S₂) : IsTerminalTime M (fun ω => min (S₁ ω) (S₂ ω)) := by
  intro t ω ht hlt
  have hlt₁ : ENNReal.ofReal t < S₁ ω := lt_of_lt_of_le hlt (min_le_left _ _)
  have hlt₂ : ENNReal.ofReal t < S₂ ω := lt_of_lt_of_le hlt (min_le_right _ _)
  show Min.min (S₁ (M.θ t ω)) (S₂ (M.θ t ω)) = Min.min (S₁ ω) (S₂ ω) - ENNReal.ofReal t
  rw [h₁ t ω ht hlt₁, h₂ t ω ht hlt₂]
  rcases le_total (S₁ ω) (S₂ ω) with h | h
  · rw [min_eq_left h, min_eq_left (tsub_le_tsub_right h (ENNReal.ofReal t))]
  · rw [min_eq_right h, min_eq_right (tsub_le_tsub_right h (ENNReal.ofReal t))]

/-- A constant infinite time is a terminal time (the case of a mode that is
never left). -/
theorem isTerminalTime_top : IsTerminalTime M (fun _ => (⊤ : ℝ≥0∞)) := by
  intro t ω _ _
  simp

/-! ### The boundary hitting time -/

/-- The first hitting time `t_*(ω) = inf{t > 0 : x_t(ω) ∈ B}` of a set `B`
(for `B = ∂X^i` this is the boundary hitting time of Section 2.2), with the
convention `t_* = ∞` if `B` is never hit. -/
def hittingTime (M : ShiftSystem Ω X) (B : Set X) (ω : Ω) : ℝ≥0∞ :=
  sInf ((fun t : ℝ => ENNReal.ofReal t) '' {t : ℝ | 0 < t ∧ M.x t ω ∈ B})

/-- Auxiliary lemma: subtracting a constant commutes with `sInf` in `ℝ≥0∞`
below the infimum. -/
theorem sInf_image_sub_const (T : Set ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hle : ∀ a ∈ T, c ≤ a) :
    sInf ((fun a => a - c) '' T) = sInf T - c := by
  refine le_antisymm ?_ ?_
  · refine ENNReal.le_sub_of_add_le_right hc (le_sInf ?_)
    intro a ha
    calc sInf ((fun a => a - c) '' T) + c ≤ (a - c) + c :=
          add_le_add (sInf_le (Set.mem_image_of_mem (fun a => a - c) ha)) le_rfl
      _ = a := tsub_add_cancel_of_le (hle a ha)
  · refine le_sInf ?_
    rintro y ⟨a, ha, rfl⟩
    exact tsub_le_tsub_right (sInf_le ha) c

/-- **The boundary hitting time is a terminal time** (Section 4, step 1 of the
proof of Proposition 5): `t_*(θ_t ω) = t_*(ω) - t` for `t < t_*(ω)`. -/
theorem isTerminalTime_hittingTime (B : Set X) : IsTerminalTime M (hittingTime M B) := by
  intro t ω ht hlt
  set A : Ω → Set ℝ := fun ν => {u : ℝ | 0 < u ∧ M.x u ν ∈ B} with hA
  have hgt : ∀ v ∈ A ω, t < v := by
    intro v hv
    have hle : hittingTime M B ω ≤ ENNReal.ofReal v := sInf_le ⟨v, hv, rfl⟩
    have : ENNReal.ofReal t < ENNReal.ofReal v := lt_of_lt_of_le hlt hle
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mp this
  have himg : (fun u : ℝ => ENNReal.ofReal u) '' A (M.θ t ω)
      = (fun a => a - ENNReal.ofReal t) ''
          ((fun u : ℝ => ENNReal.ofReal u) '' A ω) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu0 : 0 < u := hu.1
      have hmem : u + t ∈ A ω := by
        refine ⟨by linarith, ?_⟩
        have := M.x_shift u t ω hu0.le ht
        rw [← this]; exact hu.2
      refine ⟨ENNReal.ofReal (u + t), ⟨u + t, hmem, rfl⟩, ?_⟩
      show ENNReal.ofReal (u + t) - ENNReal.ofReal t = ENNReal.ofReal u
      rw [← ENNReal.ofReal_sub _ ht]
      congr 1
      ring
    · rintro ⟨a, ⟨v, hv, rfl⟩, rfl⟩
      have hvt : t < v := hgt v hv
      refine ⟨v - t, ⟨by linarith, ?_⟩, ?_⟩
      · have := M.x_shift (v - t) t ω (by linarith) ht
        rw [this]
        have : v - t + t = v := by ring
        rw [this]; exact hv.2
      · show ENNReal.ofReal (v - t) = ENNReal.ofReal v - ENNReal.ofReal t
        rw [ENNReal.ofReal_sub _ ht]
  rw [hittingTime, hittingTime, himg]
  refine sInf_image_sub_const _ _ ENNReal.ofReal_ne_top ?_
  rintro a ⟨v, hv, rfl⟩
  exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr (hgt v hv))

/-! ### The survivor function of Eq. (2) -/

/-- **Equation (2)**: the right-continuous multiplicative functional
`F(t, ω) = I_{t < t_*(ω)} · exp(-∫₀ᵗ λ(x_s(ω)) ds)`, the survivor function of
the sojourn time `S^i`. -/
def survivorFunctional (M : ShiftSystem Ω X) (lam : X → ℝ) (B : Set X) (t : ℝ) (ω : Ω) : ℝ :=
  if ENNReal.ofReal t < hittingTime M B ω then M.multFunctional lam t ω else 0


@[simp] theorem survivorFunctional_zero_time (lam : X → ℝ) (B : Set X) (ω : Ω)
    (h : 0 < hittingTime M B ω) : survivorFunctional M lam B 0 ω = 1 := by
  simp [survivorFunctional, h]

theorem survivorFunctional_nonneg (lam : X → ℝ) (B : Set X) (t : ℝ) (ω : Ω) :
    0 ≤ survivorFunctional M lam B t ω := by
  unfold survivorFunctional
  split_ifs with h
  · exact (M.multFunctional_pos lam t ω).le
  · exact le_refl 0

theorem survivorFunctional_le_one {lam : X → ℝ} (hlam : ∀ y, 0 ≤ lam y) (B : Set X)
    {t : ℝ} (ht : 0 ≤ t) (ω : Ω) : survivorFunctional M lam B t ω ≤ 1 := by
  unfold survivorFunctional
  split_ifs with h
  · exact M.multFunctional_le_one hlam ht ω
  · exact zero_le_one

/-- **The survivor function (2) is a multiplicative functional**:
`F(t + u, ω) = F(t, ω) · F(u, θ_t ω)`.

This is the property that makes `F` the survivor function of a terminal
time. -/
theorem survivorFunctional_mul (lam : X → ℝ) (B : Set X) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (ω : Ω) (hint : ∀ a b : ℝ, IntervalIntegrable (fun s => lam (M.x s ω)) volume a b) :
    survivorFunctional M lam B (t + u) ω
      = survivorFunctional M lam B t ω * survivorFunctional M lam B u (M.θ t ω) := by
  have hofReal : ENNReal.ofReal (t + u) = ENNReal.ofReal t + ENNReal.ofReal u :=
    ENNReal.ofReal_add ht hu
  by_cases hmain : ENNReal.ofReal (t + u) < hittingTime M B ω
  · have hT : ENNReal.ofReal t < hittingTime M B ω := by
      refine lt_of_le_of_lt ?_ hmain
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hshift : hittingTime M B (M.θ t ω) = hittingTime M B ω - ENNReal.ofReal t :=
      isTerminalTime_hittingTime B t ω ht hT
    have hU : ENNReal.ofReal u < hittingTime M B (M.θ t ω) := by
      rw [hshift, lt_tsub_iff_right, add_comm, ← hofReal]
      exact hmain
    rw [survivorFunctional, survivorFunctional, survivorFunctional, if_pos hmain, if_pos hT,
      if_pos hU, M.multFunctional_mul lam t u ht hu ω hint]
  · rw [survivorFunctional, if_neg hmain]
    by_cases hT : ENNReal.ofReal t < hittingTime M B ω
    · have hshift : hittingTime M B (M.θ t ω) = hittingTime M B ω - ENNReal.ofReal t :=
        isTerminalTime_hittingTime B t ω ht hT
      have hU : ¬ ENNReal.ofReal u < hittingTime M B (M.θ t ω) := by
        rw [hshift, lt_tsub_iff_right, add_comm, ← hofReal]
        exact hmain
      rw [survivorFunctional, survivorFunctional, if_neg hU, mul_zero]
    · rw [survivorFunctional, if_neg hT, zero_mul]

end TerminalTime

/-! ## The exponentially distributed threshold (Eq. (3)) -/

section Exponential

open ProbabilityTheory Real

/-- The survivor function of the standard exponential law:
`P[m > c] = exp(-c)` for `c ≥ 0`.  This is the law of the random variable `m`
of Section 2.2 with `P_{x^i}[m^i > t] = e^{-t}`. -/
theorem expMeasure_Ioi (c : ℝ) (hc : 0 ≤ c) :
    (expMeasure 1) (Set.Ioi c) = ENNReal.ofReal (Real.exp (-c)) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hIic : (expMeasure 1) (Set.Iic c) = ENNReal.ofReal (1 - Real.exp (-c)) := by
    have hcdf : cdf (expMeasure 1) c = 1 - Real.exp (-(1 * c)) := by
      rw [cdf_expMeasure_eq one_pos c, if_pos hc]
    have hreal : (expMeasure 1).real (Set.Iic c) = 1 - Real.exp (-c) := by
      rw [← cdf_eq_real, hcdf, one_mul]
    have hne : (expMeasure 1) (Set.Iic c) ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hne, ← measureReal_def, hreal]
  have hcompl : Set.Ioi c = (Set.Iic c)ᶜ := by
    ext y; simp [Set.mem_Ioi]
  rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), hIic, measure_univ]
  have hle : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpos : (0:ℝ) ≤ 1 - Real.exp (-c) := by linarith
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hpos]
  congr 1
  ring

/-- **Equation (3)**: with `m` exponentially distributed with survivor function
`P[m > t] = e^{-t}`, the rate-driven sojourn time `S'` satisfies
`P[S' > t] = P[Λ_t ≤ m] = exp(-Λ_t)`. -/
theorem expMeasure_survivor {Ω X : Type*} (M : ShiftSystem Ω X) (lam : X → ℝ)
    (hlam : ∀ y, 0 ≤ lam y) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    (expMeasure 1) {m : ℝ | M.addFunctional lam t ω < m}
      = ENNReal.ofReal (M.multFunctional lam t ω) := by
  have hset : {m : ℝ | M.addFunctional lam t ω < m} = Set.Ioi (M.addFunctional lam t ω) := rfl
  rw [hset, expMeasure_Ioi _ (ShiftSystem.addFunctional_nonneg hlam ht ω)]
  rfl

/-- The lack-of-memory property of the exponential threshold:
`P[m > c + s] = P[m > c] · P[m > s]`. -/
theorem expMeasure_Ioi_add (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    (expMeasure 1) (Set.Ioi (c + s))
      = (expMeasure 1) (Set.Ioi c) * (expMeasure 1) (Set.Ioi s) := by
  rw [expMeasure_Ioi _ (by linarith), expMeasure_Ioi c hc, expMeasure_Ioi s hs,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 1
  ring_nf

end Exponential

end Bujorianu2006

end
