/-
# Decay from an unstable state: §9.1.5, (9.1.22)–(9.1.32)

The conditional mean exit time `T(a, x)` through `a` satisfies (9.1.22)–(9.1.23), i.e.
(5.2.183)–(5.2.185); its solution is `Gardiner.Escape.condExit_spec`, and the closed form (9.1.24)
is `Gardiner.Escape.greenSol_eq_split`.  Here:

* `isBwdSol_reflect` — reflection symmetry of the backward equation for odd drift and even
  diffusion;
* `symmetric_decay` — **exact result for (9.1.25)-type symmetric problems**: if `A` is odd, `B`
  even, and the interval is `(-c, c)`, then starting from the unstable point `0`,
  `π_a(0) = π_c(0) = ½` and `T(a, 0) = T(c, 0) = T(0)` (the conditional exit times equal the
  unconditional one (5.2.158));
* `invertedParabola_decay` — its application to Gardiner's example (9.1.25), `U = -kx²/2`;
* `smolReflB_eq` — the right-hand side of (9.1.31) is *exactly* the mean exit time to `a` with a
  reflecting barrier at `b` (formula (5.2.161) for the Smoluchowski equation), as the text says.
  The approximation `T(a, b) ≃ (9.1.31)` itself rests on the heuristic estimates (9.1.26)–(9.1.30)
  and is not formalised; note the text's case label in (9.1.30) should read `x' < b`, not
  `x' < a`.
-/
import SHSLib.Gardiner.Escape.FirstPassage

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

section reflect

variable {A B : ℝ → ℝ}

/-- **Reflection symmetry.**  If `A` is odd and `B` is even, `x ↦ u(-x)` solves the backward
equation with right-hand side `x ↦ f(-x)` whenever `u` solves it with `f`. -/
theorem isBwdSol_reflect (hAodd : ∀ x, A (-x) = -A x) (hBeven : ∀ x, B (-x) = B x)
    {f u : ℝ → ℝ} (hu : IsBwdSol A B f u) :
    IsBwdSol A B (fun x => f (-x)) (fun x => u (-x)) := by
  obtain ⟨u1, u2, h⟩ := hu
  refine ⟨fun x => -u1 (-x), fun x => u2 (-x), fun x => ⟨?_, ?_, ?_⟩⟩
  · have := (h (-x)).1.comp x (hasDerivAt_neg x)
    convert this using 1; ring
  · have := ((h (-x)).2.1.comp x (hasDerivAt_neg x)).neg
    convert this using 1
    simp only; ring
  · have := (h (-x)).2.2
    rw [hAodd, hBeven] at this
    simp only
    linarith

lemma isBwdSol_const (c : ℝ) : IsBwdSol A B (fun _ => 0) (fun _ => c) :=
  ⟨fun _ => 0, fun _ => 0, fun x => ⟨hasDerivAt_const x c, hasDerivAt_const x 0, by ring⟩⟩

variable (hA : Continuous A) (hB : Continuous B) (hBpos : ∀ x, 0 < B x)
  (hAodd : ∀ x, A (-x) = -A x) (hBeven : ∀ x, B (-x) = B x)
include hA hB hBpos hAodd hBeven

omit hAodd hBeven in
lemma exitB_isBwdSol {a b : ℝ} (hab : a < b) : IsBwdSol A B (fun _ => 0) (exitB A B a b) := by
  have h := isBwdSol_sub (isBwdSol_const (A := A) (B := B) 1) (exitA_spec hA hB hBpos hab).1
  have e : (fun x => (1 : ℝ) - exitA A B a b x) = exitB A B a b := by
    ext x; have := exitA_add_exitB hA hB hBpos hab x; linarith
  simpa only [sub_self, e] using h

lemma exitA_reflect {c : ℝ} (hc : 0 < c) :
    (fun x => exitA A B (-c) c (-x)) = exitB A B (-c) c := by
  have hac : -c < c := by linarith
  obtain ⟨hs, ha, hb, -⟩ := exitA_spec hA hB hBpos hac
  have hv := isBwdSol_reflect hAodd hBeven hs
  have hB' := exitB_isBwdSol hA hB hBpos hac
  refine bwd_unique hA hB hBpos hac hv hB' ?_ ?_
  · simp only [neg_neg, hb]
    have := exitA_add_exitB hA hB hBpos hac (-c); rw [ha] at this; linarith
  · simp only [ha]
    have := exitA_add_exitB hA hB hBpos hac c; rw [hb] at this; linarith

/-- **Decay from the unstable point of a symmetric problem** (§9.1.5, exact).  For odd `A`,
even `B` on `(-c, c)`: `π_a(0) = π_c(0) = ½`, and the conditional exit times
`T(a, 0) = π_a(0)⁻¹ [π_a T(a, ·)](0)` and `T(c, 0)` both equal the unconditional mean exit time
`T(0)` of (5.2.158). -/
theorem symmetric_decay {c : ℝ} (hc : 0 < c) :
    exitA A B (-c) c 0 = 1 / 2 ∧ exitB A B (-c) c 0 = 1 / 2 ∧
      greenSol A B (exitA A B (-c) c) (-c) c 0 / exitA A B (-c) c 0 = mfptTwo A B (-c) c 0 ∧
      greenSol A B (exitB A B (-c) c) (-c) c 0 / exitB A B (-c) c 0 = mfptTwo A B (-c) c 0 := by
  have hac : -c < c := by linarith
  have hr := congrFun (exitA_reflect hA hB hBpos hAodd hBeven hc) 0
  simp only [neg_zero] at hr
  have hsum := exitA_add_exitB hA hB hBpos hac 0
  have hpa : exitA A B (-c) c 0 = 1 / 2 := by linarith
  have hpb : exitB A B (-c) c 0 = 1 / 2 := by linarith
  -- the reflected conditional solution
  obtain ⟨sA, aA, bA, -⟩ := greenSol_spec hA hB hBpos (exitA_cont hA hB hBpos (-c) c) hac
  obtain ⟨-, -, -, uB⟩ := greenSol_spec hA hB hBpos (exitB_cont hA hB hBpos (-c) c) hac
  have hv := isBwdSol_reflect hAodd hBeven sA
  have hfeq : (fun x => -exitA A B (-c) c (-x)) = fun x => -exitB A B (-c) c x := by
    ext x; rw [← congrFun (exitA_reflect hA hB hBpos hAodd hBeven hc) x]
  rw [hfeq] at hv
  have hw := uB _ hv (by simp only [neg_neg, bA]) (by simp only [aA])
  have hw0 := congrFun hw 0
  simp only [neg_zero] at hw0
  have hT := congrFun (condExit_add hA hB hBpos hac) 0
  simp only at hT
  refine ⟨hpa, hpb, ?_, ?_⟩
  · rw [hpa]; rw [← hT, ← hw0]; ring
  · rw [hpb]; rw [← hT, hw0]; ring

end reflect

/-- **Example (9.1.25): the inverted parabola `U = -kx²/2`** (drift `A = kx`, `B = 2D`), started at
the unstable point `0` between absorbing barriers at `±c`: the splitting probabilities are `½`
and both conditional mean exit times equal the unconditional one. -/
theorem invertedParabola_decay {k D c : ℝ} (hD : 0 < D) (hc : 0 < c) :
    exitA (fun x => k * x) (fun _ => 2 * D) (-c) c 0 = 1 / 2 ∧
      exitB (fun x => k * x) (fun _ => 2 * D) (-c) c 0 = 1 / 2 ∧
      greenSol (fun x => k * x) (fun _ => 2 * D) (exitA (fun x => k * x) (fun _ => 2 * D) (-c) c)
          (-c) c 0 / exitA (fun x => k * x) (fun _ => 2 * D) (-c) c 0
        = mfptTwo (fun x => k * x) (fun _ => 2 * D) (-c) c 0 ∧
      greenSol (fun x => k * x) (fun _ => 2 * D) (exitB (fun x => k * x) (fun _ => 2 * D) (-c) c)
          (-c) c 0 / exitB (fun x => k * x) (fun _ => 2 * D) (-c) c 0
        = mfptTwo (fun x => k * x) (fun _ => 2 * D) (-c) c 0 :=
  symmetric_decay (by fun_prop) continuous_const (fun _ => by linarith) (fun x => by ring)
    (fun _ => rfl) hc

section smol

variable {U U' : ℝ → ℝ} (hU : ∀ x, HasDerivAt U (U' x) x) (hU' : Continuous U') {D : ℝ}
  (hD : 0 < D)
include hU hU' hD

/-- **(9.1.31) is an exact reflecting-barrier exit time.**  For the Smoluchowski equation, the
mean exit time (5.2.161) to an absorbing barrier at `a`, with `b` reflecting, started at `b`, is
`D⁻¹ ∫_a^b dx' e^{U(x')/D} ∫_{x'}^b e^{-U(z)/D} dz`, the right-hand side of (9.1.31) (the
normalisation `𝒩` of `p_s` cancels). -/
theorem smolReflB_eq (a b : ℝ) :
    mfptReflB (fun x => -U' x) (fun _ => 2 * D) a b b
      = D⁻¹ * ∫ y in a..b, exp (U y / D) * ∫ z in y..b, exp (-U z / D) := by
  rw [mfptReflB, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro y _
  simp only [smol_psi hU hU' hD]
  have hin : ∫ z in y..b, exp (-(U z - U a) / D) / (2 * D)
      = exp (U a / D) / (2 * D) * ∫ z in y..b, exp (-U z / D) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro z _
    simp only
    rw [show -(U z - U a) / D = U a / D + -U z / D by ring, exp_add]; ring
  rw [hin, ← exp_neg, show -(-(U y - U a) / D) = U y / D + -(U a / D) by ring, exp_add, exp_neg]
  have := exp_pos (U a / D)
  field_simp

end smol

/-- **Instance of (9.1.31)** for the quartic double well (`D = 1`, `a = -1`, `b = 0`). -/
theorem doubleWell_reflB :
    mfptReflB (fun y => -(y ^ 3 - y)) (fun _ => 2 * 1) (-1) 0 0
      = 1⁻¹ * ∫ y in (-1 : ℝ)..0, exp (Gardiner.Adiabatic.dwU 0 y / 1) *
          ∫ z in y..0, exp (-Gardiner.Adiabatic.dwU 0 z / 1) := by
  have hU : ∀ y, HasDerivAt (Gardiner.Adiabatic.dwU 0) (y ^ 3 - y) y := by
    intro y
    rw [dwU_zero]
    have := ((hasDerivAt_pow 4 y).div_const 4).sub ((hasDerivAt_pow 2 y).div_const 2)
    convert this using 1; push_cast; ring
  exact smolReflB_eq (U' := fun y => y ^ 3 - y) hU (by fun_prop) one_pos (-1) 0

end Gardiner.Escape
