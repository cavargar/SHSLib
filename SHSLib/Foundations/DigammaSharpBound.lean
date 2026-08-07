/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sharp upper bound `ψ(x) < log x − 1/(2x)`

Batch 148 proved `log x − 1/x < ψ(x) < log x` from the mean value theorem.  The
upper bound is not sharp: the classical estimate is

  `ψ(x) < log x − 1/(2x)`  (`digamma_lt_log_sub_half_inv`).

The proof is a telescoping argument on `f(x) = log x − 1/(2x) − ψ(x)`:

* `f(x) − f(x+1) > 0` for every `x > 0`, which after using the recurrence
  `ψ(x+1) = ψ(x) + 1/x` reduces to the elementary inequality
  `log (1+t) < t − t²/(2(1+t))` at `t = 1/x` (`log_one_add_lt_sub`);
* `f(x+n) → 0` as `n → ∞`, from `ψ(y) − log y → 0` of batch 148.

Hence `f(x) > f(x+1) ≥ lim_n f(x+n) = 0`.  Specialising at `x = n+1` sharpens
the harmonic bound of batch 148 to
`H_n < γ + log(n+1) − 1/(2(n+1))` (`harmonic_lt_log_sub_half_inv`).
-/
import SHSLib.Foundations.DigammaAsymptotics

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-! ### An elementary logarithmic inequality -/

/-- `log (1+t) < t − t²/(2(1+t))` for every `t > 0`. -/
theorem log_one_add_lt_sub {t : ℝ} (ht : 0 < t) :
    Real.log (1 + t) < t - t ^ 2 / (2 * (1 + t)) := by
  set g : ℝ → ℝ := fun s => s - s ^ 2 / (2 * (1 + s)) - Real.log (1 + s) with hg_def
  have hderiv : ∀ s ∈ Ici (0 : ℝ), HasDerivAt g (s ^ 2 / (2 * (1 + s) ^ 2)) s := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := hs
    have hpos : (0 : ℝ) < 1 + s := by linarith
    have h1 : HasDerivAt (fun w : ℝ => w) 1 s := hasDerivAt_id s
    have hden : HasDerivAt (fun w : ℝ => 2 * (1 + w)) 2 s := by
      simpa using ((hasDerivAt_id s).const_add (1 : ℝ)).const_mul (2 : ℝ)
    have hnum : HasDerivAt (fun w : ℝ => w ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    have hdiv : HasDerivAt (fun w : ℝ => w ^ 2 / (2 * (1 + w)))
        ((2 * s * (2 * (1 + s)) - s ^ 2 * 2) / (2 * (1 + s)) ^ 2) s :=
      hnum.div hden (by positivity)
    have hlog : HasDerivAt (fun w : ℝ => Real.log (1 + w)) (1 / (1 + s)) s := by
      have h := (Real.hasDerivAt_log hpos.ne').comp s ((hasDerivAt_id s).const_add (1 : ℝ))
      simpa [one_div] using h
    have h := (h1.sub hdiv).sub hlog
    convert h using 1
    field_simp
    ring
  have hmono : StrictMonoOn g (Ici (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : (0 : ℝ) < s := hs
      rw [(hderiv s (le_of_lt hs0)).deriv]
      positivity
  have h0 : g 0 = 0 := by simp [hg_def]
  have hlt := hmono (Set.self_mem_Ici) (mem_Ici.mpr ht.le) ht
  rw [h0] at hlt
  simp only [hg_def] at hlt
  linarith

/-! ### The telescoping step -/

/-- The step inequality for `f(x) = log x − 1/(2x) − ψ(x)`. -/
theorem log_sub_half_inv_sub_digamma_step {x : ℝ} (hx : 0 < x) :
    (Real.log (x + 1) - 1 / (2 * (x + 1)) - digamma (x + 1))
      < Real.log x - 1 / (2 * x) - digamma x := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hrec : digamma (x + 1) = digamma x + 1 / x := digamma_recurrence hx
  have hlog : Real.log (x + 1) - Real.log x = Real.log (1 + 1 / x) := by
    rw [← Real.log_div hx1.ne' hx.ne']
    congr 1
    field_simp
  have hkey := log_one_add_lt_sub (t := 1 / x) (by positivity)
  have hsimp : (1 / x) ^ 2 / (2 * (1 + 1 / x)) = 1 / (2 * x * (x + 1)) := by
    field_simp
  rw [hsimp] at hkey
  have hgap : 1 / (2 * x) - 1 / (2 * (x + 1)) = 1 / (2 * x * (x + 1)) := by
    field_simp
    ring
  rw [hrec]
  have : Real.log (x + 1) = Real.log x + Real.log (1 + 1 / x) := by linarith [hlog]
  rw [this]
  linarith [hkey, hgap]

/-! ### A reusable telescoping criterion -/

/-- If `f` strictly decreases along unit steps on `(0, ∞)` and tends to `0` at
infinity, then `f` is strictly positive on `(0, ∞)`. -/
theorem pos_of_step_of_tendsto_atTop {f : ℝ → ℝ}
    (hstep : ∀ y : ℝ, 0 < y → f (y + 1) < f y)
    (hlim : Tendsto f atTop (𝓝 0)) {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have hchain : ∀ n : ℕ, f (x + 1 + n) ≤ f (x + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hpos : (0 : ℝ) < x + 1 + n := by positivity
        have h := hstep (x + 1 + n) hpos
        have hcast : x + 1 + ((n : ℝ) + 1) = (x + 1 + n) + 1 := by ring
        push_cast
        rw [hcast]
        linarith
  have hgo : Tendsto (fun n : ℕ => x + 1 + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun n : ℕ => f (x + 1 + n)) atTop (𝓝 0) := hlim.comp hgo
  have hle : (0 : ℝ) ≤ f (x + 1) := le_of_tendsto htend (Eventually.of_forall hchain)
  exact lt_of_le_of_lt hle (hstep x hx)

/-! ### The sharp bound -/

/-- **`ψ(x) < log x − 1/(2x)`** for every `x > 0`. -/
theorem digamma_lt_log_sub_half_inv {x : ℝ} (hx : 0 < x) :
    digamma x < Real.log x - 1 / (2 * x) := by
  set f : ℝ → ℝ := fun y => Real.log y - 1 / (2 * y) - digamma y with hf_def
  have hstep : ∀ y : ℝ, 0 < y → f (y + 1) < f y := fun y hy =>
    log_sub_half_inv_sub_digamma_step hy
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => digamma y - Real.log y) atTop (𝓝 0) :=
      tendsto_digamma_sub_log_atTop
    have h2 : Tendsto (fun y : ℝ => 1 / (2 * y)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have h1 := h0.const_mul (1 / 2 : ℝ)
      simp only [mul_zero] at h1
      exact h1.congr (fun y => by simp [one_div, mul_comm])
    have := (h1.neg).sub h2
    simpa [hf_def, sub_eq_add_neg] using this.congr (fun y => by ring)
  have hpos := pos_of_step_of_tendsto_atTop hstep hlim hx
  simp only [hf_def] at hpos
  linarith

/-- The sharpened harmonic bound: `H_n < γ + log(n+1) − 1/(2(n+1))`. -/
theorem harmonic_lt_log_sub_half_inv (n : ℕ) :
    ((harmonic n : ℚ) : ℝ)
      < Real.eulerMascheroniConstant + Real.log ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := digamma_lt_log_sub_half_inv hpos
  rw [digamma_nat_add_one_eq_harmonic n] at h
  linarith

end SHSLib.Trigamma
