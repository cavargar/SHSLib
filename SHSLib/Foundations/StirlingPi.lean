/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Explicit approximations to `π` from the central binomial coefficient

Batch 162 proved the exact identity `W(n) = 16ⁿ/(C(2n,n)²(2n+1))` for Wallis'
partial product together with the bracket

  `πn/(2n+1)·e^{F₁(n)} < W(n) < πn/(2n+1)·e^{F₂(n)}`,
  `F₁ = 1/(4n) − 1/(96n³) − 1/(20160n⁵)`,
  `F₂ = 1/(4n) − 1/(96n³) + 1/(315n⁵)`.

Solving for `π` turns this into a *computable* approximation with proved error
bars: with `A(n) = 16ⁿ/(n · C(2n,n)²)`,

  `A(n) e^{−F₂(n)} < π < A(n) e^{−F₁(n)}`,

whose two sides differ by the factor `e^{1/(315n⁵) + 1/(20160n⁵)}`.  In
particular `A(n)·e^{−1/(4n) + 1/(96n³)} → π`, with relative error `O(n⁻⁵)`.
-/
import SHSLib.Foundations.StirlingWallis

open Real Set Filter Topology

namespace SHSLib.Trigamma

/-- **Explicit two-sided approximation of `π`** by the central binomial
coefficient: for `n ≥ 1`,
`16ⁿ/(n C(2n,n)²) · e^{−1/(4n) + 1/(96n³) − 1/(315n⁵)} < π
   < 16ⁿ/(n C(2n,n)²) · e^{−1/(4n) + 1/(96n³) + 1/(20160n⁵)}`. -/
theorem pi_bracket_centralBinom {n : ℕ} (hn : 1 ≤ n) :
    16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2)
          * Real.exp (-(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
            - 1 / (315 * (n : ℝ) ^ 5)) < π ∧
      π < 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2)
            * Real.exp (-(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
              + 1 / (20160 * (n : ℝ) ^ 5)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hcb : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  obtain ⟨h1, h2⟩ := wallis_bracket hn
  rw [wallis_eq_centralBinom n] at h1 h2
  set F1 : ℝ := 1 / (4 * (n : ℝ)) - 1 / (96 * (n : ℝ) ^ 3) - 1 / (20160 * (n : ℝ) ^ 5)
    with hF1
  set F2 : ℝ := 1 / (4 * (n : ℝ)) - 1 / (96 * (n : ℝ) ^ 3) + 1 / (315 * (n : ℝ) ^ 5)
    with hF2
  have hneg1 : -(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
      + 1 / (20160 * (n : ℝ) ^ 5) = -F1 := by rw [hF1]; ring
  have hneg2 : -(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
      - 1 / (315 * (n : ℝ) ^ 5) = -F2 := by rw [hF2]; ring
  rw [hneg1, hneg2]
  constructor
  · -- from `W(n) < πn/(2n+1) e^{F₂}`
    have h := mul_lt_mul_of_pos_right h2 (mul_pos (mul_pos hcb hcb) h2n1)
    have hL : 16 ^ n / ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1))
        * ((Nat.centralBinom n : ℝ) * (Nat.centralBinom n : ℝ) * (2 * (n : ℝ) + 1))
        = 16 ^ n := by
      field_simp
    have hR : π * (n : ℝ) / (2 * (n : ℝ) + 1) * Real.exp F2
        * ((Nat.centralBinom n : ℝ) * (Nat.centralBinom n : ℝ) * (2 * (n : ℝ) + 1))
        = π * ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2 * Real.exp F2) := by
      field_simp
    rw [hL, hR] at h
    have hrw : 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2) * Real.exp (-F2)
        = 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2 * Real.exp F2) := by
      rw [Real.exp_neg]
      field_simp
    rw [hrw, div_lt_iff₀ (by positivity)]
    linarith
  · -- from `πn/(2n+1) e^{F₁} < W(n)`
    have h := mul_lt_mul_of_pos_right h1 (mul_pos (mul_pos hcb hcb) h2n1)
    have hL : π * (n : ℝ) / (2 * (n : ℝ) + 1) * Real.exp F1
        * ((Nat.centralBinom n : ℝ) * (Nat.centralBinom n : ℝ) * (2 * (n : ℝ) + 1))
        = π * ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2 * Real.exp F1) := by
      field_simp
    have hR : 16 ^ n / ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1))
        * ((Nat.centralBinom n : ℝ) * (Nat.centralBinom n : ℝ) * (2 * (n : ℝ) + 1))
        = 16 ^ n := by
      field_simp
    rw [hL, hR] at h
    have hrw : 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2) * Real.exp (-F1)
        = 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2 * Real.exp F1) := by
      rw [Real.exp_neg]
      field_simp
    rw [hrw, lt_div_iff₀ (by positivity)]
    linarith

/-- **The approximating sequence converges to `π`**:
`16ⁿ/(n C(2n,n)²) · e^{−1/(4n) + 1/(96n³)} → π`. -/
theorem tendsto_pi_approx :
    Tendsto (fun n : ℕ => 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2)
      * Real.exp (-(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3))) atTop (𝓝 π) := by
  have hinvpow : ∀ k : ℕ, 1 ≤ k →
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) ^ k)) atTop (𝓝 0) := by
    intro k hk
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ k) atTop atTop :=
      (tendsto_pow_atTop (by omega : k ≠ 0)).comp tendsto_natCast_atTop_atTop
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hpow
  have hexpfac : ∀ c : ℝ, ∀ k : ℕ, 1 ≤ k →
      Tendsto (fun n : ℕ => Real.exp (c / ((n : ℝ) ^ k))) atTop (𝓝 1) := by
    intro c k hk
    have h0 : Tendsto (fun n : ℕ => c / ((n : ℝ) ^ k)) atTop (𝓝 0) := by
      have h := (hinvpow k hk).const_mul c
      simp only [mul_zero] at h
      refine h.congr (fun n => ?_)
      rw [mul_one_div]
    simpa using (Real.continuous_exp.tendsto 0).comp h0
  -- squeeze between the two sides of `pi_bracket_centralBinom`
  set G : ℕ → ℝ := fun n => 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2)
    * Real.exp (-(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)) with hG
  have hlow : Tendsto (fun n : ℕ => π * Real.exp (-(1 / (20160 * (n : ℝ) ^ 5)))) atTop (𝓝 π) := by
    have h := hexpfac (-(1 / 20160 : ℝ)) 5 (by norm_num)
    have h' : Tendsto (fun n : ℕ => Real.exp (-(1 / (20160 * (n : ℝ) ^ 5)))) atTop (𝓝 1) := by
      refine h.congr (fun n => ?_)
      rcases eq_or_ne ((n : ℝ)) 0 with h0 | h0
      · simp [h0]
      · congr 1
        field_simp
    simpa using h'.const_mul π
  have hhigh : Tendsto (fun n : ℕ => π * Real.exp (1 / (315 * (n : ℝ) ^ 5))) atTop (𝓝 π) := by
    have h := hexpfac ((1 / 315 : ℝ)) 5 (by norm_num)
    have h' : Tendsto (fun n : ℕ => Real.exp (1 / (315 * (n : ℝ) ^ 5))) atTop (𝓝 1) := by
      refine h.congr (fun n => ?_)
      rcases eq_or_ne ((n : ℝ)) 0 with h0 | h0
      · simp [h0]
      · congr 1
        field_simp
    simpa using h'.const_mul π
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨-, h2⟩ := pi_bracket_centralBinom hn
    have hsplit : 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2)
        * Real.exp (-(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
          + 1 / (20160 * (n : ℝ) ^ 5))
        = G n * Real.exp (1 / (20160 * (n : ℝ) ^ 5)) := by
      rw [hG]
      rw [show -(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3) + 1 / (20160 * (n : ℝ) ^ 5)
        = (-(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)) + 1 / (20160 * (n : ℝ) ^ 5) by ring,
        Real.exp_add]
      ring
    rw [hsplit] at h2
    have h3 := mul_lt_mul_of_pos_right h2 (Real.exp_pos (-(1 / (20160 * (n : ℝ) ^ 5))))
    have hcancel : G n * Real.exp (1 / (20160 * (n : ℝ) ^ 5))
        * Real.exp (-(1 / (20160 * (n : ℝ) ^ 5))) = G n := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [hcancel] at h3
    exact h3.le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨h1, -⟩ := pi_bracket_centralBinom hn
    have hsplit : 16 ^ n / ((n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2)
        * Real.exp (-(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)
          - 1 / (315 * (n : ℝ) ^ 5))
        = G n * Real.exp (-(1 / (315 * (n : ℝ) ^ 5))) := by
      rw [hG]
      rw [show -(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3) - 1 / (315 * (n : ℝ) ^ 5)
        = (-(1 / (4 * (n : ℝ))) + 1 / (96 * (n : ℝ) ^ 3)) + -(1 / (315 * (n : ℝ) ^ 5)) by ring,
        Real.exp_add]
      ring
    rw [hsplit] at h1
    have h3 := mul_lt_mul_of_pos_right h1 (Real.exp_pos (1 / (315 * (n : ℝ) ^ 5)))
    have hcancel : G n * Real.exp (-(1 / (315 * (n : ℝ) ^ 5)))
        * Real.exp (1 / (315 * (n : ℝ) ^ 5)) = G n := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [hcancel] at h3
    exact h3.le

end SHSLib.Trigamma
