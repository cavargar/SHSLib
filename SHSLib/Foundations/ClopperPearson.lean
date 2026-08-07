/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Clopper–Pearson interval

The exact ("Clopper–Pearson") confidence interval for the success probability
of a binomial experiment is *defined* by Beta quantiles and *interpreted*
through binomial tail probabilities.  For `c` successes in `n` trials at level
`α` the endpoints are

  `p⁻ = Q_{α/2}(c, n−c+1)`,   `p⁺ = Q_{1−α/2}(c+1, n−c)`,

and they are characterised by

  `P(Bin(n, p⁻) ≥ c) = α/2`,   `P(Bin(n, p⁺) ≤ c) = α/2`.

This module builds that dictionary on top of

* the Beta quantile of `SHSLib/Foundations/BetaQuantileFunction.lean`,
* the Beta–Binomial identity of `SHSLib/Foundations/BetaBinomial.lean` and its
  measure form in `SHSLib/Foundations/BetaBinomialMeasure.lean`,
* the parameter recurrence of `SHSLib/Foundations/BetaRecurrence.lean`.

Throughout, the experiment is indexed by two natural numbers `j, m`: there are
`c = j+1` successes in `n = j+m+2` trials.  This covers exactly the interior
cases `1 ≤ c ≤ n−1`, where both endpoints are genuine quantiles (for `c = 0`
the lower endpoint is `0` and for `c = n` the upper endpoint is `1` by
convention, no Beta law being involved).

The two monotonicity lemmas `regBetaFn_succ_fst_le` and `regBetaFn_le_succ_snd`
are of independent interest: they say that the Beta CDF decreases when the
first parameter is increased and increases when the second one is, which at
integer parameters is the obvious statement that a binomial upper tail shrinks
as its threshold rises.
-/
import SHSLib.Foundations.BetaRecurrence
import SHSLib.Foundations.BetaQuantileFunction
import SHSLib.Foundations.BetaBinomialMeasure

open Real Set MeasureTheory ENNReal NNReal

namespace SHSLib.Trigamma

/-! ### Monotonicity of the Beta CDF in its parameters -/

/-- Increasing the first parameter decreases the Beta CDF:
`I_x(a+1, b) ≤ I_x(a, b)`.  This is the recurrence of
`regBetaFn_recurrence` together with the nonnegativity of the correction
term. -/
theorem regBetaFn_succ_fst_le {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regBetaFn (a + 1) b x ≤ regBetaFn a b x := by
  have h1x : (0:ℝ) ≤ 1 - x := by linarith
  have hB : 0 < betaFn a b := betaFn_pos ha hb
  have hterm : 0 ≤ x ^ a * (1 - x) ^ b / (a * betaFn a b) := by
    have h1 : (0:ℝ) ≤ x ^ a := Real.rpow_nonneg hx0 a
    have h2 : (0:ℝ) ≤ (1 - x) ^ b := Real.rpow_nonneg h1x b
    have h3 : 0 < a * betaFn a b := mul_pos ha hB
    exact div_nonneg (mul_nonneg h1 h2) h3.le
  rw [regBetaFn_recurrence ha hb hx0 hx1]
  linarith

/-- Increasing the second parameter increases the Beta CDF:
`I_x(a, b) ≤ I_x(a, b+1)`.  This follows from `regBetaFn_succ_fst_le` by the
reflection formula `I_x(a,b) = 1 − I_{1−x}(b,a)`. -/
theorem regBetaFn_le_succ_snd {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regBetaFn a b x ≤ regBetaFn a (b + 1) x := by
  have hb1 : (0:ℝ) < b + 1 := by linarith
  have h1 : regBetaFn a b x = 1 - regBetaFn b a (1 - x) := regBetaFn_symm ha hb hx0 hx1
  have h2 : regBetaFn a (b + 1) x = 1 - regBetaFn (b + 1) a (1 - x) :=
    regBetaFn_symm ha hb1 hx0 hx1
  have h3 : regBetaFn (b + 1) a (1 - x) ≤ regBetaFn b a (1 - x) :=
    regBetaFn_succ_fst_le hb ha (by linarith) (by linarith)
  linarith

/-- The two steps combined: moving one unit from the second parameter to the
first decreases the Beta CDF.  At integer parameters this is the inclusion of
binomial upper tails `{i ≥ c+1} ⊆ {i ≥ c}`. -/
theorem regBetaFn_succ_fst_le_succ_snd {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regBetaFn (a + 1) b x ≤ regBetaFn a (b + 1) x :=
  (regBetaFn_succ_fst_le ha hb hx0 hx1).trans (regBetaFn_le_succ_snd ha hb hx0 hx1)

/-! ### The Clopper–Pearson endpoints -/

/-- The **Clopper–Pearson lower endpoint** for `j+1` successes in `j+m+2`
trials at level `alpha`: the `alpha/2`-quantile of `Beta(j+1, m+2)`. -/
noncomputable def clopperPearsonLower (j m : ℕ) (alpha : ℝ) : ℝ :=
  betaQuantile ((j : ℝ) + 1) ((m : ℝ) + 2) (alpha / 2)

/-- The **Clopper–Pearson upper endpoint** for `j+1` successes in `j+m+2`
trials at level `alpha`: the `(1 − alpha/2)`-quantile of `Beta(j+2, m+1)`. -/
noncomputable def clopperPearsonUpper (j m : ℕ) (alpha : ℝ) : ℝ :=
  betaQuantile ((j : ℝ) + 2) ((m : ℝ) + 1) (1 - alpha / 2)

section
variable {alpha : ℝ} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)

include halpha0 halpha1

theorem clopperPearsonLower_mem_Icc (j m : ℕ) :
    clopperPearsonLower j m alpha ∈ Set.Icc (0:ℝ) 1 :=
  betaQuantile_mem_Icc (by positivity) (by positivity) (by linarith) (by linarith)

theorem clopperPearsonUpper_mem_Icc (j m : ℕ) :
    clopperPearsonUpper j m alpha ∈ Set.Icc (0:ℝ) 1 :=
  betaQuantile_mem_Icc (by positivity) (by positivity) (by linarith) (by linarith)

/-- The lower endpoint is where the Beta CDF equals `alpha/2`. -/
theorem regBetaFn_clopperPearsonLower (j m : ℕ) :
    regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 2) (clopperPearsonLower j m alpha) = alpha / 2 :=
  regBetaFn_betaQuantile (by positivity) (by positivity) (by linarith) (by linarith)

/-- The upper endpoint is where the Beta CDF equals `1 − alpha/2`. -/
theorem regBetaFn_clopperPearsonUpper (j m : ℕ) :
    regBetaFn ((j : ℝ) + 2) ((m : ℝ) + 1) (clopperPearsonUpper j m alpha) = 1 - alpha / 2 :=
  regBetaFn_betaQuantile (by positivity) (by positivity) (by linarith) (by linarith)

/-- **The interval is nonempty**: the lower endpoint never exceeds the upper
one.  At the upper endpoint the CDF of the *lower* Beta law is at least
`1 − alpha/2 ≥ alpha/2`, and that CDF is strictly increasing. -/
theorem clopperPearsonLower_le_upper (j m : ℕ) :
    clopperPearsonLower j m alpha ≤ clopperPearsonUpper j m alpha := by
  set pL := clopperPearsonLower j m alpha with hpL
  set pU := clopperPearsonUpper j m alpha with hpU
  obtain ⟨hL0, hL1⟩ := clopperPearsonLower_mem_Icc halpha0 halpha1 j m
  obtain ⟨hU0, hU1⟩ := clopperPearsonUpper_mem_Icc halpha0 halpha1 j m
  have ha : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hb : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hchain : regBetaFn ((j : ℝ) + 2) ((m : ℝ) + 1) pU
      ≤ regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 2) pU := by
    have h := regBetaFn_succ_fst_le_succ_snd (a := (j : ℝ) + 1) (b := (m : ℝ) + 1)
      (x := pU) ha hb hU0 hU1
    have e1 : (j : ℝ) + 1 + 1 = (j : ℝ) + 2 := by ring
    have e2 : (m : ℝ) + 1 + 1 = (m : ℝ) + 2 := by ring
    rwa [e1, e2] at h
  have hU := regBetaFn_clopperPearsonUpper halpha0 halpha1 j m
  have hL := regBetaFn_clopperPearsonLower halpha0 halpha1 j m
  have hle : regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 2) pL
      ≤ regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 2) pU := by
    rw [hL, ← hpU] at *
    rw [hU] at hchain
    linarith
  by_contra hcon
  push_neg at hcon
  have hstrict := regBetaFn_strictMonoOn (a := (j : ℝ) + 1) (b := (m : ℝ) + 2)
    (by positivity) (by positivity) ⟨hU0, hU1⟩ ⟨hL0, hL1⟩ hcon
  linarith

/-! ### The endpoints in binomial language -/

/-- **The defining property of the lower endpoint**:
`P(Bin(j+m+2, p⁻) ≥ j+1) = alpha/2`. -/
theorem binomTail_clopperPearsonLower (j m : ℕ) :
    binomTail j (m + 1) (clopperPearsonLower j m alpha) = alpha / 2 := by
  have h := regBetaFn_clopperPearsonLower halpha0 halpha1 j m
  rw [← h, ← regBetaFn_nat_eq]
  push_cast
  ring_nf

/-- **The defining property of the upper endpoint**, in upper-tail form:
`P(Bin(j+m+2, p⁺) ≥ j+2) = 1 − alpha/2`; equivalently
`P(Bin(j+m+2, p⁺) ≤ j+1) = alpha/2`. -/
theorem binomTail_clopperPearsonUpper (j m : ℕ) :
    binomTail (j + 1) m (clopperPearsonUpper j m alpha) = 1 - alpha / 2 := by
  have h := regBetaFn_clopperPearsonUpper halpha0 halpha1 j m
  rw [← h, ← regBetaFn_nat_eq]
  push_cast
  ring_nf

/-- The lower endpoint as a statement about the binomial measure:
the upper tail `{i ≥ j+1}` of `Bin(j+m+2, p⁻)` has mass `alpha/2`. -/
theorem binomial_toMeasure_clopperPearsonLower (j m : ℕ) :
    (PMF.binomial (clopperPearsonLower j m alpha).toNNReal
        (Real.toNNReal_le_one.mpr (clopperPearsonLower_mem_Icc halpha0 halpha1 j m).2)
        (j + (m + 1) + 1)).toMeasure (binomUpperTail j (j + (m + 1) + 1))
      = ENNReal.ofReal (alpha / 2) := by
  obtain ⟨h0, h1⟩ := clopperPearsonLower_mem_Icc halpha0 halpha1 j m
  rw [binomial_toMeasure_upperTail j (m + 1) h0 h1,
    binomTail_clopperPearsonLower halpha0 halpha1 j m]

/-- The upper endpoint as a statement about the binomial measure:
the lower tail `{i ≤ j+1}` of `Bin(j+m+2, p⁺)` has mass `alpha/2`. -/
theorem binomial_toMeasure_clopperPearsonUpper (j m : ℕ) :
    (PMF.binomial (clopperPearsonUpper j m alpha).toNNReal
        (Real.toNNReal_le_one.mpr (clopperPearsonUpper_mem_Icc halpha0 halpha1 j m).2)
        (j + 1 + m + 1)).toMeasure (binomLowerTail (j + 1) (j + 1 + m + 1))
      = ENNReal.ofReal (alpha / 2) := by
  obtain ⟨h0, h1⟩ := clopperPearsonUpper_mem_Icc halpha0 halpha1 j m
  have hcompl := measure_compl (μ := (PMF.binomial (clopperPearsonUpper j m alpha).toNNReal
      (Real.toNNReal_le_one.mpr h1) (j + 1 + m + 1)).toMeasure)
    (s := binomUpperTail (j + 1) (j + 1 + m + 1)) MeasurableSet.of_discrete
    (measure_ne_top _ _)
  rw [compl_binomUpperTail] at hcompl
  rw [hcompl, binomial_toMeasure_upperTail (j + 1) m h0 h1,
    binomTail_clopperPearsonUpper halpha0 halpha1 j m]
  rw [measure_univ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  ring_nf

end

end SHSLib.Trigamma
