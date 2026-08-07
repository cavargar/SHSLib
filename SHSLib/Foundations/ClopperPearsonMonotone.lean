/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monotonicity of the Clopper–Pearson endpoints in the observed count

Observing more successes should shift the exact confidence interval to the
right.  Both endpoints are quantiles at a *fixed* level of Beta laws whose
parameters change by moving one unit from the second parameter to the first
when the count increases by one, so everything follows from the single
comparison

  `Q_p(a, b+1) ≤ Q_p(a+1, b)`,

which in turn is the parameter monotonicity `I_x(a+1,b) ≤ I_x(a,b+1)` of
`SHSLib/Foundations/ClopperPearson.lean` read through the strictly increasing
CDF: the quantile of the pointwise *smaller* CDF is the *larger* number.
-/
import SHSLib.Foundations.ClopperPearson

open Real Set

namespace SHSLib.Trigamma

/-- **Moving one unit from the second parameter to the first increases the
quantile.**  Equivalently: the Beta law `Beta(a+1, b)` is stochastically larger
than `Beta(a, b+1)`, so its quantiles are larger. -/
theorem betaQuantile_succ_snd_le_succ_fst {a b p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    betaQuantile a (b + 1) p ≤ betaQuantile (a + 1) b p := by
  have ha1 : (0:ℝ) < a + 1 := by linarith
  have hb1 : (0:ℝ) < b + 1 := by linarith
  obtain ⟨hx0, hx1⟩ := betaQuantile_mem_Icc ha hb1 hp0 hp1
  obtain ⟨hy0, hy1⟩ := betaQuantile_mem_Icc ha1 hb hp0 hp1
  set x := betaQuantile a (b + 1) p with hxdef
  set y := betaQuantile (a + 1) b p with hydef
  have hcx : regBetaFn a (b + 1) x = p := regBetaFn_betaQuantile ha hb1 hp0 hp1
  have hcy : regBetaFn (a + 1) b y = p := regBetaFn_betaQuantile ha1 hb hp0 hp1
  have hcmp : regBetaFn (a + 1) b y ≤ regBetaFn a (b + 1) y :=
    regBetaFn_succ_fst_le_succ_snd ha hb hy0 hy1
  by_contra hcon
  push_neg at hcon
  have hstrict := regBetaFn_strictMonoOn (a := a) (b := b + 1) ha hb1 ⟨hy0, hy1⟩ ⟨hx0, hx1⟩ hcon
  rw [hcx] at hstrict
  rw [hcy] at hcmp
  linarith

section
variable {alpha : ℝ} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)

include halpha0 halpha1

/-- **The lower endpoint increases with the observed count.**  Both sides refer
to the same number `j+m+3` of trials, the left-hand side to `j+1` observed
successes and the right-hand side to `j+2`. -/
theorem clopperPearsonLower_mono (j m : ℕ) :
    clopperPearsonLower j (m + 1) alpha ≤ clopperPearsonLower (j + 1) m alpha := by
  have h := betaQuantile_succ_snd_le_succ_fst (a := (j : ℝ) + 1) (b := (m : ℝ) + 2)
    (p := alpha / 2) (by positivity) (by positivity) (by linarith) (by linarith)
  have e1 : ((m : ℝ) + 2 + 1) = ((m + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
  have e2 : ((j : ℝ) + 1 + 1) = ((j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [e1, e2] at h
  simpa only [clopperPearsonLower] using h

/-- **The upper endpoint increases with the observed count.**  Both sides refer
to the same number `j+m+3` of trials, the left-hand side to `j+1` observed
successes and the right-hand side to `j+2`. -/
theorem clopperPearsonUpper_mono (j m : ℕ) :
    clopperPearsonUpper j (m + 1) alpha ≤ clopperPearsonUpper (j + 1) m alpha := by
  have h := betaQuantile_succ_snd_le_succ_fst (a := (j : ℝ) + 2) (b := (m : ℝ) + 1)
    (p := 1 - alpha / 2) (by positivity) (by positivity) (by linarith) (by linarith)
  have e1 : ((m : ℝ) + 1 + 1) = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have e2 : ((j : ℝ) + 2 + 1) = ((j + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
  rw [e1, e2] at h
  simpa only [clopperPearsonUpper] using h

end

end SHSLib.Trigamma
