/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coverage of the Clopper–Pearson interval

For `n` Bernoulli trials with unknown success probability `p`, the exact
confidence interval built from the observed count `c` is

  `[p⁻(c), p⁺(c)]`,   `p⁻(c) = Q_{α/2}(c, n−c+1)`,  `p⁺(c) = Q_{1−α/2}(c+1, n−c)`,

with the conventions `p⁻(0) = 0` and `p⁺(n) = 1`.  This module defines those
total endpoints (`cpLo`, `cpHi`) and proves the coverage guarantee

  `P(p⁻(C) ≤ p ≤ p⁺(C)) ≥ 1 − α`,   `C ∼ Bin(n, p)`,

for every `p ∈ [0,1]` and every level `0 ≤ α ≤ 1`.

The argument is the classical one.  The counts at which the lower endpoint
overshoots the truth form a set `A`; each `c ∈ A` satisfies
`P(Bin(n,p) ≥ c) < α/2`, and `A` is contained in the upper tail above its own
smallest element, whose probability is exactly one of those small numbers.  The
counts at which the upper endpoint undershoots are handled symmetrically with
the largest element and a lower tail.  No monotonicity of the endpoints is
needed: containment in the tail above the minimum is automatic.
-/
import SHSLib.Foundations.ClopperPearsonMonotone

open Real Set MeasureTheory ENNReal NNReal

namespace SHSLib.Trigamma

/-! ### The mirror of the quantile/CDF adjunction -/

/-- The companion of `betaQuantile_le_iff`: for `p, x ∈ [0,1]`,
`x ≤ Q(p) ↔ I_x(a,b) ≤ p`. -/
theorem le_betaQuantile_iff {a b p x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ betaQuantile a b p ↔ regBetaFn a b x ≤ p := by
  have hQ := betaQuantile_mem_Icc ha hb hp0 hp1
  have hval : regBetaFn a b (betaQuantile a b p) = p := regBetaFn_betaQuantile ha hb hp0 hp1
  constructor
  · intro h
    have := (regBetaFn_strictMonoOn ha hb).monotoneOn ⟨hx0, hx1⟩ hQ h
    rwa [hval] at this
  · intro h
    by_contra hcon
    push_neg at hcon
    have := regBetaFn_strictMonoOn ha hb hQ ⟨hx0, hx1⟩ hcon
    rw [hval] at this
    linarith

/-! ### The endpoints for an arbitrary observed count -/

/-- The Clopper–Pearson lower endpoint for `c` successes in `n` trials, with the
convention `p⁻(0) = 0`. -/
noncomputable def cpLo (n c : ℕ) (alpha : ℝ) : ℝ :=
  if c = 0 then 0 else betaQuantile (c : ℝ) ((n : ℝ) - c + 1) (alpha / 2)

/-- The Clopper–Pearson upper endpoint for `c` successes in `n` trials, with the
convention `p⁺(n) = 1`. -/
noncomputable def cpHi (n c : ℕ) (alpha : ℝ) : ℝ :=
  if c = n then 1 else betaQuantile ((c : ℝ) + 1) ((n : ℝ) - c) (1 - alpha / 2)

@[simp] theorem cpLo_zero (n : ℕ) (alpha : ℝ) : cpLo n 0 alpha = 0 := by
  simp [cpLo]

@[simp] theorem cpHi_self (n : ℕ) (alpha : ℝ) : cpHi n n alpha = 1 := by
  simp [cpHi]

/-- The lower endpoint agrees with `clopperPearsonLower` on the interior
counts: `c = j+1` successes in `n = j+m+2` trials. -/
theorem cpLo_eq_clopperPearsonLower (j m : ℕ) (alpha : ℝ) :
    cpLo (j + m + 2) (j + 1) alpha = clopperPearsonLower j m alpha := by
  rw [cpLo, if_neg (by omega), clopperPearsonLower]
  norm_num
  ring_nf

/-- The upper endpoint agrees with `clopperPearsonUpper` on the interior
counts. -/
theorem cpHi_eq_clopperPearsonUpper (j m : ℕ) (alpha : ℝ) :
    cpHi (j + m + 2) (j + 1) alpha = clopperPearsonUpper j m alpha := by
  rw [cpHi, if_neg (by omega), clopperPearsonUpper]
  norm_num
  ring_nf

section
variable {p alpha : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)

include hp0 hp1 ha0 ha1

/-- Characterisation of the lower endpoint: for a positive count,
`p⁻(c) ≤ p` exactly when the binomial upper tail at `p` is at least `α/2`. -/
theorem cpLo_le_iff {n c : ℕ} (hc1 : 1 ≤ c) (hcn : c ≤ n) :
    cpLo n c alpha ≤ p ↔ alpha / 2 ≤ regBetaFn (c : ℝ) ((n : ℝ) - c + 1) p := by
  have hcpos : (0:ℝ) < (c : ℝ) := by exact_mod_cast hc1
  have hbpos : (0:ℝ) < (n : ℝ) - c + 1 := by
    have : (c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcn
    linarith
  rw [cpLo, if_neg (by omega)]
  exact betaQuantile_le_iff hcpos hbpos (by linarith) (by linarith) hp0 hp1

/-- Characterisation of the upper endpoint: for a count below `n`,
`p ≤ p⁺(c)` exactly when the binomial upper tail above `c` at `p` is at most
`1 − α/2`. -/
theorem le_cpHi_iff {n c : ℕ} (hcn : c < n) :
    p ≤ cpHi n c alpha ↔ regBetaFn ((c : ℝ) + 1) ((n : ℝ) - c) p ≤ 1 - alpha / 2 := by
  have hapos : (0:ℝ) < (c : ℝ) + 1 := by positivity
  have hbpos : (0:ℝ) < (n : ℝ) - c := by
    have : (c : ℝ) < (n : ℝ) := by exact_mod_cast hcn
    linarith
  rw [cpHi, if_neg (by omega)]
  exact le_betaQuantile_iff hapos hbpos (by linarith) (by linarith) hp0 hp1

end

section
variable {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)

include hp0 hp1

/-- The binomial mass of the upper tail `{i ≥ c}`, in closed form. -/
theorem binomial_measure_upperTail {n c : ℕ} (hc1 : 1 ≤ c) (hcn : c ≤ n) :
    (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure
        (binomUpperTail (c - 1) n)
      = ENNReal.ofReal (regBetaFn (c : ℝ) ((n : ℝ) - c + 1) p) := by
  obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = j + m + 1 := ⟨n - j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [binomial_toMeasure_upperTail j m hp0 hp1, ← regBetaFn_nat_eq]
  congr 2 <;> (push_cast; ring)

/-- The binomial mass of the lower tail `{i ≤ c}`, in closed form. -/
theorem binomial_measure_lowerTail {n c : ℕ} (hcn : c < n) :
    (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure
        (binomLowerTail c n)
      = 1 - ENNReal.ofReal (regBetaFn ((c : ℝ) + 1) ((n : ℝ) - c) p) := by
  have hupper : (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure
      (binomUpperTail c n) = ENNReal.ofReal (regBetaFn ((c : ℝ) + 1) ((n : ℝ) - c) p) := by
    have h := binomial_measure_upperTail hp0 hp1 (n := n) (c := c + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at h
    rw [h]
    congr 2 <;> (push_cast; ring)
  have hcompl := measure_compl (μ := (PMF.binomial p.toNNReal
      (Real.toNNReal_le_one.mpr hp1) n).toMeasure)
    (s := binomUpperTail c n) MeasurableSet.of_discrete (measure_ne_top _ _)
  rw [compl_binomUpperTail] at hcompl
  rw [hcompl, hupper, measure_univ]

end

/-! ### The coverage bound -/

section
variable {p alpha : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)

include hp0 hp1 ha0 ha1

/-- The counts at which the lower endpoint overshoots the true parameter carry
probability at most `α/2`. -/
theorem measure_lowerEndpoint_bad (n : ℕ) :
    (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure
        {c : Fin (n + 1) | ¬ (cpLo n c alpha ≤ p)} ≤ ENNReal.ofReal (alpha / 2) := by
  classical
  set μ := (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure with hμ
  set S : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun c => ¬ (cpLo n (c : ℕ) alpha ≤ p)) with hS
  have hsetS : {c : Fin (n + 1) | ¬ (cpLo n c alpha ≤ p)} = ↑S := by
    ext c; simp [hS]
  rw [hsetS]
  rcases S.eq_empty_or_nonempty with hemp | hne
  · simp [hemp]
  · set c₀ := S.min' hne with hc₀
    have hc₀S : c₀ ∈ S := S.min'_mem hne
    have hc₀bad : ¬ (cpLo n (c₀ : ℕ) alpha ≤ p) := by
      simpa [hS] using hc₀S
    have hc₀pos : 1 ≤ (c₀ : ℕ) := by
      by_contra hcon
      have : (c₀ : ℕ) = 0 := by omega
      rw [this] at hc₀bad
      simp at hc₀bad
      linarith
    have hc₀n : (c₀ : ℕ) ≤ n := by have := c₀.isLt; omega
    have hsub : (↑S : Set (Fin (n + 1))) ⊆ binomUpperTail ((c₀ : ℕ) - 1) n := by
      intro c hc
      have hle : c₀ ≤ c := S.min'_le c (by simpa using hc)
      have : (c₀ : ℕ) ≤ (c : ℕ) := hle
      simp only [binomUpperTail, Set.mem_setOf_eq]
      omega
    have hlt : regBetaFn ((c₀ : ℕ) : ℝ) ((n : ℝ) - (c₀ : ℕ) + 1) p < alpha / 2 := by
      by_contra hcon
      push_neg at hcon
      exact hc₀bad ((cpLo_le_iff hp0 hp1 ha0 ha1 hc₀pos hc₀n).mpr hcon)
    calc μ ↑S ≤ μ (binomUpperTail ((c₀ : ℕ) - 1) n) := measure_mono hsub
      _ = ENNReal.ofReal (regBetaFn ((c₀ : ℕ) : ℝ) ((n : ℝ) - (c₀ : ℕ) + 1) p) :=
          binomial_measure_upperTail hp0 hp1 hc₀pos hc₀n
      _ ≤ ENNReal.ofReal (alpha / 2) := ENNReal.ofReal_le_ofReal hlt.le

/-- The counts at which the upper endpoint undershoots the true parameter carry
probability at most `α/2`. -/
theorem measure_upperEndpoint_bad (n : ℕ) :
    (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure
        {c : Fin (n + 1) | ¬ (p ≤ cpHi n c alpha)} ≤ ENNReal.ofReal (alpha / 2) := by
  classical
  set μ := (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure with hμ
  set T : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun c => ¬ (p ≤ cpHi n (c : ℕ) alpha)) with hT
  have hsetT : {c : Fin (n + 1) | ¬ (p ≤ cpHi n c alpha)} = ↑T := by
    ext c; simp [hT]
  rw [hsetT]
  rcases T.eq_empty_or_nonempty with hemp | hne
  · simp [hemp]
  · set c₁ := T.max' hne with hc₁
    have hc₁T : c₁ ∈ T := T.max'_mem hne
    have hc₁bad : ¬ (p ≤ cpHi n (c₁ : ℕ) alpha) := by
      simpa [hT] using hc₁T
    have hc₁n : (c₁ : ℕ) < n := by
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp c₁.isLt) with h | h
      · exact h
      · exact absurd (by rw [h]; simpa using hp1) hc₁bad
    have hsub : (↑T : Set (Fin (n + 1))) ⊆ binomLowerTail (c₁ : ℕ) n := by
      intro c hc
      have hle : c ≤ c₁ := T.le_max' c (by simpa using hc)
      have : (c : ℕ) ≤ (c₁ : ℕ) := hle
      simpa [binomLowerTail] using this
    have hgt : 1 - alpha / 2 < regBetaFn (((c₁ : ℕ) : ℝ) + 1) ((n : ℝ) - (c₁ : ℕ)) p := by
      by_contra hcon
      push_neg at hcon
      exact hc₁bad ((le_cpHi_iff hp0 hp1 ha0 ha1 hc₁n).mpr hcon)
    have hmem : regBetaFn (((c₁ : ℕ) : ℝ) + 1) ((n : ℝ) - (c₁ : ℕ)) p ∈ Set.Icc (0:ℝ) 1 := by
      have hapos : (0:ℝ) < ((c₁ : ℕ) : ℝ) + 1 := by positivity
      have hbpos : (0:ℝ) < (n : ℝ) - (c₁ : ℕ) := by
        have : ((c₁ : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hc₁n
        linarith
      exact regBetaFn_mem_Icc hapos hbpos hp0 hp1
    calc μ ↑T ≤ μ (binomLowerTail (c₁ : ℕ) n) := measure_mono hsub
      _ = 1 - ENNReal.ofReal (regBetaFn (((c₁ : ℕ) : ℝ) + 1) ((n : ℝ) - (c₁ : ℕ)) p) :=
          binomial_measure_lowerTail hp0 hp1 hc₁n
      _ ≤ ENNReal.ofReal (alpha / 2) := by
          have hsub : (1 : ℝ≥0∞)
              - ENNReal.ofReal (regBetaFn (((c₁ : ℕ) : ℝ) + 1) ((n : ℝ) - (c₁ : ℕ)) p)
              = ENNReal.ofReal
                  (1 - regBetaFn (((c₁ : ℕ) : ℝ) + 1) ((n : ℝ) - (c₁ : ℕ)) p) := by
            rw [ENNReal.ofReal_sub _ hmem.1]
            simp
          rw [hsub]
          exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Coverage of the Clopper–Pearson interval.**  If the count `C` is binomial
with `n` trials and success probability `p`, then the exact interval built from
`C` contains `p` with probability at least `1 − α`. -/
theorem clopperPearson_coverage (n : ℕ) :
    ENNReal.ofReal (1 - alpha) ≤
      (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure
        {c : Fin (n + 1) | cpLo n c alpha ≤ p ∧ p ≤ cpHi n c alpha} := by
  classical
  set μ := (PMF.binomial p.toNNReal (Real.toNNReal_le_one.mpr hp1) n).toMeasure with hμ
  set A : Set (Fin (n + 1)) := {c | ¬ (cpLo n c alpha ≤ p)} with hA
  set B : Set (Fin (n + 1)) := {c | ¬ (p ≤ cpHi n c alpha)} with hB
  have hgood : {c : Fin (n + 1) | cpLo n c alpha ≤ p ∧ p ≤ cpHi n c alpha} = (A ∪ B)ᶜ := by
    ext c
    simp [hA, hB]
  have hbad : μ (A ∪ B) ≤ ENNReal.ofReal alpha := by
    calc μ (A ∪ B) ≤ μ A + μ B := measure_union_le _ _
      _ ≤ ENNReal.ofReal (alpha / 2) + ENNReal.ofReal (alpha / 2) :=
          add_le_add (measure_lowerEndpoint_bad hp0 hp1 ha0 ha1 n)
            (measure_upperEndpoint_bad hp0 hp1 ha0 ha1 n)
      _ = ENNReal.ofReal alpha := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  rw [hgood, measure_compl MeasurableSet.of_discrete (measure_ne_top _ _), measure_univ]
  have h1 : ENNReal.ofReal (1 - alpha) = 1 - ENNReal.ofReal alpha := by
    rw [ENNReal.ofReal_sub _ ha0]
    simp
  rw [h1]
  exact tsub_le_tsub_left hbad 1

end

end SHSLib.Trigamma
