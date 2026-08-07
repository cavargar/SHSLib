/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Beta–Binomial identity

At integer parameters the regularised incomplete Beta function is the upper
tail of a binomial distribution: writing `n = j + m + 1`,

  `I_x(j+1, m+1) = ∑_{i=j+1}^{n} C(n,i) x^i (1−x)^{n−i}`,

i.e. `P(Beta(j+1,m+1) ≤ x) = P(Binomial(n, x) ≥ j+1)`.

The proof matches derivatives.  Both sides are polynomials in `x`: the left is
a primitive of `t^j(1−t)^m` by the fundamental theorem of calculus, and the
derivative of the right telescopes, after the two binomial identities
`i·C(n,i) = n·C(n−1,i−1)` and `(n−i)·C(n,i) = n·C(n−1,i)`, to
`n·C(n−1,j)·x^j(1−x)^m`.  Since `B(j+1,m+1)·n·C(n−1,j) = 1` and both sides
vanish at `x = 0`, the two polynomials coincide — for *every* real `x`, not
only on `[0,1]`.
-/
import SHSLib.Foundations.IncompleteBeta

open Real Set Filter Topology MeasureTheory

namespace SHSLib.Trigamma

/-- The `i`-th term of the binomial upper tail, with `n = j+m+1`. -/
noncomputable def binomTailTerm (j m i : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose (j + m + 1) (j + 1 + i) : ℝ) * x ^ (j + 1 + i) * (1 - x) ^ (m - i)

/-- The **binomial upper tail** `∑_{i=j+1}^{j+m+1} C(j+m+1, i) x^i (1−x)^{j+m+1−i}`,
written with the summation index shifted to `Finset.range (m+1)`. -/
noncomputable def binomTail (j m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), binomTailTerm j m i x

/-- The telescoping auxiliary: `v i = C(j+m, j+i) x^{j+i}(1−x)^{m−i}`. -/
noncomputable def binomTailAux (j m : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  (Nat.choose (j + m) (j + i) : ℝ) * x ^ (j + i) * (1 - x) ^ (m - i)

/-- The derivative of one term of the tail, in telescoping form. -/
theorem binomTailTerm_hasDerivAt (j m i : ℕ) (hi : i ≤ m) (x : ℝ) :
    HasDerivAt (binomTailTerm j m i)
      ((j + m + 1 : ℕ) * (binomTailAux j m x i - binomTailAux j m x (i + 1))) x := by
  have hA : ((j + m + 1 : ℕ) : ℝ) * (Nat.choose (j + m) (j + i) : ℝ)
      = (Nat.choose (j + m + 1) (j + i + 1) : ℝ) * ((j + i + 1 : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.add_one_mul_choose_eq (j + m) (j + i))
  have hBnat : (j + m + 1) * Nat.choose (j + m) (j + 1 + i)
      = Nat.choose (j + m + 1) (j + 1 + i) * (m - i) := by
    have h1 := Nat.add_one_mul_choose_eq (j + m) (j + 1 + i)
    have h2 := Nat.choose_succ_right_eq (j + m + 1) (j + 1 + i)
    have h3 : (j + m + 1) - (j + 1 + i) = m - i := by omega
    rw [h3] at h2
    omega
  have hB : ((j + m + 1 : ℕ) : ℝ) * (Nat.choose (j + m) (j + 1 + i) : ℝ)
      = (Nat.choose (j + m + 1) (j + 1 + i) : ℝ) * ((m - i : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hBnat
  have h1 : HasDerivAt (fun y : ℝ => y ^ (j + 1 + i)) ((j + 1 + i : ℕ) * x ^ (j + i)) x := by
    simpa using hasDerivAt_pow (j + 1 + i) x
  have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ (m - i))
      (((m - i : ℕ) * (1 - x) ^ (m - i - 1)) * (-1)) x := by
    have hbase : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    exact hbase.pow (m - i)
  have hd := (h1.const_mul ((Nat.choose (j + m + 1) (j + 1 + i) : ℝ))).mul h2
  unfold binomTailTerm
  convert hd using 1
  simp only [binomTailAux]
  have e1 : j + (i + 1) = j + i + 1 := by omega
  have e2 : m - (i + 1) = m - i - 1 := by omega
  have e3 : j + 1 + i = j + i + 1 := by omega
  rw [e1, e2, e3]
  rw [e3] at hB
  linear_combination (x ^ (j + i) * (1 - x) ^ (m - i)) * hA
    - (x ^ (j + i + 1) * (1 - x) ^ (m - i - 1)) * hB

/-- **The derivative of the binomial tail**:
`d/dx ∑_{i>j} C(n,i)x^i(1−x)^{n−i} = n·C(n−1,j)·x^j(1−x)^m`. -/
theorem binomTail_hasDerivAt (j m : ℕ) (x : ℝ) :
    HasDerivAt (binomTail j m)
      ((j + m + 1 : ℕ) * (Nat.choose (j + m) j : ℝ) * x ^ j * (1 - x) ^ m) x := by
  have hsum := HasDerivAt.sum (fun i (hi : i ∈ Finset.range (m + 1)) =>
      binomTailTerm_hasDerivAt j m i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) x)
  have hfe : (∑ i ∈ Finset.range (m + 1), binomTailTerm j m i) = binomTail j m := by
    funext y
    simp [binomTail, Finset.sum_apply]
  rw [hfe] at hsum
  have htel : (∑ i ∈ Finset.range (m + 1),
      ((j + m + 1 : ℕ) * (binomTailAux j m x i - binomTailAux j m x (i + 1))))
      = (j + m + 1 : ℕ) * (binomTailAux j m x 0 - binomTailAux j m x (m + 1)) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub' (binomTailAux j m x) (m + 1)]
  have hzero : binomTailAux j m x (m + 1) = 0 := by
    simp only [binomTailAux]
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hstart : binomTailAux j m x 0 = (Nat.choose (j + m) j : ℝ) * x ^ j * (1 - x) ^ m := by
    simp [binomTailAux]
  rw [htel, hzero, hstart] at hsum
  convert hsum using 1
  ring

/-- At integer parameters the Euler integrand is a polynomial. -/
theorem betaIntegrand_nat (j m : ℕ) (t : ℝ) :
    betaIntegrand ((j : ℝ) + 1) ((m : ℝ) + 1) t = t ^ j * (1 - t) ^ m := by
  simp [betaIntegrand, Real.rpow_natCast]

/-- **Fundamental theorem of calculus at integer parameters**: the incomplete
Beta function with parameters `j+1, m+1` is differentiable everywhere with
derivative `x^j(1−x)^m`. -/
theorem incompleteBetaFn_nat_hasDerivAt (j m : ℕ) (x : ℝ) :
    HasDerivAt (incompleteBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1)) (x ^ j * (1 - x) ^ m) x := by
  have hcont : Continuous (fun t : ℝ => t ^ j * (1 - t) ^ m) := by fun_prop
  have hfun : incompleteBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1)
      = fun u : ℝ => ∫ t in (0:ℝ)..u, t ^ j * (1 - t) ^ m := by
    funext u
    simp only [incompleteBetaFn]
    exact intervalIntegral.integral_congr (fun t _ => betaIntegrand_nat j m t)
  rw [hfun]
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 x)
    (hcont.stronglyMeasurableAtFilter volume (𝓝 x)) hcont.continuousAt

/-- `B(j+1, m+1)·(j+m+1)·C(j+m, j) = 1`. -/
theorem betaFn_nat_mul_choose (j m : ℕ) :
    betaFn ((j : ℝ) + 1) ((m : ℝ) + 1) * ((j + m + 1 : ℕ) * (Nat.choose (j + m) j : ℝ)) = 1 := by
  have hchoose : Nat.choose (j + m) j * Nat.factorial j * Nat.factorial m
      = Nat.factorial (j + m) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j m)
    simpa using h
  have hfact : Nat.factorial (j + m + 1) = (j + m + 1) * Nat.factorial (j + m) := rfl
  have hjm : (Nat.factorial (j + m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hj : (Nat.factorial j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hchooseR : (Nat.choose (j + m) j : ℝ) * (Nat.factorial j : ℝ) * (Nat.factorial m : ℝ)
      = (Nat.factorial (j + m) : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hchoose
  rw [betaFn_nat_succ j m, hfact]
  push_cast
  field_simp
  linarith [hchooseR]

/-- **The Beta–Binomial identity, unnormalised**: for every real `x`,
`B(x; j+1, m+1) = B(j+1,m+1) · ∑_{i=j+1}^{j+m+1} C(j+m+1,i) x^i (1−x)^{j+m+1−i}`. -/
theorem incompleteBetaFn_nat_eq (j m : ℕ) (x : ℝ) :
    incompleteBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1) x
      = betaFn ((j : ℝ) + 1) ((m : ℝ) + 1) * binomTail j m x := by
  set B : ℝ := betaFn ((j : ℝ) + 1) ((m : ℝ) + 1) with hB
  set D : ℝ → ℝ := fun y => incompleteBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1) y - B * binomTail j m y
    with hD
  have hderiv : ∀ y : ℝ, HasDerivAt D 0 y := by
    intro y
    have h1 := incompleteBetaFn_nat_hasDerivAt j m y
    have h2 := (binomTail_hasDerivAt j m y).const_mul B
    have hkey : B * ((j + m + 1 : ℕ) * (Nat.choose (j + m) j : ℝ) * y ^ j * (1 - y) ^ m)
        = y ^ j * (1 - y) ^ m := by
      have := betaFn_nat_mul_choose j m
      calc B * ((j + m + 1 : ℕ) * (Nat.choose (j + m) j : ℝ) * y ^ j * (1 - y) ^ m)
          = (B * ((j + m + 1 : ℕ) * (Nat.choose (j + m) j : ℝ))) * (y ^ j * (1 - y) ^ m) := by
            ring
        _ = y ^ j * (1 - y) ^ m := by rw [this, one_mul]
    rw [hkey] at h2
    simpa using h1.sub h2
  have hdiff : Differentiable ℝ D := fun y => (hderiv y).differentiableAt
  have hzero : ∀ y : ℝ, deriv D y = 0 := fun y => (hderiv y).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero x 0
  have hD0 : D 0 = 0 := by
    simp only [hD, incompleteBetaFn_zero, binomTail, binomTailTerm]
    rw [Finset.sum_eq_zero]
    · ring
    · intro i _
      rw [zero_pow (by omega)]
      ring
  rw [hD0] at hconst
  have : incompleteBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1) x - B * binomTail j m x = 0 := hconst
  linarith

/-- **The Beta–Binomial identity**: for every real `x`,
`I_x(j+1, m+1) = ∑_{i=j+1}^{j+m+1} C(j+m+1,i) x^i (1−x)^{j+m+1−i}`.

Read probabilistically with `n = j+m+1` and `x ∈ [0,1]`:
`P(Beta(j+1, m+1) ≤ x) = P(Binomial(n, x) ≥ j+1)`. -/
theorem regBetaFn_nat_eq (j m : ℕ) (x : ℝ) :
    regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1) x = binomTail j m x := by
  have hB : betaFn ((j : ℝ) + 1) ((m : ℝ) + 1) ≠ 0 :=
    (betaFn_pos (by positivity) (by positivity)).ne'
  rw [regBetaFn, incompleteBetaFn_nat_eq j m x, mul_comm, mul_div_assoc, div_self hB, mul_one]

/-- The binomial upper tail vanishes at `x = 0`. -/
theorem binomTail_zero (j m : ℕ) : binomTail j m 0 = 0 := by
  rw [← regBetaFn_nat_eq j m 0, regBetaFn_zero]

/-- The binomial upper tail equals `1` at `x = 1`: with success probability one
every one of the `j+m+1` trials succeeds, so at least `j+1` do. -/
theorem binomTail_one (j m : ℕ) : binomTail j m 1 = 1 := by
  rw [← regBetaFn_nat_eq j m 1, regBetaFn_one (by positivity) (by positivity)]

end SHSLib.Trigamma
