/-
# Pathwise small-noise expansion for additive noise (Gardiner §6.2, §6.2.1)

For additive noise the SDE (6.2.1) reads `dx = a(x)dt + ε dw`.  Written as the integral equation

  `x(t) = x(0) + ∫₀ᵗ a(x(s)) ds + ε (w(t) - w(0))`

it makes sense for **every continuous driving path** `w`, with no stochastic integral at all
(`Gardiner.SDE.IsPathSol`).  The perturbation hierarchy (6.2.10)–(6.2.11) becomes, pathwise,

  `x₀(t) = x(0) + ∫₀ᵗ a(x₀)`,   `x₁(t) = w(t) - w(0) + ∫₀ᵗ a'(x₀) x₁`,
  `xₙ(t) = ∫₀ᵗ aₙ(x₀, …, xₙ)  (n ≥ 2)`

(`Gardiner.SDE.IsHierarchy`), where `aₙ = Gardiner.SDE.snCoeff` is the coefficient of (6.2.5);
by (6.2.7) these are the linear equations (6.2.10b) `dxₙ = [-k(x₀)xₙ + Aₙ]dt` (+ `dw` for `n = 1`,
since `b₀ = 1` and `bₙ = 0` for `n ≥ 1`).

Main result (`Gardiner.SDE.pathwise_expansion`): **the expansion `x = Σ εⁿxₙ` with an explicit
remainder, uniformly on `[0, T]`**.  If `a` is one-sided Lipschitz,
`(a(u) - a(v))(u - v) ≤ L(u - v)²` (this covers every globally Lipschitz drift and also dissipative
polynomial drifts such as the cubic `-x³` of §6.2.4 with `L = 0`), has a derivative tower up to
order `N + 1` bounded by `M` near the deterministic path, and `|xₘ(t)| ≤ R` on `[0, T]`, then for
`|ε| ≤ 1` and `t ∈ [0, T]`

  `|x(t) - Σ_{n=0}^N εⁿ xₙ(t)| ≤ T e^{LT + 1/2} · 2M e^{(N+1)R} · |ε|^{N+1}`.

This is (6.2.25), `x(t) - Σ εʳxᵣ(t) ~ ε^{n+1}`, with an explicit constant.  The remainder
`yₙ = (x - Σ_{r≤n} εʳxᵣ)/ε^{n+1}` of (6.2.17) satisfies the pathwise version of (6.2.21)
(`Gardiner.SDE.remainder_eq`, where the `b̂ₙ dW` term vanishes because the noise is additive) and is
bounded uniformly in `ε` (`Gardiner.SDE.remainder_bounded`), which is the content of
(6.2.22)–(6.2.25).  `Gardiner.SDE.linearisation_error` is the case `N = 1` (6.2.13)–(6.2.14).

The noise cancels exactly in `x - Σ εⁿxₙ`, so the error is a `C¹` function and the proof is an
energy estimate (`Gardiner.SDE.energy_bound`) plus the algebraic remainder
`Gardiner.SDE.expansion_remainder`.
-/
import SHSLib.Gardiner.SDE.Expansion

open Set Finset MeasureTheory intervalIntegral Polynomial
open scoped Nat Topology

noncomputable section

namespace Gardiner.SDE

/-! ### The energy estimate -/

/-- **Energy estimate.**  If `e(0) = 0`, `e' = g + d` with `g e ≤ L e²` (one-sided Lipschitz
part) and `|d| ≤ δ` on `[0, T]`, then `|e(t)| ≤ T δ e^{LT + 1/2}` on `[0, T]`. -/
theorem energy_bound {e g d : ℝ → ℝ} {L δ T : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (he : ∀ t, HasDerivAt e (g t + d t) t) (h0 : e 0 = 0)
    (hg : ∀ t ∈ Icc 0 T, g t * e t ≤ L * e t ^ 2) (hd : ∀ t ∈ Icc 0 T, |d t| ≤ δ) :
    ∀ t ∈ Icc 0 T, |e t| ≤ T * δ * Real.exp (L * T + 1 / 2) := by
  set K : ℝ := 2 * L + 1 / T with hK
  have hKpos : 0 < K := by positivity
  have hu : ∀ t, HasDerivAt (fun s => e s ^ 2) (2 * e t * (g t + d t)) t := by
    intro t
    have := (he t).pow 2
    convert this using 1; push_cast; ring
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, 2 * e t * (g t + d t) ≤ K * e t ^ 2 + T * δ ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
    have h1 := hg t ht'
    have h2 : e t * d t ≤ |e t| * δ := by
      calc e t * d t ≤ |e t * d t| := le_abs_self _
        _ = |e t| * |d t| := abs_mul _ _
        _ ≤ |e t| * δ := mul_le_mul_of_nonneg_left (hd t ht') (abs_nonneg _)
    have h3 : 2 * (|e t| * δ) ≤ e t ^ 2 / T + T * δ ^ 2 := by
      rw [div_add' _ _ _ hT.ne', le_div_iff₀ hT]
      nlinarith [sq_nonneg (|e t| - T * δ), sq_abs (e t)]
    have : K * e t ^ 2 = 2 * L * e t ^ 2 + e t ^ 2 / T := by rw [hK]; ring
    rw [this]
    nlinarith
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => e s ^ 2)
    (f' := fun t => 2 * e t * (g t + d t)) (δ := 0) (K := K) (ε := T * δ ^ 2) (a := 0) (b := T)
    (fun t _ => ((hu t).continuousAt).continuousWithinAt)
    (fun t _ r hr => (hu t).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [h0]) hbound
  intro t ht
  have h := hgr t ht
  rw [gronwallBound_of_K_ne_0 hKpos.ne', sub_zero] at h
  simp only [zero_mul, zero_add] at h
  -- `(e^{Kt} - 1)/K ≤ t e^{Kt} ≤ T e^{KT}`
  have hexp : (Real.exp (K * t) - 1) / K ≤ T * Real.exp (K * T) := by
    rw [div_le_iff₀ hKpos]
    have h1 : 1 - K * t ≤ Real.exp (-(K * t)) := by
      have := Real.add_one_le_exp (-(K * t)); linarith
    have h2 : Real.exp (K * t) - 1 ≤ K * t * Real.exp (K * t) := by
      have h3 : Real.exp (-(K * t)) * Real.exp (K * t) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (K * t)]
    have h4 : Real.exp (K * t) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hKpos.le)
    calc Real.exp (K * t) - 1 ≤ K * t * Real.exp (K * t) := h2
      _ ≤ K * T * Real.exp (K * T) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left ht.2 hKpos.le) h4 (Real.exp_pos _).le
        positivity
      _ = T * Real.exp (K * T) * K := by ring
  have hsq : e t ^ 2 ≤ (T * δ * Real.exp (L * T + 1 / 2)) ^ 2 := by
    have hKT : K * T = 2 * (L * T + 1 / 2) := by rw [hK]; field_simp
    calc e t ^ 2 ≤ T * δ ^ 2 / K * (Real.exp (K * t) - 1) := h
      _ = T * δ ^ 2 * ((Real.exp (K * t) - 1) / K) := by ring
      _ ≤ T * δ ^ 2 * (T * Real.exp (K * T)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (T * δ * Real.exp (L * T + 1 / 2)) ^ 2 := by
          rw [hKT, mul_pow, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hpos : 0 ≤ T * δ * Real.exp (L * T + 1 / 2) := by positivity
  rw [← sq_abs] at hsq
  exact (sq_le_sq₀ (abs_nonneg _) hpos).mp hsq

/-! ### Continuity of the coefficients `aₙ` along continuous paths -/

lemma continuous_coeff_pow {F : ℝ → ℝ[X]} (hF : ∀ k, Continuous fun s => (F s).coeff k) (p : ℕ) :
    ∀ k, Continuous fun s => (F s ^ p).coeff k := by
  induction p with
  | zero => intro k; simp only [pow_zero, coeff_one]; exact continuous_const
  | succ p ih =>
    intro k
    simp only [pow_succ, Polynomial.coeff_mul]
    exact continuous_finset_sum _ fun x _ => (ih _).mul (hF _)

/-- Along continuous paths `s ↦ D(s)`, `s ↦ X(s)`, the coefficient `aₙ(s)` is continuous. -/
lemma continuous_snCoeff {D X : ℝ → ℕ → ℝ} (hD : ∀ p, Continuous fun s => D s p)
    (hX : ∀ m, Continuous fun s => X s m) (n : ℕ) :
    Continuous fun s => snCoeff (D s) (X s) n := by
  unfold snCoeff compPoly
  simp only [finset_sum_coeff, coeff_C_mul]
  refine continuous_finset_sum _ fun p _ => ((hD p).div_const _).mul ?_
  refine continuous_coeff_pow (fun k => ?_) p n
  simp only [pertPoly_coeff]
  split_ifs
  · exact hX k
  · exact continuous_const

/-! ### Pathwise solutions and the pathwise hierarchy -/

/-- A pathwise solution of `dx = a(x)dt + ε dw` on `[0, T]` (additive noise, (6.2.1) with
`b ≡ 1`), driven by an arbitrary continuous path `w`. -/
structure IsPathSol (a : ℝ → ℝ) (ε : ℝ) (w x : ℝ → ℝ) (T : ℝ) : Prop where
  cont : Continuous x
  eq : ∀ t ∈ Icc 0 T, x t = x 0 + (∫ s in (0 : ℝ)..t, a (x s)) + ε * (w t - w 0)

/-- The drift of the `n`-th equation of the hierarchy, `aₙ(x₀(s), …, xₙ(s))`, for a derivative
tower `Da` of `a` (`Da p = a⁽ᵖ⁾`). -/
def hierDrift (Da : ℕ → ℝ → ℝ) (xs : ℕ → ℝ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  snCoeff (fun p => Da p (xs 0 s)) (fun m => xs m s) n

/-- (6.2.10)–(6.2.11), pathwise, for additive noise: `x₀` solves the deterministic equation with
`x₀(0) = x(0)`, `x₁` is driven by `w`, and `xₙ(0) = 0` for `n ≥ 1`; only the equations of order
`n ≤ N` are required (the functions `xₙ`, `n > N`, are unconstrained continuous functions). -/
structure IsHierarchy (Da : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (x0 : ℝ) (xs : ℕ → ℝ → ℝ) (N : ℕ) (T : ℝ) :
    Prop where
  cont : ∀ n, Continuous (xs n)
  eq : ∀ n ≤ N, ∀ t ∈ Icc 0 T, xs n t = (if n = 0 then x0 else 0) +
    (if n = 1 then w t - w 0 else 0) + ∫ s in (0 : ℝ)..t, hierDrift Da xs n s

/-- The drift of the `n = 0` equation is `a(x₀)`. -/
lemma hierDrift_zero (Da : ℕ → ℝ → ℝ) (xs : ℕ → ℝ → ℝ) (s : ℝ) :
    hierDrift Da xs 0 s = Da 0 (xs 0 s) := snCoeff_zero _ _

/-- The drift of the `n = 1` equation is `a'(x₀) x₁ = -k(x₀) x₁` (6.2.9), (6.2.13). -/
lemma hierDrift_one (Da : ℕ → ℝ → ℝ) (xs : ℕ → ℝ → ℝ) (s : ℝ) :
    hierDrift Da xs 1 s = xs 1 s * Da 1 (xs 0 s) := snCoeff_one _ _

/-- (6.2.10b): for `n ≥ 1` the drift is `xₙ a'(x₀) + Aₙ(x₀, …, xₙ₋₁)`. -/
lemma hierDrift_split (Da : ℕ → ℝ → ℝ) (xs : ℕ → ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) (s : ℝ) :
    hierDrift Da xs n s = xs n s * Da 1 (xs 0 s) +
      snA (fun p => Da p (xs 0 s)) (fun m => xs m s) n := snCoeff_split _ _ hn

lemma sum_range_succ_eq_add_Icc (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range (N + 1), f n = f 0 + ∑ m ∈ Icc 1 N, f m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]; ring

/-- The partial sum `Σ_{n≤N} εⁿxₙ(t)`. -/
def partialSum (xs : ℕ → ℝ → ℝ) (ε : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ range (N + 1), ε ^ n * xs n t

/-- The integrated form of the partial sum: `Σ εⁿxₙ = x(0) + ε(w - w(0)) + ∫ Σ εⁿaₙ`
(for `N ≥ 1`). -/
lemma partialSum_eq {Da : ℕ → ℝ → ℝ} {w : ℝ → ℝ} {x0 : ℝ} {xs : ℕ → ℝ → ℝ} {N : ℕ} {T : ℝ}
    (hH : IsHierarchy Da w x0 xs N T) (hDc : ∀ p, Continuous (Da p)) (hN : 1 ≤ N)
    (ε : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    partialSum xs ε N t = x0 + ε * (w t - w 0) +
      ∫ s in (0 : ℝ)..t, ∑ n ∈ range (N + 1), ε ^ n * hierDrift Da xs n s := by
  have hcont : ∀ n, Continuous (hierDrift Da xs n) := fun n =>
    continuous_snCoeff (fun p => (hDc p).comp (hH.cont 0)) (fun m => hH.cont m) n
  rw [intervalIntegral.integral_finset_sum (f := fun n s => ε ^ n * hierDrift Da xs n s)
    (fun n _ => (continuous_const.mul (hcont n)).intervalIntegrable 0 t)]
  simp only [intervalIntegral.integral_const_mul, partialSum]
  rw [Finset.sum_congr rfl fun n hn => by rw [hH.eq n (by simp at hn; omega) t ht]]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single 1 (fun b _ hb => by simp [hb]) (by simp; omega)]
  simp

/-! ### The main theorem -/

/-- **Pathwise small-noise expansion with explicit remainder (additive noise).**

Let `Da` be a derivative tower for the drift `a = Da 0` up to order `N + 1` (`N ≥ 1`), let `a` be
one-sided Lipschitz with constant `L ≥ 0`, let `x` be a pathwise solution of
`dx = a(x)dt + ε dw` on `[0, T]` and `xs` the pathwise hierarchy (6.2.10)–(6.2.11) with
`x₀(0) = x(0)`.  If `|xₘ(t)| ≤ R` for `1 ≤ m ≤ N` and the derivatives of order `≤ N + 1` are bounded
by `M` within distance `(N + 1)R` of the deterministic path, then for `|ε| ≤ 1`

  `|x(t) - Σ_{n=0}^N εⁿ xₙ(t)| ≤ T e^{LT + 1/2} · 2M e^{(N+1)R} · |ε|^{N+1}`   on `[0, T]`. -/
theorem pathwise_expansion (N : ℕ) (hN : 1 ≤ N) (Da : ℕ → ℝ → ℝ)
    (hDa : ∀ k ≤ N, ∀ y, HasDerivAt (Da k) (Da (k + 1) y) y)
    (hDc : ∀ p, Continuous (Da p))
    {L : ℝ} (hL : 0 ≤ L) (hosl : ∀ u v, (Da 0 u - Da 0 v) * (u - v) ≤ L * (u - v) ^ 2)
    {ε T R M : ℝ} (hε : |ε| ≤ 1) (hT : 0 < T) (hR : 0 ≤ R)
    {w x : ℝ → ℝ} (hx : IsPathSol (Da 0) ε w x T)
    {xs : ℕ → ℝ → ℝ} (hH : IsHierarchy Da w (x 0) xs N T)
    (hxR : ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Icc 0 T, |xs m t| ≤ R)
    (hM : ∀ p ≤ N + 1, ∀ t ∈ Icc 0 T, ∀ z, |z - xs 0 t| ≤ (N + 1) * R → |Da p z| ≤ M) :
    ∀ t ∈ Icc 0 T, |x t - partialSum xs ε N t| ≤
      T * Real.exp (L * T + 1 / 2) * (2 * M * Real.exp ((N + 1) * R)) * |ε| ^ (N + 1) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans
    (hM 0 (by omega) 0 (by simp; exact hT.le) (xs 0 0) (by simp; positivity))
  have hcont : ∀ n, Continuous (hierDrift Da xs n) := fun n =>
    continuous_snCoeff (fun p => (hDc p).comp (hH.cont 0)) (fun m => hH.cont m) n
  set sumA : ℝ → ℝ := fun s => ∑ n ∈ range (N + 1), ε ^ n * hierDrift Da xs n s
  have hsumAc : Continuous sumA := continuous_finset_sum _ fun n _ => continuous_const.mul (hcont n)
  set S := partialSum xs ε N
  have hSc : Continuous S :=
    continuous_finset_sum _ fun n _ => continuous_const.mul (hH.cont n)
  -- the error, written as an integral (the noise cancels)
  set e : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, (Da 0 (x s) - sumA s)
  have hgc : Continuous fun s => Da 0 (x s) - sumA s := ((hDc 0).comp hx.cont).sub hsumAc
  have hee : ∀ t ∈ Icc 0 T, x t - S t = e t := by
    intro t ht
    rw [hx.eq t ht]
    simp only [S, e]
    rw [partialSum_eq hH hDc hN ε ht, intervalIntegral.integral_sub (f := fun s => Da 0 (x s))
      (g := sumA) (((hDc 0).comp hx.cont).intervalIntegrable 0 t) (hsumAc.intervalIntegrable 0 t)]
    ring
  have hderiv : ∀ t, HasDerivAt e ((Da 0 (x t) - Da 0 (S t)) + (Da 0 (S t) - sumA t)) t := by
    intro t
    have := intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 t)
      hgc.aestronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
    convert this using 1; ring
  -- the defect is the algebraic remainder of (6.2.19)
  have hdef : ∀ t ∈ Icc 0 T, |Da 0 (S t) - sumA t| ≤ 2 * M * Real.exp ((N + 1) * R) * |ε| ^ (N + 1) := by
    intro t ht
    have h := expansion_remainder N Da hDa (fun m => xs m t) 0 hε (fun m h1 h2 => hxR m h1 h2 t ht)
      (by simpa using hR) (fun p hp z hz => hM p hp t ht z hz)
    simp only [zero_mul, add_zero] at h
    have hS : S t = xs 0 t + ∑ m ∈ Icc 1 N, xs m t * ε ^ m := by
      simp only [S, partialSum]
      rw [sum_range_succ_eq_add_Icc]
      simp only [pow_zero, one_mul]
      congr 1
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    rw [hS]
    convert h using 3
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have hbound := energy_bound (e := e) (g := fun t => Da 0 (x t) - Da 0 (S t))
    (d := fun t => Da 0 (S t) - sumA t) hT hL (by positivity) hderiv (by simp [e])
    (fun t ht => by
      rw [← hee t ht]
      exact hosl _ _) hdef
  intro t ht
  rw [hee t ht]
  calc |e t| ≤ T * (2 * M * Real.exp ((N + 1) * R) * |ε| ^ (N + 1)) * Real.exp (L * T + 1 / 2) :=
        hbound t ht
    _ = _ := by ring

/-- (6.2.17), (6.2.24)–(6.2.25): the scaled remainder `yₙ(ε, t) = (x(t) - Σ_{r≤n} εʳxᵣ(t))/ε^{n+1}`
is bounded uniformly in `0 < |ε| ≤ 1` and `t ∈ [0, T]`, i.e. the expansion is asymptotic. -/
theorem remainder_bounded (N : ℕ) (hN : 1 ≤ N) (Da : ℕ → ℝ → ℝ)
    (hDa : ∀ k ≤ N, ∀ y, HasDerivAt (Da k) (Da (k + 1) y) y)
    (hDc : ∀ p, Continuous (Da p))
    {L : ℝ} (hL : 0 ≤ L) (hosl : ∀ u v, (Da 0 u - Da 0 v) * (u - v) ≤ L * (u - v) ^ 2)
    {ε T R M : ℝ} (hε0 : ε ≠ 0) (hε : |ε| ≤ 1) (hT : 0 < T) (hR : 0 ≤ R)
    {w x : ℝ → ℝ} (hx : IsPathSol (Da 0) ε w x T)
    {xs : ℕ → ℝ → ℝ} (hH : IsHierarchy Da w (x 0) xs N T)
    (hxR : ∀ m, 1 ≤ m → m ≤ N → ∀ t ∈ Icc 0 T, |xs m t| ≤ R)
    (hM : ∀ p ≤ N + 1, ∀ t ∈ Icc 0 T, ∀ z, |z - xs 0 t| ≤ (N + 1) * R → |Da p z| ≤ M) :
    ∀ t ∈ Icc 0 T, |(x t - partialSum xs ε N t) / ε ^ (N + 1)| ≤
      T * Real.exp (L * T + 1 / 2) * (2 * M * Real.exp ((N + 1) * R)) := by
  intro t ht
  have h := pathwise_expansion N hN Da hDa hDc hL hosl hε hT hR hx hH hxR hM t ht
  have hpos : 0 < |ε| ^ (N + 1) := by positivity
  rw [abs_div, abs_pow, div_le_iff₀ hpos]
  exact h

/-- (6.2.19): Gardiner's `â_{n+1}[X₀, …, Xₙ, Y, ε]`, for the drift tower `Da`. -/
def aHat (Da : ℕ → ℝ → ℝ) (N : ℕ) (X : ℕ → ℝ) (Y ε : ℝ) : ℝ :=
  (Da 0 (X 0 + ∑ m ∈ Icc 1 N, X m * ε ^ m + Y * ε ^ (N + 1)) -
    ∑ n ∈ range (N + 1), snCoeff (fun p => Da p (X 0)) X n * ε ^ n) / ε ^ (N + 1)

/-- (6.2.20), uniformly on bounded sets: `|â_{N+1}| ≤ 2M e^{(N+1)R}` for `0 < |ε| ≤ 1`. -/
theorem aHat_bounded (N : ℕ) (Da : ℕ → ℝ → ℝ)
    (hDa : ∀ k ≤ N, ∀ y, HasDerivAt (Da k) (Da (k + 1) y) y)
    (X : ℕ → ℝ) (Y : ℝ) {R M ε : ℝ} (hε0 : ε ≠ 0) (hε : |ε| ≤ 1)
    (hX : ∀ m, 1 ≤ m → m ≤ N → |X m| ≤ R) (hY : |Y| ≤ R)
    (hM : ∀ p ≤ N + 1, ∀ z, |z - X 0| ≤ (N + 1) * R → |Da p z| ≤ M) :
    |aHat Da N X Y ε| ≤ 2 * M * Real.exp ((N + 1) * R) := by
  have h := expansion_remainder N Da hDa X Y hε hX hY hM
  have hpos : 0 < |ε| ^ (N + 1) := by positivity
  rw [aHat, abs_div, abs_pow, div_le_iff₀ hpos]
  exact h

/-- (6.2.21), pathwise for additive noise: the remainder `yₙ` of (6.2.17) satisfies
`yₙ(t) = ∫₀ᵗ â_{n+1}[x₀(s), …, xₙ(s), yₙ(s), ε] ds`; the `b̂ₙ dW` term of (6.2.21) vanishes since
`b ≡ 1` has `b₀ = 1` and `bᵣ = 0` for `r ≥ 1`. -/
theorem remainder_eq (N : ℕ) (hN : 1 ≤ N) (Da : ℕ → ℝ → ℝ) (hDc : ∀ p, Continuous (Da p))
    {ε T : ℝ} (hε0 : ε ≠ 0) {w x : ℝ → ℝ} (hx : IsPathSol (Da 0) ε w x T)
    {xs : ℕ → ℝ → ℝ} (hH : IsHierarchy Da w (x 0) xs N T) :
    ∀ t ∈ Icc 0 T, (x t - partialSum xs ε N t) / ε ^ (N + 1) =
      ∫ s in (0 : ℝ)..t, aHat Da N (fun m => xs m s)
        ((x s - partialSum xs ε N s) / ε ^ (N + 1)) ε := by
  have hcont : ∀ n, Continuous (hierDrift Da xs n) := fun n =>
    continuous_snCoeff (fun p => (hDc p).comp (hH.cont 0)) (fun m => hH.cont m) n
  set sumA : ℝ → ℝ := fun s => ∑ n ∈ range (N + 1), ε ^ n * hierDrift Da xs n s
  have hsumAc : Continuous sumA := continuous_finset_sum _ fun n _ => continuous_const.mul (hcont n)
  have hpe : ε ^ (N + 1) ≠ 0 := pow_ne_zero _ hε0
  intro t ht
  -- rewrite the integrand on `[0, t]`
  have hint : ∀ s ∈ uIcc 0 t, aHat Da N (fun m => xs m s)
      ((x s - partialSum xs ε N s) / ε ^ (N + 1)) ε = (Da 0 (x s) - sumA s) / ε ^ (N + 1) := by
    intro s _
    simp only [aHat]
    congr 1
    have hS : xs 0 s + ∑ m ∈ Icc 1 N, xs m s * ε ^ m = partialSum xs ε N s := by
      simp only [partialSum]
      rw [sum_range_succ_eq_add_Icc]
      simp only [pow_zero, one_mul]
      congr 1
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    have hx' : xs 0 s + ∑ m ∈ Icc 1 N, xs m s * ε ^ m +
        (x s - partialSum xs ε N s) / ε ^ (N + 1) * ε ^ (N + 1) = x s := by
      rw [div_mul_cancel₀ _ hpe, hS]; ring
    rw [hx']
    simp only [sumA, hierDrift]
    congr 1
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [intervalIntegral.integral_congr hint, intervalIntegral.integral_div,
    hx.eq t ht, partialSum_eq hH hDc hN ε ht, intervalIntegral.integral_sub
      (f := fun s => Da 0 (x s)) (g := sumA)
      (((hDc 0).comp hx.cont).intervalIntegrable 0 t) (hsumAc.intervalIntegrable 0 t)]
  congr 1
  ring

/-- (6.2.13)–(6.2.14), pathwise: **the linearisation error**.  With `x₀` the deterministic
solution and `x₁ = w - w(0) + ∫ a'(x₀) x₁` the (pathwise) time-dependent Ornstein–Uhlenbeck
correction, `|x - x₀ - εx₁| ≤ T e^{LT + 1/2} · 2M e^{2R} ε²` on `[0, T]`. -/
theorem linearisation_error (Da : ℕ → ℝ → ℝ)
    (hDa : ∀ k ≤ 1, ∀ y, HasDerivAt (Da k) (Da (k + 1) y) y) (hDc : ∀ p, Continuous (Da p))
    {L : ℝ} (hL : 0 ≤ L) (hosl : ∀ u v, (Da 0 u - Da 0 v) * (u - v) ≤ L * (u - v) ^ 2)
    {ε T R M : ℝ} (hε : |ε| ≤ 1) (hT : 0 < T) (hR : 0 ≤ R)
    {w x : ℝ → ℝ} (hx : IsPathSol (Da 0) ε w x T)
    {xs : ℕ → ℝ → ℝ} (hH : IsHierarchy Da w (x 0) xs 1 T)
    (hxR : ∀ t ∈ Icc 0 T, |xs 1 t| ≤ R)
    (hM : ∀ p ≤ 2, ∀ t ∈ Icc 0 T, ∀ z, |z - xs 0 t| ≤ 2 * R → |Da p z| ≤ M) :
    ∀ t ∈ Icc 0 T, |x t - (xs 0 t + ε * xs 1 t)| ≤
      T * Real.exp (L * T + 1 / 2) * (2 * M * Real.exp (2 * R)) * ε ^ 2 := by
  intro t ht
  have h := pathwise_expansion 1 le_rfl Da hDa hDc hL hosl hε hT hR hx hH
    (fun m h1 h2 t ht => by
      obtain rfl : m = 1 := by omega
      exact hxR t ht)
    (fun p hp t ht z hz => hM p hp t ht z (by norm_num at hz ⊢; linarith)) t ht
  simp only [partialSum, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
    one_mul, zero_add, pow_one] at h
  norm_num at h
  exact h

end Gardiner.SDE
