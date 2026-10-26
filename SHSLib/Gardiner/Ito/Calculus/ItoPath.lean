/-
# The pathwise core of Itô's formula

`Gardiner.Ito.IsC12.ito_pathwise` is a purely deterministic statement.  Let
`X(t) = X₀ + ∫₀ᵗ a(s) ds + b w(t)` with `a`, `w` continuous.  Suppose that along a subsequence of
uniform partitions of `[0, T]`

* `Σᵢ F_x(tᵢ, Xᵢ) Δwᵢ → I`,
* `Σᵢ F_xx(tᵢ, Xᵢ)(Δwᵢ² - Δt) → 0`  (weighted quadratic variation), and
* `Σᵢ Δwᵢ² → T`  (quadratic variation).

Then `F(T, X_T) - F(0, X_0) = ∫₀ᵀ (F_t + a F_x + ½ b² F_xx)(s, X_s) ds + b I`.

For a Wiener path `w = W(·, ω)` the three hypotheses hold almost surely along a subsequence,
which gives Itô's formula (`Gardiner.Ito.IsFWiener.ito_formula`).
-/
import SHSLib.Gardiner.Ito.Calculus.Taylor

open Filter Topology Set MeasureTheory

noncomputable section

namespace Gardiner.Ito

/-- The increment `w(tᵢ₊₁) - w(tᵢ)` of a path over the `i`-th cell of the uniform partition. -/
def gridIncr (w : ℝ → ℝ) (T : ℝ) (n i : ℕ) : ℝ := w (gridPt T n (i + 1)) - w (gridPt T n i)

lemma two_abs_mul_le_sqrt {u h : ℝ} (hh : 0 ≤ h) :
    2 * |u| * h ≤ Real.sqrt h * (u ^ 2 + h) := by
  have hs := Real.sq_sqrt hh
  have hs0 := Real.sqrt_nonneg h
  have h1 : 2 * |u| * Real.sqrt h ≤ u ^ 2 + h := by
    nlinarith [sq_nonneg (|u| - Real.sqrt h), sq_abs u]
  calc 2 * |u| * h = (2 * |u| * Real.sqrt h) * Real.sqrt h := by
        rw [mul_assoc (2 * |u|), ← sq, hs]
    _ ≤ (u ^ 2 + h) * Real.sqrt h := mul_le_mul_of_nonneg_right h1 hs0
    _ = _ := by ring

lemma integral_cell_bound {a : ℝ → ℝ} {T A : ℝ} (hT : 0 ≤ T) (hA : ∀ s ∈ Icc 0 T, |a s| ≤ A)
    {n i : ℕ} (hi : i ≤ n) :
    |∫ s in gridPt T n i..gridPt T n (i + 1), a s| ≤ A * (T / (n + 1)) := by
  have hab := gridPt_succ T n i
  have h0 := gridPt_nonneg hT n i
  have hbT := gridPt_le hT (show i + 1 ≤ n + 1 by omega)
  have hh0 : 0 ≤ T / ((n : ℝ) + 1) := by positivity
  have := intervalIntegral.norm_integral_le_of_norm_le_const (C := A) (a := gridPt T n i)
    (b := gridPt T n (i + 1)) (f := a) (fun s hs => by
      rw [Set.uIoc_of_le (by linarith)] at hs
      rw [Real.norm_eq_abs]; exact hA s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hba : |gridPt T n (i + 1) - gridPt T n i| = T / (n + 1) := by
    rw [hab, add_sub_cancel_left, abs_of_nonneg hh0]
  rw [Real.norm_eq_abs, hba] at this
  exact this

variable {F Ft Fx Fxx : ℝ → ℝ → ℝ}

/-- **Pathwise Itô formula** (deterministic core). -/
theorem IsC12.ito_pathwise (hF : IsC12 F Ft Fx Fxx) {T : ℝ} (hT : 0 < T) {X a w : ℝ → ℝ}
    {X0 b I : ℝ} (ha : Continuous a) (hw : Continuous w)
    (hX : ∀ t, X t = X0 + (∫ s in (0 : ℝ)..t, a s) + b * w t) {ns : ℕ → ℕ} (hns : StrictMono ns)
    (h1 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1),
      Fx (gridPt T (ns k) i) (X (gridPt T (ns k) i)) * gridIncr w T (ns k) i) atTop (𝓝 I))
    (h2 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1),
      Fxx (gridPt T (ns k) i) (X (gridPt T (ns k) i)) *
        (gridIncr w T (ns k) i ^ 2 - T / (ns k + 1))) atTop (𝓝 0))
    (h3 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1), gridIncr w T (ns k) i ^ 2) atTop
      (𝓝 T)) :
    F T (X T) - F 0 (X 0) =
      (∫ s in (0 : ℝ)..T, (Ft s (X s) + a s * Fx s (X s) + b ^ 2 / 2 * Fxx s (X s))) + b * I := by
  have hXc : Continuous X := by
    have : X = fun t => X0 + (∫ s in (0 : ℝ)..t, a s) + b * w t := funext hX
    rw [this]
    exact (continuous_const.add (intervalIntegral.continuous_primitive
      (fun _ _ => ha.intervalIntegrable _ _) 0)).add (continuous_const.mul hw)
  have hFtc : Continuous fun s => Ft s (X s) := hF.cont_Ft.comp (continuous_id.prodMk hXc)
  have hFxc : Continuous fun s => Fx s (X s) := hF.cont_Fx.comp (continuous_id.prodMk hXc)
  have hFxxc : Continuous fun s => Fxx s (X s) := hF.cont_Fxx.comp (continuous_id.prodMk hXc)
  -- notation
  set α : ℕ → ℕ → ℝ := fun n i => ∫ s in gridPt T n i..gridPt T n (i + 1), a s with hα
  set dX : ℕ → ℕ → ℝ := fun n i => X (gridPt T n (i + 1)) - X (gridPt T n i) with hdXdef
  have hdX : ∀ n i, dX n i = α n i + b * gridIncr w T n i := by
    intro n i
    have e := intervalIntegral.integral_interval_sub_left
      (ha.intervalIntegrable (μ := volume) 0 (gridPt T n (i + 1)))
      (ha.intervalIntegrable (μ := volume) 0 (gridPt T n i))
    simp only [dX, α, gridIncr, hX]
    rw [← e]
    ring
  set D : ℕ → ℝ := fun n => F T (X T) - F 0 (X 0) - ∑ i ∈ Finset.range (n + 1),
    (Ft (gridPt T n i) (X (gridPt T n i)) * (T / (n + 1)) +
      Fx (gridPt T n i) (X (gridPt T n i)) * (X (gridPt T n (i + 1)) - X (gridPt T n i)) +
      Fxx (gridPt T n i) (X (gridPt T n i)) / 2 * (X (gridPt T n (i + 1)) - X (gridPt T n i)) ^ 2)
    with hD
  set St : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Ft (gridPt T n i) (X (gridPt T n i)) * (T / (n + 1)) with hSt
  set Sa : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Fx (gridPt T n i) (X (gridPt T n i)) * α n i with hSa
  set S1 : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Fx (gridPt T n i) (X (gridPt T n i)) * gridIncr w T n i with hS1
  set S2 : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Fxx (gridPt T n i) (X (gridPt T n i)) * (gridIncr w T n i ^ 2 - T / (n + 1)) with hS2
  set Sxx : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Fxx (gridPt T n i) (X (gridPt T n i)) * (T / (n + 1)) with hSxx
  set R : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Fxx (gridPt T n i) (X (gridPt T n i)) / 2 *
      (2 * b * α n i * gridIncr w T n i + α n i ^ 2) with hR
  have key : ∀ n, F T (X T) - F 0 (X 0) =
      D n + (St n + Sa n + b * S1 n + b ^ 2 / 2 * S2 n + b ^ 2 / 2 * Sxx n + R n) := by
    intro n
    have : ∑ i ∈ Finset.range (n + 1),
        (Ft (gridPt T n i) (X (gridPt T n i)) * (T / (n + 1)) +
          Fx (gridPt T n i) (X (gridPt T n i)) * (X (gridPt T n (i + 1)) - X (gridPt T n i)) +
          Fxx (gridPt T n i) (X (gridPt T n i)) / 2 *
            (X (gridPt T n (i + 1)) - X (gridPt T n i)) ^ 2) =
        St n + Sa n + b * S1 n + b ^ 2 / 2 * S2 n + b ^ 2 / 2 * Sxx n + R n := by
      simp only [hSt, hSa, hS1, hS2, hSxx, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hdX n i
      simp only [dX] at this
      rw [this]; ring
    simp only [hD]; rw [this]; ring
  -- bounds
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    ha.continuousOn
  have hA' : ∀ s ∈ Icc 0 T, |a s| ≤ A := fun s hs => by
    have := hA s hs; rwa [Real.norm_eq_abs] at this
  obtain ⟨Mx, hMx⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hFxxc.continuousOn
  have hMx' : ∀ s ∈ Icc 0 T, |Fxx s (X s)| ≤ Mx := fun s hs => by
    have := hMx s hs; rwa [Real.norm_eq_abs] at this
  have hαb : ∀ n i, i ≤ n → |α n i| ≤ A * (T / (n + 1)) :=
    fun n i hi => integral_cell_bound hT.le hA' hi
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA' 0 ⟨le_rfl, hT.le⟩)
  have hMx0 : 0 ≤ Mx := (abs_nonneg _).trans (hMx' 0 ⟨le_rfl, hT.le⟩)
  set Q : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), gridIncr w T n i ^ 2 with hQ
  have hstep : Tendsto (fun k => T / ((ns k : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T).comp hns.tendsto_atTop
    simp only [mul_zero] at this
    refine this.congr fun k => ?_
    simp [div_eq_mul_inv]
  -- R → 0
  have hRb : ∀ n, |R n| ≤ Mx / 2 * (|b| * A * Real.sqrt (T / (n + 1)) * (Q n + T) +
      A ^ 2 * T * (T / (n + 1))) := by
    intro n
    have hh0 : 0 ≤ T / ((n : ℝ) + 1) := by positivity
    have hcell : ∀ i ∈ Finset.range (n + 1), |Fxx (gridPt T n i) (X (gridPt T n i)) / 2 *
        (2 * b * α n i * gridIncr w T n i + α n i ^ 2)| ≤
        Mx / 2 * (|b| * A * Real.sqrt (T / (n + 1)) * (gridIncr w T n i ^ 2 + T / (n + 1)) +
          A ^ 2 * (T / (n + 1)) ^ 2) := by
      intro i hi
      have hin : i ≤ n := by simp at hi; omega
      have hti : gridPt T n i ∈ Icc 0 T :=
        ⟨gridPt_nonneg hT.le n i, gridPt_le hT.le (by omega)⟩
      have e1 := hMx' _ hti
      have e2 := hαb n i hin
      have e3 := two_abs_mul_le_sqrt (u := gridIncr w T n i) hh0
      rw [abs_mul, abs_div, abs_two]
      refine mul_le_mul (div_le_div_of_nonneg_right e1 zero_le_two) ?_ (abs_nonneg _)
        (by positivity)
      calc |2 * b * α n i * gridIncr w T n i + α n i ^ 2|
          ≤ |b| * |α n i| * (2 * |gridIncr w T n i|) + |α n i| ^ 2 := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_two, abs_pow]; ring
        _ ≤ |b| * (A * (T / (n + 1))) * (2 * |gridIncr w T n i|) + (A * (T / (n + 1))) ^ 2 := by
            gcongr
        _ = |b| * A * (2 * |gridIncr w T n i| * (T / (n + 1))) + A ^ 2 * (T / (n + 1)) ^ 2 := by
            ring
        _ ≤ |b| * A * (Real.sqrt (T / (n + 1)) * (gridIncr w T n i ^ 2 + T / (n + 1))) +
            A ^ 2 * (T / (n + 1)) ^ 2 := by gcongr
        _ = _ := by ring
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hcell).trans (le_of_eq ?_))
    simp only [hQ, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    field_simp
  have hR0 : Tendsto (fun k => R (ns k)) atTop (𝓝 0) := by
    have hB : Tendsto (fun k => Mx / 2 * (|b| * A * Real.sqrt (T / (ns k + 1)) * (Q (ns k) + T) +
        A ^ 2 * T * (T / (ns k + 1)))) atTop
        (𝓝 (Mx / 2 * (|b| * A * Real.sqrt 0 * (T + T) + A ^ 2 * T * 0))) := by
      refine tendsto_const_nhds.mul (((tendsto_const_nhds.mul
        ((Real.continuous_sqrt.tendsto 0).comp hstep)).mul (h3.add tendsto_const_nhds)).add
        (tendsto_const_nhds.mul hstep))
    simp only [Real.sqrt_zero, mul_zero, zero_mul, add_zero] at hB
    exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact hRb (ns k)) hB
  -- D → 0
  have hQx : ∀ n, ∑ i ∈ Finset.range (n + 1), (X (gridPt T n (i + 1)) - X (gridPt T n i)) ^ 2 ≤
      2 * A ^ 2 * T * (T / (n + 1)) + 2 * b ^ 2 * Q n := by
    intro n
    have hcell : ∀ i ∈ Finset.range (n + 1), (X (gridPt T n (i + 1)) - X (gridPt T n i)) ^ 2 ≤
        2 * A ^ 2 * (T / (n + 1)) ^ 2 + 2 * b ^ 2 * gridIncr w T n i ^ 2 := by
      intro i hi
      have hin : i ≤ n := by simp at hi; omega
      have e := hdX n i
      simp only [dX] at e
      rw [e]
      have e2 := hαb n i hin
      have e3 : α n i ^ 2 ≤ (A * (T / (n + 1))) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e2 2
      nlinarith [sq_nonneg (α n i - b * gridIncr w T n i)]
    refine (Finset.sum_le_sum hcell).trans (le_of_eq ?_)
    simp only [hQ, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    push_cast
    field_simp
  have hQxlim : Tendsto (fun k => 2 * A ^ 2 * T * (T / (ns k + 1)) + 2 * b ^ 2 * Q (ns k)) atTop
      (𝓝 (2 * A ^ 2 * T * 0 + 2 * b ^ 2 * T)) :=
    (tendsto_const_nhds.mul hstep).add (tendsto_const_nhds.mul h3)
  have hD0 : Tendsto (fun k => D (ns k)) atTop (𝓝 0) := by
    set C := 2 * A ^ 2 * T * 0 + 2 * b ^ 2 * T + 1 with hC
    have hev : ∀ᶠ k in atTop, 2 * A ^ 2 * T * (T / (ns k + 1)) + 2 * b ^ 2 * Q (ns k) < C :=
      hQxlim.eventually (gt_mem_nhds (by linarith))
    obtain ⟨K1, hK1⟩ := eventually_atTop.mp hev
    have hC0 : 0 < T + C := by
      have : 0 ≤ 2 * b ^ 2 * T := by positivity
      linarith
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hF.taylor_pathwise hT.le hXc (η := ε / (2 * (T + C))) (by positivity)
    refine ⟨max K1 N, fun k hk => ?_⟩
    have hkN : N ≤ ns k := (le_of_max_le_right hk).trans (hns.id_le k)
    have hb := hN (ns k) hkN
    have hq := (hQx (ns k)).trans (hK1 k (le_of_max_le_left hk)).le
    rw [Real.dist_eq, sub_zero]
    calc |D (ns k)| ≤ ε / (2 * (T + C)) * (T + ∑ i ∈ Finset.range (ns k + 1),
          (X (gridPt T (ns k) (i + 1)) - X (gridPt T (ns k) i)) ^ 2) := hb
      _ ≤ ε / (2 * (T + C)) * (T + C) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  -- the other limits
  have hSt0 : Tendsto (fun k => St (ns k)) atTop (𝓝 (∫ s in (0 : ℝ)..T, Ft s (X s))) :=
    (riemannSum_tendsto hT.le hFtc).comp hns.tendsto_atTop
  have hSa0 : Tendsto (fun k => Sa (ns k)) atTop (𝓝 (∫ s in (0 : ℝ)..T, Fx s (X s) * a s)) :=
    (riemannStieltjes_tendsto hT.le hFxc ha).comp hns.tendsto_atTop
  have hSxx0 : Tendsto (fun k => Sxx (ns k)) atTop (𝓝 (∫ s in (0 : ℝ)..T, Fxx s (X s))) :=
    (riemannSum_tendsto hT.le hFxxc).comp hns.tendsto_atTop
  have hlim := hD0.add (((((hSt0.add hSa0).add (h1.const_mul b)).add (h2.const_mul (b ^ 2 / 2))).add
    (hSxx0.const_mul (b ^ 2 / 2))).add hR0)
  have hconst : Tendsto (fun k => D (ns k) + (St (ns k) + Sa (ns k) + b * S1 (ns k) +
      b ^ 2 / 2 * S2 (ns k) + b ^ 2 / 2 * Sxx (ns k) + R (ns k))) atTop
      (𝓝 (F T (X T) - F 0 (X 0))) := by
    refine tendsto_const_nhds.congr fun k => ?_
    exact key (ns k)
  have huniq := tendsto_nhds_unique hconst hlim
  rw [huniq]
  have i1 : IntervalIntegrable (fun s => Ft s (X s)) volume 0 T := hFtc.intervalIntegrable 0 T
  have i2 : IntervalIntegrable (fun s => a s * Fx s (X s)) volume 0 T :=
    (ha.mul hFxc).intervalIntegrable 0 T
  have i3 : IntervalIntegrable (fun s => b ^ 2 / 2 * Fxx s (X s)) volume 0 T :=
    (continuous_const.mul hFxxc).intervalIntegrable 0 T
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul]
  have e : ∫ s in (0 : ℝ)..T, a s * Fx s (X s) = ∫ s in (0 : ℝ)..T, Fx s (X s) * a s := by
    congr 1; funext s; ring
  rw [e]
  ring

end Gardiner.Ito
