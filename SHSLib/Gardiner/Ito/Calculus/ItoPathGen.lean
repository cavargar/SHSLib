/-
# Pathwise core of Itô's formula for a general Itô process

`Gardiner.Ito.IsC12.ito_pathwise_gen` is deterministic.  Let `X` be a continuous path whose
increments over the uniform partition of `[0, T]` split as
`X(tᵢ₊₁) - X(tᵢ) = ∫_{tᵢ}^{tᵢ₊₁} a + yᵢ` with `a` continuous, and let `β ≥ 0` be continuous.
Suppose that along a subsequence of partitions

* `Σᵢ F_x(tᵢ, Xᵢ) yᵢ → J`,
* `Σᵢ F_xx(tᵢ, Xᵢ) (yᵢ² - ∫_{tᵢ}^{tᵢ₊₁} β) → 0`, and
* `Σᵢ (yᵢ² - ∫_{tᵢ}^{tᵢ₊₁} β) → 0`.

Then `F(T, X_T) - F(0, X_0) = ∫₀ᵀ (F_t + a F_x + ½ β F_xx)(s, X_s) ds + J`.

For an Itô process `x = x₀ + ∫ a ds + ∫ b dW`, `yᵢ` is the increment of `∫ b dW` and `β = b²`;
the hypotheses hold almost surely along a subsequence (`Gardiner.Ito.ItoGeneral`).
-/
import SHSLib.Gardiner.Ito.Calculus.ItoPath

open Filter Topology Set MeasureTheory

noncomputable section

namespace Gardiner.Ito

variable {F Ft Fx Fxx : ℝ → ℝ → ℝ}

/-- **Pathwise Itô formula for a general Itô process** (deterministic core). -/
theorem IsC12.ito_pathwise_gen (hF : IsC12 F Ft Fx Fxx) {T : ℝ} (hT : 0 < T) {X a β : ℝ → ℝ}
    (hXc : Continuous X) (ha : Continuous a) (hβ : Continuous β) {y : ℕ → ℕ → ℝ}
    (hdX : ∀ n i, i ≤ n → X (gridPt T n (i + 1)) - X (gridPt T n i) =
      (∫ s in gridPt T n i..gridPt T n (i + 1), a s) + y n i)
    {ns : ℕ → ℕ} (hns : StrictMono ns) {J : ℝ}
    (h1 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1),
      Fx (gridPt T (ns k) i) (X (gridPt T (ns k) i)) * y (ns k) i) atTop (𝓝 J))
    (h2 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1),
      Fxx (gridPt T (ns k) i) (X (gridPt T (ns k) i)) *
        (y (ns k) i ^ 2 - ∫ s in gridPt T (ns k) i..gridPt T (ns k) (i + 1), β s)) atTop (𝓝 0))
    (h3 : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1),
      (y (ns k) i ^ 2 - ∫ s in gridPt T (ns k) i..gridPt T (ns k) (i + 1), β s)) atTop (𝓝 0)) :
    F T (X T) - F 0 (X 0) =
      (∫ s in (0 : ℝ)..T, (Ft s (X s) + a s * Fx s (X s) + β s / 2 * Fxx s (X s))) + J := by
  have hFtc : Continuous fun s => Ft s (X s) := hF.cont_Ft.comp (continuous_id.prodMk hXc)
  have hFxc : Continuous fun s => Fx s (X s) := hF.cont_Fx.comp (continuous_id.prodMk hXc)
  have hFxxc : Continuous fun s => Fxx s (X s) := hF.cont_Fxx.comp (continuous_id.prodMk hXc)
  set α : ℕ → ℕ → ℝ := fun n i => ∫ s in gridPt T n i..gridPt T n (i + 1), a s with hα
  set βc : ℕ → ℕ → ℝ := fun n i => ∫ s in gridPt T n i..gridPt T n (i + 1), β s with hβc
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
    Fx (gridPt T n i) (X (gridPt T n i)) * y n i with hS1
  set S2 : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Fxx (gridPt T n i) (X (gridPt T n i)) * (y n i ^ 2 - βc n i) with hS2
  set Sxx : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Fxx (gridPt T n i) (X (gridPt T n i)) * βc n i with hSxx
  set R : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1),
    Fxx (gridPt T n i) (X (gridPt T n i)) / 2 * (2 * α n i * y n i + α n i ^ 2) with hR
  have key : ∀ n, F T (X T) - F 0 (X 0) =
      D n + (St n + Sa n + S1 n + 1 / 2 * S2 n + 1 / 2 * Sxx n + R n) := by
    intro n
    have : ∑ i ∈ Finset.range (n + 1),
        (Ft (gridPt T n i) (X (gridPt T n i)) * (T / (n + 1)) +
          Fx (gridPt T n i) (X (gridPt T n i)) * (X (gridPt T n (i + 1)) - X (gridPt T n i)) +
          Fxx (gridPt T n i) (X (gridPt T n i)) / 2 *
            (X (gridPt T n (i + 1)) - X (gridPt T n i)) ^ 2) =
        St n + Sa n + S1 n + 1 / 2 * S2 n + 1 / 2 * Sxx n + R n := by
      simp only [hSt, hSa, hS1, hS2, hSxx, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := by simp at hi; omega
      rw [hdX n i hin]; ring
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
  set Q : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), y n i ^ 2 with hQ
  have hstep : Tendsto (fun k => T / ((ns k : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T).comp hns.tendsto_atTop
    simp only [mul_zero] at this
    refine this.congr fun k => ?_
    simp [div_eq_mul_inv]
  -- `Q → ∫ β`
  have hβsum : Tendsto (fun k => ∑ i ∈ Finset.range (ns k + 1), βc (ns k) i) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, β s)) := by
    have := (riemannStieltjes_tendsto hT.le (f := fun _ => (1 : ℝ)) continuous_const hβ).comp
      hns.tendsto_atTop
    simp only [one_mul] at this
    exact this
  have hQlim : Tendsto (fun k => Q (ns k)) atTop (𝓝 (0 + ∫ s in (0 : ℝ)..T, β s)) := by
    refine (h3.add hβsum).congr fun k => ?_
    simp only [hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hβc]; ring
  rw [zero_add] at hQlim
  -- R → 0
  have hRb : ∀ n, |R n| ≤ Mx / 2 * (A * Real.sqrt (T / (n + 1)) * (Q n + T) +
      A ^ 2 * T * (T / (n + 1))) := by
    intro n
    have hh0 : 0 ≤ T / ((n : ℝ) + 1) := by positivity
    have hcell : ∀ i ∈ Finset.range (n + 1), |Fxx (gridPt T n i) (X (gridPt T n i)) / 2 *
        (2 * α n i * y n i + α n i ^ 2)| ≤
        Mx / 2 * (A * Real.sqrt (T / (n + 1)) * (y n i ^ 2 + T / (n + 1)) +
          A ^ 2 * (T / (n + 1)) ^ 2) := by
      intro i hi
      have hin : i ≤ n := by simp at hi; omega
      have hti : gridPt T n i ∈ Icc 0 T :=
        ⟨gridPt_nonneg hT.le n i, gridPt_le hT.le (by omega)⟩
      have e1 := hMx' _ hti
      have e2 := hαb n i hin
      have e3 := two_abs_mul_le_sqrt (u := y n i) hh0
      rw [abs_mul, abs_div, abs_two]
      refine mul_le_mul (div_le_div_of_nonneg_right e1 zero_le_two) ?_ (abs_nonneg _)
        (by positivity)
      calc |2 * α n i * y n i + α n i ^ 2|
          ≤ |α n i| * (2 * |y n i|) + |α n i| ^ 2 := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_two, abs_pow]; ring
        _ ≤ (A * (T / (n + 1))) * (2 * |y n i|) + (A * (T / (n + 1))) ^ 2 := by
            gcongr
        _ = A * (2 * |y n i| * (T / (n + 1))) + A ^ 2 * (T / (n + 1)) ^ 2 := by
            ring
        _ ≤ A * (Real.sqrt (T / (n + 1)) * (y n i ^ 2 + T / (n + 1))) +
            A ^ 2 * (T / (n + 1)) ^ 2 := by gcongr
        _ = _ := by ring
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hcell).trans (le_of_eq ?_))
    simp only [hQ, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    field_simp
  have hR0 : Tendsto (fun k => R (ns k)) atTop (𝓝 0) := by
    have hB : Tendsto (fun k => Mx / 2 * (A * Real.sqrt (T / (ns k + 1)) * (Q (ns k) + T) +
        A ^ 2 * T * (T / (ns k + 1)))) atTop
        (𝓝 (Mx / 2 * (A * Real.sqrt 0 * ((∫ s in (0 : ℝ)..T, β s) + T) + A ^ 2 * T * 0))) := by
      refine tendsto_const_nhds.mul (((tendsto_const_nhds.mul
        ((Real.continuous_sqrt.tendsto 0).comp hstep)).mul (hQlim.add tendsto_const_nhds)).add
        (tendsto_const_nhds.mul hstep))
    simp only [Real.sqrt_zero, mul_zero, zero_mul, add_zero] at hB
    exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact hRb (ns k)) hB
  -- D → 0
  have hQx : ∀ n, ∑ i ∈ Finset.range (n + 1), (X (gridPt T n (i + 1)) - X (gridPt T n i)) ^ 2 ≤
      2 * A ^ 2 * T * (T / (n + 1)) + 2 * Q n := by
    intro n
    have hcell : ∀ i ∈ Finset.range (n + 1), (X (gridPt T n (i + 1)) - X (gridPt T n i)) ^ 2 ≤
        2 * A ^ 2 * (T / (n + 1)) ^ 2 + 2 * y n i ^ 2 := by
      intro i hi
      have hin : i ≤ n := by simp at hi; omega
      rw [hdX n i hin]
      have e2 := hαb n i hin
      have e3 : α n i ^ 2 ≤ (A * (T / (n + 1))) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e2 2
      nlinarith [sq_nonneg (α n i - y n i)]
    refine (Finset.sum_le_sum hcell).trans (le_of_eq ?_)
    simp only [hQ, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    push_cast
    field_simp
  have hQxlim : Tendsto (fun k => 2 * A ^ 2 * T * (T / (ns k + 1)) + 2 * Q (ns k)) atTop
      (𝓝 (2 * A ^ 2 * T * 0 + 2 * ∫ s in (0 : ℝ)..T, β s)) :=
    (tendsto_const_nhds.mul hstep).add (tendsto_const_nhds.mul hQlim)
  have hD0 : Tendsto (fun k => D (ns k)) atTop (𝓝 0) := by
    set C := |2 * A ^ 2 * T * 0 + 2 * ∫ s in (0 : ℝ)..T, β s| + 1 with hC
    have hev : ∀ᶠ k in atTop, 2 * A ^ 2 * T * (T / (ns k + 1)) + 2 * Q (ns k) < C :=
      hQxlim.eventually (gt_mem_nhds (by
        have := le_abs_self (2 * A ^ 2 * T * 0 + 2 * ∫ s in (0 : ℝ)..T, β s); linarith))
    obtain ⟨K1, hK1⟩ := eventually_atTop.mp hev
    have hC0 : 0 < T + C := by
      have : 0 ≤ |2 * A ^ 2 * T * 0 + 2 * ∫ s in (0 : ℝ)..T, β s| := abs_nonneg _
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
  have hSxx0 : Tendsto (fun k => Sxx (ns k)) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, Fxx s (X s) * β s)) :=
    (riemannStieltjes_tendsto hT.le hFxxc hβ).comp hns.tendsto_atTop
  have hlim := hD0.add (((((hSt0.add hSa0).add h1).add (h2.const_mul (1 / 2))).add
    (hSxx0.const_mul (1 / 2))).add hR0)
  have hconst : Tendsto (fun k => D (ns k) + (St (ns k) + Sa (ns k) + S1 (ns k) +
      1 / 2 * S2 (ns k) + 1 / 2 * Sxx (ns k) + R (ns k))) atTop
      (𝓝 (F T (X T) - F 0 (X 0))) := by
    refine tendsto_const_nhds.congr fun k => ?_
    exact key (ns k)
  have huniq := tendsto_nhds_unique hconst hlim
  rw [huniq]
  have i1 : IntervalIntegrable (fun s => Ft s (X s)) volume 0 T := hFtc.intervalIntegrable 0 T
  have i2 : IntervalIntegrable (fun s => a s * Fx s (X s)) volume 0 T :=
    (ha.mul hFxc).intervalIntegrable 0 T
  have i3 : IntervalIntegrable (fun s => β s / 2 * Fxx s (X s)) volume 0 T :=
    ((hβ.div_const 2).mul hFxxc).intervalIntegrable 0 T
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2]
  have e : ∫ s in (0 : ℝ)..T, a s * Fx s (X s) = ∫ s in (0 : ℝ)..T, Fx s (X s) * a s := by
    congr 1; funext s; ring
  have e2 : ∫ s in (0 : ℝ)..T, β s / 2 * Fxx s (X s) =
      1 / 2 * ∫ s in (0 : ℝ)..T, Fxx s (X s) * β s := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext s; ring
  rw [e, e2]
  ring

end Gardiner.Ito
