/-
# Wiener increments, quadratic variation and `∫W dW` (Gardiner §4.2.2, §4.2.5)

For a Wiener process `W` (`Gardiner.Ito.IsWiener W P`) and a partition
`t₀ = p 0 ≤ p 1 ≤ … ≤ p n = t` of `[t₀, t]` (`Gardiner.Ito.IsPartition`, with mesh `≤ δ`),
write `ΔWᵢ = W(p (i+1)) - W(p i)` (`Gardiner.Ito.dW`) and `Δtᵢ = p (i+1) - p i`.

* **Increments** (Gardiner §3.8.1 / text before (4.2.16)): the `ΔWᵢ` are independent
  (`Gardiner.Ito.IsWiener.dW_iIndepFun`) and `ΔWᵢ ~ N(0, Δtᵢ)` (`Gardiner.Ito.IsWiener.dW_map`).
* **Moments** (4.2.14), (4.2.17), §4.2.5 i)–ii): `⟨ΔWᵢ²⟩ = Δtᵢ`, `⟨ΔWᵢ⁴⟩ = 3Δtᵢ²`,
  `⟨(ΔWᵢ² - Δtᵢ)²⟩ = 2Δtᵢ²` (`Gardiner.Ito.IsWiener.dW_sq_mean`, `…dW_four`, `…dW_sq_sub_sq`).
* **Quadratic variation** (4.2.14)–(4.2.19): with `Q = Σᵢ ΔWᵢ²` (`Gardiner.Ito.qvSum`),
  `⟨Q⟩ = t - t₀` and the **exact** mean-square error
  `⟨(Q - (t - t₀))²⟩ = 2 Σᵢ Δtᵢ² ≤ 2δ(t - t₀)` (`Gardiner.Ito.IsWiener.qv_mean`,
  `Gardiner.Ito.IsWiener.qv_ms_error`, `Gardiner.Ito.IsWiener.qv_ms_le`), hence
  `ms-lim Q = t - t₀` as the mesh tends to zero (`Gardiner.Ito.IsWiener.qv_msLim`).
* **`∫ W dW`** (4.2.12)–(4.2.13), (4.2.20): the left-point sum `S = Σᵢ W(p i) ΔWᵢ`
  (`Gardiner.Ito.itoSum`) equals `½[W(t)² - W(t₀)²] - ½Q` for every path
  (`Gardiner.Ito.itoSum_eq`, derived from `Gardiner.SDE.ito_sum_identity`), so
  `⟨(S - ½[(W(t)² - W(t₀)²) - (t - t₀)])²⟩ = ½ Σᵢ Δtᵢ²` (`Gardiner.Ito.IsWiener.itoSum_ms_error`)
  and `ms-lim S = ½[W(t)² - W(t₀)² - (t - t₀)]` (`Gardiner.Ito.IsWiener.itoSum_msLim`).
  This discharges, in mean square, the quadratic-variation hypothesis `Σδᵢ² = t - t₀` of
  `Gardiner.SDE.ito_sum_of_qv` (`Gardiner.Ito.IsWiener.ito_sum_of_qv_ms`).
* **Instances** for the standard Wiener process (`Gardiner.Ito.stdWiener`) on uniform partitions
  of `[0, 1]`: `⟨(Q_n - 1)²⟩ = 2/n` and `⟨(S_n - ½(W(1)² - W(0)² - 1))²⟩ = 1/(2n)`
  (`Gardiner.Ito.qv_unif_instance`, `Gardiner.Ito.itoSum_unif_instance`).

**Erratum (4.2.18).**  The left-hand side is missing the square on `Wᵢ - Wᵢ₋₁`, and the middle
line `Σ_{i,j}[(tᵢ - tᵢ₋₁) - (t - t₀)][(tⱼ - tⱼ₋₁) - (t - t₀)]` should be
`Σ_{i,j}(tᵢ - tᵢ₋₁)(tⱼ - tⱼ₋₁) - (t - t₀)²`, which vanishes.  As printed, the middle line equals
`(n - 1)²(t - t₀)²`, so the printed right-hand side `2Σ Δtᵢ² + (n - 1)²(t - t₀)²` is wrong
(`Gardiner.Ito.eq_4_2_18_printed_wrong`: for `n = 2` on `[0, 1]` the mean-square error is `1`,
the printed expression gives `2`).  The final value `2 Σ Δtᵢ²` is correct.
-/
import SHSLib.Gardiner.Ito.Brownian
import SHSLib.Gardiner.SDE.SchemeMoments
import SHSLib.Gardiner.SDE.Schemes

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

/-! ### Partitions -/

/-- `p 0 = t₀ ≤ p 1 ≤ … ≤ p n = t` is a partition of `[t₀, t]` with mesh at most `δ`
(`p` is monotone on all of `ℕ`; its values beyond `n` are irrelevant). -/
structure IsPartition (p : ℕ → ℝ) (n : ℕ) (t₀ t δ : ℝ) : Prop where
  start : p 0 = t₀
  stop : p n = t
  mono : Monotone p
  mesh : ∀ i < n, p (i + 1) - p i ≤ δ

/-- The uniform partition `tᵢ = t₀ + i(t - t₀)/n`. -/
def unifPart (t₀ t : ℝ) (n : ℕ) (i : ℕ) : ℝ := t₀ + i * ((t - t₀) / n)

lemma isPartition_unifPart {t₀ t : ℝ} (h : t₀ ≤ t) {n : ℕ} (hn : 0 < n) :
    IsPartition (unifPart t₀ t n) n t₀ t ((t - t₀) / n) where
  start := by simp [unifPart]
  stop := by
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [unifPart]; field_simp; ring
  mono := fun i j hij => by
    have : 0 ≤ (t - t₀) / n := div_nonneg (by linarith) (by positivity)
    simp only [unifPart]; gcongr
  mesh := fun i _ => by simp only [unifPart]; push_cast; ring_nf; exact le_rfl

lemma IsPartition.step_nonneg {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ)
    (i : ℕ) : 0 ≤ p (i + 1) - p i := sub_nonneg.mpr (hp.mono (Nat.le_succ i))

lemma IsPartition.sum_step {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ) :
    ∑ i ∈ range n, (p (i + 1) - p i) = t - t₀ := by
  rw [sum_range_sub (f := p), hp.stop, hp.start]

lemma IsPartition.le {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ) : t₀ ≤ t := by
  rw [← hp.start, ← hp.stop]; exact hp.mono (Nat.zero_le n)

/-- `Σᵢ Δtᵢ² ≤ δ (t - t₀)`. -/
lemma IsPartition.sum_sq_le {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ) :
    ∑ i ∈ range n, (p (i + 1) - p i) ^ 2 ≤ δ * (t - t₀) := by
  rw [← hp.sum_step, mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hp.mesh i (mem_range.mp hi)) (hp.step_nonneg i)

/-! ### Increments -/

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- The increment `ΔWᵢ = W(p (i+1)) - W(p i)` over the `i`-th cell of the partition `p`. -/
def dW (W : ℝ → Ω → ℝ) (p : ℕ → ℝ) (i : ℕ) : Ω → ℝ := W (p (i + 1)) - W (p i)

/-- The quadratic-variation sum `Q = Σ_{i<n} ΔWᵢ²`. -/
def qvSum (W : ℝ → Ω → ℝ) (p : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ range n, dW W p i ω ^ 2

/-- The left-point (Itô) sum `S = Σ_{i<n} W(p i) ΔWᵢ` of (4.2.12). -/
def itoSum (W : ℝ → Ω → ℝ) (p : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, W (p i) ω * dW W p i ω

omit [MeasurableSpace Ω] in
/-- The partial sums of the increments are the displacements: `Σ_{j<i} ΔWⱼ = W(p i) - W(p 0)`. -/
lemma psum_dW (W : ℝ → Ω → ℝ) (p : ℕ → ℝ) (ω : Ω) (i : ℕ) :
    Gardiner.SDE.psum (fun j => dW W p j ω) i = W (p i) ω - W (p 0) ω := by
  simp only [Gardiner.SDE.psum, dW, Pi.sub_apply]
  exact sum_range_sub (fun j => W (p j) ω) i

omit [MeasurableSpace Ω] in
/-- (4.2.12)–(4.2.13), for every path: `S = ½[W(t)² - W(t₀)²] - ½ Σ ΔWᵢ²`.  Derived from the
algebraic identity `Gardiner.SDE.ito_sum_identity` of the Itô-free layer. -/
theorem itoSum_eq (W : ℝ → Ω → ℝ) (p : ℕ → ℝ) (n : ℕ) (ω : Ω) :
    itoSum W p n ω = 1 / 2 * (W (p n) ω ^ 2 - W (p 0) ω ^ 2) - 1 / 2 * qvSum W p n ω := by
  have h := Gardiner.SDE.ito_sum_identity (fun j => dW W p j ω) n
  simp only [psum_dW] at h
  have hsplit : itoSum W p n ω = W (p 0) ω * (W (p n) ω - W (p 0) ω) +
      ∑ i ∈ range n, (W (p i) ω - W (p 0) ω) * dW W p i ω := by
    rw [itoSum, ← sum_range_sub (fun j => W (p j) ω) n, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [dW, Pi.sub_apply]; ring
  rw [hsplit, h, qvSum]
  ring

lemma coe_step {p : ℕ → ℝ} (hp : Monotone p) (i : ℕ) :
    (((p (i + 1) - p i).toNNReal : ℝ≥0) : ℝ) = p (i + 1) - p i :=
  Real.coe_toNNReal _ (sub_nonneg.mpr (hp (Nat.le_succ i)))

namespace IsWiener

variable (hW : IsWiener W P)
include hW

lemma dW_measurable (p : ℕ → ℝ) (i : ℕ) : Measurable (dW W p i) := hW.measurable_sub _ _

/-- `ΔWᵢ ~ N(0, Δtᵢ)`. -/
theorem dW_map {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (i : ℕ) :
    P.map (dW W p i) = gaussianReal 0 (p (i + 1) - p i).toNNReal :=
  hW.law_sub (p i) (p (i + 1)) (h0.trans (hp (Nat.zero_le i))) (hp (Nat.le_succ i))

/-- **The increments over a partition are independent.** -/
theorem dW_iIndepFun {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) :
    iIndepFun (dW W p) P := by
  refine iIndepFun_nat_of_fin fun n => ?_
  have h := hW.indep_incr n (fun j : Fin (n + 1) => p j)
    (fun a b hab => hp (Fin.le_iff_val_le_val.mp hab)) (by simpa using h0)
  convert h using 2 with i

lemma dW_integral_comp {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (i : ℕ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    ∫ ω, f (dW W p i ω) ∂P = ∫ z, f z ∂(gaussianReal 0 (p (i + 1) - p i).toNNReal) := by
  have := hW.isProbabilityMeasure
  exact Gardiner.SDE.integral_comp_gauss (hW.dW_measurable p i) (hW.dW_map hp h0 i) hf

lemma dW_integrable_pow {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (i k : ℕ) :
    Integrable (fun ω => dW W p i ω ^ k) P :=
  Gardiner.SDE.integrable_comp_gauss (hW.dW_measurable p i) (hW.dW_map hp h0 i)
    (continuous_pow k) (Gardiner.SDE.gauss_integrable_pow _ k)


/-- `⟨ΔWᵢ⟩ = 0`. -/
theorem dW_mean {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (i : ℕ) :
    ∫ ω, dW W p i ω ∂P = 0 := by
  rw [hW.dW_integral_comp hp h0 i (f := fun z => z) continuous_id, Gardiner.SDE.gauss_m1]

/-- (4.2.14), §4.2.5 i): `⟨ΔWᵢ²⟩ = Δtᵢ`. -/
theorem dW_sq_mean {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (i : ℕ) :
    ∫ ω, dW W p i ω ^ 2 ∂P = p (i + 1) - p i := by
  rw [hW.dW_integral_comp hp h0 i (continuous_pow 2), Gardiner.SDE.gauss_m2, coe_step hp i]

/-- (4.2.17): `⟨ΔWᵢ⁴⟩ = 3Δtᵢ²`. -/
theorem dW_four {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (i : ℕ) :
    ∫ ω, dW W p i ω ^ 4 ∂P = 3 * (p (i + 1) - p i) ^ 2 := by
  rw [hW.dW_integral_comp hp h0 i (continuous_pow 4), Gardiner.SDE.gauss_m4, coe_step hp i]

/-- §4.2.5 ii): `⟨(ΔWᵢ² - Δtᵢ)²⟩ = 2Δtᵢ²`. -/
theorem dW_sq_sub_sq {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (i : ℕ) :
    ∫ ω, (dW W p i ω ^ 2 - (p (i + 1) - p i)) ^ 2 ∂P = 2 * (p (i + 1) - p i) ^ 2 := by
  have h := hW.dW_integral_comp hp h0 i
    (f := fun z => (z ^ 2 - (((p (i + 1) - p i).toNNReal : ℝ≥0) : ℝ)) ^ 2) (by fun_prop)
  rw [Gardiner.SDE.gauss_ii, coe_step hp i] at h
  exact h

/-- The centred squared increments `ΔWᵢ² - Δtᵢ`. -/
lemma centred_memLp {p : ℕ → ℝ} (hp : Monotone p) (h0 : 0 ≤ p 0) (i : ℕ) :
    MemLp (fun ω => dW W p i ω ^ 2 - (p (i + 1) - p i)) 2 P := by
  have := hW.isProbabilityMeasure
  have hm : Measurable fun ω => dW W p i ω ^ 2 - (p (i + 1) - p i) :=
    ((hW.dW_measurable p i).pow_const 2).sub_const _
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_
  have h4 := hW.dW_integrable_pow hp h0 i 4
  have h2 := hW.dW_integrable_pow hp h0 i 2
  have : (fun ω => (dW W p i ω ^ 2 - (p (i + 1) - p i)) ^ 2) = fun ω =>
      dW W p i ω ^ 4 - 2 * (p (i + 1) - p i) * dW W p i ω ^ 2 + (p (i + 1) - p i) ^ 2 := by
    funext ω; ring
  rw [this]
  exact (h4.sub (h2.const_mul _)).add (integrable_const _)

/-- (4.2.14): `⟨Σ ΔWᵢ²⟩ = t - t₀`. -/
theorem qv_mean {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ) (h0 : 0 ≤ t₀) :
    ∫ ω, qvSum W p n ω ∂P = t - t₀ := by
  have h0' : 0 ≤ p 0 := hp.start ▸ h0
  simp only [qvSum]
  rw [integral_finset_sum _ fun i _ => hW.dW_integrable_pow hp.mono h0' i 2, ← hp.sum_step]
  exact sum_congr rfl fun i _ => hW.dW_sq_mean hp.mono h0' i

/-- **(4.2.15)–(4.2.18), corrected: the exact mean-square error of the quadratic-variation
sum**, `⟨(Σ ΔWᵢ² - (t - t₀))²⟩ = 2 Σ Δtᵢ²`. -/
theorem qv_ms_error {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ)
    (h0 : 0 ≤ t₀) :
    ∫ ω, (qvSum W p n ω - (t - t₀)) ^ 2 ∂P = 2 * ∑ i ∈ range n, (p (i + 1) - p i) ^ 2 := by
  have := hW.isProbabilityMeasure
  have h0' : 0 ≤ p 0 := hp.start ▸ h0
  set Y : ℕ → Ω → ℝ := fun i ω => dW W p i ω ^ 2 - (p (i + 1) - p i) with hY
  have hsum : (fun ω => qvSum W p n ω - (t - t₀)) = ∑ i ∈ range n, Y i := by
    funext ω
    rw [Finset.sum_apply, ← hp.sum_step, qvSum, ← sum_sub_distrib]
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    ((hW.dW_measurable p i).pow_const 2).sub_const _
  have hYL2 : ∀ i ∈ range n, MemLp (Y i) 2 P := fun i _ => hW.centred_memLp hp.mono h0' i
  have hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0 := by
    intro i
    simp only [hY]
    rw [integral_sub (hW.dW_integrable_pow hp.mono h0' i 2) (integrable_const _),
      hW.dW_sq_mean hp.mono h0' i]
    simp
  have hind : iIndepFun Y P :=
    (hW.dW_iIndepFun hp.mono h0').comp (fun i z => z ^ 2 - (p (i + 1) - p i))
      (fun i => (measurable_id.pow_const 2).sub_const _)
  have hvar := IndepFun.variance_sum hYL2
    (fun i _ j _ hij => hind.indepFun hij)
  have hmean0 : ∫ ω, (∑ i ∈ range n, Y i) ω ∂P = 0 := by
    simp only [Finset.sum_apply]
    rw [integral_finset_sum _ fun i hi => (hYL2 i hi).integrable one_le_two]
    exact sum_eq_zero fun i _ => hYmean i
  have hsm : AEMeasurable (∑ i ∈ range n, Y i) P := by
    have := Finset.measurable_sum (range n) (fun i _ => hYm i)
    convert this.aemeasurable using 1
    funext ω; simp
  rw [variance_of_integral_eq_zero hsm hmean0] at hvar
  have hsq : (fun ω => (qvSum W p n ω - (t - t₀)) ^ 2) =
      fun ω => (∑ i ∈ range n, Y i) ω ^ 2 := by
    funext ω; rw [← hsum]
  rw [hsq, hvar, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [variance_of_integral_eq_zero (hYm i).aemeasurable (hYmean i)]
  exact hW.dW_sq_sub_sq hp.mono h0' i

/-- The mean-square error of the quadratic-variation sum is at most `2δ(t - t₀)`. -/
theorem qv_ms_le {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ) (h0 : 0 ≤ t₀) :
    ∫ ω, (qvSum W p n ω - (t - t₀)) ^ 2 ∂P ≤ 2 * δ * (t - t₀) := by
  rw [hW.qv_ms_error hp h0, mul_assoc]
  exact mul_le_mul_of_nonneg_left hp.sum_sq_le (by norm_num)

/-- **(4.2.19): `ms-lim Σ ΔWᵢ² = t - t₀`** along any sequence of partitions of `[t₀, t]` whose
mesh tends to zero. -/
theorem qv_msLim {t₀ t : ℝ} (h0 : 0 ≤ t₀) {p : ℕ → ℕ → ℝ} {n : ℕ → ℕ} {δ : ℕ → ℝ}
    (hp : ∀ k, IsPartition (p k) (n k) t₀ t (δ k)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (qvSum W (p k) (n k) ω - (t - t₀)) ^ 2 ∂P) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k => 2 * δ k * (t - t₀)) atTop (𝓝 0) := by
    simpa using (hδ.const_mul 2).mul_const (t - t₀)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k => integral_nonneg fun ω => sq_nonneg _) (fun k => hW.qv_ms_le (hp k) h0)

/-- **The mean-square error of the left-point sum for `∫ W dW`**:
`⟨(S - ½[(W(t)² - W(t₀)²) - (t - t₀)])²⟩ = ½ Σ Δtᵢ²`. -/
theorem itoSum_ms_error {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ)
    (h0 : 0 ≤ t₀) :
    ∫ ω, (itoSum W p n ω - 1 / 2 * ((W t ω ^ 2 - W t₀ ω ^ 2) - (t - t₀))) ^ 2 ∂P =
      1 / 2 * ∑ i ∈ range n, (p (i + 1) - p i) ^ 2 := by
  have h : (fun ω => (itoSum W p n ω - 1 / 2 * ((W t ω ^ 2 - W t₀ ω ^ 2) - (t - t₀))) ^ 2) =
      fun ω => 1 / 4 * (qvSum W p n ω - (t - t₀)) ^ 2 := by
    funext ω
    rw [itoSum_eq, hp.stop, hp.start]
    ring
  rw [h, integral_const_mul, hW.qv_ms_error hp h0]
  ring

/-- **(4.2.20): `∫_{t₀}^t W dW = ms-lim Σ W(tᵢ₋₁)ΔWᵢ = ½[W(t)² - W(t₀)² - (t - t₀)]`** along any
sequence of partitions whose mesh tends to zero. -/
theorem itoSum_msLim {t₀ t : ℝ} (h0 : 0 ≤ t₀) {p : ℕ → ℕ → ℝ} {n : ℕ → ℕ} {δ : ℕ → ℝ}
    (hp : ∀ k, IsPartition (p k) (n k) t₀ t (δ k)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (itoSum W (p k) (n k) ω -
      1 / 2 * ((W t ω ^ 2 - W t₀ ω ^ 2) - (t - t₀))) ^ 2 ∂P) atTop (𝓝 0) := by
  have h := (hW.qv_msLim h0 hp hδ).const_mul (1 / 4)
  rw [mul_zero] at h
  refine h.congr fun k => ?_
  rw [← integral_const_mul]
  congr 1
  funext ω
  rw [itoSum_eq, (hp k).stop, (hp k).start]
  ring

/-- **Comparison with `Gardiner.SDE.ito_sum_of_qv`.**  That theorem needs the exact identity
`Σδᵢ² = t - t₀`, which never holds for Wiener increments (it is a statement about a random
variable).  With real Wiener increments, `ito_sum_of_qv` holds *up to an error whose mean square is
exactly `½ Σ Δtᵢ²`*: for the increments `δᵢ = ΔWᵢ(ω)`,
`Σ psum δ i · δ i = ½[(psum δ n)² - (t - t₀)] + Eₙ(ω)` with `⟨Eₙ²⟩ = ½ Σ Δtᵢ² ≤ ½δ(t - t₀)`. -/
theorem ito_sum_of_qv_ms {p : ℕ → ℝ} {n : ℕ} {t₀ t δ : ℝ} (hp : IsPartition p n t₀ t δ)
    (h0 : 0 ≤ t₀) :
    ∫ ω, (∑ i ∈ range n, Gardiner.SDE.psum (fun j => dW W p j ω) i * dW W p i ω -
        1 / 2 * (Gardiner.SDE.psum (fun j => dW W p j ω) n ^ 2 - (t - t₀))) ^ 2 ∂P =
      1 / 2 * ∑ i ∈ range n, (p (i + 1) - p i) ^ 2 := by
  have h : (fun ω => (∑ i ∈ range n, Gardiner.SDE.psum (fun j => dW W p j ω) i * dW W p i ω -
        1 / 2 * (Gardiner.SDE.psum (fun j => dW W p j ω) n ^ 2 - (t - t₀))) ^ 2) =
      fun ω => 1 / 4 * (qvSum W p n ω - (t - t₀)) ^ 2 := by
    funext ω
    rw [Gardiner.SDE.ito_sum_identity, qvSum]
    ring
  rw [h, integral_const_mul, hW.qv_ms_error hp h0]
  ring

end IsWiener

/-! ### Instances: the standard Wiener process on uniform partitions of `[0, 1]` -/

lemma sum_unif_sq (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ range n, (unifPart 0 1 n (i + 1) - unifPart 0 1 n i) ^ 2 = 1 / n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [unifPart]
  push_cast
  simp only [sub_zero, zero_add]
  rw [sum_congr rfl (g := fun _ => (1 / (n : ℝ)) ^ 2) fun i _ => by ring, sum_const, card_range,
    nsmul_eq_mul]
  field_simp

/-- **Instance of (4.2.18)–(4.2.19)**: for the standard Wiener process and the uniform partition of
`[0, 1]` into `n` cells, `⟨(Σ ΔWᵢ² - 1)²⟩ = 2/n`, which tends to `0`. -/
theorem qv_unif_instance (n : ℕ) (hn : 0 < n) :
    ∫ ω, (qvSum stdWiener (unifPart 0 1 n) n ω - (1 - 0)) ^ 2 ∂stdWienerMeasure = 2 / (n : ℝ) := by
  rw [isWiener_stdWiener.qv_ms_error (isPartition_unifPart zero_le_one hn) le_rfl,
    sum_unif_sq n hn]
  ring

/-- **Instance of (4.2.20)**: for the standard Wiener process and the uniform partition of `[0, 1]`,
`⟨(Σ W(tᵢ₋₁)ΔWᵢ - ½[W(1)² - W(0)² - 1])²⟩ = 1/(2n)`. -/
theorem itoSum_unif_instance (n : ℕ) (hn : 0 < n) :
    ∫ ω, (itoSum stdWiener (unifPart 0 1 n) n ω -
      1 / 2 * ((stdWiener 1 ω ^ 2 - stdWiener 0 ω ^ 2) - (1 - 0))) ^ 2 ∂stdWienerMeasure =
      1 / (2 * (n : ℝ)) := by
  rw [isWiener_stdWiener.itoSum_ms_error (isPartition_unifPart zero_le_one hn) le_rfl,
    sum_unif_sq n hn]
  field_simp

/-- The uniform partitions realise `ms-lim Σ ΔWᵢ² = t - t₀` for the standard Wiener process. -/
theorem qv_msLim_unif {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h : t₀ ≤ t) :
    Tendsto (fun k : ℕ => ∫ ω, (qvSum stdWiener (unifPart t₀ t (k + 1)) (k + 1) ω - (t - t₀)) ^ 2
      ∂stdWienerMeasure) atTop (𝓝 0) := by
  refine isWiener_stdWiener.qv_msLim h0 (δ := fun k => (t - t₀) / (k + 1 : ℕ))
    (fun k => isPartition_unifPart h k.succ_pos) ?_
  have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (t - t₀)
  rw [mul_zero] at this
  refine this.congr fun k => ?_
  push_cast; ring

/-! ### Erratum (4.2.18) -/

/-- The right-hand side of (4.2.18) as printed:
`2 Σᵢ Δtᵢ² + Σ_{i,j} [Δtᵢ - (t - t₀)][Δtⱼ - (t - t₀)]`. -/
def printed_4_2_18 (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * ∑ i ∈ range n, (p (i + 1) - p i) ^ 2 +
    ∑ i ∈ range n, ∑ j ∈ range n,
      ((p (i + 1) - p i) - (p n - p 0)) * ((p (j + 1) - p j) - (p n - p 0))

/-- **Erratum (4.2.18).**  For the uniform partition of `[0, 1]` into two cells the mean-square
error of the quadratic-variation sum is `1`, but the printed right-hand side of (4.2.18) gives `2`.
The correct value is `2 Σ Δtᵢ²` (`Gardiner.Ito.IsWiener.qv_ms_error`). -/
theorem eq_4_2_18_printed_wrong :
    ∫ ω, (qvSum stdWiener (unifPart 0 1 2) 2 ω - (1 - 0)) ^ 2 ∂stdWienerMeasure = 1 ∧
      printed_4_2_18 (unifPart 0 1 2) 2 = 2 := by
  refine ⟨?_, ?_⟩
  · rw [qv_unif_instance 2 (by norm_num)]; norm_num
  · simp only [printed_4_2_18, unifPart, sum_range_succ, sum_range_zero]; norm_num

end Gardiner.Ito
