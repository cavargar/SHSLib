/-
# Itô processes and Itô's formula (Gardiner §4.3.3, (4.3.14); §4.2.6 d)

An **Itô process** on `[0, T]` (`Gardiner.Ito.IsItoProcess`) is a process
`x(t) = x(0) + ∫₀ᵗ a(s) ds + ∫₀ᵗ b(s) dW(s)` with an Itô integrand `b` (random, nonanticipating)
and a drift `a`, where `x`, `a`, `b` have continuous paths.  For `F(t, x)` of class `C^{1,2}` with
bounded `F_x`, `F_xx` and a bounded noise coefficient `b`, **Itô's formula** holds:

`F(T, x(T)) - F(0, x(0)) = ∫₀ᵀ (F_t + a F_x + ½ b² F_xx)(s, x(s)) ds + ∫₀ᵀ b F_x(s, x(s)) dW(s)`

almost surely (`Gardiner.Ito.IsFWiener.ito_formula_process`).  With `F` independent of `t` this is
Gardiner (4.3.14).

Proof: along the uniform partitions, the increments of `x` split into a drift part and the
increments of `I = ∫ b dW`.  Then `Σ F_x(tᵢ, xᵢ) ΔIᵢ → ∫ b F_x dW` in mean square
(`sum_mul_incr_tendsto`), and the weighted quadratic variations
`Σ F_xx(tᵢ, xᵢ)(ΔIᵢ² - ∫_{tᵢ}^{tᵢ₊₁} b²)` and `Σ (ΔIᵢ² - ∫ b²)` tend to `0` in mean square
(`qv_weighted_sq_le`).  Along a subsequence all three converge almost surely, and the deterministic
`IsC12.ito_pathwise_gen` applies path by path.
-/
import SHSLib.Gardiner.Ito.Calculus.QuadVar
import SHSLib.Gardiner.Ito.Calculus.ItoPathGen

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- **An Itô process** on `[0, T]` (Gardiner §4.3.3): `x(t) = x(0) + ∫₀ᵗ a ds + ∫₀ᵗ b dW` almost
surely for each `t ∈ [0, T]`, where `b` is an Itô integrand, `x` is jointly measurable and
adapted, and `x`, `a`, `b` have almost surely continuous paths. -/
structure IsItoProcess (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ)
    (x a b : ℝ → Ω → ℝ) : Prop where
  measurable : Measurable (Function.uncurry x)
  adapted : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (x t)
  cont : ∀ᵐ ω ∂P, Continuous fun t => x t ω
  drift_cont : ∀ᵐ ω ∂P, Continuous fun t => a t ω
  noise : IsItoIntegrand 𝓕 P T b
  noise_cont : ∀ᵐ ω ∂P, Continuous fun t => b t ω
  eq : ∀ t, 0 ≤ t → t ≤ T →
    x t =ᵐ[P] fun ω => x 0 ω + (∫ s in (0 : ℝ)..t, a s ω) + itoInt W 𝓕 P t b ω

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- For a bounded Itô integrand with continuous paths, `∫ₛᵗ b²` is almost surely equal to an
`𝓕 t`-measurable random variable. -/
lemma sqInt_aestronglyMeasurable {T B : ℝ} {b : ℝ → Ω → ℝ} (hb : IsItoIntegrand 𝓕 P T b)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b u ω| ≤ B) (hbc : ∀ᵐ ω ∂P, Continuous fun u => b u ω)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    AEStronglyMeasurable[𝓕 t] (sqInt b s t) P := by
  have := hW.isProbabilityMeasure
  set R : ℕ → Ω → ℝ := fun m ω => ∑ k ∈ Finset.range (m + 1),
    b (s + gridPt (t - s) m k) ω ^ 2 * ((t - s) / (m + 1)) with hR
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  have hpt : ∀ m k, k ∈ Finset.range (m + 1) →
      0 ≤ s + gridPt (t - s) m k ∧ s + gridPt (t - s) m k ≤ t := by
    intro m k hk
    have h1 := gridPt_nonneg hts m k
    have h2 := gridPt_le hts (n := m) (i := k) (by simp at hk; omega)
    exact ⟨by linarith, by linarith⟩
  have hRm : ∀ m, StronglyMeasurable[𝓕 t] (R m) := by
    intro m
    have : R m = ∑ k ∈ Finset.range (m + 1), fun ω =>
        b (s + gridPt (t - s) m k) ω ^ 2 * ((t - s) / (m + 1)) := by
      funext ω; simp [hR]
    rw [this]
    refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
    obtain ⟨h1, h2⟩ := hpt m k hk
    exact (((hb.adapted _ h1 (h2.trans htT)).mono (𝓕.mono h2)).pow 2).mul_const _
  have hb2 : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, b u ω ^ 2 ≤ B ^ 2 := fun u hu ω => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB u hu ω) 2
  have hRb : ∀ m ω, |R m ω| ≤ B ^ 2 * (t - s) := by
    intro m ω
    rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (by positivity))]
    calc R m ω ≤ ∑ k ∈ Finset.range (m + 1), B ^ 2 * ((t - s) / (m + 1)) :=
          Finset.sum_le_sum fun k hk => by
            obtain ⟨h1, h2⟩ := hpt m k hk
            exact mul_le_mul_of_nonneg_right (hb2 _ ⟨h1, h2.trans htT⟩ ω) (by positivity)
      _ = B ^ 2 * (t - s) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
  have hβm := measurable_sqInt hb.measurable s t
  have hβb : ∀ ω, |sqInt b s t ω| ≤ B ^ 2 * (t - s) := fun ω => by
    rw [abs_of_nonneg (sqInt_nonneg b s t ω)]; exact sqInt_le hB hs hst htT ω
  have hRi : ∀ m, Integrable (R m) P := fun m =>
    Integrable.of_bound ((hRm m).mono (𝓕.le t)).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hRb m ω)
  have hβi : Integrable (sqInt b s t) P :=
    Integrable.of_bound hβm.aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hβb ω)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m => R m ω) atTop (𝓝 (sqInt b s t ω)) := by
    filter_upwards [hbc] with ω hω
    have hc : Continuous fun u => b (s + u) ω ^ 2 :=
      (hω.comp (continuous_const.add continuous_id)).pow 2
    have h := riemannSum_tendsto hts hc
    have e : ∫ u in (0 : ℝ)..t - s, b (s + u) ω ^ 2 = sqInt b s t ω := by
      rw [intervalIntegral.integral_comp_add_left (fun u => b u ω ^ 2) s, add_zero,
        add_sub_cancel, intervalIntegral.integral_of_le hst]
      rfl
    rw [e] at h
    exact h
  have hl1 : Tendsto (fun m => ∫ ω, |R m ω - sqInt b s t ω| ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun m ω => |R m ω - sqInt b s t ω|) (f := fun _ => 0)
      (fun _ => 2 * (B ^ 2 * (t - s)))
      (fun m => ((hRi m).sub hβi).abs.aestronglyMeasurable) (integrable_const _)
      (fun m => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        have := abs_sub (R m ω) (sqInt b s t ω)
        linarith [hRb m ω, hβb ω])
      (hlim.mono fun ω hω => by
        have := (hω.sub_const (sqInt b s t ω)).abs
        simpa using this)
    simpa using h
  have hce := condExp_eq_of_tendsto_l1 (𝓕 := 𝓕) (μ := P) t hRm hRi hβi hl1
  exact ⟨P[sqInt b s t | 𝓕 t], stronglyMeasurable_condExp, hce.symm⟩

end Gardiner.Ito

namespace Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **Itô's formula for an Itô process** (Gardiner (4.3.14); time-dependent form as in
(4.2.39)): for `x = x(0) + ∫ a ds + ∫ b dW` with bounded `b`, and `F ∈ C^{1,2}` with bounded
`F_x`, `F_xx`,
`F(T, x(T)) - F(0, x(0)) = ∫₀ᵀ (F_t + a F_x + ½ b² F_xx)(s, x(s)) ds + ∫₀ᵀ b F_x(s, x(s)) dW(s)`
almost surely. -/
theorem IsFWiener.ito_formula_process {T B C1 C2 : ℝ} (hT : 0 < T)
    {F Ft Fx Fxx : ℝ → ℝ → ℝ} (hF : IsC12 F Ft Fx Fxx)
    (hFx : ∀ t y, |Fx t y| ≤ C1) (hFxx : ∀ t y, |Fxx t y| ≤ C2)
    {x a b : ℝ → Ω → ℝ} (hx : IsItoProcess W 𝓕 P T x a b) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b u ω| ≤ B) :
    (fun ω => F T (x T ω) - F 0 (x 0 ω)) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, (Ft s (x s ω) + a s ω * Fx s (x s ω) + b s ω ^ 2 / 2 * Fxx s (x s ω))) +
        itoInt W 𝓕 P T (fun s ω => b s ω * Fx s (x s ω)) ω := by
  have := hW.isProbabilityMeasure
  set g : ℝ → Ω → ℝ := fun t ω => Fx t (x t ω) with hg
  set k2 : ℝ → Ω → ℝ := fun t ω => Fxx t (x t ω) with hk2
  have hgm : Measurable (Function.uncurry g) :=
    hF.cont_Fx.measurable.comp (measurable_fst.prodMk hx.measurable)
  have hgad : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (g t) := fun t h0 h1 =>
    (hF.cont_Fx.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
      (hx.adapted t h0 h1)
  have hk2ad : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (k2 t) := fun t h0 h1 =>
    (hF.cont_Fxx.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
      (hx.adapted t h0 h1)
  have hgc : ∀ᵐ ω ∂P, Continuous fun t => g t ω :=
    hx.cont.mono fun ω h => hF.cont_Fx.comp (continuous_id.prodMk h)
  have hb := hx.noise
  set J := itoInt W 𝓕 P T (fun u ω => g u ω * b u ω) with hJ
  set tp : ℕ → ℕ → ℝ := fun n i => gridPt T n i with htp
  have ht0 : ∀ n i, 0 ≤ tp n i := fun n i => gridPt_nonneg hT.le n i
  have htle : ∀ n i, tp n i ≤ tp n (i + 1) := fun n i => gridPt_mono hT.le n (Nat.le_succ i)
  have htT : ∀ n i, i ≤ n → tp n (i + 1) ≤ T := fun n i hi => gridPt_le hT.le (by omega)
  set D : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    itoIncr W 𝓕 P b (tp n i) (tp n (i + 1)) ω ^ 2 - sqInt b (tp n i) (tp n (i + 1)) ω with hD
  set A1 : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (n + 1),
    g (tp n i) ω * itoIncr W 𝓕 P b (tp n i) (tp n (i + 1)) ω with hA1
  set A2 : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (n + 1), k2 (tp n i) ω * D n i ω with hA2
  set A3 : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (n + 1), D n i ω with hA3
  -- mean-square convergence of the three sums
  have e1 : Tendsto (fun n => ∫ ω, (A1 n ω - J ω) ^ 2 ∂P) atTop (𝓝 0) :=
    sum_mul_incr_tendsto hW hT hb hgm hgad (fun t ω => hFx t (x t ω)) hgc
  have hβ : ∀ n, ∀ i ≤ n, AEStronglyMeasurable[𝓕 (gridPt T n (i + 1))]
      (sqInt b (gridPt T n i) (gridPt T n (i + 1))) P := fun n i hi =>
    sqInt_aestronglyMeasurable hW hb hB hx.noise_cont (ht0 n i) (htle n i) (htT n i hi)
  have e2 : ∀ n, ∫ ω, A2 n ω ^ 2 ∂P ≤ 8 * C2 ^ 2 * B ^ 4 * T ^ 2 / (n + 1) := fun n =>
    qv_weighted_sq_le hW hb hB0 hB hT n (fun i => k2 (tp n i))
      (fun i hi => hk2ad _ (ht0 n i) ((htle n i).trans (htT n i hi))) (fun i _ ω => hFxx _ _)
      (hβ n)
  have e3 : ∀ n, ∫ ω, A3 n ω ^ 2 ∂P ≤ 8 * 1 ^ 2 * B ^ 4 * T ^ 2 / (n + 1) := by
    intro n
    have h := qv_weighted_sq_le hW hb hB0 hB hT (C := 1) n (fun _ => fun _ => (1 : ℝ))
      (fun i _ => stronglyMeasurable_const) (fun i _ ω => by simp) (hβ n)
    simp only [one_mul] at h
    exact h
  have hbound : ∀ c : ℝ, Tendsto (fun n : ℕ => 8 * c ^ 2 * B ^ 4 * T ^ 2 / ((n : ℝ) + 1)) atTop
      (𝓝 0) := fun c =>
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have e2' : Tendsto (fun n => ∫ ω, A2 n ω ^ 2 ∂P) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) e2 (hbound C2)
  have e3' : Tendsto (fun n => ∫ ω, A3 n ω ^ 2 ∂P) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) e3 (hbound 1)
  -- integrability
  have hDm : ∀ n i, i ≤ n → MemLp (D n i) 2 P := fun n i hi =>
    memLp_itoIncr_sq_sub hW hb hB0 hB hT (ht0 n i) (htle n i) (htT n i hi)
  have hA1m : ∀ n, MemLp (fun ω => A1 n ω - J ω) 2 P := by
    intro n
    refine MemLp.sub ?_ (memLp_itoInt hW (isItoIntegrand_mul_bdd hb hgm hgad
      (fun t ω => hFx t (x t ω))))
    have := memLp_finset_sum' (Finset.range (n + 1)) fun i hi =>
      memLp_mul_of_bdd ((hgad _ (ht0 n i) ((htle n i).trans (htT n i (by simp at hi; omega)))).mono
        (𝓕.le _)).aestronglyMeasurable (fun ω => hFx (tp n i) (x (tp n i) ω))
        (memLp_itoIncr hW hb (htle n i) (htT n i (by simp at hi; omega)))
    convert this using 1; funext ω; simp [hA1]
  have hA2m : ∀ n, MemLp (A2 n) 2 P := by
    intro n
    have := memLp_finset_sum' (Finset.range (n + 1)) fun i hi =>
      memLp_mul_of_bdd ((hk2ad _ (ht0 n i) ((htle n i).trans (htT n i (by simp at hi; omega)))).mono
        (𝓕.le _)).aestronglyMeasurable (fun ω => hFxx (tp n i) (x (tp n i) ω))
        (hDm n i (by simp at hi; omega))
    convert this using 1; funext ω; simp [hA2]
  have hA3m : ∀ n, MemLp (A3 n) 2 P := by
    intro n
    have := memLp_finset_sum' (Finset.range (n + 1)) fun i hi => hDm n i (by simp at hi; omega)
    convert this using 1; funext ω; simp [hA3]
  -- a common almost surely convergent subsequence
  set Z : ℕ → Ω → ℝ := fun n ω => (A1 n ω - J ω) ^ 2 + A2 n ω ^ 2 + A3 n ω ^ 2 with hZ
  have hZi : ∀ n, Integrable (Z n) P := fun n =>
    ((hA1m n).integrable_sq.add (hA2m n).integrable_sq).add (hA3m n).integrable_sq
  have hZlim : Tendsto (fun n => ∫ ω, Z n ω ∂P) atTop (𝓝 0) := by
    have := (e1.add e2').add e3'
    simp only [add_zero] at this
    refine this.congr fun n => ?_
    simp only [hZ]
    have i12 : Integrable (fun ω => (A1 n ω - J ω) ^ 2 + A2 n ω ^ 2) P :=
      (hA1m n).integrable_sq.add (hA2m n).integrable_sq
    rw [integral_add i12 (hA3m n).integrable_sq,
      integral_add (hA1m n).integrable_sq (hA2m n).integrable_sq]
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto_zero hZi
    (fun n ω => by positivity) hZlim
  -- the grid decomposition holds almost surely
  have hgrid : ∀ᵐ ω ∂P, ∀ n i, i ≤ n + 1 → x (tp n i) ω =
      x 0 ω + (∫ s in (0 : ℝ)..tp n i, a s ω) + itoInt W 𝓕 P (tp n i) b ω := by
    refine ae_all_iff.mpr fun n => ae_all_iff.mpr fun i => ?_
    by_cases hi : i ≤ n + 1
    · exact (hx.eq _ (ht0 n i) (gridPt_le hT.le hi)).mono fun ω h _ => h
    · exact Eventually.of_forall fun ω h => absurd h hi
  filter_upwards [hae, hgrid, hx.cont, hx.drift_cont, hx.noise_cont] with ω hZω hgr hxc hac hbc
  have l1 : Tendsto (fun k => A1 (ns k) ω - J ω) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (Z := fun k => Z (ns k) ω) (fun k => by
      simp only [hZ]; nlinarith [sq_nonneg (A2 (ns k) ω), sq_nonneg (A3 (ns k) ω)]) hZω
  have l2 : Tendsto (fun k => A2 (ns k) ω) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (Z := fun k => Z (ns k) ω) (fun k => by
      simp only [hZ]; nlinarith [sq_nonneg (A1 (ns k) ω - J ω), sq_nonneg (A3 (ns k) ω)]) hZω
  have l3 : Tendsto (fun k => A3 (ns k) ω) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (Z := fun k => Z (ns k) ω) (fun k => by
      simp only [hZ]; nlinarith [sq_nonneg (A1 (ns k) ω - J ω), sq_nonneg (A2 (ns k) ω)]) hZω
  have l1' : Tendsto (fun k => A1 (ns k) ω) atTop (𝓝 (J ω)) := by
    simpa using l1.add_const (J ω)
  have hsq : ∀ n i, ∫ s in gridPt T n i..gridPt T n (i + 1), b s ω ^ 2 =
      sqInt b (tp n i) (tp n (i + 1)) ω := fun n i => by
    rw [intervalIntegral.integral_of_le (htle n i)]; rfl
  have hdX : ∀ n i, i ≤ n → x (gridPt T n (i + 1)) ω - x (gridPt T n i) ω =
      (∫ s in gridPt T n i..gridPt T n (i + 1), a s ω) +
        itoIncr W 𝓕 P b (gridPt T n i) (gridPt T n (i + 1)) ω := by
    intro n i hi
    have h1 := hgr n (i + 1) (by omega)
    have h2 := hgr n i (by omega)
    simp only [htp] at h1 h2
    rw [h1, h2]
    have e := intervalIntegral.integral_interval_sub_left
      (hac.intervalIntegrable (μ := volume) 0 (gridPt T n (i + 1)))
      (hac.intervalIntegrable (μ := volume) 0 (gridPt T n i))
    simp only [itoIncr]
    rw [← e]; ring
  have key := hF.ito_pathwise_gen hT hxc hac (hbc.pow 2)
    (y := fun n i => itoIncr W 𝓕 P b (gridPt T n i) (gridPt T n (i + 1)) ω) hdX hns
    (J := J ω) l1' (by
      refine l2.congr fun k => ?_
      simp only [hA2, hD, hk2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsq]) (by
      refine l3.congr fun k => ?_
      simp only [hA3, hD]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsq])
  have hJeq : (fun s ω => b s ω * Fx s (x s ω)) = fun u ω => g u ω * b u ω := by
    funext s ω; simp only [hg]; ring
  rw [hJeq]
  exact key

/-- **Itô's formula (4.3.14)** in Gardiner's time-independent form: for `f ∈ C²` with bounded
`f'`, `f''` and an Itô process `dx = a dt + b dW` with bounded `b`,
`f(x(T)) - f(x(0)) = ∫₀ᵀ (a f'(x) + ½ b² f''(x)) ds + ∫₀ᵀ b f'(x) dW` almost surely. -/
theorem IsFWiener.ito_formula_process_C2 {T B C1 C2 : ℝ} (hT : 0 < T) {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf''c : Continuous f'') (hf'b : ∀ y, |f' y| ≤ C1) (hf''b : ∀ y, |f'' y| ≤ C2)
    {x a b : ℝ → Ω → ℝ} (hx : IsItoProcess W 𝓕 P T x a b) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b u ω| ≤ B) :
    (fun ω => f (x T ω) - f (x 0 ω)) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, (a s ω * f' (x s ω) + b s ω ^ 2 / 2 * f'' (x s ω))) +
        itoInt W 𝓕 P T (fun s ω => b s ω * f' (x s ω)) ω := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr fun y => (hf' y).continuousAt
  have hF : IsC12 (fun _ y => f y) (fun _ _ => 0) (fun _ y => f' y) (fun _ y => f'' y) :=
    ⟨continuous_const, hf'c.comp continuous_snd, hf''c.comp continuous_snd,
      fun _ _ => hasDerivAt_const _ _, fun _ y => hf y, fun _ y => hf' y⟩
  have h := hW.ito_formula_process hT hF (fun _ y => hf'b y) (fun _ y => hf''b y) hx hB0 hB
  filter_upwards [h] with ω hω
  rw [hω]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [zero_add]

end Gardiner.Ito
