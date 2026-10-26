/-
# Square-integrable initial factors and GBM with an unbounded initial value

`Gardiner.Ito.itoInt_mul_left` takes a *bounded* `𝓕 0`-measurable factor out of the Itô integral.
Here the boundedness is removed: if `Z` is `𝓕 0`-measurable and `Z G` is again an Itô integrand,
then `∫₀ᵀ Z G dW = Z ∫₀ᵀ G dW` a.s. (`Gardiner.Ito.itoInt_mul_left_of_isItoIntegrand`).  The proof
truncates `Z` and passes to the limit with the Itô isometry and dominated convergence.

As an application, geometric Brownian motion solves `dx = λx dt + μx dW` for every square-integrable
initial value `x₀` independent of `W` (`Gardiner.Ito.IsFWiener.geomBM_ito_of_memLp`), which is
Gardiner's setting in §4.4.2.
-/
import SHSLib.Gardiner.Ito.Calculus.GBM

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A mean-square limit agrees a.e. with a pointwise a.e. limit. -/
lemma ae_eq_of_l2_of_ae_tendsto {X : ℕ → α → ℝ} {Y Z : α → ℝ} (hX : ∀ n, MemLp (X n) 2 μ)
    (hY : MemLp Y 2 μ) (h1 : Tendsto (fun n => ∫ a, (X n a - Y a) ^ 2 ∂μ) atTop (𝓝 0))
    (h2 : ∀ᵐ a ∂μ, Tendsto (fun n => X n a) atTop (𝓝 (Z a))) : Y =ᵐ[μ] Z := by
  have hL := l2_tendsto_toLp hX hY h1
  have hm : TendstoInMeasure μ X atTop Y := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun n => (hX n).aestronglyMeasurable) hY.aestronglyMeasurable ?_
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (p := 2) X hX Y hY).mp hL
  obtain ⟨ns, hns, hlim⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hlim, h2] with a ha hb
  exact tendsto_nhds_unique ha (hb.comp hns.tendsto_atTop)

/-- Truncation of a real number to `[-k, k]`. -/
def truncAt (k : ℕ) (z : ℝ) : ℝ := max (-(k : ℝ)) (min k z)

lemma continuous_truncAt (k : ℕ) : Continuous (truncAt k) := by
  unfold truncAt; fun_prop

lemma abs_truncAt_le (k : ℕ) (z : ℝ) : |truncAt k z| ≤ k := by
  unfold truncAt; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith) (min_le_left _ _)

lemma truncAt_eq_of_abs_le {k : ℕ} {z : ℝ} (h : |z| ≤ k) : truncAt k z = z := by
  unfold truncAt; rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma abs_truncAt_sub_le (k : ℕ) (z : ℝ) : |truncAt k z - z| ≤ |z| := by
  unfold truncAt
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  simp only [max_def, min_def]
  split_ifs <;> rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, abs_le] <;>
    constructor <;> linarith

lemma tendsto_truncAt (z : ℝ) : Tendsto (fun k : ℕ => truncAt k z) atTop (𝓝 z) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |z|
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  exact (truncAt_eq_of_abs_le (hN.trans (by exact_mod_cast hk))).symm

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- **`𝓕 0`-measurable factors can be taken out of the Itô integral**: if `Z` is
`𝓕 0`-measurable (e.g. a random initial value independent of `W`) and both `G` and `Z G` are Itô
integrands on `[0, T]`, then `∫₀ᵀ Z G dW = Z ∫₀ᵀ G dW` almost surely.  No boundedness of `Z` is
needed. -/
theorem itoInt_mul_left_of_isItoIntegrand {T : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 0] Z)
    (hZG : IsItoIntegrand 𝓕 P T (fun t ω => Z ω * G t ω)) :
    itoInt W 𝓕 P T (fun t ω => Z ω * G t ω) =ᵐ[P] fun ω => Z ω * itoInt W 𝓕 P T G ω := by
  have := hW.isProbabilityMeasure
  set Zk : ℕ → Ω → ℝ := fun k ω => truncAt k (Z ω) with hZk_def
  have hZk : ∀ k, StronglyMeasurable[𝓕 0] (Zk k) := fun k =>
    (continuous_truncAt k).comp_stronglyMeasurable hZ
  have hb : ∀ k ω, |Zk k ω| ≤ k := fun k ω => abs_truncAt_le k (Z ω)
  have hkG : ∀ k, IsItoIntegrand 𝓕 P T (fun t ω => Zk k ω * G t ω) := fun k =>
    isItoIntegrand_mul_left hG (hZk k) (hb k)
  have hk : ∀ k, itoInt W 𝓕 P T (fun t ω => Zk k ω * G t ω) =ᵐ[P]
      fun ω => Zk k ω * itoInt W 𝓕 P T G ω := fun k => itoInt_mul_left hW hG (hZk k) (hb k)
  refine ae_eq_of_l2_of_ae_tendsto (fun k => memLp_itoInt hW (hkG k)) (memLp_itoInt hW hZG)
    ?_ ?_
  · -- mean-square convergence via the isometry and dominated convergence
    have e : ∀ k, ∫ ω, (itoInt W 𝓕 P T (fun t ω => Zk k ω * G t ω) ω -
        itoInt W 𝓕 P T (fun t ω => Z ω * G t ω) ω) ^ 2 ∂P =
        ∫ p, (Zk k p.2 * G p.1 p.2 - Z p.2 * G p.1 p.2) ^ 2 ∂(tsMeasure P T) := by
      intro k
      have hs := itoInt_sub hW (hkG k) hZG
      have hs2 : (fun ω => itoInt W 𝓕 P T (fun t ω => Zk k ω * G t ω - Z ω * G t ω) ω ^ 2)
          =ᵐ[P] fun ω => (itoInt W 𝓕 P T (fun t ω => Zk k ω * G t ω) ω -
            itoInt W 𝓕 P T (fun t ω => Z ω * G t ω) ω) ^ 2 := hs.mono fun ω hω => by simp only at hω ⊢; rw [hω]
      rw [← integral_congr_ae hs2,
        itoInt_sq hW ((hkG k).sub hZG), ← integral_sq_tsMeasure ((hkG k).sub hZG).memLp]
      rfl
    simp_rw [e]
    have hlim := tendsto_integral_of_dominated_convergence
      (μ := tsMeasure P T)
      (F := fun (k : ℕ) (p : ℝ × Ω) => (Zk k p.2 * G p.1 p.2 - Z p.2 * G p.1 p.2) ^ 2)
      (f := fun _ => 0) (fun p => (Z p.2 * G p.1 p.2) ^ 2)
      (fun k => ((hkG k).sub hZG).memLp.integrable_sq.aestronglyMeasurable)
      hZG.memLp.integrable_sq ?_ ?_
    · simpa using hlim
    · intro k
      refine Eventually.of_forall fun p => ?_
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sub_mul, mul_pow, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [← sq_abs, ← sq_abs (Z p.2)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncAt_sub_le k (Z p.2)) 2
    · refine Eventually.of_forall fun p => ?_
      have : Tendsto (fun k : ℕ => (Zk k p.2 * G p.1 p.2 - Z p.2 * G p.1 p.2) ^ 2) atTop
          (𝓝 ((Z p.2 * G p.1 p.2 - Z p.2 * G p.1 p.2) ^ 2)) :=
        (((tendsto_truncAt (Z p.2)).mul_const _).sub_const _).pow 2
      simpa using this
  · filter_upwards [ae_all_iff.2 hk] with ω hω
    simp_rw [hω]
    exact (tendsto_truncAt (Z ω)).mul_const _

/-- `c x(t)` is an Itô integrand on `[0, T]` for geometric Brownian motion with a
square-integrable `𝓕 0`-measurable initial value. -/
lemma IsFWiener.isItoIntegrand_geomBM_of_memLp (hWj : Measurable (Function.uncurry W)) (T lam mu c : ℝ)
    {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) (hx02 : MemLp x0 2 P) :
    IsItoIntegrand 𝓕 P T (fun s ω => c * geomBM lam mu x0 W s ω) := by
  have := hW.isProbabilityMeasure
  have hx0m : Measurable x0 := (hx0.mono (𝓕.le 0)).measurable
  refine isItoIntegrand_of_msBounded ?_ (fun t ht _ => ?_) ?_
  · have hc : Continuous fun p : ℝ × ℝ => Real.exp ((lam - mu ^ 2 / 2) * p.1 + mu * p.2) := by
      fun_prop
    have h2 : Measurable fun p : ℝ × Ω => Real.exp ((lam - mu ^ 2 / 2) * p.1 + mu * W p.1 p.2) :=
      hc.measurable.comp (measurable_fst.prodMk hWj)
    exact measurable_const.mul ((hx0m.comp measurable_snd).mul h2)
  · exact stronglyMeasurable_const.mul (hW.geomBM_sm hx0 ht)
  · refine ⟨c ^ 2 * ((∫ ω, x0 ω ^ 2 ∂P) * Real.exp (|2 * lam + mu ^ 2| * T)), fun t ht => ?_⟩
    obtain ⟨hi, he⟩ := hW.integral_geomBM_sq lam mu hx0 hx02 ht.1
    have hsm : AEStronglyMeasurable (fun ω => c * geomBM lam mu x0 W t ω) P :=
      (stronglyMeasurable_const.mul ((hW.geomBM_sm hx0 ht.1).mono (𝓕.le t))).aestronglyMeasurable
    refine ⟨(memLp_two_iff_integrable_sq hsm).mpr ?_, ?_⟩
    · simpa [mul_pow] using hi.const_mul (c ^ 2)
    · simp_rw [mul_pow]
      rw [integral_const_mul, he]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
        (integral_nonneg fun _ => sq_nonneg _)) (sq_nonneg _)
      refine Real.exp_le_exp.mpr ?_
      calc (2 * lam + mu ^ 2) * t ≤ |2 * lam + mu ^ 2| * t :=
            mul_le_mul_of_nonneg_right (le_abs_self _) ht.1
        _ ≤ |2 * lam + mu ^ 2| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)

/-- **Geometric Brownian motion solves `dx = λx dt + μx dW` for every square-integrable initial
value independent of `W`** (Gardiner §4.4.2, (4.4.3)–(4.4.8)):
`x(T) - x₀ = ∫₀ᵀ λ x dt + ∫₀ᵀ μ x dW` a.s. for `𝓕 0`-measurable `x₀ ∈ L²`.  This removes the
boundedness assumption of `Gardiner.Ito.IsFWiener.geomBM_ito`. -/
theorem IsFWiener.geomBM_ito_of_memLp (hWj : Measurable (Function.uncurry W)) {T : ℝ}
    (hT : 0 < T) (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0)
    (hx02 : MemLp x0 2 P) :
    (fun ω => geomBM lam mu x0 W T ω - x0 ω) =ᵐ[P] fun ω =>
      (∫ s in (0 : ℝ)..T, lam * geomBM lam mu x0 W s ω) +
        itoInt W 𝓕 P T (fun s ω => mu * geomBM lam mu x0 W s ω) ω := by
  set d := lam - mu ^ 2 / 2 with hd
  have hF : IsC12 (fun t x => 1 * Real.exp (mu * x + d * t))
      (fun t x => d * (1 * Real.exp (mu * x + d * t)))
      (fun t x => mu * Real.exp (mu * x + d * t))
      (fun t x => mu ^ 2 * Real.exp (mu * x + d * t)) := by
    refine ⟨by fun_prop, by fun_prop, by fun_prop, fun t x => ?_, fun t x => ?_, fun t x => ?_⟩
    · have := (((hasDerivAt_id t).const_mul d).const_add (mu * x)).exp.const_mul 1
      convert this using 1; simp; ring
    · have := (((hasDerivAt_id x).const_mul mu).add_const (d * t)).exp.const_mul 1
      convert this using 1; simp; ring
    · have := (((hasDerivAt_id x).const_mul mu).add_const (d * t)).exp.const_mul mu
      convert this using 1; simp; ring
  have h := hW.ito_formula_W_growth hWj hT hF (expGrowth_exp mu mu d T)
    (expGrowth_exp (mu ^ 2) mu d T)
  have hG := hW.isItoIntegrand_expW hWj mu mu d T
  have hcongr : (fun s ω => mu * geomBM lam mu x0 W s ω) =
      fun s ω => x0 ω * (mu * Real.exp (mu * W s ω + d * s)) := by
    funext s ω; simp only [geomBM, hd]; ring_nf
  have hZG := hW.isItoIntegrand_geomBM_of_memLp hWj T lam mu mu hx0 hx02
  rw [hcongr] at hZG ⊢
  have hm := itoInt_mul_left_of_isItoIntegrand hW hG hx0 hZG
  filter_upwards [h, hm, hW.zero] with ω hω hmω h0
  rw [hmω]
  simp only [h0, mul_zero, zero_add, Real.exp_zero, one_mul] at hω
  have hT1 : geomBM lam mu x0 W T ω = x0 ω * Real.exp (mu * W T ω + d * T) := by
    simp only [geomBM, hd]; ring_nf
  have hI : ∫ s in (0 : ℝ)..T, lam * geomBM lam mu x0 W s ω =
      x0 ω * ∫ s in (0 : ℝ)..T, (d * Real.exp (mu * W s ω + d * s) +
        mu ^ 2 * Real.exp (mu * W s ω + d * s) / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [geomBM, hd]; ring_nf
  rw [hT1, hI]
  calc x0 ω * Real.exp (mu * W T ω + d * T) - x0 ω
      = x0 ω * (Real.exp (mu * W T ω + d * T) - 1) := by ring
    _ = _ := by rw [hω]; ring

end Gardiner.Ito
