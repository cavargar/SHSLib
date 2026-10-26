/-
# Short-time behaviour of the Smoluchowski limit (Gardiner §6.4.3)

Gardiner, *Handbook of Stochastic Methods*, §6.4.3, (6.4.70)–(6.4.80).  In the time domain the
reduced equation (6.4.74) is the memory equation (6.4.78)

`q'(t) = K ∫₀ᵗ e^{γ(t'-t)} q(t') dt'`,

with `K = ∂_y(U' + ∂_y)` (here an arbitrary bounded operator on a Banach space `E`, the
interchange of `K` with the time integral being the only property used).

* `Gardiner.Adiabatic.hasDerivAt_memKernel`: the memory integral `m(t)` obeys `m' = q - γm`.
* (6.4.77) ⟺ (6.4.78): `Gardiner.Adiabatic.memory_to_telegraph` and
  `Gardiner.Adiabatic.telegraph_to_memory`: the memory equation is equivalent to the
  telegraph-type equation `γ⁻¹q'' + q' = γ⁻¹Kq` with `q'(0) = 0`.  The left side of (6.4.77)
  should read `∂²p̂/∂t²` (erratum: `p` printed).
* (6.4.79): `Gardiner.Adiabatic.memKernel_ibp`.
* (6.4.80) with explicit error: `Gardiner.Adiabatic.shortTime_bound`:
  `‖q'(t) - γ⁻¹K(q(t) - e^{-γt}q(0))‖ ≤ ‖K‖ M γ⁻²` whenever `‖q'‖ ≤ M` on `[0, t]`.  The printed
  (6.4.80) lacks the factor `γ⁻¹` on the right (erratum); with it, (6.4.80) is valid for all
  `t ≥ 0`, with the memory time `γ⁻¹` visible in `e^{-γt}`.
* Instance: `Gardiner.Adiabatic.shortTime_instance`, `E = ℝ`, `K = -2`, `γ = 3`,
  `q(t) = 2e^{-t} - e^{-2t}`.
-/
import SHSLib.Gardiner.Approx.ChemicalLNA

open Set MeasureTheory intervalIntegral

noncomputable section

namespace Gardiner.Adiabatic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The memory integral `m(t) = ∫₀ᵗ e^{γ(t'-t)} q(t') dt'` of (6.4.75), (6.4.78). -/
def memKernel (γ : ℝ) (q : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) • q s

omit [CompleteSpace E] in
lemma memKernel_eq (γ : ℝ) (q : ℝ → E) (t : ℝ) :
    memKernel γ q t = Real.exp (-γ * t) • ∫ s in (0 : ℝ)..t, Real.exp (γ * s) • q s := by
  rw [memKernel, ← intervalIntegral.integral_smul]
  congr 1; ext s
  rw [smul_smul, ← Real.exp_add]; congr 2; ring

/-- `m' = q - γm`. -/
theorem hasDerivAt_memKernel (γ : ℝ) {q : ℝ → E} (hq : Continuous q) (t : ℝ) :
    HasDerivAt (memKernel γ q) (q t - γ • memKernel γ q t) t := by
  have hcf : Continuous (fun s => Real.exp (γ * s) • q s) := by fun_prop
  have hI := (hcf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have he : HasDerivAt (fun t => Real.exp (-γ * t)) (-γ * Real.exp (-γ * t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-γ)).exp
  have := he.smul hI
  have hfun : memKernel γ q = fun t => Real.exp (-γ * t) • ∫ s in (0 : ℝ)..t,
      Real.exp (γ * s) • q s := funext (memKernel_eq γ q)
  rw [hfun]
  convert this using 1
  have h1 : Real.exp (-γ * t) • Real.exp (γ * t) • q t = q t := by
    rw [smul_smul, ← Real.exp_add, show -γ * t + γ * t = 0 by ring, Real.exp_zero,
      one_smul]
  rw [h1, neg_mul, neg_smul, sub_eq_add_neg]
  simp only [smul_smul]

/-- **(6.4.78) ⟹ (6.4.77)**: if `q' = K m` with `m` the memory integral, then
`γ⁻¹q'' + q' = γ⁻¹Kq` and `q'(0) = 0`. -/
theorem memory_to_telegraph {γ : ℝ} (hγ : γ ≠ 0) (K : E →L[ℝ] E) {q q' q'' : ℝ → E}
    (hq : ∀ t, HasDerivAt q (q' t) t) (hq' : ∀ t, HasDerivAt q' (q'' t) t)
    (hmem : ∀ t, q' t = K (memKernel γ q t)) (t : ℝ) :
    γ⁻¹ • q'' t + q' t = γ⁻¹ • K (q t) ∧ q' 0 = 0 := by
  have hc : Continuous q := continuous_iff_continuousAt.2 fun t => (hq t).continuousAt
  have hd : HasDerivAt q' (K (q t - γ • memKernel γ q t)) t := by
    have := (K.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_memKernel γ hc t))
    rw [show q' = fun t => K (memKernel γ q t) from funext hmem]
    exact this
  have h2 := (hq' t).unique hd
  refine ⟨?_, ?_⟩
  · rw [h2, map_sub, map_smul, hmem t, smul_sub, smul_smul, inv_mul_cancel₀ hγ, one_smul]
    abel
  · rw [hmem 0, memKernel, intervalIntegral.integral_same, map_zero]

/-- **(6.4.77) ⟹ (6.4.78)**: conversely, a solution of `γ⁻¹q'' + q' = γ⁻¹Kq` with `q'(0) = 0`
satisfies the memory equation. -/
theorem telegraph_to_memory {γ : ℝ} (hγ : γ ≠ 0) (K : E →L[ℝ] E) {q q' q'' : ℝ → E}
    (hq : ∀ t, HasDerivAt q (q' t) t) (hq' : ∀ t, HasDerivAt q' (q'' t) t)
    (htel : ∀ t, γ⁻¹ • q'' t + q' t = γ⁻¹ • K (q t)) (h0 : q' 0 = 0) (t : ℝ) :
    q' t = K (memKernel γ q t) := by
  have hc : Continuous q := continuous_iff_continuousAt.2 fun t => (hq t).continuousAt
  set r : ℝ → E := fun t => q' t - K (memKernel γ q t)
  have hr : ∀ t, HasDerivAt r ((-γ • ContinuousLinearMap.id ℝ E) (r t) + 0) t := by
    intro t
    have h1 := (hq' t).sub (K.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_memKernel γ hc t))
    convert h1 using 1
    have e : q'' t = K (q t) - γ • q' t := by
      have := congrArg (fun v => γ • v) (htel t)
      simp only [smul_add, smul_smul, mul_inv_cancel₀ hγ, one_smul] at this
      rw [← this]; abel
    simp only [r, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, add_zero,
      map_sub, map_smul, e]
    rw [neg_smul, neg_smul]; abel
  have hz : ∀ t : ℝ, HasDerivAt (fun _ => (0 : E))
      (((-γ : ℝ) • ContinuousLinearMap.id ℝ E) 0 + 0) t :=
    fun t => by simp only [map_zero, add_zero]; exact hasDerivAt_const t (0 : E)
  have := vec_linear_ode_unique ((-γ : ℝ) • ContinuousLinearMap.id ℝ E) (fun _ => (0 : E)) r
    (fun _ => (0 : E))
    hr hz (by
    simp [r, h0, memKernel])
  have := congrFun this t
  simp only [r, sub_eq_zero] at this
  exact this

/-- **(6.4.79)**: integration by parts in the memory integral. -/
theorem memKernel_ibp {γ : ℝ} (hγ : γ ≠ 0) {q q' : ℝ → E} (hq : ∀ t, HasDerivAt q (q' t) t)
    (hq'c : Continuous q') (t : ℝ) :
    memKernel γ q t = γ⁻¹ • (q t - Real.exp (-γ * t) • q 0)
      - γ⁻¹ • ∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) • q' s := by
  have hderiv : ∀ s, HasDerivAt (fun s => Real.exp (γ * (s - t)) • q s)
      (γ • (Real.exp (γ * (s - t)) • q s) + Real.exp (γ * (s - t)) • q' s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (γ * (s - t))) (Real.exp (γ * (s - t)) * γ) s := by
      simpa using (((hasDerivAt_id s).sub_const t).const_mul γ).exp
    convert he.smul (hq s) using 1
    rw [smul_smul, mul_comm, add_comm]
  have hc : Continuous q := continuous_iff_continuousAt.2 fun t => (hq t).continuousAt
  have hcont1 : Continuous fun s => Real.exp (γ * (s - t)) • q s := by fun_prop
  have hcont2 : Continuous fun s => Real.exp (γ * (s - t)) • q' s := by fun_prop
  have hcont3 : Continuous fun s => γ • (Real.exp (γ * (s - t)) • q s)
      + Real.exp (γ * (s - t)) • q' s := by fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ => hderiv s) (hcont3.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_add ((hcont1.const_smul γ).intervalIntegrable 0 t)
    (hcont2.intervalIntegrable 0 t), intervalIntegral.integral_smul] at hftc
  simp only [sub_self, mul_zero, Real.exp_zero, one_smul, zero_sub] at hftc
  have e : memKernel γ q t = ∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) • q s := rfl
  have hI : γ • (∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) • q s)
      = q t - Real.exp (-γ * t) • q 0 - ∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) • q' s := by
    rw [show -γ * t = γ * -t by ring, ← hftc]; abel
  rw [e, ← smul_sub, ← hI, smul_smul, inv_mul_cancel₀ hγ, one_smul]

lemma integral_exp_kernel {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) = (1 - Real.exp (-γ * t)) / γ := by
  have h : ∀ s, HasDerivAt (fun s => Real.exp (γ * (s - t)) / γ) (Real.exp (γ * (s - t))) s := by
    intro s
    have := ((((hasDerivAt_id s).sub_const t).const_mul γ).exp).div_const γ
    convert this using 1; field_simp; simp
  have hc : Continuous fun s => Real.exp (γ * (s - t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => h s) (hc.intervalIntegrable _ _)]
  rw [show γ * (0 - t) = -γ * t by ring]
  simp; ring

/-- **(6.4.80), corrected, with an explicit `O(γ⁻²)` error, valid for all `t ≥ 0`.**  If `q`
solves the memory equation (6.4.78) and `‖q'‖ ≤ M` on `[0, t]`, then
`‖q'(t) - γ⁻¹K(q(t) - e^{-γt}q(0))‖ ≤ ‖K‖ M / γ²`. -/
theorem shortTime_bound {γ : ℝ} (hγ : 0 < γ) (K : E →L[ℝ] E) {q q' : ℝ → E}
    (hq : ∀ t, HasDerivAt q (q' t) t) (hq'c : Continuous q')
    (hmem : ∀ t, q' t = K (memKernel γ q t)) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ s ∈ Icc 0 t, ‖q' s‖ ≤ M) :
    ‖q' t - γ⁻¹ • K (q t - Real.exp (-γ * t) • q 0)‖ ≤ ‖K‖ * M / γ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  rw [hmem t, memKernel_ibp hγ.ne' hq hq'c t, map_sub, map_smul, map_smul, sub_sub_cancel_left,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hγ]
  have hint : ‖∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) • q' s‖
      ≤ ∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) * M := by
    refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ ?_
    · refine Filter.Eventually.of_forall fun s hs => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hM s ⟨hs.1.le, hs.2⟩) (Real.exp_pos _).le
    · have hc : Continuous fun s => Real.exp (γ * (s - t)) * M := by fun_prop
      exact hc.intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_const, integral_exp_kernel hγ t] at hint
  have h1 : (1 - Real.exp (-γ * t)) / γ * M ≤ M / γ := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hγ]
    have := Real.exp_pos (-γ * t)
    nlinarith
  calc γ⁻¹ * ‖K (∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) • q' s)‖
      ≤ γ⁻¹ * (‖K‖ * (M / γ)) := by
        gcongr
        exact (K.le_opNorm _).trans (by gcongr; exact hint.trans h1)
    _ = ‖K‖ * M / γ ^ 2 := by field_simp

/-- **Instance**: `E = ℝ`, `K = -2` (i.e. `Kv = -2v`), `γ = 3`, `q(t) = 2e^{-t} - e^{-2t}` solves
`γ⁻¹q'' + q' = γ⁻¹Kq` with `q'(0) = 0`, hence the memory equation (6.4.78), and satisfies the
corrected short-time equation (6.4.80) up to `‖K‖M/γ² = 4/9` for all `t ≥ 0`. -/
theorem shortTime_instance {t : ℝ} (ht : 0 ≤ t) :
    let q : ℝ → ℝ := fun t => 2 * Real.exp (-t) - Real.exp (-2 * t)
    let q' : ℝ → ℝ := fun t => -2 * Real.exp (-t) + 2 * Real.exp (-2 * t)
    (∀ s, q' s = (-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ (memKernel 3 q s)) ∧ q' 0 = 0 ∧
      ‖q' t - (3 : ℝ)⁻¹ • ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
          (q t - Real.exp (-3 * t) • q 0)‖ ≤ 4 / 9 := by
  intro q q'
  have hexp : ∀ c s : ℝ, HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * s)) s :=
    fun c s => by simpa [mul_comm] using ((hasDerivAt_id s).const_mul c).exp
  have hq : ∀ s, HasDerivAt q (q' s) s := fun s => by
    have := ((hexp (-1) s).const_mul 2).sub (hexp (-2) s)
    convert this using 1
    · funext y; simp only [q, Pi.sub_apply, neg_mul, one_mul]
    · simp only [q', neg_mul, one_mul]; ring
  set q'' : ℝ → ℝ := fun s => 2 * Real.exp (-s) - 4 * Real.exp (-2 * s)
  have hq' : ∀ s, HasDerivAt q' (q'' s) s := fun s => by
    have := ((hexp (-1) s).const_mul (-2)).add ((hexp (-2) s).const_mul 2)
    convert this using 1
    · funext y; simp only [q', Pi.add_apply, neg_mul, one_mul]
    · simp only [q'', neg_mul, one_mul]; ring
  have hmem := fun s => telegraph_to_memory (E := ℝ) (by norm_num : (3 : ℝ) ≠ 0)
    ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) hq hq'
    (fun s => by simp only [q, q', q'', ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]; ring) (by simp [q']) s
  refine ⟨hmem, (memory_to_telegraph (by norm_num : (3 : ℝ) ≠ 0) _ hq hq' hmem 0).2, ?_⟩
  have hc : Continuous q' := by fun_prop
  have hb := shortTime_bound (by norm_num : (0 : ℝ) < 3) ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    hq hc hmem ht (M := 2) (fun s hs => by
      simp only [q', Real.norm_eq_abs]
      have h1 : Real.exp (-2 * s) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith [hs.1])
      have h2 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hs.1])
      have h3 := Real.exp_pos (-2 * s)
      rw [abs_le]; constructor <;> nlinarith)
  have hK : ‖(-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ ≤ 2 := by
    refine (norm_smul_le (-2 : ℝ) (ContinuousLinearMap.id ℝ ℝ)).trans ?_
    have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)
    rw [Real.norm_eq_abs]; norm_num; linarith
  refine hb.trans ?_
  have : ‖(-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ * 2 / 3 ^ 2 ≤ 2 * 2 / 3 ^ 2 := by gcongr
  linarith

end Gardiner.Adiabatic
