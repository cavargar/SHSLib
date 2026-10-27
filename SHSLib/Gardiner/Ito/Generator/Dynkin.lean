/-
# Dynkin's formula and the martingale problem for Itô processes (Gardiner §4.3.4)

Let `x` be an Itô process on `[0, T]` (`Gardiner.Ito.IsItoProcess`) whose drift and noise
coefficients are `a(x(t), t)` and `b(x(t), t)`, with `|b(x(t), t)| ≤ B`, and let `f ∈ C²` have
bounded `f'`, `f''` (`C2BddDeriv`).  Then:

* `ito_formula_itoGen`: Itô's formula (4.3.14) in generator form,
  `f(x(t)) - f(x(0)) = ∫₀ᵗ L f(x(u), u) du + ∫₀ᵗ b f'(x) dW` a.s.;
* `dynkin` / `dynkin_zero`: **Dynkin's formula**
  `E f(x(t)) = E f(x(s)) + E ∫ₛᵗ L f(x(u), u) du` (integrated form of (4.3.18));
* `isMartingaleOn_itoDynkinProc`: **the martingale problem**, i.e.
  `f(x(t)) - f(x(0)) - ∫₀ᵗ L f(x(u), u) du` is a martingale on `[0, T]`;
* `martingale_itoDynkinProc_clamp`: if moreover every path of `x` is continuous and `a`, `b` are
  jointly continuous, the process stopped at `T` is a Mathlib `Martingale` (the form used by
  `SHSCat.GenPres.SolvesMartingaleProblem`).
-/
import SHSLib.Gardiner.Ito.Calculus.ItoGeneral
import SHSLib.Gardiner.Ito.Calculus.Martingale
import SHSLib.Gardiner.Ito.Generator.Basic

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.Generator

open Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ}

/-- An Itô process on `[0, T]` is an Itô process on every `[0, S]`, `S ≤ T`. -/
lemma isItoProcess_mono [SFinite P] {T S : ℝ} {x a b : ℝ → Ω → ℝ}
    (hx : IsItoProcess W 𝓕 P T x a b) (hST : S ≤ T) : IsItoProcess W 𝓕 P S x a b where
  measurable := hx.measurable
  adapted t h0 h1 := hx.adapted t h0 (h1.trans hST)
  cont := hx.cont
  drift_cont := hx.drift_cont
  noise := hx.noise.mono hST
  noise_cont := hx.noise_cont
  eq t h0 h1 := hx.eq t h0 (h1.trans hST)

/-- The **Itô process with state-dependent coefficients**: an Itô process whose drift and noise
coefficients are `a(x(t), t)` and `b(x(t), t)`. -/
abbrev IsItoDiffusion (W : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (T : ℝ)
    (a b : ℝ → ℝ → ℝ) (x : ℝ → Ω → ℝ) : Prop :=
  IsItoProcess W 𝓕 P T x (fun t ω => a (x t ω) t) (fun t ω => b (x t ω) t)

variable (hW : IsFWiener W 𝓕 P)
include hW

section Diffusion

variable {T B C1 C2 : ℝ} {a b : ℝ → ℝ → ℝ} {x : ℝ → Ω → ℝ} {f : ℝ → ℝ}

omit hW in
/-- The noise integrand `b(x(u), u) f'(x(u))` of Itô's formula is an Itô integrand. -/
lemma isItoIntegrand_noise (hx : IsItoDiffusion W 𝓕 P T a b x) (hf : C2BddDeriv f C1 C2) :
    IsItoIntegrand 𝓕 P T (fun u ω => b (x u ω) u * deriv f (x u ω)) := by
  have h := isItoIntegrand_mul_bdd (g := fun u ω => deriv f (x u ω)) (C := C1) hx.noise
    (hf.continuous_deriv.measurable.comp hx.measurable)
    (fun t h0 h1 => hf.continuous_deriv.comp_stronglyMeasurable (hx.adapted t h0 h1))
    (fun t ω => hf.bdd1 _)
  convert h using 1
  funext u ω
  ring

/-- **Itô's formula (4.3.14) in generator form**: for `0 ≤ t ≤ T`,
`f(x(t)) - f(x(0)) = ∫₀ᵗ L f(x(u), u) du + ∫₀ᵗ b(x(u), u) f'(x(u)) dW(u)` almost surely. -/
theorem ito_formula_itoGen (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    (fun ω => f (x t ω) - f (x 0 ω)) =ᵐ[P] fun ω =>
      (∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω)) +
        itoInt W 𝓕 P t (fun u ω => b (x u ω) u * deriv f (x u ω)) ω := by
  have := hW.isProbabilityMeasure
  have hxt := isItoProcess_mono hx htT
  rcases ht0.eq_or_lt with h0 | hpos
  · subst h0
    filter_upwards [itoInt_of_nonpos hW le_rfl (isItoIntegrand_noise hxt hf)] with ω hω
    simp [hω]
  exact hW.ito_formula_process_C2 hpos hf.hasDerivAt hf.hasDerivAt_deriv hf.continuous_deriv2
    hf.bdd1 hf.bdd2 hxt hB0 (fun u hu ω => hB u ⟨hu.1, hu.2.trans htT⟩ ω)

/-- The Dynkin process is almost surely the running Itô integral `∫₀ᵗ b f'(x) dW`. -/
theorem itoDynkinProc_ae_eq (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    itoDynkinProc a b f x t =ᵐ[P] itoInt W 𝓕 P t (fun u ω => b (x u ω) u * deriv f (x u ω)) := by
  filter_upwards [ito_formula_itoGen hW hx hB0 hB hf ht0 htT] with ω hω
  simp only [itoDynkinProc]
  linarith

/-- The Dynkin process at time `t ∈ [0, T]` is square integrable. -/
theorem memLp_itoDynkinProc (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) : MemLp (itoDynkinProc a b f x t) 2 P := by
  have := hW.isProbabilityMeasure
  exact (memLp_itoInt hW ((isItoIntegrand_noise hx hf).mono htT)).ae_eq
    (itoDynkinProc_ae_eq hW hx hB0 hB hf ht0 htT).symm

/-- **Dynkin's formula, compensated form**: `E[f(x(t)) - f(x(0)) - ∫₀ᵗ L f(x(u), u) du] = 0`
(no integrability hypothesis on `f(x(t))` is needed). -/
theorem integral_itoDynkinProc (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) : ∫ ω, itoDynkinProc a b f x t ω ∂P = 0 := by
  have := hW.isProbabilityMeasure
  rw [integral_congr_ae (itoDynkinProc_ae_eq hW hx hB0 hB hf ht0 htT)]
  exact itoInt_mean hW ((isItoIntegrand_noise hx hf).mono htT)

/-- The generator integral `∫₀ᵗ L f(x(u), u) du` is integrable when `f(x(0))`, `f(x(t))` are. -/
theorem integrable_genIntegral (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hi0 : Integrable (fun ω => f (x 0 ω)) P)
    (hit : Integrable (fun ω => f (x t ω)) P) :
    Integrable (fun ω => ∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω)) P := by
  have := hW.isProbabilityMeasure
  have hM := (memLp_itoDynkinProc hW hx hB0 hB hf ht0 htT).integrable one_le_two
  have : (fun ω => ∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω)) =
      fun ω => (f (x t ω) - f (x 0 ω)) - itoDynkinProc a b f x t ω := by
    funext ω; simp only [itoDynkinProc]; ring
  rw [this]
  exact (hit.sub hi0).sub hM

/-- **Dynkin's formula from time `0`**: `E f(x(t)) = E f(x(0)) + E ∫₀ᵗ L f(x(u), u) du`. -/
theorem dynkin_zero (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hi0 : Integrable (fun ω => f (x 0 ω)) P)
    (hit : Integrable (fun ω => f (x t ω)) P) :
    ∫ ω, f (x t ω) ∂P =
      ∫ ω, f (x 0 ω) ∂P + ∫ ω, (∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω)) ∂P := by
  have := hW.isProbabilityMeasure
  have hM := (memLp_itoDynkinProc hW hx hB0 hB hf ht0 htT).integrable one_le_two
  have h0 := integral_itoDynkinProc hW hx hB0 hB hf ht0 htT
  have hD := integrable_genIntegral hW hx hB0 hB hf ht0 htT hi0 hit
  simp only [itoDynkinProc] at h0
  have e1 : ∫ ω, (f (x t ω) - f (x 0 ω) - ∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω)) ∂P =
      ∫ ω, (f (x t ω) - f (x 0 ω)) ∂P - ∫ ω, (∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω)) ∂P :=
    integral_sub (hit.sub hi0) hD
  have e2 : ∫ ω, (f (x t ω) - f (x 0 ω)) ∂P = ∫ ω, f (x t ω) ∂P - ∫ ω, f (x 0 ω) ∂P :=
    integral_sub hit hi0
  linarith

omit hW in
/-- Almost every path of `u ↦ L f(x(u), u)` is continuous. -/
lemma ae_continuous_itoGen (hx : IsItoDiffusion W 𝓕 P T a b x) (hf : C2BddDeriv f C1 C2) :
    ∀ᵐ ω ∂P, Continuous fun u => itoGen a b f u (x u ω) := by
  filter_upwards [hx.cont, hx.drift_cont, hx.noise_cont] with ω hxc hac hbc
  exact (hac.mul (hf.continuous_deriv.comp hxc)).add
    (((hbc.pow 2).div_const 2).mul (hf.continuous_deriv2.comp hxc))

/-- **Dynkin's formula** (integrated form of Gardiner (4.3.18)): for `0 ≤ s ≤ t ≤ T`,
`E f(x(t)) = E f(x(s)) + E ∫ₛᵗ L f(x(u), u) du`. -/
theorem dynkin (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (hi0 : Integrable (fun ω => f (x 0 ω)) P)
    (his : Integrable (fun ω => f (x s ω)) P) (hit : Integrable (fun ω => f (x t ω)) P) :
    ∫ ω, f (x t ω) ∂P =
      ∫ ω, f (x s ω) ∂P + ∫ ω, (∫ u in s..t, itoGen a b f u (x u ω)) ∂P := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hDt := integrable_genIntegral hW hx hB0 hB hf ht0 htT hi0 hit
  have hDs := integrable_genIntegral hW hx hB0 hB hf hs0 (hst.trans htT) hi0 his
  have e : (fun ω => ∫ u in s..t, itoGen a b f u (x u ω)) =ᵐ[P] fun ω =>
      (∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω)) - ∫ u in (0 : ℝ)..s, itoGen a b f u (x u ω) := by
    filter_upwards [ae_continuous_itoGen hx hf] with ω hω
    exact (intervalIntegral.integral_interval_sub_left (hω.intervalIntegrable _ _)
      (hω.intervalIntegrable _ _)).symm
  rw [integral_congr_ae e, integral_sub hDt hDs, dynkin_zero hW hx hB0 hB hf ht0 htT hi0 hit,
    dynkin_zero hW hx hB0 hB hf hs0 (hst.trans htT) hi0 his]
  ring

/-- **The martingale problem**: `f(x(t)) - f(x(0)) - ∫₀ᵗ L f(x(u), u) du` is a martingale on
`[0, T]`. -/
theorem isMartingaleOn_itoDynkinProc (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2) :
    IsMartingaleOn (itoDynkinProc a b f x) 𝓕 P T := by
  have := hW.isProbabilityMeasure
  have hG := isItoIntegrand_noise hx hf
  refine ⟨fun t ht => (memLp_itoDynkinProc hW hx hB0 hB hf ht.1 ht.2).integrable one_le_two,
    fun t ht => ⟨_, itoInt_stronglyMeasurable hW (hG.mono ht.2),
      itoDynkinProc_ae_eq hW hx hB0 hB hf ht.1 ht.2⟩, fun s t hs hst htT => ?_⟩
  calc P[itoDynkinProc a b f x t | 𝓕 s]
      =ᵐ[P] P[itoInt W 𝓕 P t (fun u ω => b (x u ω) u * deriv f (x u ω)) | 𝓕 s] :=
        condExp_congr_ae (itoDynkinProc_ae_eq hW hx hB0 hB hf (hs.trans hst) htT)
    _ =ᵐ[P] itoInt W 𝓕 P s (fun u ω => b (x u ω) u * deriv f (x u ω)) :=
        condExp_itoInt hW hst (hG.mono htT)
    _ =ᵐ[P] itoDynkinProc a b f x s :=
        (itoDynkinProc_ae_eq hW hx hB0 hB hf hs (hst.trans htT)).symm

end Diffusion

end Gardiner.Ito.Generator

namespace Gardiner.Ito.Generator

open Gardiner.Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

/-- A martingale on `[0, T]` that is adapted on `[0, T]` and vanishes at `0` becomes, after
stopping at `T` (and freezing at `0` for negative times), a Mathlib `Martingale` indexed by `ℝ`. -/
theorem IsMartingaleOn.martingale_clamp [IsFiniteMeasure P] {M : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hM : IsMartingaleOn M 𝓕 P T) (hMa : ∀ t ∈ Icc (0 : ℝ) T, StronglyMeasurable[𝓕 t] (M t))
    (hM0 : ∀ ω, M 0 ω = 0) :
    Martingale (fun t => M (max 0 (min t T))) 𝓕 P := by
  have hc : ∀ t, max 0 (min t T) ∈ Icc (0 : ℝ) T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hz : M 0 = 0 := funext hM0
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · rcases le_or_gt 0 t with ht | ht
    · refine (hMa _ (hc t)).mono (𝓕.mono ?_)
      exact max_le ht (min_le_left _ _)
    · have : max 0 (min t T) = 0 := max_eq_left ((min_le_left _ _).trans ht.le)
      show StronglyMeasurable[𝓕 t] (M (max 0 (min t T)))
      rw [this, hz]
      exact stronglyMeasurable_const
  · show P[M (max 0 (min t T)) | 𝓕 s] =ᵐ[P] M (max 0 (min s T))
    have hct := hc t
    rcases lt_or_ge s 0 with hs | hs
    · have e : max 0 (min s T) = 0 := max_eq_left ((min_le_left _ _).trans hs.le)
      rw [e, hz]
      calc P[M (max 0 (min t T)) | 𝓕 s]
          =ᵐ[P] P[P[M (max 0 (min t T)) | 𝓕 0] | 𝓕 s] :=
            (condExp_condExp_of_le (𝓕.mono hs.le) (𝓕.le 0)).symm
        _ =ᵐ[P] P[M 0 | 𝓕 s] := condExp_congr_ae (hM.condExp_eq 0 _ le_rfl hct.1 hct.2)
        _ = 0 := by rw [hz]; exact condExp_zero
    rcases le_or_gt s T with hsT | hsT
    · have e : max 0 (min s T) = s := by rw [min_eq_left hsT, max_eq_right hs]
      rw [e]
      exact hM.condExp_eq s _ hs (le_max_of_le_right (le_min hst hsT)) hct.2
    · have e1 : max 0 (min s T) = T := by rw [min_eq_right hsT.le, max_eq_right hT]
      have e2 : max 0 (min t T) = T := by
        rw [min_eq_right (hsT.le.trans hst), max_eq_right hT]
      rw [e1, e2]
      exact (condExp_of_stronglyMeasurable (𝓕.le s) ((hMa T ⟨hT, le_rfl⟩).mono (𝓕.mono hsT.le))
        (hM.integrable T ⟨hT, le_rfl⟩)).eventuallyEq

variable {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

omit hW in
/-- If every path of `x` is continuous and `a`, `b` are jointly continuous, the Dynkin process
at `t ∈ [0, T]` is `𝓕 t`-measurable (the generator integral is a limit of Riemann sums). -/
theorem stronglyMeasurable_itoDynkinProc {T C1 C2 : ℝ} {a b : ℝ → ℝ → ℝ} {x : ℝ → Ω → ℝ}
    {f : ℝ → ℝ} (hxa : ∀ t, 0 ≤ t → t ≤ T → StronglyMeasurable[𝓕 t] (x t))
    (hxc : ∀ ω, Continuous fun t => x t ω) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) (hf : C2BddDeriv f C1 C2) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) : StronglyMeasurable[𝓕 t] (itoDynkinProc a b f x t) := by
  have hL : Continuous fun p : ℝ × ℝ => itoGen a b f p.1 p.2 := by
    unfold itoGen
    have ha' : Continuous fun p : ℝ × ℝ => a p.2 p.1 := ha.comp continuous_swap
    have hb' : Continuous fun p : ℝ × ℝ => b p.2 p.1 := hb.comp continuous_swap
    exact (ha'.mul (hf.continuous_deriv.comp continuous_snd)).add
      (((hb'.pow 2).div_const 2).mul (hf.continuous_deriv2.comp continuous_snd))
  have hgu : ∀ u, 0 ≤ u → u ≤ t → StronglyMeasurable[𝓕 t] fun ω => itoGen a b f u (x u ω) :=
    fun u h0 h1 => ((hL.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
      (hxa u h0 (h1.trans htT))).mono (𝓕.mono h1)
  have hD : StronglyMeasurable[𝓕 t] fun ω => ∫ u in (0 : ℝ)..t, itoGen a b f u (x u ω) := by
    refine stronglyMeasurable_of_tendsto (f := fun (n : ℕ) ω => ∑ i ∈ Finset.range (n + 1),
      itoGen a b f (gridPt t n i) (x (gridPt t n i) ω) * (t / (n + 1))) atTop (fun n => ?_) ?_
    · have := Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun i hi =>
        (hgu _ (gridPt_nonneg ht0 n i)
          (gridPt_le (n := n) (i := i) ht0 (Finset.mem_range.mp hi).le)).mul_const (t / (n + 1))
      convert this using 1
      funext ω
      simp
    · rw [tendsto_pi_nhds]
      intro ω
      exact riemannSum_tendsto ht0 (hL.comp (continuous_id.prodMk (hxc ω)))
  have h0 := hxa 0 le_rfl (ht0.trans htT)
  exact ((hf.continuous.comp_stronglyMeasurable (hxa t ht0 htT)).sub
    ((hf.continuous.comp_stronglyMeasurable h0).mono (𝓕.mono ht0))).sub hD

/-- **The martingale problem, Mathlib form**: if every path of `x` is continuous and `a`, `b`
are jointly continuous, then `t ↦ f(x(t∧T)) - f(x(0)) - ∫₀^{t∧T} L f(x(u), u) du` (frozen at `0`
for `t < 0`) is an `𝓕`-martingale. -/
theorem martingale_itoDynkinProc_clamp {T B C1 C2 : ℝ} (hT : 0 ≤ T) {a b : ℝ → ℝ → ℝ}
    {x : ℝ → Ω → ℝ} {f : ℝ → ℝ} (hx : IsItoDiffusion W 𝓕 P T a b x) (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, |b (x u ω) u| ≤ B) (hf : C2BddDeriv f C1 C2)
    (hxc : ∀ ω, Continuous fun t => x t ω) (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b)) :
    Martingale (fun t => itoDynkinProc a b f x (max 0 (min t T))) 𝓕 P := by
  have := hW.isProbabilityMeasure
  exact (isMartingaleOn_itoDynkinProc hW hx hB0 hB hf).martingale_clamp hT
    (fun t ht => stronglyMeasurable_itoDynkinProc hx.adapted hxc ha hb hf ht.1 ht.2)
    (itoDynkinProc_zero a b f x)

end Gardiner.Ito.Generator
