/-
# Diffusion in a double well: small-`D` asymptotics with error terms

Gardiner, *Handbook of Stochastic Methods*, §9.1.2 (9.1.4)–(9.1.8), §9.1.4 (9.1.11)–(9.1.13) and
§9.2.1 d) (9.2.18)–(9.2.25), for the Smoluchowski equation (9.1.1)
`∂ₜp = ∂ₓ[U'(x)p] + D∂ₓ²p` with stationary density `p_s = 𝒩 e^{-U/D}` (9.1.2), where `U` has
minima `a < c` (curvatures `k_a`, `k_c`) and a barrier top `b` between them (curvature `-k_b`).

Everything is proved with an explicit relative error `O(√D)`:

* `Gardiner.Escape.normalization_asymp` — **(9.1.6)**:
  `𝒩⁻¹ = [e^{-U(a)/D}√(2πD/k_a) + e^{-U(c)/D}√(2πD/k_c)](1 + O(√D))`;
* `Gardiner.Escape.population_ratio_asymp` — **(9.2.23)**:
  `n_a/n_c = √(k_c/k_a) e^{(U(c)-U(a))/D}(1 + O(√D))`;
* `Gardiner.Escape.population_small` — **(9.1.7)–(9.1.8)**: if `U(a) > U(c)` the population of
  the upper well is exponentially small, `n_a ≤ C e^{-(U(a)-U(c))/D}`;
* `Gardiner.Escape.barrier_integral_asymp` — **(9.1.13)** (with `𝒩` divided out):
  `∫_a^c e^{U/D} = √(2πD/k_b) e^{U(b)/D}(1 + O(√D))`;
* `Gardiner.Escape.relaxTime_asymp` — **(9.2.24)–(9.2.25)**: the relaxation time (9.2.18)
  `τ_r = n_a n_c D⁻¹ ∫_a^c p_s⁻¹` satisfies `τ_r = 2π H(b; a, c) √(n_a n_c) (1 + O(√D))`.

The hypotheses are bundled in `Gardiner.Escape.TwoWellHyp`.
-/
import SHSLib.Gardiner.Escape.Kramers

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-- Hypotheses for a double well: minima `a < c` with curvatures `ka, kc`, barrier top `b`
between them with curvature `-kb`, quantitative Taylor bounds on `|s| ≤ r`, separation `η` of
each critical value from the values of `U` away from it, and integrability of `e^{-U}`. -/
structure TwoWellHyp (U : ℝ → ℝ) (a b c : ℝ) where
  /-- radius of the Taylor windows -/
  r : ℝ
  /-- `U''(a)` -/
  ka : ℝ
  /-- `|U''(b)|` -/
  kb : ℝ
  /-- `U''(c)` -/
  kc : ℝ
  /-- cubic Taylor constant -/
  M : ℝ
  /-- separation -/
  η : ℝ
  cont : Continuous U
  hr : 0 < r
  hka : 0 < ka
  hkb : 0 < kb
  hkc : 0 < kc
  hM : 0 ≤ M
  hMra : M * r ≤ ka / 4
  hMrb : M * r ≤ kb / 4
  hMrc : M * r ≤ kc / 4
  hη : 0 < η
  taylor_a : ∀ s, |s| ≤ r → |U (a + s) - U a - ka / 2 * s ^ 2| ≤ M * |s| ^ 3
  taylor_b : ∀ s, |s| ≤ r → |U b - U (b + s) - kb / 2 * s ^ 2| ≤ M * |s| ^ 3
  taylor_c : ∀ s, |s| ≤ r → |U (c + s) - U c - kc / 2 * s ^ 2| ≤ M * |s| ^ 3
  sep_ab : a + r ≤ b - r
  sep_bc : b + r ≤ c - r
  well_a : ∀ z ≤ b, r ≤ |z - a| → U a + η ≤ U z
  well_c : ∀ z, b ≤ z → r ≤ |z - c| → U c + η ≤ U z
  barrier : ∀ z ∈ Icc a c, r ≤ |z - b| → U z + η ≤ U b
  integrable : Integrable (fun z => exp (-U z))

/-- `𝒩⁻¹ = ∫ e^{-U/D}`, the inverse normalisation of (9.1.2). -/
def normInt (U : ℝ → ℝ) (D : ℝ) : ℝ := ∫ x, exp (-U x / D)

/-- `𝒩⁻¹ n_a = ∫_{-∞}^b e^{-U/D}` (the unnormalised population of the left well (9.2.4)). -/
def popA (U : ℝ → ℝ) (D b : ℝ) : ℝ := ∫ x in Iic b, exp (-U x / D)

/-- `𝒩⁻¹ n_c = ∫_b^∞ e^{-U/D}`. -/
def popC (U : ℝ → ℝ) (D b : ℝ) : ℝ := ∫ x in Ioi b, exp (-U x / D)

/-- The relaxation time (9.2.18), `τ_r = n_a n_c D⁻¹ ∫_a^c p_s(x)⁻¹ dx`, with
`p_s = 𝒩 e^{-U/D}`, `n_a = 𝒩 popA`, `n_c = 𝒩 popC`. -/
def relaxTime (U : ℝ → ℝ) (D a b c : ℝ) : ℝ :=
  (popA U D b / normInt U D) * (popC U D b / normInt U D) *
    (normInt U D * ∫ x in a..c, exp (U x / D)) / D

/-- The factor `H(b; a, c)` of (9.2.25). -/
def Hfac (ka kb kc Ua Ub Uc D : ℝ) : ℝ :=
  (√kb)⁻¹ * (√(√(ka * kc)))⁻¹ * exp ((2 * Ub - Ua - Uc) / (2 * D))

/-! ### Elementary relative-error algebra -/

lemma div_rate {x y e₁ e₂ : ℝ} (hx : |x - 1| ≤ e₁) (hy : |y - 1| ≤ e₂) (he₂ : e₂ ≤ 1 / 2) :
    |x / y - 1| ≤ 2 * (e₁ + e₂) := by
  have hy' := abs_le.mp hy
  have hy0 : 1 / 2 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have hxy : |x - y| ≤ e₁ + e₂ := by
    calc |x - y| = |(x - 1) - (y - 1)| := by ring_nf
      _ ≤ |x - 1| + |y - 1| := abs_sub _ _
      _ ≤ e₁ + e₂ := add_le_add hx hy
  have he : 0 ≤ e₁ + e₂ := le_trans (abs_nonneg _) hxy
  rw [div_sub_one hypos.ne', abs_div, abs_of_pos hypos, div_le_iff₀ hypos]
  nlinarith

lemma rel_of_abs {P S C D : ℝ} (hS : 0 < S) (h : |P - S| ≤ C * D) : |P / S - 1| ≤ C * D / S := by
  rw [div_sub_one hS.ne', abs_div, abs_of_pos hS]
  exact div_le_div_of_nonneg_right h hS.le

lemma setIntegral_exp_pos {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ} {p q : ℝ} (hpq : p < q)
    (hJ : Icc p q ⊆ S) (hint : IntegrableOn (fun z => exp (f z)) S) :
    0 < ∫ z in S, exp (f z) := by
  have h1 : 0 < ∫ z in p..q, exp (f z) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (Continuous.intervalIntegrable (by fun_prop) _ _) (fun x _ => exp_pos _) hpq
  rw [← setIntegral_Icc_eq _ hpq.le] at h1
  exact h1.trans_le (setIntegral_mono_set hint (ae_of_all _ (fun _ => (exp_pos _).le))
    (HasSubset.Subset.eventuallyLE hJ))

lemma exp_split_neg (u ua D : ℝ) : exp (-u / D) = exp (-ua / D) * exp (-((u - ua) / D)) := by
  rw [← exp_add]; congr 1; ring

lemma exp_split_pos (u ub D : ℝ) : exp (u / D) = exp (ub / D) * exp (-((ub - u) / D)) := by
  rw [← exp_add]; congr 1; ring

/-- A `C D` error on an `α√D` main term is a relative error `(C/α)√D`. -/
lemma rel_sqrt {P α C D : ℝ} (hα : 0 < α) (hD : 0 < D) (h : |P - α * √D| ≤ C * D) :
    |P / (α * √D) - 1| ≤ C / α * √D := by
  have hs : 0 < √D := sqrt_pos.mpr hD
  have := rel_of_abs (mul_pos hα hs) h
  refine this.trans (le_of_eq ?_)
  rw [mul_div_mul_comm, Real.div_sqrt]

section twoWell

variable {U : ℝ → ℝ} {a b c : ℝ}

/-! ### The three Laplace estimates -/

lemma TwoWellHyp.left_laplace (h : TwoWellHyp U a b c) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      IntegrableOn (fun z => exp (-((U z - U a) / D))) (Iic b) ∧
        |(∫ z in Iic b, exp (-((U z - U a) / D))) - √(2 * π / h.ka) * √D| ≤ C * D := by
  have hcont := h.cont
  have hint : IntegrableOn (fun z => exp (-(U z - U a))) (Iic b) := by
    refine IntegrableOn.congr_fun ((h.integrable.const_mul (exp (U a))).integrableOn)
      (fun z _ => ?_) measurableSet_Iic
    rw [← exp_add]; congr 1; ring
  obtain ⟨C, hC⟩ := laplace_min (W := fun z => U z - U a) (S := Iic b) (m := a) (by fun_prop)
    measurableSet_Iic h.hr h.hka h.hM h.hMra h.taylor_a
    (fun z hz => le_trans hz.2 (by linarith [h.sep_ab, h.hr])) h.hη
    (fun z hz hz' => by have := h.well_a z hz hz'; linarith) hint
  refine ⟨C, fun D hD hD1 => ?_⟩
  obtain ⟨h1, h2⟩ := hC D hD hD1
  exact ⟨h1, by rwa [sqrt_two_pi_D _ _ hD.le] at h2⟩

lemma TwoWellHyp.right_laplace (h : TwoWellHyp U a b c) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      IntegrableOn (fun z => exp (-((U z - U c) / D))) (Ioi b) ∧
        |(∫ z in Ioi b, exp (-((U z - U c) / D))) - √(2 * π / h.kc) * √D| ≤ C * D := by
  have hcont := h.cont
  have hint : IntegrableOn (fun z => exp (-(U z - U c))) (Ioi b) := by
    refine IntegrableOn.congr_fun ((h.integrable.const_mul (exp (U c))).integrableOn)
      (fun z _ => ?_) measurableSet_Ioi
    rw [← exp_add]; congr 1; ring
  obtain ⟨C, hC⟩ := laplace_min (W := fun z => U z - U c) (S := Ioi b) (m := c) (by fun_prop)
    measurableSet_Ioi h.hr h.hkc h.hM h.hMrc h.taylor_c
    (fun z hz => lt_of_lt_of_le (by linarith [h.sep_bc, h.hr]) hz.1) h.hη
    (fun z hz hz' => by have := h.well_c z (le_of_lt hz) hz'; linarith) hint
  refine ⟨C, fun D hD hD1 => ?_⟩
  obtain ⟨h1, h2⟩ := hC D hD hD1
  exact ⟨h1, by rwa [sqrt_two_pi_D _ _ hD.le] at h2⟩

lemma TwoWellHyp.barrier_laplace (h : TwoWellHyp U a b c) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |(∫ z in a..c, exp (-((U b - U z) / D))) - √(2 * π / h.kb) * √D| ≤ C * D := by
  have hcont := h.cont
  have hr := h.hr
  have h1 := h.sep_ab
  have h2 := h.sep_bc
  obtain ⟨C, hC⟩ := laplace_min (W := fun z => U b - U z) (S := Icc a c) (m := b) (by fun_prop)
    measurableSet_Icc h.hr h.hkb h.hM h.hMrb h.taylor_b
    (Icc_subset_Icc (by linarith) (by linarith)) h.hη
    (fun z hz hz' => by have := h.barrier z hz hz'; linarith)
    (Continuous.integrableOn_Icc (by fun_prop))
  refine ⟨C, fun D hD hD1 => ?_⟩
  have := (hC D hD hD1).2
  rwa [setIntegral_Icc_eq _ (by linarith), sqrt_two_pi_D _ _ hD.le] at this

/-! ### Rewriting the unnormalised quantities -/

lemma popA_eq (U : ℝ → ℝ) (D a b : ℝ) :
    popA U D b = exp (-U a / D) * ∫ z in Iic b, exp (-((U z - U a) / D)) := by
  rw [popA, ← integral_const_mul]; congr 1; ext z; exact exp_split_neg _ _ _

lemma popC_eq (U : ℝ → ℝ) (D b c : ℝ) :
    popC U D b = exp (-U c / D) * ∫ z in Ioi b, exp (-((U z - U c) / D)) := by
  rw [popC, ← integral_const_mul]; congr 1; ext z; exact exp_split_neg _ _ _

lemma barrierInt_eq (U : ℝ → ℝ) (D a b c : ℝ) :
    ∫ x in a..c, exp (U x / D) = exp (U b / D) * ∫ z in a..c, exp (-((U b - U z) / D)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro z _; exact exp_split_pos _ _ _

lemma TwoWellHyp.normInt_eq (h : TwoWellHyp U a b c) {D : ℝ} (hD : 0 < D) (hD1 : D ≤ 1) :
    normInt U D = popA U D b + popC U D b := by
  obtain ⟨CA, hA⟩ := h.left_laplace
  obtain ⟨CC, hC⟩ := h.right_laplace
  have iA : IntegrableOn (fun x => exp (-U x / D)) (Iic b) := by
    refine IntegrableOn.congr_fun (((hA D hD hD1).1).const_mul (exp (-U a / D)))
      (fun z _ => ?_) measurableSet_Iic
    exact (exp_split_neg _ _ _).symm
  have iC : IntegrableOn (fun x => exp (-U x / D)) (Ioi b) := by
    refine IntegrableOn.congr_fun (((hC D hD hD1).1).const_mul (exp (-U c / D)))
      (fun z _ => ?_) measurableSet_Ioi
    exact (exp_split_neg _ _ _).symm
  rw [normInt, popA, popC, ← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi iA iC,
    Iic_union_Ioi, setIntegral_univ]

/-! ### (9.1.6): the normalisation -/

/-- **(9.1.6) with rate.**  `𝒩⁻¹ = ∫ e^{-U/D}` equals
`e^{-U(a)/D}√(2πD/k_a) + e^{-U(c)/D}√(2πD/k_c)` up to a relative error `C√D`, `0 < D ≤ 1`. -/
theorem normalization_asymp (h : TwoWellHyp U a b c) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |normInt U D / (exp (-U a / D) * √(2 * π * D / h.ka)
        + exp (-U c / D) * √(2 * π * D / h.kc)) - 1| ≤ C * √D := by
  obtain ⟨CA, hA⟩ := h.left_laplace
  obtain ⟨CC, hC⟩ := h.right_laplace
  set αa := √(2 * π / h.ka)
  set αc := √(2 * π / h.kc)
  have hαa : 0 < αa := sqrt_pos.mpr (by have := h.hka; positivity)
  have hαc : 0 < αc := sqrt_pos.mpr (by have := h.hkc; positivity)
  set m := min αa αc
  have hm : 0 < m := lt_min hαa hαc
  set C0 := max (max CA CC) 0
  refine ⟨C0 / m, fun D hD hD1 => ?_⟩
  have hs : 0 < √D := sqrt_pos.mpr hD
  set A := exp (-U a / D)
  set B := exp (-U c / D)
  have hA0 : 0 < A := exp_pos _
  have hB0 : 0 < B := exp_pos _
  set Pa := ∫ z in Iic b, exp (-((U z - U a) / D))
  set Pc := ∫ z in Ioi b, exp (-((U z - U c) / D))
  have ea := (hA D hD hD1).2
  have ec := (hC D hD hD1).2
  have hN : normInt U D = A * Pa + B * Pc := by rw [h.normInt_eq hD hD1, popA_eq, popC_eq]
  rw [sqrt_two_pi_D _ _ hD.le, sqrt_two_pi_D _ _ hD.le, hN]
  set T := A * (αa * √D) + B * (αc * √D)
  have hT : (A + B) * (m * √D) ≤ T := by
    have h1 : m ≤ αa := min_le_left _ _
    have h2 : m ≤ αc := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_left h1 hA0.le, mul_le_mul_of_nonneg_left h2 hB0.le]
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hdiff : |A * Pa + B * Pc - T| ≤ (A + B) * (C0 * D) := by
    have e : A * Pa + B * Pc - T = A * (Pa - αa * √D) + B * (Pc - αc * √D) := by ring
    rw [e]
    have hCA : CA * D ≤ C0 * D := mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_max_left _ _)) hD.le
    have hCC : CC * D ≤ C0 * D := mul_le_mul_of_nonneg_right
      (le_trans (le_max_right _ _) (le_max_left _ _)) hD.le
    calc |A * (Pa - αa * √D) + B * (Pc - αc * √D)|
        ≤ |A * (Pa - αa * √D)| + |B * (Pc - αc * √D)| := abs_add_le _ _
      _ = A * |Pa - αa * √D| + B * |Pc - αc * √D| := by
          rw [abs_mul, abs_mul, abs_of_pos hA0, abs_of_pos hB0]
      _ ≤ A * (C0 * D) + B * (C0 * D) := by
          gcongr; exacts [ea.trans hCA, ec.trans hCC]
      _ = (A + B) * (C0 * D) := by ring
  rw [div_sub_one hT0.ne', abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
  have hC0 : 0 ≤ C0 := le_max_right _ _
  calc |A * Pa + B * Pc - T| ≤ (A + B) * (C0 * D) := hdiff
    _ = (A + B) * (C0 * (√D * √D)) := by rw [mul_self_sqrt hD.le]
    _ = C0 / m * √D * ((A + B) * (m * √D)) := by field_simp
    _ ≤ C0 / m * √D * T := by gcongr

/-! ### (9.2.23): ratio of the populations, and (9.1.8) -/

/-- **(9.2.23) with rate.**  `n_a/n_c = √(k_c/k_a) e^{(U(c)-U(a))/D}(1 + O(√D))`. -/
theorem population_ratio_asymp (h : TwoWellHyp U a b c) :
    ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
      |(popA U D b / popC U D b) / (√(h.kc / h.ka) * exp ((U c - U a) / D)) - 1|
        ≤ C * √D := by
  obtain ⟨CA, hA⟩ := h.left_laplace
  obtain ⟨CC, hC⟩ := h.right_laplace
  set αa := √(2 * π / h.ka)
  set αc := √(2 * π / h.kc)
  have hαa : 0 < αa := sqrt_pos.mpr (by have := h.hka; positivity)
  have hαc : 0 < αc := sqrt_pos.mpr (by have := h.hkc; positivity)
  set ka' := max CA 0 / αa
  set kc' := max CC 0 / αc
  have hka' : 0 ≤ ka' := by positivity
  have hkc' : 0 ≤ kc' := by positivity
  have hpos : 0 < 1 / (4 * (kc' + 1) ^ 2) := by
    apply div_pos one_pos; have : 0 < kc' + 1 := by linarith
    positivity
  refine ⟨2 * (ka' + kc'), min 1 (1 / (4 * (kc' + 1) ^ 2)), lt_min one_pos hpos,
    fun D hD hD0 => ?_⟩
  have hD1 : D ≤ 1 := le_trans hD0 (min_le_left _ _)
  have hs : 0 < √D := sqrt_pos.mpr hD
  set Pa := ∫ z in Iic b, exp (-((U z - U a) / D))
  set Pc := ∫ z in Ioi b, exp (-((U z - U c) / D))
  have ea : |Pa / (αa * √D) - 1| ≤ ka' * √D :=
    rel_sqrt hαa hD (((hA D hD hD1).2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le))
  have ec : |Pc / (αc * √D) - 1| ≤ kc' * √D :=
    rel_sqrt hαc hD (((hC D hD hD1).2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le))
  have hsmall : kc' * √D ≤ 1 / 2 := by
    have h1 : D ≤ 1 / (4 * (kc' + 1) ^ 2) := le_trans hD0 (min_le_right _ _)
    have hk1 : 0 < kc' + 1 := by linarith
    have h2 : √D ≤ 1 / (2 * (kc' + 1)) := by
      rw [show 1 / (2 * (kc' + 1)) = √(1 / (4 * (kc' + 1) ^ 2)) by
        rw [sqrt_div' _ (by positivity), sqrt_one, show 4 * (kc' + 1) ^ 2 = (2 * (kc' + 1)) ^ 2 by
          ring, sqrt_sq (by linarith)]]
      exact sqrt_le_sqrt h1
    calc kc' * √D ≤ (kc' + 1) * (1 / (2 * (kc' + 1))) := by
          apply mul_le_mul (by linarith) h2 hs.le hk1.le
      _ = 1 / 2 := by field_simp
  have key := div_rate ea ec hsmall
  have e : (popA U D b / popC U D b) / (√(h.kc / h.ka) * exp ((U c - U a) / D))
      = (Pa / (αa * √D)) / (Pc / (αc * √D)) := by
    rw [popA_eq U D a b, popC_eq U D b c]
    have hPc : Pc ≠ 0 := by
      intro h0; rw [h0, zero_div] at ec; rw [abs_le] at ec; linarith [ec.1]
    have hsq : √(h.kc / h.ka) = αa / αc := by
      rw [sqrt_div' _ h.hka.le]
      simp only [αa, αc]
      rw [sqrt_div' _ h.hka.le, sqrt_div' _ h.hkc.le]
      have : 0 < √(2 * π) := sqrt_pos.mpr (by positivity)
      have : 0 < √h.ka := sqrt_pos.mpr h.hka
      have : 0 < √h.kc := sqrt_pos.mpr h.hkc
      field_simp
    have hex : exp ((U c - U a) / D) = exp (-U a / D) / exp (-U c / D) := by
      rw [← exp_sub]; congr 1; ring
    rw [hsq, hex]
    have := exp_pos (-U a / D); have := exp_pos (-U c / D)
    field_simp
    exact mul_div_cancel_right₀ Pa hPc
  rw [e]; linarith

/-- **(9.1.7)–(9.1.8).**  If `U(a) > U(c)`, the stationary population of the upper well
`n_a = popA/𝒩⁻¹` is exponentially small: `n_a ≤ C e^{-(U(a)-U(c))/D}` for small `D`. -/
theorem population_small (h : TwoWellHyp U a b c) :
    ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
      popA U D b / normInt U D ≤ C * exp (-(U a - U c) / D) := by
  obtain ⟨C, D₀, hD₀, hC⟩ := population_ratio_asymp h
  refine ⟨(C + 1) * √(h.kc / h.ka), min D₀ 1, lt_min hD₀ one_pos, fun D hD hD0 => ?_⟩
  have hD1 : D ≤ 1 := le_trans hD0 (min_le_right _ _)
  have hDD : D ≤ D₀ := le_trans hD0 (min_le_left _ _)
  have key := hC D hD hDD
  obtain ⟨CA, hA⟩ := h.left_laplace
  have hpA : 0 ≤ popA U D b := setIntegral_nonneg measurableSet_Iic (fun _ _ => (exp_pos _).le)
  have hpC : 0 ≤ popC U D b := setIntegral_nonneg measurableSet_Ioi (fun _ _ => (exp_pos _).le)
  set T := √(h.kc / h.ka) * exp ((U c - U a) / D)
  have hT : 0 < T := mul_pos (sqrt_pos.mpr (div_pos h.hkc h.hka)) (exp_pos _)
  have hratio : popA U D b / popC U D b ≤ (1 + C * √D) * T := by
    have := (abs_le.mp key).2
    rw [sub_le_iff_le_add, div_le_iff₀ hT] at this
    linarith
  have hC0 : 0 ≤ C := by
    have := le_trans (abs_nonneg _) key
    exact nonneg_of_mul_nonneg_left this (sqrt_pos.mpr hD)
  have hsD : √D ≤ 1 := sqrt_le_one.mpr hD1
  rw [h.normInt_eq hD hD1]
  have h0 : 0 < popC U D b := by
    obtain ⟨CC, hCC⟩ := h.right_laplace
    have hcont := h.cont
    rw [popC_eq]
    exact mul_pos (exp_pos _) (setIntegral_exp_pos (f := fun z => -((U z - U c) / D))
      (by fun_prop) (by linarith : b + 1 < b + 2) (fun z hz => lt_of_lt_of_le (by linarith) hz.1)
      (hCC D hD hD1).1)
  calc popA U D b / (popA U D b + popC U D b) ≤ popA U D b / popC U D b := by
        apply div_le_div_of_nonneg_left hpA h0; linarith
    _ ≤ (1 + C * √D) * T := hratio
    _ ≤ (1 + C) * T := by gcongr; nlinarith
    _ = (C + 1) * √(h.kc / h.ka) * exp (-(U a - U c) / D) := by
        simp only [T]; rw [show (U c - U a) / D = -(U a - U c) / D by ring]; ring

/-! ### (9.1.13): the barrier integral -/

/-- **(9.1.13) with rate** (the common factor `𝒩⁻¹` divided out):
`∫_a^c e^{U/D} = √(2πD/k_b) e^{U(b)/D}(1 + O(√D))` for `0 < D ≤ 1`. -/
theorem barrier_integral_asymp (h : TwoWellHyp U a b c) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |(∫ x in a..c, exp (U x / D)) / (√(2 * π * D / h.kb) * exp (U b / D)) - 1| ≤ C * √D := by
  obtain ⟨C, hC⟩ := h.barrier_laplace
  have hαb : 0 < √(2 * π / h.kb) := sqrt_pos.mpr (by have := h.hkb; positivity)
  refine ⟨max C 0 / √(2 * π / h.kb), fun D hD hD1 => ?_⟩
  have := rel_sqrt hαb hD ((hC D hD hD1).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hD.le))
  rw [barrierInt_eq U D a b c, sqrt_two_pi_D _ _ hD.le]
  convert this using 2
  have := exp_pos (U b / D)
  field_simp

/-! ### (9.2.24)–(9.2.25): the relaxation time -/

lemma sqrt_rate {u e : ℝ} (hu : 0 ≤ u) (h : |u - 1| ≤ e) : |√u - 1| ≤ e := by
  have hsu : 0 ≤ √u := sqrt_nonneg u
  have key : (√u - 1) * (√u + 1) = u - 1 := by linear_combination sq_sqrt hu
  have h1 : |√u - 1| * (√u + 1) = |u - 1| := by
    rw [← key, abs_mul, abs_of_pos (by linarith : 0 < √u + 1)]
  have h2 : |√u - 1| ≤ |√u - 1| * (√u + 1) := by
    nlinarith [abs_nonneg (√u - 1)]
  linarith

lemma prod_rate {x y z e₁ e₂ e₃ : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : |x - 1| ≤ e₁) (hy : |y - 1| ≤ e₂) (hz : |z - 1| ≤ e₃) :
    |√(x * y) * z - 1| ≤ (e₁ + e₂ + e₁ * e₂) * (1 + e₃) + e₃ := by
  have he₁ : 0 ≤ e₁ := le_trans (abs_nonneg _) hx
  have he₂ : 0 ≤ e₂ := le_trans (abs_nonneg _) hy
  have he₃ : 0 ≤ e₃ := le_trans (abs_nonneg _) hz
  have hxy : |x * y - 1| ≤ e₁ + e₂ + e₁ * e₂ := by
    have e : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
    rw [e]
    calc |(x - 1) + (y - 1) + (x - 1) * (y - 1)|
        ≤ |x - 1| + |y - 1| + |x - 1| * |y - 1| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_mul _ _).le)
      _ ≤ e₁ + e₂ + e₁ * e₂ := by gcongr
  have hs := sqrt_rate (mul_nonneg hx0 hy0) hxy
  have hz1 : |z| ≤ 1 + e₃ := by
    calc |z| = |(z - 1) + 1| := by ring_nf
      _ ≤ |z - 1| + |1| := abs_add_le _ _
      _ ≤ 1 + e₃ := by rw [abs_one]; linarith
  have e : √(x * y) * z - 1 = (√(x * y) - 1) * z + (z - 1) := by ring
  rw [e]
  calc |(√(x * y) - 1) * z + (z - 1)| ≤ |√(x * y) - 1| * |z| + |z - 1| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ (e₁ + e₂ + e₁ * e₂) * (1 + e₃) + e₃ := by
        gcongr

/-- **(9.2.24)–(9.2.25) with rate.**  The relaxation time (9.2.18)
`τ_r = n_a n_c D⁻¹ ∫_a^c p_s⁻¹` satisfies `τ_r = 2π H(b; a, c) (n_a n_c)^{1/2} (1 + O(√D))`,
`H = |U''(b)|^{-1/2} U''(a)^{-1/4} U''(c)^{-1/4} e^{[2U(b) - U(a) - U(c)]/(2D)}`. -/
theorem relaxTime_asymp (h : TwoWellHyp U a b c) :
    ∃ C, ∀ D, 0 < D → D ≤ 1 →
      |relaxTime U D a b c / (2 * π * Hfac h.ka h.kb h.kc (U a) (U b) (U c) D *
        √((popA U D b / normInt U D) * (popC U D b / normInt U D))) - 1| ≤ C * √D := by
  obtain ⟨CA, hA⟩ := h.left_laplace
  obtain ⟨CC, hC⟩ := h.right_laplace
  obtain ⟨CB, hB⟩ := h.barrier_laplace
  set αa := √(2 * π / h.ka)
  set αc := √(2 * π / h.kc)
  set αb := √(2 * π / h.kb)
  have hαa : 0 < αa := sqrt_pos.mpr (by have := h.hka; positivity)
  have hαc : 0 < αc := sqrt_pos.mpr (by have := h.hkc; positivity)
  have hαb : 0 < αb := sqrt_pos.mpr (by have := h.hkb; positivity)
  set ka' := max CA 0 / αa
  set kc' := max CC 0 / αc
  set kb' := max CB 0 / αb
  refine ⟨(ka' + kc' + ka' * kc') * (1 + kb') + kb', fun D hD hD1 => ?_⟩
  have hs : 0 < √D := sqrt_pos.mpr hD
  have hs1 : √D ≤ 1 := sqrt_le_one.mpr hD1
  set Pa := ∫ z in Iic b, exp (-((U z - U a) / D))
  set Pc := ∫ z in Ioi b, exp (-((U z - U c) / D))
  set Pb := ∫ z in a..c, exp (-((U b - U z) / D))
  have ea : |Pa / (αa * √D) - 1| ≤ ka' * √D :=
    rel_sqrt hαa hD (((hA D hD hD1).2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le))
  have ec : |Pc / (αc * √D) - 1| ≤ kc' * √D :=
    rel_sqrt hαc hD (((hC D hD hD1).2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le))
  have eb : |Pb / (αb * √D) - 1| ≤ kb' * √D :=
    rel_sqrt hαb hD ((hB D hD hD1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le))
  have hPa0 : 0 ≤ Pa := setIntegral_nonneg measurableSet_Iic (fun _ _ => (exp_pos _).le)
  have hPc0 : 0 ≤ Pc := setIntegral_nonneg measurableSet_Ioi (fun _ _ => (exp_pos _).le)
  have key := prod_rate (div_nonneg hPa0 (by positivity)) (div_nonneg hPc0 (by positivity))
    ea ec eb
  have hka' : 0 ≤ ka' := by positivity
  have hkc' : 0 ≤ kc' := by positivity
  have hkb' : 0 ≤ kb' := by positivity
  have hbound : (ka' * √D + kc' * √D + ka' * √D * (kc' * √D)) * (1 + kb' * √D) + kb' * √D
      ≤ ((ka' + kc' + ka' * kc') * (1 + kb') + kb') * √D := by
    have h1 : ka' * √D * (kc' * √D) ≤ ka' * kc' * √D := by
      rw [show ka' * √D * (kc' * √D) = ka' * kc' * √D * √D by ring]
      exact mul_le_of_le_one_right (by positivity) hs1
    have h2 : kb' * √D ≤ kb' := mul_le_of_le_one_right hkb' hs1
    have h3 : 0 ≤ ka' * √D + kc' * √D + ka' * √D * (kc' * √D) := by positivity
    have h4 := mul_le_mul (by linarith : ka' * √D + kc' * √D + ka' * √D * (kc' * √D)
        ≤ ka' * √D + kc' * √D + ka' * kc' * √D) (by linarith : 1 + kb' * √D ≤ 1 + kb')
      (by positivity) (by positivity)
    calc (ka' * √D + kc' * √D + ka' * √D * (kc' * √D)) * (1 + kb' * √D) + kb' * √D
        ≤ (ka' * √D + kc' * √D + ka' * kc' * √D) * (1 + kb') + kb' * √D := by linarith
      _ = _ := by ring
  refine le_trans (le_of_eq ?_) (key.trans hbound)
  -- the identity `τ_r / (2πH√(n_a n_c)) = √(x_a x_c) x_b`
  have hN := h.normInt_eq hD hD1
  set A := exp (-U a / D)
  set B := exp (-U c / D)
  set E := exp (U b / D)
  have hA0 : 0 < A := exp_pos _
  have hB0 : 0 < B := exp_pos _
  have hE0 : 0 < E := exp_pos _
  have hcont := h.cont
  have hPa : 0 < Pa := setIntegral_exp_pos (f := fun z => -((U z - U a) / D)) (by fun_prop)
    (by linarith : b - 1 < b) (fun z hz => hz.2) (hA D hD hD1).1
  have hPc : 0 < Pc := setIntegral_exp_pos (f := fun z => -((U z - U c) / D)) (by fun_prop)
    (by linarith : b + 1 < b + 2) (fun z hz => lt_of_lt_of_le (by linarith) hz.1)
    (hC D hD hD1).1
  have hX : popA U D b = A * Pa := popA_eq U D a b
  have hY : popC U D b = B * Pc := popC_eq U D b c
  have hI : ∫ x in a..c, exp (U x / D) = E * Pb := barrierInt_eq U D a b c
  have hX0 : 0 < A * Pa := mul_pos hA0 hPa
  have hY0 : 0 < B * Pc := mul_pos hB0 hPc
  have hsq1 : √((A * Pa) / (A * Pa + B * Pc) * ((B * Pc) / (A * Pa + B * Pc)))
      = √((A * Pa) * (B * Pc)) / (A * Pa + B * Pc) := by
    rw [show (A * Pa) / (A * Pa + B * Pc) * ((B * Pc) / (A * Pa + B * Pc))
      = (A * Pa) * (B * Pc) / (A * Pa + B * Pc) ^ 2 by rw [div_mul_div_comm, sq], sqrt_div' _ (by positivity),
      sqrt_sq (by positivity)]
  have hsqXY : √((A * Pa) * (B * Pc)) = √(A * B) * √(Pa * Pc) := by
    rw [show (A * Pa) * (B * Pc) = (A * B) * (Pa * Pc) by ring, sqrt_mul (by positivity)]
  have hAB : √(A * B) * E = exp ((2 * U b - U a - U c) / (2 * D)) := by
    have : A * B = exp ((-U a - U c) / (2 * D)) ^ 2 := by
      simp only [A, B]; rw [← exp_add, sq, ← exp_add]; congr 1; field_simp; ring
    rw [this, sqrt_sq (exp_pos _).le]
    simp only [E]; rw [← exp_add]; congr 1; field_simp; ring
  have hαprod : √(αa * αc) * αb * √h.kb * √(√(h.ka * h.kc)) = 2 * π := by
    have h1 : αa * αc = 2 * π / √(h.ka * h.kc) := sqrt_two_pi_mul' h.kc h.hka
    have hk : 0 < √(h.ka * h.kc) := sqrt_pos.mpr (mul_pos h.hka h.hkc)
    have h2 : √(αa * αc) = √(2 * π) / √(√(h.ka * h.kc)) := by
      rw [h1, sqrt_div' _ hk.le]
    have h3 : αb * √h.kb = √(2 * π) := by
      simp only [αb]; rw [← sqrt_mul' _ h.hkb.le]; congr 1; field_simp [h.hkb.ne']
    have hk2 : 0 < √(√(h.ka * h.kc)) := sqrt_pos.mpr hk
    rw [h2, show √(2 * π) / √(√(h.ka * h.kc)) * αb * √h.kb * √(√(h.ka * h.kc))
      = √(2 * π) * (αb * √h.kb) * (√(√(h.ka * h.kc)) / √(√(h.ka * h.kc))) by ring, h3,
      div_self hk2.ne', mul_one, mul_self_sqrt (by positivity)]
  have hsqR : √((Pa / (αa * √D)) * (Pc / (αc * √D))) = √(Pa * Pc) / (√(αa * αc) * √D) := by
    rw [show (Pa / (αa * √D)) * (Pc / (αc * √D)) = (Pa * Pc) / ((αa * αc) * √D ^ 2) by
      field_simp, sqrt_div' _ (by positivity), sqrt_mul' _ (sq_nonneg _), sqrt_sq hs.le]
  rw [relaxTime, hN, hX, hY, hI, hsq1, hsqXY, hsqR, Hfac, ← hAB]
  have hXY : (A * Pa) * (B * Pc) = (√(A * B) * √(Pa * Pc)) * (√(A * B) * √(Pa * Pc)) := by
    rw [← hsqXY, mul_self_sqrt (by positivity)]
  have hsAB : 0 < √(A * B) := sqrt_pos.mpr (by positivity)
  have hsP : 0 < √(Pa * Pc) := sqrt_pos.mpr (by positivity)
  have hkb : 0 < √h.kb := sqrt_pos.mpr h.hkb
  have hkk : 0 < √(√(h.ka * h.kc)) := sqrt_pos.mpr (sqrt_pos.mpr (mul_pos h.hka h.hkc))
  have hαac : 0 < √(αa * αc) := sqrt_pos.mpr (by positivity)
  rw [show (A * Pa) / (A * Pa + B * Pc) * ((B * Pc) / (A * Pa + B * Pc))
      * ((A * Pa + B * Pc) * (E * Pb)) / D
      = ((A * Pa) * (B * Pc)) * (E * Pb) / ((A * Pa + B * Pc) * D) by
    field_simp, hXY, ← hαprod]
  field_simp
  rw [sq_sqrt hD.le]
  ring_nf

end twoWell

end Gardiner.Escape
