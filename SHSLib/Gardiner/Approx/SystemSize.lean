/-
# Van Kampen's system size expansion

Gardiner, *Handbook of Stochastic Methods*, §7.2.3, equations (7.2.28)–(7.2.40) and
(7.2.59)–(7.2.61).

The master equation has finitely many jumps `a → a + r_j` with extensive rates
`W(a; r_j) = Ω ψ_j(a/Ω)` (7.2.29), so that the jump moments are `αₙ(a) = Ω α̃ₙ(a/Ω)`
(7.2.31).  In the fluctuation variable `z` of (7.2.30), `a = Ωφ(t) + Ω^{1/2} z`, the
backward generator of the master equation becomes `Gardiner.vkGen`
(`Gardiner.finJumpGen_fluct`, `Gardiner.hasDerivAt_fluct_frame`).

Main results:

* `Gardiner.vkGen_sub_lnaGen_le` — **the rescaled master-equation generator is within
  `O(Ω^{-1/2})` of the linear-noise operator on smooth test functions**, with the explicit
  bound `Ω^{-1/2} [K z² |f'|/2 + L |z| |f''|/2 + ‖f'''‖ β̃₃(φ + Ω^{-1/2}z)/6]`, where `K`
  bounds `α̃₁''`, `L` is a Lipschitz constant of `α̃₂` and `β̃₃ = Σ_j |ψ_j| |r_j|³` is the
  third absolute jump moment; `Gardiner.vkGen_tendsto_lnaGen` is the limit `Ω → ∞`.
* **Erratum (7.2.35), (7.2.40).**  The limiting operator is
  `α̃₁'(φ) z ∂_z f + ½ α̃₂(φ) ∂_z² f`, i.e. the Fokker–Planck equation is
  `∂ₜP = -α̃₁'(φ(t)) ∂_z(zP) + ½ α̃₂(φ(t)) ∂_z² P` and the SDE is
  `dz = α̃₁'(φ(t)) z dt + √α̃₂(φ(t)) dW`.  The text prints `α̃₁` in place of its derivative
  `α̃₁'` in both (7.2.35) and (7.2.40); its own example (7.2.47) uses `α̃₁' = -k₁`.
  `Gardiner.lnaFP` is the corrected right-hand side.
* §7.2.3 a), comparison with Kramers–Moyal: `Gardiner.km_change_of_variables` is
  (7.2.36)–(7.2.37), which is the small-noise equation (6.3.1) with `ε² = 1/Ω` (7.2.38);
  `Gardiner.vkGen_sub_kmGen_le` and `Gardiner.kmGen_sub_lnaGen_le` show that the
  master-equation and the Kramers–Moyal generators have the same limit and differ by
  `O(Ω^{-1/2})`.
* (7.2.33)–(7.2.34): the coefficient `vkCoeff m` of `Ω^{-(m-2)/2}` (backward form);
  `vkCoeff 1` is cancelled by the transport term exactly when `φ' = α̃₁(φ)` (7.2.33), and
  `vkCoeff 2` is the linear-noise operator.
* (7.2.59)–(7.2.60): `Gardiner.vk_moment_hierarchy`, from integration by parts
  (`Gardiner.integral_pow_mul_tower`).
* The moments of the linear-noise equation, (4.4.84)–(4.4.85) in one dimension:
  `Gardiner.lna_mean_ode`, `Gardiner.lna_second_moment_ode`, `Gardiner.linear_ode_eq`.
-/
import SHSLib.Gardiner.Approx.KramersMoyal
import SHSLib.Gardiner.Approx.SmallNoise

open MeasureTheory Filter Topology Set
open scoped BigOperators Nat

noncomputable section

namespace Gardiner

section VanKampen

variable {ι : Type*} (s : Finset ι) (r : ι → ℝ) (ψ : ι → ℝ → ℝ)

/-- (7.2.29): the extensive transition rates `W(a; r_j) = Ω ψ_j(a/Ω)`. -/
def extRate (Ω : ℝ) : ι → ℝ → ℝ := fun j a => Ω * ψ j (a / Ω)

/-- (7.2.31): the intensive jump moments `α̃ₙ(x) = Σ_j ψ_j(x) r_jⁿ`. -/
abbrev intMoment (n : ℕ) (x : ℝ) : ℝ := finJumpMoment s r ψ x n

/-- (7.2.31): under the scaling (7.2.29), `αₙ(a) = Ω α̃ₙ(a/Ω)`. -/
theorem jumpMoment_extensive (Ω a : ℝ) (n : ℕ) :
    finJumpMoment s r (extRate ψ Ω) a n = Ω * intMoment s r ψ n (a / Ω) := by
  simp only [intMoment, finJumpMoment, extRate, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- (7.2.30): the master-equation generator acting on a function of the fluctuation
variable, `g(a) = f((a - Ωφ)/Ω^{1/2})`, evaluated at `a = Ωφ + Ω^{1/2} z`. -/
theorem finJumpGen_fluct {Ω : ℝ} (hΩ : 0 < Ω) (phi z : ℝ) (f : ℝ → ℝ) :
    finJumpGen s r (extRate ψ Ω) (fun a => f ((a - Ω * phi) / Real.sqrt Ω))
        (Ω * phi + Real.sqrt Ω * z)
      = ∑ j ∈ s, Ω * ψ j (phi + (Real.sqrt Ω)⁻¹ * z)
          * (f (z + (Real.sqrt Ω)⁻¹ * r j) - f z) := by
  have hs0 : 0 < Real.sqrt Ω := Real.sqrt_pos.2 hΩ
  have hs : Real.sqrt Ω ^ 2 = Ω := Real.sq_sqrt hΩ.le
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [extRate]
  have e1 : (Ω * phi + Real.sqrt Ω * z) / Ω = phi + (Real.sqrt Ω)⁻¹ * z := by
    generalize Real.sqrt Ω = σ at hs hs0 ⊢; subst hs; field_simp
  have e2 : (Ω * phi + Real.sqrt Ω * z + r j - Ω * phi) / Real.sqrt Ω
      = z + (Real.sqrt Ω)⁻¹ * r j := by field_simp; ring
  have e3 : (Ω * phi + Real.sqrt Ω * z - Ω * phi) / Real.sqrt Ω = z := by field_simp; ring
  rw [e1, e2, e3]

/-- (7.2.32), the transport term: along the moving frame `a = Ωφ(t) + Ω^{1/2} z`, a function
of `z` changes at rate `-Ω^{1/2} φ'(t) ∂_z f`. -/
theorem hasDerivAt_fluct_frame {Ω : ℝ} (hΩ : 0 < Ω) (f : ℝ → ℝ) (f' : ℝ) (phi : ℝ → ℝ)
    (dphi a t : ℝ) (hphi : HasDerivAt phi dphi t) (hf : HasDerivAt f f' ((a - Ω * phi t) / Real.sqrt Ω)) :
    HasDerivAt (fun t => f ((a - Ω * phi t) / Real.sqrt Ω)) (-(Real.sqrt Ω * dphi) * f') t := by
  have hs0 : 0 < Real.sqrt Ω := Real.sqrt_pos.2 hΩ
  have hs : Real.sqrt Ω ^ 2 = Ω := Real.sq_sqrt hΩ.le
  have hin : HasDerivAt (fun t => (a - Ω * phi t) / Real.sqrt Ω) (-(Real.sqrt Ω * dphi)) t := by
    have := ((hphi.const_mul Ω).const_sub a).div_const (Real.sqrt Ω)
    convert this using 1
    generalize Real.sqrt Ω = σ at hs hs0 ⊢; subst hs; field_simp
  have := hf.comp t hin
  convert this using 1
  ring

/-- The backward generator of the fluctuation variable `z` (7.2.30)–(7.2.32): the
master-equation generator in the moving frame plus the transport term,
`Σ_j Ω ψ_j(φ + Ω^{-1/2} z) [f(z + Ω^{-1/2} r_j) - f(z)] - Ω^{1/2} φ' f'(z)`.
The test function is given by its derivative tower `D`. -/
def vkGen (Ω phi dphi : ℝ) (D : ℕ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (∑ j ∈ s, Ω * ψ j (phi + (Real.sqrt Ω)⁻¹ * z) * (D 0 (z + (Real.sqrt Ω)⁻¹ * r j) - D 0 z))
    - Real.sqrt Ω * dphi * D 1 z

/-- The Kramers–Moyal route (7.2.36)–(7.2.39): the generator of the Kramers–Moyal
Fokker–Planck equation (7.2.37) in the fluctuation variable.  It is the small-noise
generator `snGen` of (6.3.8) with `A = α̃₁`, `B = α̃₂`, `ε = Ω^{-1/2}` (7.2.38). -/
def kmGen' (Ω phi : ℝ) (D : ℕ → ℝ → ℝ) (z : ℝ) : ℝ :=
  snGen (intMoment s r ψ 1) (intMoment s r ψ 2) (Real.sqrt Ω)⁻¹ phi z (D 1 z) (D 2 z)

/-- **The master equation and its Kramers–Moyal truncation have the same system-size
limit**: in the fluctuation variable, with `φ' = α̃₁(φ)` (7.2.33), the two generators differ
by at most `Ω^{-1/2} ‖f'''‖ β̃₃(φ + Ω^{-1/2}z)/6`. -/
theorem vkGen_sub_kmGen_le {Ω : ℝ} (hΩ : 0 < Ω) (phi z M : ℝ) (D : ℕ → ℝ → ℝ)
    (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y) (hM : ∀ y, |D 3 y| ≤ M) :
    |vkGen s r ψ Ω phi (intMoment s r ψ 1 phi) D z - kmGen' s r ψ Ω phi D z|
      ≤ (Real.sqrt Ω)⁻¹ * (M / 6 * finAbsJumpMoment s r ψ (phi + (Real.sqrt Ω)⁻¹ * z) 3) := by
  have hs0 : 0 < Real.sqrt Ω := Real.sqrt_pos.2 hΩ
  have hs : Real.sqrt Ω ^ 2 = Ω := Real.sq_sqrt hΩ.le
  set ε := (Real.sqrt Ω)⁻¹ with hε
  set u := phi + ε * z
  set c : ι → ℝ → ℝ := fun j _ => Ω * ψ j u
  set r' : ι → ℝ := fun j => ε * r j
  have key := finJumpGen_sub_finKM_le s r' c D 2 z M hD hM
  have hmom : ∀ k, finJumpMoment s r' c z k = Ω * ε ^ k * intMoment s r ψ k u := by
    intro k
    simp only [finJumpMoment, intMoment, r', c, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have habs : finAbsJumpMoment s r' c z 3 = ε * finAbsJumpMoment s r ψ u 3 := by
    simp only [finAbsJumpMoment, r', c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_mul, abs_of_pos hΩ, abs_of_pos (by positivity : (0:ℝ) < ε)]
    have : Ω * ε ^ 3 = ε := by rw [hε]; clear_value ε u c r'; generalize Real.sqrt Ω = σ at hs hs0 ⊢; subst hs; field_simp
    calc Ω * |ψ j u| * (ε * |r j|) ^ 3 = (Ω * ε ^ 3) * (|ψ j u| * |r j| ^ 3) := by ring
      _ = _ := by rw [this]
  have hdiff : vkGen s r ψ Ω phi (intMoment s r ψ 1 phi) D z - kmGen' s r ψ Ω phi D z
      = finJumpGen s r' c (D 0) z - finKM s r' c D 2 z := by
    simp only [vkGen, kmGen', snGen, finKM, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, hmom]
    simp only [finJumpGen, c, r']
    have h1 : Ω * ε ^ 1 = Real.sqrt Ω := by rw [hε]; clear_value ε u c r'; generalize Real.sqrt Ω = σ at hs hs0 ⊢; subst hs; field_simp
    have h2 : Ω * ε ^ 2 = 1 := by rw [hε]; clear_value ε u c r'; generalize Real.sqrt Ω = σ at hs hs0 ⊢; subst hs; field_simp
    rw [h1, h2]
    have h3 : (intMoment s r ψ 1 u - intMoment s r ψ 1 phi) / ε
        = Real.sqrt Ω * (intMoment s r ψ 1 u - intMoment s r ψ 1 phi) := by
      rw [hε]; field_simp
    rw [h3]
    norm_num
    ring
  rw [hdiff]
  calc _ ≤ M / ((2 + 1)! : ℝ) * finAbsJumpMoment s r' c z (2 + 1) := key
    _ = _ := by rw [habs]; norm_num [Nat.factorial]; ring

/-- **The Kramers–Moyal route to the linear noise approximation** (7.2.37)–(7.2.39): the
generator of the Kramers–Moyal equation in the fluctuation variable is within
`Ω^{-1/2} (K z² |f'| + L |z| |f''|)/2` of the linear-noise operator
`α̃₁'(φ) z f' + ½ α̃₂(φ) f''`.  Here `E` is a derivative tower of `α̃₁` with `|α̃₁''| ≤ K`
between `φ` and `φ + Ω^{-1/2} z`, and `L` controls the variation of `α̃₂`. -/
theorem kmGen_sub_lnaGen_le {Ω : ℝ} (hΩ : 0 < Ω) (phi z K L : ℝ) (D : ℕ → ℝ → ℝ)
    (E : ℕ → ℝ → ℝ) (hE0 : E 0 = intMoment s r ψ 1)
    (hE : ∀ k ≤ 1, ∀ u, HasDerivAt (E k) (E (k + 1) u) u)
    (hK : ∀ t ∈ uIcc 0 ((Real.sqrt Ω)⁻¹ * z), |E 2 (phi + t)| ≤ K)
    (hL : |intMoment s r ψ 2 (phi + (Real.sqrt Ω)⁻¹ * z) - intMoment s r ψ 2 phi|
      ≤ L * |(Real.sqrt Ω)⁻¹ * z|) :
    |kmGen' s r ψ Ω phi D z - ouGen (E 1 phi) (intMoment s r ψ 2 phi) z (D 1 z) (D 2 z)|
      ≤ (Real.sqrt Ω)⁻¹ * (K * z ^ 2 * |D 1 z| / 2 + L * |z| * |D 2 z| / 2) := by
  have hs0 : 0 < Real.sqrt Ω := Real.sqrt_pos.2 hΩ
  have := snGen_sub_ouGen_le E (intMoment s r ψ 2) (inv_ne_zero hs0.ne') phi z (D 1 z) (D 2 z) K L
    hE hK hL
  rw [abs_of_pos (inv_pos.2 hs0), hE0] at this
  simpa [kmGen'] using this

/-- **Van Kampen's expansion with an explicit error term.**  On a test function `f` with
`|f'''| ≤ M`, the generator of the fluctuation variable (7.2.30)–(7.2.32), with `φ` solving
the deterministic equation (7.2.33), differs from the **linear-noise operator**
`α̃₁'(φ) z f'(z) + ½ α̃₂(φ) f''(z)` (the corrected (7.2.35)) by at most
`Ω^{-1/2} [K z² |f'(z)|/2 + L |z| |f''(z)|/2 + M β̃₃(φ + Ω^{-1/2} z)/6]`. -/
theorem vkGen_sub_lnaGen_le {Ω : ℝ} (hΩ : 0 < Ω) (phi z K L M : ℝ) (D : ℕ → ℝ → ℝ)
    (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y) (hM : ∀ y, |D 3 y| ≤ M)
    (E : ℕ → ℝ → ℝ) (hE0 : E 0 = intMoment s r ψ 1)
    (hE : ∀ k ≤ 1, ∀ u, HasDerivAt (E k) (E (k + 1) u) u)
    (hK : ∀ t ∈ uIcc 0 ((Real.sqrt Ω)⁻¹ * z), |E 2 (phi + t)| ≤ K)
    (hL : |intMoment s r ψ 2 (phi + (Real.sqrt Ω)⁻¹ * z) - intMoment s r ψ 2 phi|
      ≤ L * |(Real.sqrt Ω)⁻¹ * z|) :
    |vkGen s r ψ Ω phi (intMoment s r ψ 1 phi) D z
        - ouGen (E 1 phi) (intMoment s r ψ 2 phi) z (D 1 z) (D 2 z)|
      ≤ (Real.sqrt Ω)⁻¹ * (K * z ^ 2 * |D 1 z| / 2 + L * |z| * |D 2 z| / 2
          + M / 6 * finAbsJumpMoment s r ψ (phi + (Real.sqrt Ω)⁻¹ * z) 3) := by
  have h1 := vkGen_sub_kmGen_le s r ψ hΩ phi z M D hD hM
  have h2 := kmGen_sub_lnaGen_le s r ψ hΩ phi z K L D E hE0 hE hK hL
  calc _ ≤ |vkGen s r ψ Ω phi (intMoment s r ψ 1 phi) D z - kmGen' s r ψ Ω phi D z|
        + |kmGen' s r ψ Ω phi D z - ouGen (E 1 phi) (intMoment s r ψ 2 phi) z (D 1 z) (D 2 z)| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- **The system-size limit (7.2.35), corrected**: as `Ω → ∞` the generator of the
fluctuation variable converges to the linear-noise operator on every smooth test function
with bounded third derivative, provided `α̃₁''` is bounded, `α̃₂` is Lipschitz at `φ`, and the
rates are continuous at `φ`. -/
theorem vkGen_tendsto_lnaGen (phi z K L M : ℝ) (D : ℕ → ℝ → ℝ)
    (hD : ∀ k ≤ 2, ∀ y, HasDerivAt (D k) (D (k + 1) y) y) (hM : ∀ y, |D 3 y| ≤ M)
    (E : ℕ → ℝ → ℝ) (hE0 : E 0 = intMoment s r ψ 1)
    (hE : ∀ k ≤ 1, ∀ u, HasDerivAt (E k) (E (k + 1) u) u) (hK : ∀ u, |E 2 u| ≤ K)
    (hL : ∀ x, |intMoment s r ψ 2 x - intMoment s r ψ 2 phi| ≤ L * |x - phi|)
    (hψ : ∀ j ∈ s, ContinuousAt (ψ j) phi) :
    Tendsto (fun Ω => vkGen s r ψ Ω phi (intMoment s r ψ 1 phi) D z) atTop
      (𝓝 (ouGen (E 1 phi) (intMoment s r ψ 2 phi) z (D 1 z) (D 2 z))) := by
  -- the argument `φ + Ω^{-1/2} z` tends to `φ`
  have hinv : Tendsto (fun Ω : ℝ => (Real.sqrt Ω)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop)
  have harg : Tendsto (fun Ω : ℝ => phi + (Real.sqrt Ω)⁻¹ * z) atTop (𝓝 phi) := by
    simpa using (hinv.mul_const z).const_add phi
  have hβ : Tendsto (fun Ω : ℝ => finAbsJumpMoment s r ψ (phi + (Real.sqrt Ω)⁻¹ * z) 3) atTop
      (𝓝 (finAbsJumpMoment s r ψ phi 3)) := by
    simp only [finAbsJumpMoment]
    refine tendsto_finset_sum _ fun j hj => ?_
    exact (((hψ j hj).tendsto.comp harg).abs).mul_const _
  set b : ℝ → ℝ := fun Ω => (Real.sqrt Ω)⁻¹ * (K * z ^ 2 * |D 1 z| / 2 + L * |z| * |D 2 z| / 2
      + M / 6 * finAbsJumpMoment s r ψ (phi + (Real.sqrt Ω)⁻¹ * z) 3)
  have hb : Tendsto b atTop (𝓝 0) := by
    have := hinv.mul (((tendsto_const_nhds (x := K * z ^ 2 * |D 1 z| / 2 + L * |z| * |D 2 z| / 2)).add
      (hβ.const_mul (M / 6))))
    simpa [b] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [eventually_gt_atTop 0] with Ω hΩ
  refine vkGen_sub_lnaGen_le s r ψ hΩ phi z K L M D hD hM E hE0 hE (fun t _ => hK _) ?_
  simpa using hL (phi + (Real.sqrt Ω)⁻¹ * z)

/-! ### (7.2.33)–(7.2.34): the coefficients of the expansion -/

/-- The coefficient of `Ω^{-(m-2)/2}` in (7.2.34), in backward (generator) form:
`Σ_{n=1}^{m} α̃ₙ^{(m-n)}(φ) z^{m-n} f⁽ⁿ⁾(z) / (n! (m-n)!)`, where `Dα n k = α̃ₙ^{(k)}(φ)` and
`Df n = f⁽ⁿ⁾(z)`.  (The forward form has `(-∂_z)ⁿ z^{m-n}` in place of `z^{m-n} f⁽ⁿ⁾`.) -/
def vkCoeff (Dα : ℕ → ℕ → ℝ) (Df : ℕ → ℝ) (z : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, Dα n (m - n) * z ^ (m - n) * Df n / ((n ! : ℝ) * ((m - n)! : ℝ))

/-- (7.2.33): the `m = 1` coefficient `α̃₁(φ) f'` is cancelled by the transport term
`-Ω^{1/2} φ' f'` exactly when `φ' = α̃₁(φ)`. -/
theorem vkCoeff_one (Dα : ℕ → ℕ → ℝ) (Df : ℕ → ℝ) (z dphi : ℝ) :
    vkCoeff Dα Df z 1 - dphi * Df 1 = 0 ↔ dphi * Df 1 = Dα 1 0 * Df 1 := by
  rw [show vkCoeff Dα Df z 1 = Dα 1 0 * Df 1 by simp [vkCoeff]]
  constructor <;> intro h <;> linarith

/-- (7.2.34)–(7.2.35): the `m = 2` coefficient is the linear-noise operator
`α̃₁'(φ) z f' + ½ α̃₂(φ) f''`. -/
theorem vkCoeff_two (Dα : ℕ → ℕ → ℝ) (Df : ℕ → ℝ) (z : ℝ) :
    vkCoeff Dα Df z 2 = ouGen (Dα 1 1) (Dα 2 0) z (Df 1) (Df 2) := by
  simp [vkCoeff, ouGen, Finset.sum_Icc_succ_top, Nat.factorial]
  ring

/-! ### The corrected linear-noise Fokker–Planck equation (7.2.35) -/

/-- **(7.2.35), corrected**: the right-hand side
`-α̃₁'(φ) ∂_z(z P) + ½ α̃₂(φ) ∂_z² P` of the linear-noise Fokker–Planck equation, with
`a₁ = α̃₁'(φ(t))` and `a₂ = α̃₂(φ(t))`.  (The text prints `α̃₁[φ(t)]` for `a₁`.)  The
corresponding SDE (7.2.40) is `dz = a₁ z dt + √a₂ dW(t)`. -/
def lnaFP (a₁ a₂ : ℝ) (P : ℝ → ℝ) (z : ℝ) : ℝ :=
  -a₁ * deriv (fun z => z * P z) z + (1 / 2) * a₂ * deriv (deriv P) z

/-- (7.2.38)–(7.2.39): the corrected (7.2.35) is the lowest-order equation (6.3.12) of the
small-noise hierarchy for the Kramers–Moyal equation (7.2.37) with `ε² = 1/Ω`,
`Ã₁ = α̃₁'(φ)`, `B̃₀ = α̃₂(φ)`. -/
theorem lnaFP_eq_hierRHS_zero (At Bt : ℕ → ℝ) (ph : ℕ → ℝ → ℝ) (z : ℝ) :
    lnaFP (At 1) (Bt 0) (ph 0) z = hierRHS At Bt ph 0 z := by
  rw [hierRHS_zero, lnaFP]

/-- The linear-noise operator is the generator of the corrected (7.2.35): for a test
function `f` and a density `P`, `∫ f · lnaFP P = ∫ (a₁ z f' + ½ a₂ f'') P`
(integration by parts; surface terms vanish by integrability). -/
theorem integral_mul_lnaFP (a₁ a₂ : ℝ) (D : ℕ → ℝ → ℝ) (P P' P'' : ℝ → ℝ)
    (hD : ∀ k ≤ 1, ∀ y, HasDerivAt (D k) (D (k + 1) y) y)
    (hP : ∀ z, HasDerivAt P (P' z) z) (hP' : ∀ z, HasDerivAt P' (P'' z) z)
    (i1 : Integrable (fun z => D 0 z * (P z + z * P' z)))
    (i2 : Integrable (fun z => D 1 z * (z * P z)))
    (i3 : Integrable (fun z => D 0 z * (z * P z)))
    (i4 : Integrable (fun z => D 0 z * P'' z)) (i5 : Integrable (fun z => D 1 z * P' z))
    (i6 : Integrable (fun z => D 0 z * P' z)) (i7 : Integrable (fun z => D 2 z * P z))
    (i8 : Integrable (fun z => D 1 z * P z)) :
    ∫ z, D 0 z * lnaFP a₁ a₂ P z
      = ∫ z, ouGen a₁ a₂ z (D 1 z) (D 2 z) * P z := by
  have hzP : ∀ z, HasDerivAt (fun z => z * P z) (P z + z * P' z) z := by
    intro z; simpa [one_mul] using (hasDerivAt_id z).mul (hP z)
  have hd1 : deriv (fun z => z * P z) = fun z => P z + z * P' z := funext fun z => (hzP z).deriv
  have hd2 : deriv (deriv P) = P'' := by
    rw [show deriv P = P' from funext fun z => (hP z).deriv]
    exact funext fun z => (hP' z).deriv
  simp only [lnaFP, hd1, hd2]
  -- the two integrations by parts
  have ibp1 := integral_mul_deriv_eq_deriv_mul_of_integrable (hD 0 (by norm_num)) hzP i1 i2 i3
  have ibp2 := integral_mul_deriv_eq_deriv_mul_of_integrable (hD 0 (by norm_num)) hP' i4 i5 i6
  have ibp3 := integral_mul_deriv_eq_deriv_mul_of_integrable (hD 1 (by norm_num)) hP i5 i7 i8
  have e : ∀ z, D 0 z * (-a₁ * (P z + z * P' z) + 1 / 2 * a₂ * P'' z)
      = (-a₁) * (D 0 z * (P z + z * P' z)) + (1 / 2 * a₂) * (D 0 z * P'' z) := fun z => by ring
  have e' : ∀ z, ouGen a₁ a₂ z (D 1 z) (D 2 z) * P z
      = a₁ * (D 1 z * (z * P z)) + (1 / 2 * a₂) * (D 2 z * P z) := fun z => by
    simp only [ouGen]; ring
  simp_rw [e, e']
  rw [integral_add (i1.const_mul _) (i4.const_mul _), integral_add (i2.const_mul _) (i7.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, ibp1, ibp2,
    ibp3]
  ring

/-- The moments of the corrected linear-noise equation: `∫ z · lnaFP P = a₁ ∫ z P` and
`∫ z² · lnaFP P = 2 a₁ ∫ z² P + a₂ ∫ P` (the `m = 2` truncation of (7.2.60)). -/
theorem integral_moments_lnaFP (a₁ a₂ : ℝ) (P P' P'' : ℝ → ℝ)
    (hP : ∀ z, HasDerivAt P (P' z) z) (hP' : ∀ z, HasDerivAt P' (P'' z) z)
    (hint : ∀ i ≤ 3, Integrable (fun z => z ^ i * P z))
    (hint' : ∀ i ≤ 3, Integrable (fun z => z ^ i * P' z))
    (hint'' : ∀ i ≤ 2, Integrable (fun z => z ^ i * P'' z)) :
    ∫ z, z * lnaFP a₁ a₂ P z = a₁ * ∫ z, z * P z ∧
      ∫ z, z ^ 2 * lnaFP a₁ a₂ P z = 2 * a₁ * (∫ z, z ^ 2 * P z) + a₂ * ∫ z, P z := by
  set F : ℝ → ℝ := fun z => a₁ * (z * P z)
  set F' : ℝ → ℝ := fun z => a₁ * (P z + z * P' z)
  set G : ℝ → ℝ := fun z => a₂ * P z
  set G' : ℝ → ℝ := fun z => a₂ * P' z
  set G'' : ℝ → ℝ := fun z => a₂ * P'' z
  have hF : ∀ z, HasDerivAt F (F' z) z := fun z => by
    simpa [F, F', one_mul] using ((hasDerivAt_id z).mul (hP z)).const_mul a₁
  have hG : ∀ z, HasDerivAt G (G' z) z := fun z => (hP z).const_mul a₂
  have hG' : ∀ z, HasDerivAt G' (G'' z) z := fun z => (hP' z).const_mul a₂
  have hd1 : deriv (fun z => z * P z) = fun z => P z + z * P' z :=
    funext fun z => by simpa [one_mul] using ((hasDerivAt_id z).mul (hP z)).deriv
  have hd2 : deriv (deriv P) = P'' := by
    rw [show deriv P = P' from funext fun z => (hP z).deriv]
    exact funext fun z => (hP' z).deriv
  have hl : ∀ z, lnaFP a₁ a₂ P z = -F' z + (1 / 2) * G'' z := by
    intro z; simp only [lnaFP, hd1, hd2, F', G'']; ring
  have iF : ∀ i ≤ 2, Integrable (fun z => z ^ i * F z) := fun i hi => by
    have := (hint (i + 1) (by omega)).const_mul a₁
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [F]; ring
  have iF' : ∀ i ≤ 2, Integrable (fun z => z ^ i * F' z) := fun i hi => by
    have := ((hint i (by omega)).add (hint' (i + 1) (by omega))).const_mul a₁
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [F', Pi.add_apply]; ring
  have iG : ∀ i ≤ 2, Integrable (fun z => z ^ i * G z) := fun i hi =>
    ((hint i (by omega)).const_mul a₂).congr (Eventually.of_forall fun z => by simp only [G]; ring)
  have iG' : ∀ i ≤ 2, Integrable (fun z => z ^ i * G' z) := fun i hi =>
    ((hint' i (by omega)).const_mul a₂).congr (Eventually.of_forall fun z => by simp only [G']; ring)
  have iG'' : ∀ i ≤ 2, Integrable (fun z => z ^ i * G'' z) := fun i hi =>
    ((hint'' i (by omega)).const_mul a₂).congr (Eventually.of_forall fun z => by simp only [G'']; ring)
  simp_rw [hl]
  have m1 := integral_pow_mul_fp 1 hF hG hG' (fun i hi => iF i (by omega)) (iF' 1 (by omega))
    (fun i hi => iG i (by omega)) (fun i hi => iG' i (by omega)) (iG'' 1 (by omega))
  have m2 := integral_pow_mul_fp 2 hF hG hG' (fun i hi => iF i (by omega)) (iF' 2 le_rfl)
    (fun i hi => iG i (by omega)) (fun i hi => iG' i (by omega)) (iG'' 2 le_rfl)
  simp only [pow_one] at m1
  refine ⟨?_, ?_⟩
  · rw [m1]
    have h1 : ∀ y : ℝ, y ^ (1 - 1) * F y = a₁ * (y * P y) := fun y => by simp [F]
    simp_rw [h1]
    rw [integral_const_mul]
    norm_num
  · rw [m2]
    have h1 : ∀ y : ℝ, y ^ (2 - 1) * F y = a₁ * (y ^ 2 * P y) := fun y => by simp [F]; ring
    have h2 : ∀ y : ℝ, y ^ (2 - 2) * G y = a₂ * P y := fun y => by simp [G]
    simp_rw [h1, h2]
    rw [integral_const_mul, integral_const_mul]
    norm_num
    ring

/-- **The mean of the linear-noise approximation** (7.2.48), (4.4.84): if `P(t, ·)` solves
the corrected (7.2.35) with coefficient `a₁(t)` and `d/dt` commutes with `∫ dz` (`hswap`),
then `d⟨z⟩/dt = a₁(t) ⟨z⟩`. -/
theorem lna_mean_ode (a₁ a₂ : ℝ) (P : ℝ → ℝ → ℝ) (P' P'' : ℝ → ℝ) (t : ℝ)
    (hP : ∀ z, HasDerivAt (P t) (P' z) z) (hP' : ∀ z, HasDerivAt P' (P'' z) z)
    (hint : ∀ i ≤ 3, Integrable (fun z => z ^ i * P t z))
    (hint' : ∀ i ≤ 3, Integrable (fun z => z ^ i * P' z))
    (hint'' : ∀ i ≤ 2, Integrable (fun z => z ^ i * P'' z))
    (hswap : HasDerivAt (fun t => ∫ z, z * P t z) (∫ z, z * lnaFP a₁ a₂ (P t) z) t) :
    HasDerivAt (fun t => ∫ z, z * P t z) (a₁ * ∫ z, z * P t z) t := by
  rw [← (integral_moments_lnaFP a₁ a₂ (P t) P' P'' hP hP' hint hint' hint'').1]
  exact hswap

/-- **The second moment of the linear-noise approximation** (7.2.49), (4.4.85): under the
same hypotheses, `d⟨z²⟩/dt = 2 a₁(t) ⟨z²⟩ + a₂(t) ∫ P`. -/
theorem lna_second_moment_ode (a₁ a₂ : ℝ) (P : ℝ → ℝ → ℝ) (P' P'' : ℝ → ℝ) (t : ℝ)
    (hP : ∀ z, HasDerivAt (P t) (P' z) z) (hP' : ∀ z, HasDerivAt P' (P'' z) z)
    (hint : ∀ i ≤ 3, Integrable (fun z => z ^ i * P t z))
    (hint' : ∀ i ≤ 3, Integrable (fun z => z ^ i * P' z))
    (hint'' : ∀ i ≤ 2, Integrable (fun z => z ^ i * P'' z))
    (hswap : HasDerivAt (fun t => ∫ z, z ^ 2 * P t z) (∫ z, z ^ 2 * lnaFP a₁ a₂ (P t) z) t) :
    HasDerivAt (fun t => ∫ z, z ^ 2 * P t z)
      (2 * a₁ * (∫ z, z ^ 2 * P t z) + a₂ * ∫ z, P t z) t := by
  rw [← (integral_moments_lnaFP a₁ a₂ (P t) P' P'' hP hP' hint hint' hint'').2]
  exact hswap

end VanKampen

/-! ### (7.2.36)–(7.2.37): the Kramers–Moyal equation in intensive variables -/

/-- The right-hand side `-∂ₐ[α₁ q] + ½ ∂ₐ²[α₂ q]` of the Kramers–Moyal Fokker–Planck
equation (7.2.36). -/
def kmFP (α₁ α₂ q : ℝ → ℝ) (a : ℝ) : ℝ :=
  -deriv (fun a => α₁ a * q a) a + (1 / 2) * deriv (deriv (fun a => α₂ a * q a)) a

/-- **(7.2.36) ⟹ (7.2.37)**: if `αₙ(a) = Ω α̃ₙ(a/Ω)` (7.2.31), then the density
`P_x(x) = Ω P_a(Ωx)` of `x = a/Ω` satisfies `∂ₜ P_x = -∂ₓ[α̃₁ P_x] + (1/2Ω) ∂ₓ²[α̃₂ P_x]`, i.e.
the small-noise equation (6.3.1) with `ε² = 1/Ω` (7.2.38).  Pointwise:
`Ω · RHS(7.2.36)(Ωx) = RHS(6.3.1)(x)`. -/
theorem km_change_of_variables {Ω : ℝ} (hΩ : 0 < Ω) (α₁t α₂t P : ℝ → ℝ) (x : ℝ) :
    Ω * kmFP (fun a => Ω * α₁t (a / Ω)) (fun a => Ω * α₂t (a / Ω)) P (Ω * x)
      = snFP α₁t α₂t (Real.sqrt Ω)⁻¹ (fun x => Ω * P (Ω * x)) x := by
  have hs : Real.sqrt Ω ^ 2 = Ω := Real.sq_sqrt hΩ.le
  set g₁ : ℝ → ℝ := fun a => Ω * α₁t (a / Ω) * P a
  set g₂ : ℝ → ℝ := fun a => Ω * α₂t (a / Ω) * P a
  have h1 : (fun x => α₁t x * (Ω * P (Ω * x))) = fun x => g₁ (Ω * x) := by
    funext y; simp only [g₁]; field_simp
  have h2 : (fun x => α₂t x * (Ω * P (Ω * x))) = fun x => g₂ (Ω * x) := by
    funext y; simp only [g₂]; field_simp
  have d1 : deriv (fun x => g₁ (Ω * x)) x = Ω * deriv g₁ (Ω * x) := by
    simpa using deriv_comp_mul_left (f := g₁) Ω x
  have d2 : deriv (fun x => g₂ (Ω * x)) = fun x => Ω * deriv g₂ (Ω * x) := by
    funext y; simpa using deriv_comp_mul_left (f := g₂) Ω y
  have d3 : deriv (fun x => Ω * deriv g₂ (Ω * x)) x = Ω * (Ω * deriv (deriv g₂) (Ω * x)) := by
    rw [deriv_const_mul_field]
    simpa using congrArg (Ω * ·) (deriv_comp_mul_left (f := deriv g₂) Ω x)
  simp only [snFP, kmFP, h1, h2, d1, d2, d3]
  rw [inv_pow, hs]
  field_simp
  simp only [g₁, g₂]
  ring

/-! ### (7.2.59)–(7.2.61): the moment hierarchy -/

/-- **(7.2.60)**: suppose `∂ₜ P = Σ_{(m,n) ∈ T} c_{m,n} (-∂_z)ⁿ [z^{m-n} P]` (the right-hand
side of (7.2.34), truncated to a finite set `T` of indices; `c_{m,n}` is
`Ω^{-(m-2)/2} α̃ₙ^{(m-n)}(φ)/(n!(m-n)!)`), where `G (m,n)` is a derivative tower of
`z^{m-n} P`.  If `d/dt` commutes with `∫ dz` (`hswap`), then
`d⟨zᵏ⟩/dt = Σ_{(m,n) ∈ T} c_{m,n} k!/(k-n)! ⟨z^{(k-n)+(m-n)}⟩`, which is (7.2.60): the
falling factorial `k!/(k-n)!` vanishes for `n > k`, so the inner sum runs to `min(m, k)`. -/
theorem vk_moment_hierarchy (T : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℝ) (P : ℝ → ℝ → ℝ)
    (G : ℕ × ℕ → ℕ → ℝ → ℝ) (dP : ℝ → ℝ) (t : ℝ) (k : ℕ)
    (hG0 : ∀ p ∈ T, ∀ z, G p 0 z = z ^ (p.1 - p.2) * P t z)
    (hG : ∀ p ∈ T, ∀ j < p.2, ∀ z, HasDerivAt (G p j) (G p (j + 1) z) z)
    (hint : ∀ p ∈ T, ∀ j ≤ p.2, ∀ i ≤ k, Integrable (fun z => z ^ i * G p j z))
    (hpde : ∀ z, dP z = ∑ p ∈ T, c p * ((-1) ^ p.2 * G p p.2 z))
    (hswap : HasDerivAt (fun t => ∫ z, z ^ k * P t z) (∫ z, z ^ k * dP z) t) :
    HasDerivAt (fun t => ∫ z, z ^ k * P t z)
      (∑ p ∈ T, c p * (k.descFactorial p.2 : ℝ) * ∫ z, z ^ (k - p.2 + (p.1 - p.2)) * P t z) t := by
  have key : ∫ z, z ^ k * dP z
      = ∑ p ∈ T, c p * (k.descFactorial p.2 : ℝ) * ∫ z, z ^ (k - p.2 + (p.1 - p.2)) * P t z := by
    have e : ∀ z, z ^ k * dP z = ∑ p ∈ T, (c p * (-1) ^ p.2) * (z ^ k * G p p.2 z) := by
      intro z; rw [hpde, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    simp_rw [e]
    rw [integral_finset_sum _ fun p hp => (hint p hp p.2 le_rfl k le_rfl).const_mul _]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [integral_const_mul, integral_pow_mul_tower p.2 (G p) k (hG p hp) (hint p hp)]
    have e2 : ∀ z, z ^ (k - p.2) * G p 0 z = z ^ (k - p.2 + (p.1 - p.2)) * P t z := by
      intro z; rw [hG0 p hp, pow_add]; ring
    simp_rw [e2]
    have : ((-1 : ℝ) ^ p.2) * (-1) ^ p.2 = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    calc c p * (-1) ^ p.2 * ((-1) ^ p.2 * (k.descFactorial p.2 : ℝ)
          * ∫ z, z ^ (k - p.2 + (p.1 - p.2)) * P t z)
        = c p * ((-1) ^ p.2 * (-1) ^ p.2) * (k.descFactorial p.2 : ℝ)
          * ∫ z, z ^ (k - p.2 + (p.1 - p.2)) * P t z := by ring
      _ = _ := by rw [this, mul_one]
  rw [← key]
  exact hswap

end Gardiner
