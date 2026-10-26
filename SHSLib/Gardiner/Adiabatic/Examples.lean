/-
# Concrete instances of the main theorems of `SHSLib.Gardiner.Adiabatic`

Every main theorem of the adiabatic-elimination layer is applied here (or next to its
statement) to a concrete, non-degenerate instance.

* Brownian motion (§6.4, (6.4.1)–(6.4.18)): explicit solutions of the Kramers moment equations
  for harmonically bound particles (`Gardiner.Adiabatic.harmonic_instance`) and for the
  OU-driven white-noise limit (`Gardiner.Adiabatic.ouDriven_instance`), and the stationary
  statistics (`Gardiner.Adiabatic.harmonic_stationary_instance`).
* Projector algebra (§6.4.1, §6.5, §6.6): the persistent random walk / telegraph-noise operators
  on `ℂ × ℂ` for the exact elimination (6.4.50)–(6.4.51)
  (`Gardiner.Adiabatic.tg_exact_elimination_instance`), its three-operator version (6.5.69)
  with `PL₃ ≠ L₃P` (`Gardiner.Adiabatic.tg_exact_elimination_L3_instance`) and the commuting case
  (6.5.24)–(6.5.26) (`Gardiner.Adiabatic.tg_commuting_instance`); an explicit solution of a
  two-state Kramers-type system on `ℝ × ℝ` for the time-domain equations (6.4.42)–(6.4.44)
  (`Gardiner.Adiabatic.proj_time_instance`); the Laplace-transformed equation (6.4.47) for
  `v(t) = e^{-4t}` (`Gardiner.Adiabatic.laplace_instance`).
-/
import SHSLib.Gardiner.Adiabatic.Chemical
import SHSLib.Gardiner.Adiabatic.Telegraph

open MeasureTheory Filter Topology Set

noncomputable section

namespace Gardiner.Adiabatic

/-! ### Brownian motion -/

/-- The second moments built from the mean propagator solve the Kramers moment equations. -/
lemma harmonic_moments_sol {τ k D c lp lm : ℝ} (hτ : 0 < τ) (hk0 : 0 < k) (hne : lp ≠ lm)
    (hs : τ * (lp + lm) = -1) (hp : τ * (lp * lm) = k) (t : ℝ) :
    HasDerivAt (fun t => D / k + (c + 1) * harmMu lp lm t ^ 2)
        (2 * ((c + 1) * (harmMu lp lm t * harmNu lp lm t))) t ∧
      HasDerivAt (fun t => (c + 1) * (harmMu lp lm t * harmNu lp lm t))
        ((τ * (D / τ + (c + 1) * harmNu lp lm t ^ 2) - k * (D / k + (c + 1) * harmMu lp lm t ^ 2)
          - (c + 1) * (harmMu lp lm t * harmNu lp lm t)) / τ) t ∧
      HasDerivAt (fun t => D / τ + (c + 1) * harmNu lp lm t ^ 2)
        ((-2 * k * ((c + 1) * (harmMu lp lm t * harmNu lp lm t))
          - 2 * (D / τ + (c + 1) * harmNu lp lm t ^ 2) + 2 * D / τ) / τ) t := by
  have hmu := (harm_mean_sol hτ hne hs hp t).1
  have hnu := (harm_mean_sol hτ hne hs hp t).2
  have hk : k ≠ 0 := hk0.ne'
  refine ⟨?_, ?_, ?_⟩
  · convert ((hmu.pow 2).const_mul (c + 1)).const_add (D / k) using 1
    push_cast; ring
  · convert (hmu.mul hnu).const_mul (c + 1) using 1
    field_simp
    ring
  · convert ((hnu.pow 2).const_mul (c + 1)).const_add (D / τ) using 1
    push_cast; field_simp; ring

/-- **Instance of `harmonic_variance_rate` (and hence of `harmonic_mean_rate`).**  For every
`τ, k > 0` with `4kτ < 1`, every `D` and every initial excess variance `c`, the functions
`m₁ = μ`, `m₂ = ν`, `S = D/k + (c + 1)μ²`, `X = (c + 1)μν`, `V = D/τ + (c + 1)ν²` (with the
propagator `μ = harmMu`, `ν = harmNu`) solve the Kramers moment equations with thermalised initial
velocity, and the Kramers variance is within `8kτ|c|` of the Smoluchowski variance. -/
theorem harmonic_instance {τ k D c : ℝ} (hτ : 0 < τ) (hk : 0 < k) (hkτ : 4 * k * τ < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    let lp := (-1 + Real.sqrt (1 - 4 * k * τ)) / (2 * τ)
    let lm := (-1 - Real.sqrt (1 - 4 * k * τ)) / (2 * τ)
    let S := fun t => D / k + (c + 1) * harmMu lp lm t ^ 2
    |(S t - harmMu lp lm t ^ 2) - (D / k + ((S 0 - harmMu lp lm 0 ^ 2) - D / k)
        * Real.exp (-2 * k * t))|
      ≤ 8 * k * τ * |(S 0 - harmMu lp lm 0 ^ 2) - D / k| ∧
    |harmMu lp lm t - harmMu lp lm 0 * Real.exp (-k * t)| ≤ 4 * k * τ * |harmMu lp lm 0| := by
  intro lp lm S
  obtain ⟨hne, hs, hp⟩ := harm_roots hτ hkτ
  have hmu := fun t => (harm_mean_sol hτ hne hs hp t).1
  have hnu := fun t => (harm_mean_sol hτ hne hs hp t).2
  have hnu0 : harmNu lp lm 0 = 0 := by simp [harmNu]
  have hsol := fun t => harmonic_moments_sol (D := D) (c := c) hτ hk hne hs hp t
  exact ⟨harmonic_variance_rate hτ hk hkτ (harmMu lp lm) (harmNu lp lm) S
    (fun t => (c + 1) * (harmMu lp lm t * harmNu lp lm t))
    (fun t => D / τ + (c + 1) * harmNu lp lm t ^ 2) hmu hnu (fun t => (hsol t).1)
    (fun t => (hsol t).2.1) (fun t => (hsol t).2.2) (by simp [hnu0]) (by simp [hnu0]) ht,
    harmonic_mean_rate _ _ hτ hk hkτ.le hmu hnu hnu0 ht⟩

/-- **Instance of `harmonic_stationary`**: `τ = 1/8`, `k = 1`, `D = 2`; the stationary
second moments `⟨x²⟩ = 2`, `⟨xv⟩ = 0`, `⟨v²⟩ = 16` are the unique stationary point, and
`⟨x²⟩ = D/k` is the Smoluchowski value. -/
theorem harmonic_stationary_instance :
    (2 : ℝ) = 2 / 1 ∧ (0 : ℝ) = 0 ∧ (16 : ℝ) = 2 / (1 / 8) :=
  harmonic_stationary (τ := 1 / 8) (k := 1) (D := 2) (S := 2) (X := 0) (V := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Instance of `ouDriven_variance_rate` (6.4.6)–(6.4.10)**: with `⟨η⟩ = 0`,
`⟨η²⟩ = 1/(2τ)` (stationary), `⟨xη⟩ = √(2D)(1 - e^{-t/τ})/2` and
`⟨x²⟩ = 2D(t - τ(1 - e^{-t/τ}))`, the variance of `x` is within `2Dτ` of `2Dt`. -/
theorem ouDriven_instance {τ D : ℝ} (hτ : 0 < τ) (hD : 0 ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    let S := fun t => 2 * D * (t - τ * (1 - Real.exp (-(1 / τ) * t)))
    0 ≤ ((S 0 - 0 ^ 2) + 2 * D * t) - (S t - 0 ^ 2) ∧
      ((S 0 - 0 ^ 2) + 2 * D * t) - (S t - 0 ^ 2) ≤ 2 * D * τ := by
  intro S
  set c := Real.sqrt (2 * D)
  have hc2 : c ^ 2 = 2 * D := Real.sq_sqrt (by linarith)
  have he := fun t => hasDerivAt_exp_mul (-(1 / τ)) t
  refine ouDriven_variance_rate hτ hD (fun _ => 0) (fun _ => 0) S
    (fun t => c / 2 * (1 - Real.exp (-(1 / τ) * t))) (fun _ => 1 / (2 * τ))
    (fun t => by simpa using hasDerivAt_const t (0 : ℝ))
    (fun t => by simpa using hasDerivAt_const t (0 : ℝ)) (fun t => ?_) (fun t => ?_)
    (fun t => ?_) rfl (by simp) rfl ht
  · convert (((hasDerivAt_id t).sub (((he t).const_sub 1).const_mul τ)).const_mul (2 * D))
      using 1
    simp only [show -(1 / τ) * t = -(t / τ) by ring]
    field_simp
    rw [show Real.sqrt (2 * D) * c = 2 * D from Real.mul_self_sqrt (by linarith)]
  · convert ((he t).const_sub 1).const_mul (c / 2) using 1
    field_simp; ring
  · convert hasDerivAt_const t (1 / (2 * τ)) using 1
    field_simp; ring

/-! ### Projector algebra on telegraph-noise operators -/

/-- **Instance of `exact_elimination` (6.4.50)–(6.4.51)** for the persistent random walk with
`γ = λ = c = 1`, `s = 1`: `K = γL₁ + (1 - P)L₂ = [[0, 0], [1, -2]]`, `G = (s - K)⁻¹`,
`ṽ = (1, 0)`. -/
theorem tg_exact_elimination_instance :
    ((1 : Module.End ℂ (ℂ × ℂ)) * (tgOp 1 0 (1 / 3) (1 / 3) * tgL2 1)) • ((1 : ℂ), (0 : ℂ))
        = ((0 : ℂ), (1 / 3 : ℂ)) ∧
      (tgOp 1 0 0 1 : Module.End ℂ (ℂ × ℂ)) • ((1 : ℂ), (0 : ℂ))
        = (tgP * tgL2 1 * tgOp 1 0 (1 / 3) (1 / 3) * tgL2 1) • ((1 : ℂ), (0 : ℂ))
          + ((2 / 3 : ℂ), (0 : ℂ)) := by
  have h := exact_elimination (P := tgP) (L₂ := tgL2 1) (tgOp 1 0 0 1)
    ((1 : ℂ) • tgL1 1 + (1 - tgP) * tgL2 1) (tgOp 1 0 (1 / 3) (1 / 3)) ((1 : ℂ), (0 : ℂ))
    ((0 : ℂ), (1 / 3 : ℂ)) ((2 / 3 : ℂ), (0 : ℂ)) ?_ ?_ ?_
  · refine ⟨by rw [one_mul]; exact h.1.symm, h.2⟩
  · simp only [tgP, tgL2, Module.End.mul_apply, Module.End.smul_def, tgOp_apply]
    ext <;> norm_num
  · simp only [tgP, tgL1, tgL2, tgOp_one, tgOp_smul, tgOp_mul, tgOp_neg, sub_eq_add_neg,
      tgOp_add, Module.End.smul_def, tgOp_apply]
    ext <;> norm_num
  · simp only [tgP, tgL1, tgL2, tgOp_one, tgOp_smul, tgOp_mul, tgOp_neg, sub_eq_add_neg,
      tgOp_add]
    congr 1 <;> norm_num

/-- **Instance of `exact_elimination_L3` (6.5.67)–(6.5.69) with `PL₃ ≠ L₃P`**: telegraph noise
with `γ = λ = c = 1`, the `α`-dependent drift `L₃ = tgL3 1 1` (non-commuting by
`tg_not_commute`), `s = 2`. -/
theorem tg_exact_elimination_L3_instance :
    (tgOp 2 0 0 2 : Module.End ℂ (ℂ × ℂ)) • ((1 : ℂ), (0 : ℂ))
      = (tgP * tgL3 1 1 + tgP * (tgL2 1 + tgL3 1 1) * tgOp (1 / 2) 0 (1 / 3) (1 / 3)
          * (tgL2 1 + (1 - tgP) * tgL3 1 1)) • ((1 : ℂ), (0 : ℂ)) + ((-1 / 3 : ℂ), (0 : ℂ)) ∧
      tgP * tgL3 1 1 ≠ tgL3 1 1 * tgP := by
  refine ⟨exact_elimination_L3 (P := tgP) (L₃ := tgL3 1 1) (tgOp 2 0 0 2)
    (tgL1 1 + (1 - tgP) * tgL2 1 + (1 - tgP) * tgL3 1 1) (tgOp (1 / 2) 0 (1 / 3) (1 / 3))
    (tgP * (tgL2 1 + tgL3 1 1)) (tgL2 1 + (1 - tgP) * tgL3 1 1) ((1 : ℂ), (0 : ℂ))
    ((0 : ℂ), (2 / 3 : ℂ)) ((-1 / 3 : ℂ), (0 : ℂ)) ?_ ?_ ?_, tg_not_commute 1 1 one_ne_zero⟩
  · simp only [tgP, tgL2, tgL3, tgOp_mul, tgOp_add, Module.End.smul_def, tgOp_apply]
    ext <;> norm_num
  · simp only [tgP, tgL1, tgL2, tgL3, tgOp_one, tgOp_mul, tgOp_neg, sub_eq_add_neg, tgOp_add,
      Module.End.smul_def, tgOp_apply]
    ext <;> norm_num
  · simp only [tgP, tgL1, tgL2, tgL3, tgOp_one, tgOp_mul, tgOp_neg, sub_eq_add_neg, tgOp_add]
    congr 1 <;> norm_num

/-- **Instance of `commuting_L3_v`, `commuting_L3_w` (6.5.24)–(6.5.26)**: an `α`-independent
drift `L₃ = a·id` commutes with the telegraph projector. -/
theorem tg_commuting_instance (lam : ℝ) (c a γ : ℂ) :
    tgP * (γ ^ 2 • tgL1 lam + γ • tgL2 c + tgOp a 0 0 a)
        = γ • (tgP * tgL2 c * (1 - tgP)) + tgOp a 0 0 a * tgP ∧
      (1 - tgP) * tgOp a 0 0 a = tgOp a 0 0 a * (1 - tgP) ∧
      (1 - tgP) * tgOp a 0 0 a * tgP = 0 ∧ tgP * tgOp a 0 0 a * (1 - tgP) = 0 := by
  have h3 : tgP * tgOp a 0 0 a = tgOp a 0 0 a * tgP := by
    simp only [tgP, tgOp_mul]; congr 1 <;> ring
  exact ⟨commuting_L3_v (tg_projHyp lam c) h3 γ, commuting_L3_w (tg_projHyp lam c) h3⟩

/-! ### Time domain and Laplace transform -/

/-- The operators of a two-state Kramers-type system on `ℝ × ℝ`: `P(x, y) = (x, 0)`,
`L₁(x, y) = (0, -3y)`, `L₂(x, y) = (2y, 2x)`. -/
def rP : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.inl ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)
def rL1 : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.inr ℝ ℝ ℝ).comp ((-3 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
def rL2 : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (2 : ℝ) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ))

@[simp] lemma rP_apply (p : ℝ × ℝ) : rP p = (p.1, 0) := rfl
@[simp] lemma rL1_apply (p : ℝ × ℝ) : rL1 p = (0, -3 * p.2) := by simp [rL1]
@[simp] lemma rL2_apply (p : ℝ × ℝ) : rL2 p = (2 * p.2, 2 * p.1) := by simp [rL2]

lemma r_projHyp : ProjHyp rP rL1 rL2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp

/-- **Instance of `hasDerivAt_proj_v`, `hasDerivAt_proj_w` (6.4.42)–(6.4.44)**: with `γ = 1`,
`p(t) = e^{t}(2, 1)` solves `∂ₜp = (γL₁ + L₂)p`, and `v = Pp`, `w = (1 - P)p` obey the split
equations. -/
theorem proj_time_instance (t : ℝ) :
    HasDerivAt (fun t => rP ((Real.exp t * 2, Real.exp t))) (rP (rL2 ((1 - rP)
      ((Real.exp t * 2, Real.exp t))))) t ∧
    HasDerivAt (fun t => (1 - rP) ((Real.exp t * 2, Real.exp t)))
      ((1 : ℝ) • rL1 ((1 - rP) ((Real.exp t * 2, Real.exp t)))
        + (1 - rP) (rL2 ((1 - rP) ((Real.exp t * 2, Real.exp t))))
        + rL2 (rP ((Real.exp t * 2, Real.exp t)))) t := by
  have hp : ∀ t, HasDerivAt (fun t => (Real.exp t * 2, Real.exp t))
      (((1 : ℝ) • rL1 + rL2) ((Real.exp t * 2, Real.exp t))) t := by
    intro t
    have := ((Real.hasDerivAt_exp t).mul_const 2).prodMk (Real.hasDerivAt_exp t)
    convert this using 1
    simp only [ContinuousLinearMap.add_apply, rL1_apply,
      rL2_apply, one_smul, Prod.mk_add_mk]
    ext <;> simp <;> ring
  exact ⟨hasDerivAt_proj_v r_projHyp 1 _ t (hp t), hasDerivAt_proj_w r_projHyp 1 _ t (hp t)⟩

/-- **Instance of `laplace_v_eq` (6.4.47)**: `v(t) = e^{-4t}`, `w = v`, `T = -4`; then
`s ṽ(s) = T w̃(s) + v(0)` at `s = 0`. -/
theorem laplace_instance :
    (0 : ℝ) • laplace (fun t => Real.exp (-4 * t)) 0
      = ((-4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (laplace (fun t => Real.exp (-4 * t)) 0)
        + Real.exp (-4 * 0) := by
  have hi : IntegrableOn (fun t => Real.exp (-0 * t) • Real.exp (-4 * t)) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 4)
    simpa using this
  refine laplace_v_eq ((-4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) _ _ 0 (fun t => ?_) hi hi ?_
  · simpa [mul_comm] using hasDerivAt_exp_mul (-4) t
  · simp only [neg_zero, zero_mul, Real.exp_zero, one_smul]
    have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-4 : ℝ) < 0))
    simpa [Function.comp_def] using this

end Gardiner.Adiabatic
