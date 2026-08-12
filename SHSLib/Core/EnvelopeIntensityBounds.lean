/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Discharging the hypotheses of Lemma 2 from a growth envelope

`SHS.lemma2_bounded_implies_finite` (Hespanha 2005, Lemma 2) derives the
integrability conditions (15)–(16) of Theorem 2 from *assumed* continuous bounds
`α(t)` on the transition intensities and `β(t)` on the test function along the
sample paths.  For a model whose intensities and test function grow at most
polynomially in the state, those bounds need not be assumed: they follow from a
continuous envelope for the sample path, such as the one produced by
`SHS.hybrid_path_growth_bound` or by
`SHS.exists_hasGlobalFlow_of_linear_growth` (the envelope
`ODEFlow.linearGrowthBound`, which is continuous in time).

The main result `SHS.lemma2_of_polynomial_bounds` composes the polynomial bounds
with the envelope: `α(s) = c_λ(1 + E(s))^{p_λ}` and
`β(s) = c_ψ(1 + max(E(s), c_φ))^{p_ψ}`, where `c_φ` bounds the reset images.
-/
import SHSLib.Core.GronwallGrowthBound

open MeasureTheory Set

noncomputable section

/-- **Lemma 2 for polynomially bounded data.**  If the sample path obeys a
continuous envelope `E`, the intensities are bounded by `c_λ(1 + ‖x‖)^{p_λ}`, the
test function by `c_ψ(1 + ‖x‖)^{p_ψ}` and the reset images by `max ‖x‖ c_φ`, then
the integrability conditions (15)–(16) of Theorem 2 hold. -/
theorem SHS.lemma2_of_polynomial_bounds
    {Q : Type*} [Fintype Q] {n m : ℕ}
    (S : SHS Q n m) (ψ : SHS.TestFunction Q n) (z₀ : SHS.InitialCondition Q n)
    (t : ℝ) (ht : z₀.t₀ ≤ t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q_proc : ℝ → Ω → Q) (x_proc : ℝ → Ω → EuclideanSpace ℝ (Fin n))
    -- a continuous envelope for the sample path
    (env : ℝ → ℝ) (henv_cont : Continuous env)
    (hpath : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc z₀.t₀ t, ‖x_proc s ω‖ ≤ env s)
    -- polynomial bound on the intensities
    (cI : ℝ) (hcI : 0 ≤ cI) (pI : ℕ)
    (hint_poly : ∀ ℓ q x s, S.intensity ℓ q x s ≤ cI * (1 + ‖x‖) ^ pI)
    -- polynomial bound on the test function
    (cpsi : ℝ) (hcpsi : 0 ≤ cpsi) (ppsi : ℕ)
    (hpsi_poly : ∀ q x s, |ψ.toFun q x s| ≤ cpsi * (1 + ‖x‖) ^ ppsi)
    -- bound on the reset images
    (cphi : ℝ) (hcphi : 0 ≤ cphi)
    (hreset : ∀ ℓ q x s, ‖S.phi_x ℓ q x s‖ ≤ max ‖x‖ cphi)
    (hmeas1 : AEStronglyMeasurable (fun ω => ∫ s in Set.Icc z₀.t₀ t,
        ∑ ℓ : Fin m, S.intensity ℓ (q_proc s ω) (x_proc s ω) s) P)
    (hmeas2 : AEStronglyMeasurable (fun ω => ∫ s in Set.Icc z₀.t₀ t,
        ∑ ℓ : Fin m, |ψ.toFun (S.phi_q ℓ (q_proc s ω) (x_proc s ω) s)
                        (S.phi_x ℓ (q_proc s ω) (x_proc s ω) s) s -
                      ψ.toFun (q_proc s ω) (x_proc s ω) s| *
          S.intensity ℓ (q_proc s ω) (x_proc s ω) s) P) :
    Integrable (fun ω => ∫ s in Set.Icc z₀.t₀ t,
        ∑ ℓ : Fin m, S.intensity ℓ (q_proc s ω) (x_proc s ω) s) P ∧
    Integrable (fun ω => ∫ s in Set.Icc z₀.t₀ t,
        ∑ ℓ : Fin m, |ψ.toFun (S.phi_q ℓ (q_proc s ω) (x_proc s ω) s)
                        (S.phi_x ℓ (q_proc s ω) (x_proc s ω) s) s -
                      ψ.toFun (q_proc s ω) (x_proc s ω) s| *
          S.intensity ℓ (q_proc s ω) (x_proc s ω) s) P := by
  classical
  -- the envelope is nonnegative wherever the path is defined; use its positive part
  set envp : ℝ → ℝ := fun s => max (env s) 0 with henvp
  have henvp_cont : Continuous envp := henv_cont.max continuous_const
  have henvp_nonneg : ∀ s, 0 ≤ envp s := fun s => le_max_right _ _
  have hpathp : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc z₀.t₀ t, ‖x_proc s ω‖ ≤ envp s := by
    filter_upwards [hpath] with ω hω s hs
    exact le_trans (hω s hs) (le_max_left _ _)
  set alpha : ℝ → ℝ := fun s => cI * (1 + envp s) ^ pI with halpha
  set beta : ℝ → ℝ := fun s => cpsi * (1 + max (envp s) cphi) ^ ppsi with hbeta
  have halpha_cont : Continuous alpha := by
    rw [halpha]
    exact continuous_const.mul ((continuous_const.add henvp_cont).pow pI)
  have hbeta_cont : Continuous beta := by
    rw [hbeta]
    exact continuous_const.mul
      ((continuous_const.add (henvp_cont.max continuous_const)).pow ppsi)
  have halpha_nonneg : ∀ s, 0 ≤ alpha s := fun s =>
    mul_nonneg hcI (pow_nonneg (by linarith [henvp_nonneg s]) _)
  have hbeta_nonneg : ∀ s, 0 ≤ beta s := fun s =>
    mul_nonneg hcpsi (pow_nonneg (by
      have : 0 ≤ max (envp s) cphi := le_trans (henvp_nonneg s) (le_max_left _ _)
      linarith) _)
  refine S.lemma2_bounded_implies_finite ψ z₀ alpha halpha_cont halpha_nonneg beta hbeta_cont
    hbeta_nonneg t ht P q_proc x_proc ?_ ?_ ?_ hmeas1 hmeas2
  · -- intensities
    intro ℓ
    filter_upwards [hpathp] with ω hω s hs
    refine le_trans (hint_poly ℓ (q_proc s ω) (x_proc s ω) s) ?_
    have hmono : (1 + ‖x_proc s ω‖) ^ pI ≤ (1 + envp s) ^ pI :=
      pow_le_pow_left₀ (by linarith [norm_nonneg (x_proc s ω)]) (by linarith [hω s hs]) pI
    exact mul_le_mul_of_nonneg_left hmono hcI
  · -- test function
    filter_upwards [hpathp] with ω hω s hs
    refine le_trans (hpsi_poly (q_proc s ω) (x_proc s ω) s) ?_
    have hle : ‖x_proc s ω‖ ≤ max (envp s) cphi := le_trans (hω s hs) (le_max_left _ _)
    have hmono : (1 + ‖x_proc s ω‖) ^ ppsi ≤ (1 + max (envp s) cphi) ^ ppsi :=
      pow_le_pow_left₀ (by linarith [norm_nonneg (x_proc s ω)]) (by linarith) ppsi
    exact mul_le_mul_of_nonneg_left hmono hcpsi
  · -- test function at the reset images
    intro ℓ
    filter_upwards [hpathp] with ω hω s hs
    refine le_trans (hpsi_poly _ _ s) ?_
    have hle : ‖S.phi_x ℓ (q_proc s ω) (x_proc s ω) s‖ ≤ max (envp s) cphi :=
      le_trans (hreset ℓ (q_proc s ω) (x_proc s ω) s)
        (max_le_max (hω s hs) le_rfl)
    have hmono : (1 + ‖S.phi_x ℓ (q_proc s ω) (x_proc s ω) s‖) ^ ppsi
        ≤ (1 + max (envp s) cphi) ^ ppsi :=
      pow_le_pow_left₀ (by linarith [norm_nonneg (S.phi_x ℓ (q_proc s ω) (x_proc s ω) s)])
        (by linarith) ppsi
    exact mul_le_mul_of_nonneg_left hmono hcpsi

end
