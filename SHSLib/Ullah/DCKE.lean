/-
§8.2: the differential Chapman–Kolmogorov equation (8.13).

Adding the two limits (8.11) and (8.12) in the splitting (8.6) gives the dCKE

  ∂p(y,t)/∂t = -∂_i[A_i(y,t) p(y,t)] + ½ ∂²_{ij}[B_{ij}(y,t) p(y,t)]
                + ∫ dy' [W(y|y',t) p(y',t) - W(y'|y,t) p(y,t)].

Two versions are given: `Ullah.differentialCK`, which takes the two limits as
hypotheses, and `Ullah.differentialCK_of_kernel`, which derives them from the
Chapman–Kolmogorov equation, the normalization of the transition density, the
differentiability conditions (8.8), (8.9) and the jump condition.
-/
import SHSLib.Ullah.Limits

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Ullah

open Gardiner

variable {n : ℕ} {p : ℝ → Sp n → ℝ} {k : ℝ → Sp n → Sp n → ℝ} {W : Sp n → Sp n → ℝ}
  {A : Sp n → Fin n → ℝ} {B : Sp n → Fin n → Fin n → ℝ} {t : ℝ} {y : Sp n}

/-- **The differential Chapman–Kolmogorov equation (8.13)**, from the splitting (8.6)
and the two limits (8.11), (8.12).

`dp` is the time derivative (8.4) of `p(y, t)`; `Inear ε` is the value of
`I_{‖y-y'‖<ε}` and `jumpFar p W t ε y` that of `I_{‖y-y'‖≥ε}`. -/
theorem differentialCK {dp : ℝ} {Inear : ℝ → ℝ}
    (hdp : Tendsto (fun dt => timeQuot p t dt y) (𝓝[>] (0 : ℝ)) (𝓝 dp))
    (hsplit : ∀ ε > (0 : ℝ), ∀ᶠ dt in 𝓝[>] (0 : ℝ),
      timeQuot p t dt y = IQuot p k t dt y (ball y ε) + IQuot p k t dt y (ball y ε)ᶜ)
    (hnear : ∀ ε > (0 : ℝ),
      Tendsto (fun dt => IQuot p k t dt y (ball y ε)) (𝓝[>] (0 : ℝ)) (𝓝 (Inear ε)))
    (hfar : ∀ ε > (0 : ℝ), Tendsto (fun dt => IQuot p k t dt y (ball y ε)ᶜ)
      (𝓝[>] (0 : ℝ)) (𝓝 (jumpFar p W t ε y)))
    (hnear0 : Tendsto Inear (𝓝[>] (0 : ℝ)) (𝓝 (fpTerm p A B t y)))
    (hfar0 : Tendsto (fun ε => jumpFar p W t ε y) (𝓝[>] (0 : ℝ)) (𝓝 (jumpTerm p W t y))) :
    dp = fpTerm p A B t y + jumpTerm p W t y := by
  -- (8.6): for every `ε > 0` the derivative is the sum of the two contributions
  have hεeq : ∀ ε > (0 : ℝ), dp = Inear ε + jumpFar p W t ε y := by
    intro ε hε
    refine tendsto_nhds_unique hdp (((hnear ε hε).add (hfar ε hε)).congr' ?_)
    filter_upwards [hsplit ε hε] with dt h using h.symm
  -- now let `ε → 0`
  have h1 : Tendsto (fun _ : ℝ => dp) (𝓝[>] (0 : ℝ))
      (𝓝 (fpTerm p A B t y + jumpTerm p W t y)) := by
    refine (hnear0.add hfar0).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using (hεeq ε hε).symm
  exact tendsto_nhds_unique tendsto_const_nhds h1

/-- **The differential Chapman–Kolmogorov equation (8.13)**, assembled from the
primitive assumptions of §8.2.

The hypotheses are, in order: the differentiability (8.4) of `p(y, t)` in time; the
Chapman–Kolmogorov equation (8.3), the normalization `∫ dy' p(y',t+Δt|y,t) = 1` and
the integrability needed to combine them; the integrability of the terms of the
Taylor expansion (8.7) on the ball `‖q‖ < ε`; the interchange of the partial
derivatives with the `q`-integration, which the text performs implicitly when it
recognizes the conditional moments; the differentiability conditions (8.8), (8.9),
each split into the limit `Δt → 0` at fixed `ε` and the subsequent `ε → 0` limit
which removes the `o(ε)`; the vanishing of the remainder; and finally the jump
condition, in the form of the limit of `I_{‖y-y'‖≥ε}` and the integrability of the
jump integrand. -/
theorem differentialCK_of_kernel [NeZero n] {dp : ℝ}
    {a : ℝ → Fin n → ℝ} {b : ℝ → Fin n → Fin n → ℝ} {r : ℝ → ℝ}
    (hdp : Tendsto (fun dt => timeQuot p t dt y) (𝓝[>] (0 : ℝ)) (𝓝 dp))
    (hCK : ∀ dt > (0 : ℝ), p (t + dt) y = ∫ y', k dt y' y * p t y')
    (hnorm : ∀ dt > (0 : ℝ), ∫ y', k dt y y' = 1)
    (hgain : ∀ dt > (0 : ℝ), Integrable fun y' => k dt y' y * p t y')
    (hloss : ∀ dt > (0 : ℝ), Integrable fun y' => k dt y y')
    (hflux : ∀ dt > (0 : ℝ), Integrable (flux p k t dt y))
    (hfq : ∀ dt > (0 : ℝ), ∀ ε > (0 : ℝ),
      IntegrableOn (fun q => fq p k t dt y q) (ball (0 : Sp n) ε))
    (hT1 : ∀ dt > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ i,
      IntegrableOn (fun q => q i * pd (fun w => fq p k t dt w q) i y) (ball (0 : Sp n) ε))
    (hT2 : ∀ dt > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ i j,
      IntegrableOn (fun q => q i * q j * pd2 (fun w => fq p k t dt w q) i j y)
        (ball (0 : Sp n) ε))
    (hRemInt : ∀ dt > (0 : ℝ), ∀ ε > (0 : ℝ),
      IntegrableOn (fun q => taylorRem (fun w => fq p k t dt w q) y (y - q))
        (ball (0 : Sp n) ε))
    (hswap₁ : ∀ dt > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ i,
      ∫ q in ball (0 : Sp n) ε, q i * pd (fun w => fq p k t dt w q) i y
        = pd (fun w => Mom1 k dt ε w i * p t w) i y)
    (hswap₂ : ∀ dt > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ i j,
      ∫ q in ball (0 : Sp n) ε, q i * q j * pd2 (fun w => fq p k t dt w q) i j y
        = pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y)
    (hA : ∀ ε > (0 : ℝ), ∀ i,
      Tendsto (fun dt : ℝ => (1 / dt) * pd (fun w => Mom1 k dt ε w i * p t w) i y)
        (𝓝[>] (0 : ℝ)) (𝓝 (a ε i)))
    (hAeps : ∀ i, Tendsto (fun ε => a ε i) (𝓝[>] (0 : ℝ))
      (𝓝 (pd (fun w => A w i * p t w) i y)))
    (hB : ∀ ε > (0 : ℝ), ∀ i j,
      Tendsto (fun dt : ℝ => (1 / dt) * pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y)
        (𝓝[>] (0 : ℝ)) (𝓝 (b ε i j)))
    (hBeps : ∀ i j, Tendsto (fun ε => b ε i j) (𝓝[>] (0 : ℝ))
      (𝓝 (pd2 (fun w => B w i j * p t w) i j y)))
    (hRlim : ∀ ε > (0 : ℝ),
      Tendsto (fun dt : ℝ => (1 / dt) * Rem p k t dt ε y) (𝓝[>] (0 : ℝ)) (𝓝 (r ε)))
    (hReps : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hfar : ∀ ε > (0 : ℝ), Tendsto (fun dt => IQuot p k t dt y (ball y ε)ᶜ)
      (𝓝[>] (0 : ℝ)) (𝓝 (jumpFar p W t ε y)))
    (hjump : Integrable fun y' => W y y' * p t y' - W y' y * p t y) :
    dp = fpTerm p A B t y + jumpTerm p W t y := by
  refine differentialCK (Inear := fun ε => -(∑ i, a ε i) + (1 / 2) * ∑ i, ∑ j, b ε i j + r ε)
    hdp ?_ ?_ hfar (near_limit_eps hAeps hBeps hReps) (jumpFar_tendsto hjump)
  · -- (8.6)
    intro ε _
    filter_upwards [self_mem_nhdsWithin] with dt hdt
    rw [timeQuot_eq_IQuot_univ (hCK dt hdt) (hnorm dt hdt) (hgain dt hdt) (hloss dt hdt),
      IQuot_split (hflux dt hdt)]
  · -- the near region
    intro ε hε
    refine near_tendsto ?_ (hA ε hε) (hB ε hε) (hRlim ε hε)
    filter_upwards [self_mem_nhdsWithin] with dt hdt
    exact near_expansion (hfq dt hdt ε hε) (hT1 dt hdt ε hε) (hT2 dt hdt ε hε)
      (hRemInt dt hdt ε hε) (hswap₁ dt hdt ε hε) (hswap₂ dt hdt ε hε)

/-- A consistency check: the hypotheses of `Ullah.differentialCK` are simultaneously
satisfiable, so the theorem is not vacuous.  (The witness is the degenerate process
with `p = 0`, `k = 0`, `W = 0`.) -/
example (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (t : ℝ) (y : Sp n) :
    (0 : ℝ) = fpTerm (fun _ _ => (0 : ℝ)) A B t y
      + jumpTerm (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) t y := by
  have hpd : ∀ j : Fin n, (pd (fun _ : Sp n => (0 : ℝ)) j) = fun _ => 0 := by
    intro j; funext z; simp [pd]
  refine differentialCK (p := fun _ _ => (0 : ℝ)) (k := fun _ _ _ => (0 : ℝ))
    (W := fun _ _ => (0 : ℝ)) (A := A) (B := B) (Inear := fun _ => 0) ?_ ?_ ?_ ?_ ?_ ?_
  · simp [timeQuot]
  · intro ε _; filter_upwards with dt; simp [timeQuot, IQuot, flux]
  · intro ε _; simp [IQuot, flux]
  · intro ε _; simp [IQuot, flux, jumpFar]
  · have h0 : fpTerm (fun _ _ => (0 : ℝ)) A B t y = 0 := by
      simp only [fpTerm, mul_zero, pd2, hpd]
      simp
    rw [h0]; simp
  · simp [jumpFar, jumpTerm]

end Ullah
