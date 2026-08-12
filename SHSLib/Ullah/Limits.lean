/-
§8.2, the two limits (8.11) and (8.12).

`fpTerm` is the right-hand side of (8.11), the drift–diffusion (Fokker–Planck) part
produced by the near region, and `jumpTerm` is the right-hand side of (8.12), the
jump part produced by the far region.

The limits are taken in two stages, exactly as in the text: first `Δt → 0` at fixed
`ε`, then `ε → 0`, the second stage absorbing the `o(ε)` errors of (8.8), (8.9).
-/
import SHSLib.Ullah.Near

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Ullah

open Gardiner

variable {n : ℕ}

/-- The right-hand side of (8.11): `-∂_i[A_i(y,t) p(y,t)] + ½ ∂²_{ij}[B_{ij}(y,t) p(y,t)]`. -/
def fpTerm (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (t : ℝ) (y : Sp n) : ℝ :=
  -(∑ i, pd (fun w => A w i * p t w) i y)
    + (1 / 2) * ∑ i, ∑ j, pd2 (fun w => B w i j * p t w) i j y

/-- The jump contribution of the far region `‖y - y'‖ ≥ ε`, before `ε → 0`. -/
def jumpFar (p : ℝ → Sp n → ℝ) (W : Sp n → Sp n → ℝ) (t ε : ℝ) (y : Sp n) : ℝ :=
  ∫ y' in (ball y ε)ᶜ, (W y y' * p t y' - W y' y * p t y)

/-- The right-hand side of (8.12):
`∫ dy' [W(y|y',t) p(y',t) - W(y'|y,t) p(y,t)]`. -/
def jumpTerm (p : ℝ → Sp n → ℝ) (W : Sp n → Sp n → ℝ) (t : ℝ) (y : Sp n) : ℝ :=
  ∫ y', (W y y' * p t y' - W y' y * p t y)

variable {p : ℝ → Sp n → ℝ} {k : ℝ → Sp n → Sp n → ℝ} {W : Sp n → Sp n → ℝ}
  {A : Sp n → Fin n → ℝ} {B : Sp n → Fin n → Fin n → ℝ} {t ε : ℝ} {y : Sp n}

/-! ### The near region: `Δt → 0` at fixed `ε` -/

/-- The limit `Δt → 0` of the near contribution, at fixed `ε`: given the expansion of
`I_{‖q‖<ε}` and the existence of the limits of the two moment terms and of the
remainder, the near contribution converges. -/
theorem near_tendsto {a : Fin n → ℝ} {b : Fin n → Fin n → ℝ} {r : ℝ}
    (hexp : ∀ᶠ dt in 𝓝[>] (0 : ℝ), IQuot p k t dt y (ball y ε)
      = (1 / dt) * (-(∑ i, pd (fun w => Mom1 k dt ε w i * p t w) i y)
        + (1 / 2) * ∑ i, ∑ j, pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y
        + Rem p k t dt ε y))
    (hA : ∀ i, Tendsto (fun dt : ℝ => (1 / dt) * pd (fun w => Mom1 k dt ε w i * p t w) i y)
      (𝓝[>] (0 : ℝ)) (𝓝 (a i)))
    (hB : ∀ i j, Tendsto
      (fun dt : ℝ => (1 / dt) * pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y)
      (𝓝[>] (0 : ℝ)) (𝓝 (b i j)))
    (hR : Tendsto (fun dt : ℝ => (1 / dt) * Rem p k t dt ε y) (𝓝[>] (0 : ℝ)) (𝓝 r)) :
    Tendsto (fun dt => IQuot p k t dt y (ball y ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(∑ i, a i) + (1 / 2) * ∑ i, ∑ j, b i j + r)) := by
  have hdist : ∀ dt : ℝ,
      (1 / dt) * (-(∑ i, pd (fun w => Mom1 k dt ε w i * p t w) i y)
        + (1 / 2) * ∑ i, ∑ j, pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y
        + Rem p k t dt ε y)
      = -(∑ i, (1 / dt) * pd (fun w => Mom1 k dt ε w i * p t w) i y)
        + (1 / 2) * ∑ i, ∑ j, (1 / dt) * pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y
        + (1 / dt) * Rem p k t dt ε y := by
    intro dt
    have s1 : (1 / dt) * ∑ i, pd (fun w => Mom1 k dt ε w i * p t w) i y
        = ∑ i, (1 / dt) * pd (fun w => Mom1 k dt ε w i * p t w) i y := Finset.mul_sum _ _ _
    have s2 : (1 / dt) * ∑ i, ∑ j, pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y
        = ∑ i, ∑ j, (1 / dt) * pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    calc (1 / dt) * (-(∑ i, pd (fun w => Mom1 k dt ε w i * p t w) i y)
            + (1 / 2) * ∑ i, ∑ j, pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y
            + Rem p k t dt ε y)
        = -((1 / dt) * ∑ i, pd (fun w => Mom1 k dt ε w i * p t w) i y)
            + (1 / 2) * ((1 / dt) * ∑ i, ∑ j, pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y)
            + (1 / dt) * Rem p k t dt ε y := by ring
      _ = _ := by rw [s1, s2]
  have key : Tendsto (fun dt : ℝ =>
      -(∑ i, (1 / dt) * pd (fun w => Mom1 k dt ε w i * p t w) i y)
        + (1 / 2) * ∑ i, ∑ j, (1 / dt) * pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y
        + (1 / dt) * Rem p k t dt ε y) (𝓝[>] (0 : ℝ))
      (𝓝 (-(∑ i, a i) + (1 / 2) * ∑ i, ∑ j, b i j + r)) :=
    (((tendsto_finset_sum _ fun i _ => hA i).neg).add
      ((tendsto_finset_sum _ fun i _ =>
        tendsto_finset_sum _ fun j _ => hB i j).const_mul (1 / 2))).add hR
  refine key.congr' ?_
  filter_upwards [hexp] with dt h using by rw [← hdist dt, ← h]

/-- The limit `ε → 0` of the near contribution: this is (8.11).  The hypotheses are
(8.8), (8.9) — the `Δt → 0` limits of the moment terms equal the drift and diffusion
terms up to `o(ε)` — and the fact that the remainder term is `o(1)`. -/
theorem near_limit_eps {a : ℝ → Fin n → ℝ} {b : ℝ → Fin n → Fin n → ℝ} {r : ℝ → ℝ}
    (hA : ∀ i, Tendsto (fun ε => a ε i) (𝓝[>] (0 : ℝ))
      (𝓝 (pd (fun w => A w i * p t w) i y)))
    (hB : ∀ i j, Tendsto (fun ε => b ε i j) (𝓝[>] (0 : ℝ))
      (𝓝 (pd2 (fun w => B w i j * p t w) i j y)))
    (hr : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε => -(∑ i, a ε i) + (1 / 2) * ∑ i, ∑ j, b ε i j + r ε) (𝓝[>] (0 : ℝ))
      (𝓝 (fpTerm p A B t y)) := by
  have key : Tendsto (fun ε => -(∑ i, a ε i) + (1 / 2) * ∑ i, ∑ j, b ε i j + r ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(∑ i, pd (fun w => A w i * p t w) i y)
        + (1 / 2) * ∑ i, ∑ j, pd2 (fun w => B w i j * p t w) i j y + 0)) :=
    (((tendsto_finset_sum _ fun i _ => hA i).neg).add
      ((tendsto_finset_sum _ fun i _ =>
        tendsto_finset_sum _ fun j _ => hB i j).const_mul (1 / 2))).add hr
  simpa [fpTerm] using key

/-! ### The far region: `ε → 0` -/

/-- The volume of a small ball tends to `0`. -/
lemma tendsto_volume_ball [NeZero n] (y : Sp n) :
    Tendsto (fun ε : ℝ => volume (ball y ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : Fintype.card (Fin n) = n := by simp
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  simp only [EuclideanSpace.volume_ball, hc]
  have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have h2 : Tendsto (fun ε : ℝ => (ENNReal.ofReal ε) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [zero_pow (NeZero.ne n)] using ENNReal.Tendsto.pow (n := n) h1
  have h3 := ENNReal.Tendsto.mul_const h2
    (Or.inr (ENNReal.ofReal_ne_top (r := √Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))))
  simpa using h3

/-- "As `ε → 0` the region of integration approaches the full state space": the far
contribution converges to the jump term (8.12) of the dCKE. -/
theorem jumpFar_tendsto [NeZero n]
    (hg : Integrable fun y' => W y y' * p t y' - W y' y * p t y) :
    Tendsto (fun ε => jumpFar p W t ε y) (𝓝[>] (0 : ℝ)) (𝓝 (jumpTerm p W t y)) := by
  have hsmall : Tendsto
      (fun ε : ℝ => ∫ y' in ball y ε, (W y y' * p t y' - W y' y * p t y))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hg.tendsto_setIntegral_nhds_zero (tendsto_volume_ball y)
  have heq : ∀ ε : ℝ, jumpFar p W t ε y
      = jumpTerm p W t y - ∫ y' in ball y ε, (W y y' * p t y' - W y' y * p t y) := by
    intro ε
    have := integral_add_compl (measurableSet_ball (x := y) (ε := ε)) hg
    simp only [jumpFar, jumpTerm]
    linarith [this]
  simpa [heq] using (tendsto_const_nhds (x := jumpTerm p W t y)
    (f := 𝓝[>] (0 : ℝ))).sub hsmall

end Ullah
