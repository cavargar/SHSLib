/-
§8.2, the near region `‖y - y'‖ < ε`: equations (8.7)–(8.11).

The substitution `y - y' = q` of (8.7), the auxiliary function
`f(y; q) = p(y + q, t + Δt | y, t) p(y, t)`, its Taylor expansion in the first
argument, the cancellation of the first two terms by the symmetry
`∫ f(y; q) dq = ∫ f(y; -q) dq`, and the appearance of the conditional moments
`⟨ΔY_i⟩_y`, `⟨ΔY_i ΔY_j⟩_y` of (8.8), (8.9).
-/
import SHSLib.Ullah.Basic
import SHSLib.Gardiner.HigherMoments

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Ullah

open Gardiner

variable {n : ℕ}

/-! ### The auxiliary function `f(y; q)` and the conditional moments -/

/-- The function `f(y; q) ≜ p(y + q, t + Δt | y, t) p(y, t)` of the text. -/
def fq (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (t dt : ℝ) (w q : Sp n) : ℝ :=
  k dt w (w + q) * p t w

/-- The first conditional moment `⟨ΔY_i⟩_y = ∫_{‖q‖<ε} dq q_i p(y+q, t+Δt|y,t)`. -/
def Mom1 (k : ℝ → Sp n → Sp n → ℝ) (dt ε : ℝ) (w : Sp n) (i : Fin n) : ℝ :=
  ∫ q in ball (0 : Sp n) ε, q i * k dt w (w + q)

/-- The second conditional moment
`⟨ΔY_i ΔY_j⟩_y = ∫_{‖q‖<ε} dq q_i q_j p(y+q, t+Δt|y,t)`. -/
def Mom2 (k : ℝ → Sp n → Sp n → ℝ) (dt ε : ℝ) (w : Sp n) (i j : Fin n) : ℝ :=
  ∫ q in ball (0 : Sp n) ε, q i * q j * k dt w (w + q)

/-- The third conditional moment, whose coefficient `C_{ijk}(y,t)` is shown in the
text to vanish. -/
def Mom3 (k : ℝ → Sp n → Sp n → ℝ) (dt ε : ℝ) (w : Sp n) (i j l : Fin n) : ℝ :=
  ∫ q in ball (0 : Sp n) ε, q i * q j * q l * k dt w (w + q)

/-- The remainder `o(‖q qᵀ‖)` of the Taylor expansion, integrated over the ball. -/
def Rem (p : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (t dt ε : ℝ) (y : Sp n) : ℝ :=
  ∫ q in ball (0 : Sp n) ε, taylorRem (fun w => fq p k t dt w q) y (y - q)

/-! ### The moments in the two coordinate systems -/

variable {p : ℝ → Sp n → ℝ} {k : ℝ → Sp n → Sp n → ℝ} {t dt ε : ℝ} {y : Sp n}

lemma Mom1_eq (w : Sp n) (i : Fin n) :
    Mom1 k dt ε w i = ∫ x in ball w ε, (x i - w i) * k dt w x := by
  rw [Mom1, setIntegral_ball_shift w ε fun x => (x i - w i) * k dt w x]
  simp

lemma Mom2_eq (w : Sp n) (i j : Fin n) :
    Mom2 k dt ε w i j = ∫ x in ball w ε, (x i - w i) * (x j - w j) * k dt w x := by
  rw [Mom2, setIntegral_ball_shift w ε fun x => (x i - w i) * (x j - w j) * k dt w x]
  simp

lemma Mom3_eq (w : Sp n) (i j l : Fin n) :
    Mom3 k dt ε w i j l = ∫ x in ball w ε, (x i - w i) * (x j - w j) * (x l - w l) * k dt w x := by
  rw [Mom3, setIntegral_ball_shift w ε fun x => (x i - w i) * (x j - w j) * (x l - w l) * k dt w x]
  simp

/-- (8.8): the drift condition, stated with the conditional moment `⟨ΔY_i⟩_y`.  It is
Gardiner's condition (ii), transported to the variable `q = y' - y`. -/
lemma condDrift_iff_mom {A : Sp n → Fin n → ℝ} :
    CondDrift k A ↔ ∃ C : ℝ, ∀ ε > 0, ∀ (i : Fin n) (w : Sp n), ∃ L : ℝ,
      Tendsto (fun dt : ℝ => (1 / dt) * Mom1 k dt ε w i) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
        |L - A w i| ≤ C * ε := by
  simp only [CondDrift, Mom1_eq]

/-- (8.9): the diffusion condition, stated with the conditional moment
`⟨ΔY_i ΔY_j⟩_y`.  It is Gardiner's condition (iii), transported to `q = y' - y`. -/
lemma condDiffusion_iff_mom {B : Sp n → Fin n → Fin n → ℝ} :
    CondDiffusion k B ↔ ∃ C : ℝ, ∀ ε > 0, ∀ (i j : Fin n) (w : Sp n), ∃ L : ℝ,
      Tendsto (fun dt : ℝ => (1 / dt) * Mom2 k dt ε w i j) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
        |L - B w i j| ≤ C * ε := by
  simp only [CondDiffusion, Mom2_eq]

/-- The vanishing of the third-order coefficient, the displayed chain of inequalities
after (8.9): if the third moments `(1/Δt) ⟨ΔY_i ΔY_j ΔY_l⟩_y` converge to
`C_{ijl}(y,t) + o(ε)`, then `C` vanishes, because they are bounded by
`ε (B_{ij}(y,t) + o(ε))`. -/
theorem third_coefficient_eq_zero {B : Sp n → Fin n → Fin n → ℝ}
    {C : Sp n → Fin n → Fin n → Fin n → ℝ}
    (h3 : ∃ K : ℝ, ∀ ε > 0, ∀ (i j l : Fin n) (w : Sp n), ∃ L : ℝ,
      Tendsto (fun dt : ℝ => (1 / dt) * Mom3 k dt ε w i j l) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
        |L - C w i j l| ≤ K * ε)
    (h2 : CondDiffusion k B)
    (hk0 : ∀ dt z x, 0 ≤ k dt z x)
    (hint : ∀ (dt ε : ℝ) (i j : Fin n) (z : Sp n),
      IntegrableOn (fun x => (x i - z i) * (x j - z j) * k dt z x) (ball z ε))
    (i j l : Fin n) (w : Sp n) : C w i j l = 0 := by
  have h3' : CondThird k C := by
    obtain ⟨K, hK⟩ := h3
    exact ⟨K, by simpa only [Mom3_eq] using hK⟩
  exact h3'.eq_zero h2 hk0 hint i j l w

/-! ### The Taylor expansion of the near region -/

/-- The integrand of (8.7) written with the function `f(y; q)`: it is
`f(y - q; q) - f(y; -q)`. -/
lemma flux_sub_eq (q : Sp n) :
    flux p k t dt y (y - q) = fq p k t dt (y - q) q - fq p k t dt y (-q) := by
  simp [flux, fq, sub_add_cancel, ← sub_eq_add_neg]

/-- The Taylor expansion of `f(y - q; q)` about `y`, in the form used in the text:
`f(y; q) - ∑_i q_i ∂f/∂y_i + (1/2) ∑_{ij} q_i q_j ∂²f/∂y_i∂y_j + o(‖q qᵀ‖)`. -/
lemma taylorPoly_shift (f : Sp n → ℝ) (y q : Sp n) :
    taylorPoly f y (y - q) =
      -(∑ i, q i * pd f i y) + (1 / 2) * ∑ i, ∑ j, q i * q j * pd2 f i j y := by
  simp only [taylorPoly, PiLp.sub_apply]
  have e1 : ∑ i, pd f i y * (y i - q i - y i) = -(∑ i, q i * pd f i y) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, ∑ j, pd2 f i j y * (y i - q i - y i) * (y j - q j - y j)
      = ∑ i, ∑ j, q i * q j * pd2 f i j y :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]

/-- The pointwise decomposition of the integrand of (8.7): the Taylor polynomial, the
remainder, and the pair of terms `f(y; q) - f(y; -q)` which cancels on integration. -/
lemma flux_sub_decomp (q : Sp n) :
    flux p k t dt y (y - q) =
      (-(∑ i, q i * pd (fun w => fq p k t dt w q) i y)
        + (1 / 2) * ∑ i, ∑ j, q i * q j * pd2 (fun w => fq p k t dt w q) i j y)
      + taylorRem (fun w => fq p k t dt w q) y (y - q)
      + (fq p k t dt y q - fq p k t dt y (-q)) := by
  have hd := taylor_decomp (fun w => fq p k t dt w q) y (y - q)
  rw [← taylorPoly_shift]
  rw [flux_sub_eq]
  simp only at hd ⊢
  linarith [hd]

/-- The change of variables `y' = y - q` of (8.7). -/
lemma IQuot_ball_eq_shift :
    IQuot p k t dt y (ball y ε)
      = (1 / dt) * ∫ q in ball (0 : Sp n) ε, flux p k t dt y (y - q) := by
  rw [IQuot, setIntegral_ball_shift y ε (flux p k t dt y)]
  congr 1
  rw [← setIntegral_ball_neg ε fun q => flux p k t dt y (y + q)]
  simp [← sub_eq_add_neg]

/-- The symmetry `∫ f(y; q) dq = ∫ f(y; -q) dq`, which makes the first two terms of
the expansion cancel. -/
lemma integral_fq_sub_reflect (hfq : IntegrableOn (fun q => fq p k t dt y q) (ball (0 : Sp n) ε)) :
    ∫ q in ball (0 : Sp n) ε, (fq p k t dt y q - fq p k t dt y (-q)) = 0 := by
  rw [integral_sub hfq (integrableOn_ball_neg hfq),
    setIntegral_ball_neg ε fun q => fq p k t dt y q, sub_self]

/-- The moment `∫_{‖q‖<ε} dq q_i f(w; q)` factors as `⟨ΔY_i⟩_w p(w, t)`. -/
lemma integral_fq_first (w : Sp n) (i : Fin n) :
    ∫ q in ball (0 : Sp n) ε, q i * fq p k t dt w q = Mom1 k dt ε w i * p t w := by
  simp only [fq, Mom1, ← mul_assoc]
  exact integral_mul_const _ _

/-- The moment `∫_{‖q‖<ε} dq q_i q_j f(w; q)` factors as `⟨ΔY_i ΔY_j⟩_w p(w, t)`. -/
lemma integral_fq_second (w : Sp n) (i j : Fin n) :
    ∫ q in ball (0 : Sp n) ε, q i * q j * fq p k t dt w q = Mom2 k dt ε w i j * p t w := by
  simp only [fq, Mom2, ← mul_assoc]
  exact integral_mul_const _ _

/-- **The expansion of the near region.**  This is the displayed equation for
`I_{‖q‖<ε}` following (8.7): after the substitution `y' = y - q`, the Taylor expansion
of `f(y - q; q)` about `y`, and the cancellation of `∫ f(y;q) dq - ∫ f(y;-q) dq`, the
near contribution consists of a first-order term, a second-order term and the
remainder.  The hypotheses `hswap₁`, `hswap₂` are the interchange of the partial
derivatives with the `q`-integration which the text performs implicitly when it
recognizes the conditional moments `⟨ΔY_i⟩_y` and `⟨ΔY_i ΔY_j⟩_y`. -/
theorem near_expansion
    (hfq : IntegrableOn (fun q => fq p k t dt y q) (ball (0 : Sp n) ε))
    (hT1 : ∀ i, IntegrableOn (fun q => q i * pd (fun w => fq p k t dt w q) i y)
      (ball (0 : Sp n) ε))
    (hT2 : ∀ i j, IntegrableOn (fun q => q i * q j * pd2 (fun w => fq p k t dt w q) i j y)
      (ball (0 : Sp n) ε))
    (hRem : IntegrableOn (fun q => taylorRem (fun w => fq p k t dt w q) y (y - q))
      (ball (0 : Sp n) ε))
    (hswap₁ : ∀ i, ∫ q in ball (0 : Sp n) ε, q i * pd (fun w => fq p k t dt w q) i y
      = pd (fun w => Mom1 k dt ε w i * p t w) i y)
    (hswap₂ : ∀ i j, ∫ q in ball (0 : Sp n) ε, q i * q j * pd2 (fun w => fq p k t dt w q) i j y
      = pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y) :
    IQuot p k t dt y (ball y ε)
      = (1 / dt) * (-(∑ i, pd (fun w => Mom1 k dt ε w i * p t w) i y)
          + (1 / 2) * ∑ i, ∑ j, pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y
          + Rem p k t dt ε y) := by
  classical
  -- integrability of the two Taylor sums
  have hS1 : IntegrableOn
      (fun q => -(∑ i, q i * pd (fun w => fq p k t dt w q) i y)) (ball (0 : Sp n) ε) :=
    (integrable_finset_sum _ fun i _ => hT1 i).neg
  have hS2j : ∀ i, IntegrableOn
      (fun q => ∑ j, q i * q j * pd2 (fun w => fq p k t dt w q) i j y) (ball (0 : Sp n) ε) :=
    fun i => integrable_finset_sum _ fun j _ => hT2 i j
  have hS2 : IntegrableOn
      (fun q => (1 / 2 : ℝ) * ∑ i, ∑ j, q i * q j * pd2 (fun w => fq p k t dt w q) i j y)
      (ball (0 : Sp n) ε) :=
    (integrable_finset_sum _ fun i _ => hS2j i).const_mul _
  have hpair : IntegrableOn
      (fun q => fq p k t dt y q - fq p k t dt y (-q)) (ball (0 : Sp n) ε) :=
    hfq.sub (integrableOn_ball_neg hfq)
  have hA : IntegrableOn
      (fun q => -(∑ i, q i * pd (fun w => fq p k t dt w q) i y)
        + (1 / 2 : ℝ) * ∑ i, ∑ j, q i * q j * pd2 (fun w => fq p k t dt w q) i j y)
      (ball (0 : Sp n) ε) := hS1.add hS2
  have hB : IntegrableOn
      (fun q => (-(∑ i, q i * pd (fun w => fq p k t dt w q) i y)
          + (1 / 2 : ℝ) * ∑ i, ∑ j, q i * q j * pd2 (fun w => fq p k t dt w q) i j y)
        + taylorRem (fun w => fq p k t dt w q) y (y - q))
      (ball (0 : Sp n) ε) := hA.add hRem
  -- the two Taylor integrals
  have e1 : ∫ q in ball (0 : Sp n) ε, -(∑ i, q i * pd (fun w => fq p k t dt w q) i y)
      = -(∑ i, pd (fun w => Mom1 k dt ε w i * p t w) i y) := by
    rw [integral_neg, integral_finset_sum _ fun i _ => hT1 i]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => hswap₁ i)
  have e2 : ∫ q in ball (0 : Sp n) ε,
        (1 / 2 : ℝ) * ∑ i, ∑ j, q i * q j * pd2 (fun w => fq p k t dt w q) i j y
      = (1 / 2 : ℝ) * ∑ i, ∑ j, pd2 (fun w => Mom2 k dt ε w i j * p t w) i j y := by
    rw [integral_const_mul, integral_finset_sum _ fun i _ => hS2j i]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [integral_finset_sum _ fun j _ => hT2 i j]
      exact Finset.sum_congr rfl fun j _ => hswap₂ i j
  rw [IQuot_ball_eq_shift]
  congr 1
  rw [integral_congr_ae (Filter.Eventually.of_forall fun q => flux_sub_decomp q)]
  rw [integral_add hB hpair, integral_add hA hRem, integral_add hS1 hS2,
    integral_fq_sub_reflect hfq, add_zero, e1, e2]
  rfl

end Ullah
