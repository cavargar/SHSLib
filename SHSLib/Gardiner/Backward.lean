/-
The backward differential Chapman–Kolmogorov equation: §3.6 of Gardiner,
"Equations for Time Development in Initial Time — Backward Equations",
equations (3.6.1)–(3.6.4).

Notation.  `G s z` stands for `p(x, t | z, s)`, the transition density with a
fixed *final* condition `(x, t)`, regarded as a function of the initial point `z`
and the initial time `s`.  `k ds y z` stands for `p(z, t' + ds | y, t')`, the
transition density over the short time `ds` starting from the initial point `y`
at the initial time `t'`, and `W z y` is the jump rate `W(z | y, t')` of (3.4.1).

The derivation follows §3.6: the Chapman–Kolmogorov equation turns the difference
quotient (3.6.1) into (3.6.2); the continuity assumption of the text replaces the
inner time `t' + Δt'` by `t'`, giving (3.6.3); and then the argument of §3.4.1 —
Taylor expansion inside the ball `|z - y| < ε`, conditions (ii) and (iii) for the
first two moments, and condition (i) outside the ball — produces (3.6.4).
-/
import SHSLib.Gardiner.WeakForm

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-! ### The quantities of the backward derivation -/

/-- The difference quotient of (3.6.3), tested against a function `g`:
`(1/Δt') ∫ dz p(z, t' + Δt' | y, t') [g(z) - g(y)]`.  For `g = p(x, t | ·, t')`
this is the negative of the quotient appearing in (3.6.3). -/
def bwdQuot (k : ℝ → Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ds : ℝ) : ℝ :=
  (1 / ds) * ∫ z, (g z - g y) * k ds y z

/-- The first and second order Taylor contributions of `bwdQuot` on the ball
`|z - y| < ε`; the analogue of lines 1 and 2 of (3.4.12). -/
def bQ12 (k : ℝ → Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ds ε : ℝ) : ℝ :=
  (1 / ds) * ∫ z in ball y ε, taylorPoly g y z * k ds y z

/-- The Taylor remainder contribution of `bwdQuot` on the ball `|z - y| < ε`;
the analogue of line 3 of (3.4.12). -/
def bQ3 (k : ℝ → Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ds ε : ℝ) : ℝ :=
  (1 / ds) * ∫ z in ball y ε, taylorRem g y z * k ds y z

/-- The contribution of the region `|z - y| ≥ ε`; the analogue of lines 4–6 of
(3.4.12). -/
def bQjump (k : ℝ → Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ds ε : ℝ) : ℝ :=
  (1 / ds) * ∫ z in (ball y ε)ᶜ, (g z - g y) * k ds y z

/-- The second moment over the ball, controlling the remainder as in (3.4.14). -/
def bQsq (k : ℝ → Sp n → Sp n → ℝ) (y : Sp n) (ds ε : ℝ) : ℝ :=
  (1 / ds) * ∫ z in ball y ε, ‖z - y‖ ^ 2 * k ds y z

/-- The drift and diffusion part of the backward generator: the first two terms of
(3.6.4), with the opposite sign. -/
def bwdGen (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (g : Sp n → ℝ)
    (y : Sp n) : ℝ :=
  (∑ i, A y i * pd g i y) + (1 / 2) * ∑ i, ∑ j, B y i j * pd2 g i j y

/-- The jump part of the backward generator, over the region `|z - y| ≥ ε`. -/
def bJumpPre (W : Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ε : ℝ) : ℝ :=
  ∫ z in (ball y ε)ᶜ, (g z - g y) * W z y

/-- The jump term of (3.6.4) itself: `∫ dz W(z | y, t') [g(y) - g(z)]`, over the
region `|z - y| ≥ ε`. -/
def bwdJump (W : Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ε : ℝ) : ℝ :=
  ∫ z in (ball y ε)ᶜ, W z y * (g y - g z)

lemma bJumpPre_eq_neg_bwdJump (W : Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ε : ℝ) :
    bJumpPre W g y ε = -bwdJump W g y ε := by
  rw [bJumpPre, bwdJump, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)

/-! ### From (3.6.1) to (3.6.2) -/

/-- The step (3.6.1) → (3.6.2): by the Chapman–Kolmogorov equation applied to the
second term and the normalisation of the transition density in the first,
`p(x,t|y,t'+Δt') - p(x,t|y,t')` is the integral of
`p(z,t'+Δt'|y,t') [p(x,t|y,t'+Δt') - p(x,t|z,t'+Δt')]`. -/
theorem backward_ck_step (G : ℝ → Sp n → ℝ) (k : ℝ → Sp n → Sp n → ℝ) (y : Sp n) (t' ds : ℝ)
    (hnorm : ∫ z, k ds y z = 1)
    (hck : G t' y = ∫ z, k ds y z * G (t' + ds) z)
    (hkint : Integrable (fun z => k ds y z))
    (hint : Integrable (fun z => k ds y z * G (t' + ds) z)) :
    G (t' + ds) y - G t' y = ∫ z, k ds y z * (G (t' + ds) y - G (t' + ds) z) := by
  have hfun : (fun z => k ds y z * (G (t' + ds) y - G (t' + ds) z))
      = fun z => G (t' + ds) y * k ds y z - k ds y z * G (t' + ds) z := by
    funext z; ring
  rw [hfun, integral_sub (hkint.const_mul _) hint, integral_const_mul, hnorm, mul_one, ← hck]

/-! ### The analogue of (3.4.12): splitting into the two regions -/

/-- The decomposition of the difference quotient into the Taylor contributions on
`|z - y| < ε` and the jump contribution on `|z - y| ≥ ε`. -/
theorem bwdQuot_split (k : ℝ → Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ds ε : ℝ)
    (hInear : IntegrableOn (fun z => taylorPoly g y z * k ds y z) (ball y ε))
    (hIrem : IntegrableOn (fun z => taylorRem g y z * k ds y z) (ball y ε))
    (hIfar : IntegrableOn (fun z => (g z - g y) * k ds y z) (ball y ε)ᶜ) :
    bwdQuot k g y ds = bQ12 k g y ds ε + bQ3 k g y ds ε + bQjump k g y ds ε := by
  have hfun : (fun z => (g z - g y) * k ds y z)
      = fun z => taylorPoly g y z * k ds y z + taylorRem g y z * k ds y z := by
    funext z; rw [taylor_decomp g y z]; ring
  have hInearFull : IntegrableOn (fun z => (g z - g y) * k ds y z) (ball y ε) := by
    rw [hfun]; exact hInear.add hIrem
  have hIfull : Integrable (fun z => (g z - g y) * k ds y z) := by
    have : IntegrableOn (fun z => (g z - g y) * k ds y z) (ball y ε ∪ (ball y ε)ᶜ) := by
      rw [MeasureTheory.integrableOn_union]
      exact ⟨hInearFull, hIfar⟩
    rwa [Set.union_compl_self, MeasureTheory.integrableOn_univ] at this
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_ball (x := y) (ε := ε)) hIfull
  have hnearsplit : ∫ z in ball y ε, (g z - g y) * k ds y z
      = (∫ z in ball y ε, taylorPoly g y z * k ds y z)
        + ∫ z in ball y ε, taylorRem g y z * k ds y z := by
    rw [hfun, MeasureTheory.integral_add hInear hIrem]
  rw [bwdQuot, bQ12, bQ3, bQjump, ← hsplit, hnearsplit]
  ring

/-! ### The analogue of (3.4.14): the remainder is negligible -/

/-- The remainder contribution is bounded by the second moment times the
supremum of the Taylor remainder on the ball. -/
theorem bQ3_le (k : ℝ → Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ds ε δ : ℝ)
    (hds : 0 < ds) (hk0 : ∀ z, 0 ≤ k ds y z)
    (hrem : ∀ z : Sp n, ‖z - y‖ < ε → |taylorRem g y z| ≤ δ * ‖z - y‖ ^ 2)
    (hIrem : IntegrableOn (fun z => taylorRem g y z * k ds y z) (ball y ε))
    (hIsq : IntegrableOn (fun z => ‖z - y‖ ^ 2 * k ds y z) (ball y ε)) :
    |bQ3 k g y ds ε| ≤ δ * bQsq k y ds ε := by
  have hpt : ∀ z ∈ ball y ε, |taylorRem g y z * k ds y z| ≤ δ * ‖z - y‖ ^ 2 * k ds y z := by
    intro z hz
    have hd : ‖z - y‖ < ε := by simpa [dist_eq_norm] using hz
    rw [abs_mul, abs_of_nonneg (hk0 z)]
    exact mul_le_mul_of_nonneg_right (hrem z hd) (hk0 z)
  have hmono : ∫ z in ball y ε, |taylorRem g y z * k ds y z|
      ≤ ∫ z in ball y ε, δ * ‖z - y‖ ^ 2 * k ds y z := by
    refine MeasureTheory.integral_mono_ae hIrem.abs ?_ ?_
    · exact (hIsq.const_mul δ).congr (Filter.Eventually.of_forall fun z => by ring)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz using hpt z hz
  have habs : |∫ z in ball y ε, taylorRem g y z * k ds y z|
      ≤ ∫ z in ball y ε, |taylorRem g y z * k ds y z| := by
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := (volume : Measure (Sp n)).restrict (ball y ε))
        (f := fun z => taylorRem g y z * k ds y z))
  have hconst : ∫ z in ball y ε, δ * ‖z - y‖ ^ 2 * k ds y z
      = δ * ∫ z in ball y ε, ‖z - y‖ ^ 2 * k ds y z := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  rw [bQ3, bQsq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ds)]
  calc (1 / ds) * |∫ z in ball y ε, taylorRem g y z * k ds y z|
      ≤ (1 / ds) * (δ * ∫ z in ball y ε, ‖z - y‖ ^ 2 * k ds y z) := by
        rw [← hconst]
        exact mul_le_mul_of_nonneg_left (habs.trans hmono) (by positivity)
    _ = δ * ((1 / ds) * ∫ z in ball y ε, ‖z - y‖ ^ 2 * k ds y z) := by ring

lemma bQsq_nonneg (k : ℝ → Sp n → Sp n → ℝ) (y : Sp n) (ds ε : ℝ) (hds : 0 < ds)
    (hk0 : ∀ z, 0 ≤ k ds y z) : 0 ≤ bQsq k y ds ε := by
  refine mul_nonneg (by positivity) ?_
  exact MeasureTheory.setIntegral_nonneg measurableSet_ball fun z _ =>
    mul_nonneg (by positivity) (hk0 z)

/-! ### The first two moments: conditions (ii) and (iii) give the drift and diffusion -/

/-- The Taylor contribution `bQ12` is the corresponding combination of the first
and second moments of the transition density over the ball. -/
theorem bQ12_eq (k : ℝ → Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n) (ds ε : ℝ)
    (hint1 : ∀ i : Fin n, IntegrableOn (fun z => (z i - y i) * k ds y z) (ball y ε))
    (hint2 : ∀ i j : Fin n,
      IntegrableOn (fun z => (z i - y i) * (z j - y j) * k ds y z) (ball y ε)) :
    bQ12 k g y ds ε
      = (∑ i, pd g i y * ((1 / ds) * ∫ z in ball y ε, (z i - y i) * k ds y z))
        + (1 / 2) * ∑ i, ∑ j, pd2 g i j y *
            ((1 / ds) * ∫ z in ball y ε, (z i - y i) * (z j - y j) * k ds y z) := by
  have h1 : ∫ z in ball y ε, (∑ i, pd g i y * (z i - y i)) * k ds y z
      = ∑ i, pd g i y * ∫ z in ball y ε, (z i - y i) * k ds y z := by
    have hfun : (fun z => (∑ i, pd g i y * (z i - y i)) * k ds y z)
        = fun z => ∑ i, pd g i y * ((z i - y i) * k ds y z) := by
      funext z; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfun, MeasureTheory.integral_finset_sum _ (fun i _ => (hint1 i).const_mul _)]
    exact Finset.sum_congr rfl fun i _ => by rw [MeasureTheory.integral_const_mul]
  have h2 : ∀ i : Fin n, ∫ z in ball y ε, (∑ j, pd2 g i j y * (z i - y i) * (z j - y j))
        * k ds y z
      = ∑ j, pd2 g i j y * ∫ z in ball y ε, (z i - y i) * (z j - y j) * k ds y z := by
    intro i
    have hfun : (fun z => (∑ j, pd2 g i j y * (z i - y i) * (z j - y j)) * k ds y z)
        = fun z => ∑ j, pd2 g i j y * ((z i - y i) * (z j - y j) * k ds y z) := by
      funext z; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfun, MeasureTheory.integral_finset_sum _ (fun j _ => (hint2 i j).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => by rw [MeasureTheory.integral_const_mul]
  have hsq : ∫ z in ball y ε,
        (∑ i, ∑ j, pd2 g i j y * (z i - y i) * (z j - y j)) * k ds y z
      = ∑ i, ∑ j, pd2 g i j y * ∫ z in ball y ε, (z i - y i) * (z j - y j) * k ds y z := by
    have hfun : (fun z => (∑ i, ∑ j, pd2 g i j y * (z i - y i) * (z j - y j)) * k ds y z)
        = fun z => ∑ i, (∑ j, pd2 g i j y * (z i - y i) * (z j - y j)) * k ds y z := by
      funext z; rw [Finset.sum_mul]
    rw [hfun, MeasureTheory.integral_finset_sum _ (fun i _ => ?_)]
    · exact Finset.sum_congr rfl fun i _ => h2 i
    · have : IntegrableOn
          (fun z => ∑ j, pd2 g i j y * ((z i - y i) * (z j - y j) * k ds y z)) (ball y ε) :=
        MeasureTheory.integrable_finset_sum _ (fun j _ => (hint2 i j).const_mul _)
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hdecomp : (fun z => taylorPoly g y z * k ds y z)
      = fun z => (∑ i, pd g i y * (z i - y i)) * k ds y z
          + (1 / 2) * ((∑ i, ∑ j, pd2 g i j y * (z i - y i) * (z j - y j)) * k ds y z) := by
    funext z; rw [taylorPoly]; ring
  have hI1 : IntegrableOn (fun z => (∑ i, pd g i y * (z i - y i)) * k ds y z) (ball y ε) := by
    have : IntegrableOn (fun z => ∑ i, pd g i y * ((z i - y i) * k ds y z)) (ball y ε) :=
      MeasureTheory.integrable_finset_sum _ (fun i _ => (hint1 i).const_mul _)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hI2 : IntegrableOn
      (fun z => (∑ i, ∑ j, pd2 g i j y * (z i - y i) * (z j - y j)) * k ds y z) (ball y ε) := by
    have : IntegrableOn
        (fun z => ∑ i, ∑ j, pd2 g i j y * ((z i - y i) * (z j - y j) * k ds y z)) (ball y ε) :=
      MeasureTheory.integrable_finset_sum _ fun i _ =>
        MeasureTheory.integrable_finset_sum _ fun j _ => (hint2 i j).const_mul _
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun j _ => by ring
  have hX : (∑ i, pd g i y * ((1 / ds) * ∫ z in ball y ε, (z i - y i) * k ds y z))
      = (1 / ds) * ∑ i, pd g i y * ∫ z in ball y ε, (z i - y i) * k ds y z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hY : (∑ i, ∑ j, pd2 g i j y *
        ((1 / ds) * ∫ z in ball y ε, (z i - y i) * (z j - y j) * k ds y z))
      = (1 / ds) * ∑ i, ∑ j, pd2 g i j y *
          ∫ z in ball y ε, (z i - y i) * (z j - y j) * k ds y z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [bQ12, hdecomp, MeasureTheory.integral_add hI1 (hI2.const_mul _),
    MeasureTheory.integral_const_mul, h1, hsq, hX, hY]
  ring

/-- Conditions (ii) and (iii) of §3.4 give the limit of the Taylor contribution
`bQ12`: it converges, for each `ε`, to the drift/diffusion part `bwdGen` of the
backward generator up to an error `O(ε)`. -/
theorem bQ12_tendsto {k : ℝ → Sp n → Sp n → ℝ} {A : Sp n → Fin n → ℝ}
    {B : Sp n → Fin n → Fin n → ℝ} (hA : CondDrift k A) (hB : CondDiffusion k B)
    (g : Sp n → ℝ) (y : Sp n)
    (hint1 : ∀ (ds ε : ℝ) (i : Fin n), IntegrableOn (fun z => (z i - y i) * k ds y z) (ball y ε))
    (hint2 : ∀ (ds ε : ℝ) (i j : Fin n),
      IntegrableOn (fun z => (z i - y i) * (z j - y j) * k ds y z) (ball y ε)) :
    ∃ K : ℝ, ∀ ε > 0, ∃ L : ℝ,
      Tendsto (fun ds => bQ12 k g y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
        |L - bwdGen A B g y| ≤ K * ε := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  refine ⟨(∑ i, |pd g i y|) * max CA 0
      + (1 / 2) * ((∑ i, ∑ j, |pd2 g i j y|) * max CB 0), ?_⟩
  intro ε hε
  choose L1 hL1 hL1A using fun i => hCA ε hε i y
  choose L2 hL2 hL2B using fun (i j : Fin n) => hCB ε hε i j y
  refine ⟨(∑ i, pd g i y * L1 i) + (1 / 2) * ∑ i, ∑ j, pd2 g i j y * L2 i j, ?_, ?_⟩
  · have heq : (fun ds => bQ12 k g y ds ε)
        = fun ds => (∑ i, pd g i y * ((1 / ds) * ∫ z in ball y ε, (z i - y i) * k ds y z))
          + (1 / 2) * ∑ i, ∑ j, pd2 g i j y *
              ((1 / ds) * ∫ z in ball y ε, (z i - y i) * (z j - y j) * k ds y z) := by
      funext ds
      exact bQ12_eq k g y ds ε (fun i => hint1 ds ε i) (fun i j => hint2 ds ε i j)
    rw [heq]
    refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
    · exact tendsto_finset_sum _ fun i _ => (hL1 i).const_mul _
    · exact tendsto_finset_sum _ fun i _ =>
        tendsto_finset_sum _ fun j _ => (hL2 i j).const_mul _
  · have hCA' : ∀ i, |L1 i - A y i| ≤ max CA 0 * ε := fun i =>
      (hL1A i).trans (by nlinarith [le_max_left CA (0:ℝ), hε.le])
    have hCB' : ∀ i j, |L2 i j - B y i j| ≤ max CB 0 * ε := fun i j =>
      (hL2B i j).trans (by nlinarith [le_max_left CB (0:ℝ), hε.le])
    have hd1 : |(∑ i, pd g i y * L1 i) - ∑ i, A y i * pd g i y|
        ≤ (∑ i, |pd g i y|) * (max CA 0 * ε) := by
      have : (∑ i, pd g i y * L1 i) - ∑ i, A y i * pd g i y
          = ∑ i, pd g i y * (L1 i - A y i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      calc |∑ i, pd g i y * (L1 i - A y i)| ≤ ∑ i, |pd g i y * (L1 i - A y i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |pd g i y| * (max CA 0 * ε) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hCA' i) (abs_nonneg _)
        _ = (∑ i, |pd g i y|) * (max CA 0 * ε) := by rw [Finset.sum_mul]
    have hd2 : |(∑ i, ∑ j, pd2 g i j y * L2 i j) - ∑ i, ∑ j, B y i j * pd2 g i j y|
        ≤ (∑ i, ∑ j, |pd2 g i j y|) * (max CB 0 * ε) := by
      have : (∑ i, ∑ j, pd2 g i j y * L2 i j) - ∑ i, ∑ j, B y i j * pd2 g i j y
          = ∑ i, ∑ j, pd2 g i j y * (L2 i j - B y i j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      calc |∑ i, ∑ j, pd2 g i j y * (L2 i j - B y i j)|
          ≤ ∑ i, |∑ j, pd2 g i j y * (L2 i j - B y i j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, |pd2 g i j y| * (max CB 0 * ε) := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hCB' i j) (abs_nonneg _)
        _ = (∑ i, ∑ j, |pd2 g i j y|) * (max CB 0 * ε) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    have hsplit : ((∑ i, pd g i y * L1 i) + (1 / 2) * ∑ i, ∑ j, pd2 g i j y * L2 i j)
        - bwdGen A B g y
        = ((∑ i, pd g i y * L1 i) - ∑ i, A y i * pd g i y)
          + (1 / 2) * ((∑ i, ∑ j, pd2 g i j y * L2 i j) - ∑ i, ∑ j, B y i j * pd2 g i j y) := by
      rw [bwdGen]; ring
    rw [hsplit]
    calc |((∑ i, pd g i y * L1 i) - ∑ i, A y i * pd g i y)
            + (1 / 2) * ((∑ i, ∑ j, pd2 g i j y * L2 i j) - ∑ i, ∑ j, B y i j * pd2 g i j y)|
        ≤ |(∑ i, pd g i y * L1 i) - ∑ i, A y i * pd g i y|
            + |(1 / 2) * ((∑ i, ∑ j, pd2 g i j y * L2 i j)
              - ∑ i, ∑ j, B y i j * pd2 g i j y)| := abs_add_le _ _
      _ ≤ (∑ i, |pd g i y|) * (max CA 0 * ε)
            + (1 / 2) * ((∑ i, ∑ j, |pd2 g i j y|) * (max CB 0 * ε)) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
          exact add_le_add hd1 (mul_le_mul_of_nonneg_left hd2 (by norm_num))
      _ = ((∑ i, |pd g i y|) * max CA 0
            + (1 / 2) * ((∑ i, ∑ j, |pd2 g i j y|) * max CB 0)) * ε := by ring


/-! ### The backward generator: the analogue of (3.4.16) -/

/-- **The generator form of the backward equation.**  The limit `L` of the
difference quotient (3.6.3), tested against a compactly supported `C²` function `g`,
is the sum of the drift/diffusion part `bwdGen` and the principal value `J` of the
jump integral.

As in §3.4.1, the steps that the text justifies informally appear as hypotheses:
`hsplit` is the splitting into the two regions, `hQ3le` the estimate of the Taylor
remainder, `h12` and `he` the limit of the first two Taylor terms up to `O(ε)`,
`hsq` and `hM` the boundedness of the second moment, `hjump` the limit of the
contribution of `|z - y| ≥ ε` given by condition (i), and `hPV` the existence of the
principal value integral. -/
theorem backward_generator (k : ℝ → Sp n → Sp n → ℝ) (A : Sp n → Fin n → ℝ)
    (B : Sp n → Fin n → Fin n → ℝ) (W : Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n)
    (L J : ℝ) (e M : ℝ → ℝ) (C : ℝ)
    (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g)
    (hsplit : ∀ ds > 0, ∀ ε > 0,
      bwdQuot k g y ds = bQ12 k g y ds ε + bQ3 k g y ds ε + bQjump k g y ds ε)
    (hQ3le : ∀ ds > 0, ∀ ε > 0, ∀ δ ≥ (0 : ℝ),
      (∀ z : Sp n, ‖z - y‖ < ε → |taylorRem g y z| ≤ δ * ‖z - y‖ ^ 2) →
      |bQ3 k g y ds ε| ≤ δ * bQsq k y ds ε)
    (hD : Tendsto (bwdQuot k g y) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (h12 : ∀ ε > 0, Tendsto (fun ds => bQ12 k g y ds ε) (𝓝[>] (0 : ℝ))
      (𝓝 (bwdGen A B g y + e ε)))
    (he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hsq : ∀ ε > 0, Tendsto (fun ds => bQsq k y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 (M ε)))
    (hM : ∀ ε > 0, |M ε| ≤ C)
    (hjump : ∀ ε > 0, Tendsto (fun ds => bQjump k g y ds ε) (𝓝[>] (0 : ℝ))
      (𝓝 (bJumpPre W g y ε)))
    (hPV : Tendsto (fun ε => bJumpPre W g y ε) (𝓝[>] (0 : ℝ)) (𝓝 J)) :
    L = bwdGen A B g y + J := by
  set IAB := bwdGen A B g y with hIAB
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hM 1 one_pos)
  set q3 : ℝ → ℝ := fun ε => L - (IAB + e ε) - bJumpPre W g y ε with hq3def
  have hQ3lim : ∀ ε > 0, Tendsto (fun ds => bQ3 k g y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 (q3 ε)) := by
    intro ε hε
    have hEq : (fun ds => bwdQuot k g y ds - bQ12 k g y ds ε - bQjump k g y ds ε)
        =ᶠ[𝓝[>] (0 : ℝ)] fun ds => bQ3 k g y ds ε := by
      filter_upwards [self_mem_nhdsWithin] with ds hds
      have := hsplit ds hds ε hε
      linarith
    exact Tendsto.congr' hEq ((hD.sub (h12 ε hε)).sub (hjump ε hε))
  have hbound : ∀ δ > (0 : ℝ), ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → |q3 ε| ≤ δ * C := by
    intro δ hδ
    obtain ⟨ε₀, hε₀, hrem⟩ := uniform_taylorRem g hg hgs hδ
    refine ⟨ε₀, hε₀, fun ε hε hle => ?_⟩
    have hb : ∀ ds ∈ Set.Ioi (0 : ℝ), |bQ3 k g y ds ε| ≤ δ * bQsq k y ds ε := by
      intro ds hds
      exact hQ3le ds hds ε hε δ hδ.le fun z hz => hrem y z (lt_of_lt_of_le hz hle)
    have h1 : Tendsto (fun ds => |bQ3 k g y ds ε|) (𝓝[>] (0 : ℝ)) (𝓝 |q3 ε|) :=
      (hQ3lim ε hε).abs
    have h2 : Tendsto (fun ds => δ * bQsq k y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 (δ * M ε)) :=
      (hsq ε hε).const_mul δ
    have hle' : |q3 ε| ≤ δ * M ε := by
      refine le_of_tendsto_of_tendsto h1 h2 ?_
      filter_upwards [self_mem_nhdsWithin] with ds hds using hb ds hds
    have hMC : M ε ≤ C := le_trans (le_abs_self _) (hM ε hε)
    exact hle'.trans (by nlinarith)
  have hq3 : Tendsto q3 (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro η hη
    obtain ⟨ε₀, hε₀, hb⟩ := hbound (η / (2 * (C + 1))) (by positivity)
    filter_upwards [Ioc_mem_nhdsGT hε₀] with ε hε
    have := hb ε hε.1 hε.2
    have hlt : η / (2 * (C + 1)) * C < η := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    simpa [Real.norm_eq_abs] using lt_of_le_of_lt this hlt
  have hsum : Tendsto (fun ε : ℝ => IAB + e ε + q3 ε + bJumpPre W g y ε) (𝓝[>] (0 : ℝ))
      (𝓝 (IAB + 0 + 0 + J)) :=
    ((tendsto_const_nhds.add he).add hq3).add hPV
  have hconst : (fun ε : ℝ => IAB + e ε + q3 ε + bJumpPre W g y ε) = fun _ => L := by
    funext ε; simp only [hq3def]; ring
  rw [hconst] at hsum
  have := tendsto_nhds_unique tendsto_const_nhds hsum
  simpa using this

/-! ### The derivation, assembled -/

lemma integrableOn_ball_mul_of_bounded {f h : Sp n → ℝ} {y : Sp n} {ε C : ℝ}
    (hf : Integrable f) (hh : Continuous h) (hb : ∀ z ∈ ball y ε, |h z| ≤ C) :
    IntegrableOn (fun z => h z * f z) (ball y ε) := by
  refine Integrable.bdd_mul (c := C) hf.restrict hh.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem (measurableSet_ball (x := y) (ε := ε))] with z hz using hb z hz

lemma integrableOn_compl_ball_mul_of_bounded {f h : Sp n → ℝ} {y : Sp n} {ε C : ℝ}
    (hf : Integrable f) (hh : Continuous h) (hb : ∀ z, |h z| ≤ C) :
    IntegrableOn (fun z => h z * f z) (ball y ε)ᶜ := by
  refine Integrable.bdd_mul (c := C) hf.restrict hh.aestronglyMeasurable.restrict ?_
  filter_upwards with z using hb z

/-- **The generator form of the backward equation**, assembled from the conditions
(ii) and (iii) of §3.4 and the limits taken in the text.  Compared with
`backward_generator`, the splitting into the two regions, the estimate of the Taylor
remainder and the limit of the first two Taylor terms are now *proved*, from the
non-negativity and integrability of the transition density and from conditions (ii)
and (iii). -/
theorem backward_generator_of_kernel {k : ℝ → Sp n → Sp n → ℝ} {A : Sp n → Fin n → ℝ}
    {B : Sp n → Fin n → Fin n → ℝ} (W : Sp n → Sp n → ℝ) (g : Sp n → ℝ) (y : Sp n)
    (L J : ℝ) (M : ℝ → ℝ) (C : ℝ)
    (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g)
    (hk0 : ∀ ds z, 0 ≤ k ds y z) (hkint : ∀ ds, Integrable (fun z => k ds y z))
    (hA : CondDrift k A) (hB : CondDiffusion k B)
    (hD : Tendsto (bwdQuot k g y) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hsq : ∀ ε > 0, Tendsto (fun ds => bQsq k y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 (M ε)))
    (hM : ∀ ε > 0, |M ε| ≤ C)
    (hjump : ∀ ε > 0, Tendsto (fun ds => bQjump k g y ds ε) (𝓝[>] (0 : ℝ))
      (𝓝 (bJumpPre W g y ε)))
    (hPV : Tendsto (fun ε => bJumpPre W g y ε) (𝓝[>] (0 : ℝ)) (𝓝 J)) :
    L = bwdGen A B g y + J := by
  classical
  obtain ⟨Cg, hCg0, hCg⟩ := exists_bound_of_contDiff_hasCompactSupport hg.continuous hgs
  have hcontPoly : Continuous fun z : Sp n => taylorPoly g y z :=
    (continuous_taylorPoly g hg).comp (continuous_id.prodMk continuous_const)
  have hcontRem : Continuous fun z : Sp n => taylorRem g y z :=
    (continuous_taylorRem g hg).comp (continuous_id.prodMk continuous_const)
  have hcoord : ∀ i : Fin n, Continuous fun z : Sp n => z i - y i := fun i =>
    (PiLp.continuous_apply 2 (fun _ => ℝ) i).sub continuous_const
  have hballmem : ∀ (ε : ℝ) (z : Sp n), z ∈ ball y ε → ‖z - y‖ < ε := by
    intro ε z hz; simpa [dist_eq_norm] using hz
  -- integrability of the integrands over the ball and its complement
  have hI1 : ∀ (ds ε : ℝ) (i : Fin n),
      IntegrableOn (fun z => (z i - y i) * k ds y z) (ball y ε) := by
    intro ds ε i
    refine integrableOn_ball_mul_of_bounded (hkint ds) (hcoord i) (C := max ε 0) ?_
    intro z hz
    have h1 : |z i - y i| ≤ ‖z - y‖ := by
      simpa [PiLp.sub_apply] using PiLp.norm_apply_le (z - y) i
    exact h1.trans ((hballmem ε z hz).le.trans (le_max_left _ _))
  have hI2 : ∀ (ds ε : ℝ) (i j : Fin n),
      IntegrableOn (fun z => (z i - y i) * (z j - y j) * k ds y z) (ball y ε) := by
    intro ds ε i j
    refine integrableOn_ball_mul_of_bounded (hkint ds) ((hcoord i).mul (hcoord j))
      (C := max ε 0 ^ 2) ?_
    intro z hz
    have hi : |z i - y i| ≤ ‖z - y‖ := by
      simpa [PiLp.sub_apply] using PiLp.norm_apply_le (z - y) i
    have hj : |z j - y j| ≤ ‖z - y‖ := by
      simpa [PiLp.sub_apply] using PiLp.norm_apply_le (z - y) j
    have hb : ‖z - y‖ ≤ max ε 0 := (hballmem ε z hz).le.trans (le_max_left _ _)
    have h0 : (0 : ℝ) ≤ max ε 0 := le_max_right _ _
    rw [abs_mul]
    nlinarith [abs_nonneg (z i - y i), abs_nonneg (z j - y j), norm_nonneg (z - y)]
  have hIsq : ∀ (ds ε : ℝ), IntegrableOn (fun z => ‖z - y‖ ^ 2 * k ds y z) (ball y ε) := by
    intro ds ε
    refine integrableOn_ball_mul_of_bounded (hkint ds)
      ((continuous_id.sub continuous_const).norm.pow 2) (C := max ε 0 ^ 2) ?_
    intro z hz
    have hb : ‖z - y‖ ≤ max ε 0 := (hballmem ε z hz).le.trans (le_max_left _ _)
    have h0 : (0 : ℝ) ≤ max ε 0 := le_max_right _ _
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hIpoly : ∀ (ds ε : ℝ), 0 < ε →
      IntegrableOn (fun z => taylorPoly g y z * k ds y z) (ball y ε) := by
    intro ds ε hε
    obtain ⟨Cp, _, hCp⟩ := taylorPoly_bounded g hg hgs ε hε
    refine integrableOn_ball_mul_of_bounded (hkint ds) hcontPoly (C := Cp) ?_
    intro z hz
    exact hCp (z, y) (by simpa [nearDiag] using hz)
  have hIrem : ∀ (ds ε : ℝ), 0 < ε →
      IntegrableOn (fun z => taylorRem g y z * k ds y z) (ball y ε) := by
    intro ds ε hε
    obtain ⟨Cr, _, hCr⟩ := taylorRem_bounded g hg hgs ε hε
    refine integrableOn_ball_mul_of_bounded (hkint ds) hcontRem (C := Cr) ?_
    intro z hz
    exact hCr (z, y) (by simpa [nearDiag] using hz)
  have hIfar : ∀ (ds ε : ℝ), IntegrableOn (fun z => (g z - g y) * k ds y z) (ball y ε)ᶜ := by
    intro ds ε
    refine integrableOn_compl_ball_mul_of_bounded (hkint ds)
      (hg.continuous.sub continuous_const) (C := 2 * Cg) ?_
    intro z
    exact (abs_sub _ _).trans (by linarith [hCg z, hCg y])
  -- the splitting and the remainder estimate
  have hsplit : ∀ ds > 0, ∀ ε > 0,
      bwdQuot k g y ds = bQ12 k g y ds ε + bQ3 k g y ds ε + bQjump k g y ds ε := by
    intro ds _ ε hε
    exact bwdQuot_split k g y ds ε (hIpoly ds ε hε) (hIrem ds ε hε) (hIfar ds ε)
  have hQ3le : ∀ ds > 0, ∀ ε > 0, ∀ δ ≥ (0 : ℝ),
      (∀ z : Sp n, ‖z - y‖ < ε → |taylorRem g y z| ≤ δ * ‖z - y‖ ^ 2) →
      |bQ3 k g y ds ε| ≤ δ * bQsq k y ds ε := by
    intro ds hds ε hε δ _ hrem
    exact bQ3_le k g y ds ε δ hds (hk0 ds) hrem (hIrem ds ε hε) (hIsq ds ε)
  -- conditions (ii) and (iii) give the limit of the first two Taylor terms
  obtain ⟨K, hK⟩ := bQ12_tendsto hA hB g y hI1 hI2
  have hKex : ∀ ε : ℝ, ∃ Lf : ℝ, 0 < ε →
      (Tendsto (fun ds => bQ12 k g y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 Lf) ∧
        |Lf - bwdGen A B g y| ≤ K * ε) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨Lf, hLf⟩ := hK ε hε
      exact ⟨Lf, fun _ => hLf⟩
    · exact ⟨0, fun h => absurd h hε⟩
  choose Lf hLf using hKex
  set e : ℝ → ℝ := fun ε => Lf ε - bwdGen A B g y with hedef
  have h12 : ∀ ε > 0, Tendsto (fun ds => bQ12 k g y ds ε) (𝓝[>] (0 : ℝ))
      (𝓝 (bwdGen A B g y + e ε)) := by
    intro ε hε
    have : bwdGen A B g y + e ε = Lf ε := by simp [hedef]
    rw [this]
    exact (hLf ε hε).1
  have he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hKlim : Tendsto (fun ε : ℝ => K * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => K * ε) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hKlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [Real.norm_eq_abs, hedef] using (hLf ε hε).2
  exact backward_generator k A B W g y L J e M C hg hgs hsplit hQ3le hD h12 he hsq hM hjump hPV

/-! ### (3.6.4): the backward differential Chapman–Kolmogorov equation -/

/-- **The backward differential Chapman–Kolmogorov equation**, (3.6.4).

`G s z` is `p(x, t | z, s)` and `k ds y z` is `p(z, t' + ds | y, t')`.  The
conclusion is the derivative in the initial time `t'` of `p(x, t | y, t')`:
```
∂p/∂t' = - ∑ᵢ Aᵢ(y,t') ∂p/∂yᵢ - ½ ∑ᵢⱼ Bᵢⱼ(y,t') ∂²p/∂yᵢ∂yⱼ
           + ∫ dz W(z|y,t') [p(x,t|y,t') - p(x,t|z,t')].
```
The hypotheses `hnorm`, `hck`, `hGint` give the passage (3.6.1) → (3.6.2), `h363` is
the continuity step (3.6.2) → (3.6.3) of the text (the two difference quotients have
the same limit), and the remaining hypotheses are those of
`backward_generator_of_kernel`. -/
theorem backwardDifferentialCK {k : ℝ → Sp n → Sp n → ℝ} {A : Sp n → Fin n → ℝ}
    {B : Sp n → Fin n → Fin n → ℝ} (G : ℝ → Sp n → ℝ) (W : Sp n → Sp n → ℝ) (y : Sp n)
    (t' L Jb : ℝ) (M : ℝ → ℝ) (C : ℝ)
    (hg : ContDiff ℝ 2 (G t')) (hgs : HasCompactSupport (G t'))
    (hk0 : ∀ ds z, 0 ≤ k ds y z) (hkint : ∀ ds, Integrable (fun z => k ds y z))
    (hA : CondDrift k A) (hB : CondDiffusion k B)
    (hD : Tendsto (bwdQuot k (G t') y) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hsq : ∀ ε > 0, Tendsto (fun ds => bQsq k y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 (M ε)))
    (hM : ∀ ε > 0, |M ε| ≤ C)
    (hjump : ∀ ε > 0, Tendsto (fun ds => bQjump k (G t') y ds ε) (𝓝[>] (0 : ℝ))
      (𝓝 (bJumpPre W (G t') y ε)))
    (hPV : Tendsto (fun ε => bwdJump W (G t') y ε) (𝓝[>] (0 : ℝ)) (𝓝 Jb))
    (hnorm : ∀ ds > 0, ∫ z, k ds y z = 1)
    (hck : ∀ ds > 0, G t' y = ∫ z, k ds y z * G (t' + ds) z)
    (hGint : ∀ ds > 0, Integrable (fun z => k ds y z * G (t' + ds) z))
    (h363 : Tendsto (fun ds => (1 / ds) * (∫ z, k ds y z * (G (t' + ds) y - G (t' + ds) z))
        - (1 / ds) * ∫ z, k ds y z * (G t' y - G t' z)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ds => (G (t' + ds) y - G t' y) / ds) (𝓝[>] (0 : ℝ))
      (𝓝 (-(∑ i, A y i * pd (G t') i y)
          - (1 / 2) * ∑ i, ∑ j, B y i j * pd2 (G t') i j y + Jb)) := by
  -- the principal value of the jump integral, in the two sign conventions
  have hPV' : Tendsto (fun ε => bJumpPre W (G t') y ε) (𝓝[>] (0 : ℝ)) (𝓝 (-Jb)) := by
    have : (fun ε => bJumpPre W (G t') y ε) = fun ε => -bwdJump W (G t') y ε := by
      funext ε; exact bJumpPre_eq_neg_bwdJump W (G t') y ε
    rw [this]
    exact hPV.neg
  -- the generator form of the equation
  have hL : L = bwdGen A B (G t') y + -Jb :=
    backward_generator_of_kernel W (G t') y L (-Jb) M C hg hgs hk0 hkint hA hB hD hsq hM
      hjump hPV'
  -- (3.6.1) = (3.6.2) = (3.6.3), by the Chapman–Kolmogorov equation and continuity
  have hquot : ∀ ds > (0 : ℝ), (G (t' + ds) y - G t' y) / ds
      = ((1 / ds) * (∫ z, k ds y z * (G (t' + ds) y - G (t' + ds) z))
          - (1 / ds) * ∫ z, k ds y z * (G t' y - G t' z))
        + -bwdQuot k (G t') y ds := by
    intro ds hds
    have hstep := backward_ck_step G k y t' ds (hnorm ds hds) (hck ds hds) (hkint ds)
      (hGint ds hds)
    have hneg : bwdQuot k (G t') y ds = -((1 / ds) * ∫ z, k ds y z * (G t' y - G t' z)) := by
      rw [bwdQuot, ← mul_neg, ← integral_neg]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [hneg, hstep, div_eq_inv_mul, one_div]
    ring
  have hlim : Tendsto (fun ds => ((1 / ds) *
        (∫ z, k ds y z * (G (t' + ds) y - G (t' + ds) z))
        - (1 / ds) * ∫ z, k ds y z * (G t' y - G t' z)) + -bwdQuot k (G t') y ds)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 + -L)) := h363.add hD.neg
  have hcongr : (fun ds => (G (t' + ds) y - G t' y) / ds) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ds => ((1 / ds) * (∫ z, k ds y z * (G (t' + ds) y - G (t' + ds) z))
          - (1 / ds) * ∫ z, k ds y z * (G t' y - G t' z)) + -bwdQuot k (G t') y ds := by
    filter_upwards [self_mem_nhdsWithin] with ds hds using hquot ds hds
  have hfin := hlim.congr' hcongr.symm
  have hval : (0 : ℝ) + -L = -(∑ i, A y i * pd (G t') i y)
      - (1 / 2) * ∑ i, ∑ j, B y i j * pd2 (G t') i j y + Jb := by
    rw [hL, bwdGen]; ring
  rwa [hval] at hfin

end Gardiner
