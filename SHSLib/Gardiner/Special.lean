/-
Interpretation of the conditions and results: §3.5 of Gardiner,
*Handbook of Stochastic Methods*.

The three special cases of the differential Chapman–Kolmogorov equation (3.4.22):

* §3.5.1, the **Master equation** (3.5.2), obtained when `A = B = 0`;
* §3.5.2, the **Fokker–Planck equation** (3.5.6), obtained when `W = 0`;
* §3.5.3, **Liouville's equation** (3.5.13), obtained when `B = W = 0`;

together with

* the symmetry and positive semidefiniteness of the diffusion matrix `B`,
  which the text deduces from its definition (3.4.3);
* the deterministic solution (3.5.17) of Liouville's equation, in the weak
  (distributional) form of the argument (3.5.18)–(3.5.21);
* the Gaussian short-time solution (3.5.9) of the frozen-coefficient
  Fokker–Planck equation (3.5.8), in one dimension.
-/
import SHSLib.Gardiner.Strong

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-! ### Partial derivatives of the zero function -/

lemma pd_of_eq_zero (f : Sp n → ℝ) (hf : ∀ z, f z = 0) (i : Fin n) (z : Sp n) :
    pd f i z = 0 := by
  have : f = fun _ => (0 : ℝ) := funext hf
  subst this
  simp [pd]

lemma pd2_of_eq_zero (f : Sp n → ℝ) (hf : ∀ z, f z = 0) (i j : Fin n) (z : Sp n) :
    pd2 f i j z = 0 := by
  have h : ∀ z, pd f j z = 0 := fun z => pd_of_eq_zero f hf j z
  exact pd_of_eq_zero _ h i z

@[simp] lemma pd_const_zero (i : Fin n) (z : Sp n) : pd (fun _ : Sp n => (0 : ℝ)) i z = 0 :=
  pd_of_eq_zero _ (fun _ => rfl) i z

@[simp] lemma pd2_const_zero (i j : Fin n) (z : Sp n) :
    pd2 (fun _ : Sp n => (0 : ℝ)) i j z = 0 :=
  pd2_of_eq_zero _ (fun _ => rfl) i j z

/-! ### 3.5.1 Jump processes: the Master equation -/

/-- **The Master equation** (3.5.2).  It is the differential Chapman–Kolmogorov
equation in the case (3.5.1) `A = B = 0`, i.e. the case of a pure jump process. -/
theorem masterEquation
    (p : ℝ → Sp n → ℝ) (W : Sp n → Sp n → ℝ) (t : ℝ) (dtp : Sp n → ℝ)
    (hjump : LocallyIntegrable (fun z => ∫ x, (W z x * p t x - W x z * p t z)))
    (hdtp : LocallyIntegrable dtp)
    (hweak : ∀ f : Sp n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∫ z, f z * dtp z = ∫ z, f z * (∫ x, (W z x * p t x - W x z * p t z))) :
    ∀ᵐ z : Sp n, dtp z = ∫ x, (W z x * p t x - W x z * p t z) := by
  have hA : ∀ i : Fin n, ContDiff ℝ 1 (fun w : Sp n => (0 : ℝ) * p t w) := by
    intro i; simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : Sp n => (0 : ℝ)))
  have hB : ∀ i j : Fin n, ContDiff ℝ 2 (fun w : Sp n => (0 : ℝ) * p t w) := by
    intro i j; simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : Sp n => (0 : ℝ)))
  have hdd : ∀ f : Sp n → ℝ,
      driftDiffTerm p (fun _ _ => 0) (fun _ _ _ => 0) f t = 0 := by
    intro f; simp [driftDiffTerm]
  have key := differentialCK p (fun _ _ => 0) (fun _ _ _ => 0) W t dtp hA hB hjump hdtp
    (by intro f hf hfs; rw [hdd f, zero_add]; exact hweak f hf hfs)
  refine key.mono fun z hz => ?_
  rw [hz, ckRHS]
  simp

/-! ### 3.5.2 Diffusion processes: the Fokker–Planck equation -/

/-- The right-hand side of the Fokker–Planck equation (3.5.6). -/
def fpRHS (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (t : ℝ) (z : Sp n) : ℝ :=
  -(∑ i, pd (fun w => A w i * p t w) i z)
    + (1 / 2) * (∑ i, ∑ j, pd2 (fun w => B w i j * p t w) i j z)

/-- **The Fokker–Planck equation** (3.5.6).  It is the differential
Chapman–Kolmogorov equation in the case `W = 0`, i.e. the case of a diffusion
process. -/
theorem fokkerPlanck
    (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (t : ℝ) (dtp : Sp n → ℝ)
    (hAp : ∀ i, ContDiff ℝ 1 (fun w => A w i * p t w))
    (hBp : ∀ i j, ContDiff ℝ 2 (fun w => B w i j * p t w))
    (hdtp : LocallyIntegrable dtp)
    (hweak : ∀ f : Sp n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∫ z, f z * dtp z = driftDiffTerm p A B f t) :
    ∀ᵐ z : Sp n, dtp z = fpRHS p A B t z := by
  have hjump : LocallyIntegrable
      (fun z : Sp n => ∫ x, ((0 : ℝ) * p t x - (0 : ℝ) * p t z)) := by
    simpa using (locallyIntegrable_const (0 : ℝ) : LocallyIntegrable (fun _ : Sp n => (0 : ℝ)))
  have key := differentialCK p A B (fun _ _ => 0) t dtp hAp hBp hjump hdtp
    (by intro f hf hfs; rw [hweak f hf hfs]; simp)
  refine key.mono fun z hz => ?_
  rw [hz, ckRHS, fpRHS]
  simp

/-! ### 3.5.3 Deterministic processes: Liouville's equation -/

/-- The right-hand side of Liouville's equation (3.5.13). -/
def liouvilleRHS (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (t : ℝ) (z : Sp n) : ℝ :=
  -(∑ i, pd (fun w => A w i * p t w) i z)

/-- **Liouville's equation** (3.5.13).  It is the differential Chapman–Kolmogorov
equation in the case `B = W = 0`, i.e. the case of a deterministic motion. -/
theorem liouville
    (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (t : ℝ) (dtp : Sp n → ℝ)
    (hAp : ∀ i, ContDiff ℝ 1 (fun w => A w i * p t w))
    (hdtp : LocallyIntegrable dtp)
    (hweak : ∀ f : Sp n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∫ z, f z * dtp z = ∫ z, (∑ i, A z i * pd f i z) * p t z) :
    ∀ᵐ z : Sp n, dtp z = liouvilleRHS p A t z := by
  have hB : ∀ i j : Fin n, ContDiff ℝ 2 (fun w : Sp n => (0 : ℝ) * p t w) := by
    intro i j; simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : Sp n => (0 : ℝ)))
  have hdd : ∀ f : Sp n → ℝ,
      driftDiffTerm p A (fun _ _ _ => 0) f t = ∫ z, (∑ i, A z i * pd f i z) * p t z := by
    intro f; simp [driftDiffTerm]
  have key := fokkerPlanck p A (fun _ _ _ => 0) t dtp hAp hB hdtp
    (by intro f hf hfs; rw [hdd f]; exact hweak f hf hfs)
  refine key.mono fun z hz => ?_
  rw [hz, fpRHS, liouvilleRHS]
  simp

/-- The weak form of the deterministic solution (3.5.17) of Liouville's equation:
if `x` solves the ordinary differential equation (3.5.14) `dx/dt = A(x(t), t)`,
then the point mass `δ(z - x(t))` solves Liouville's equation in the sense of
distributions, i.e. for every test function `f`,
`d/dt ⟨δ(· - x(t)), f⟩ = ⟨δ(· - x(t)), ∑ᵢ Aᵢ ∂ᵢ f⟩`.

This is the content of the computation (3.5.18)–(3.5.21). -/
theorem liouville_deterministic_weak
    (A : ℝ → Sp n → Fin n → ℝ) (x : ℝ → Sp n) (v : Sp n) (t : ℝ)
    (hx : HasDerivAt x v t) (hv : ∀ i, v i = A t (x t) i)
    (f : Sp n → ℝ) (hf : ContDiff ℝ 1 f) :
    HasDerivAt (fun s => f (x s)) (∑ i, A t (x t) i * pd f i (x t)) t := by
  have hfd : HasFDerivAt f (fderiv ℝ f (x t)) (x t) :=
    (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hcomp : HasDerivAt (fun s => f (x s)) (fderiv ℝ f (x t) v) t := hfd.comp_hasDerivAt t hx
  have hval : fderiv ℝ f (x t) v = ∑ i, A t (x t) i * pd f i (x t) := by
    rw [fderiv_apply_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hv i]; ring
  rwa [hval] at hcomp

/-! ### 3.5.2 The diffusion matrix is symmetric and positive semidefinite -/

/-- The diffusion matrix defined by condition (iii), (3.4.3), is symmetric. -/
theorem CondDiffusion.symm_of_cond {k : ℝ → Sp n → Sp n → ℝ} {B : Sp n → Fin n → Fin n → ℝ}
    (h : CondDiffusion k B) (i j : Fin n) (z : Sp n) : B z i j = B z j i := by
  obtain ⟨C, hC⟩ := h
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hle : ∀ ε > (0 : ℝ), |B z i j - B z j i| ≤ 2 * C' * ε := by
    intro ε hε
    obtain ⟨L, hL, hLB⟩ := hC ε hε i j z
    obtain ⟨L', hL', hLB'⟩ := hC ε hε j i z
    have hfun : (fun dt : ℝ => (1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * k dt z x)
        = fun dt : ℝ => (1 / dt) * ∫ x in ball z ε, (x j - z j) * (x i - z i) * k dt z x := by
      funext dt
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hfun] at hL
    have hLL' : L = L' := tendsto_nhds_unique hL hL'
    subst hLL'
    have h1 : |L - B z i j| ≤ C' * ε := le_trans hLB (by
      have : C ≤ C' := le_max_left _ _
      nlinarith)
    have h2 : |L - B z j i| ≤ C' * ε := le_trans hLB' (by
      have : C ≤ C' := le_max_left _ _
      nlinarith)
    calc |B z i j - B z j i| = |(L - B z j i) - (L - B z i j)| := by ring_nf
      _ ≤ |L - B z j i| + |L - B z i j| := abs_sub _ _
      _ ≤ 2 * C' * ε := by linarith
  have hzero : |B z i j - B z j i| ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    set d := |B z i j - B z j i| with hd
    have hε : 0 < d / (2 * C' + 2) := by positivity
    have := hle _ hε
    have hden : (0 : ℝ) < 2 * C' + 2 := by positivity
    have hlt : 2 * C' * (d / (2 * C' + 2)) < d := by
      have hrw : 2 * C' * (d / (2 * C' + 2)) = (2 * C' * d) / (2 * C' + 2) := by ring
      rw [hrw, div_lt_iff₀ hden]
      nlinarith
    linarith
  have : B z i j - B z j i = 0 := by
    have := abs_nonneg (B z i j - B z j i)
    have habs : |B z i j - B z j i| = 0 := le_antisymm hzero this
    exact abs_eq_zero.mp habs
  linarith

/-- The diffusion matrix defined by condition (iii), (3.4.3), is positive
semidefinite, since it is a limit of second moments of a non-negative measure. -/
theorem CondDiffusion.posSemidef_of_cond {k : ℝ → Sp n → Sp n → ℝ}
    {B : Sp n → Fin n → Fin n → ℝ} (h : CondDiffusion k B)
    (hk : ∀ dt z x, 0 ≤ k dt z x)
    (hint : ∀ (dt : ℝ), 0 < dt → ∀ (ε : ℝ), 0 < ε → ∀ (z : Sp n) (i j : Fin n),
      IntegrableOn (fun x => (x i - z i) * (x j - z j) * k dt z x) (ball z ε))
    (z : Sp n) (a : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, a i * a j * B z i j := by
  obtain ⟨C, hC⟩ := h
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  set M : ℝ := (∑ i, |a i|) ^ 2 with hMdef
  have hM0 : 0 ≤ M := by positivity
  set S : ℝ := ∑ i, ∑ j, a i * a j * B z i j with hSdef
  have key : ∀ ε > (0 : ℝ), -(M * C' * ε) ≤ S := by
    intro ε hε
    choose L hL hLB using hC ε hε
    -- the quadratic form of the finite-`dt` second moments is non-negative
    have hnn : ∀ dt : ℝ, 0 < dt → 0 ≤ ∑ i, ∑ j, a i * a j *
        ((1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * k dt z x) := by
      intro dt hdt
      have hIint : ∀ i j : Fin n, IntegrableOn
          (fun x : Sp n => a i * a j * ((x i - z i) * (x j - z j) * k dt z x)) (ball z ε) :=
        fun i j => (hint dt hdt ε hε z i j).const_mul _
      have hpt : ∀ x : Sp n, (∑ i, ∑ j,
          a i * a j * ((x i - z i) * (x j - z j) * k dt z x))
          = (∑ i, a i * (x i - z i)) ^ 2 * k dt z x := by
        intro x
        have hsq : (∑ i, a i * (x i - z i)) ^ 2
            = ∑ i, ∑ j, (a i * (x i - z i)) * (a j * (x j - z j)) := by
          rw [sq, Finset.sum_mul_sum]
        rw [hsq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hswap : (∑ i, ∑ j, a i * a j *
          ((1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * k dt z x))
          = (1 / dt) * ∫ x in ball z ε, (∑ i, a i * (x i - z i)) ^ 2 * k dt z x := by
        have e1 : ∀ i j : Fin n, a i * a j *
            ((1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * k dt z x)
            = (1 / dt) * ∫ x in ball z ε,
              a i * a j * ((x i - z i) * (x j - z j) * k dt z x) := by
          intro i j; rw [integral_const_mul]; ring
        simp_rw [e1, ← Finset.mul_sum]
        congr 1
        have step1 : ∀ i : Fin n,
            (∑ j, ∫ x in ball z ε, a i * a j * ((x i - z i) * (x j - z j) * k dt z x))
            = ∫ x in ball z ε, ∑ j, a i * a j * ((x i - z i) * (x j - z j) * k dt z x) :=
          fun i => (integral_finset_sum _ (fun j _ => hIint i j)).symm
        rw [Finset.sum_congr rfl (fun i _ => step1 i),
          ← integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hIint i j)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x)
      rw [hswap]
      have hpos : 0 ≤ ∫ x in ball z ε, (∑ i, a i * (x i - z i)) ^ 2 * k dt z x :=
        setIntegral_nonneg measurableSet_ball fun x _ =>
          mul_nonneg (by positivity) (hk dt z x)
      have : (0 : ℝ) ≤ 1 / dt := by positivity
      exact mul_nonneg this hpos
    -- pass to the limit `dt → 0`
    have htend : Tendsto (fun dt : ℝ => ∑ i, ∑ j, a i * a j *
        ((1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * k dt z x))
        (𝓝[>] (0 : ℝ)) (𝓝 (∑ i, ∑ j, a i * a j * L i j z)) := by
      refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
      exact ((hL i j z).const_mul (a i * a j))
    have hev : ∀ᶠ dt in 𝓝[>] (0 : ℝ), 0 ≤ ∑ i, ∑ j, a i * a j *
        ((1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * k dt z x) :=
      Filter.eventually_of_mem self_mem_nhdsWithin fun dt hdt => hnn dt hdt
    have hlim0 : 0 ≤ ∑ i, ∑ j, a i * a j * L i j z := ge_of_tendsto htend hev
    -- compare the limit with the diffusion matrix
    have hterm : ∀ i j : Fin n,
        a i * a j * L i j z - a i * a j * B z i j ≤ |a i| * |a j| * (C' * ε) := by
      intro i j
      have h1 : |L i j z - B z i j| ≤ C' * ε := le_trans (hLB i j z) (by nlinarith)
      have h2 : a i * a j * L i j z - a i * a j * B z i j
          = (a i * a j) * (L i j z - B z i j) := by ring
      rw [h2]
      calc (a i * a j) * (L i j z - B z i j)
          ≤ |(a i * a j) * (L i j z - B z i j)| := le_abs_self _
        _ = |a i| * |a j| * |L i j z - B z i j| := by rw [abs_mul, abs_mul]
        _ ≤ |a i| * |a j| * (C' * ε) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hsum : (∑ i, ∑ j, a i * a j * L i j z) - S ≤ M * (C' * ε) := by
      have hsub : (∑ i, ∑ j, a i * a j * L i j z) - S
          = ∑ i, ∑ j, (a i * a j * L i j z - a i * a j * B z i j) := by
        rw [hSdef, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_sub_distrib (s := Finset.univ)
          (f := fun j => a i * a j * L i j z) (g := fun j => a i * a j * B z i j)).symm
      have hbound : (∑ i, ∑ j, (a i * a j * L i j z - a i * a j * B z i j))
          ≤ ∑ i, ∑ j, |a i| * |a j| * (C' * ε) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      have hMsum : (∑ i, ∑ j, |a i| * |a j| * (C' * ε)) = M * (C' * ε) := by
        have h1 : ∀ i : Fin n, (∑ j, |a i| * |a j| * (C' * ε))
            = (∑ j, |a i| * |a j|) * (C' * ε) := fun i => (Finset.sum_mul _ _ _).symm
        rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_mul, ← Finset.sum_mul_sum,
          hMdef, sq]
      rw [hsub]
      exact le_trans hbound (le_of_eq hMsum)
    nlinarith
  -- conclude by letting `ε → 0`
  by_contra hneg
  push_neg at hneg
  set K : ℝ := M * C' with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hM0 hC'0
  have hε : 0 < (-S) / (K + 1) := div_pos (by linarith) (by positivity)
  have hk1 := key _ hε
  have hden : (0 : ℝ) < K + 1 := by positivity
  have hlt : K * ((-S) / (K + 1)) < -S := by
    have hrw : K * ((-S) / (K + 1)) = (K * (-S)) / (K + 1) := by ring
    rw [hrw, div_lt_iff₀ hden]
    nlinarith
  linarith

/-! ### 3.5.2 The Gaussian short-time solution (3.5.9), in one dimension -/

/-- (3.5.9) in one dimension: the Gaussian density with mean `y + A t` and
variance `B t`. -/
def gauss (A B y : ℝ) (t z : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * B * t))⁻¹ * Real.exp (-(z - y - A * t) ^ 2 / (2 * B * t))

/-- The Gaussian (3.5.9) satisfies the frozen-coefficient Fokker–Planck equation
(3.5.8) in the space variable: `∂_z G = G · (-(z - y - A t)/(B t))`. -/
theorem hasDerivAt_gauss_space (A B y t z : ℝ) (hB : 0 < B) (ht : 0 < t) :
    HasDerivAt (fun w => gauss A B y t w)
      (gauss A B y t z * (-(z - y - A * t) / (B * t))) z := by
  have h1 : HasDerivAt (fun w : ℝ => w - y - A * t) 1 z :=
    ((hasDerivAt_id z).sub_const y).sub_const (A * t)
  have h2 : HasDerivAt (fun w : ℝ => (w - y - A * t) ^ 2) (2 * (z - y - A * t)) z := by
    simpa using h1.pow 2
  have h3 : HasDerivAt (fun w : ℝ => -(w - y - A * t) ^ 2 / (2 * B * t))
      (-(2 * (z - y - A * t)) / (2 * B * t)) z := h2.neg.div_const _
  have h4 := (Real.hasDerivAt_exp (-(z - y - A * t) ^ 2 / (2 * B * t))).comp z h3
  have h5 := h4.const_mul (Real.sqrt (2 * Real.pi * B * t))⁻¹
  convert h5 using 1
  simp only [gauss]
  field_simp

/-- The second space derivative of the Gaussian (3.5.9). -/
theorem hasDerivAt_gauss_space_two (A B y t z : ℝ) (hB : 0 < B) (ht : 0 < t) :
    HasDerivAt (fun w => gauss A B y t w * (-(w - y - A * t) / (B * t)))
      (gauss A B y t z * ((z - y - A * t) ^ 2 / (B * t) ^ 2 - 1 / (B * t))) z := by
  have hBt : (B * t) ≠ 0 := by positivity
  have hg := hasDerivAt_gauss_space A B y t z hB ht
  have h0 : HasDerivAt (fun w : ℝ => -(w - y - A * t)) (-1) z :=
    (((hasDerivAt_id z).sub_const y).sub_const (A * t)).neg
  have h1 : HasDerivAt (fun w : ℝ => -(w - y - A * t) / (B * t)) (-1 / (B * t)) z :=
    h0.div_const (B * t)
  have hmul := hg.mul h1
  convert hmul using 1
  field_simp
  ring

/-- The time derivative of the Gaussian (3.5.9). -/
theorem hasDerivAt_gauss_time (A B y t z : ℝ) (hB : 0 < B) (ht : 0 < t) :
    HasDerivAt (fun s => gauss A B y s z)
      (gauss A B y t z * (-(1 / (2 * t)) + A * (z - y - A * t) / (B * t)
        + (z - y - A * t) ^ 2 / (2 * B * t ^ 2))) t := by
  have hpos : (0 : ℝ) < 2 * Real.pi * B * t := by positivity
  have hsq : Real.sqrt (2 * Real.pi * B * t) ^ 2 = 2 * Real.pi * B * t :=
    Real.sq_sqrt hpos.le
  have hsne : Real.sqrt (2 * Real.pi * B * t) ≠ 0 := by positivity
  have hlin : HasDerivAt (fun s : ℝ => 2 * Real.pi * B * s) (2 * Real.pi * B) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi * B)
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (2 * Real.pi * B * s))
      (1 / (2 * Real.sqrt (2 * Real.pi * B * t)) * (2 * Real.pi * B)) t :=
    (Real.hasDerivAt_sqrt hpos.ne').comp t hlin
  have hc : HasDerivAt (fun s : ℝ => (Real.sqrt (2 * Real.pi * B * s))⁻¹)
      (-(1 / (2 * Real.sqrt (2 * Real.pi * B * t)) * (2 * Real.pi * B))
        / Real.sqrt (2 * Real.pi * B * t) ^ 2) t := hsqrt.inv hsne
  have hu : HasDerivAt (fun s : ℝ => z - y - A * s) (-A) t := by
    simpa using ((hasDerivAt_const t (z - y)).sub ((hasDerivAt_id t).const_mul A))
  have hnum : HasDerivAt (fun s : ℝ => -(z - y - A * s) ^ 2) (2 * A * (z - y - A * t)) t := by
    have h2 : HasDerivAt (fun s : ℝ => (z - y - A * s) ^ 2)
        (2 * (z - y - A * t) ^ 1 * (-A)) t := hu.pow 2
    have h3 := h2.neg
    convert h3 using 1
    ring
  have hden : HasDerivAt (fun s : ℝ => 2 * B * s) (2 * B) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * B)
  have hq : HasDerivAt (fun s : ℝ => -(z - y - A * s) ^ 2 / (2 * B * s))
      ((2 * A * (z - y - A * t) * (2 * B * t) - -(z - y - A * t) ^ 2 * (2 * B))
        / (2 * B * t) ^ 2) t := hnum.div hden (by positivity)
  have hprod := hc.mul hq.exp
  convert hprod using 1
  simp only [gauss]
  rw [hsq]
  field_simp
  ring

/-- **The Gaussian (3.5.9) solves the frozen-coefficient Fokker–Planck equation
(3.5.8)** in one dimension: `∂_t G = -A ∂_z G + (B/2) ∂²_z G`. -/
theorem gauss_solves_fokkerPlanck (A B y t z : ℝ) (hB : 0 < B) (ht : 0 < t) :
    deriv (fun s => gauss A B y s z) t
      = -A * deriv (fun w => gauss A B y t w) z
        + (B / 2) * deriv (deriv (fun w => gauss A B y t w)) z := by
  have hBt : (B * t) ≠ 0 := by positivity
  have hd1 : deriv (fun w => gauss A B y t w)
      = fun w => gauss A B y t w * (-(w - y - A * t) / (B * t)) :=
    funext fun w => (hasDerivAt_gauss_space A B y t w hB ht).deriv
  rw [hd1, (hasDerivAt_gauss_time A B y t z hB ht).deriv,
    (hasDerivAt_gauss_space_two A B y t z hB ht).deriv]
  field_simp
  ring

end Gardiner
