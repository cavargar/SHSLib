/-
# Asymptotic method for stationary distributions

Gardiner, *Handbook of Stochastic Methods*, §6.3.3, (6.3.52)–(6.3.56).

For the Fokker–Planck equation (6.3.52) with small diffusion `ε² B`, the ansatz (6.3.53)
`p_s(x) = exp[-φ(x)/ε²]` turns the stationary equation into (6.3.54), whose leading order in
`ε` is the Hamilton–Jacobi equation (6.3.56).

* `Gardiner.snStatEq` — the left-hand side of (6.3.54), in corrected form:
  `[Σ Aᵢ∂ᵢφ + ½ Σ Bᵢⱼ ∂ᵢφ ∂ⱼφ]
    + ε² [-Σ ∂ᵢAᵢ - ½ Σ (∂ᵢBᵢⱼ ∂ⱼφ + ∂ⱼBᵢⱼ ∂ᵢφ) - ½ Σ Bᵢⱼ ∂ᵢ∂ⱼφ] + ε⁴ [½ Σ ∂ᵢ∂ⱼBᵢⱼ]`.
* `Gardiner.fpRHS_exp_eq` — the identity
  `fpRHS[exp(-φ/ε²)] = ε⁻² exp(-φ/ε²) · snStatEq`, valid for all `C²` coefficients.
* `Gardiner.stationary_exp_iff` — (6.3.53) is stationary iff (6.3.54) holds.
* `Gardiner.hamiltonJacobi_of_stationary` — (6.3.55)–(6.3.56): if
  `exp[-(φ₀ + εφ₁)/ε²]` is stationary for arbitrarily small `ε ≠ 0`, then `φ₀` solves the
  Hamilton–Jacobi equation `Σ Aᵢ∂ᵢφ₀ + ½ Σ Bᵢⱼ ∂ᵢφ₀ ∂ⱼφ₀ = 0`.
* `Gardiner.ou_stationary_exp`, `Gardiner.ou_hamiltonJacobi` — non-degenerate instance: the
  Ornstein–Uhlenbeck process `A = -kx`, `B = 1`, `φ = kx²`.

**Erratum.**  The printed (6.3.54) reads
`… + ε²[-Σ ∂ᵢAᵢ + Σ ∂ᵢBᵢⱼ ∂ⱼφ + Σ ∂ᵢ∂ⱼBᵢⱼ] = 0`; the correct equation (formalized here) has
the coefficients `-½(∂ᵢBᵢⱼ∂ⱼφ + ∂ⱼBᵢⱼ∂ᵢφ)` (`= -Σ ∂ᵢBᵢⱼ∂ⱼφ` for symmetric `B`), an additional
term `-½ Σ Bᵢⱼ ∂ᵢ∂ⱼφ` at order `ε²`, and the term `½ Σ ∂ᵢ∂ⱼBᵢⱼ` at order `ε⁴`, not `ε²`.
The leading order (6.3.56) is unaffected.
-/
import SHSLib.Gardiner.Special

open Finset Filter Topology

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-! ### Calculus for `pd` -/

lemma pd_add_fun (u v : Sp n → ℝ) (i : Fin n) (z : Sp n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    pd (fun w => u w + v w) i z = pd u i z + pd v i z := by
  have hd : HasFDerivAt (fun w => u w + v w) (fderiv ℝ u z + fderiv ℝ v z) z :=
    hu.hasFDerivAt.add hv.hasFDerivAt
  rw [pd, hd.fderiv]
  simp [pd]

lemma pd_const_mul_fun (a : ℝ) (u : Sp n → ℝ) (i : Fin n) (z : Sp n)
    (hu : DifferentiableAt ℝ u z) :
    pd (fun w => a * u w) i z = a * pd u i z := by
  have hd : HasFDerivAt (fun w => a * u w) (a • fderiv ℝ u z) z := hu.hasFDerivAt.const_mul a
  rw [pd, hd.fderiv]
  simp [pd]

lemma pd_exp_div (phi : Sp n → ℝ) (ε : ℝ) (i : Fin n) (z : Sp n)
    (hphi : DifferentiableAt ℝ phi z) :
    pd (fun w => Real.exp (-phi w / ε ^ 2)) i z
      = -pd phi i z / ε ^ 2 * Real.exp (-phi z / ε ^ 2) := by
  have e : (fun w => Real.exp (-phi w / ε ^ 2)) = fun w => Real.exp ((-1 / ε ^ 2) * phi w) := by
    funext w; ring_nf
  have hd := (hphi.hasFDerivAt.const_mul (-1 / ε ^ 2)).exp
  rw [e, pd, hd.fderiv]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, pd]
  ring_nf

/-! ### The stationary equation (6.3.54) -/

/-- The Hamilton–Jacobi operator `Σ Aᵢ∂ᵢφ + ½ Σ Bᵢⱼ ∂ᵢφ ∂ⱼφ`, the left-hand side of (6.3.56). -/
def snHJ (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (phi : Sp n → ℝ) (z : Sp n) : ℝ :=
  ∑ i, A z i * pd phi i z + (1 / 2) * ∑ i, ∑ j, B z i j * pd phi i z * pd phi j z

/-- The `ε²` bracket of the corrected (6.3.54). -/
def snFirst (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (phi : Sp n → ℝ)
    (z : Sp n) : ℝ :=
  -∑ i, pd (fun w => A w i) i z
    - (1 / 2) * ∑ i, ∑ j, (pd (fun w => B w i j) i z * pd phi j z
        + pd (fun w => B w i j) j z * pd phi i z)
    - (1 / 2) * ∑ i, ∑ j, B z i j * pd2 phi i j z

/-- The `ε⁴` bracket of the corrected (6.3.54). -/
def snSecond (B : Sp n → Fin n → Fin n → ℝ) (z : Sp n) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, pd2 (fun w => B w i j) i j z

/-- The left-hand side of (6.3.54) (corrected). -/
def snStatEq (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (phi : Sp n → ℝ) (ε : ℝ)
    (z : Sp n) : ℝ :=
  snHJ A B phi z + ε ^ 2 * snFirst A B phi z + ε ^ 4 * snSecond B z

/-- **(6.3.53)–(6.3.54).**  For `C¹` drift, `C²` diffusion and `C²` potential `φ`, the
Fokker–Planck operator of (6.3.52) (diffusion `ε²B`) applied to `exp(-φ/ε²)` equals
`ε⁻² exp(-φ/ε²)` times the left-hand side of the corrected (6.3.54). -/
theorem fpRHS_exp_eq (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (phi : Sp n → ℝ)
    (hA : ∀ i, ContDiff ℝ 1 (fun w => A w i)) (hB : ∀ i j, ContDiff ℝ 2 (fun w => B w i j))
    (hphi : ContDiff ℝ 2 phi) {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) (z : Sp n) :
    fpRHS (fun _ w => Real.exp (-phi w / ε ^ 2)) A (fun w i j => ε ^ 2 * B w i j) t z
      = Real.exp (-phi z / ε ^ 2) / ε ^ 2 * snStatEq A B phi ε z := by
  set p : Sp n → ℝ := fun w => Real.exp (-phi w / ε ^ 2) with hpdef
  have hphiD : Differentiable ℝ phi := hphi.differentiable (by norm_num)
  have hpC : ContDiff ℝ 2 p := ((hphi.neg).div_const _).exp
  have hpD : Differentiable ℝ p := hpC.differentiable (by norm_num)
  have hBD : ∀ i j, Differentiable ℝ (fun w => B w i j) := fun i j =>
    (hB i j).differentiable (by norm_num)
  have hAD : ∀ i, Differentiable ℝ (fun w => A w i) := fun i => (hA i).differentiable one_ne_zero
  have hpd : ∀ i w, pd p i w = -pd phi i w / ε ^ 2 * p w := fun i w =>
    pd_exp_div phi ε i w (hphiD w)
  have hpdphiD : ∀ j, Differentiable ℝ (pd phi j) := fun j =>
    (contDiff_pd phi hphi j).differentiable one_ne_zero
  have hpdBD : ∀ i j k, Differentiable ℝ (pd (fun w => B w i j) k) := fun i j k =>
    (contDiff_pd _ (hB i j) k).differentiable one_ne_zero
  -- the drift term
  have hdrift : ∀ i, pd (fun w => A w i * p w) i z
      = (pd (fun w => A w i) i z - A z i * pd phi i z / ε ^ 2) * p z := by
    intro i
    rw [pd_mul _ _ i z (hAD i z) (hpD z), hpd]
    ring
  -- the diffusion term
  have hfirst : ∀ i j, pd (fun w => ε ^ 2 * B w i j * p w) j
      = fun w => (ε ^ 2 * pd (fun w => B w i j) j w) * p w
          + (-B w i j) * (pd phi j w * p w) := by
    intro i j
    funext w
    rw [pd_mul (fun w => ε ^ 2 * B w i j) p j w ((hBD i j w).const_mul _) (hpD w),
      pd_const_mul_fun _ _ j w (hBD i j w), hpd]
    field_simp
  have hdiff : ∀ i j, pd2 (fun w => ε ^ 2 * B w i j * p w) i j z
      = (ε ^ 2 * pd2 (fun w => B w i j) i j z - pd (fun w => B w i j) j z * pd phi i z
        - pd (fun w => B w i j) i z * pd phi j z - B z i j * pd2 phi i j z
        + B z i j * pd phi j z * pd phi i z / ε ^ 2) * p z := by
    intro i j
    rw [pd2, hfirst i j]
    have h1 : DifferentiableAt ℝ (fun w => ε ^ 2 * pd (fun w => B w i j) j w * p w) z :=
      ((hpdBD i j j z).const_mul _).mul (hpD z)
    have h2 : DifferentiableAt ℝ (fun w => -B w i j * (pd phi j w * p w)) z :=
      (hBD i j z).neg.mul ((hpdphiD j z).mul (hpD z))
    rw [pd_add_fun _ _ i z h1 h2,
      pd_mul (fun w => ε ^ 2 * pd (fun w => B w i j) j w) p i z ((hpdBD i j j z).const_mul _)
        (hpD z),
      pd_const_mul_fun _ _ i z (hpdBD i j j z),
      pd_mul (fun w => -B w i j) (fun w => pd phi j w * p w) i z (hBD i j z).neg
        ((hpdphiD j z).mul (hpD z)),
      pd_mul _ _ i z (hpdphiD j z) (hpD z), hpd]
    have hneg : pd (fun w => -B w i j) i z = -pd (fun w => B w i j) i z := by
      have := pd_const_mul_fun (-1) (fun w => B w i j) i z (hBD i j z)
      simp only [neg_one_mul] at this
      exact this
    rw [hneg]
    simp only [pd2]
    field_simp
    ring
  -- assemble
  have hfp : fpRHS (fun _ w => Real.exp (-phi w / ε ^ 2)) A (fun w i j => ε ^ 2 * B w i j) t z
      = -(∑ i, pd (fun w => A w i * p w) i z)
        + (1 / 2) * ∑ i, ∑ j, pd2 (fun w => ε ^ 2 * B w i j * p w) i j z := rfl
  rw [hfp]
  simp only [hdrift, hdiff]
  have hsymm : ∑ i, ∑ j, B z i j * pd phi j z * pd phi i z
      = ∑ i, ∑ j, B z i j * pd phi i z * pd phi j z :=
    sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have e1 : ∑ i, ∑ j, (ε ^ 2 * pd2 (fun w => B w i j) i j z - pd (fun w => B w i j) j z * pd phi i z
        - pd (fun w => B w i j) i z * pd phi j z - B z i j * pd2 phi i j z
        + B z i j * pd phi j z * pd phi i z / ε ^ 2) * p z
      = p z * (ε ^ 2 * ∑ i, ∑ j, pd2 (fun w => B w i j) i j z
        - ∑ i, ∑ j, (pd (fun w => B w i j) i z * pd phi j z
            + pd (fun w => B w i j) j z * pd phi i z)
        - ∑ i, ∑ j, B z i j * pd2 phi i j z
        + (∑ i, ∑ j, B z i j * pd phi j z * pd phi i z) / ε ^ 2) := by
    simp only [mul_sum, sum_div, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have e2 : ∑ i, (pd (fun w => A w i) i z - A z i * pd phi i z / ε ^ 2) * p z
      = p z * (∑ i, pd (fun w => A w i) i z - (∑ i, A z i * pd phi i z) / ε ^ 2) := by
    simp only [mul_sum, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e1, e2, hsymm, show Real.exp (-phi z / ε ^ 2) = p z from rfl]
  simp only [snStatEq, snHJ, snFirst, snSecond]
  field_simp
  ring

/-- (6.3.53) is a stationary solution of (6.3.52) iff the corrected (6.3.54) holds. -/
theorem stationary_exp_iff (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (phi : Sp n → ℝ) (hA : ∀ i, ContDiff ℝ 1 (fun w => A w i))
    (hB : ∀ i j, ContDiff ℝ 2 (fun w => B w i j)) (hphi : ContDiff ℝ 2 phi) {ε : ℝ}
    (hε : ε ≠ 0) (t : ℝ) :
    (∀ z, fpRHS (fun _ w => Real.exp (-phi w / ε ^ 2)) A (fun w i j => ε ^ 2 * B w i j) t z = 0)
      ↔ ∀ z, snStatEq A B phi ε z = 0 := by
  refine forall_congr' fun z => ?_
  rw [fpRHS_exp_eq A B phi hA hB hphi hε t z]
  have : Real.exp (-phi z / ε ^ 2) / ε ^ 2 ≠ 0 := by positivity
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left this
  · intro h; rw [h, mul_zero]

/-- **(6.3.55)–(6.3.56): the Hamilton–Jacobi equation.**  Let `φ_ε = φ₀ + εφ₁` (the expansion
(6.3.55) to first order, with `C²` coefficients).  If `exp(-φ_ε/ε²)` is a stationary solution of
(6.3.52) for arbitrarily small `ε ≠ 0`, then `φ₀` satisfies
`Σ Aᵢ∂ᵢφ₀ + ½ Σ Bᵢⱼ ∂ᵢφ₀ ∂ⱼφ₀ = 0`. -/
theorem hamiltonJacobi_of_stationary (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (phi0 phi1 : Sp n → ℝ) (hA : ∀ i, ContDiff ℝ 1 (fun w => A w i))
    (hB : ∀ i j, ContDiff ℝ 2 (fun w => B w i j)) (hphi0 : ContDiff ℝ 2 phi0)
    (hphi1 : ContDiff ℝ 2 phi1) (t : ℝ)
    (hstat : ∃ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ z, fpRHS (fun _ w => Real.exp (-(phi0 w + ε * phi1 w) / ε ^ 2))
      A (fun w i j => ε ^ 2 * B w i j) t z = 0) (z : Sp n) :
    snHJ A B phi0 z = 0 := by
  have h0D : Differentiable ℝ phi0 := hphi0.differentiable (by norm_num)
  have h1D : Differentiable ℝ phi1 := hphi1.differentiable (by norm_num)
  have h0D' : ∀ j, Differentiable ℝ (pd phi0 j) := fun j =>
    (contDiff_pd phi0 hphi0 j).differentiable one_ne_zero
  have h1D' : ∀ j, Differentiable ℝ (pd phi1 j) := fun j =>
    (contDiff_pd phi1 hphi1 j).differentiable one_ne_zero
  -- partial derivatives of `φ_ε`
  have hpd : ∀ ε i w, pd (fun w => phi0 w + ε * phi1 w) i w = pd phi0 i w + ε * pd phi1 i w :=
    fun ε i w => by
      rw [pd_add_fun _ _ i w (h0D w) ((h1D w).const_mul ε), pd_const_mul_fun _ _ i w (h1D w)]
  have hpd2 : ∀ ε i j, pd2 (fun w => phi0 w + ε * phi1 w) i j z
      = pd2 phi0 i j z + ε * pd2 phi1 i j z := fun ε i j => by
    rw [pd2, show pd (fun w => phi0 w + ε * phi1 w) j = fun w => pd phi0 j w + ε * pd phi1 j w
      from funext (hpd ε j), pd_add_fun _ _ i z (h0D' j z) ((h1D' j z).const_mul ε),
      pd_const_mul_fun _ _ i z (h1D' j z)]
    rfl
  -- `snStatEq` along `φ_ε` is a continuous function of `ε`, equal at `ε = 0` to `snHJ φ₀`
  set F : ℝ → ℝ := fun ε =>
    (∑ i, A z i * (pd phi0 i z + ε * pd phi1 i z)
      + (1 / 2) * ∑ i, ∑ j, B z i j * (pd phi0 i z + ε * pd phi1 i z)
        * (pd phi0 j z + ε * pd phi1 j z))
    + ε ^ 2 * (-∑ i, pd (fun w => A w i) i z
      - (1 / 2) * ∑ i, ∑ j, (pd (fun w => B w i j) i z * (pd phi0 j z + ε * pd phi1 j z)
          + pd (fun w => B w i j) j z * (pd phi0 i z + ε * pd phi1 i z))
      - (1 / 2) * ∑ i, ∑ j, B z i j * (pd2 phi0 i j z + ε * pd2 phi1 i j z))
    + ε ^ 4 * snSecond B z with hF
  have hFeq : ∀ ε, snStatEq A B (fun w => phi0 w + ε * phi1 w) ε z = F ε := fun ε => by
    simp only [snStatEq, snHJ, snFirst, hpd, hpd2, hF]
  have hFc : Continuous F := by
    simp only [hF]; fun_prop
  have hF0 : F 0 = snHJ A B phi0 z := by simp [hF, snHJ]
  have hlim : Tendsto F (𝓝[≠] 0) (𝓝 (snHJ A B phi0 z)) :=
    hF0 ▸ (hFc.tendsto 0).mono_left nhdsWithin_le_nhds
  by_contra hne
  have hev := hlim.eventually_ne hne
  have hev' : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ≠ 0 := self_mem_nhdsWithin
  obtain ⟨ε, hε, hεF, hε0⟩ := (hstat.and_eventually (hev.and hev')).exists
  have hC : ContDiff ℝ 2 (fun w => phi0 w + ε * phi1 w) := hphi0.add (hphi1.const_smul ε)
  have := (stationary_exp_iff A B (fun w => phi0 w + ε * phi1 w) hA hB hC hε0 t).1 hε z
  rw [hFeq] at this
  exact hεF this

/-! ### Non-degenerate instance: the Ornstein–Uhlenbeck process -/

lemma pd_coord_self {n : ℕ} (i : Fin n) (z : Sp n) : pd (fun w : Sp n => w i) i z = 1 := by
  have hd : HasFDerivAt (fun w : Sp n => w i) (EuclideanSpace.proj i : Sp n →L[ℝ] ℝ) z :=
    (EuclideanSpace.proj i : Sp n →L[ℝ] ℝ).hasFDerivAt
  rw [pd, hd.fderiv]
  simp

lemma pd_ou_potential (k : ℝ) (z : Sp 1) :
    pd (fun w : Sp 1 => k * w 0 ^ 2) 0 z = 2 * k * z 0 := by
  have hd : HasFDerivAt (fun w : Sp 1 => k * w 0 ^ 2)
      ((k * (2 * z 0)) • (EuclideanSpace.proj 0 : Sp 1 →L[ℝ] ℝ)) z := by
    have h1 := (EuclideanSpace.proj (0 : Fin 1) : Sp 1 →L[ℝ] ℝ).hasFDerivAt (x := z)
    have h2 := (h1.pow 2).const_mul k
    convert h2 using 1
    simp [smul_smul]
  rw [pd, hd.fderiv]
  simp; ring

lemma pd_ou_drift (k : ℝ) (z : Sp 1) : pd (fun w : Sp 1 => -k * w 0) 0 z = -k := by
  rw [pd_const_mul_fun (-k) (fun w : Sp 1 => w 0) 0 z
    (EuclideanSpace.proj (0 : Fin 1) : Sp 1 →L[ℝ] ℝ).differentiableAt, pd_coord_self]; ring

lemma pd2_ou_potential (k : ℝ) (z : Sp 1) : pd2 (fun w : Sp 1 => k * w 0 ^ 2) 0 0 z = 2 * k := by
  rw [pd2, show pd (fun w : Sp 1 => k * w 0 ^ 2) 0 = fun w => (2 * k) * w 0 from
    funext fun w => pd_ou_potential k w,
    pd_const_mul_fun (2 * k) (fun w : Sp 1 => w 0) 0 z
      (EuclideanSpace.proj (0 : Fin 1) : Sp 1 →L[ℝ] ℝ).differentiableAt, pd_coord_self]; ring

lemma pd_const_fun {n : ℕ} (c : ℝ) (i : Fin n) (z : Sp n) : pd (fun _ : Sp n => c) i z = 0 := by
  simp [pd]

theorem ou_snStatEq (k ε : ℝ) (z : Sp 1) :
    snStatEq (fun w _ => -k * w 0) (fun _ _ _ => 1) (fun w => k * w 0 ^ 2) ε z = 0 := by
  have hc : pd2 (fun _ : Sp 1 => (1 : ℝ)) 0 0 z = 0 := by
    rw [pd2, show pd (fun _ : Sp 1 => (1 : ℝ)) 0 = fun _ => 0 from funext fun w => pd_const_fun 1 0 w]
    exact pd_const_fun 0 0 z
  simp only [snStatEq, snHJ, snFirst, snSecond, Fin.sum_univ_one, pd_ou_potential, pd_ou_drift,
    pd2_ou_potential, pd_const_fun, hc]
  ring

/-- **Non-degenerate instance of (6.3.53)–(6.3.54).**  For the Ornstein–Uhlenbeck process
`A(x) = -kx`, `B = 1` (so that (6.3.52) is `∂ₜp = ∂ₓ(kxp) + ½ε² ∂ₓ²p`), the function
`exp(-kx²/ε²)` is an exact stationary solution for every `ε ≠ 0`. -/
theorem ou_stationary_exp (k : ℝ) {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) (z : Sp 1) :
    fpRHS (fun _ w => Real.exp (-(k * w 0 ^ 2) / ε ^ 2)) (fun w _ => -k * w 0)
      (fun _ _ _ => ε ^ 2 * 1) t z = 0 := by
  have hA : ∀ i : Fin 1, ContDiff ℝ 1 (fun w : Sp 1 => -k * w 0) := fun _ =>
    contDiff_const.mul (EuclideanSpace.proj (0 : Fin 1) : Sp 1 →L[ℝ] ℝ).contDiff
  have hphi : ContDiff ℝ 2 (fun w : Sp 1 => k * w 0 ^ 2) :=
    contDiff_const.mul ((EuclideanSpace.proj (0 : Fin 1) : Sp 1 →L[ℝ] ℝ).contDiff.pow 2)
  exact (stationary_exp_iff (fun w _ => -k * w 0) (fun _ _ _ => 1) (fun w => k * w 0 ^ 2) hA
    (fun _ _ => contDiff_const) hphi hε t).2 (fun z => ou_snStatEq k ε z) z

/-- **Non-degenerate instance of (6.3.55)–(6.3.56).**  The hypotheses of
`hamiltonJacobi_of_stationary` hold for the Ornstein–Uhlenbeck process (`φ₀ = kx²`, `φ₁ = 0`),
and its conclusion is the Hamilton–Jacobi equation `-kx · 2kx + ½ (2kx)² = 0`. -/
theorem ou_hamiltonJacobi (k t : ℝ) (z : Sp 1) :
    snHJ (fun w _ => -k * w 0) (fun _ _ _ => 1) (fun w => k * w 0 ^ 2) z = 0 := by
  have hA : ∀ i : Fin 1, ContDiff ℝ 1 (fun w : Sp 1 => -k * w 0) := fun _ =>
    contDiff_const.mul (EuclideanSpace.proj (0 : Fin 1) : Sp 1 →L[ℝ] ℝ).contDiff
  have hphi : ContDiff ℝ 2 (fun w : Sp 1 => k * w 0 ^ 2) :=
    contDiff_const.mul ((EuclideanSpace.proj (0 : Fin 1) : Sp 1 →L[ℝ] ℝ).contDiff.pow 2)
  refine hamiltonJacobi_of_stationary (fun w _ => -k * w 0) (fun _ _ _ => 1)
    (fun w => k * w 0 ^ 2) (fun _ => 0) hA (fun _ _ => contDiff_const) hphi contDiff_const t ?_ z
  refine Eventually.frequently ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  intro w
  have := ou_stationary_exp k hε t w
  simpa using this

end Gardiner
