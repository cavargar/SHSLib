/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The differential Chapman–Kolmogorov equation (Gardiner, Ullah) in the
# categorical organization

Gardiner (§3.4, §3.6) and Ullah–Wolkenhauer (§8.2) derive the dCKE from a
transition density `k ds y z = p(z, t+ds | y, t)` satisfying the regularity
conditions (i)–(iii).  This file places that framework in the categorical
picture:

* `Gardiner.dckePres A B W` — the generator presentation of the (backward)
  dCKE operator `Lg = A·∇g + ½ B:∇²g + PV∫ (g(z) − g(y)) W(z|y) dz` on `ℝⁿ`,
  for compactly supported `C²` test functions.
* `Gardiner.hasStrongGenerator_of_kernel` — **the bridge to transition
  semigroups**: if a transition semigroup (in the sense of Bujorianu–Lygeros)
  is represented by a normalized transition density satisfying Gardiner's
  conditions, then Gardiner's backward generator theorem
  (`Gardiner.backward_generator_of_kernel`) identifies its strong generator on
  test functions with the dCKE operator.
* `Gardiner.GardinerKernel.hom` — the same fact as a morphism
  `SemigroupSys.strongGenerator.obj ⟨ℝⁿ, S⟩ ⟶ dckePres A B W` in `GenPres`, so
  Dynkin's formula / martingale problems / forward equations for the semigroup
  transfer to the dCKE presentation.
* `Gardiner.GardinerKernel.ofUllah` — the same kernel object built from Ullah's
  conditional-moment conditions (8.8)–(8.9) (identified with Gardiner's
  conditions (ii)–(iii) by `Ullah.condDrift_iff_mom`/`condDiffusion_iff_mom`);
  and `Ullah.fpTerm_add_jumpTerm` shows that Ullah's strong form (8.13) has
  exactly Gardiner's right-hand side (3.4.22).
-/
import SHSLib.Category.Semigroup
import SHSLib.Gardiner.Backward
import SHSLib.Gardiner.Strong
import SHSLib.Ullah.DCKE

open CategoryTheory MeasureTheory Set Filter Topology Metric

noncomputable section

namespace Gardiner

open SHSCat

variable {n : ℕ}

/-! ### The dCKE presentation -/

/-- A test function of the dCKE operator: a compactly supported `C²` function
whose jump integral exists as a principal value at every point. -/
structure DCKETest (W : Sp n → Sp n → ℝ) : Type where
  /-- The test function. -/
  g : Sp n → ℝ
  contDiff : ContDiff ℝ 2 g
  compactSupport : HasCompactSupport g
  /-- The principal value `PV∫ (g(z) − g(y)) W(z|y) dz`. -/
  pvJump : Sp n → ℝ
  pv : ∀ y, Tendsto (fun ε => bJumpPre W g y ε) (𝓝[>] (0 : ℝ)) (𝓝 (pvJump y))

/-- **The generator presentation of the (backward) dCKE operator.** -/
def dckePres (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (W : Sp n → Sp n → ℝ) :
    GenPres.{0} where
  State := Sp n
  Test := DCKETest W
  ev := fun φ => φ.g
  gen := fun φ y => bwdGen A B φ.g y + φ.pvJump y

/-! ### Kernel semigroups and their strong generator -/

/-- For a semigroup represented by a normalized transition density, the
difference quotient of the semigroup is Gardiner's backward quotient (3.6.3). -/
theorem semigroup_quot_eq_bwdQuot (S : Bujorianu2006.TransitionSemigroup (Sp n))
    (k : ℝ → Sp n → Sp n → ℝ)
    (hrep : ∀ ds > (0 : ℝ), ∀ (g : Sp n → ℝ) (y : Sp n), S.P ds g y = ∫ z, g z * k ds y z)
    (hnorm : ∀ ds > (0 : ℝ), ∀ y, ∫ z, k ds y z = 1)
    (hkint : ∀ ds y, Integrable (fun z => k ds y z))
    {g : Sp n → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (y : Sp n)
    {ds : ℝ} (hds : 0 < ds) :
    (S.P ds g y - g y) / ds = bwdQuot k g y ds := by
  obtain ⟨C, -, hC⟩ := exists_bound_of_contDiff_hasCompactSupport hg hgs
  have hgk : Integrable (fun z => g z * k ds y z) :=
    integrable_mul_of_bounded (hkint ds y) hg.aestronglyMeasurable hC
  have hck : Integrable (fun z => g y * k ds y z) := (hkint ds y).const_mul _
  have hsplit : (∫ z, (g z - g y) * k ds y z) = (∫ z, g z * k ds y z) - g y := by
    have : (fun z => (g z - g y) * k ds y z) = fun z => g z * k ds y z - g y * k ds y z := by
      funext z; ring
    rw [this, integral_sub hgk hck, integral_const_mul, hnorm ds hds y, mul_one]
  rw [bwdQuot, hsplit, hrep ds hds g y, div_eq_inv_mul, one_div]

/-- **Gardiner's backward equation identifies the strong generator.**

Let a transition semigroup be represented, at positive times, by a normalized,
nonnegative, integrable transition density `k` satisfying Gardiner's conditions
(ii)–(iii) (`hA`, `hB`).  For a compactly supported `C²` function `g`, assume
that the generator limit exists at every point (`hD`), that the second moment
over small balls stays bounded (`hsq`, `hM`), that the far-region contribution
converges to the jump integral (condition (i), `hjump`) and that the principal
value `J y` of the jump integral exists (`hPV`).  Then the strong generator of
the semigroup sends `g` to the dCKE operator `A·∇g + ½ B:∇²g + J`. -/
theorem hasStrongGenerator_of_kernel (S : Bujorianu2006.TransitionSemigroup (Sp n))
    {k : ℝ → Sp n → Sp n → ℝ} {A : Sp n → Fin n → ℝ} {B : Sp n → Fin n → Fin n → ℝ}
    (W : Sp n → Sp n → ℝ)
    (hrep : ∀ ds > (0 : ℝ), ∀ (g : Sp n → ℝ) (y : Sp n), S.P ds g y = ∫ z, g z * k ds y z)
    (hnorm : ∀ ds > (0 : ℝ), ∀ y, ∫ z, k ds y z = 1)
    (hk0 : ∀ ds y z, 0 ≤ k ds y z) (hkint : ∀ ds y, Integrable (fun z => k ds y z))
    (hA : CondDrift k A) (hB : CondDiffusion k B)
    {g : Sp n → ℝ} (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g) (J : Sp n → ℝ)
    (hD : ∀ y, ∃ L, Tendsto (bwdQuot k g y) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hsq : ∀ y, ∃ (M : ℝ → ℝ) (C : ℝ),
      (∀ ε > 0, Tendsto (fun ds => bQsq k y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 (M ε))) ∧
      ∀ ε > 0, |M ε| ≤ C)
    (hjump : ∀ y, ∀ ε > 0, Tendsto (fun ds => bQjump k g y ds ε) (𝓝[>] (0 : ℝ))
      (𝓝 (bJumpPre W g y ε)))
    (hPV : ∀ y, Tendsto (fun ε => bJumpPre W g y ε) (𝓝[>] (0 : ℝ)) (𝓝 (J y))) :
    S.HasStrongGenerator g (fun y => bwdGen A B g y + J y) := by
  intro y
  obtain ⟨L, hL⟩ := hD y
  obtain ⟨M, C, hM1, hM2⟩ := hsq y
  have hval : L = bwdGen A B g y + J y :=
    backward_generator_of_kernel W g y L (J y) M C hg hgs (fun ds z => hk0 ds y z)
      (fun ds => hkint ds y) hA hB hL hM1 hM2 (hjump y) (hPV y)
  show Tendsto _ _ (𝓝 (bwdGen A B g y + J y))
  rw [← hval]
  refine hL.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ds hds
  exact (semigroup_quot_eq_bwdQuot S k hrep hnorm hkint hg.continuous hgs y hds).symm

/-- **Gardiner's kernel hypotheses**, uniformly over compactly supported `C²`
test functions, for a transition semigroup `S` on `ℝⁿ` represented by the
transition density `k`, with dCKE coefficients `A`, `B`, `W`. -/
structure GardinerKernel (S : Bujorianu2006.TransitionSemigroup (Sp n))
    (k : ℝ → Sp n → Sp n → ℝ) (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ)
    (W : Sp n → Sp n → ℝ) : Prop where
  rep : ∀ ds > (0 : ℝ), ∀ (g : Sp n → ℝ) (y : Sp n), S.P ds g y = ∫ z, g z * k ds y z
  norm : ∀ ds > (0 : ℝ), ∀ y, ∫ z, k ds y z = 1
  nonneg : ∀ ds y z, 0 ≤ k ds y z
  integrable : ∀ ds y, Integrable (fun z => k ds y z)
  /-- Condition (ii) of §3.4. -/
  drift : CondDrift k A
  /-- Condition (iii) of §3.4. -/
  diffusion : CondDiffusion k B
  /-- The generator limit exists for every test function. -/
  limit_exists : ∀ g : Sp n → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
    ∀ y, ∃ L, Tendsto (bwdQuot k g y) (𝓝[>] (0 : ℝ)) (𝓝 L)
  /-- The second moment over small balls stays bounded, (3.4.14). -/
  second_moment : ∀ y, ∃ (M : ℝ → ℝ) (C : ℝ),
    (∀ ε > 0, Tendsto (fun ds => bQsq k y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 (M ε))) ∧
    ∀ ε > 0, |M ε| ≤ C
  /-- Condition (i) of §3.4: the far region produces the jump integral. -/
  jump : ∀ g : Sp n → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
    ∀ y, ∀ ε > 0, Tendsto (fun ds => bQjump k g y ds ε) (𝓝[>] (0 : ℝ))
      (𝓝 (bJumpPre W g y ε))

namespace GardinerKernel

variable {S : Bujorianu2006.TransitionSemigroup (Sp n)} {k : ℝ → Sp n → Sp n → ℝ}
  {A : Sp n → Fin n → ℝ} {B : Sp n → Fin n → Fin n → ℝ} {W : Sp n → Sp n → ℝ}

/-- Under Gardiner's hypotheses, every dCKE test function lies in the domain of
the strong generator, with the dCKE operator as value. -/
theorem hasStrongGenerator (h : GardinerKernel S k A B W) (φ : DCKETest W) :
    S.HasStrongGenerator φ.g (fun y => bwdGen A B φ.g y + φ.pvJump y) :=
  hasStrongGenerator_of_kernel S W h.rep h.norm h.nonneg h.integrable h.drift h.diffusion
    φ.contDiff φ.compactSupport φ.pvJump (h.limit_exists φ.g φ.contDiff φ.compactSupport)
    h.second_moment (h.jump φ.g φ.contDiff φ.compactSupport) φ.pv

/-- **The Gardiner bridge as a morphism of presentations**: from the
strong-generator presentation of the kernel semigroup to the dCKE
presentation. -/
def hom (h : GardinerKernel S k A B W) :
    SemigroupSys.strongGenerator.obj (⟨Sp n, S⟩ : SemigroupSys.{0}) ⟶ dckePres A B W where
  map := fun y => y
  pull := fun φ => ⟨(φ.g, fun y => bwdGen A B φ.g y + φ.pvJump y), h.hasStrongGenerator φ⟩
  ev_pull := fun _ _ => rfl
  gen_pull := fun _ _ => rfl

/-- **Gardiner's kernel object from Ullah's conditions.**  Ullah's
conditional-moment conditions (8.8)–(8.9) replace Gardiner's conditions
(ii)–(iii); the remaining hypotheses are shared. -/
theorem ofUllah
    (rep : ∀ ds > (0 : ℝ), ∀ (g : Sp n → ℝ) (y : Sp n), S.P ds g y = ∫ z, g z * k ds y z)
    (norm : ∀ ds > (0 : ℝ), ∀ y, ∫ z, k ds y z = 1)
    (nonneg : ∀ ds y z, 0 ≤ k ds y z)
    (integrable : ∀ ds y, Integrable (fun z => k ds y z))
    (hmom1 : ∃ C : ℝ, ∀ ε > 0, ∀ (i : Fin n) (w : Sp n), ∃ L : ℝ,
      Tendsto (fun dt : ℝ => (1 / dt) * Ullah.Mom1 k dt ε w i) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
        |L - A w i| ≤ C * ε)
    (hmom2 : ∃ C : ℝ, ∀ ε > 0, ∀ (i j : Fin n) (w : Sp n), ∃ L : ℝ,
      Tendsto (fun dt : ℝ => (1 / dt) * Ullah.Mom2 k dt ε w i j) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
        |L - B w i j| ≤ C * ε)
    (limit_exists : ∀ g : Sp n → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      ∀ y, ∃ L, Tendsto (bwdQuot k g y) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (second_moment : ∀ y, ∃ (M : ℝ → ℝ) (C : ℝ),
      (∀ ε > 0, Tendsto (fun ds => bQsq k y ds ε) (𝓝[>] (0 : ℝ)) (𝓝 (M ε))) ∧
      ∀ ε > 0, |M ε| ≤ C)
    (jump : ∀ g : Sp n → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      ∀ y, ∀ ε > 0, Tendsto (fun ds => bQjump k g y ds ε) (𝓝[>] (0 : ℝ))
        (𝓝 (bJumpPre W g y ε))) :
    GardinerKernel S k A B W where
  rep := rep
  norm := norm
  nonneg := nonneg
  integrable := integrable
  drift := Ullah.condDrift_iff_mom.mpr hmom1
  diffusion := Ullah.condDiffusion_iff_mom.mpr hmom2
  limit_exists := limit_exists
  second_moment := second_moment
  jump := jump

end GardinerKernel

end Gardiner

namespace Ullah

open Gardiner

variable {n : ℕ}

/-- Ullah's right-hand side of the dCKE (8.13) is exactly Gardiner's (3.4.22). -/
theorem fpTerm_add_jumpTerm (p : ℝ → Sp n → ℝ) (A : Sp n → Fin n → ℝ)
    (B : Sp n → Fin n → Fin n → ℝ) (W : Sp n → Sp n → ℝ) (t : ℝ) (y : Sp n) :
    fpTerm p A B t y + jumpTerm p W t y = ckRHS p A B W t y := rfl

end Ullah
