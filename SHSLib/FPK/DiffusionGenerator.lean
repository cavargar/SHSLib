/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eq. (4) and Eq. (16) of Bect (2010): the differential generator and the probability
current

Between its jumps the hybrid state of a GSHS follows the Itô equation (2), whose
differential generator is the second-order operator (4)

  `L = Σ_i f₀ⁱ ∂/∂zⁱ + ½ Σ_{i,j} aⁱʲ ∂²/∂zⁱ∂zʲ`,      `aⁱʲ = Σ_l f_lⁱ f_lʲ`,

and the "physical" reading of the Fokker–Planck equation of Section 4.2 rests on the
probability current (16)

  `jⁱ = f₀ⁱ p − ½ Σ_j ∂(aⁱʲ p)/∂zʲ`.

This file names these two objects — `GSHS.generatorL` and `GSHS.probabilityCurrent` —
on top of the partial-derivative calculus of `SHSLib.FPK.ProbabilityCurrent`, and
records their basic properties:

* `GSHS.generatorL_add`, `GSHS.generatorL_smul`, `GSHS.generatorL_of_const` — `L` is
  linear in the test function and kills the constants;
* `GSHS.generatorL_mul_density_eq` — **Eq. (44)** written with `L`;
* `GSHS.conservation_equation` — the statement of Section 4.2: for a smooth density,
  the Fokker–Planck equation `∂p/∂t = F p` is the conservation equation
  `∂p/∂t + div(j) = 0` for the probability current.
-/
import SHSLib.FPK.ProbabilityCurrent

open MeasureTheory Set Finset

noncomputable section

namespace GSHS

variable {n r : ℕ}

/-! ### Eq. (4): the differential generator of the diffusion -/

/-- **Eq. (4)**: the value at `x` of the differential generator

  `Lφ = Σ_i f₀ⁱ ∂φ/∂zⁱ + ½ Σ_{i,j} aⁱʲ ∂²φ/∂zⁱ∂zʲ`

of the Itô equation (2), where `gphi i = ∂φ/∂zⁱ(x)` and `ddphi i j = ∂²φ/∂zⁱ∂zʲ(x)`. -/
def generatorL (f0 : (Fin n → ℝ) → Fin n → ℝ) (f : Fin r → (Fin n → ℝ) → Fin n → ℝ)
    (gphi : Fin n → ℝ) (ddphi : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, f0 x i * gphi i + 2⁻¹ * ∑ i, ∑ j, diffusionMatrix f x i j * ddphi i j

variable {f0 : (Fin n → ℝ) → Fin n → ℝ} {f : Fin r → (Fin n → ℝ) → Fin n → ℝ}
  {x : Fin n → ℝ}

/-- The generator is additive in the test function. -/
theorem generatorL_add (g₁ g₂ : Fin n → ℝ) (d₁ d₂ : Fin n → Fin n → ℝ) :
    generatorL f0 f (fun i => g₁ i + g₂ i) (fun i j => d₁ i j + d₂ i j) x
      = generatorL f0 f g₁ d₁ x + generatorL f0 f g₂ d₂ x := by
  simp only [generatorL]
  have h1 : ∑ i, f0 x i * (g₁ i + g₂ i) = (∑ i, f0 x i * g₁ i) + ∑ i, f0 x i * g₂ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, ∑ j, diffusionMatrix f x i j * (d₁ i j + d₂ i j)
      = (∑ i, ∑ j, diffusionMatrix f x i j * d₁ i j)
        + ∑ i, ∑ j, diffusionMatrix f x i j * d₂ i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]
  ring

/-- The generator is homogeneous in the test function. -/
theorem generatorL_smul (c : ℝ) (g : Fin n → ℝ) (d : Fin n → Fin n → ℝ) :
    generatorL f0 f (fun i => c * g i) (fun i j => c * d i j) x
      = c * generatorL f0 f g d x := by
  simp only [generatorL]
  have h1 : ∑ i, f0 x i * (c * g i) = c * ∑ i, f0 x i * g i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, ∑ j, diffusionMatrix f x i j * (c * d i j)
      = c * ∑ i, ∑ j, diffusionMatrix f x i j * d i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]
  ring

/-- The generator kills the constants: a test function with vanishing first and second
derivatives at `x` has `Lφ(x) = 0`. -/
theorem generatorL_of_const : generatorL f0 f (fun _ => 0) (fun _ _ => 0) x = 0 := by
  simp [generatorL]

/-! ### Eq. (16): the probability current -/

/-- **Eq. (16)**: the probability current `jⁱ = f₀ⁱ p − ½ Σ_j ∂(aⁱʲ p)/∂zʲ`, where
`gapf y i j = ∂(aⁱʲ p)/∂zʲ (y)`. -/
def probabilityCurrent (f0 : (Fin n → ℝ) → Fin n → ℝ) (p : (Fin n → ℝ) → ℝ)
    (gapf : (Fin n → ℝ) → Fin n → Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  f0 y i * p y - 2⁻¹ * ∑ j, gapf y i j

theorem probabilityCurrent_apply (p : (Fin n → ℝ) → ℝ)
    (gapf : (Fin n → ℝ) → Fin n → Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    probabilityCurrent f0 p gapf y i = f0 y i * p y - 2⁻¹ * ∑ j, gapf y i j := rfl

/-! ### Eq. (44) in terms of `L` -/

/-- **Eq. (44)** (Appendix C.1) written with the generator (4): with the probability
current `j` of Eq. (16),

  `(Lφ) p = j·∇φ + ½ Σ_l div((f_lφ) p f_l)`. -/
theorem generatorL_mul_density_eq {p : (Fin n → ℝ) → ℝ} {df : Fin r → Fin n → Fin n → ℝ}
    {dp : Fin n → ℝ} {gphi : (Fin n → ℝ) → Fin n → ℝ} {ddphi : Fin n → Fin n → ℝ}
    {Jx : Fin n → ℝ}
    (hJx : ∀ i, Jx i = f0 x i * p x
      - 2⁻¹ * ∑ j, ((∑ l, (df l i j * f l x j + f l x i * df l j j)) * p x
          + diffusionMatrix f x i j * dp j)) :
    generatorL f0 f (gphi x) ddphi x * p x
      = (∑ i, Jx i * gphi x i)
        + 2⁻¹ * ∑ l, ∑ j, ((∑ i, (df l i j * gphi x i + f l x i * ddphi i j))
            * (p x * f l x j)
          + (∑ i, f l x i * gphi x i) * (dp j * f l x j + p x * df l j j)) := by
  simpa [generatorL] using
    generator_mul_density_eq (f := f) (p := p) (x := x) (df := df) (dp := dp)
      (f0 := f0) (gphi := gphi) (ddphi := ddphi) (Jx := Jx) hJx

/-! ### Section 4.2: the FPK equation as a conservation equation -/

/-- **Section 4.2**: for a smooth probability density, the Fokker–Planck equation
`∂p/∂t = F p` is exactly the conservation equation

  `∂p/∂t + div(j) = 0`

for the probability current `j` of Eq. (16).  Here `dpdt` is `∂p/∂t(x)`, `dJ i` is
`∂jⁱ/∂zⁱ(x)`, `dfp i = ∂(f₀ⁱ p)/∂zⁱ(x)` and `ddgap i j = ∂²(aⁱʲ p)/∂zⁱ∂zʲ(x)`. -/
theorem conservation_equation {p : (Fin n → ℝ) → ℝ}
    {gapf : (Fin n → ℝ) → Fin n → Fin n → ℝ} {dfp : Fin n → ℝ} {ddgap : Fin n → Fin n → ℝ}
    {dJ : Fin n → ℝ} {dpdt : ℝ}
    (hfp : ∀ i, HasPDerivAt (fun y => f0 y i * p y) i x (dfp i))
    (hgap : ∀ i j, HasPDerivAt (fun y => gapf y i j) i x (ddgap i j))
    (hdJ : ∀ i, HasPDerivAt (fun y => probabilityCurrent f0 p gapf y i) i x (dJ i)) :
    dpdt = formalAdjointVal dfp ddgap ↔ dpdt + ∑ i, dJ i = 0 := by
  obtain ⟨hJ, hsum⟩ := divergence_current_eq_neg_formalAdjoint
    (Jf := probabilityCurrent f0 p gapf) (gapf := gapf) (f0 := f0) (p := p) (x := x)
    (dfp := dfp) (ddgap := ddgap) (fun y i => rfl) hfp hgap
  have hdJeq : ∀ i, dJ i = dfp i - 2⁻¹ * ∑ j, ddgap i j := fun i => (hdJ i).unique (hJ i)
  have hdiv : ∑ i, dJ i = -formalAdjointVal dfp ddgap := by
    rw [show (∑ i, dJ i) = ∑ i, (dfp i - 2⁻¹ * ∑ j, ddgap i j) from
      Finset.sum_congr rfl fun i _ => hdJeq i]
    exact hsum
  rw [hdiv]
  constructor
  · intro h; rw [h]; ring
  · intro h; linarith

end GSHS
