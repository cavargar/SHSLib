/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semigroup, resolvent and `p`-excessive functions

Formalization of the potential-theoretic ingredients used in the proof of
Proposition 4 (strong Markov property) of

  M.L. Bujorianu and J. Lygeros, "Toward a General Theory of Stochastic Hybrid
  Systems", LNCIS 337, Springer, 2006.

The proof of Proposition 4 uses the characterization of the strong Markov
property through the resolvent

  `U_p g = ∫₀^∞ e^{-pt} P_t g dt`,

and the fact that `U_p g` is a `p`-excessive function of the semigroup, i.e.
`e^{-pt} P_t (U_p g) ≤ U_p g`.  Both the identity

  `e^{-pt} P_t (U_p g) = ∫_t^∞ e^{-ps} P_s g ds`

and the resulting sub-invariance are proved here.
-/
import SHSLib.Bujorianu2006.MarkovString

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Bujorianu2006

/-- A transition semigroup `(P_t)_{t ≥ 0}` acting on functions on `X`
(Section 3.2: `P_t f(x) = E_x f(x_t)`). -/
structure TransitionSemigroup (X : Type*) where
  /-- The operators `P_t`. -/
  P : ℝ → (X → ℝ) → (X → ℝ)
  /-- `P_0 = id`. -/
  P_zero : ∀ g x, P 0 g x = g x
  /-- The semigroup law `P_s ∘ P_t = P_{s+t}`. -/
  P_add : ∀ s t g x, 0 ≤ s → 0 ≤ t → P s (P t g) x = P (s + t) g x
  /-- Positivity. -/
  P_nonneg : ∀ t g x, 0 ≤ t → (∀ y, 0 ≤ g y) → 0 ≤ P t g x
  /-- `P_t` is additive (linearity, first half). -/
  P_sub : ∀ t (g h : X → ℝ), P t (fun y => g y - h y) = fun y => P t g y - P t h y
  /-- `P_t` is homogeneous (linearity, second half). -/
  P_const_mul : ∀ t (c : ℝ) (g : X → ℝ), P t (fun y => c * g y) = fun y => c * P t g y

namespace TransitionSemigroup

variable {X : Type*} (S : TransitionSemigroup X)

/-- The resolvent `U_p g = ∫₀^∞ e^{-pt} P_t g dt` of the semigroup. -/
def resolvent (p : ℝ) (g : X → ℝ) (x : X) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * S.P t g x

variable {S}

/-- Translation of the tail integral: `∫_{s>0} F(s + t) ds = ∫_{u > t} F(u) du`. -/
theorem integral_Ioi_shift (F : ℝ → ℝ) (t : ℝ) :
    (∫ s in Ioi (0 : ℝ), F (s + t)) = ∫ u in Ioi t, F u := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) t).setIntegral_preimage_emb
    (measurableEmbedding_addRight t) F (Ioi t)
  have hpre : (fun s : ℝ => s + t) ⁻¹' (Ioi t) = Ioi (0 : ℝ) := by
    ext s; simp
  rw [hpre] at h
  exact h

/-- **The semigroup acting on the resolvent produces the tail of the resolvent
integral**: `e^{-pt} P_t(U_p g)(x) = ∫_t^∞ e^{-ps} P_s g(x) ds`.

The hypothesis `hcomm` is the interchange of `P_t` with the (Bochner) integral
defining the resolvent. -/
theorem exp_mul_semigroup_resolvent (p t : ℝ) (g : X → ℝ) (x : X) (ht : 0 ≤ t)
    (hcomm : S.P t (fun y => ∫ s in Ioi (0 : ℝ), Real.exp (-(p * s)) * S.P s g y) x
      = ∫ s in Ioi (0 : ℝ), Real.exp (-(p * s)) * S.P t (S.P s g) x) :
    Real.exp (-(p * t)) * S.P t (S.resolvent p g) x
      = ∫ u in Ioi t, Real.exp (-(p * u)) * S.P u g x := by
  have hsemi : ∀ s : ℝ, 0 ≤ s → S.P t (S.P s g) x = S.P (s + t) g x := by
    intro s hs
    rw [S.P_add t s g x ht hs, add_comm t s]
  have hres : S.resolvent p g = fun y => ∫ s in Ioi (0 : ℝ), Real.exp (-(p * s)) * S.P s g y :=
    rfl
  rw [hres, hcomm, ← integral_const_mul]
  have hcongr : (∫ s in Ioi (0 : ℝ), Real.exp (-(p * t)) *
        (Real.exp (-(p * s)) * S.P t (S.P s g) x))
      = ∫ s in Ioi (0 : ℝ), Real.exp (-(p * (s + t))) * S.P (s + t) g x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    rw [hsemi s (le_of_lt hs), ← mul_assoc, ← Real.exp_add]
    congr 3
    ring
  rw [hcongr]
  exact integral_Ioi_shift (fun u => Real.exp (-(p * u)) * S.P u g x) t

/-- **`U_p g` is `p`-excessive** (Section 3.2): for a nonnegative `g`,
`e^{-pt} P_t (U_p g) ≤ U_p g` for all `t ≥ 0`.  This is the property used in
the proof of Proposition 4 to identify the strong Markov property through the
resolvent. -/
theorem resolvent_excessive (p t : ℝ) (g : X → ℝ) (x : X) (ht : 0 ≤ t)
    (hg : ∀ y, 0 ≤ g y)
    (hint : IntegrableOn (fun u => Real.exp (-(p * u)) * S.P u g x) (Ioi (0 : ℝ)))
    (hcomm : S.P t (fun y => ∫ s in Ioi (0 : ℝ), Real.exp (-(p * s)) * S.P s g y) x
      = ∫ s in Ioi (0 : ℝ), Real.exp (-(p * s)) * S.P t (S.P s g) x) :
    Real.exp (-(p * t)) * S.P t (S.resolvent p g) x ≤ S.resolvent p g x := by
  rw [exp_mul_semigroup_resolvent p t g x ht hcomm]
  refine setIntegral_mono_set hint ?_ ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.exp_nonneg _) (S.P_nonneg u g x (le_of_lt hu) hg)
  · filter_upwards with u hu
    exact lt_of_le_of_lt ht hu

/-- The resolvent of a nonnegative function is nonnegative. -/
theorem resolvent_nonneg (p : ℝ) (g : X → ℝ) (x : X) (hg : ∀ y, 0 ≤ g y) :
    0 ≤ S.resolvent p g x := by
  refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
  exact mul_nonneg (Real.exp_nonneg _) (S.P_nonneg u g x (le_of_lt hu) hg)

end TransitionSemigroup

/-! ## Theorem 1(i) implies Proposition 2

The strong Markov property, applied to the constant stopping times, gives back
the simple Markov property (Eq. (14)). -/

namespace ShiftSystem

variable {Ω X : Type*} (M : ShiftSystem Ω X)

/-- The strong Markov property with respect to a family `𝒯` of (nonnegative)
random times: `E^x[f · (g ∘ θ_τ)] = E^x[f · E^{x_τ}[g]]`. -/
def HasStrongMarkovProperty (E : X → (Ω → ℝ) → ℝ) (𝒯 : Set (Ω → ℝ)) : Prop :=
  ∀ τ ∈ 𝒯, (∀ ω, 0 ≤ τ ω) → ∀ (y : X) (f g : Ω → ℝ),
    E y (fun ω => f ω * g (M.θ (τ ω) ω)) = E y (fun ω => f ω * E (M.x (τ ω) ω) g)

variable {M}

/-- **Theorem 1(i) ⟹ Proposition 2**: a strong Markov process is a Markov
process, since the deterministic times are stopping times. -/
theorem hasMarkovProperty_of_strong {E : X → (Ω → ℝ) → ℝ} {𝒯 : Set (Ω → ℝ)}
    (h : M.HasStrongMarkovProperty E 𝒯)
    (hconst : ∀ t : ℝ, 0 ≤ t → (fun _ : Ω => t) ∈ 𝒯) :
    M.HasMarkovProperty E := by
  intro t ht y f g
  exact h (fun _ => t) (hconst t ht) (fun _ => ht) y f g

end ShiftSystem

end Bujorianu2006

end
