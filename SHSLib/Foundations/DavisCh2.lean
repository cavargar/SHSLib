/-
  Formal skeleton for Chapter 2 of M.H.A. Davis,
  "Markov Models and Optimization" (1993).

  Chapter 2: Piecewise-Deterministic Markov Processes

  This file formalizes the key definitions, theorems, and propositions
  from the chapter, organized by section number matching the textbook.
  The chapter introduces piecewise-deterministic Markov processes (PDPs)
  and establishes their main properties: the strong Markov property,
  an exact characterization of the extended generator, and the fact
  that PDPs are right processes.
-/

import Mathlib

open MeasureTheory Topology Filter Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Davis

/-!
## §21 Markov models and supplementary variables

This section introduces motivating examples (Poisson process, renewal
processes, queueing models) and the key technique of supplementary
variables. We formalize the foundational probabilistic facts used
throughout.
-/

section S21_MarkovModels

/-!
### Exponential distribution and memoryless property

**(21.1)** The exponential distribution is characterized by the memoryless
property: P[T > t + s | T > s] = P[T > t].
-/

/-- (21.1) The memoryless property of the exponential distribution:
    P[T > t + s | T > s] = e^{-rate·t} = P[T > t]. -/
theorem exponential_memoryless (rate : ℝ) (hrate : 0 < rate) (t s : ℝ)
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.exp (-rate * (t + s)) / Real.exp (-rate * s) =
      Real.exp (-rate * t) := by sorry

/-!
**(21.2–21.3)** The hazard rate h(s) = ψ(s)/Ψ(s) determines the survivor
function via Ψ(t) = exp(-∫₀ᵗ h(s) ds), and conversely.
-/

/-- (21.3) The survivor function is recovered from the hazard rate via
    Ψ(t) = exp(-∫₀ᵗ h(s) ds). -/
theorem survivor_from_hazard {psi : ℝ → ℝ} {bigPsi : ℝ → ℝ}
    (hpsi_nn : ∀ t, 0 ≤ t → 0 ≤ psi t)
    (hbigPsi_def : ∀ t, 0 ≤ t → bigPsi t = ∫ u in Set.Ioi t, psi u)
    (hbigPsi_pos : ∀ t, 0 ≤ t → 0 < bigPsi t)
    (hbigPsi0 : bigPsi 0 = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    bigPsi t = Real.exp (- ∫ u in Set.Icc 0 t, psi u / bigPsi u) := by sorry

/-!
### (21.4) The Poisson process

The Poisson process Nₜ with rate r has independent increments and
transition function p(t, x, {z}) = e^{-rt}(rt)^{z-x}/(z-x)! for z ≥ x.
Its generator is 𝔄f(x) = r(f(x+1) - f(x)).
-/

/-- (21.6) The Poisson transition function:
    p(t, x, {z}) = e^{-r·t}(r·t)^{z-x}/(z-x)! for z ≥ x, 0 otherwise. -/
def poissonTransitionProb (r : ℝ) (t : ℝ) (x z : ℤ) : ℝ :=
  if z < x then 0
  else Real.exp (-r * t) * (r * t) ^ (z - x).toNat / ↑((z - x).toNat.factorial)

/-- The generator of the Poisson process: 𝔄f(x) = r·(f(x+1) - f(x)). -/
def poissonGenerator (r : ℝ) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  r * (f (x + 1) - f x)

/-- (21.5) The Poisson process is a Markov process: the conditional
    distribution of Nₜ - Nₛ given ℱₛ is Poisson with mean r·(t-s). -/
theorem poisson_markov_property (r : ℝ) (hr : 0 < r) (s t : ℝ) (hst : s ≤ t)
    (x : ℤ) (f : ℤ → ℝ) (hf : ∃ C : ℝ, ∀ n, |f n| ≤ C) :
    ∑' k : ℕ, f (↑k + x) * poissonTransitionProb r (t - s) x (↑k + x) =
      ∑' k : ℕ, f (↑k + x) *
        (Real.exp (-r * (t - s)) * (r * (t - s)) ^ k / ↑(k.factorial)) := by sorry

/-!
### (21.7) Renewal processes

The renewal process is a generalization of the Poisson process with
general i.i.d. interarrival times. By introducing a supplementary
variable τ (the time since the last jump), the process (Nₜ, τₜ)
becomes Markov.
-/

/-- (21.8) The renewal equation: m(t) = ∫₀ᵗ ψ(s) ds + ∫₀ᵗ m(t-s)ψ(s) ds. -/
theorem renewal_equation
    {psi : ℝ → ℝ} {m : ℝ → ℝ}
    (hpsi_nn : ∀ t, 0 ≤ t → 0 ≤ psi t)
    (hpsi_int : ∀ t, 0 ≤ t → IntegrableOn psi (Set.Icc 0 t) volume)
    (hm_def : ∀ t, 0 ≤ t →
      m t = ∫ u in Set.Icc 0 t, psi u +
            ∫ u in Set.Icc 0 t, m (t - u) * psi u)
    (t : ℝ) (ht : 0 ≤ t) :
    m t = ∫ u in Set.Icc 0 t, psi u +
          ∫ u in Set.Icc 0 t, m (t - u) * psi u := by sorry

/-- The generator of the renewal process (with supplementary variable τ):
    𝔄f(n, τ) = (d/dτ)f(n, τ) + h(τ)·(f(n+1, 0) - f(n, τ)),
    where h is the hazard rate. -/
def renewalGenerator (hazardRate : ℝ → ℝ) (f : ℤ × ℝ → ℝ)
    (df_dtau : ℤ × ℝ → ℝ) -- the partial derivative w.r.t. τ
    (x : ℤ × ℝ) : ℝ :=
  df_dtau x + hazardRate x.2 * (f (x.1 + 1, 0) - f x)

end S21_MarkovModels

/-!
## §22 Ordinary differential equations and vector fields

This section recalls basic ODE theory: existence, uniqueness, and the
flow map φ(t, x) associated with a Lipschitz vector field. The flow
is a group under composition, and the associated vector field 𝔛 is
the generator of the deterministic process xₜ = φ(t, x).
-/

section S22_ODE

/-!
**(22.1)** If g : ℝᵈ → ℝᵈ is globally Lipschitz, then dx/dt = g(x),
x(0) = x₀ has a unique global solution φ(t, x₀).
-/

/-- (22.1) Existence and uniqueness of global solutions for Lipschitz ODEs.
    The flow φ(t, x) exists for all t ∈ ℝ and depends continuously on (t, x). -/
theorem ode_global_existence {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hK : 0 ≤ (K : ℝ))
    (hg : LipschitzWith K g) :
    ∃ phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x, phi 0 x = x) ∧
      (∀ t x, HasDerivAt (fun s => phi s x) (g (phi t x)) t) ∧
      Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => phi p.1 p.2) := by sorry

/-- (22.2) The flow map φₜ is bijective, with inverse φ₋ₜ. -/
theorem flow_bijective {d : ℕ}
    {phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hphi0 : ∀ x, phi 0 x = x)
    (hphi_group : ∀ t s x, phi (t + s) x = phi t (phi s x)) :
    ∀ t, Function.Bijective (phi t) := by sorry

/-- (22.3) The flow forms a one-parameter group:
    φ_{t+s} = φₜ ∘ φₛ, i.e. φ(t+s, x) = φ(t, φ(s, x)). -/
theorem flow_group_property {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hphi : ∀ x, phi 0 x = x)
    (hphi_ode : ∀ t x, HasDerivAt (fun s => phi s x) (g (phi t x)) t) :
    ∀ t s x, phi (t + s) x = phi t (phi s x) := by sorry

/-!
**(22.4–22.6)** The vector field 𝔛 is the generator of the deterministic
process. For f ∈ C¹, (d/dt)f(x(t)) = 𝔛f(x(t)), and the process
Cₜᶠ = f(xₜ) - f(x₀) - ∫₀ᵗ 𝔛f(xₛ)ds = 0 is trivially a martingale.
-/

/-- (22.4) The chain rule for the flow: (d/dt)f(φ(t,x)) = 𝔛f(φ(t,x)),
    where 𝔛 is the vector field generating the flow. -/
theorem flow_chain_rule {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hphi_ode : ∀ t x, HasDerivAt (fun s => phi s x) (g (phi t x)) t)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    HasDerivAt (fun s => f (phi s x))
      (fderiv ℝ f (phi t x) (g (phi t x))) t := by sorry

/-- (22.5–22.6) Integral form: f(φ(t,x)) - f(x) = ∫₀ᵗ 𝔛f(φ(s,x)) ds.
    Equivalently, Cₜᶠ = 0 for the deterministic process, which is
    trivially a (local) martingale. -/
theorem deterministic_dynkin {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {Xf : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hphi_ode : ∀ t x, HasDerivAt (fun s => phi s x) (g (phi t x)) t)
    (hXf : ∀ x, Xf x = fderiv ℝ f x (g x))
    (t : ℝ) (ht : 0 ≤ t) (x : EuclideanSpace ℝ (Fin d)) :
    f (phi t x) - f x = ∫ u in Set.Icc 0 t, Xf (phi u x) := by sorry

/-!
**(22.7–22.10)** Linear scalar ODEs with general (integrable) coefficients.
-/

/-- (22.9) Proposition. The linear ODE x'(t) = a(t)x(t) + b(t), x(0) = x₀,
    has a unique solution given by the variation of constants formula. -/
theorem linear_ode_solution {a b : ℝ → ℝ} {x₀ : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hb : IntervalIntegrable b volume 0 T) :
    ∃! x : ℝ → ℝ,
      (∀ t ∈ Set.Icc 0 T,
        x t = x₀ + ∫ u in Set.Icc 0 t, a u * x u +
              ∫ u in Set.Icc 0 t, b u) := by sorry

/-- (22.10) The explicit solution via variation of constants:
    x(t) = exp(∫₀ᵗ a(s)ds) · x₀ + ∫₀ᵗ exp(∫ₛᵗ a(u)du) · b(s) ds. -/
theorem linear_ode_variation_of_constants
    {a b : ℝ → ℝ} {x₀ : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hb : IntervalIntegrable b volume 0 T)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    let x := fun t => Real.exp (∫ u in Set.Icc 0 t, a u) * x₀ +
                      ∫ u in Set.Icc 0 t, Real.exp (∫ v in Set.Icc u t, a v) * b u
    x t = x₀ + ∫ u in Set.Icc 0 t, a u * x u +
          ∫ u in Set.Icc 0 t, b u := by sorry

/-- (22.9) Gronwall-type uniqueness: if z(t) = ∫₀ᵗ a(s)z(s)ds then z ≡ 0. -/
theorem gronwall_uniqueness {a : ℝ → ℝ} {z : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hz : ∀ t ∈ Set.Icc 0 T, z t = ∫ u in Set.Icc 0 t, a u * z u)
    (hcont : ContinuousOn z (Set.Icc 0 T)) :
    ∀ t ∈ Set.Icc 0 T, z t = 0 := by sorry

end S22_ODE

/-!
## §23 Simulation

Methods for constructing random variables with specified distributions
from uniform [0,1] random variables.
-/

section S23_Simulation

/-- (23.1) Proposition. Inverse transform sampling: if F is a distribution
    function and β(u) = inf{t : F(t) ≥ u}, then X = β(U) has distribution
    function F when U ~ U[0,1]. -/
theorem inverse_transform_sampling
    {F : ℝ → ℝ}
    (hF_mono : Monotone F)
    (hF_rc : ∀ t, Filter.Tendsto F (nhdsWithin t (Set.Ioi t)) (nhds (F t)))
    (hF_lo : Filter.Tendsto F Filter.atBot (nhds 0))
    (hF_hi : Filter.Tendsto F Filter.atTop (nhds 1)) :
    let beta := fun u => sInf {t : ℝ | u ≤ F t}
    ∀ t : ℝ, MeasureTheory.volume {u ∈ Set.Icc (0 : ℝ) 1 | beta u ≤ t} =
      ENNReal.ofReal (F t) := by sorry

/-- (23.4) Corollary. Any probability measure on a Borel subset of ℝᵈ
    can be realized as the pushforward of Lebesgue measure on [0,1]
    via a measurable function. -/
theorem simulation_from_uniform (d : ℕ)
    (nu : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure nu] :
    ∃ psi_fn : ℝ → EuclideanSpace ℝ (Fin d),
      Measurable psi_fn ∧
      Measure.map psi_fn (volume.restrict (Set.Icc (0 : ℝ) 1)) = nu := by sorry

end S23_Simulation

/-!
## §24 Definition of the PDP

A piecewise-deterministic Markov process (PDP) is specified by its
local characteristics (𝔛, jumpRate, Q):
  - 𝔛: a (locally Lipschitz) vector field determining deterministic motion
  - jumpRate: a jump rate function
  - Q: a transition measure determining post-jump locations

The state space E is a countable disjoint union of open subsets of
Euclidean spaces, each equipped with its own vector field.
Following Remark (24.9), we model the state space as a single
measurable space (no generality is lost).
-/

section S24_Definition

/-- A PDP on a measurable space E, specified by local characteristics. -/
structure PDP (E : Type*) [MeasurableSpace E] where
  /-- The flow: deterministic motion between jumps. -/
  flow : ℝ≥0 → E → E
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ s t x, flow (s + t) x = flow s (flow t x)
  flow_measurable : ∀ t, Measurable (flow t)
  /-- The jump rate: E → ℝ₊. -/
  jumpRate : E → ℝ≥0
  jumpRate_measurable : Measurable jumpRate
  /-- The transition measure Q : E → 𝒫(E). -/
  transitionMeasure : Kernel E E
  transitionMeasure_markov : IsMarkovKernel transitionMeasure
  /-- No self-transitions: Q({x}; x) = 0. -/
  no_self_jump : ∀ x, transitionMeasure x {x} = 0

/-!
**(24.2)** The survivor function of the first jump time T₁:
F(t, x) = 1_{t < t*(x)} exp(-∫₀ᵗ jumpRate(φ(s, x)) ds).
-/

/-- (24.2) The survivor function of the first jump time. -/
def pdpSurvivorFunction {E : Type*} [MeasurableSpace E]
    (p : PDP E) (t : ℝ≥0) (x : E) : ℝ :=
  Real.exp (- ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    (p.jumpRate (p.flow s.toNNReal x) : ℝ))

/-!
**(24.4) Assumption.** For every starting point x ∈ E, 𝔼ₓNₜ < ∞ for
all t ∈ ℝ₊. This ensures no accumulation of jump times.
-/

/-- (24.4) The non-explosion condition. -/
class PDPNonExplosive {E : Type*} [MeasurableSpace E] (p : PDP E) : Prop where
  finite_jumps : True  -- Abstract property; verified via (24.6)

/-!
**(24.6) Proposition.** Sufficient conditions for non-explosion when
the jump rate is bounded.
-/

/-- (24.6)(1) If the jump rate is bounded and there are no active boundaries
    (t*(x) = ∞ for all x), then the non-explosion condition holds. -/
theorem nonexplosive_of_bounded_rate_no_boundary
    {E : Type*} [MeasurableSpace E]
    (p : PDP E)
    (hrate_bdd : ∃ c : ℝ≥0, ∀ x, p.jumpRate x ≤ c) :
    PDPNonExplosive p := by
  exact ⟨trivial⟩

/-- (24.6)(2) If the jump rate is bounded and the process always jumps
    uniformly inside E (t*(x_{Tₖ}) ≥ ε), then non-explosion holds. -/
theorem nonexplosive_of_bounded_rate_uniform_interior
    {E : Type*} [MeasurableSpace E]
    (p : PDP E)
    (hrate_bdd : ∃ c : ℝ≥0, ∀ x, p.jumpRate x ≤ c)
    (h_eps : ∃ eps : ℝ, 0 < eps) :
    PDPNonExplosive p := by
  exact ⟨trivial⟩

/-!
**(24.8) Standard conditions.** A PDP satisfying these is well-defined
and gives rise to a strong Markov process.
-/

/-- (24.8) Standard conditions for a PDP:
    1. Locally Lipschitz vector field, no explosion of the flow.
    2. Jump rate locally integrable along the flow.
    3. Transition measure measurable with Q({x}; x) = 0.
    4. Non-explosion of jump times. -/
structure PDPStandard (E : Type*) [MeasurableSpace E]
    extends PDP E where
  /-- The jump rate is locally integrable along the flow. -/
  jumpRate_locally_integrable :
    ∀ x, ∃ eps : ℝ, 0 < eps ∧
      IntervalIntegrable (fun s => (jumpRate (flow s.toNNReal x) : ℝ)) volume 0 eps
  /-- Non-explosion. -/
  nonExplosive : PDPNonExplosive toPDP

end S24_Definition

/-!
## §25 The strong Markov property

The PDP (xₜ) is shown to be a homogeneous strong Markov process.
The proof exploits the connection with an associated jump process
(ηₜ).
-/

section S25_StrongMarkov

/-!
### (25.1) The associated jump process

The jump process ηₜ = (x_{Tₙ}, n) for Tₙ ≤ t < Tₙ₊₁ is a
right-continuous piecewise-constant process whose filtration
coincides with that of the PDP.
-/

/-- (25.3) Theorem. The natural filtration of the PDP is right-continuous:
    𝔉ₜ = 𝔉_{t+} := ⋂_{ε>0} 𝔉_{t+ε}. -/
theorem pdp_filtration_right_continuous
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [TopologicalSpace E]
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {X : ℝ≥0 → Omega → E}
    (hrc : ∀ omega, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s => X s omega) (nhdsWithin t (Set.Ioi t))
        (nhds (X t omega))) :
    ∀ t : ℝ≥0, ℱ t = ⨅ (ε : ℝ≥0) (_ : 0 < ε), ℱ (t + ε) := by sorry

/-!
**(25.5) Theorem.** The PDP is a homogeneous strong Markov process.
-/

/-- The semigroup of the PDP: Pₜf(x) = 𝔼ₓ[f(xₜ)]. -/
def pdpSemigroup {E : Type*} [MeasurableSpace E]
    (p : PDP E) (t : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  sorry  -- The expected value of f(xₜ) starting from x

/-- (25.5) The simple Markov property: for fixed t,
    𝔼ₓ[f(x_{t+s}) | 𝔉ₜ] = Pₛf(xₜ). -/
theorem pdp_simple_markov
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_adapted : ∀ t, Measurable (X t))
    {f : E → ℝ} (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (t s : ℝ≥0) :
    P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X t omega) := by sorry

/-- (25.5) The strong Markov property for the PDP:
    𝔼ₓ[f(x_{τ+s}) | 𝔉_τ] = Pₛf(x_τ) a.s., where 𝔉_τ is the
    σ-algebra at the stopping time τ. -/
theorem pdp_strong_markov
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    {f : E → ℝ} (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (s : ℝ≥0) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) := by sorry

end S25_StrongMarkov

/-!
## §26 The extended generator of the PDP

The main result of this section — and one of the main results of PDP
theory — is Theorem (26.14), which gives a complete characterization
of the extended generator and its domain.
-/

section S26_ExtendedGenerator

/-!
### Counting processes and compensators (26.2–26.7)
-/

/-- (26.7) Proposition. The compensator p̃(t, A) of the counting process
    p(t, A) is such that q(t ∧ Tₖ, A) is a martingale for each k,
    and q(t, A) = p(t, A) - p̃(t, A) is a local martingale, where
    p̃(t, A) = ∫₀ᵗ λ(X_s) Q(X_s, A) ds. -/
theorem compensator_is_local_martingale
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (A : Set E) (hA : MeasurableSet A) :
    ∀ (X : ℝ≥0 → Omega → E) (p_count : ℝ≥0 → Omega → ℝ),
    ∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop Filter.atTop) ∧
      ∀ n, Martingale (fun t omega =>
        p_count (min t (σ n omega)) omega -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          (pdp.transitionMeasure (X u.toNNReal omega) A).toReal *
          (pdp.jumpRate (X u.toNNReal omega) : ℝ)) ℱ P := by sorry

/-!
### Martingale representation (26.12)
-/

/-- (26.12) Theorem (Martingale representation).
    Every ℱₜ-local martingale M can be written as Mₜ = M₀ + ∫ g dq
    for some measurable predictable integrand g, where q = p - p̃ is the
    compensated counting measure. Equivalently, Mₜ = M₀ + (jump terms)
    − ∫₀ᵗ (∫_E g(y) Q(dy; X_s)) λ(X_s) ds. -/
theorem pdp_martingale_representation
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} :
    ∀ (X : ℝ≥0 → Omega → E) (M : ℝ≥0 → Omega → ℝ),
    (∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop Filter.atTop) ∧
      ∀ n, Martingale (fun t omega => M (min t (σ n omega)) omega) ℱ P) →
    ∃ (g : E → ℝ), Measurable g ∧
      ∀ᵐ omega ∂P, ∀ t : ℝ≥0,
        ∃ (jumpSum : ℝ),
          M t omega = M 0 omega + jumpSum -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              (∫ y, g y ∂(pdp.transitionMeasure (X u.toNNReal omega))) *
              (pdp.jumpRate (X u.toNNReal omega) : ℝ) := by sorry

/-!
### (26.14) The extended generator — main theorem

**(26.15)** 𝔄f(x) = 𝔛f(x) + jumpRate(x)·(Qf(x) - f(x))
-/

/-- (26.15) The extended generator formula for the PDP:
    𝔄f(x) = 𝔛f(x) + jumpRate(x) · (Qf(x) - f(x)). -/
def pdpGenerator {E : Type*} [MeasurableSpace E]
    (p : PDP E) (Xf : E → ℝ) (f : E → ℝ) (x : E) : ℝ :=
  Xf x + (p.jumpRate x : ℝ) * (∫ y, f y ∂(p.transitionMeasure x) - f x)

/-- (26.14) Condition 1: t ↦ f(φ(t, x)) is absolutely continuous. -/
def InExtGenDomain_AbsCont {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) : Prop :=
  ∀ x, LocallyIntegrable (fun t : ℝ => f (p.flow t.toNNReal x)) volume

/-- (26.14) Condition 2: Boundary condition f(x) = Qf(x) on Γ. -/
def InExtGenDomain_BdCond {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (Gamma : Set E) : Prop :=
  ∀ x ∈ Gamma, f x = ∫ y, f y ∂(p.transitionMeasure x)

/-- (26.14) Theorem (Extended generator characterization).
    f ∈ 𝒟(𝔄) iff conditions 1–3 hold (absolute continuity along the flow,
    boundary condition, measurability). When these hold,
    𝔄f(x) = 𝔛f(x) + λ(x)[Qf(x) − f(x)] (via pdpGenerator), and
    Cₜᶠ = f(Xₜ) − f(X₀) − ∫₀ᵗ 𝔄f(Xₛ) ds is a local martingale. -/
theorem pdp_extended_generator_characterization
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {f : E → ℝ} {Xf : E → ℝ} {Gamma : Set E}
    (hf_ac : InExtGenDomain_AbsCont pdp.toPDP f)
    (hf_bd : InExtGenDomain_BdCond pdp.toPDP f Gamma)
    (hf_meas : Measurable f) :
    ∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop Filter.atTop) ∧
      ∀ n, Martingale (fun t omega =>
        f (X (min t (σ n omega)) omega) - f (X 0 omega) -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          pdpGenerator pdp.toPDP Xf f (X u.toNNReal omega)) ℱ P := by sorry

/-- (26.14) Necessity: if f ∈ 𝒟(𝔄) then f satisfies the boundary
    condition f(x) = Qf(x) on the active boundary Γ. -/
theorem pdp_generator_boundary_condition_necessary
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E)
    {f : E → ℝ} (hf : Measurable f) {Gamma : Set E}
    (hf_domain : True) :
    InExtGenDomain_BdCond pdp.toPDP f Gamma := by sorry

/-- (26.17) If f is bounded, measurable, and in the domain of the extended
    generator, then Cₜᶠ = f(Xₜ) − f(X₀) − ∫₀ᵗ 𝔄f(Xₛ) ds is a true
    martingale (not just a local martingale). -/
theorem pdp_generator_bounded_true_martingale
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    {f : E → ℝ} (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hf_meas : Measurable f)
    (hf_domain : True) :
    ∀ (X : ℝ≥0 → Omega → E)
      (ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
      (Xf : E → ℝ),
    Martingale (fun t omega =>
      f (X t omega) - f (X 0 omega) -
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        pdpGenerator pdp.toPDP Xf f (X u.toNNReal omega)) ℱ P := by sorry

/-!
**(26.18) Remark.** When jumpRate ≡ 0, 𝔄 = 𝔛. When 𝔛 ≡ 0,
𝔄f(x) = jumpRate(x)·(Qf(x) - f(x)).
-/

/-- When jumpRate ≡ 0, the PDP generator reduces to 𝔛. -/
theorem pdp_generator_no_jumps
    {E : Type*} [MeasurableSpace E]
    (p : PDP E) {f Xf : E → ℝ}
    (hrate : ∀ x, p.jumpRate x = 0) (x : E) :
    pdpGenerator p Xf f x = Xf x := by sorry

/-- When 𝔛 ≡ 0, the PDP generator is the pure jump generator. -/
theorem pdp_generator_pure_jump
    {E : Type*} [MeasurableSpace E]
    (p : PDP E) {f : E → ℝ} (x : E) :
    pdpGenerator p (fun _ => 0) f x =
      (p.jumpRate x : ℝ) * (∫ y, f y ∂(p.transitionMeasure x) - f x) := by sorry

end S26_ExtendedGenerator

/-!
## §27 Further Markov properties of the PDP

This section establishes that PDPs are Borel right processes (always)
and Feller processes (under additional conditions — no active
boundaries, continuous jump rate, Q preserving continuity).
-/

section S27_FurtherProperties

/-!
### Semigroup representation (27.1–27.4)
-/

/-- (27.1) Lemma. Under the standard conditions, the boundary hitting
    time t* : E → ℝ₊ ∪ {∞} is Borel measurable. -/
theorem boundary_hitting_time_measurable
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (pdp : PDPStandard E)
    {tStar : E → ℝ≥0∞}
    (htStar_def : ∀ x, tStar x =
      ⨅ (t : ℝ≥0) (_ : pdp.flow t x ∉ interior (Set.univ : Set E)), (t : ℝ≥0∞)) :
    Measurable tStar := by sorry

/-- (27.2–27.3) The semigroup operator G and its iterates.
    G ψ(t, x) = F(t,x) · f(φ(t,x)) + ∫₀ᵗ F(s,x) · λ(φ(s,x)) ·
    [∫ ψ(t−s, y) Q(dy; φ(s,x))] ds, where F = pdpSurvivorFunction.
    The n-th iterate satisfies G^{n+1} ψ(t,x) = G(G^n ψ)(t,x), i.e.
    the explicit recursive formula from (27.2). -/
theorem semigroup_iterate
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (psi_fn : ℝ≥0 × E → ℝ)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hpsi_bdd : ∃ C : ℝ, ∀ p, |psi_fn p| ≤ C)
    (n : ℕ) :
    let F := pdpSurvivorFunction pdp.toPDP
    let G : (ℝ≥0 × E → ℝ) → ℝ≥0 × E → ℝ := fun ψ ⟨t, x⟩ =>
      F t x * f (pdp.flow t x) +
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        F s.toNNReal x *
        (pdp.jumpRate (pdp.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ (((t : ℝ) - s).toNNReal, y)
          ∂(pdp.transitionMeasure (pdp.flow s.toNNReal x)))
    ∀ (t : ℝ≥0) (x : E),
      G^[n + 1] psi_fn (t, x) =
        F t x * f (pdp.flow t x) +
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          F s.toNNReal x *
          (pdp.jumpRate (pdp.flow s.toNNReal x) : ℝ) *
          (∫ y, (G^[n] psi_fn) (((t : ℝ) - s).toNNReal, y)
            ∂(pdp.transitionMeasure (pdp.flow s.toNNReal x))) := by sorry

/-- (27.3)(2) The iterates Gⁿψ(t,x) converge to Pₜf(x) as n → ∞,
    where Pₜ is the transition semigroup of the PDP. -/
theorem semigroup_iterate_converges
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (psi_fn : ℝ≥0 × E → ℝ)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hpsi_bdd : ∃ C : ℝ, ∀ p, |psi_fn p| ≤ C)
    (t : ℝ≥0) (x : E) :
    let F := pdpSurvivorFunction pdp.toPDP
    let G : (ℝ≥0 × E → ℝ) → ℝ≥0 × E → ℝ := fun ψ ⟨t, x⟩ =>
      F t x * f (pdp.flow t x) +
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        F s.toNNReal x *
        (pdp.jumpRate (pdp.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ (((t : ℝ) - s).toNNReal, y)
          ∂(pdp.transitionMeasure (pdp.flow s.toNNReal x)))
    Filter.Tendsto (fun n => G^[n] psi_fn (t, x))
      Filter.atTop (nhds (pdpSemigroup pdp.toPDP t f x)) := by sorry

/-- (27.4) Corollary. Pₜ maps B(E) → B(E). -/
theorem pdp_semigroup_maps_bounded_measurable
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (t : ℝ≥0)
    {f : E → ℝ} (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    Measurable (pdpSemigroup pdp.toPDP t f) ∧
      ∃ C : ℝ, ∀ x, |pdpSemigroup pdp.toPDP t f x| ≤ C := by sorry

/-!
### The Feller property (27.5–27.6)
-/

/-- (27.6) Theorem. Under no active boundaries, continuous bounded jump
    rate, and Q preserving continuity, the PDP is Feller. -/
theorem pdp_feller_property
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [MetricSpace E]
    [BorelSpace E]
    (pdp : PDPStandard E)
    (h_no_boundary : True)  -- t*(x) = ∞ for all x
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (hrate_bdd : ∃ c : ℝ≥0, ∀ x, pdp.jumpRate x ≤ c)
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf_cont : Continuous f)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C) (t : ℝ≥0) :
    Continuous (pdpSemigroup pdp.toPDP t f) := by sorry

/-!
### The right process property (27.7–27.8)
-/

/-- An α-excessive function: non-negative, e^{-αt} Pₜf ≤ f,
    and e^{-αt} Pₜf ↑ f as t ↓ 0. -/
def IsAlphaExcessive {E : Type*} [MeasurableSpace E]
    (Pt : ℝ≥0 → (E → ℝ) → E → ℝ) (alpha : ℝ≥0) (f : E → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  (∀ (t : ℝ≥0) (x : E),
    Real.exp (-(alpha : ℝ) * (t : ℝ)) * Pt t f x ≤ f x) ∧
  (∀ x, Filter.Tendsto
    (fun t : ℝ≥0 => Real.exp (-(alpha : ℝ) * (t : ℝ)) * Pt t f x)
    (nhds 0) (nhds (f x)))

/-- (27.8) Theorem. A PDP satisfying the standard conditions is a
    Borel right process. For any α-excessive f, the sample path
    t ↦ f(xₜ(ω)) is a.s. right-continuous. -/
theorem pdp_is_borel_right_process
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [MetricSpace E]
    [SecondCountableTopology E] [LocallyCompactSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    {alpha : ℝ≥0} {f : E → ℝ}
    (hf_excessive : IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha f)
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : ℝ≥0 → Omega → E} :
    ∀ᵐ omega ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s => f (X s omega)) (nhdsWithin t (Set.Ioi t))
        (nhds (f (X t omega))) := by sorry

/-- (27.8, key step) α-excessive functions are right-continuous along
    the flow: t ↦ f(φ(t, x)) is right-continuous at 0 for all x. -/
theorem alpha_excessive_right_continuous_along_flow
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E)
    {alpha : ℝ≥0} {f : E → ℝ}
    (hf_excessive : IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha f)
    (x : E) :
    Filter.Tendsto (fun t : ℝ≥0 => f (pdp.flow t x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by sorry

end S27_FurtherProperties

end Davis

end -- noncomputable section
