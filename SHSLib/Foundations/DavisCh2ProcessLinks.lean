import SHSLib.Foundations.DavisCh2

open MeasureTheory MeasurableSpace Topology Filter Set
open ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace Davis

/-!
# Process-level links for Davis Chapter 2

Several statements in the Chapter 2 skeleton quantify over an *arbitrary*
process `X`, filtration `ℱ` and measure `P` with **no hypothesis connecting
them to the PDP** `pdp`.  At that generality they are not merely unproven: they
are false.  This module

* records explicit **falsity certificates** for those statements, and
* supplies **faithful replacements**: either unconditional theorems, or
  statements in which the genuine probabilistic input is named as an explicit
  hypothesis (the convention already used for
  `pdp_extended_generator_characterization`).

The originals are preserved, commented out, at their original location in
`SHSLib/Foundations/DavisCh2.lean`.

## The reference counterexample PDP

`trivialPDP` is the PDP on `ℝ` with the constant flow `φ(t,x) = x`, zero jump
rate, and the (never activated) deterministic transition kernel `x ↦ δ_{x+1}`.
It satisfies the standard conditions, and its renewal semigroup is the
identity: `P_t f = f`.
-/

section TrivialPDP

/-- The PDP on `ℝ` with constant flow, zero jump rate and transition kernel
`x ↦ δ_{x+1}`.  It is the reference counterexample used below. -/
def trivialPDP : PDP ℝ where
  flow := fun _ x => x
  flow_zero := fun _ => rfl
  flow_add := fun _ _ _ => rfl
  flow_measurable := fun _ => measurable_id
  jumpRate := fun _ => 0
  jumpRate_measurable := measurable_const
  transitionMeasure := Kernel.deterministic (fun x : ℝ => x + 1) (by fun_prop)
  transitionMeasure_markov := by infer_instance
  no_self_jump := by
    intro x
    rw [Kernel.deterministic_apply]
    simp

@[simp] lemma trivialPDP_flow (t : ℝ≥0) (x : ℝ) : trivialPDP.flow t x = x := rfl

@[simp] lemma trivialPDP_jumpRate (x : ℝ) : trivialPDP.jumpRate x = 0 := rfl

@[simp] lemma trivialPDP_transitionMeasure (x : ℝ) :
    trivialPDP.transitionMeasure x = Measure.dirac (x + 1) := by
  rw [show trivialPDP.transitionMeasure
        = Kernel.deterministic (fun x : ℝ => x + 1) (by fun_prop) from rfl,
    Kernel.deterministic_apply]

@[simp] lemma trivialPDP_survivor (t : ℝ≥0) (x : ℝ) :
    pdpSurvivorFunction trivialPDP t x = 1 := by
  simp [pdpSurvivorFunction]

/-- The standard-conditions upgrade of `trivialPDP`. -/
def trivialPDPStandard : PDPStandard ℝ where
  toPDP := trivialPDP
  jumpRate_locally_integrable := by
    intro x
    exact ⟨1, one_pos, by simp⟩
  nonExplosive := ⟨trivial⟩

/-- The renewal operator of `trivialPDP` returns `f` itself. -/
lemma trivialPDP_semigroupOp (f : ℝ → ℝ) (ψ : ℝ≥0 × ℝ → ℝ) (q : ℝ≥0 × ℝ) :
    pdpSemigroupOp trivialPDP f ψ q = f q.2 := by
  simp [pdpSemigroupOp]

/-- The renewal semigroup of `trivialPDP` is the identity: `P_t f = f`. -/
lemma trivialPDP_semigroup (t : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) :
    pdpSemigroup trivialPDP t f x = f x := by
  have hiter : ∀ n : ℕ,
      (pdpSemigroupOp trivialPDP f)^[n + 1] (fun _ => 0) (t, x) = f x := by
    intro n
    rw [Function.iterate_succ_apply']
    exact trivialPDP_semigroupOp f _ (t, x)
  have htend : Tendsto
      (fun n => (pdpSemigroupOp trivialPDP f)^[n] (fun _ => 0) (t, x))
      atTop (nhds (f x)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (hiter m).symm
  simp [pdpSemigroup, htend.limUnder_eq]

/-- The filtration that carries no information at all.  Used, with a
two-point sample space, to witness the failure of the unlinked statements. -/
def botFiltration {Omega : Type*} (m : MeasurableSpace Omega) :
    Filtration ℝ≥0 m where
  seq := fun _ => ⊥
  mono' := fun _ _ _ => le_rfl
  le' := fun _ => bot_le

/-- On `Bool`, the trivial σ-algebra does not see the singleton `{true}`. -/
lemma not_measurableSet_bot_true :
    ¬ MeasurableSet[(⊥ : MeasurableSpace Bool)] ({true} : Set Bool) := by
  rw [MeasurableSpace.measurableSet_bot_iff]
  rintro (h1 | h1)
  · simpa using (Set.ext_iff.mp h1 true)
  · simpa using (Set.ext_iff.mp h1 false)

end TrivialPDP

/-!
## §25.3 Right-continuity of the filtration
-/

-- The falsity certificate for the unlinked form of Davis (25.3) is
-- `Davis.pdp_filtration_right_continuous_false` in `SHSLib.Foundations.DavisCh2`,
-- which this module imports.  It was proved independently here against an earlier
-- state of `DavisCh2`; the canonical version is kept and this copy removed.

/-- **Faithful replacement for Davis (25.3): the right-limit filtration is
right-continuous.**  For an arbitrary filtration `ℱ` on `ℝ≥0`, write
`ℱ⁺ t = ⨅_{ε>0} ℱ (t+ε)`.  Then `ℱ⁺` *is* right-continuous:
`⨅_{ε>0} ℱ⁺ (t+ε) = ℱ⁺ t`.  Right-continuity of the natural filtration of a
process — Davis's actual claim — is a property of the PDP construction, not of
an arbitrary filtration; the certificate above shows the unlinked form fails. -/
theorem filtration_rightLimit_idem {Omega : Type*} {m : MeasurableSpace Omega}
    (ℱ : Filtration ℝ≥0 m) (t : ℝ≥0) :
    (⨅ (ε : ℝ≥0) (_ : 0 < ε), ⨅ (δ : ℝ≥0) (_ : 0 < δ), ℱ (t + ε + δ))
      = ⨅ (ε : ℝ≥0) (_ : 0 < ε), ℱ (t + ε) := by
  refine le_antisymm (le_iInf fun ε => le_iInf fun hε => ?_) ?_
  · have h1 : (⨅ (ε : ℝ≥0) (_ : 0 < ε), ⨅ (δ : ℝ≥0) (_ : 0 < δ), ℱ (t + ε + δ))
        ≤ ⨅ (δ : ℝ≥0) (_ : 0 < δ), ℱ (t + ε / 2 + δ) :=
      iInf₂_le (ε / 2) (half_pos hε)
    have h2 : (⨅ (δ : ℝ≥0) (_ : 0 < δ), ℱ (t + ε / 2 + δ)) ≤ ℱ (t + ε / 2 + ε / 2) :=
      iInf₂_le (ε / 2) (half_pos hε)
    have h3 : t + ε / 2 + ε / 2 = t + ε := by rw [add_assoc, add_halves]
    rw [h3] at h2
    exact le_trans h1 h2
  · refine le_iInf fun ε => le_iInf fun hε => le_iInf fun δ => le_iInf fun hδ => ?_
    exact le_trans (iInf₂_le ε hε) (ℱ.mono (by simp))

/-!
## §25.5 The (strong) Markov property
-/

/-- **Falsity certificate for the unlinked form of the simple Markov property,
Davis (25.5).**  With `X` unrelated to the PDP the identity fails: take the
PDP with constant flow and no jumps (`trivialPDP`, whose semigroup is the
identity), the deterministic path `X s ω = s`, and `f = 1_{[1,∞)}`.  Then the
left-hand side is `f (1) = 1` and the right-hand side is `f (0) = 0`. -/
theorem pdp_simple_markov_false :
    ¬ ∀ (Omega E : Type) [MeasurableSpace Omega] [MeasurableSpace E]
        (P : Measure Omega), IsProbabilityMeasure P →
        ∀ (pdp : PDP E) (X : ℝ≥0 → Omega → E)
          (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Omega›),
        (∀ t, Measurable (X t)) →
        ∀ (f : E → ℝ), Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        ∀ t s : ℝ≥0, P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
          fun omega => pdpSemigroup pdp s f (X t omega) := by
  intro h
  set f : ℝ → ℝ := fun x => if (1 : ℝ) ≤ x then 1 else 0 with hf
  have hfmeas : Measurable f :=
    measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
  have h0 := h Unit ℝ (Measure.dirac ()) inferInstance trivialPDP
      (fun s _ => (s : ℝ)) (botFiltration _) (fun _ => measurable_const)
      f hfmeas ⟨1, by intro x; by_cases hx : (1 : ℝ) ≤ x <;> simp [hf, hx]⟩ 0 1
  rw [condExp_const ((botFiltration (PUnit.instMeasurableSpace)).le 0)] at h0
  have h1 : f ((0 : ℝ≥0) + 1 : ℝ≥0) = pdpSemigroup trivialPDP 1 f ((0 : ℝ≥0) : ℝ) := by
    simpa [MeasureTheory.ae_dirac_eq] using h0
  rw [trivialPDP_semigroup] at h1
  norm_num [hf] at h1

/-- **Falsity certificate for the unlinked form of the strong Markov property,
Davis (25.5).**  The same data as in `pdp_simple_markov_false`, with the
(constant, hence stopping) time `τ ≡ 0`. -/
theorem pdp_strong_markov_false :
    ¬ ∀ (Omega E : Type) [MeasurableSpace Omega] [MeasurableSpace E]
        (P : Measure Omega), IsProbabilityMeasure P →
        ∀ (pdp : PDP E) (X : ℝ≥0 → Omega → E)
          (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Omega›) (tau : Omega → ℝ≥0)
          (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
          (f : E → ℝ), Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        ∀ s : ℝ≥0,
          P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
            fun omega => pdpSemigroup pdp s f (X (tau omega) omega) := by
  intro h
  set f : ℝ → ℝ := fun x => if (1 : ℝ) ≤ x then 1 else 0 with hf
  have hfmeas : Measurable f :=
    measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
  have h0 := h Unit ℝ (Measure.dirac ()) inferInstance trivialPDP
      (fun s _ => (s : ℝ)) (botFiltration _) (fun _ => 0)
      (isStoppingTime_const (botFiltration (PUnit.instMeasurableSpace)) 0)
      f hfmeas ⟨1, by intro x; by_cases hx : (1 : ℝ) ≤ x <;> simp [hf, hx]⟩ 1
  rw [condExp_const (IsStoppingTime.measurableSpace_le _)] at h0
  have h1 : f ((0 : ℝ≥0) + 1 : ℝ≥0) = pdpSemigroup trivialPDP 1 f ((0 : ℝ≥0) : ℝ) := by
    simpa [MeasureTheory.ae_dirac_eq] using h0
  rw [trivialPDP_semigroup] at h1
  norm_num [hf] at h1

/-- **Faithful replacement for the simple Markov property (Davis 25.5), general
state space.**  The probabilistic input — that the conditional law of
`X_{t+s}` given `ℱ_t` is a kernel `κ` evaluated at `X_t` — is named as the
hypothesis `hkernel`; the analytic input is that `κ` represents the renewal
semigroup.  This generalizes `pdp_simple_markov_finite_of_kernel` from a finite
state space to an arbitrary measurable state space. -/
theorem pdp_simple_markov_of_kernel
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} (pdp : PDP E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {f : E → ℝ} (t s : ℝ≥0) (κ : Kernel E E)
    (hrepr : ∀ x, (∫ y, f y ∂(κ x)) = pdpSemigroup pdp s f x)
    (hkernel : P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => ∫ y, f y ∂(κ (X t omega))) :
    P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X t omega) :=
  hkernel.trans (Filter.Eventually.of_forall fun omega => hrepr (X t omega))

/-- For a stopping time `τ` with values in `ℝ≥0`, the event `{τ = i}` belongs to
`ℱ i`. -/
lemma stoppingTime_measurableSet_eq
    {Omega : Type*} [MeasurableSpace Omega]
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞))) (i : ℝ≥0) :
    MeasurableSet[ℱ i] {omega | ((tau omega : ℝ≥0∞)) = (i : ℝ≥0∞)} := by
  have h1 : MeasurableSet[htau.measurableSpace]
      (Set.univ ∩ {omega | ((tau omega : ℝ≥0∞)) = (i : ℝ≥0∞)}) := by
    rw [Set.univ_inter]; exact htau.measurableSet_eq' i
  have h2 := (htau.measurableSet_inter_eq_iff Set.univ i).mp h1
  rwa [Set.univ_inter] at h2

/-- **Strong Markov property at a countably-valued stopping time.**
If the simple Markov property holds at every time `t` in the (countable) range of
the stopping time `τ`, with transition operator `f ↦ g`, then the strong Markov
property holds at `τ`:
`E[f(X_{τ+s}) | ℱ_τ] = g(X_τ)` a.s.

This is the classical first step of the proof of the strong Markov property, and
it is genuine content: only the *simple* Markov property is assumed.  The proof
decomposes `Ω` along the countably many values of `τ`, uses that
`E[· | ℱ_τ] = E[· | ℱ_t]` on `{τ = t}`, and replaces `f(X_{τ+s})` by
`f(X_{t+s})` there. -/
theorem strong_markov_of_simple_of_countable_range
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {f g : E → ℝ} {s : ℝ≥0}
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (S : Set ℝ≥0) (hScount : S.Countable) (hrange : ∀ omega, tau omega ∈ S)
    (hint : Integrable (fun omega => f (X (tau omega + s) omega)) P)
    (hfint : ∀ t ∈ S, Integrable (fun omega => f (X (t + s) omega)) P)
    (hsimple : ∀ t ∈ S, P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
        fun omega => g (X t omega)) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => g (X (tau omega) omega) := by
  classical
  set F : Omega → ℝ := fun omega => f (X (tau omega + s) omega) with hFdef
  have key : ∀ i ∈ S, ∀ᵐ omega ∂P,
      tau omega = i → (P[F | htau.measurableSpace]) omega = g (X (tau omega) omega) := by
    intro i hi
    have hAi : MeasurableSet[ℱ i] {omega | ((tau omega : ℝ≥0∞)) = (i : ℝ≥0∞)} :=
      stoppingTime_measurableSet_eq htau i
    set A : Set Omega := {omega | ((tau omega : ℝ≥0∞)) = (i : ℝ≥0∞)} with hA
    have hmemA : ∀ omega, omega ∈ A ↔ tau omega = i := fun omega => ENNReal.coe_inj
    have hA0 : MeasurableSet A := ℱ.le i _ hAi
    have step1 : P[F | htau.measurableSpace] =ᵐ[P.restrict A] P[F | ℱ i] :=
      condExp_stopping_time_ae_eq_restrict_eq (μ := P) (f := F) htau i
    set Fi : Omega → ℝ := fun omega => f (X (i + s) omega) with hFi
    have hEq : A.indicator F = A.indicator Fi := by
      funext omega
      by_cases hmem : omega ∈ A
      · simp only [Set.indicator_of_mem hmem, hFdef, hFi]
        rw [show tau omega = i from (hmemA omega).1 hmem]
      · simp [Set.indicator_of_notMem hmem]
    have step2 : P[F | ℱ i] =ᵐ[P.restrict A] P[Fi | ℱ i] := by
      have h1 : P[A.indicator F | ℱ i] =ᵐ[P] A.indicator (P[F | ℱ i]) :=
        condExp_indicator hint hAi
      have h2 : P[A.indicator Fi | ℱ i] =ᵐ[P] A.indicator (P[Fi | ℱ i]) :=
        condExp_indicator (hfint i hi) hAi
      rw [hEq] at h1
      have h3 : A.indicator (P[F | ℱ i]) =ᵐ[P] A.indicator (P[Fi | ℱ i]) := h1.symm.trans h2
      exact (ae_restrict_iff' hA0).2 (h3.mono (fun omega homega hmem => by
        simpa [Set.indicator_of_mem hmem] using homega))
    have step3 : P[Fi | ℱ i] =ᵐ[P] fun omega => g (X i omega) := hsimple i hi
    have hfinal : P[F | htau.measurableSpace] =ᵐ[P.restrict A] fun omega => g (X i omega) :=
      (step1.trans step2).trans (ae_restrict_of_ae step3)
    filter_upwards [(ae_restrict_iff' hA0).1 hfinal] with omega homega hmem
    have hmem' : omega ∈ A := (hmemA omega).2 hmem
    rw [homega hmem', hmem]
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ S,
      tau omega = i → (P[F | htau.measurableSpace]) omega = g (X (tau omega) omega) :=
    (ae_ball_iff hScount).2 key
  filter_upwards [hall] with omega homega
  exact homega (tau omega) (hrange omega) rfl

/-- **Faithful replacement for the strong Markov property (Davis 25.5) at a
countably-valued stopping time.**  Specialization of
`strong_markov_of_simple_of_countable_range` to the renewal semigroup: if the
simple Markov property holds with transition operator `P_s = pdpSemigroup pdp s`
at every value of the stopping time `τ`, then so does the strong Markov
property at `τ`. -/
theorem pdp_strong_markov_of_simple_of_countable_range
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {f : E → ℝ} {s : ℝ≥0}
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (S : Set ℝ≥0) (hScount : S.Countable) (hrange : ∀ omega, tau omega ∈ S)
    (hint : Integrable (fun omega => f (X (tau omega + s) omega)) P)
    (hfint : ∀ t ∈ S, Integrable (fun omega => f (X (t + s) omega)) P)
    (hsimple : ∀ t ∈ S, P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
        fun omega => pdpSemigroup pdp s f (X t omega)) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) :=
  strong_markov_of_simple_of_countable_range htau S hScount hrange hint hfint hsimple

/-!
## §26.7 The compensator of the counting process
-/

-- The falsity certificate for the unlinked form of Davis (26.7) is
-- `Davis.compensator_is_local_martingale_false` in `SHSLib.Foundations.DavisCh2`,
-- which this module imports.

/-- **Faithful replacement for Davis (26.7).**  The genuine probabilistic input
is that the compensated counting process, stopped at each member of a
localizing sequence `σₙ ↑ ∞`, is a martingale; the localization packaging is
then immediate.  (The falsity certificate above shows that no such conclusion
can hold without the link between `p_count`, `X`, `ℱ` and the PDP.) -/
theorem compensator_is_local_martingale_of_stopped
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (A : Set E)
    (X : ℝ≥0 → Omega → E) (p_count : ℝ≥0 → Omega → ℝ)
    (σ : ℕ → Omega → ℝ≥0)
    (hσ_st : ∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞)))
    (hσ_top : ∀ᵐ omega ∂P, Tendsto (fun n => (σ n omega : ℝ≥0∞)) atTop (nhds ⊤))
    (hstopped : ∀ n, Martingale (fun t omega =>
        p_count (min t (σ n omega)) omega -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          (pdp.transitionMeasure (X u.toNNReal omega) A).toReal *
          (pdp.jumpRate (X u.toNNReal omega) : ℝ)) ℱ P) :
    ∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Tendsto (fun n => (σ n omega : ℝ≥0∞)) atTop (nhds ⊤)) ∧
      ∀ n, Martingale (fun t omega =>
        p_count (min t (σ n omega)) omega -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          (pdp.transitionMeasure (X u.toNNReal omega) A).toReal *
          (pdp.jumpRate (X u.toNNReal omega) : ℝ)) ℱ P :=
  ⟨σ, hσ_st, hσ_top, hstopped⟩

/-!
## §26.14 The boundary condition
-/

-- The falsity certificate for the unlinked form of the boundary condition,
-- Davis (26.14), is `Davis.pdp_generator_boundary_condition_necessary_false` in
-- `SHSLib.Foundations.DavisCh2`, which this module imports.

/-- Constant functions always satisfy the boundary condition (the transition
measure is a probability measure).  This is the unconditional content of
`InExtGenDomain_BdCond`; the general necessity claim is false as formalized,
see `pdp_generator_boundary_condition_necessary_false`. -/
theorem pdp_boundary_condition_const {E : Type*} [MeasurableSpace E]
    (p : PDP E) (c : ℝ) (Gamma : Set E) :
    InExtGenDomain_BdCond p (fun _ => c) Gamma := by
  intro x _
  haveI := p.transitionMeasure_markov
  simp

/-!
## §27.8 Right-continuity of excessive functions along the paths
-/

/-- **Falsity certificate for the unlinked form of Davis (27.8).**  With `X` an
arbitrary process, no path regularity can follow.  Take `trivialPDP` (semigroup
= identity, so every non-negative function is `0`-excessive), `f = |·|`, and the
path `X s = 0` for `s ≤ 1`, `X s = 2` for `s > 1`, which is not right-continuous
at `s = 1`. -/
theorem pdp_is_borel_right_process_false :
    ¬ ∀ (E : Type) [MeasurableSpace E] [TopologicalSpace E] [MetricSpace E]
        [SecondCountableTopology E] [LocallyCompactSpace E] [BorelSpace E]
        (pdp : PDPStandard E) (alpha : ℝ≥0) (f : E → ℝ),
        IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha f →
        ∀ (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega)
          (X : ℝ≥0 → Omega → E),
        ∀ᵐ omega ∂P, ∀ t : ℝ≥0,
          Tendsto (fun s => f (X s omega)) (nhdsWithin t (Set.Ioi t))
            (nhds (f (X t omega))) := by
  intro h
  have hexc : IsAlphaExcessive (pdpSemigroup trivialPDPStandard.toPDP) 0 (fun x : ℝ => |x|) := by
    refine ⟨fun x => abs_nonneg x, ?_, ?_⟩
    · intro t x
      show Real.exp (-(0 : ℝ) * (t : ℝ)) * pdpSemigroup trivialPDP t (fun x : ℝ => |x|) x ≤ |x|
      rw [trivialPDP_semigroup]
      simp
    · intro x
      show Tendsto (fun t : ℝ≥0 => Real.exp (-(0 : ℝ) * (t : ℝ)) *
        pdpSemigroup trivialPDP t (fun x : ℝ => |x|) x) (nhds 0) (nhds |x|)
      simp [trivialPDP_semigroup]
  have h0 := h ℝ trivialPDPStandard 0 (fun x : ℝ => |x|) hexc Unit (Measure.dirac ())
      (fun s _ => if s ≤ 1 then (0 : ℝ) else 2)
  have h1 := (by simpa [MeasureTheory.ae_dirac_eq] using h0 : ∀ t : ℝ≥0,
      Tendsto (fun s : ℝ≥0 => |if s ≤ (1 : ℝ≥0) then (0 : ℝ) else 2|)
        (nhdsWithin t (Set.Ioi t)) (nhds |if t ≤ (1 : ℝ≥0) then (0 : ℝ) else 2|))
  have h2 := h1 1
  simp only [le_refl, if_true, abs_zero] at h2
  have h3 : Tendsto (fun s : ℝ≥0 => |if s ≤ (1 : ℝ≥0) then (0 : ℝ) else 2|)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 2) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : ¬ (s ≤ (1 : ℝ≥0)) := not_le.mpr hs
    simp [hs']
  have h4 := tendsto_nhds_unique h2 h3
  norm_num at h4

/-- **Faithful replacement for Davis (27.8).**  Path right-continuity is a
property of the process, not of the excessive function: if the paths of `X` are
right-continuous and `f` is continuous, then `t ↦ f(X_t)` is right-continuous.
(For the PDP, right-continuity of the paths is part of the construction.) -/
theorem path_right_continuous_comp
    {Omega E : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → Omega → E} {f : E → ℝ} (hf : Continuous f)
    (hrc : ∀ omega, ∀ t : ℝ≥0,
      Tendsto (fun s => X s omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    (omega : Omega) (t : ℝ≥0) :
    Tendsto (fun s => f (X s omega)) (nhdsWithin t (Set.Ioi t)) (nhds (f (X t omega))) :=
  (hf.continuousAt).tendsto.comp (hrc omega t)

/-!
## Strong Markov property at a general (right-continuous) stopping time

The countable-range result `strong_markov_of_simple_of_countable_range` is
upgraded to an *arbitrary* stopping time by the classical dyadic approximation
`τ ↦ τₙ := ⌈2ⁿ τ⌉ / 2ⁿ`, using right-continuity of the paths and bounded
convergence for conditional expectations.
-/

section DyadicApproximation

/-- The dyadic upper approximation `⌈2ⁿ t⌉ / 2ⁿ` of `t : ℝ≥0`. -/
def dyadicUp (n : ℕ) (t : ℝ≥0) : ℝ≥0 := (⌈(2 ^ n : ℝ≥0) * t⌉₊ : ℝ≥0) / 2 ^ n

lemma dyadicUp_ge (n : ℕ) (t : ℝ≥0) : t ≤ dyadicUp n t := by
  rw [dyadicUp, le_div_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n), mul_comm]
  exact Nat.le_ceil _

lemma dyadicUp_le_add (n : ℕ) (t : ℝ≥0) : dyadicUp n t ≤ t + (2 ^ n)⁻¹ := by
  rw [dyadicUp, div_le_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n)]
  refine (Nat.ceil_lt_add_one (R := ℝ≥0) (a := (2 ^ n : ℝ≥0) * t) (zero_le _)).le.trans ?_
  rw [add_mul, inv_mul_cancel₀ (by positivity : ((2 : ℝ≥0) ^ n) ≠ 0), mul_comm]

/-- `⌈2ⁿ t⌉/2ⁿ ≤ u` exactly when `t` is at most the largest dyadic rational of
order `n` below `u`.  This is what makes `dyadicUp ∘ τ` a stopping time. -/
lemma dyadicUp_le_iff (n : ℕ) (t u : ℝ≥0) :
    dyadicUp n t ≤ u ↔ t ≤ (⌊(2 ^ n : ℝ≥0) * u⌋₊ : ℝ≥0) / 2 ^ n := by
  have hpos : (0 : ℝ≥0) < 2 ^ n := by positivity
  rw [dyadicUp, div_le_iff₀ hpos, le_div_iff₀ hpos]
  constructor
  · intro h
    have h1 : (⌈(2 ^ n : ℝ≥0) * t⌉₊ : ℕ) ≤ ⌊(2 ^ n : ℝ≥0) * u⌋₊ := by
      rw [Nat.le_floor_iff (zero_le _)]
      calc ((⌈(2 ^ n : ℝ≥0) * t⌉₊ : ℕ) : ℝ≥0) ≤ u * 2 ^ n := h
        _ = 2 ^ n * u := by ring
    calc t * (2 ^ n : ℝ≥0) = 2 ^ n * t := by ring
      _ ≤ (⌈(2 ^ n : ℝ≥0) * t⌉₊ : ℝ≥0) := Nat.le_ceil _
      _ ≤ ((⌊(2 ^ n : ℝ≥0) * u⌋₊ : ℕ) : ℝ≥0) := by exact_mod_cast h1
  · intro h
    have h1 : (⌈(2 ^ n : ℝ≥0) * t⌉₊ : ℕ) ≤ ⌊(2 ^ n : ℝ≥0) * u⌋₊ := by
      rw [Nat.ceil_le]
      calc (2 ^ n : ℝ≥0) * t = t * 2 ^ n := by ring
        _ ≤ ((⌊(2 ^ n : ℝ≥0) * u⌋₊ : ℕ) : ℝ≥0) := h
    calc ((⌈(2 ^ n : ℝ≥0) * t⌉₊ : ℕ) : ℝ≥0) ≤ ((⌊(2 ^ n : ℝ≥0) * u⌋₊ : ℕ) : ℝ≥0) := by
          exact_mod_cast h1
      _ ≤ 2 ^ n * u := Nat.floor_le (zero_le _)
      _ = u * 2 ^ n := by ring

lemma dyadicUp_floor_le (n : ℕ) (u : ℝ≥0) : (⌊(2 ^ n : ℝ≥0) * u⌋₊ : ℝ≥0) / 2 ^ n ≤ u := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n)]
  calc ((⌊(2 ^ n : ℝ≥0) * u⌋₊ : ℕ) : ℝ≥0) ≤ 2 ^ n * u := Nat.floor_le (zero_le _)
    _ = u * 2 ^ n := by ring

lemma tendsto_dyadicUp (t : ℝ≥0) : Tendsto (fun n => dyadicUp n t) atTop (nhds t) := by
  have h0 : Tendsto (fun n : ℕ => t + ((2 : ℝ≥0) ^ n)⁻¹) atTop (nhds (t + 0)) := by
    refine Filter.Tendsto.const_add t ?_
    have h : Tendsto (fun n : ℕ => ((2 : ℝ≥0)⁻¹) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (zero_le _) (by norm_num)
    simpa [inv_pow] using h
  rw [add_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun n => dyadicUp_ge n t) (fun n => dyadicUp_le_add n t)

/-- The dyadic approximation of a stopping time is a stopping time. -/
lemma isStoppingTime_dyadicUp {Omega : Type*} [MeasurableSpace Omega]
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞))) (n : ℕ) :
    IsStoppingTime ℱ (fun omega => ((dyadicUp n (tau omega) : ℝ≥0) : ℝ≥0∞)) := by
  intro u
  have hset : {omega | ((dyadicUp n (tau omega) : ℝ≥0) : ℝ≥0∞) ≤ (u : ℝ≥0∞)}
      = {omega | ((tau omega : ℝ≥0∞)) ≤
          (((⌊(2 ^ n : ℝ≥0) * u⌋₊ : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ≥0∞)} := by
    ext omega
    simp only [Set.mem_setOf_eq, ENNReal.coe_le_coe]
    exact dyadicUp_le_iff n (tau omega) u
  show MeasurableSet[ℱ u] {omega | ((dyadicUp n (tau omega) : ℝ≥0) : ℝ≥0∞) ≤ (u : ℝ≥0∞)}
  rw [hset]
  exact (ℱ.mono (dyadicUp_floor_le n u)) _ (htau _)

/-- If a time change `u` takes countably many values and each level set is
measurable, then evaluating a measurable family along it stays measurable. -/
lemma measurable_comp_countable_time {Omega E : Type*} [MeasurableSpace Omega]
    [MeasurableSpace E] {u : Omega → ℝ≥0} (hcount : (Set.range u).Countable)
    (hmeas : ∀ v : ℝ≥0, MeasurableSet {omega | u omega = v})
    {H : ℝ≥0 → Omega → E} (hH : ∀ v, Measurable (H v)) :
    Measurable (fun omega => H (u omega) omega) := by
  intro B hB
  have hpre : (fun omega => H (u omega) omega) ⁻¹' B
      = ⋃ v ∈ Set.range u, ({omega | u omega = v} ∩ (H v) ⁻¹' B) := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro h; exact ⟨u omega, ⟨omega, rfl⟩, rfl, h⟩
    · rintro ⟨v, -, rfl, h⟩; exact h
  rw [hpre]
  exact MeasurableSet.biUnion hcount fun v _ => (hmeas v).inter (hH v hB)

/-- A right-continuous path is a sequential limit along any sequence decreasing
to the time from above. -/
lemma tendsto_of_rightContinuous {E : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → E} {t : ℝ≥0} (hrc : Tendsto X (nhdsWithin t (Set.Ioi t)) (nhds (X t)))
    {u : ℕ → ℝ≥0} (hu : Tendsto u atTop (nhds t)) (hge : ∀ n, t ≤ u n) :
    Tendsto (fun n => X (u n)) atTop (nhds (X t)) := by
  have hIci : Tendsto X (nhdsWithin t (Set.Ici t)) (nhds (X t)) := by
    rw [← Set.Ioi_union_left, nhdsWithin_union, nhdsWithin_singleton, Filter.tendsto_sup]
    exact ⟨hrc, tendsto_pure_nhds _ _⟩
  exact hIci.comp (tendsto_nhdsWithin_iff.2 ⟨hu, Filter.Eventually.of_forall hge⟩)

end DyadicApproximation

/-- **Strong Markov property at an arbitrary stopping time.**

If the paths of `X` are right-continuous, `f` and `g` are bounded continuous,
and the *simple* Markov property `E[f(X_{t+s}) | ℱ_t] = g(X_t)` holds at every
deterministic time `t`, then the strong Markov property
`E[f(X_{τ+s}) | ℱ_τ] = g(X_τ)` holds at every stopping time `τ` whose
associated random variable `g(X_τ)` is `ℱ_τ`-measurable (which is automatic for
a progressively measurable process).

The proof is the classical dyadic approximation: `τₙ = ⌈2ⁿτ⌉/2ⁿ` is a
countably-valued stopping time decreasing to `τ`, the countable-range strong
Markov property applies to each `τₙ`, the tower property transfers it to `ℱ_τ`,
and bounded convergence passes to the limit. -/
theorem strong_markov_of_simple_of_rightContinuous
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P] {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} {f g : E → ℝ} {s : ℝ≥0} {C : ℝ}
    (hXmeas : ∀ t, Measurable (X t)) (hfcont : Continuous f) (hgcont : Continuous g)
    (hfC : ∀ x, |f x| ≤ C) (hgC : ∀ x, |g x| ≤ C)
    (hrc : ∀ omega : Omega, ∀ t : ℝ≥0,
      Tendsto (fun v => X v omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    {tau : Omega → ℝ≥0} (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (hsimple : ∀ t : ℝ≥0, P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => g (X t omega))
    (hGmeas : StronglyMeasurable[htau.measurableSpace] (fun omega => g (X (tau omega) omega))) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => g (X (tau omega) omega) := by
  classical
  set tn : ℕ → Omega → ℝ≥0 := fun n omega => dyadicUp n (tau omega)
  have hstn : ∀ n, IsStoppingTime ℱ (fun omega => ((tn n omega : ℝ≥0) : ℝ≥0∞)) :=
    fun n => isStoppingTime_dyadicUp htau n
  have hcount : ∀ n, (Set.range (tn n)).Countable := by
    intro n
    refine Set.Countable.mono ?_ (Set.countable_range fun k : ℕ => (k : ℝ≥0) / 2 ^ n)
    rintro _ ⟨omega, rfl⟩
    exact ⟨_, rfl⟩
  have hmeasset : ∀ n (v : ℝ≥0), MeasurableSet {omega | tn n omega = v} := by
    intro n v
    have h2 : MeasurableSet {omega | ((tn n omega : ℝ≥0) : ℝ≥0∞) = (v : ℝ≥0∞)} :=
      ℱ.le v _ (stoppingTime_measurableSet_eq (hstn n) v)
    convert h2 using 2 with omega
    simp [ENNReal.coe_inj]
  set fs : ℕ → Omega → ℝ := fun n omega => f (X (tn n omega + s) omega)
  set gs : ℕ → Omega → ℝ := fun n omega => g (X (tn n omega) omega)
  have hfsmeas : ∀ n, Measurable (fs n) := fun n =>
    measurable_comp_countable_time (hcount n) (hmeasset n)
      (H := fun v omega => f (X (v + s) omega))
      (fun v => hfcont.measurable.comp (hXmeas (v + s)))
  have hgsmeas : ∀ n, Measurable (gs n) := fun n =>
    measurable_comp_countable_time (hcount n) (hmeasset n)
      (H := fun v omega => g (X v omega)) (fun v => hgcont.measurable.comp (hXmeas v))
  have hfsint : ∀ n, Integrable (fs n) P := fun n =>
    Integrable.of_bound (hfsmeas n).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun _ => by simpa [Real.norm_eq_abs] using hfC _)
  have hgsint : ∀ n, Integrable (gs n) P := fun n =>
    Integrable.of_bound (hgsmeas n).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun _ => by simpa [Real.norm_eq_abs] using hgC _)
  have hftint : ∀ t : ℝ≥0, Integrable (fun omega => f (X (t + s) omega)) P := fun t =>
    Integrable.of_bound (hfcont.measurable.comp (hXmeas (t + s))).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun _ => by simpa [Real.norm_eq_abs] using hfC _)
  have hSM : ∀ n, P[fs n | (hstn n).measurableSpace] =ᵐ[P] gs n := fun n =>
    strong_markov_of_simple_of_countable_range (hstn n) (Set.range (tn n)) (hcount n)
      (fun omega => ⟨omega, rfl⟩) (hfsint n) (fun t _ => hftint t) (fun t _ => hsimple t)
  have hmono : ∀ n, htau.measurableSpace ≤ (hstn n).measurableSpace := fun n =>
    IsStoppingTime.measurableSpace_mono htau (hstn n)
      (fun omega => ENNReal.coe_le_coe.2 (dyadicUp_ge n (tau omega)))
  have htower : ∀ n, P[fs n | htau.measurableSpace] =ᵐ[P] P[gs n | htau.measurableSpace] := by
    intro n
    have h1 : P[P[fs n | (hstn n).measurableSpace] | htau.measurableSpace] =ᵐ[P]
        P[fs n | htau.measurableSpace] :=
      condExp_condExp_of_le (hmono n) (hstn n).measurableSpace_le
    exact h1.symm.trans (condExp_congr_ae (hSM n))
  have hshift : ∀ (omega : Omega) (t : ℝ≥0),
      Tendsto (fun v : ℝ≥0 => X (v + s) omega) (nhdsWithin t (Set.Ioi t))
        (nhds (X (t + s) omega)) := by
    intro omega t
    have hmap : Tendsto (fun v : ℝ≥0 => v + s) (nhdsWithin t (Set.Ioi t))
        (nhdsWithin (t + s) (Set.Ioi (t + s))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(continuous_add_right s).continuousAt.tendsto.comp
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact Set.mem_Ioi.2 (by gcongr; exact hv)
    exact (hrc omega (t + s)).comp hmap
  have hfconv : ∀ omega,
      Tendsto (fun n => fs n omega) atTop (nhds (f (X (tau omega + s) omega))) := by
    intro omega
    exact hfcont.continuousAt.tendsto.comp
      (tendsto_of_rightContinuous (X := fun v : ℝ≥0 => X (v + s) omega) (t := tau omega)
        (hshift omega (tau omega)) (u := fun n => tn n omega) (tendsto_dyadicUp (tau omega))
        (fun n => dyadicUp_ge n (tau omega)))
  have hgconv : ∀ omega,
      Tendsto (fun n => gs n omega) atTop (nhds (g (X (tau omega) omega))) := by
    intro omega
    exact hgcont.continuousAt.tendsto.comp
      (tendsto_of_rightContinuous (X := fun v : ℝ≥0 => X v omega) (t := tau omega)
        (hrc omega (tau omega)) (u := fun n => tn n omega) (tendsto_dyadicUp (tau omega))
        (fun n => dyadicUp_ge n (tau omega)))
  have hkey : P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      P[fun omega => g (X (tau omega) omega) | htau.measurableSpace] :=
    tendsto_condExp_unique fs gs _ _ hfsint hgsint
      (Filter.Eventually.of_forall hfconv) (Filter.Eventually.of_forall hgconv)
      (fun _ => C) (integrable_const C) (fun _ => C) (integrable_const C)
      (fun _ => Filter.Eventually.of_forall fun _ => by simpa [Real.norm_eq_abs] using hfC _)
      (fun _ => Filter.Eventually.of_forall fun _ => by simpa [Real.norm_eq_abs] using hgC _)
      htower
  have hGint : Integrable (fun omega => g (X (tau omega) omega)) P :=
    Integrable.of_bound (hGmeas.mono htau.measurableSpace_le).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun _ => by simpa [Real.norm_eq_abs] using hgC _)
  rwa [condExp_of_stronglyMeasurable htau.measurableSpace_le hGmeas hGint] at hkey

/-- **Expectation form of the strong Markov property.**  Integrating the
conditional identity of `strong_markov_of_simple_of_rightContinuous` gives
`E[f(X_{τ+s})] = E[g(X_τ)]`. -/
theorem expectation_strong_markov_of_simple_of_rightContinuous
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P] {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} {f g : E → ℝ} {s : ℝ≥0} {C : ℝ}
    (hXmeas : ∀ t, Measurable (X t)) (hfcont : Continuous f) (hgcont : Continuous g)
    (hfC : ∀ x, |f x| ≤ C) (hgC : ∀ x, |g x| ≤ C)
    (hrc : ∀ omega : Omega, ∀ t : ℝ≥0,
      Tendsto (fun v => X v omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    {tau : Omega → ℝ≥0} (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (hsimple : ∀ t : ℝ≥0, P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => g (X t omega))
    (hGmeas : StronglyMeasurable[htau.measurableSpace] (fun omega => g (X (tau omega) omega))) :
    ∫ omega, f (X (tau omega + s) omega) ∂P = ∫ omega, g (X (tau omega) omega) ∂P := by
  have hcond := strong_markov_of_simple_of_rightContinuous hXmeas hfcont hgcont hfC hgC hrc htau
    hsimple hGmeas
  calc ∫ omega, f (X (tau omega + s) omega) ∂P
      = ∫ omega, (P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace]) omega ∂P :=
        (integral_condExp htau.measurableSpace_le).symm
    _ = ∫ omega, g (X (tau omega) omega) ∂P := integral_congr_ae hcond

/-- For a progressively measurable process, the value at a stopping time is
`ℱ_τ`-measurable, hence so is any continuous function of it.  This supplies the
hypothesis `hGmeas` of `strong_markov_of_simple_of_rightContinuous`. -/
theorem stronglyMeasurable_comp_stoppedValue
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} {X : ℝ≥0 → Omega → E}
    (hprog : ProgMeasurable ℱ X) {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    {g : E → ℝ} (hg : Continuous g) :
    StronglyMeasurable[htau.measurableSpace] (fun omega => g (X (tau omega) omega)) := by
  have h := measurable_stoppedValue (u := X) (f := ℱ) hprog htau
  have heq : MeasureTheory.stoppedValue X (fun omega => (tau omega : ℝ≥0∞))
      = fun omega => X (tau omega) omega := by
    funext omega
    simp only [MeasureTheory.stoppedValue]
    rw [show WithTop.untopA ((tau omega : ℝ≥0∞)) = tau omega from NNReal.eq rfl]
  rw [heq] at h
  exact (hg.measurable.comp h).stronglyMeasurable

/-- **Strong Markov property for a progressively measurable process.**  Same as
`strong_markov_of_simple_of_rightContinuous`, with the measurability of `g(X_τ)`
supplied by progressive measurability instead of assumed. -/
theorem strong_markov_of_simple_of_progMeasurable
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {P : Measure Omega} [IsProbabilityMeasure P] {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} {f g : E → ℝ} {s : ℝ≥0} {C : ℝ}
    (hprog : ProgMeasurable ℱ X) (hfcont : Continuous f) (hgcont : Continuous g)
    (hfC : ∀ x, |f x| ≤ C) (hgC : ∀ x, |g x| ≤ C)
    (hrc : ∀ omega : Omega, ∀ t : ℝ≥0,
      Tendsto (fun v => X v omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    {tau : Omega → ℝ≥0} (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (hsimple : ∀ t : ℝ≥0, P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => g (X t omega)) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => g (X (tau omega) omega) :=
  strong_markov_of_simple_of_rightContinuous
    (fun t => ((hprog.stronglyAdapted t).mono (ℱ.le t)).measurable)
    hfcont hgcont hfC hgC hrc htau hsimple
    (stronglyMeasurable_comp_stoppedValue hprog htau hgcont)

/-- **Strong Markov property for the PDP renewal semigroup at an arbitrary
stopping time.**  Specialization of `strong_markov_of_simple_of_rightContinuous`
with `g = P_s f`. -/
theorem pdp_strong_markov_of_simple_of_rightContinuous
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P] (pdp : PDP E) {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} {f : E → ℝ} {s : ℝ≥0} {C : ℝ}
    (hXmeas : ∀ t, Measurable (X t)) (hfcont : Continuous f)
    (hgcont : Continuous (pdpSemigroup pdp s f))
    (hfC : ∀ x, |f x| ≤ C) (hgC : ∀ x, |pdpSemigroup pdp s f x| ≤ C)
    (hrc : ∀ omega : Omega, ∀ t : ℝ≥0,
      Tendsto (fun v => X v omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    {tau : Omega → ℝ≥0} (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (hsimple : ∀ t : ℝ≥0, P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X t omega))
    (hGmeas : StronglyMeasurable[htau.measurableSpace]
      (fun omega => pdpSemigroup pdp s f (X (tau omega) omega))) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) :=
  strong_markov_of_simple_of_rightContinuous hXmeas hfcont hgcont hfC hgC hrc htau hsimple hGmeas

end Davis
