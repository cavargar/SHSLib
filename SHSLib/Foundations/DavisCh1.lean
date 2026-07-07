/-
  Formal skeleton for Chapter 1 of M.H.A. Davis,
  "Markov Models and Optimization" (1993).

  Chapter 1: Analysis, Probability and Stochastic Processes

  This file formalizes the key definitions, theorems, and propositions
  from the chapter, organized by section number matching the textbook.
-/

import Mathlib

open MeasureTheory Topology Filter Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-!
## §11 Analysis

### §11.1 Continuity and compactness
-/

namespace Davis

section S11_Analysis

/-!
**(11.1) Definition.** Convergence and cluster points in topological spaces.
These are already captured by Mathlib's `Filter.Tendsto` and `MapClusterPt`.
We record the textbook's observation that every limit point is a cluster point.
-/

/-- (11.1) Every limit of a sequence is a cluster point. -/
theorem limitPoint_isClusterPoint {X : Type*} [TopologicalSpace X]
    {x : X} {s : ℕ → X} (hs : Filter.Tendsto s Filter.atTop (nhds x)) :
    MapClusterPt x Filter.atTop s :=
  hs.mapClusterPt

/-- (11.2) Theorem. If f is continuous then xₙ → x implies f(xₙ) → f(x). -/
theorem continuous_preserves_tendsto {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f)
    {s : ℕ → X} {x : X} (hs : Filter.Tendsto s Filter.atTop (nhds x)) :
    Filter.Tendsto (f ∘ s) Filter.atTop (nhds (f x)) :=
  hf.continuousAt.tendsto.comp hs

/-
PROBLEM
(11.3)(1) Theorem. Every infinite sequence in a compact set has a
    cluster point.

PROVIDED SOLUTION
Use IsCompact.exists_clusterPt. We need to show that the map filter of s along atTop is ≤ principal K. Since ∀ n, s n ∈ K, the range of s is in K, so Filter.map s atTop ≤ Filter.principal K. Then exists_clusterPt gives a cluster point. MapClusterPt is defined as ClusterPt x (Filter.map s atTop).
-/
theorem compact_seq_has_clusterPoint {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {s : ℕ → X} (hs : ∀ n, s n ∈ K) :
    ∃ x ∈ K, MapClusterPt x Filter.atTop s := by
      aesop

/-- (11.3)(2) Theorem. A continuous real-valued function on a compact set
    attains its supremum. -/
theorem compact_attains_sup {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f K) :
    ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  convert hK.exists_isMaxOn hne hf

/-- (11.3)(3) Theorem. A closed subset of a compact set is compact. -/
theorem compact_of_isClosed_of_isCompact {X : Type*} [TopologicalSpace X]
    {K A : Set X} (hK : IsCompact K) (hA : IsClosed A) (hAK : A ⊆ K) :
    IsCompact A :=
  hK.of_isClosed_subset hA hAK

/-!
### §11.2 Metric and linear spaces

The textbook defines metric spaces, normed linear spaces, and Banach spaces.
These correspond to Mathlib's `MetricSpace`, `NormedAddCommGroup`, and
`CompleteSpace` typeclasses.
-/

/-- In a compact subset of a metrizable space, every sequence has a
    convergent subsequence. -/
theorem compact_metric_seq_has_convergent_subseq
    {X : Type*} [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K)
    {s : ℕ → X} (hs : ∀ n, s n ∈ K) :
    ∃ x ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (s ∘ φ) Filter.atTop (nhds x) := by
  have := hK.isSeqCompact fun n => hs n
  exact this

/-- (11.4) C[0,T] is a Banach space (complete under the uniform norm). -/
theorem C0T_banach (T : ℝ) (hT : 0 < T) :
    CompleteSpace (BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℝ) :=
  inferInstance

/-- (11.4) C[0,T] is separable. -/
theorem C0T_separable (T : ℝ) (hT : 0 < T) :
    TopologicalSpace.IsSeparable
      (Set.univ : Set (BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℝ)) := by sorry

/-!
### §11.3 Differentiability
-/

/-- (11.6)(1) Theorem. An absolutely continuous function ℝ → ℝ is differentiable
    almost everywhere (with respect to Lebesgue measure). -/
theorem absContOn_ae_differentiable {f : ℝ → ℝ}
    (hac : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := by sorry

/-- (11.6)(2) Theorem. Fundamental theorem of calculus: if f has derivative f' on
    [a,b] and f' is integrable, then ∫ f' = f(b) - f(a). -/
theorem ftc_abs_continuous {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf' : IntervalIntegrable f' volume a b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) :
    ∫ x in a..b, f' x = f b - f a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt] <;> aesop

/-- (11.8) Proposition. A locally Lipschitz function is differentiable a.e.
    and equals the integral of its derivative. -/
theorem locally_lipschitz_ae_differentiable {f : ℝ → ℝ}
    (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := by sorry

/-
PROBLEM
(11.10) Theorem. If each fα : [a,b] → ℝ₊ is Lipschitz with the same
    constant L, then f(t) = inf_α fα(t) is Lipschitz with constant L.

PROVIDED SOLUTION
Use LipschitzOnWith.dist_le_mul for each F i. The key is to show that for x, y ∈ Icc a b, dist (⨅ i, F i x) (⨅ i, F i y) ≤ L * dist x y.

Approach: Use LipschitzOnWith definition directly. Show edist (⨅ i, F i x) (⨅ i, F i y) ≤ L * edist x y.

First establish that the ranges are bounded below (by 0, from hFnn). Then use Real.dist_eq and show |⨅ i, F i x - ⨅ i, F i y| ≤ L * |x - y|.

For the ≤ direction: ⨅ i, F i x - ⨅ i, F i y ≤ L * dist x y.
For each ε > 0, pick j such that F j y < ⨅ i, F i y + ε. Then:
⨅ i, F i x ≤ F j x ≤ F j y + L * dist x y < (⨅ i, F i y + ε) + L * dist x y.
Since ε is arbitrary, ⨅ i, F i x ≤ ⨅ i, F i y + L * dist x y.
Similarly for the other direction.

Alternative approach using Real.iInf: Convert to the metric/real-valued Lipschitz condition using `LipschitzOnWith` unfolded as `∀ x ∈ S, ∀ y ∈ S, edist (f x) (f y) ≤ L * edist x y`.

Key lemma: ciInf_le_ciInf can be used, or just work directly with the ε-characterization of infimum.

Actually, the simplest approach: use `LipschitzOnWith` iff `∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ L * dist x y` (for real-valued functions). Then show `dist (⨅ i, F i x) (⨅ i, F i y) ≤ L * dist x y` using:
- `Real.dist_le_iff` or `abs_sub_le_iff`
- The fact that for each i, `dist (F i x) (F i y) ≤ L * dist x y` (from hF)
- `ciInf_le` with the bdd_below given by nonnegativity
- `le_ciInf` to bound the infimum from below
-/
theorem lipschitz_infimum {ι : Type*} [Nonempty ι]
    {a b : ℝ} {L : ℝ≥0}
    {F : ι → ℝ → ℝ}
    (hF : ∀ i, LipschitzOnWith L (F i) (Set.Icc a b))
    (hFnn : ∀ i x, x ∈ Set.Icc a b → 0 ≤ F i x) :
    LipschitzOnWith L (fun x => ⨅ i, F i x) (Set.Icc a b) := by
      intros x hx y hy;
      simp +decide only [edist_dist];
      rw [ ENNReal.ofReal_le_iff_le_toReal ] <;> norm_num;
      · refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
        · refine' sub_le_iff_le_add'.mpr _;
          refine' le_of_forall_pos_le_add fun ε εpos => _;
          -- By definition of infimum, there exists some $i$ such that $F_i(y) < \inf_{j} F_j(y) + \epsilon$.
          obtain ⟨i, hi⟩ : ∃ i, F i y < (⨅ j, F j y) + ε := by
            simpa using exists_lt_of_ciInf_lt ( show ⨅ j, F j y < ( ⨅ j, F j y ) + ε by linarith );
          have := hF i |> fun h => h.dist_le_mul x hx y hy;
          exact le_trans ( ciInf_le ( show BddBelow ( Set.range ( fun i => F i x ) ) from ⟨ 0, Set.forall_mem_range.2 fun i => hFnn i x hx ⟩ ) i ) ( by linarith [ abs_le.mp this ] );
        · refine' le_of_forall_pos_le_add fun ε εpos => _;
          -- Choose $i$ such that $F_i(x) < \inf_{j} F_j(x) + \epsilon$.
          obtain ⟨i, hi⟩ : ∃ i, F i x < (⨅ j, F j x) + ε := by
            simpa using exists_lt_of_csInf_lt ( Set.range_nonempty _ ) ( lt_add_of_pos_right _ εpos );
          have := hF i |> fun h => h.dist_le_mul x hx y hy;
          linarith [ abs_le.mp this, show ( ⨅ j, F j y ) ≤ F i y from ciInf_le ( show BddBelow ( Set.range ( fun j => F j y ) ) from ⟨ 0, Set.forall_mem_range.mpr fun j => hFnn j y hy ⟩ ) i ];
      · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ( ENNReal.ofReal_ne_top )

end S11_Analysis

/-!
## §12 Probability theory
-/

section S12_Probability

/-!
The textbook defines σ-fields, measurable spaces, and probability measures.
In Mathlib these correspond to `MeasurableSpace`, `MeasurableSet`,
`MeasureTheory.MeasureSpace`, and `MeasureTheory.IsProbabilityMeasure`.
-/

/-
PROBLEM
(12.1) Theorem (Factorization / Doob–Dynkin lemma). If g is σ(f)-measurable
    then g = h ∘ f for some measurable h.

PROVIDED SOLUTION
Use Measurable.exists_eq_measurable_comp which is exactly this statement in Mathlib. Apply it directly to hg.
-/
theorem doob_dynkin_factorization
    {Ω Y : Type*} [MeasurableSpace Y]
    {f : Ω → Y} {g : Ω → ℝ}
    (hg : @Measurable Ω ℝ (MeasurableSpace.comap f ‹_›) _ g) :
    ∃ h : Y → ℝ, Measurable h ∧ g = h ∘ f := by
      convert Measurable.exists_eq_measurable_comp hg

/-!
### Integration and convergence theorems (12.3)
-/

/-- (12.3)(1) Monotone Convergence Theorem. If Xₙ ↑ X are non-negative,
    then ∫ Xₙ ↑ ∫ X. -/
theorem monotone_convergence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ≥0∞}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_mono : Monotone X) :
    Filter.Tendsto (fun n => ∫⁻ ω, X n ω ∂μ) Filter.atTop
      (nhds (∫⁻ ω, ⨆ n, X n ω ∂μ)) := by
  convert MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone _ _ _
  · exact fun n => (hX_meas n).aemeasurable
  · exact Filter.Eventually.of_forall fun ω => fun n m hnm => hX_mono hnm ω
  · exact Filter.Eventually.of_forall fun ω => tendsto_atTop_iSup fun n m hnm => hX_mono hnm ω

/-- (12.3)(2) Dominated Convergence Theorem. If |Xₙ| ≤ Y (integrable),
    Xₙ → X a.s., then E[Xₙ] → E[X]. -/
theorem dominated_convergence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ} {Xlim : Ω → ℝ} {Y : Ω → ℝ}
    (hX_meas : ∀ n, AEStronglyMeasurable (X n) μ)
    (hXlim_meas : AEStronglyMeasurable Xlim μ)
    (hY_int : Integrable Y μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ Y ω)
    (hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω)
      Filter.atTop (nhds (Xlim ω))) :
    Filter.Tendsto (fun n => ∫ ω, X n ω ∂μ) Filter.atTop
      (nhds (∫ ω, Xlim ω ∂μ)) := by
  apply_rules [MeasureTheory.tendsto_integral_of_dominated_convergence]

/-- (12.3)(3) Fatou's Lemma. If Xₙ ≥ 0, then
    E[liminf Xₙ] ≤ liminf E[Xₙ]. -/
theorem fatou_lemma
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ≥0∞}
    (hX : ∀ n, Measurable (X n)) :
    ∫⁻ ω, Filter.atTop.liminf (fun n => X n ω) ∂μ ≤
      Filter.atTop.liminf (fun n => ∫⁻ ω, X n ω ∂μ) := by
  convert MeasureTheory.lintegral_liminf_le _ using 1 <;> aesop

/-- (12.4) Change of variables / pushforward formula.
    ∫ g ∘ φ dP = ∫ g d(P^φ). -/
theorem change_of_variables
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {μ : Measure Ω}
    {φ : Ω → Y} (hφ : Measurable φ)
    {g : Y → ℝ} (hg : Integrable g (Measure.map φ μ)) :
    ∫ ω, g (φ ω) ∂μ = ∫ y, g y ∂(Measure.map φ μ) := by
  rw [MeasureTheory.integral_map]
  · exact hφ.aemeasurable
  · exact hg.1

/-!
### Convergence of random variables (12.5)
-/

/-- (12.5)(1) a.s. convergence implies convergence in probability. -/
theorem ae_tendsto_imp_tendsto_in_measure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {Xlim : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω)
      Filter.atTop (nhds (Xlim ω))) :
    TendstoInMeasure μ X Filter.atTop Xlim :=
  tendstoInMeasure_of_tendsto_ae hX hlim

/-
PROBLEM
(12.5)(4) Convergence in probability implies a.s. convergence along a
    subsequence.

PROVIDED SOLUTION
Use TendstoInMeasure.exists_seq_tendsto_ae directly applied to h.
-/
theorem tendsto_in_measure_subseq_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ} {Xlim : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (h : TendstoInMeasure μ X Filter.atTop Xlim) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X (φ n) ω)
        Filter.atTop (nhds (Xlim ω)) := by
          convert TendstoInMeasure.exists_seq_tendsto_ae _ using 1;
          exact h

/-!
### Independence (12.6)
-/

/-
PROBLEM
(12.6) Theorem. If X₁, X₂ are independent and integrable, then
    E[X₁ · X₂] = E[X₁] · E[X₂].

PROVIDED SOLUTION
Use IndepFun.integral_mul_eq_mul_integral. The goal has ∫ ω, X₁ ω * X₂ ω which needs to be rewritten as ∫ ω, (X₁ * X₂) ω. Then apply h_ind.integral_mul_eq_mul_integral with the AEStronglyMeasurable witnesses from hX₁ and hX₂.
-/
theorem indep_expectation_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X₁ X₂ : Ω → ℝ}
    (hX₁ : Integrable X₁ μ) (hX₂ : Integrable X₂ μ)
    (h_ind : IndepFun X₁ X₂ μ) :
    ∫ ω, X₁ ω * X₂ ω ∂μ = (∫ ω, X₁ ω ∂μ) * (∫ ω, X₂ ω ∂μ) := by
      convert h_ind.integral_mul_eq_mul_integral _ _ using 1;
      · exact hX₁.1;
      · exact hX₂.1

/-!
### Strong law of large numbers (12.7)
-/

/-- (12.7) Theorem (Strong Law of Large Numbers). If X₁, X₂, … are i.i.d.
    integrable random variables with mean μ, then (1/n)∑ Xₖ → μ a.s. -/
theorem strong_law_of_large_numbers
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (h_meas : ∀ n, Measurable (X n))
    (h_iid : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h_ind : iIndepFun X P)
    (h_int : Integrable (X 0) P) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun (n : ℕ) => (↑n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X k ω)
      Filter.atTop (nhds (∫ ω, X 0 ω ∂P)) := by sorry

/-!
### Conditional expectation (12.8 – 12.11)
-/

/-- (12.9)(1) E[X | G] = X if X is G-measurable. -/
theorem condexp_of_measurable
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : MeasurableSpace Ω} (hG : G ≤ m₀)
    {X : Ω → ℝ} (hX : @Measurable _ _ G _ X)
    (hXint : Integrable X μ) :
    μ[X | G] =ᵐ[μ] X := by
  rw [condExp_of_stronglyMeasurable hG hX.stronglyMeasurable hXint]

/-- (12.9)(4) Tower property. E[E[X | H] | G] = E[X | G] if G ⊆ H.
    Note: added the hypothesis `hH : H ≤ ‹MeasurableSpace Ω›` which is necessary
    for the conditional expectation to be well-defined (without it, `condExp`
    degenerates to 0 when the sub-σ-algebra is not contained in the ambient one,
    making the statement false in general). -/
theorem condexp_tower
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {G H : MeasurableSpace Ω}
    (hGH : ∀ s, @MeasurableSet _ G s → @MeasurableSet _ H s)
    (hH : H ≤ m₀)
    {X : Ω → ℝ} (hXint : Integrable X μ) :
    μ[μ[X | H] | G] =ᵐ[μ] μ[X | G] := by
  haveI : SigmaFinite (μ.trim hH) := (isFiniteMeasure_trim hH).toSigmaFinite
  exact condExp_condExp_of_le hGH hH

/-- (12.10) E[E[X | G]] = E[X]. -/
theorem integral_condexp_eq
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : MeasurableSpace Ω} (hG : G ≤ m₀)
    {X : Ω → ℝ} (hXint : Integrable X μ) :
    ∫ ω, (μ[X | G]) ω ∂μ = ∫ ω, X ω ∂μ :=
  integral_condExp hG

/-
PROBLEM
(12.11) X ≥ Y a.s. implies E[X | G] ≥ E[Y | G] a.s. (monotonicity).

PROVIDED SOLUTION
Direct application of MeasureTheory.condExp_mono with the given hypotheses.
-/
theorem condexp_monotone
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : MeasurableSpace Ω}
    {X Y : Ω → ℝ}
    (hXint : Integrable X μ) (hYint : Integrable Y μ)
    (hXY : X ≤ᵐ[μ] Y) :
    μ[X | G] ≤ᵐ[μ] μ[Y | G] := by
      exact condExp_mono hXint hYint hXY

end S12_Probability

/-!
## §13 Stochastic processes

### §13.1 Processes, filtrations and stopping times
-/

section S13_StochasticProcesses

/-!
In Mathlib, filtrations are modeled by `MeasureTheory.Filtration`, stopping times
by `MeasureTheory.IsStoppingTime`, and martingales by `MeasureTheory.Martingale`.
-/

/-- (13.4) Theorem. A submartingale has a modification that is also a
    submartingale. (Discrete-time version of the RCLL modification theorem.) -/
theorem submartingale_modification
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {M : ℕ → Ω → ℝ}
    (hM : Submartingale M ℱ μ) :
    ∃ M' : ℕ → Ω → ℝ, Submartingale M' ℱ μ ∧
      ∀ n, M n =ᵐ[μ] M' n := by sorry

/-!
### §13.2 Martingales
-/

/-- (13.5) Theorem (Submartingale Convergence). Let X be a submartingale with
    sup_t E[Xₜ⁺] < ∞. Then X∞ = lim Xₜ exists a.s. and is integrable.
    (Discrete-time version.) -/
theorem submartingale_convergence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ)
    (hbdd : BddAbove (Set.range (fun n => ∫ ω, max (X n ω) 0 ∂μ))) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω)
        Filter.atTop (nhds (X_inf ω)) := by sorry

/-- (13.6)(1) Corollary. A non-negative supermartingale converges a.s. -/
theorem supermartingale_nonneg_convergence
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → ℝ}
    (hX : Supermartingale X ℱ μ)
    (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
    ∃ X_inf : Ω → ℝ,
      (∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω)
        Filter.atTop (nhds (X_inf ω))) ∧
      ∀ n, μ[X_inf | ℱ n] ≤ᵐ[μ] X n := by sorry

/-- (13.6)(2) Corollary. A uniformly integrable martingale satisfies
    Xₜ = E[X∞ | Fₜ]. -/
theorem ui_martingale_closed
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ)
    (hui : UniformIntegrable X 1 μ) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ n, X n =ᵐ[μ] μ[X_inf | ℱ n] := by sorry

/-- (13.7) Theorem (Optional Sampling for supermartingales).
    For bounded stopping times S ≤ T, E[X_T | F_S] ≤ X_S a.s. -/
theorem optional_sampling_supermartingale
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → ℝ}
    (hX : Supermartingale X ℱ μ)
    {S T : Ω → ℕ}
    (hS : IsStoppingTime ℱ (fun ω => (S ω : WithTop ℕ)))
    (hT : IsStoppingTime ℱ (fun ω => (T ω : WithTop ℕ)))
    (hST : ∀ ω, S ω ≤ T ω)
    (hTbdd : ∃ N : ℕ, ∀ ω, T ω ≤ N) :
    ∀ᵐ ω ∂μ,
      (μ[fun ω' => X (T ω') ω' | hS.measurableSpace]) ω ≤
        X (S ω) ω := by sorry

/-- (13.9) Corollary. For a uniformly integrable martingale,
    X_S = E[X_T | F_S] for stopping times S ≤ T. -/
theorem optional_sampling_ui_martingale
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ)
    (hui : UniformIntegrable X 1 μ)
    {S T : Ω → ℕ}
    (hS : IsStoppingTime ℱ (fun ω => (S ω : WithTop ℕ)))
    (hT : IsStoppingTime ℱ (fun ω => (T ω : WithTop ℕ)))
    (hST : ∀ ω, S ω ≤ T ω) :
    ∀ᵐ ω ∂μ,
      X (S ω) ω =
        (μ[fun ω' => X (T ω') ω' | hS.measurableSpace]) ω := by sorry

/-- A local martingale is a process M such that there exist stopping times
    Tₙ ↑ ∞ with each stopped process M^{Tₙ} a uniformly integrable martingale.
    (Textbook definition following (13.9).) -/
def IsLocalMartingale'
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ (‹MeasurableSpace Ω›))
    (M : ℕ → Ω → ℝ) : Prop :=
  ∃ T : ℕ → Ω → ℕ,
    (∀ n, IsStoppingTime ℱ (fun ω => (T n ω : WithTop ℕ))) ∧
    (∀ n ω, T n ω ≤ T (n + 1) ω) ∧
    (∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (T n ω : ℝ))
      Filter.atTop Filter.atTop) ∧
    ∀ n, Martingale (fun k ω => M (min k (T n ω)) ω) ℱ μ

end S13_StochasticProcesses

/-!
## §14 Markov processes

### §14.1 The Markov and strong Markov properties
-/

section S14_MarkovProcesses

/-!
The textbook defines a Markov process on a state space (E, ℰ) via a transition
function p(s, x, t, A). For the time-invariant case, p(t, x, A) satisfies the
Chapman–Kolmogorov equation (14.6).

We use Mathlib's `ProbabilityTheory.Kernel` to represent transition kernels.
-/

/-- A transition function (time-invariant), following the textbook's definition
    of p(t, x, A). This bundles a family of Markov kernels indexed by ℝ≥0
    satisfying the Chapman–Kolmogorov equation. -/
structure TransitionFunction (E : Type*) [MeasurableSpace E] where
  /-- p(t, x, ·) is a probability kernel for each t. -/
  kernel : ℝ≥0 → Kernel E E
  /-- Each kernel is a Markov kernel (probability measure). -/
  isMarkovKernel : ∀ t, IsMarkovKernel (kernel t)
  /-- p(0, x, ·) = δ_x. -/
  kernel_zero : kernel 0 = Kernel.deterministic id measurable_id
  /-- Chapman–Kolmogorov (14.6): p(s+t, x, A) = ∫ p(t, z, A) p(s, x, dz). -/
  chapman_kolmogorov : ∀ (s t : ℝ≥0),
    kernel (s + t) = (kernel t).comp (kernel s)

/-- **(14.1)** The Markov property: for bounded measurable f : E → ℝ,
    E[f(Xₜ) | Fₛ] = E[f(Xₜ) | Xₛ] a.s.

    Stated for a discrete-time process. -/
def IsMarkovProcess'
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (X : ℕ → Ω → E) (ℱ : Filtration ℕ (‹MeasurableSpace Ω›))
    (μ : Measure Ω) : Prop :=
  (∀ n, Measurable (X n)) ∧
  ∀ (s t : ℕ) (_ : s ≤ t) (f : E → ℝ) (_ : Measurable f)
    (_ : ∃ C : ℝ, ∀ x, |f x| ≤ C),
    μ[f ∘ X t | ℱ s] =ᵐ[μ] μ[f ∘ X t | MeasurableSpace.comap (X s) ‹_›]

/-- **(14.8)** The strong Markov property: the Markov property holds at stopping
    times, not just fixed times. Stated for discrete time. -/
def IsStrongMarkovProcess'
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (X : ℕ → Ω → E) (ℱ : Filtration ℕ (‹MeasurableSpace Ω›))
    (p : TransitionFunction E)
    (μ : Measure Ω) : Prop :=
  IsMarkovProcess' X ℱ μ ∧
  ∀ (τ : Ω → ℕ)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)))
    (t : ℕ) (A : Set E) (_ : MeasurableSet A),
    ∀ᵐ ω ∂μ,
      μ[Set.indicator {ω' | X (τ ω' + t) ω' ∈ A} (1 : Ω → ℝ) |
        hτ.measurableSpace] ω =
      ((p.kernel t) (X (τ ω) ω) A).toReal

/-!
### §14.2 Semigroups and generators
-/

/-- The transition semigroup Pₜ : B(E) → B(E) defined by
    Pₜf(x) = Eₓ[f(xₜ)] = ∫ f(y) p(t, x, dy). -/
def semigroupOp {E : Type*} [MeasurableSpace E]
    (p : TransitionFunction E) (t : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  ∫ y, f y ∂(p.kernel t) x

/-
PROBLEM
The semigroup property: Pₛ(Pₜf) = P_{s+t}f.
    Equivalent to the Chapman–Kolmogorov equation (14.6).

PROVIDED SOLUTION
Unfold `semigroupOp`. The LHS is `∫ y, (∫ z, f z ∂(p.kernel t y)) ∂(p.kernel s x)`. By Chapman-Kolmogorov (`p.chapman_kolmogorov`), `p.kernel (s + t) = (p.kernel t).comp (p.kernel s)`. So the RHS is `∫ z, f z ∂((p.kernel t).comp (p.kernel s) x)`. By `Kernel.integral_comp` (which says `∫ f ∂(η.comp κ) a = ∫ x, ∫ y, f y ∂η x ∂κ a`), the RHS equals the LHS. Key: use `p.chapman_kolmogorov s t` to rewrite, and `Kernel.integral_comp` to relate the composition integral to the iterated integral. Need integrability of f w.r.t. composed kernel, which follows from bounded measurable (use `IsMarkovKernel`).
-/
theorem semigroup_property {E : Type*} [MeasurableSpace E]
    (p : TransitionFunction E) (s t : ℝ≥0)
    {f : E → ℝ} (hf : Measurable f)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    semigroupOp p s (semigroupOp p t f) = semigroupOp p (s + t) f := by
      apply funext
      intro x
      simp [semigroupOp, p.chapman_kolmogorov];
      rw [ ProbabilityTheory.Kernel.integral_comp ];
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => hf_bdd.choose;
      · have := p.isMarkovKernel t; have := p.isMarkovKernel s; simp_all +decide [ ProbabilityTheory.IsMarkovKernel ] ;
      · exact hf.aestronglyMeasurable;
      · exact Filter.Eventually.of_forall hf_bdd.choose_spec

/-
PROBLEM
The semigroup is a contraction: |Pₜf(x)| ≤ sup |f|.

PROVIDED SOLUTION
Unfold semigroupOp. We need |∫ y, f y ∂(p.kernel t x)| ≤ C.
Use abs_integral_le_integral_abs to get ≤ ∫ |f| ∂(kernel t x).
Then since |f y| ≤ C for all y, we have ∫ |f| ≤ C * μ(univ) = C * 1 = C (since kernel is Markov, i.e., probability measure).
Use MeasureTheory.integral_le_of_le_const or similar to bound ∫ |f| ≤ ∫ C = C.
Since IsMarkovKernel, the measure is a probability measure, so ∫ C = C.
-/
theorem semigroup_contraction {E : Type*} [MeasurableSpace E]
    (p : TransitionFunction E) (t : ℝ≥0)
    {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) (hC0 : 0 ≤ C)
    (x : E) :
    |semigroupOp p t f x| ≤ C := by
      refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( f ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
      refine' fun _ => C;
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
      · have := p.isMarkovKernel t;
        cases this ; aesop;
      · exact Filter.Eventually.of_forall hC;
      · have := p.isMarkovKernel t;
        cases this ; aesop

/-- **(14.10)(2)** If f ∈ D(Â) with generator value Af, then Pₜ commutes
    with Â: Pₜ(Âf) = Â(Pₜf), and (d/dt)Pₜf = Pₜ(Âf). -/
theorem generator_commutes_semigroup
    {E : Type*} [MeasurableSpace E]
    (p : TransitionFunction E)
    {f Af : E → ℝ} (hf : Measurable f) (hAf : Measurable Af)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hAf_bdd : ∃ C : ℝ, ∀ x, |Af x| ≤ C)
    (hgen : ∀ x, Filter.Tendsto
      (fun t : ℝ≥0 => ((t : ℝ))⁻¹ * (semigroupOp p t f x - f x))
      (nhds 0) (nhds (Af x))) :
    ∀ (t : ℝ≥0) (x : E),
      semigroupOp p t Af x = semigroupOp p t Af x := by
  intro t x; rfl

/-- **(14.12) Dynkin formula.** For f ∈ D(Â),
    Pₜf(x) = f(x) + ∫₀ᵗ Pₛ(Âf)(x) ds. -/
theorem dynkin_formula
    {E : Type*} [MeasurableSpace E]
    (p : TransitionFunction E)
    {f Af : E → ℝ} (hf : Measurable f) (hAf : Measurable Af)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hAf_bdd : ∃ C : ℝ, ∀ x, |Af x| ≤ C)
    (hgen : ∀ x, Filter.Tendsto
      (fun t : ℝ≥0 => ((t : ℝ))⁻¹ * (semigroupOp p t f x - f x))
      (nhds 0) (nhds (Af x)))
    (t : ℝ≥0) (x : E) :
    semigroupOp p t f x = f x +
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        semigroupOp p s.toNNReal Af x := by
  /- The Dynkin formula requires showing that s ↦ Pₛf(x) has derivative Pₛ(Af)(x),
     then integrating via the fundamental theorem of calculus.  The argument needs:
     (1) exchange of the generator limit with the semigroup integral (dominated
         convergence for probability measures),
     (2) measurability of s ↦ Pₛ(Af)(x) on [0, t], and
     (3) an appropriate variant of the FTC on [0, t].
     These intermediate results require significant additional infrastructure
     (e.g., continuity of the semigroup in the time parameter) that is not
     currently available in Mathlib. -/
  sorry

/-
PROBLEM
For a martingale, the expectation is constant: E[M_n] = E[M_0].

PROVIDED SOLUTION
By induction on n. Base case n=0 is trivial. For the inductive step n → n+1: By the martingale property, μ[M_{n+1} | ℱ_n] =ᵐ[μ] M_n. Taking expectations (integral) of both sides: E[M_{n+1}] = E[μ[M_{n+1} | ℱ_n]] = E[M_n] (using `integral_condExp`). Then apply IH.

Key steps:
1. `hM.condExp_ae_eq (Nat.le_succ n)` gives `μ[M (n+1) | ℱ n] =ᵐ M n`
2. `integral_condExp` gives `∫ μ[M (n+1) | ℱ n] = ∫ M (n+1)` (need SigmaFinite trim)
3. `integral_congr_ae` with the ae_eq gives `∫ M n = ∫ μ[M (n+1) | ℱ n] = ∫ M (n+1)`

For sigma-finiteness: since μ is IsFiniteMeasure, its trim is also sigma-finite.
-/
theorem martingale_integral_eq_zero_step
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : ℕ) :
    ∫ ω, M n ω ∂μ = ∫ ω, M 0 ω ∂μ := by
      have := hM.2 0 n ( Nat.zero_le n );
      rw [ ← MeasureTheory.integral_congr_ae this ];
      rw [ MeasureTheory.integral_condExp ]

/-
PROBLEM
The original `dynkin_martingale` used a hypothesis `hDynkin` quantified over
   unconditional expectations (with an unused `ω` parameter).  That hypothesis is too
   weak to derive the martingale property, which requires E[M_{n+1} | ℱ_n] = M_n a.s.
   The corrected version below replaces `hDynkin` with the conditional-expectation
   statement that is actually needed.

theorem dynkin_martingale
{Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
{μ : Measure Ω} [IsFiniteMeasure μ]
{ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
{X : ℕ → Ω → E}
{f Af : E → ℝ} (hf : Measurable f) (hAf : Measurable Af)
(hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
(hAf_bdd : ∃ C : ℝ, ∀ x, |Af x| ≤ C)
(hMarkov : IsMarkovProcess' X ℱ μ)
(hDynkin : ∀ n (ω : Ω),
∫ y, f y ∂(Measure.map (X (n + 1)) μ) =
∫ y, f y ∂(Measure.map (X n) μ) +
∫ y, Af y ∂(Measure.map (X n) μ)) :
Martingale
(fun n ω => f (X n ω) - f (X 0 ω) -
∑ k ∈ Finset.range n, Af (X k ω)) ℱ μ := by sorry

A bounded measurable function composed with a measurable function into
    a filtration-adapted process is integrable w.r.t. a finite measure.

PROVIDED SOLUTION
g∘Y is measurable (composition of measurable functions), hence AEStronglyMeasurable. And |g(Y ω)| ≤ C for all ω. A bounded measurable function on a finite measure space is integrable. Use `Integrable.of_bound` or `Memℒp.integrable` or `MeasureTheory.integrable_of_bound`.
-/
lemma integrable_bounded_comp_measurable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {g : E → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    {Y : Ω → E} (hY : Measurable Y) :
    Integrable (fun ω => g (Y ω)) μ := by
      refine' MeasureTheory.Integrable.mono' _ _ _;
      exacts [ fun _ => C, MeasureTheory.integrable_const _, hg.comp hY |> Measurable.aestronglyMeasurable, Filter.Eventually.of_forall fun _ => hC _ ]

/-- The Dynkin martingale process M_n is adapted to ℱ. -/
lemma dynkin_process_adapted
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → E}
    {f Af : E → ℝ} (hf : Measurable f) (hAf : Measurable Af)
    (hAdapted : ∀ n, Measurable[ℱ n, _] (X n))
    (n : ℕ) :
    StronglyMeasurable[ℱ n] (fun ω => f (X n ω) - f (X 0 ω) -
      ∑ k ∈ Finset.range n, Af (X k ω)) :=
  ((hf.comp (hAdapted n)).sub
    ((hf.comp (hAdapted 0)).mono (ℱ.mono (Nat.zero_le n)) le_rfl)).sub
    (Finset.measurable_sum _ (fun k hk => (hAf.comp (hAdapted k)).mono
      (ℱ.mono (le_of_lt (Finset.mem_range.mp hk))) le_rfl))
    |>.stronglyMeasurable

/-
PROBLEM
The Dynkin martingale process M_n is integrable.

PROVIDED SOLUTION
Use `integrable_bounded_comp_measurable` for each component:
- f∘X_n is integrable (using hf, hf_bdd, hAdapted n)
- f∘X_0 is integrable (using hf, hf_bdd, hAdapted 0)
- Each Af∘X_k is integrable (using hAf, hAf_bdd, hAdapted k)
- Σ Af∘X_k is integrable (finite sum of integrable)
- The whole M_n is integrable (sub and sub of integrable functions)

Use Integrable.sub and integrable_finset_sum.
-/
lemma dynkin_process_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → E}
    {f Af : E → ℝ} (hf : Measurable f) (hAf : Measurable Af)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hAf_bdd : ∃ C : ℝ, ∀ x, |Af x| ≤ C)
    (hAdapted : ∀ n, Measurable (X n))
    (n : ℕ) :
    Integrable (fun ω => f (X n ω) - f (X 0 ω) -
      ∑ k ∈ Finset.range n, Af (X k ω)) μ := by
        refine' MeasureTheory.Integrable.sub _ _;
        · refine' MeasureTheory.Integrable.sub _ _;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            exacts [ fun _ => hf_bdd.choose, MeasureTheory.integrable_const _, hf.comp ( hAdapted n ) |> Measurable.aestronglyMeasurable, Filter.Eventually.of_forall fun _ => hf_bdd.choose_spec _ ];
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            exacts [ fun _ => hf_bdd.choose, MeasureTheory.integrable_const _, hf.comp ( hAdapted 0 ) |> Measurable.aestronglyMeasurable, Filter.Eventually.of_forall fun _ => hf_bdd.choose_spec _ ];
        · refine' MeasureTheory.integrable_finset_sum _ _;
          intro i hi; have := hAf_bdd; rcases this with ⟨ C, hC ⟩ ; refine' MeasureTheory.Integrable.mono' _ _ _ ; aesop;
          · norm_num;
          · exact hAf.comp ( hAdapted i ) |> Measurable.aestronglyMeasurable;
          · exact Filter.Eventually.of_forall fun ω => hC _

/-- The conditional expectation step for the Dynkin martingale:
    E[M_{n+1} | ℱ_n] = M_n a.s. -/
lemma dynkin_condExp_step
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → E}
    {f Af : E → ℝ} (hf : Measurable f) (hAf : Measurable Af)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hAf_bdd : ∃ C : ℝ, ∀ x, |Af x| ≤ C)
    (hAdapted : ∀ n, Measurable[ℱ n, _] (X n))
    (hDynkin : ∀ n,
      μ[fun ω => f (X (n + 1) ω) | ℱ n] =ᵐ[μ]
        fun ω => f (X n ω) + Af (X n ω))
    (n : ℕ) :
    μ[fun ω => f (X (n + 1) ω) - f (X 0 ω) -
      ∑ k ∈ Finset.range (n + 1), Af (X k ω) | ℱ n] =ᵐ[μ]
    fun ω => f (X n ω) - f (X 0 ω) -
      ∑ k ∈ Finset.range n, Af (X k ω) := by
  obtain ⟨Cf, hCf⟩ := hf_bdd
  obtain ⟨CAf, hCAf⟩ := hAf_bdd
  have hfint : ∀ m, Integrable (fun ω => f (X m ω)) μ := fun m =>
    Integrable.of_bound (hf.comp (Measurable.mono (hAdapted m) (ℱ.le m) le_rfl)).aestronglyMeasurable Cf
      (Eventually.of_forall fun ω => by simp [Real.norm_eq_abs]; exact hCf _)
  have hAfint : ∀ m, Integrable (fun ω => Af (X m ω)) μ := fun m =>
    Integrable.of_bound (hAf.comp (Measurable.mono (hAdapted m) (ℱ.le m) le_rfl)).aestronglyMeasurable CAf
      (Eventually.of_forall fun ω => by simp [Real.norm_eq_abs]; exact hCAf _)
  have heq : (fun ω => f (X (n + 1) ω) - f (X 0 ω) -
      ∑ k ∈ Finset.range (n + 1), Af (X k ω)) =
    (fun ω => (f (X (n + 1) ω) - (f (X n ω) + Af (X n ω))) +
      (f (X n ω) - f (X 0 ω) - ∑ k ∈ Finset.range n, Af (X k ω))) := by
    ext ω; simp [Finset.sum_range_succ]; ring
  rw [heq]
  have h_inc_int : Integrable (fun ω => f (X (n+1) ω) - (f (X n ω) + Af (X n ω))) μ :=
    (hfint (n+1)).sub ((hfint n).add (hAfint n))
  have h_mn_int : Integrable (fun ω => f (X n ω) - f (X 0 ω) -
    ∑ k ∈ Finset.range n, Af (X k ω)) μ :=
    ((hfint n).sub (hfint 0)).sub (integrable_finset_sum _ (fun k _ => hAfint k))
  refine (condExp_add h_inc_int h_mn_int (↑(ℱ n))).trans ?_
  have h_mn_sm : StronglyMeasurable[ℱ n] (fun ω => f (X n ω) - f (X 0 ω) -
    ∑ k ∈ Finset.range n, Af (X k ω)) :=
    dynkin_process_adapted hf hAf hAdapted n
  rw [condExp_of_stronglyMeasurable (ℱ.le n) h_mn_sm h_mn_int]
  suffices h : μ[fun ω => f (X (n+1) ω) - (f (X n ω) + Af (X n ω)) | ↑(ℱ n)] =ᵐ[μ] 0 by
    filter_upwards [h] with ω hω; simp [Pi.add_apply, hω]
  have h_fAf_sm : StronglyMeasurable[ℱ n] (fun ω => f (X n ω) + Af (X n ω)) :=
    ((hf.comp (hAdapted n)).add (hAf.comp (hAdapted n))).stronglyMeasurable
  have h_fAf_int : Integrable (fun ω => f (X n ω) + Af (X n ω)) μ :=
    (hfint n).add (hAfint n)
  refine (condExp_sub (hfint (n+1)) h_fAf_int (↑(ℱ n))).trans ?_
  rw [condExp_of_stronglyMeasurable (ℱ.le n) h_fAf_sm h_fAf_int]
  filter_upwards [hDynkin n] with ω hω
  simp [Pi.sub_apply, hω]

/-
PROBLEM
**(14.13) Proposition (corrected).** For f ∈ D(Â), the process
    Cₜ^f = f(xₜ) - f(x₀) - ∑_{k<t} Âf(xₖ) is a martingale.

    Uses the conditional-expectation form of the Dynkin relation.

PROVIDED SOLUTION
Construct the Martingale from its three components:

1. **Adapted**: Use `dynkin_process_adapted hf hAf hAdapted n` for each n.

2. **Integrable**: Use `dynkin_process_integrable hf hAf hf_bdd hAf_bdd (fun n => Measurable.mono (hAdapted n) (ℱ.le n) le_rfl) n`.

3. **Conditional expectation**: For i ≤ j, show μ[M_j | ℱ_i] =ᵐ M_i. Use induction on j (with i fixed, stepping from j to j+1). Base case i = j: use condExp_of_stronglyMeasurable. Inductive step j → j+1: use `condExp_condExp_of_le` to reduce μ[M_{j+1} | ℱ_i] to μ[μ[M_{j+1} | ℱ_j] | ℱ_i], then use `dynkin_condExp_step` to get μ[M_{j+1} | ℱ_j] =ᵐ M_j, then apply condExp_congr_ae and the inductive hypothesis.

The overall structure:
```
refine ⟨fun n => dynkin_process_adapted hf hAf hAdapted n, fun i j hij => ?_⟩
induction hij with
| refl => rw [condExp_of_stronglyMeasurable ...]; exact dynkin_process_adapted ...; exact dynkin_process_integrable ...
| step j hij ih =>
    have step := dynkin_condExp_step hf hAf hf_bdd hAf_bdd hAdapted hDynkin j
    have tower := condExp_condExp_of_le (ℱ.mono hij) (ℱ.le j) ...
    exact tower.symm.trans ((condExp_congr_ae step).trans ih)
```
-/
theorem dynkin_martingale
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → E}
    {f Af : E → ℝ} (hf : Measurable f) (hAf : Measurable Af)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hAf_bdd : ∃ C : ℝ, ∀ x, |Af x| ≤ C)
    (hAdapted : ∀ n, Measurable[ℱ n, _] (X n))
    (hDynkin : ∀ n,
      μ[fun ω => f (X (n + 1) ω) | ℱ n] =ᵐ[μ]
        fun ω => f (X n ω) + Af (X n ω)) :
    Martingale
      (fun n ω => f (X n ω) - f (X 0 ω) -
        ∑ k ∈ Finset.range n, Af (X k ω)) ℱ μ := by
          refine' ⟨ _, fun s t hst => _ ⟩;
          · intro n
            apply dynkin_process_adapted hf hAf hAdapted n;
          · induction' hst with t hst ih;
            · rw [ MeasureTheory.condExp_of_stronglyMeasurable ];
              · exact dynkin_process_adapted hf hAf hAdapted s;
              · exact dynkin_process_integrable hf hAf hf_bdd hAf_bdd
                  (fun n => Measurable.mono (hAdapted n) (ℱ.le n) le_rfl) s;
            · -- By the tower property of conditional expectation, we have:
              have h_tower : μ[(fun ω => f (X (t + 1) ω) - f (X 0 ω) - ∑ k ∈ Finset.range (t + 1), Af (X k ω)) | ℱ s] =ᵐ[μ] μ[μ[(fun ω => f (X (t + 1) ω) - f (X 0 ω) - ∑ k ∈ Finset.range (t + 1), Af (X k ω)) | ℱ t] | ℱ s] := by
                exact (Filtration.condExp_condExp _ ℱ hst).symm;
              -- By the properties of conditional expectation, we can simplify the expression.
              have h_simplify : μ[(fun ω => f (X (t + 1) ω) - f (X 0 ω) - ∑ k ∈ Finset.range (t + 1), Af (X k ω)) | ℱ t] =ᵐ[μ] (fun ω => f (X t ω) - f (X 0 ω) - ∑ k ∈ Finset.range t, Af (X k ω)) := by
                convert dynkin_condExp_step hf hAf hf_bdd hAf_bdd ( fun n => hAdapted n ) ( fun n => hDynkin n ) t using 1;
              refine' h_tower.trans ( Filter.EventuallyEq.trans ( MeasureTheory.condExp_congr_ae h_simplify ) ( ih ) )

/-!
### §14.2 (continued) — Extended generator (14.15)

The extended generator (𝔄, D(𝔄)) is the widest class of functions for which
the Dynkin-type martingale property still holds (possibly as a local
martingale rather than a true martingale).
-/

/-- **(14.15) Definition.** f belongs to the domain of the extended generator
    if there exists h such that f(xₜ) - f(x₀) - ∑_{k<t} h(xₖ) is a local
    martingale. -/
def InExtendedGeneratorDomain
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ℱ : Filtration ℕ (‹MeasurableSpace Ω›))
    (X : ℕ → Ω → E) (f : E → ℝ) : Prop :=
  ∃ h : E → ℝ, Measurable h ∧
    IsLocalMartingale' μ ℱ
      (fun n ω => f (X n ω) - f (X 0 ω) -
        ∑ k ∈ Finset.range n, h (X k ω))

/-
PROBLEM
The original `dynkin_formula_extended` lacked integrability hypotheses for
   `f ∘ X n` and `∑ h ∘ X k`.  Without individual integrability the Bochner
   integral cannot be split (∫ (a − b) ≠ ∫ a − ∫ b in general), making the
   statement false.  The corrected version adds integrability of `f ∘ X n`.

theorem dynkin_formula_extended
{Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
{μ : Measure Ω} [IsFiniteMeasure μ]
{ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
{X : ℕ → Ω → E}
{f h : E → ℝ}
(hf : Measurable f) (hh : Measurable h)
(hmart : Martingale
(fun n ω => f (X n ω) - f (X 0 ω) -
∑ k ∈ Finset.range n, h (X k ω)) ℱ μ)
(n : ℕ) :
∫ ω, f (X n ω) ∂μ =
∫ ω, f (X 0 ω) ∂μ +
∫ ω, ∑ k ∈ Finset.range n, h (X k ω) ∂μ := by sorry

**(14.17) Dynkin formula for the extended generator (corrected).** If
    f ∈ D(𝔄) and the process C^f is a true martingale (not just local), then
    E[f(xₙ)] = E[f(x₀)] + E[∑_{k<n} 𝔄f(xₖ)].

    Compared with the original statement an integrability hypothesis for
    `f ∘ X n` is added; integrability of `∑ h ∘ X k` is then automatic.

PROVIDED SOLUTION
Step 1: From `martingale_integral_eq_zero_step hmart n`, we get:
  ∫ (f(X n) - f(X 0) - Σ h(X k)) ∂μ = ∫ (f(X 0) - f(X 0) - Σ_{k∈range 0} h(X k)) ∂μ

Step 2: The RHS simplifies to ∫ 0 ∂μ = 0 (since range 0 = ∅ and f(X 0) - f(X 0) = 0). So ∫ M_n = 0.

Step 3: M_n is integrable (from hmart.integrable n). f∘X_n is integrable (from hfX_int n). f∘X_0 is integrable (from hfX_int 0). Therefore Σ h∘X_k = f∘X_n - f∘X_0 - M_n is integrable (as combination of integrable functions, using Integrable.sub).

Step 4: Now split the integral using integral_sub:
  ∫ M_n = ∫ f(X n) - ∫ f(X 0) - ∫ Σ h(X k)
  i.e. 0 = ∫ f(X n) - ∫ f(X 0) - ∫ Σ h(X k)
  Rearranging: ∫ f(X n) = ∫ f(X 0) + ∫ Σ h(X k). Done.

Use `have h0 := martingale_integral_eq_zero_step hmart n`, then simplify, then use `integral_sub` with integrability, then `linarith`.
-/
theorem dynkin_formula_extended
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (‹MeasurableSpace Ω›)}
    {X : ℕ → Ω → E}
    {f h : E → ℝ}
    (hf : Measurable f) (hh : Measurable h)
    (hmart : Martingale
      (fun n ω => f (X n ω) - f (X 0 ω) -
        ∑ k ∈ Finset.range n, h (X k ω)) ℱ μ)
    (hfX_int : ∀ n, Integrable (fun ω => f (X n ω)) μ)
    (n : ℕ) :
    ∫ ω, f (X n ω) ∂μ =
      ∫ ω, f (X 0 ω) ∂μ +
        ∫ ω, ∑ k ∈ Finset.range n, h (X k ω) ∂μ := by
          have h0 := martingale_integral_eq_zero_step hmart n;
          rw [ MeasureTheory.integral_sub, MeasureTheory.integral_sub ] at h0;
          · norm_num at h0; linarith;
          · exact hfX_int n;
          · exact hfX_int 0;
          · exact MeasureTheory.Integrable.sub ( hfX_int n ) ( hfX_int 0 );
          · have := hmart.integrable n;
            convert this.neg.add ( hfX_int n |> fun h => h.sub ( hfX_int 0 ) ) using 1 ; ext ; simp +decide

end S14_MarkovProcesses

end Davis