/-
  Davis (1993), "Markov Models and Optimization", Chapter 2.

  # §25.5 — the strong Markov property for *arbitrary* stopping times

  `SHSLib/Foundations/DavisCh2.lean` proves the strong Markov property for
  stopping times with countably many values
  (`Davis.pdp_strong_markov_of_countable_range`).  This file removes the
  countability restriction by the classical dyadic discretisation

      τₙ := (⌊τ·2ⁿ⌋ + 1)/2ⁿ  ↓  τ,      τ < τₙ ≤ τ + 2⁻ⁿ,

  each `τₙ` being a stopping time with countably many values, and then passing
  to the limit using right continuity of the paths and continuity of `f` and of
  `Pₛf`.

  The file contains three groups of results.

  * **Dyadic upper approximation** (`dyadicUpper` and its basic properties,
    `isStoppingTime_dyadicUpper`): reusable discretisation machinery for
    `ℝ≥0`-indexed stopping times.
  * **Measurability at a stopping time**
    (`measurable_apply_stoppingTime_of_countable_range`,
    `measurable_apply_stoppingTime_of_progMeasurable`,
    `isStoppingTime_add_const`): the two ways of obtaining
    `ℱ_τ`-measurability of `ω ↦ h (τ ω) ω`.
  * **The general strong Markov property**
    (`pdp_strong_markov_of_rightContinuous`).
-/

import SHSLib.Foundations.DavisCh2

open MeasureTheory Topology Filter Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Davis

section DyadicUpper

/-- The `n`-th **dyadic upper approximation** of `t : ℝ≥0`:
`dyadicUpper n t = (⌊t·2ⁿ⌋ + 1)/2ⁿ`, the smallest dyadic rational of level `n`
that is strictly larger than `t`. -/
def dyadicUpper (n : ℕ) (t : ℝ≥0) : ℝ≥0 := (⌊t * 2 ^ n⌋₊ + 1) / 2 ^ n

/-- The dyadic upper approximation is strictly larger than the point it
approximates. -/
lemma lt_dyadicUpper (n : ℕ) (t : ℝ≥0) : t < dyadicUpper n t := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  rw [dyadicUpper, lt_div_iff₀ h2]
  exact_mod_cast Nat.lt_floor_add_one (t * 2 ^ n)

/-- The dyadic upper approximation overshoots by at most `2⁻ⁿ`. -/
lemma dyadicUpper_le_add (n : ℕ) (t : ℝ≥0) : dyadicUpper n t ≤ t + ((2 : ℝ≥0) ^ n)⁻¹ := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  rw [dyadicUpper, div_le_iff₀ h2, add_mul, inv_mul_cancel₀ h2.ne']
  gcongr
  exact Nat.floor_le (zero_le _)

/-- Comparison of `dyadicUpper n t` with an arbitrary threshold `u`. -/
lemma dyadicUpper_le_iff (n : ℕ) (t u : ℝ≥0) :
    dyadicUpper n t ≤ u ↔ t < (⌊u * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  rw [dyadicUpper, div_le_iff₀ h2, lt_div_iff₀ h2]
  constructor
  · intro h
    have h1 : ((⌊t * 2 ^ n⌋₊ + 1 : ℕ) : ℝ≥0) ≤ u * 2 ^ n := by push_cast; exact h
    exact (Nat.floor_lt (zero_le _)).mp (Nat.le_floor h1)
  · intro h
    have h3 : ⌊t * 2 ^ n⌋₊ < ⌊u * 2 ^ n⌋₊ := (Nat.floor_lt (zero_le _)).mpr h
    have h4 : ((⌊t * 2 ^ n⌋₊ + 1 : ℕ) : ℝ≥0) ≤ ((⌊u * 2 ^ n⌋₊ : ℕ) : ℝ≥0) := by exact_mod_cast h3
    calc ((⌊t * 2 ^ n⌋₊ : ℝ≥0) + 1) = ((⌊t * 2 ^ n⌋₊ + 1 : ℕ) : ℝ≥0) := by push_cast; ring
      _ ≤ ((⌊u * 2 ^ n⌋₊ : ℕ) : ℝ≥0) := h4
      _ ≤ u * 2 ^ n := Nat.floor_le (zero_le _)

/-- The dyadic *lower* rounding of `u` never exceeds `u`. -/
lemma dyadicFloor_le (n : ℕ) (u : ℝ≥0) : (⌊u * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n ≤ u := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2]
  exact Nat.floor_le (zero_le _)

lemma measurable_dyadicUpper (n : ℕ) : Measurable (dyadicUpper n) := by
  unfold dyadicUpper
  fun_prop

/-- `dyadicUpper n` takes values in the countable set of level-`n` dyadic
rationals. -/
lemma dyadicUpper_mem_range (n : ℕ) (t : ℝ≥0) :
    dyadicUpper n t ∈ (Set.range fun k : ℕ => ((k : ℝ≥0) + 1) / 2 ^ n) :=
  ⟨⌊t * 2 ^ n⌋₊, rfl⟩

lemma countable_dyadicRange (n : ℕ) :
    (Set.range fun k : ℕ => ((k : ℝ≥0) + 1) / 2 ^ n).Countable := Set.countable_range _

/-- `dyadicUpper n t → t` as `n → ∞`. -/
lemma tendsto_dyadicUpper (t : ℝ≥0) :
    Tendsto (fun n => dyadicUpper n t) atTop (nhds t) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => t)
    (h := fun n => t + ((2 : ℝ≥0) ^ n)⁻¹) tendsto_const_nhds ?_
    (fun n => (lt_dyadicUpper n t).le) (fun n => dyadicUpper_le_add n t)
  have h : Tendsto (fun n : ℕ => ((2 : ℝ≥0) ^ n)⁻¹) atTop (nhds 0) := by
    simp only [← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using tendsto_const_nhds.add h

/-- `dyadicUpper n t → t` *from the right*: the approximations converge to `t`
inside `Set.Ioi t`. -/
lemma tendsto_dyadicUpper_nhdsWithin (t : ℝ≥0) :
    Tendsto (fun n => dyadicUpper n t) atTop (nhdsWithin t (Set.Ioi t)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_dyadicUpper t)
    (Filter.Eventually.of_forall (fun n => lt_dyadicUpper n t))

/-- The dyadic upper approximation of a stopping time is a stopping time. -/
lemma isStoppingTime_dyadicUpper {Omega : Type*} [m0 : MeasurableSpace Omega]
    {ℱ : Filtration ℝ≥0 m0} {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞))) (n : ℕ) :
    IsStoppingTime ℱ (fun omega => ((dyadicUpper n (tau omega) : ℝ≥0) : ℝ≥0∞)) := by
  intro u
  have hset : {omega | ((dyadicUpper n (tau omega) : ℝ≥0) : ℝ≥0∞) ≤ (u : ℝ≥0∞)}
      = {omega | ((tau omega : ℝ≥0) : ℝ≥0∞) < (((⌊u * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ≥0∞)} := by
    ext omega
    simp only [Set.mem_setOf_eq, ENNReal.coe_le_coe, ENNReal.coe_lt_coe]
    exact dyadicUpper_le_iff n (tau omega) u
  exact hset ▸ htau.measurableSet_lt_le (dyadicFloor_le n u)

/-- Shifting an `ℝ≥0`-valued stopping time by a constant gives a stopping
time. -/
lemma isStoppingTime_add_const {Omega : Type*} [m0 : MeasurableSpace Omega]
    {ℱ : Filtration ℝ≥0 m0} {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞))) (s : ℝ≥0) :
    IsStoppingTime ℱ (fun omega => ((tau omega + s : ℝ≥0) : ℝ≥0∞)) := by
  intro u
  by_cases hs : s ≤ u
  · have hset : {omega | ((tau omega + s : ℝ≥0) : ℝ≥0∞) ≤ (u : ℝ≥0∞)}
        = {omega | ((tau omega : ℝ≥0) : ℝ≥0∞) ≤ ((u - s : ℝ≥0) : ℝ≥0∞)} := by
      ext omega
      simp only [Set.mem_setOf_eq, ENNReal.coe_le_coe]
      constructor
      · intro h; exact le_tsub_of_add_le_right h
      · intro h; exact add_le_of_le_tsub_right_of_le hs h
    exact hset ▸ ℱ.mono tsub_le_self _ (htau (u - s))
  · have hset : {omega | ((tau omega + s : ℝ≥0) : ℝ≥0∞) ≤ (u : ℝ≥0∞)} = (∅ : Set Omega) := by
      ext omega
      simp only [Set.mem_setOf_eq, ENNReal.coe_le_coe, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.mp hs) le_add_self
    exact hset ▸ @MeasurableSet.empty _ (ℱ u)

end DyadicUpper

section MeasurabilityAtStoppingTime

/-- If `τ` is a stopping time with countably many values and `h u` is
`ℱ u`-measurable for every `u`, then `ω ↦ h (τ ω) ω` is `ℱ_τ`-measurable. -/
theorem measurable_apply_stoppingTime_of_countable_range
    {Omega : Type*} [m0 : MeasurableSpace Omega]
    {ℱ : Filtration ℝ≥0 m0} {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (S : Set ℝ≥0) (hS : S.Countable) (hrange : ∀ omega, tau omega ∈ S)
    {beta : Type*} [MeasurableSpace beta]
    (h : ℝ≥0 → Omega → beta) (hmeas : ∀ u, Measurable[ℱ u] (h u)) :
    Measurable[htau.measurableSpace] (fun omega => h (tau omega) omega) := by
  classical
  intro B hB
  set D : ℝ≥0 → Set Omega := fun u => {omega | tau omega = u} ∩ (h u) ⁻¹' B with hD
  have hDmeas : ∀ u, MeasurableSet[ℱ u] (D u) := by
    intro u
    have h1 : MeasurableSet[ℱ u] {omega | tau omega = u} := by
      have hme := htau.measurableSet_eq u
      have heq : {omega | ((tau omega : ℝ≥0) : ℝ≥0∞) = (u : ℝ≥0∞)} = {omega | tau omega = u} := by
        ext omega; simp
      exact heq ▸ hme
    exact h1.inter (hmeas u hB)
  have hpre : (fun omega => h (tau omega) omega) ⁻¹' B = ⋃ u ∈ S, D u := by
    ext omega
    constructor
    · intro hx; exact Set.mem_biUnion (hrange omega) ⟨rfl, by simpa using hx⟩
    · intro hx
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨u, -, hu, hxu⟩ := hx
      have hu' : tau omega = u := hu
      simpa [hu'] using hxu
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact MeasurableSet.biUnion hS (fun u _ => ℱ.le u _ (hDmeas u))
  · intro i
    show MeasurableSet[ℱ i]
      ((fun omega => h (tau omega) omega) ⁻¹' B ∩
        {omega : Omega | ((tau omega : ℝ≥0) : ℝ≥0∞) ≤ (i : ℝ≥0∞)})
    rw [hpre, Set.iUnion₂_inter]
    refine MeasurableSet.biUnion hS (fun u _ => ?_)
    by_cases hui : u ≤ i
    · have hEq : D u ∩ {omega : Omega | ((tau omega : ℝ≥0) : ℝ≥0∞) ≤ (i : ℝ≥0∞)} = D u := by
        apply Set.inter_eq_self_of_subset_left
        rintro omega ⟨homega, -⟩
        simp only [Set.mem_setOf_eq, ENNReal.coe_le_coe]
        exact homega ▸ hui
      rw [hEq]
      exact ℱ.mono hui _ (hDmeas u)
    · have hEq : D u ∩ {omega : Omega | ((tau omega : ℝ≥0) : ℝ≥0∞) ≤ (i : ℝ≥0∞)} = ∅ := by
        ext omega
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          ENNReal.coe_le_coe, not_and]
        rintro ⟨homega, -⟩ hle
        exact hui (homega ▸ hle)
      rw [hEq]
      exact @MeasurableSet.empty _ (ℱ i)

/-- For a progressively measurable process, the value at a stopping time is
`ℱ_τ`-measurable. -/
theorem measurable_apply_stoppingTime_of_progMeasurable
    {Omega E : Type*} [m0 : MeasurableSpace Omega] [MeasurableSpace E]
    [MetricSpace E] [BorelSpace E]
    {ℱ : Filtration ℝ≥0 m0} {X : ℝ≥0 → Omega → E} {tau : Omega → ℝ≥0}
    (hX_prog : ProgMeasurable ℱ X)
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞))) :
    Measurable[htau.measurableSpace] (fun omega => X (tau omega) omega) := by
  have h := measurable_stoppedValue hX_prog htau
  have heq : stoppedValue X (fun omega => (tau omega : ℝ≥0∞))
      = fun omega => X (tau omega) omega := by
    funext omega
    have hval : WithTop.untopA ((tau omega : ℝ≥0∞)) = tau omega := NNReal.eq rfl
    simp [stoppedValue, hval]
  exact heq ▸ h

end MeasurabilityAtStoppingTime

section ProgMeasurability

/-- **Countable-valued time change.** If `r` takes countably many values and
`Y v` is measurable for each of them, then `(a, b) ↦ Y (r a) b` is measurable
for the product σ-algebra. -/
theorem measurable_uncurry_of_countable_range
    {alpha beta gamma : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    [MeasurableSpace gamma] {r : alpha → ℝ≥0} (hr : Measurable r)
    (S : Set ℝ≥0) (hS : S.Countable) (hrange : ∀ a, r a ∈ S)
    {Y : ℝ≥0 → beta → gamma} (hY : ∀ v ∈ S, Measurable (Y v)) :
    Measurable (fun p : alpha × beta => Y (r p.1) p.2) := by
  classical
  intro B hB
  have hpre : (fun p : alpha × beta => Y (r p.1) p.2) ⁻¹' B
      = ⋃ v ∈ S, ((r ⁻¹' {v}) ×ˢ ((Y v) ⁻¹' B)) := by
    ext p
    constructor
    · intro hp; exact Set.mem_biUnion (hrange p.1) ⟨rfl, by simpa using hp⟩
    · intro hp
      rw [Set.mem_iUnion₂] at hp
      obtain ⟨v, -, hv1, hv2⟩ := hp
      have hv : r p.1 = v := hv1
      simpa [hv] using hv2
  rw [hpre]
  exact MeasurableSet.biUnion hS (fun v hv => (hr (measurableSet_singleton v)).prod (hY v hv hB))

/-- **A right-continuous adapted process is progressively measurable.**

The dyadic right-endpoint approximations `Xⁿ(t, ω) = X(min (dyadicUpper n t) i, ω)`
are measurable on `Set.Iic i × Ω` (they take countably many time values, all
`≤ i`) and converge pointwise to `X(t, ω)` by right continuity of the paths.

Mathlib provides the analogous statement for *continuous* processes
(`StronglyAdapted.progMeasurable_of_continuous`); this is the càdlàg version,
which is the one needed for PDPs. -/
theorem progMeasurable_of_rightContinuous
    {Omega E : Type*} [m0 : MeasurableSpace Omega] [MeasurableSpace E] [MetricSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {ℱ : Filtration ℝ≥0 m0} {X : ℝ≥0 → Omega → E}
    (hX_adapted : ∀ u, Measurable[ℱ u] (X u))
    (hX_rc : ∀ omega, ∀ t : ℝ≥0,
      Tendsto (fun r => X r omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega))) :
    ProgMeasurable ℱ X := by
  intro i
  apply Measurable.stronglyMeasurable
  have hUmeas : ∀ n : ℕ, Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
      (fun p : Set.Iic i × Omega => X (min (dyadicUpper n (p.1 : ℝ≥0)) i) p.2) := by
    intro n
    refine @measurable_uncurry_of_countable_range (Set.Iic i) Omega E
      Subtype.instMeasurableSpace (ℱ i) _
      (fun t : Set.Iic i => min (dyadicUpper n (t : ℝ≥0)) i) ?_
      (Set.range fun k : ℕ => min (((k : ℝ≥0) + 1) / 2 ^ n) i) (Set.countable_range _) ?_
      (fun v omega => X v omega) ?_
    · exact ((measurable_dyadicUpper n).comp measurable_subtype_coe).min measurable_const
    · intro t
      obtain ⟨k, hk⟩ := dyadicUpper_mem_range n (t : ℝ≥0)
      exact ⟨k, congrArg (fun z => min z i) hk⟩
    · rintro v ⟨k, hk⟩
      exact (hX_adapted v).mono (ℱ.mono (hk ▸ min_le_right _ _)) le_rfl
  have hconv : ∀ p : Set.Iic i × Omega,
      Tendsto (fun n => X (min (dyadicUpper n (p.1 : ℝ≥0)) i) p.2) atTop
        (nhds (X (p.1 : ℝ≥0) p.2)) := by
    rintro ⟨⟨t, ht⟩, omega⟩
    rcases eq_or_lt_of_le (Set.mem_Iic.mp ht) with heq | hlt
    · have hmin : ∀ n : ℕ, min (dyadicUpper n t) i = i :=
        fun n => min_eq_right (by rw [heq]; exact (lt_dyadicUpper n i).le)
      simp only [hmin]
      rw [heq]
      exact tendsto_const_nhds
    · have hev : ∀ᶠ n in atTop, min (dyadicUpper n t) i = dyadicUpper n t :=
        ((tendsto_dyadicUpper t).eventually_lt_const hlt).mono (fun n hn => min_eq_left hn.le)
      have h1 : Tendsto (fun n => X (dyadicUpper n t) omega) atTop (nhds (X t omega)) :=
        (hX_rc omega t).comp (tendsto_dyadicUpper_nhdsWithin t)
      refine h1.congr' (hev.mono (fun n hn => ?_))
      show X (dyadicUpper n t) omega = X (min (dyadicUpper n t) i) omega
      rw [hn]
  exact @measurable_of_tendsto_metrizable (Set.Iic i × Omega) E
    (Subtype.instMeasurableSpace.prod (ℱ i)) _ _ _ _ _ _ hUmeas (tendsto_pi_nhds.mpr hconv)

end ProgMeasurability

section GeneralStrongMarkov

/-- **(25.5) Strong Markov property, general stopping times.**

If `X` is right-continuous, progressively measurable and satisfies the simple
Markov property `IsPDPMarkovProcess` for the PDP semigroup, then for *every*
stopping time `τ` and every bounded continuous `f` whose semigroup image
`Pₛ f` is continuous,

`𝔼[f(X_{τ+s}) | ℱ_τ] = (Pₛ f)(X_τ)` almost surely.

This removes the countable-range restriction in
`pdp_strong_markov_of_countable_range` by dyadic discretisation of `τ`. -/
theorem pdp_strong_markov_of_rightContinuous
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [MetricSpace E] [BorelSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E} {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_prog : ProgMeasurable ℱ X)
    (hX_rc : ∀ omega, ∀ t : ℝ≥0,
      Tendsto (fun r => X r omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    (hmarkov : IsPDPMarkovProcess P pdp ℱ X)
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    {f : E → ℝ} (hf_cont : Continuous f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C)
    (s : ℝ≥0)
    (hg_cont : Continuous (fun x => pdpSemigroup pdp s f x))
    (hg_bdd : ∀ x, |pdpSemigroup pdp s f x| ≤ C) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) := by
  classical
  set g : E → ℝ := fun x => pdpSemigroup pdp s f x with hgdef
  have hfm : Measurable f := hf_cont.measurable
  have hgm : Measurable g := hg_cont.measurable
  have hadapt : ∀ u, Measurable[ℱ u] (X u) := fun u => (hX_prog.stronglyAdapted u).measurable
  have hadapt' : ∀ u, Measurable (X u) := fun u => (hadapt u).mono (ℱ.le u) le_rfl
  have hm : htau.measurableSpace ≤ ‹MeasurableSpace Omega› := htau.measurableSpace_le
  haveI : SigmaFinite (P.trim hm) := by infer_instance
  -- the dyadic approximating stopping times
  set sigma : ℕ → Omega → ℝ≥0 := fun n omega => dyadicUpper n (tau omega) with hsigmadef
  have hsig_st : ∀ n, IsStoppingTime ℱ (fun omega => ((sigma n omega : ℝ≥0) : ℝ≥0∞)) :=
    fun n => isStoppingTime_dyadicUpper htau n
  have hsig_meas : ∀ n, Measurable (sigma n) := fun n => (measurable_dyadicUpper n).comp htau_meas
  have hsig_range : ∀ n, ∀ omega,
      sigma n omega ∈ (Set.range fun k : ℕ => ((k : ℝ≥0) + 1) / 2 ^ n) :=
    fun n omega => dyadicUpper_mem_range n (tau omega)
  have hsig_gt : ∀ n omega, tau omega < sigma n omega := fun n omega => lt_dyadicUpper n (tau omega)
  have hle : ∀ n, htau.measurableSpace ≤ (hsig_st n).measurableSpace := by
    intro n
    refine htau.measurableSpace_mono (hsig_st n) (fun omega => ?_)
    exact ENNReal.coe_le_coe.mpr (hsig_gt n omega).le
  -- integrability of the bounded pieces
  have hint_of_bdd : ∀ (h : Omega → ℝ), Measurable h → (∀ omega, |h omega| ≤ C) →
      Integrable h P := by
    intro h hh hbd
    refine Integrable.mono' (integrable_const C) hh.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun omega => ?_))
    simpa using hbd omega
  -- measurability of the approximating evaluations
  have hYn_meas : ∀ n, Measurable (fun omega => f (X (sigma n omega + s) omega)) := by
    intro n
    exact hfm.comp (measurable_apply_add_of_countable_range hadapt' (hsig_meas n) _
      (countable_dyadicRange n) (hsig_range n) s)
  have hZn_meas : ∀ n, Measurable (fun omega => g (X (sigma n omega) omega)) := by
    intro n
    have := measurable_apply_stoppingTime_of_countable_range (hsig_st n) _
      (countable_dyadicRange n) (hsig_range n) (fun u omega => g (X u omega))
      (fun u => hgm.comp (hadapt u))
    exact this.mono ((hsig_st n).measurableSpace_le) le_rfl
  -- measurability of the limiting evaluations
  have hZ_meas' : Measurable[htau.measurableSpace]
      (fun omega => g (X (tau omega) omega)) :=
    hgm.comp (measurable_apply_stoppingTime_of_progMeasurable hX_prog htau)
  have hZ_meas : Measurable (fun omega => g (X (tau omega) omega)) :=
    hZ_meas'.mono hm le_rfl
  have hY_meas : Measurable (fun omega => f (X (tau omega + s) omega)) := by
    have hst := isStoppingTime_add_const htau s
    have := hfm.comp (measurable_apply_stoppingTime_of_progMeasurable hX_prog hst)
    exact this.mono hst.measurableSpace_le le_rfl
  have hY_int : Integrable (fun omega => f (X (tau omega + s) omega)) P :=
    hint_of_bdd _ hY_meas (fun omega => hf_bdd _)
  have hZ_int : Integrable (fun omega => g (X (tau omega) omega)) P :=
    hint_of_bdd _ hZ_meas (fun omega => hg_bdd _)
  -- (1) the strong Markov property at each dyadic approximation
  have hcond : ∀ n,
      P[fun omega => f (X (sigma n omega + s) omega) | (hsig_st n).measurableSpace] =ᵐ[P]
        fun omega => g (X (sigma n omega) omega) := by
    intro n
    refine pdp_strong_markov_of_countable_range pdp hadapt' hmarkov (hsig_st n) (hsig_meas n)
      _ (countable_dyadicRange n) (hsig_range n) hfm hf_bdd s ?_ ?_
    · exact ((measurable_apply_stoppingTime_of_countable_range (hsig_st n) _
        (countable_dyadicRange n) (hsig_range n) (fun u omega => g (X u omega))
        (fun u => hgm.comp (hadapt u))).stronglyMeasurable)
    · exact hint_of_bdd _ (hZn_meas n) (fun omega => hg_bdd _)
  -- (2) the corresponding identity of set integrals over `ℱ_τ`-sets
  have hsetint : ∀ n, ∀ A, MeasurableSet[htau.measurableSpace] A →
      ∫ omega in A, f (X (sigma n omega + s) omega) ∂P
        = ∫ omega in A, g (X (sigma n omega) omega) ∂P := by
    intro n A hA
    have hA' : MeasurableSet[(hsig_st n).measurableSpace] A := hle n A hA
    have hYint : Integrable (fun omega => f (X (sigma n omega + s) omega)) P :=
      hint_of_bdd _ (hYn_meas n) (fun omega => hf_bdd _)
    have h1 : ∫ omega in A,
        (P[fun omega => f (X (sigma n omega + s) omega) | (hsig_st n).measurableSpace]) omega ∂P
        = ∫ omega in A, f (X (sigma n omega + s) omega) ∂P :=
      setIntegral_condExp ((hsig_st n).measurableSpace_le) hYint hA'
    have h2 : ∫ omega in A,
        (P[fun omega => f (X (sigma n omega + s) omega) | (hsig_st n).measurableSpace]) omega ∂P
        = ∫ omega in A, g (X (sigma n omega) omega) ∂P :=
      setIntegral_congr_ae (hm A hA) ((hcond n).mono (fun omega hx _ => hx))
    rw [← h1, h2]
  -- (3) pointwise convergence coming from right continuity of the paths
  have hconvZ : ∀ omega,
      Tendsto (fun n => g (X (sigma n omega) omega)) atTop (nhds (g (X (tau omega) omega))) := by
    intro omega
    exact (hg_cont.continuousAt.tendsto).comp
      ((hX_rc omega (tau omega)).comp (tendsto_dyadicUpper_nhdsWithin (tau omega)))
  have hconvY : ∀ omega,
      Tendsto (fun n => f (X (sigma n omega + s) omega))
        atTop (nhds (f (X (tau omega + s) omega))) := by
    intro omega
    have hshift : Tendsto (fun n => sigma n omega + s) atTop
        (nhdsWithin (tau omega + s) (Set.Ioi (tau omega + s))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Filter.Eventually.of_forall
          (fun n => Set.mem_Ioi.mpr (add_lt_add_of_lt_of_le (hsig_gt n omega) le_rfl)))
      exact (tendsto_dyadicUpper (tau omega)).add tendsto_const_nhds
    exact (hf_cont.continuousAt.tendsto).comp
      ((hX_rc omega (tau omega + s)).comp hshift)
  -- (4) bounded convergence gives the limiting identity of set integrals
  have hlim : ∀ A, MeasurableSet[htau.measurableSpace] A →
      ∫ omega in A, f (X (tau omega + s) omega) ∂P
        = ∫ omega in A, g (X (tau omega) omega) ∂P := by
    intro A hA
    have hYtend : Tendsto (fun n => ∫ omega in A, f (X (sigma n omega + s) omega) ∂P) atTop
        (nhds (∫ omega in A, f (X (tau omega + s) omega) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun n => (hYn_meas n).aestronglyMeasurable) (integrable_const C) ?_ ?_
      · exact fun n => Filter.Eventually.of_forall (fun omega => by simpa using hf_bdd _)
      · exact Filter.Eventually.of_forall (fun omega => hconvY omega)
    have hZtend : Tendsto (fun n => ∫ omega in A, g (X (sigma n omega) omega) ∂P) atTop
        (nhds (∫ omega in A, g (X (tau omega) omega) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun n => (hZn_meas n).aestronglyMeasurable) (integrable_const C) ?_ ?_
      · exact fun n => Filter.Eventually.of_forall (fun omega => by simpa using hg_bdd _)
      · exact Filter.Eventually.of_forall (fun omega => hconvZ omega)
    have : (fun n => ∫ omega in A, f (X (sigma n omega + s) omega) ∂P)
        = fun n => ∫ omega in A, g (X (sigma n omega) omega) ∂P :=
      funext (fun n => hsetint n A hA)
    rw [this] at hYtend
    exact tendsto_nhds_unique hYtend hZtend
  -- (5) conclude
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hY_int
    (fun A _ _ => hZ_int.integrableOn) ?_ hZ_meas'.stronglyMeasurable.aestronglyMeasurable).symm
  intro A hA _
  exact (hlim A hA).symm

/-- **(25.5) Strong Markov property from adaptedness and right continuity.**

Same as `pdp_strong_markov_of_rightContinuous`, with progressive measurability
replaced by the more primitive hypothesis that `X` is adapted (it is then
progressively measurable by `progMeasurable_of_rightContinuous`). -/
theorem pdp_strong_markov_of_rightContinuous_adapted
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [MetricSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E} {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_adapted : ∀ u, Measurable[ℱ u] (X u))
    (hX_rc : ∀ omega, ∀ t : ℝ≥0,
      Tendsto (fun r => X r omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    (hmarkov : IsPDPMarkovProcess P pdp ℱ X)
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    {f : E → ℝ} (hf_cont : Continuous f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C)
    (s : ℝ≥0)
    (hg_cont : Continuous (fun x => pdpSemigroup pdp s f x))
    (hg_bdd : ∀ x, |pdpSemigroup pdp s f x| ≤ C) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) :=
  pdp_strong_markov_of_rightContinuous pdp
    (progMeasurable_of_rightContinuous hX_adapted hX_rc) hX_rc hmarkov htau htau_meas
    hf_cont hf_bdd s hg_cont hg_bdd

/-- **(25.5) Strong Markov property for a Feller PDP.**

For a standard PDP satisfying the §27 regularity conditions (bounded continuous
jump rate, continuous flow, `Q` preserving continuity), the continuity and
boundedness of `Pₛ f` are automatic — they are the Feller property
(`pdp_feller_property`) and `pdpSemigroup_abs_le`.  So the strong Markov
property holds for every stopping time and every bounded continuous `f`. -/
theorem pdp_strong_markov_of_feller
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [MetricSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {X : ℝ≥0 → Omega → E} {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_adapted : ∀ u, Measurable[ℱ u] (X u))
    (hX_rc : ∀ omega, ∀ t : ℝ≥0,
      Tendsto (fun r => X r omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    (hmarkov : IsPDPMarkovProcess P pdp.toPDP ℱ X)
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    {f : E → ℝ} (hf_cont : Continuous f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C)
    (s : ℝ≥0) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp.toPDP s f (X (tau omega) omega) := by
  have hf : Measurable f := hf_cont.measurable
  have hg_cont : Continuous (fun x => pdpSemigroup pdp.toPDP s f x) :=
    pdp_feller_property pdp trivial hrate_cont ⟨c, hrate⟩ hflow hflow_cont hQ_cont hf hf_cont
      ⟨C, hf_bdd⟩ s
  have hg_bdd : ∀ x, |pdpSemigroup pdp.toPDP s f x| ≤ C := fun x =>
    pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C
      (le_trans (abs_nonneg _) (hf_bdd x)) hf_bdd s x
  exact pdp_strong_markov_of_rightContinuous_adapted pdp.toPDP hX_adapted hX_rc hmarkov htau
    htau_meas hf_cont hf_bdd s hg_cont hg_bdd

/-- **Countable-range strong Markov property, with the technical hypotheses
discharged.**  A restatement of `pdp_strong_markov_of_countable_range` in which
the `ℱ_τ`-measurability and integrability of `(Pₛ f)(X_τ)` are *derived* from
adaptedness of `X` and boundedness of `f` (via
`measurable_apply_stoppingTime_of_countable_range`) instead of assumed. -/
theorem pdp_strong_markov_of_countable_range_adapted
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E} {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_adapted : ∀ u, Measurable[ℱ u] (X u))
    (hmarkov : IsPDPMarkovProcess P pdp ℱ X)
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    (S : Set ℝ≥0) (hS : S.Countable) (hrange : ∀ omega, tau omega ∈ S)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C)
    (s : ℝ≥0)
    (hg : Measurable (fun x => pdpSemigroup pdp s f x))
    (hg_bdd : ∀ x, |pdpSemigroup pdp s f x| ≤ C) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) := by
  have hZ_meas' := measurable_apply_stoppingTime_of_countable_range htau S hS hrange
    (fun u omega => pdpSemigroup pdp s f (X u omega)) (fun u => hg.comp (hX_adapted u))
  have hZ_int : Integrable (fun omega => pdpSemigroup pdp s f (X (tau omega) omega)) P := by
    refine Integrable.mono' (integrable_const C)
      ((hZ_meas'.mono htau.measurableSpace_le le_rfl).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun omega => ?_))
    simpa using hg_bdd (X (tau omega) omega)
  exact pdp_strong_markov_of_countable_range pdp
    (fun u => (hX_adapted u).mono (ℱ.le u) le_rfl) hmarkov htau htau_meas S hS hrange hf hf_bdd s
    hZ_meas'.stronglyMeasurable hZ_int

/-- **Expectation form of the strong Markov property.**  Taking expectations in
`pdp_strong_markov_of_rightContinuous` gives
`𝔼[f(X_{τ+s})] = 𝔼[(Pₛ f)(X_τ)]`. -/
theorem pdp_expectation_strong_markov
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [MetricSpace E] [BorelSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E} {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_prog : ProgMeasurable ℱ X)
    (hX_rc : ∀ omega, ∀ t : ℝ≥0,
      Tendsto (fun r => X r omega) (nhdsWithin t (Set.Ioi t)) (nhds (X t omega)))
    (hmarkov : IsPDPMarkovProcess P pdp ℱ X)
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    {f : E → ℝ} (hf_cont : Continuous f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C)
    (s : ℝ≥0)
    (hg_cont : Continuous (fun x => pdpSemigroup pdp s f x))
    (hg_bdd : ∀ x, |pdpSemigroup pdp s f x| ≤ C) :
    ∫ omega, f (X (tau omega + s) omega) ∂P
      = ∫ omega, pdpSemigroup pdp s f (X (tau omega) omega) ∂P := by
  have hae := pdp_strong_markov_of_rightContinuous pdp hX_prog hX_rc hmarkov htau htau_meas
    hf_cont hf_bdd s hg_cont hg_bdd
  calc ∫ omega, f (X (tau omega + s) omega) ∂P
      = ∫ omega, (P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace]) omega ∂P :=
        (integral_condExp htau.measurableSpace_le).symm
    _ = ∫ omega, pdpSemigroup pdp s f (X (tau omega) omega) ∂P := integral_congr_ae hae

end GeneralStrongMarkov

section DeterministicPDP

/-!
### A worked instance: the jump-free (deterministic) PDP

All the hypotheses of the general strong Markov theorem are simultaneously
satisfiable: for a PDP with vanishing jump rate the semigroup is composition
with the flow, the flow process is a PDP-Markov process, and the strong Markov
property at an arbitrary stopping time is the flow (semigroup) identity
`φ(τ + s, z) = φ(s, φ(τ, z))`.
-/

variable {E : Type*} [MeasurableSpace E]

/-- With no jumps the survivor function is identically `1`. -/
lemma pdpSurvivorFunction_of_jumpRate_zero (p : PDP E) (hzero : ∀ x, p.jumpRate x = 0)
    (t : ℝ≥0) (x : E) : pdpSurvivorFunction p t x = 1 := by
  simp [pdpSurvivorFunction, hzero]

/-- With no jumps the renewal operator collapses to composition with the flow. -/
lemma pdpSemigroupOp_of_jumpRate_zero (p : PDP E) (hzero : ∀ x, p.jumpRate x = 0)
    (f : E → ℝ) (psi : ℝ≥0 × E → ℝ) (q : ℝ≥0 × E) :
    pdpSemigroupOp p f psi q = f (p.flow q.1 q.2) := by
  simp [pdpSemigroupOp, pdpSurvivorFunction_of_jumpRate_zero p hzero, hzero]

/-- **The semigroup of a jump-free PDP is composition with the flow**:
`Pₜ f (x) = f(φ(t, x))`. -/
lemma pdpSemigroup_of_jumpRate_zero (p : PDP E) (hzero : ∀ x, p.jumpRate x = 0)
    (t : ℝ≥0) (f : E → ℝ) (x : E) :
    pdpSemigroup p t f x = f (p.flow t x) := by
  have hiter : ∀ n : ℕ, (pdpSemigroupOp p f)^[n + 1] (fun _ => 0) (t, x) = f (p.flow t x) := by
    intro n
    rw [Function.iterate_succ_apply']
    exact pdpSemigroupOp_of_jumpRate_zero p hzero f _ (t, x)
  have htend : Tendsto (fun n => (pdpSemigroupOp p f)^[n] (fun _ => 0) (t, x)) atTop
      (nhds (f (p.flow t x))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (hiter m).symm
  exact htend.limUnder_eq

/-- **The flow process of a jump-free PDP is a PDP-Markov process.**

Its increments are deterministic, so the conditional expectation is just the
`ℱ t`-measurable value `f(φ(s, φ(t, Z)))`, which is exactly `(Pₛ f)(Xₜ)`. -/
theorem flowProcess_isPDPMarkovProcess
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    (p : PDP E) (hzero : ∀ x, p.jumpRate x = 0)
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} {Z : Omega → E}
    (hadapt : ∀ t, Measurable[ℱ t] (fun omega => p.flow t (Z omega))) :
    IsPDPMarkovProcess P p ℱ (fun t omega => p.flow t (Z omega)) := by
  intro f hf hf_bdd t s
  obtain ⟨C, hC⟩ := hf_bdd
  have hsplit : ∀ omega, p.flow (t + s) (Z omega) = p.flow s (p.flow t (Z omega)) := by
    intro omega
    rw [add_comm, p.flow_add]
  have hfun : (fun omega => f (p.flow (t + s) (Z omega)))
      = fun omega => f (p.flow s (p.flow t (Z omega))) := funext (fun omega => by rw [hsplit])
  have hmeas : StronglyMeasurable[ℱ t] (fun omega => f (p.flow (t + s) (Z omega))) := by
    rw [hfun]
    exact ((hf.comp (p.flow_measurable s)).comp (hadapt t)).stronglyMeasurable
  have hint : Integrable (fun omega => f (p.flow (t + s) (Z omega))) P := by
    refine Integrable.mono' (integrable_const C)
      ((hmeas.mono (ℱ.le t)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun omega => ?_))
    simpa using hC (p.flow (t + s) (Z omega))
  rw [condExp_of_stronglyMeasurable (ℱ.le t) hmeas hint]
  refine Filter.Eventually.of_forall (fun omega => ?_)
  show f (p.flow (t + s) (Z omega)) = pdpSemigroup p s f (p.flow t (Z omega))
  rw [pdpSemigroup_of_jumpRate_zero p hzero, hsplit]

/-- **Strong Markov property of the deterministic flow process at an arbitrary
stopping time.**  A concrete, hypothesis-free-in-spirit instance of
`pdp_strong_markov_of_rightContinuous_adapted`: it shows that the hypotheses of
the general theorem are simultaneously satisfiable. -/
theorem flowProcess_strong_markov
    {Omega : Type*} [MeasurableSpace Omega] [MetricSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (p : PDP E) (hzero : ∀ x, p.jumpRate x = 0)
    (hflow_time : ∀ x, Continuous (fun t : ℝ≥0 => p.flow t x))
    (hflow_state : ∀ t : ℝ≥0, Continuous (p.flow t))
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} {Z : Omega → E}
    (hadapt : ∀ t, Measurable[ℱ t] (fun omega => p.flow t (Z omega)))
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    {f : E → ℝ} (hf_cont : Continuous f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C)
    (s : ℝ≥0) :
    P[fun omega => f (p.flow (tau omega + s) (Z omega)) | htau.measurableSpace] =ᵐ[P]
      fun omega => f (p.flow s (p.flow (tau omega) (Z omega))) := by
  have hg : (fun x => pdpSemigroup p s f x) = fun x => f (p.flow s x) :=
    funext (fun x => pdpSemigroup_of_jumpRate_zero p hzero s f x)
  have hg_cont : Continuous (fun x => pdpSemigroup p s f x) := by
    rw [hg]; exact hf_cont.comp (hflow_state s)
  have hg_bdd : ∀ x, |pdpSemigroup p s f x| ≤ C := by
    intro x
    rw [pdpSemigroup_of_jumpRate_zero p hzero]
    exact hf_bdd _
  have hX_rc : ∀ omega, ∀ t : ℝ≥0,
      Tendsto (fun r => p.flow r (Z omega)) (nhdsWithin t (Set.Ioi t))
        (nhds (p.flow t (Z omega))) :=
    fun omega t => ((hflow_time (Z omega)).continuousAt).continuousWithinAt
  have hmain := pdp_strong_markov_of_rightContinuous_adapted (P := P) (X := fun t omega =>
    p.flow t (Z omega)) p hadapt hX_rc
    (flowProcess_isPDPMarkovProcess p hzero hadapt) htau htau_meas hf_cont hf_bdd s
    hg_cont hg_bdd
  refine hmain.trans (Filter.Eventually.of_forall (fun omega => ?_))
  exact pdpSemigroup_of_jumpRate_zero p hzero s f _

/-- Every measurable `ℝ≥0`-valued time is a stopping time for the constant
filtration. -/
lemma isStoppingTime_const_filtration {Omega : Type*} [m0 : MeasurableSpace Omega]
    {tau : Omega → ℝ≥0} (htau_meas : Measurable tau) :
    IsStoppingTime (Filtration.const ℝ≥0 m0 le_rfl) (fun omega => (tau omega : ℝ≥0∞)) := by
  intro i
  have hset : {omega | ((tau omega : ℝ≥0) : ℝ≥0∞) ≤ (i : ℝ≥0∞)} = tau ⁻¹' (Set.Iic i) := by
    ext omega
    simp only [Set.mem_setOf_eq, ENNReal.coe_le_coe, Set.mem_preimage, Set.mem_Iic]
  exact hset ▸ htau_meas measurableSet_Iic

/-- A concrete jump-free PDP on `ℝ`: the uniform translation flow
`φ(t, x) = x + t`, zero jump rate and (never used) unit-shift jump kernel. -/
def rampPDP : PDP ℝ where
  flow := fun t x => x + (t : ℝ)
  flow_zero := by intro x; simp
  flow_add := by intro s t x; push_cast; ring
  flow_measurable := fun t => measurable_id.add_const _
  jumpRate := fun _ => 0
  jumpRate_measurable := measurable_const
  transitionMeasure := Kernel.deterministic (fun x : ℝ => x + 1) (measurable_id.add_const 1)
  transitionMeasure_markov := by infer_instance
  no_self_jump := by
    intro x
    rw [Kernel.deterministic_apply]
    simp

/-- **A fully concrete instance of the general strong Markov property.**

For the translation flow `x ↦ x + t` on `ℝ`, an arbitrary random initial state
`Z`, the constant filtration and an arbitrary measurable random time `τ`,
`𝔼[f(Z + τ + s) | ℱ_τ] = f((Z + τ) + s)` almost surely.  This certifies that the
hypotheses of `pdp_strong_markov_of_rightContinuous_adapted` are simultaneously
satisfiable. -/
theorem rampPDP_strong_markov
    {Omega : Type*} [m0 : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {Z : Omega → ℝ} (hZ : Measurable Z)
    {tau : Omega → ℝ≥0} (htau_meas : Measurable tau)
    {f : ℝ → ℝ} (hf_cont : Continuous f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C) (s : ℝ≥0) :
    P[fun omega => f (Z omega + ((tau omega + s : ℝ≥0) : ℝ)) |
        (isStoppingTime_const_filtration htau_meas).measurableSpace] =ᵐ[P]
      fun omega => f (Z omega + (tau omega : ℝ) + (s : ℝ)) := by
  have hadapt : ∀ t : ℝ≥0,
      Measurable[(Filtration.const ℝ≥0 m0 le_rfl) t] (fun omega => rampPDP.flow t (Z omega)) :=
    fun t => hZ.add_const _
  exact flowProcess_strong_markov rampPDP (fun _ => rfl)
    (fun x => by fun_prop) (fun t => by fun_prop) hadapt
    (isStoppingTime_const_filtration htau_meas) htau_meas hf_cont hf_bdd s

end DeterministicPDP

end Davis
