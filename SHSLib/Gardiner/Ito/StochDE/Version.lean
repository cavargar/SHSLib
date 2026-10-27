/-
# Jointly measurable, adapted versions of continuous processes and of drift integrals

The interface `IsFWiener` gives a Wiener process that is adapted with almost surely continuous
paths, but it does not make `(t, ω) ↦ W t ω` jointly measurable, and an adapted process with only
almost surely continuous paths need not be progressively measurable.  This file provides the two
regularisations needed to build solutions of stochastic differential equations:

* `regVer X`: `regVer X t ω = lim_n X (⌊2ⁿ t⌋ / 2ⁿ) ω`.  It is jointly measurable, adapted (for
  `t ≥ 0`), and equals `X t ω` whenever `X · ω` is continuous at `t`;
* `driftVer F x t₀`: an adapted, jointly measurable process which, for almost every `ω` with
  `x · ω` continuous on `[t₀, T]`, equals the pathwise drift integral `∫_{t₀}^t F (x s ω) s ds`
  for all `t ∈ [t₀, T]`.  It is the limit of the drift integrals along the step approximations
  `x (t₀ + ⌊2ⁿ (s - t₀)⌋ / 2ⁿ)` of `x`.
-/
import SHSLib.Gardiner.Ito.StochDE.Doob

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.StochDE

/-! ### Dyadic step times -/

/-- The left dyadic approximation `⌊2ⁿ t⌋ / 2ⁿ ≤ t`. -/
def dyLeft (n : ℕ) (t : ℝ) : ℝ := (⌊t * 2 ^ n⌋ : ℝ) / 2 ^ n

lemma dyLeft_le (n : ℕ) (t : ℝ) : dyLeft n t ≤ t := by
  unfold dyLeft
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

lemma sub_lt_dyLeft (n : ℕ) (t : ℝ) : t - (1 / 2) ^ n < dyLeft n t := by
  unfold dyLeft
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [lt_div_iff₀ h2, sub_mul, one_div_pow, div_mul_cancel₀ _ h2.ne']
  linarith [Int.lt_floor_add_one (t * 2 ^ n)]

lemma dyLeft_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ dyLeft n t := by
  unfold dyLeft
  exact div_nonneg (by exact_mod_cast Int.floor_nonneg.mpr (by positivity)) (by positivity)

lemma tendsto_dyLeft (t : ℝ) : Tendsto (fun n => dyLeft n t) atTop (𝓝 t) := by
  have hlim : Tendsto (fun n : ℕ => t - (1 / 2) ^ n) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
    (fun n => (sub_lt_dyLeft n t).le) (fun n => dyLeft_le n t)

/-- The step time `a + ⌊2ⁿ (s - a)⌋ / 2ⁿ ≤ s`. -/
def stepTime (a : ℝ) (n : ℕ) (s : ℝ) : ℝ := a + dyLeft n (s - a)

lemma stepTime_le (a : ℝ) (n : ℕ) (s : ℝ) : stepTime a n s ≤ s := by
  unfold stepTime; linarith [dyLeft_le n (s - a)]

lemma le_stepTime {a s : ℝ} (h : a ≤ s) (n : ℕ) : a ≤ stepTime a n s := by
  unfold stepTime; linarith [dyLeft_nonneg (sub_nonneg.mpr h) n]

lemma tendsto_stepTime (a s : ℝ) : Tendsto (fun n => stepTime a n s) atTop (𝓝 s) := by
  have := (tendsto_dyLeft (s - a)).const_add a
  simpa [stepTime] using this

lemma measurable_comp_stepTime {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℝ}
    (hX : ∀ u, Measurable (X u)) (a : ℝ) (n : ℕ) :
    Measurable (fun p : ℝ × Ω => X (stepTime a n p.1) p.2) := by
  have e : (fun p : ℝ × Ω => X (stepTime a n p.1) p.2) =
      (fun q : ℤ × Ω => X (a + (q.1 : ℝ) / 2 ^ n) q.2) ∘
        (fun p : ℝ × Ω => (⌊(p.1 - a) * 2 ^ n⌋, p.2)) := by
    funext p; simp [stepTime, dyLeft]
  rw [e]
  exact (measurable_from_prod_countable_right (f := fun q : ℤ × Ω => X (a + (q.1 : ℝ) / 2 ^ n) q.2)
    fun z => hX (a + (z : ℝ) / 2 ^ n)).comp
    (((measurable_fst.sub_const a).mul_const _).floor.prodMk measurable_snd)

lemma stronglyMeasurable_limUnder_nat {Ω : Type*} {m : MeasurableSpace Ω} {f : ℕ → Ω → ℝ}
    (hf : ∀ n, StronglyMeasurable[m] (f n)) :
    StronglyMeasurable[m] (fun ω => limUnder atTop fun n => f n ω) :=
  StronglyMeasurable.limUnder hf

/-! ### The regularised version of a process -/

/-- `regVer X t ω = lim_n X (⌊2ⁿ t⌋ / 2ⁿ) ω` (chosen arbitrarily if the limit does not exist). -/
def regVer {Ω : Type*} (X : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => X (stepTime 0 n t) ω

lemma measurable_regVer {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℝ}
    (hX : ∀ u, Measurable (X u)) : Measurable fun p : ℝ × Ω => regVer X p.1 p.2 := by
  have := StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_comp_stepTime hX 0 n).stronglyMeasurable)
  exact this.measurable

lemma stronglyMeasurable_regVer {Ω : Type*} {m : MeasurableSpace Ω} {X : ℝ → Ω → ℝ} {t : ℝ}
    (hX : ∀ n, StronglyMeasurable[m] (X (stepTime 0 n t))) :
    StronglyMeasurable[m] (regVer X t) :=
  StronglyMeasurable.limUnder (l := atTop) hX

lemma regVer_eq {Ω : Type*} {X : ℝ → Ω → ℝ} {t : ℝ} {ω : Ω}
    (hc : ContinuousAt (fun u => X u ω) t) : regVer X t ω = X t ω :=
  ((hc.tendsto).comp (tendsto_stepTime 0 t)).limUnder_eq

/-- An adapted process (on `t ≥ 0`) has an adapted, jointly measurable regularisation. -/
lemma regVer_adapted {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ}
    {X : ℝ → Ω → ℝ} (hX : ∀ u, 0 ≤ u → StronglyMeasurable[𝓕 u] (X u)) {t : ℝ} (ht : 0 ≤ t) :
    StronglyMeasurable[𝓕 t] (regVer X t) := by
  refine stronglyMeasurable_regVer fun n => ?_
  have h0 : 0 ≤ stepTime 0 n t := le_stepTime ht n
  exact (hX _ h0).mono (𝓕.mono (stepTime_le 0 n t))

/-! ### The adapted version of a drift integral -/

section Drift

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The drift integral along the `n`-th step approximation of `x`:
`∫_{(t₀, t]} F (x (stepTime t₀ n s) ω) s ds`. -/
def stepDrift (F : ℝ → ℝ → ℝ) (x : ℝ → Ω → ℝ) (t₀ : ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioc t₀ t, F (x (stepTime t₀ n s) ω) s

/-- The adapted version of the drift integral `∫_{t₀}^t F (x s) s ds`. -/
def driftVer (F : ℝ → ℝ → ℝ) (x : ℝ → Ω → ℝ) (t₀ : ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => stepDrift F x t₀ n t ω

lemma stepDrift_eq_indicator (F : ℝ → ℝ → ℝ) (x : ℝ → Ω → ℝ) (t₀ : ℝ) (n : ℕ) (t : ℝ)
    (ω : Ω) : stepDrift F x t₀ n t ω =
      ∫ s, (Set.Ioc t₀ t).indicator (fun s => F (x (stepTime t₀ n s) ω) s) s := by
  rw [stepDrift, integral_indicator measurableSet_Ioc]

lemma measurable_stepDrift {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F))
    {x : ℝ → Ω → ℝ} (hx : ∀ u, Measurable (x u)) (t₀ : ℝ) (n : ℕ) :
    Measurable (Function.uncurry (stepDrift F x t₀ n)) := by
  have hg : Measurable fun q : (ℝ × Ω) × ℝ =>
      (Set.Ioc t₀ q.1.1).indicator (fun s => F (x (stepTime t₀ n s) q.1.2) s) q.2 := by
    have hset : MeasurableSet {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Ioc t₀ q.1.1} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
    have hf : Measurable fun q : (ℝ × Ω) × ℝ => F (x (stepTime t₀ n q.2) q.1.2) q.2 := by
      have h1 := (measurable_comp_stepTime hx t₀ n).comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst) :
          Measurable fun q : (ℝ × Ω) × ℝ => (q.2, q.1.2))
      exact hF.comp (h1.prodMk measurable_snd)
    have := hf.indicator hset
    convert this using 1
  have := StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ))
    (f := fun (p : ℝ × Ω) (s : ℝ) =>
      (Set.Ioc t₀ p.1).indicator (fun s => F (x (stepTime t₀ n s) p.2) s) s)
    hg.stronglyMeasurable
  convert this.measurable using 1
  funext p
  exact stepDrift_eq_indicator F x t₀ n p.1 p.2

lemma measurable_driftVer {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F))
    {x : ℝ → Ω → ℝ} (hx : ∀ u, Measurable (x u)) (t₀ : ℝ) :
    Measurable (Function.uncurry (driftVer F x t₀)) :=
  (StronglyMeasurable.limUnder (l := atTop)
    fun n => (measurable_stepDrift hF hx t₀ n).stronglyMeasurable).measurable

omit mΩ in
lemma stronglyMeasurable_integral_stepComp {Ω : Type*} [MeasurableSpace Ω] {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) {X : ℝ → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (a b : ℝ) (n : ℕ) :
    StronglyMeasurable fun ω => ∫ s, (Set.Ioc a b).indicator
      (fun s => F (X (stepTime a n s) ω) s) s := by
  have h1 := measurable_comp_stepTime hX a n
  have h2 : Measurable fun q : Ω × ℝ => F (X (stepTime a n q.2) q.1) q.2 :=
    hF.comp ((h1.comp measurable_swap).prodMk measurable_snd)
  have hg : Measurable fun q : Ω × ℝ =>
      (Set.Ioc a b).indicator (fun s => F (X (stepTime a n s) q.1) s) q.2 := by
    have := h2.indicator ((measurableSet_Ioc (a := a) (b := b)).preimage measurable_snd)
    convert this using 1
  exact StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ))
    (f := fun ω s => (Set.Ioc a b).indicator (fun s => F (X (stepTime a n s) ω) s) s)
    hg.stronglyMeasurable

variable {𝓕 : Filtration ℝ mΩ}

lemma stepDrift_adapted {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F))
    {x : ℝ → Ω → ℝ} {t₀ T : ℝ} (hx : ∀ u ∈ Set.Icc t₀ T, StronglyMeasurable[𝓕 u] (x u))
    (n : ℕ) {t : ℝ} (ht₀ : t₀ ≤ t) (htT : t ≤ T) :
    StronglyMeasurable[𝓕 t] (stepDrift F x t₀ n t) := by
  set x' : ℝ → Ω → ℝ := fun u => x (max t₀ (min u t))
  have hx' : ∀ u, Measurable[𝓕 t] (x' u) := fun u => by
    have hmem : max t₀ (min u t) ∈ Set.Icc t₀ T :=
      ⟨le_max_left _ _, max_le (ht₀.trans htT) ((min_le_right u t).trans htT)⟩
    exact ((hx _ hmem).mono (𝓕.mono (max_le ht₀ (min_le_right _ _)))).measurable
  have e : stepDrift F x t₀ n t = fun ω =>
      ∫ s, (Set.Ioc t₀ t).indicator (fun s => F (x' (stepTime t₀ n s) ω) s) s := by
    funext ω
    rw [stepDrift, integral_indicator (measurableSet_Ioc (a := t₀) (b := t))]
    refine setIntegral_congr_fun (measurableSet_Ioc (a := t₀) (b := t)) fun s hs => ?_
    have h1 : t₀ ≤ stepTime t₀ n s := le_stepTime hs.1.le n
    have h2 : stepTime t₀ n s ≤ t := (stepTime_le t₀ n s).trans hs.2
    simp only [x', min_eq_left h2, max_eq_right h1]
  rw [e]
  have := @stronglyMeasurable_integral_stepComp Ω (𝓕 t) F hF x' hx' t₀ t n
  exact this

lemma driftVer_adapted {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F))
    {x : ℝ → Ω → ℝ} {t₀ T : ℝ} (hx : ∀ u ∈ Set.Icc t₀ T, StronglyMeasurable[𝓕 u] (x u))
    {t : ℝ} (ht₀ : t₀ ≤ t) (htT : t ≤ T) :
    StronglyMeasurable[𝓕 t] (driftVer F x t₀ t) :=
  stronglyMeasurable_limUnder_nat fun n => stepDrift_adapted hF hx n ht₀ htT

/-- Hypotheses on a drift coefficient `F (y, s)` on `[t₀, T]`: jointly measurable, continuous in
`y`, and of linear growth. -/
structure DriftCoeff (F : ℝ → ℝ → ℝ) (t₀ T C : ℝ) : Prop where
  measurable : Measurable (Function.uncurry F)
  cont : ∀ s ∈ Set.Icc t₀ T, Continuous fun y => F y s
  growth : ∀ s ∈ Set.Icc t₀ T, ∀ y, |F y s| ≤ C * (1 + |y|)

lemma measurable_section_of_uncurry {x : ℝ → Ω → ℝ} (hxm : Measurable (Function.uncurry x))
    (ω : Ω) : Measurable fun s => x s ω :=
  hxm.comp (measurable_id.prodMk measurable_const)

lemma measurable_of_uncurry {x : ℝ → Ω → ℝ} (hxm : Measurable (Function.uncurry x)) (u : ℝ) :
    Measurable (x u) :=
  hxm.comp (measurable_const.prodMk measurable_id)

lemma DriftCoeff.integrableOn {F : ℝ → ℝ → ℝ} {t₀ T C : ℝ} (hF : DriftCoeff F t₀ T C)
    {x : ℝ → Ω → ℝ} (hxm : Measurable (Function.uncurry x)) {ω : Ω}
    (hc : ContinuousOn (fun u => x u ω) (Set.Icc t₀ T)) :
    IntegrableOn (fun s => F (x s ω) s) (Set.Icc t₀ T) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := t₀) (b := T)).exists_bound_of_continuousOn hc
  have hm : Measurable fun s => F (x s ω) s :=
    hF.measurable.comp ((measurable_section_of_uncurry hxm ω).prodMk measurable_id)
  refine Integrable.mono' (integrable_const (C * (1 + B))) hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs]
  refine (hF.growth s hs _).trans ?_
  have hC : 0 ≤ C := by
    have := hF.growth s hs 0
    simp at this
    linarith [abs_nonneg (F 0 s)]
  have := hB s hs
  rw [Real.norm_eq_abs] at this
  nlinarith

lemma tendsto_stepDrift {F : ℝ → ℝ → ℝ} {t₀ T C : ℝ} (hF : DriftCoeff F t₀ T C)
    {x : ℝ → Ω → ℝ} (hxm : Measurable (Function.uncurry x)) {ω : Ω}
    (hc : ContinuousOn (fun u => x u ω) (Set.Icc t₀ T)) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    Tendsto (fun n => stepDrift F x t₀ n t ω) atTop
      (𝓝 (∫ s in Set.Ioc t₀ t, F (x s ω) s)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := t₀) (b := T)).exists_bound_of_continuousOn hc
  have hx := measurable_of_uncurry hxm
  have hsub : Set.Ioc t₀ t ⊆ Set.Icc t₀ T := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hC : 0 ≤ C := by
    have := hF.growth t₀ ⟨le_rfl, ht.1.trans ht.2⟩ 0
    simp at this
    linarith [abs_nonneg (F 0 t₀)]
  refine tendsto_integral_of_dominated_convergence (fun _ => C * (1 + B)) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact (hF.measurable.comp (((measurable_comp_stepTime hx t₀ n).comp
      (measurable_id.prodMk measurable_const)).prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hst : stepTime t₀ n s ∈ Set.Icc t₀ T :=
      ⟨le_stepTime hs.1.le n, (stepTime_le t₀ n s).trans (hs.2.trans ht.2)⟩
    rw [Real.norm_eq_abs]
    refine (hF.growth s (hsub hs) _).trans ?_
    have := hB _ hst
    rw [Real.norm_eq_abs] at this
    nlinarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hst : Tendsto (fun n => stepTime t₀ n s) atTop (𝓝[Set.Icc t₀ T] s) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_stepTime t₀ s, Eventually.of_forall fun n =>
        ⟨le_stepTime hs.1.le n, (stepTime_le t₀ n s).trans (hs.2.trans ht.2)⟩⟩
    have h1 := (hc s (hsub hs)).tendsto.comp hst
    exact ((hF.cont s (hsub hs)).tendsto _).comp h1

/-- On a path that is continuous on `[t₀, T]`, the adapted drift version is the pathwise drift
integral. -/
lemma driftVer_eq {F : ℝ → ℝ → ℝ} {t₀ T C : ℝ} (hF : DriftCoeff F t₀ T C)
    {x : ℝ → Ω → ℝ} (hxm : Measurable (Function.uncurry x)) {ω : Ω}
    (hc : ContinuousOn (fun u => x u ω) (Set.Icc t₀ T)) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    driftVer F x t₀ t ω = ∫ s in t₀..t, F (x s ω) s := by
  rw [intervalIntegral.integral_of_le ht.1]
  exact (tendsto_stepDrift hF hxm hc ht).limUnder_eq

/-- The pathwise drift integral is continuous on `[t₀, T]`. -/
lemma continuousOn_drift {F : ℝ → ℝ → ℝ} {t₀ T C : ℝ} (hF : DriftCoeff F t₀ T C)
    (htT : t₀ ≤ T) {x : ℝ → Ω → ℝ} (hxm : Measurable (Function.uncurry x)) {ω : Ω}
    (hc : ContinuousOn (fun u => x u ω) (Set.Icc t₀ T)) :
    ContinuousOn (fun t => ∫ s in t₀..t, F (x s ω) s) (Set.Icc t₀ T) := by
  have := intervalIntegral.continuousOn_primitive_interval (a := t₀) (b := T)
    (μ := volume) (f := fun s => F (x s ω) s)
  rw [Set.uIcc_of_le htT] at this
  exact this (hF.integrableOn hxm hc)

end Drift

end Gardiner.Ito.StochDE
