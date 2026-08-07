/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform order statistics are Beta distributed

Let `U₁, …, U_n` be independent uniforms on `[0,1]`.  The classical statement
that the `(j+1)`-st smallest of them has the `Beta(j+1, n−j)` law rests on a
single combinatorial observation: the `(j+1)`-st order statistic is `≤ x`
exactly when at least `j+1` of the samples are `≤ x`, and the number of samples
below `x` is a binomial count.  Together with the Beta–Binomial identity of
`SHSLib/Foundations/BetaBinomialMeasure.lean` this gives the law of the order
statistic.

This module builds the three steps from scratch, since Mathlib does not record
the law of a sum of independent Bernoulli trials:

1. `measure_countEvent`: under the `n`-fold product of the uniform law, the
   event that exactly `k` coordinates are `≤ x` has probability
   `C(n,k) x^k (1−x)^{n−k}`.  The proof partitions the event into the `C(n,k)`
   boxes indexed by the subsets of coordinates of size `k`, and evaluates each
   box with `Measure.pi_pi`.
2. `map_belowCount`: consequently the count itself, as a map into `Fin (n+1)`,
   pushes the product measure forward to Mathlib's `PMF.binomial`.
3. `measure_orderStat_le`: combining with the Beta–Binomial dictionary, the CDF
   of the `(j+1)`-st order statistic is the regularised incomplete Beta
   function `I_x(j+1, n−j)`.

The order statistic itself is `w ∘ Tuple.sort w`, the monotone rearrangement of
the sample provided by Mathlib.
-/
import SHSLib.Foundations.BetaBinomialMeasure
import Mathlib.Data.Fin.Tuple.Sort

open MeasureTheory Set ENNReal

namespace SHSLib.Trigamma

/-! ### The uniform law and its product -/

/-- The uniform law on `[0,1]`. -/
noncomputable def unifIcc : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

instance : IsProbabilityMeasure unifIcc := ⟨by simp [unifIcc]⟩

/-- `n` independent uniforms on `[0,1]`. -/
noncomputable def unifPi (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => unifIcc)

instance (n : ℕ) : IsProbabilityMeasure (unifPi n) := by
  rw [unifPi]; infer_instance

theorem unifIcc_Iic {x : ℝ} (hx1 : x ≤ 1) : unifIcc (Set.Iic x) = ENNReal.ofReal x := by
  rw [unifIcc, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic x ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 x := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, by linarith⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

theorem unifIcc_Ioi {x : ℝ} (hx0 : 0 ≤ x) : unifIcc (Set.Ioi x) = ENNReal.ofReal (1 - x) := by
  rw [unifIcc, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi x ∩ Set.Icc (0:ℝ) 1 = Set.Ioc x 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, by linarith, h2⟩⟩
  rw [h, Real.volume_Ioc]

/-! ### The count of samples below a threshold -/

/-- The set of coordinates of `w` that do not exceed `x`. -/
noncomputable def belowSet (n : ℕ) (x : ℝ) (w : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w i ≤ x)

theorem mem_belowSet {n : ℕ} {x : ℝ} {w : Fin n → ℝ} {i : Fin n} :
    i ∈ belowSet n x w ↔ w i ≤ x := by
  simp [belowSet]

/-- The box of samples whose `S`-coordinates lie below `x` and whose remaining
coordinates lie above it. -/
def sampleBox (n : ℕ) (x : ℝ) (S : Finset (Fin n)) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun i => if i ∈ S then Set.Iic x else Set.Ioi x)

theorem mem_sampleBox_iff (n : ℕ) (x : ℝ) (S : Finset (Fin n)) (w : Fin n → ℝ) :
    w ∈ sampleBox n x S ↔ belowSet n x w = S := by
  simp only [sampleBox, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h
    ext i
    have hi := h i
    by_cases hiS : i ∈ S <;> simp [hiS] at hi ⊢
    · exact mem_belowSet.mpr hi
    · exact fun hc => absurd (mem_belowSet.mp hc) (not_le.mpr hi)
  · intro h i
    by_cases hiS : i ∈ S
    · simp only [if_pos hiS, Set.mem_Iic]
      exact mem_belowSet.mp (by rw [h]; exact hiS)
    · simp only [if_neg hiS, Set.mem_Ioi]
      have hn : i ∉ belowSet n x w := by rw [h]; exact hiS
      exact not_le.mp (fun hc => hn (mem_belowSet.mpr hc))

theorem measurableSet_sampleBox (n : ℕ) (x : ℝ) (S : Finset (Fin n)) :
    MeasurableSet (sampleBox n x S) := by
  apply MeasurableSet.univ_pi
  intro i
  by_cases h : i ∈ S <;> simp [h, measurableSet_Iic, measurableSet_Ioi]

theorem measure_sampleBox (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (S : Finset (Fin n)) :
    unifPi n (sampleBox n x S)
      = ENNReal.ofReal x ^ S.card * ENNReal.ofReal (1 - x) ^ (n - S.card) := by
  rw [unifPi, sampleBox, Measure.pi_pi]
  simp only [apply_ite unifIcc, unifIcc_Iic hx1, unifIcc_Ioi hx0]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 1
  · congr 1
    simp
  · congr 1
    rw [Finset.filter_not]
    simp [Finset.card_sdiff]

/-- The event "exactly `k` samples are below `x`" is the disjoint union of the
boxes indexed by the `k`-element sets of coordinates. -/
theorem countEvent_eq (n : ℕ) (x : ℝ) (k : ℕ) :
    {w : Fin n → ℝ | (belowSet n x w).card = k}
      = ⋃ S ∈ (Finset.univ.powersetCard k : Finset (Finset (Fin n))), sampleBox n x S := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard,
    Finset.subset_univ, true_and, exists_prop]
  constructor
  · intro h
    exact ⟨belowSet n x w, h, (mem_sampleBox_iff n x _ w).mpr rfl⟩
  · rintro ⟨S, hcard, hw⟩
    rw [(mem_sampleBox_iff n x S w).mp hw]
    exact hcard

theorem measurableSet_countEvent (n : ℕ) (x : ℝ) (k : ℕ) :
    MeasurableSet {w : Fin n → ℝ | (belowSet n x w).card = k} := by
  rw [countEvent_eq]
  exact Finset.measurableSet_biUnion _ (fun S _ => measurableSet_sampleBox n x S)

/-- **The count of samples below `x` is binomial.** -/
theorem measure_countEvent (n k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    unifPi n {w : Fin n → ℝ | (belowSet n x w).card = k}
      = (n.choose k : ℝ≥0∞) * ENNReal.ofReal x ^ k * ENNReal.ofReal (1 - x) ^ (n - k) := by
  rw [countEvent_eq, measure_biUnion_finset ?disj (fun S _ => measurableSet_sampleBox n x S)]
  · have hterm : ∀ S ∈ (Finset.univ.powersetCard k : Finset (Finset (Fin n))),
        unifPi n (sampleBox n x S)
          = ENNReal.ofReal x ^ k * ENNReal.ofReal (1 - x) ^ (n - k) := by
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      rw [measure_sampleBox n hx0 hx1 S, hS.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard]
    simp [Finset.card_univ, mul_assoc]
  · intro S _ T _ hST
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro w hwS hwT
    exact hST (((mem_sampleBox_iff n x S w).mp hwS).symm.trans
      ((mem_sampleBox_iff n x T w).mp hwT))

/-! ### The count as a `Fin (n+1)`-valued random variable -/

/-- The number of samples below `x`, as an element of `Fin (n+1)`. -/
noncomputable def belowCount (n : ℕ) (x : ℝ) (w : Fin n → ℝ) : Fin (n + 1) :=
  ⟨(belowSet n x w).card, by
    have h := Finset.card_le_univ (belowSet n x w)
    simp only [Fintype.card_fin] at h
    omega⟩

theorem measurable_belowCount (n : ℕ) (x : ℝ) : Measurable (belowCount n x) := by
  apply measurable_to_countable'
  intro k
  have hpre : (belowCount n x) ⁻¹' {k} = {w : Fin n → ℝ | (belowSet n x w).card = (k : ℕ)} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, belowCount]
    exact ⟨fun h => by rw [← h], fun h => Fin.ext h⟩
  rw [hpre]
  exact measurableSet_countEvent n x k

/-- The general value of the binomial pmf, written with `ENNReal.ofReal`. -/
theorem binomial_apply_ofReal (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : Fin (n + 1)) :
    PMF.binomial x.toNNReal (Real.toNNReal_le_one.mpr hx1) n i
      = (n.choose i : ℝ≥0∞) * ENNReal.ofReal x ^ (i : ℕ)
          * ENNReal.ofReal (1 - x) ^ (n - (i : ℕ)) := by
  have e1 : ((1:ℝ≥0∞) - ENNReal.ofReal x) = ENNReal.ofReal (1 - x) := by
    rw [ENNReal.ofReal_sub _ hx0]; simp
  rw [PMF.binomial_apply]
  simp only [Fin.val_last, show (↑x.toNNReal : ℝ≥0∞) = ENNReal.ofReal x from rfl, e1]
  ring

/-- **The law of the count is the binomial law.** -/
theorem map_belowCount (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (unifPi n).map (belowCount n x)
      = (PMF.binomial x.toNNReal (Real.toNNReal_le_one.mpr hx1) n).toMeasure := by
  refine Measure.ext_iff_singleton.mpr (fun k => ?_)
  rw [Measure.map_apply (measurable_belowCount n x) (MeasurableSet.singleton k),
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton k),
    binomial_apply_ofReal n hx0 hx1 k]
  have hpre : (belowCount n x) ⁻¹' {k} = {w : Fin n → ℝ | (belowSet n x w).card = (k : ℕ)} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, belowCount]
    exact ⟨fun h => by rw [← h], fun h => Fin.ext h⟩
  rw [hpre, measure_countEvent n (k : ℕ) hx0 hx1]

/-- The probability that at least `j+1` of the `n` samples are below `x`, in
closed form: it is the regularised incomplete Beta function. -/
theorem measure_atLeast_below (j m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    unifPi (j + m + 1) {w : Fin (j + m + 1) → ℝ | j + 1 ≤ (belowSet (j + m + 1) x w).card}
      = ENNReal.ofReal (regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1) x) := by
  have hpre : {w : Fin (j + m + 1) → ℝ | j + 1 ≤ (belowSet (j + m + 1) x w).card}
      = (belowCount (j + m + 1) x) ⁻¹' (binomUpperTail j (j + m + 1)) := by
    ext w
    simp [binomUpperTail, belowCount]
  rw [hpre, ← Measure.map_apply (measurable_belowCount _ x) MeasurableSet.of_discrete,
    map_belowCount (j + m + 1) hx0 hx1, binomial_toMeasure_upperTail j m hx0 hx1,
    regBetaFn_nat_eq]

/-! ### The order statistics -/

/-- The `j`-th order statistic of the sample `w`: the `j`-th entry of its
monotone rearrangement. -/
noncomputable def orderStat (n : ℕ) (w : Fin n → ℝ) (j : Fin n) : ℝ := w (Tuple.sort w j)

/-- **The order statistic counts**: the `j`-th smallest sample is `≤ x` exactly
when more than `j` samples are `≤ x`. -/
theorem orderStat_le_iff (n : ℕ) (x : ℝ) (w : Fin n → ℝ) (j : Fin n) :
    orderStat n w j ≤ x ↔ (j : ℕ) + 1 ≤ (belowSet n x w).card := by
  have hmap : belowSet n x (w ∘ Tuple.sort w)
      = (belowSet n x w).map ((Tuple.sort w).symm.toEmbedding) := by
    ext i
    simp [belowSet, Finset.mem_map_equiv]
  have hcard : (belowSet n x (w ∘ Tuple.sort w)).card = (belowSet n x w).card := by
    rw [hmap, Finset.card_map]
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone (j := j) (a := x)
    (Tuple.monotone_sort w)
  rw [show ({i | (w ∘ Tuple.sort w) i ≤ x} : Finset (Fin n)) = belowSet n x (w ∘ Tuple.sort w) from
    rfl, hcard] at h
  constructor
  · intro hle
    have := h.mpr hle
    omega
  · intro hge
    exact h.mp (by omega)

/-- **Uniform order statistics are Beta distributed.**  For `n = j+m+1`
independent uniforms on `[0,1]`, the `j`-th order statistic (the `(j+1)`-st
smallest sample) has CDF `I_x(j+1, m+1)`, i.e. the `Beta(j+1, n−j)` law. -/
theorem measure_orderStat_le (j m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (jj : Fin (j + m + 1)) (hjj : (jj : ℕ) = j) :
    unifPi (j + m + 1) {w : Fin (j + m + 1) → ℝ | orderStat (j + m + 1) w jj ≤ x}
      = ENNReal.ofReal (regBetaFn ((j : ℝ) + 1) ((m : ℝ) + 1) x) := by
  have hset : {w : Fin (j + m + 1) → ℝ | orderStat (j + m + 1) w jj ≤ x}
      = {w : Fin (j + m + 1) → ℝ | j + 1 ≤ (belowSet (j + m + 1) x w).card} := by
    ext w
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, orderStat_le_iff, hjj]
  rw [hset, measure_atLeast_below j m hx0 hx1]

end SHSLib.Trigamma
