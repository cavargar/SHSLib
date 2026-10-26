/-
# Elementary nonanticipating integrands for a general filtration (Gardiner §4.2.4, §4.2.6 e–f)

`Gardiner.Ito.ElemIntegrand 𝓕 P ι` is a finite family of pieces `φᵢ 1_{(aᵢ, bᵢ]}` with
`0 ≤ aᵢ ≤ bᵢ`, `φᵢ` square integrable and `𝓕 aᵢ`-measurable.  The fields are those of
`Gardiner.Ito.SimpleIntegrand` with `wienerFiltration W` replaced by `𝓕`, so a simple integrand is
an elementary integrand for the natural filtration (`Gardiner.Ito.SimpleIntegrand.toElem`, specified in
`research/docs/plans/plan_gardiner_ito_formula.md`), with the same process and integral.

Results, for a Wiener process `W` w.r.t. `𝓕` (`Gardiner.Ito.IsFWiener`):

* `ElemIntegrand.integral_mean`: `⟨∫ G dW⟩ = 0` (4.2.40);
* `ElemIntegrand.integral_mul`: `⟨∫ G dW ∫ H dW⟩ = ∫ ds ⟨G(s) H(s)⟩` (4.2.42);
* `ElemIntegrand.martingale_running`: `t ↦ ∫₀ᵗ G dW` is an `𝓕`-martingale.
-/
import SHSLib.Gardiner.Ito.Calculus.Filtered

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

/-- The indicator `1_{(a,b]}(s)` as a real function. -/
def cellInd (a b : ℝ) (s : ℝ) : ℝ := (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s

lemma cellInd_mem {a b s : ℝ} (hs : s ∈ Set.Ioc a b) : cellInd a b s = 1 := by
  simp [cellInd, Set.indicator_of_mem hs]

lemma cellInd_notMem {a b s : ℝ} (hs : s ∉ Set.Ioc a b) : cellInd a b s = 0 := by
  simp [cellInd, Set.indicator_of_notMem hs]

lemma cellInd_nonneg (a b s : ℝ) : 0 ≤ cellInd a b s := by
  unfold cellInd; exact Set.indicator_nonneg (fun _ _ => zero_le_one) s

lemma cellInd_le_one (a b s : ℝ) : cellInd a b s ≤ 1 := by
  unfold cellInd; exact Set.indicator_le_self' (fun _ _ => zero_le_one) s

lemma cellInd_sq (a b s : ℝ) : cellInd a b s ^ 2 = cellInd a b s := by
  by_cases h : s ∈ Set.Ioc a b
  · simp [cellInd_mem h]
  · simp [cellInd_notMem h]

lemma measurable_cellInd (a b : ℝ) : Measurable (cellInd a b) :=
  (measurable_const.indicator measurableSet_Ioc)

lemma cellInd_mul_cellInd (a b c d s : ℝ) :
    cellInd a b s * cellInd c d s = cellInd (max a c) (min b d) s := by
  unfold cellInd
  rw [← Set.Ioc_inter_Ioc]
  simp only [Set.indicator, Set.mem_inter_iff]
  split_ifs <;> simp_all

/-- `|(a, b] ∩ (c, d]|`. -/
def cellOverlap (a b c d : ℝ) : ℝ := max (min b d - max a c) 0

lemma integral_cellInd (a b : ℝ) : ∫ s, cellInd a b s = max (b - a) 0 := by
  unfold cellInd
  rw [integral_indicator_const _ measurableSet_Ioc]
  simp [Real.volume_Ioc, measureReal_def]
  rcases le_total a b with h | h
  · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h)]
  · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h)]; simp

lemma integrable_cellInd (a b : ℝ) : Integrable (cellInd a b) := by
  unfold cellInd
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (integrableOn_const (by simp [Real.volume_Ioc]))

lemma integral_cellInd_mul_cellInd (a b c d : ℝ) :
    ∫ s, cellInd a b s * cellInd c d s = cellOverlap a b c d := by
  simp_rw [cellInd_mul_cellInd]; rw [integral_cellInd]; rfl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **An elementary nonanticipating integrand** for the filtration `𝓕`:
`G(s) = Σᵢ φᵢ 1_{(aᵢ, bᵢ]}(s)` with `0 ≤ aᵢ ≤ bᵢ`, `φᵢ ∈ L²(P)` and `φᵢ` measurable w.r.t. `𝓕 aᵢ`.
Pieces may overlap. -/
structure ElemIntegrand (𝓕 : Filtration ℝ mΩ) (P : Measure Ω) (ι : Type*) [Fintype ι] where
  /-- left endpoints -/
  left : ι → ℝ
  /-- right endpoints -/
  right : ι → ℝ
  /-- values -/
  val : ι → Ω → ℝ
  left_nonneg : ∀ i, 0 ≤ left i
  left_le_right : ∀ i, left i ≤ right i
  adapted : ∀ i, StronglyMeasurable[𝓕 (left i)] (val i)
  memLp : ∀ i, MemLp (val i) 2 P

namespace ElemIntegrand

variable {𝓕 : Filtration ℝ mΩ} {P : Measure Ω} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The integrand as a process, `G(s, ω) = Σᵢ φᵢ(ω) 1_{(aᵢ, bᵢ]}(s)`. -/
def process (H : ElemIntegrand 𝓕 P ι) (s : ℝ) (ω : Ω) : ℝ :=
  ∑ i, H.val i ω * cellInd (H.left i) (H.right i) s

/-- The stochastic integral `∫ G dW = Σᵢ φᵢ (W(bᵢ) - W(aᵢ))`. -/
def integral (W : ℝ → Ω → ℝ) (H : ElemIntegrand 𝓕 P ι) (ω : Ω) : ℝ :=
  ∑ i, H.val i ω * (W (H.right i) ω - W (H.left i) ω)

/-- The running integral `∫₀ᵗ G dW = Σᵢ φᵢ (W(bᵢ ∧ t) - W(aᵢ ∧ t))`. -/
def running (W : ℝ → Ω → ℝ) (H : ElemIntegrand 𝓕 P ι) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i, H.val i ω * (W (min (H.right i) t) ω - W (min (H.left i) t) ω)

/-- Concatenation of the pieces of two elementary integrands. -/
def add (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) : ElemIntegrand 𝓕 P (ι ⊕ κ) where
  left := Sum.elim H.left K.left
  right := Sum.elim H.right K.right
  val := Sum.elim H.val K.val
  left_nonneg := Sum.rec H.left_nonneg K.left_nonneg
  left_le_right := Sum.rec H.left_le_right K.left_le_right
  adapted := Sum.rec H.adapted K.adapted
  memLp := Sum.rec H.memLp K.memLp

/-- Scalar multiple of an elementary integrand. -/
def smul (c : ℝ) (H : ElemIntegrand 𝓕 P ι) : ElemIntegrand 𝓕 P ι where
  left := H.left
  right := H.right
  val i := fun ω => c * H.val i ω
  left_nonneg := H.left_nonneg
  left_le_right := H.left_le_right
  adapted i := (H.adapted i).const_mul c
  memLp i := (H.memLp i).const_mul c

/-- Reindexing along an equivalence. -/
def reindex (e : ι ≃ κ) (H : ElemIntegrand 𝓕 P ι) : ElemIntegrand 𝓕 P κ where
  left := H.left ∘ e.symm
  right := H.right ∘ e.symm
  val := H.val ∘ e.symm
  left_nonneg _ := H.left_nonneg _
  left_le_right _ := H.left_le_right _
  adapted _ := H.adapted _
  memLp _ := H.memLp _

/-- The integrand with no pieces. -/
def zero : ElemIntegrand 𝓕 P (Fin 0) where
  left := Fin.elim0
  right := Fin.elim0
  val := Fin.elim0
  left_nonneg := nofun
  left_le_right := nofun
  adapted := nofun
  memLp := nofun

variable (W : ℝ → Ω → ℝ)

@[simp] lemma integral_add (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) :
    (H.add K).integral W = fun ω => H.integral W ω + K.integral W ω := by
  funext ω; simp [integral, add, Fintype.sum_sum_type]

@[simp] lemma process_add (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) :
    (H.add K).process = fun s ω => H.process s ω + K.process s ω := by
  funext s ω; simp [process, add, Fintype.sum_sum_type]

@[simp] lemma running_add (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) :
    (H.add K).running W = fun t ω => H.running W t ω + K.running W t ω := by
  funext t ω; simp [running, add, Fintype.sum_sum_type]

@[simp] lemma integral_smul (c : ℝ) (H : ElemIntegrand 𝓕 P ι) :
    (H.smul c).integral W = fun ω => c * H.integral W ω := by
  funext ω; simp [integral, smul, Finset.mul_sum, mul_assoc]

@[simp] lemma process_smul (c : ℝ) (H : ElemIntegrand 𝓕 P ι) :
    (H.smul c).process = fun s ω => c * H.process s ω := by
  funext s ω; simp [process, smul, Finset.mul_sum, mul_assoc]

@[simp] lemma running_smul (c : ℝ) (H : ElemIntegrand 𝓕 P ι) :
    (H.smul c).running W = fun t ω => c * H.running W t ω := by
  funext t ω; simp [running, smul, Finset.mul_sum, mul_assoc]

@[simp] lemma integral_reindex (e : ι ≃ κ) (H : ElemIntegrand 𝓕 P ι) :
    (H.reindex e).integral W = H.integral W := by
  funext ω
  simp only [integral, reindex, Function.comp]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

@[simp] lemma process_reindex (e : ι ≃ κ) (H : ElemIntegrand 𝓕 P ι) :
    (H.reindex e).process = H.process := by
  funext s ω
  simp only [process, reindex, Function.comp]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

@[simp] lemma running_reindex (e : ι ≃ κ) (H : ElemIntegrand 𝓕 P ι) :
    (H.reindex e).running W = H.running W := by
  funext t ω
  simp only [running, reindex, Function.comp]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

@[simp] lemma integral_zero : (zero : ElemIntegrand 𝓕 P (Fin 0)).integral W = 0 := by
  funext ω; simp [integral]

@[simp] lemma process_zero : (zero : ElemIntegrand 𝓕 P (Fin 0)).process = 0 := by
  funext s ω; simp [process]

/-- At any time after the last right endpoint the running integral is the full integral. -/
lemma running_eq_integral (H : ElemIntegrand 𝓕 P ι) {T : ℝ} (hT : ∀ i, H.right i ≤ T) :
    H.running W T = H.integral W := by
  funext ω
  simp only [running, integral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [min_eq_left (hT i), min_eq_left ((H.left_le_right i).trans (hT i))]

lemma process_eq_zero_of_le (H : ElemIntegrand 𝓕 P ι) {s : ℝ} (hs : s ≤ 0) (ω : Ω) :
    H.process s ω = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cellInd_notMem (fun h => absurd (hs.trans (H.left_nonneg i)) (not_le.mpr h.1)), mul_zero]

lemma process_eq_zero_of_ge (H : ElemIntegrand 𝓕 P ι) {T s : ℝ} (hT : ∀ i, H.right i ≤ T)
    (hs : T < s) (ω : Ω) : H.process s ω = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cellInd_notMem (fun h => absurd ((h.2.trans (hT i))) (not_le.mpr hs)), mul_zero]

lemma measurable_process (H : ElemIntegrand 𝓕 P ι) :
    Measurable (Function.uncurry H.process) := by
  unfold process
  have : Function.uncurry (fun s ω => ∑ i, H.val i ω * cellInd (H.left i) (H.right i) s) =
      fun p : ℝ × Ω => ∑ i, H.val i p.2 * cellInd (H.left i) (H.right i) p.1 := rfl
  rw [this]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((H.adapted i).mono (𝓕.le _)).measurable.comp measurable_snd |>.mul
    ((measurable_cellInd _ _).comp measurable_fst)

/-- The process of an elementary integrand is adapted. -/
lemma process_adapted (H : ElemIntegrand 𝓕 P ι) (s : ℝ) :
    StronglyMeasurable[𝓕 s] (H.process s) := by
  unfold process
  have : (fun ω => ∑ i, H.val i ω * cellInd (H.left i) (H.right i) s) =
      ∑ i, fun ω => H.val i ω * cellInd (H.left i) (H.right i) s := by
    funext ω; simp
  rw [this]
  refine Finset.stronglyMeasurable_sum _ fun i _ => ?_
  by_cases h : s ∈ Set.Ioc (H.left i) (H.right i)
  · simp only [cellInd_mem h, mul_one]
    exact (H.adapted i).mono (𝓕.mono h.1.le)
  · simp only [cellInd_notMem h, mul_zero]
    exact stronglyMeasurable_const

section Wiener

variable {W} (hW : IsFWiener W 𝓕 P)
include hW

lemma memLp_piece (H : ElemIntegrand 𝓕 P ι) (i : ι) :
    MemLp (fun ω => H.val i ω * (W (H.right i) ω - W (H.left i) ω)) 2 P :=
  hW.memLp_mul_incr (H.left_nonneg i) (H.left_le_right i) (H.adapted i) (H.memLp i)

/-- The elementary integral is square integrable. -/
theorem memLp_integral (H : ElemIntegrand 𝓕 P ι) : MemLp (H.integral W) 2 P := by
  have := memLp_finset_sum' (Finset.univ : Finset ι) fun i _ => H.memLp_piece hW i
  convert this using 1
  funext ω; simp [integral]

lemma measurable_integral (H : ElemIntegrand 𝓕 P ι) : Measurable (H.integral W) := by
  unfold integral
  exact Finset.measurable_sum _ fun i _ =>
    ((H.adapted i).mono (𝓕.le _)).measurable.mul (hW.measurable_incr _ _)

/-- **(4.2.40): the mean of an elementary integral vanishes.** -/
theorem integral_mean (H : ElemIntegrand 𝓕 P ι) : ∫ ω, H.integral W ω ∂P = 0 := by
  have := hW.isProbabilityMeasure
  simp only [integral]
  rw [integral_finset_sum _ fun i _ => (H.memLp_piece hW i).integrable one_le_two]
  refine Finset.sum_eq_zero fun i _ => ?_
  exact (hW.mul_incr (H.left_nonneg i) (H.left_le_right i) (H.adapted i)
    ((H.memLp i).integrable one_le_two)).2

end Wiener

end ElemIntegrand

namespace IsFWiener

variable {W : ℝ → Ω → ℝ} {𝓕 : Filtration ℝ mΩ} {P : Measure Ω} (hW : IsFWiener W 𝓕 P)
include hW

lemma sm_W {r u : ℝ} (hr : 0 ≤ r) (hru : r ≤ u) : StronglyMeasurable[𝓕 u] (W r) :=
  (hW.adapted r hr).mono (𝓕.mono hru)

/-- `E[Z (W b - W c)(W d - W c)] = E[Z] (b ∧ d - c)` for integrable `𝓕 c`-measurable `Z`. -/
lemma mul_incr_incr {c b d : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hcd : c ≤ d) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 c] Z) (hZi : Integrable Z P) :
    Integrable (fun ω => Z ω * ((W b ω - W c ω) * (W d ω - W c ω))) P ∧
    ∫ ω, Z ω * ((W b ω - W c ω) * (W d ω - W c ω)) ∂P = (∫ ω, Z ω ∂P) * (min b d - c) := by
  wlog hbd : b ≤ d generalizing b d
  · obtain ⟨h1, h2⟩ := this hcd hcb (le_of_not_ge hbd)
    refine ⟨h1.congr (Filter.Eventually.of_forall fun ω => by simp only; ring), ?_⟩
    rw [min_comm, ← h2]; congr 1; funext ω; ring
  rw [min_eq_left hbd]
  obtain ⟨hA, hA'⟩ := hW.mul_incr_sq hc hcb hZ hZi
  have hZb : StronglyMeasurable[𝓕 b] (fun ω => Z ω * (W b ω - W c ω)) :=
    (hZ.mono (𝓕.mono hcb)).mul ((hW.sm_W (hc.trans hcb) le_rfl).sub (hW.sm_W hc hcb))
  obtain ⟨hB, hB'⟩ := hW.mul_incr (hc.trans hcb) hbd hZb (hW.mul_incr hc hcb hZ hZi).1
  have e : (fun ω => Z ω * ((W b ω - W c ω) * (W d ω - W c ω))) =
      fun ω => Z ω * (W b ω - W c ω) ^ 2 + Z ω * (W b ω - W c ω) * (W d ω - W b ω) := by
    funext ω; ring
  rw [e]
  exact ⟨hA.add hB, by rw [integral_add hA hB, hA', hB', add_zero]⟩

/-- Cross moment of two pieces, `a ≤ c`. -/
lemma cross_of_le {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c) (hcd : c ≤ d)
    {φ ψ : Ω → ℝ} (hφ : StronglyMeasurable[𝓕 a] φ) (hψ : StronglyMeasurable[𝓕 c] ψ)
    (hφ2 : MemLp φ 2 P) (hψ2 : MemLp ψ 2 P) :
    ∫ ω, (φ ω * (W b ω - W a ω)) * (ψ ω * (W d ω - W c ω)) ∂P =
      (∫ ω, φ ω * ψ ω ∂P) * cellOverlap a b c d := by
  have hc : 0 ≤ c := ha.trans hac
  set m := min b c with hm
  have ham : a ≤ m := le_min hab hac
  have hmc : m ≤ c := min_le_right _ _
  -- the part of `(a, b]` before `c`
  have hX : StronglyMeasurable[𝓕 c] (fun ω => φ ω * (W m ω - W a ω) * ψ ω) :=
    ((hφ.mono (𝓕.mono hac)).mul ((hW.sm_W (ha.trans ham) hmc).sub (hW.sm_W ha hac))).mul hψ
  have hXi : Integrable (fun ω => φ ω * (W m ω - W a ω) * ψ ω) P := by
    have := (hW.memLp_mul_incr ha ham hφ hφ2).integrable_mul hψ2
    exact this.congr (Filter.Eventually.of_forall fun ω => rfl)
  obtain ⟨h1i, h1⟩ := hW.mul_incr hc hcd hX hXi
  have hφψ : Integrable (fun ω => φ ω * ψ ω) P := hφ2.integrable_mul hψ2
  have e : ∀ ω, (φ ω * (W b ω - W a ω)) * (ψ ω * (W d ω - W c ω)) =
      φ ω * (W m ω - W a ω) * ψ ω * (W d ω - W c ω) +
        (φ ω * (W b ω - W m ω)) * (ψ ω * (W d ω - W c ω)) := fun ω => by ring
  rcases le_total b c with hbc | hcb
  · -- disjoint intervals
    have hmb : m = b := min_eq_left hbc
    have : cellOverlap a b c d = 0 := by
      simp only [cellOverlap, max_eq_right hac]
      exact max_eq_right (by linarith [min_le_left b d])
    rw [this, mul_zero]
    simp_rw [e, hmb, sub_self, mul_zero, zero_mul, add_zero]
    rw [← hmb]; exact h1
  · have hmc' : m = c := min_eq_right hcb
    have hZ : StronglyMeasurable[𝓕 c] (fun ω => φ ω * ψ ω) := (hφ.mono (𝓕.mono hac)).mul hψ
    obtain ⟨h2i, h2⟩ := hW.mul_incr_incr hc hcb hcd hZ hφψ
    have hov : cellOverlap a b c d = min b d - c := by
      simp only [cellOverlap, max_eq_right hac]
      exact max_eq_left (by simp [hcb, hcd])
    rw [hov]
    simp_rw [e]
    rw [integral_add h1i]
    · rw [h1, zero_add, ← h2, hmc']
      congr 1; funext ω; ring
    · rw [hmc']
      exact h2i.congr (Filter.Eventually.of_forall fun ω => by simp only; ring)

/-- **Cross moment of two pieces**: `⟨φ ΔW_{(a,b]} ψ ΔW_{(c,d]}⟩ = ⟨φψ⟩ |(a,b] ∩ (c,d]|`. -/
theorem cross {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d)
    {φ ψ : Ω → ℝ} (hφ : StronglyMeasurable[𝓕 a] φ) (hψ : StronglyMeasurable[𝓕 c] ψ)
    (hφ2 : MemLp φ 2 P) (hψ2 : MemLp ψ 2 P) :
    ∫ ω, (φ ω * (W b ω - W a ω)) * (ψ ω * (W d ω - W c ω)) ∂P =
      (∫ ω, φ ω * ψ ω ∂P) * cellOverlap a b c d := by
  rcases le_total a c with hac | hca
  · exact hW.cross_of_le ha hab hac hcd hφ hψ hφ2 hψ2
  · have h := hW.cross_of_le hc hcd hca hab hψ hφ hψ2 hφ2
    have hov : cellOverlap c d a b = cellOverlap a b c d := by
      simp [cellOverlap, min_comm, max_comm]
    rw [hov] at h
    simp_rw [mul_comm (φ _ * _) (ψ _ * _), mul_comm (φ _) (ψ _)]
    exact h

end IsFWiener

namespace ElemIntegrand

variable {𝓕 : Filtration ℝ mΩ} {P : Measure Ω} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-- The correlation of two elementary integrals as a double sum. -/
theorem integral_mul_eq_sum (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) :
    ∫ ω, H.integral W ω * K.integral W ω ∂P = ∑ i, ∑ j, (∫ ω, H.val i ω * K.val j ω ∂P) *
      cellOverlap (H.left i) (H.right i) (K.left j) (K.right j) := by
  simp only [integral, Finset.sum_mul_sum]
  have hint : ∀ i j, Integrable (fun ω => H.val i ω * (W (H.right i) ω - W (H.left i) ω) *
      (K.val j ω * (W (K.right j) ω - W (K.left j) ω))) P := fun i j =>
    (H.memLp_piece hW i).integrable_mul (K.memLp_piece hW j)
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact hW.cross (H.left_nonneg i) (H.left_le_right i) (K.left_nonneg j) (K.left_le_right j)
    (H.adapted i) (K.adapted j) (H.memLp i) (K.memLp j)

omit hW in
lemma integral_process_mul (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) (s : ℝ) :
    ∫ ω, H.process s ω * K.process s ω ∂P = ∑ i, ∑ j, (∫ ω, H.val i ω * K.val j ω ∂P) *
      (cellInd (H.left i) (H.right i) s * cellInd (K.left j) (K.right j) s) := by
  simp only [process, Finset.sum_mul_sum]
  have hint : ∀ i j, Integrable (fun ω => H.val i ω * cellInd (H.left i) (H.right i) s *
      (K.val j ω * cellInd (K.left j) (K.right j) s)) P := fun i j => by
    have := ((H.memLp i).integrable_mul (K.memLp j)).mul_const
      (cellInd (H.left i) (H.right i) s * cellInd (K.left j) (K.right j) s)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]; ring
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_mul_const]
  congr 1; funext ω; ring

/-- **(4.2.42): the correlation formula (Itô isometry) for elementary integrands**,
`⟨∫ G dW ∫ H dW⟩ = ∫ ds ⟨G(s) H(s)⟩`. -/
theorem integral_mul (H : ElemIntegrand 𝓕 P ι) (K : ElemIntegrand 𝓕 P κ) :
    ∫ ω, H.integral W ω * K.integral W ω ∂P =
      ∫ s, (∫ ω, H.process s ω * K.process s ω ∂P) := by
  simp_rw [integral_process_mul H K]
  have hint : ∀ i j, Integrable (fun s => (∫ ω, H.val i ω * K.val j ω ∂P) *
      (cellInd (H.left i) (H.right i) s * cellInd (K.left j) (K.right j) s)) := fun i j => by
    simp_rw [cellInd_mul_cellInd]
    exact (integrable_cellInd _ _).const_mul _
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j,
    integral_mul_eq_sum hW H K]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_cellInd_mul_cellInd]

/-! ### The running integral is a martingale -/

/-- One piece of the running integral, `φ (W(b ∧ t) - W(a ∧ t))`. -/
def piece (W : ℝ → Ω → ℝ) (φ : Ω → ℝ) (a b t : ℝ) (ω : Ω) : ℝ :=
  φ ω * (W (min b t) ω - W (min a t) ω)

omit mΩ hW in
lemma piece_eq_zero {φ : Ω → ℝ} {a b t : ℝ} (hab : a ≤ b) (ht : t ≤ a) :
    piece W φ a b t = 0 := by
  funext ω
  simp [piece, min_eq_right ht, min_eq_right (ht.trans hab)]

omit mΩ hW in
lemma piece_eq {φ : Ω → ℝ} {a b t : ℝ} (ht : a ≤ t) :
    piece W φ a b t = fun ω => φ ω * (W (min b t) ω - W a ω) := by
  funext ω
  simp [piece, min_eq_left ht]

section Piece

variable {φ : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
  (hφ : StronglyMeasurable[𝓕 a] φ) (hφ2 : MemLp φ 2 P)
include ha hab hφ

include hφ2 in
lemma piece_memLp (t : ℝ) : MemLp (piece W φ a b t) 2 P := by
  have := hW.isProbabilityMeasure
  rcases le_total t a with hta | hat
  · rw [piece_eq_zero hab hta]; exact memLp_const 0
  · rw [piece_eq hat]
    exact hW.memLp_mul_incr ha (le_min hab hat) hφ hφ2

omit hφ2 in
lemma piece_sm (t : ℝ) : StronglyMeasurable[𝓕 t] (piece W φ a b t) := by
  rcases le_total t a with hta | hat
  · rw [piece_eq_zero hab hta]; exact stronglyMeasurable_const
  · rw [piece_eq hat]
    exact (hφ.mono (𝓕.mono hat)).mul
      ((hW.sm_W (ha.trans (le_min hab hat)) (min_le_right _ _)).sub (hW.sm_W ha hat))

include hφ2 in
lemma piece_condExp {s t : ℝ} (hst : s ≤ t) :
    P[piece W φ a b t | 𝓕 s] =ᵐ[P] piece W φ a b s := by
  have := hW.isProbabilityMeasure
  rcases le_total t a with hta | hat
  · rw [piece_eq_zero hab hta, piece_eq_zero hab (hst.trans hta), condExp_zero]
  rcases le_total a s with has | hsa
  · -- `a ≤ s ≤ t`
    have hs0 : 0 ≤ s := ha.trans has
    have hsplit : piece W φ a b t = piece W φ a b s +
        fun ω => φ ω * (W (min b t) ω - W (min b s) ω) := by
      rw [piece_eq hat, piece_eq has]; funext ω; simp only [Pi.add_apply]; ring
    have hsm := piece_sm hW ha hab hφ s
    have hint1 := (piece_memLp hW ha hab hφ hφ2 s).integrable one_le_two
    rcases le_total b s with hbs | hsb
    · have hz : (fun ω => φ ω * (W (min b t) ω - W (min b s) ω)) = 0 := by
        funext ω; simp [min_eq_left hbs, min_eq_left (hbs.trans hst)]
      rw [hsplit, hz, add_zero, condExp_of_stronglyMeasurable (𝓕.le s) hsm hint1]
    · have hbt : s ≤ min b t := le_min hsb hst
      have hφs : StronglyMeasurable[𝓕 s] φ := hφ.mono (𝓕.mono has)
      have hint2 : Integrable (fun ω => φ ω * (W (min b t) ω - W (min b s) ω)) P := by
        rw [min_eq_right hsb]
        exact (hW.memLp_mul_incr hs0 hbt hφs hφ2).integrable one_le_two
      rw [hsplit]
      refine (condExp_add hint1 hint2 _).trans ?_
      rw [condExp_of_stronglyMeasurable (𝓕.le s) hsm hint1]
      have h0 : P[fun ω => φ ω * (W (min b t) ω - W (min b s) ω) | 𝓕 s] =ᵐ[P] 0 := by
        rw [min_eq_right hsb]
        exact hW.condExp_mul_incr hs0 hbt hφs hφ2
      filter_upwards [h0] with ω hω
      simp [hω]
  · -- `s ≤ a ≤ t`
    have hzs : piece W φ a b s = 0 := piece_eq_zero hab hsa
    rw [hzs]
    have h1 : P[piece W φ a b t | 𝓕 a] =ᵐ[P] 0 := by
      rw [piece_eq hat]
      exact hW.condExp_mul_incr ha (le_min hab hat) hφ hφ2
    calc P[piece W φ a b t | 𝓕 s] =ᵐ[P] P[P[piece W φ a b t | 𝓕 a] | 𝓕 s] :=
          (condExp_condExp_of_le (𝓕.mono hsa) (𝓕.le a)).symm
      _ =ᵐ[P] P[(0 : Ω → ℝ) | 𝓕 s] := condExp_congr_ae h1
      _ = 0 := condExp_zero

end Piece

omit hW in
lemma running_eq_sum (H : ElemIntegrand 𝓕 P ι) (t : ℝ) :
    H.running W t = ∑ i, piece W (H.val i) (H.left i) (H.right i) t := by
  funext ω; simp [running, piece]

lemma memLp_running (H : ElemIntegrand 𝓕 P ι) (t : ℝ) : MemLp (H.running W t) 2 P := by
  rw [running_eq_sum]
  exact memLp_finset_sum' _ fun i _ =>
    piece_memLp hW (H.left_nonneg i) (H.left_le_right i) (H.adapted i) (H.memLp i) t

/-- **The martingale property of the running elementary integral** w.r.t. `𝓕`. -/
theorem martingale_running (H : ElemIntegrand 𝓕 P ι) : Martingale (H.running W) 𝓕 P := by
  have := hW.isProbabilityMeasure
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · rw [running_eq_sum]
    exact Finset.stronglyMeasurable_sum _ fun i _ =>
      piece_sm hW (H.left_nonneg i) (H.left_le_right i) (H.adapted i) t
  · rw [running_eq_sum, running_eq_sum]
    refine (condExp_finset_sum (fun i _ => (piece_memLp hW (H.left_nonneg i) (H.left_le_right i)
      (H.adapted i) (H.memLp i) t).integrable one_le_two) _).trans ?_
    have h : ∀ i, P[piece W (H.val i) (H.left i) (H.right i) t | 𝓕 s] =ᵐ[P]
        piece W (H.val i) (H.left i) (H.right i) s :=
      fun i => piece_condExp hW (H.left_nonneg i) (H.left_le_right i) (H.adapted i) (H.memLp i)
        hst
    filter_upwards [Filter.eventually_all.mpr h] with ω hω
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hω i

end ElemIntegrand

end Gardiner.Ito
