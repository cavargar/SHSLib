/-
# The Itô integral of simple nonanticipating integrands (Gardiner §4.2.1, §4.2.4, §4.2.6 e–f)

A simple integrand (`Gardiner.Ito.SimpleIntegrand W hWm P ι`) is a finite family of pieces
`φᵢ 1_{(aᵢ, bᵢ]}(s)` with `0 ≤ aᵢ ≤ bᵢ`, each value `φᵢ` measurable with respect to the natural
filtration `Gardiner.Ito.wienerFiltration` at its left endpoint `aᵢ` (nonanticipation) and square
integrable.  The pieces may overlap.  Its process is `G(s) = Σᵢ φᵢ 1_{(aᵢ,bᵢ]}(s)`
(`SimpleIntegrand.process`) and its stochastic integral is the left-point sum
`∫ G dW = Σᵢ φᵢ (W(bᵢ) - W(aᵢ))` (`SimpleIntegrand.integral`); the running integral is
`Σᵢ φᵢ (W(bᵢ ∧ t) - W(aᵢ ∧ t))` (`SimpleIntegrand.running`).

* **Linearity**: `SimpleIntegrand.integral_add`, `SimpleIntegrand.integral_smul` (and the same for
  `process`, `running`).
* **Mean value** (4.2.40)–(4.2.41): `⟨∫ G dW⟩ = 0` (`SimpleIntegrand.integral_mean`).
* **Correlation formula / Itô isometry** (4.2.42)–(4.2.44): for two simple integrands,
  `⟨∫ G dW ∫ H dW⟩ = Σᵢⱼ ⟨φᵢψⱼ⟩ |(aᵢ,bᵢ] ∩ (cⱼ,dⱼ]|` (`SimpleIntegrand.integral_mul_eq_sum`)
  `= ∫ ds ⟨G(s)H(s)⟩` (`SimpleIntegrand.integral_mul`), in particular
  `⟨(∫ G dW)²⟩ = ∫ ds ⟨G(s)²⟩` (`SimpleIntegrand.integral_sq`).
* **Martingale property** of the running integral with respect to the natural filtration
  (`SimpleIntegrand.martingale_running`), and `running T = integral` once `T ≥ bᵢ`
  (`SimpleIntegrand.running_eq_integral`).

Instances for `Gardiner.Ito.stdWiener` are in `SHSLib.Gardiner.Ito.WienerInstances`.  The
library's `SimpleProcess` is not used.
-/
import SHSLib.Gardiner.Ito.Increments

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ} {P : Measure Ω}

/-- The overlap length `|(a, b] ∩ (c, d]|`. -/
def overlap (a b c d : ℝ) : ℝ := max (min b d - max a c) 0

lemma overlap_comm (a b c d : ℝ) : overlap a b c d = overlap c d a b := by
  simp [overlap, min_comm, max_comm]

lemma integral_indicator_mul_indicator (a b c d : ℝ) :
    ∫ s, (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * (Set.Ioc c d).indicator (fun _ => 1) s =
      overlap a b c d := by
  have : (fun s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s *
      (Set.Ioc c d).indicator (fun _ => 1) s) =
      (Set.Ioc (max a c) (min b d)).indicator (fun _ => 1) := by
    funext s
    rw [← Set.Ioc_inter_Ioc]
    simp only [Set.indicator, Set.mem_inter_iff]
    split_ifs <;> simp_all
  rw [this, integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Ioc, overlap]

namespace IsWiener

variable (hW : IsWiener W P)
include hW

/-- A random variable measurable w.r.t. the past `𝓕 s` is independent of any function of a
future increment `W t - W s`. -/
lemma indepFun_past {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[wienerFiltration W hW.measurable s] Z) {g : ℝ → ℝ}
    (hg : Measurable g) : IndepFun Z (fun ω => g (W t ω - W s ω)) P := by
  have h := (hW.indep_past s t hs hst).symm
  have h1 : MeasurableSpace.comap Z inferInstance ≤ wienerFiltration W hW.measurable s :=
    hZ.measurable.comap_le
  have h2 : MeasurableSpace.comap (fun ω => g (W t ω - W s ω)) inferInstance ≤
      MeasurableSpace.comap (W t - W s) inferInstance := by
    have : (fun ω => g (W t ω - W s ω)) = g ∘ (W t - W s) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hg.comap_le
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h h1) h2

lemma integrable_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => W t ω - W s ω) P :=
  (hW.integrable (hs.trans hst)).sub (hW.integrable hs)

lemma integral_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W t ω - W s ω) ∂P = 0 := by
  rw [integral_sub (hW.integrable (hs.trans hst)) (hW.integrable hs),
    hW.integral_eq_zero (hs.trans hst), hW.integral_eq_zero hs, sub_zero]

lemma integrable_incr_sq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (W t ω - W s ω) ^ 2) P := by
  have := hW.isProbabilityMeasure
  exact Gardiner.SDE.integrable_comp_gauss (hW.measurable_sub s t) (hW.law_sub s t hs hst)
    (continuous_pow 2) (Gardiner.SDE.gauss_integrable_pow _ 2)

lemma integral_incr_sq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W t ω - W s ω) ^ 2 ∂P = t - s := by
  have := hW.isProbabilityMeasure
  have h := Gardiner.SDE.integral_comp_gauss (P := P) (hW.measurable_sub s t)
    (hW.law_sub s t hs hst) (continuous_pow 2)
  simp only [Pi.sub_apply] at h
  rw [h, Gardiner.SDE.gauss_m2, Real.coe_toNNReal _ (sub_nonneg.mpr hst)]

lemma memLp_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    MemLp (fun ω => W t ω - W s ω) 2 P :=
  (memLp_two_iff_integrable_sq (hW.measurable_sub s t).aestronglyMeasurable).mpr
    (hW.integrable_incr_sq hs hst)

/-- `E[Z (W t - W s)] = 0` for an integrable `𝓕 s`-measurable `Z`. -/
lemma mul_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[wienerFiltration W hW.measurable s] Z) (hZi : Integrable Z P) :
    Integrable (fun ω => Z ω * (W t ω - W s ω)) P ∧ ∫ ω, Z ω * (W t ω - W s ω) ∂P = 0 := by
  have hind := hW.indepFun_past hs hst hZ (g := id) measurable_id
  refine ⟨hind.integrable_mul hZi (hW.integrable_incr hs hst), ?_⟩
  have := hind.integral_mul_eq_mul_integral hZi.aestronglyMeasurable
    (hW.integrable_incr hs hst).aestronglyMeasurable
  simp only [Pi.mul_apply, id] at this
  rw [this, hW.integral_incr hs hst, mul_zero]

/-- `E[Z (W t - W s)²] = E[Z] (t - s)` for an integrable `𝓕 s`-measurable `Z`. -/
lemma mul_incr_sq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[wienerFiltration W hW.measurable s] Z) (hZi : Integrable Z P) :
    Integrable (fun ω => Z ω * (W t ω - W s ω) ^ 2) P ∧
      ∫ ω, Z ω * (W t ω - W s ω) ^ 2 ∂P = (∫ ω, Z ω ∂P) * (t - s) := by
  have hind := hW.indepFun_past hs hst hZ (g := fun x => x ^ 2) (measurable_id.pow_const 2)
  refine ⟨hind.integrable_mul hZi (hW.integrable_incr_sq hs hst), ?_⟩
  have := hind.integral_mul_eq_mul_integral hZi.aestronglyMeasurable
    (hW.integrable_incr_sq hs hst).aestronglyMeasurable
  simp only [Pi.mul_apply] at this
  rw [this, hW.integral_incr_sq hs hst]

/-- `Z (W t - W s)` is square integrable for a square-integrable `𝓕 s`-measurable `Z`. -/
lemma memLp_mul_incr {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[wienerFiltration W hW.measurable s] Z) (hZ2 : MemLp Z 2 P) :
    MemLp (fun ω => Z ω * (W t ω - W s ω)) 2 P := by
  have hZm : StronglyMeasurable Z := hZ.mono ((wienerFiltration W hW.measurable).le s)
  refine (memLp_two_iff_integrable_sq
    (hZm.measurable.mul (hW.measurable_sub s t)).aestronglyMeasurable).mpr ?_
  have hsq : StronglyMeasurable[wienerFiltration W hW.measurable s] (fun ω => Z ω ^ 2) :=
    hZ.pow 2
  have := (hW.mul_incr_sq hs hst hsq hZ2.integrable_sq).1
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply]; ring

lemma sm_W {r u : ℝ} (hr : 0 ≤ r) (hru : r ≤ u) :
    StronglyMeasurable[wienerFiltration W hW.measurable u] (W r) :=
  (hW.stronglyAdapted hr).mono ((wienerFiltration W hW.measurable).mono hru)

lemma sm_incr {r r' u : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') (hru : r' ≤ u) :
    StronglyMeasurable[wienerFiltration W hW.measurable u] (fun ω => W r' ω - W r ω) :=
  (hW.sm_W (hr.trans hrr) hru).sub (hW.sm_W hr (hrr.trans hru))

lemma cross_of_le {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c) (hcd : c ≤ d)
    {φ ψ : Ω → ℝ} (hφ : StronglyMeasurable[wienerFiltration W hW.measurable a] φ)
    (hψ : StronglyMeasurable[wienerFiltration W hW.measurable c] ψ) (hφ2 : MemLp φ 2 P)
    (hψ2 : MemLp ψ 2 P) :
    ∫ ω, (φ ω * (W b ω - W a ω)) * (ψ ω * (W d ω - W c ω)) ∂P =
      (∫ ω, φ ω * ψ ω ∂P) * overlap a b c d := by
  have hc : 0 ≤ c := ha.trans hac
  set 𝓕 := wienerFiltration W hW.measurable
  have hφc : StronglyMeasurable[𝓕 c] φ := hφ.mono (𝓕.mono hac)
  have hφψ : Integrable (fun ω => φ ω * ψ ω) P := hφ2.integrable_mul hψ2
  rcases le_or_gt b c with hbc | hcb
  · -- the first increment lies in the past of the second
    have hX : StronglyMeasurable[𝓕 c] (fun ω => φ ω * (W b ω - W a ω) * ψ ω) :=
      (hφc.mul (hW.sm_incr ha hab hbc)).mul hψ
    have hXi : Integrable (fun ω => φ ω * (W b ω - W a ω) * ψ ω) P :=
      (hW.memLp_mul_incr ha hab hφ hφ2).integrable_mul hψ2
    have h := (hW.mul_incr hc hcd hX hXi).2
    have hov : overlap a b c d = 0 := by
      simp only [overlap]
      refine max_eq_right ?_
      have : min b d ≤ b := min_le_left _ _
      have : c ≤ max a c := le_max_right _ _
      linarith
    rw [hov, mul_zero, ← h]
    congr 1; funext ω; ring
  · set e := min b d with he
    have hce : c ≤ e := le_min hcb.le hcd
    have heb : e ≤ b := min_le_left _ _
    have hed : e ≤ d := min_le_right _ _
    have hzero : ∀ ω, (W b ω - W e ω) * (W d ω - W e ω) = 0 := by
      intro ω
      rcases min_choice b d with h | h <;> rw [he, h] <;> simp
    -- the three pieces
    have hX1 : StronglyMeasurable[𝓕 c] (fun ω => φ ω * (W c ω - W a ω) * ψ ω) :=
      (hφc.mul (hW.sm_incr ha hac le_rfl)).mul hψ
    have hX1i : Integrable (fun ω => φ ω * (W c ω - W a ω) * ψ ω) P :=
      (hW.memLp_mul_incr ha hac hφ hφ2).integrable_mul hψ2
    obtain ⟨hT1i, hT1⟩ := hW.mul_incr hc hcd hX1 hX1i
    have hZ : StronglyMeasurable[𝓕 c] (fun ω => φ ω * ψ ω) := hφc.mul hψ
    obtain ⟨hT2i, hT2⟩ := hW.mul_incr_sq hc hce hZ hφψ
    obtain ⟨hZ3i, -⟩ := hW.mul_incr hc hce hZ hφψ
    have hZ3 : StronglyMeasurable[𝓕 e] (fun ω => φ ω * ψ ω * (W e ω - W c ω)) :=
      (hZ.mono (𝓕.mono hce)).mul (hW.sm_incr hc hce le_rfl)
    have he0 : 0 ≤ e := hc.trans hce
    obtain ⟨hT3i, hT3⟩ := hW.mul_incr he0 heb hZ3 hZ3i
    obtain ⟨hT4i, hT4⟩ := hW.mul_incr he0 hed hZ3 hZ3i
    have hsplit : (fun ω => (φ ω * (W b ω - W a ω)) * (ψ ω * (W d ω - W c ω))) = fun ω =>
        ((φ ω * (W c ω - W a ω) * ψ ω) * (W d ω - W c ω) +
          φ ω * ψ ω * (W e ω - W c ω) ^ 2) +
        ((φ ω * ψ ω * (W e ω - W c ω)) * (W b ω - W e ω) +
          (φ ω * ψ ω * (W e ω - W c ω)) * (W d ω - W e ω)) := by
      funext ω
      have h0 := hzero ω
      linear_combination φ ω * ψ ω * h0
    have e1 := integral_add (hT1i.add hT2i) (hT3i.add hT4i)
    have e2 := integral_add hT1i hT2i
    have e3 := integral_add hT3i hT4i
    simp only [Pi.add_apply] at e1 e2 e3
    rw [hsplit, e1, e2, e3, hT1, hT2, hT3, hT4]
    have hov : overlap a b c d = e - c := by
      simp only [overlap, max_eq_right hac]
      exact max_eq_left (by linarith)
    rw [hov]; ring

/-- **The basic correlation identity.**  For square-integrable `φ` (measurable at time `a`) and
`ψ` (measurable at time `c`), `E[φ ΔW_{(a,b]} · ψ ΔW_{(c,d]}] = E[φψ] |(a,b] ∩ (c,d]|`. -/
theorem cross {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d)
    {φ ψ : Ω → ℝ} (hφ : StronglyMeasurable[wienerFiltration W hW.measurable a] φ)
    (hψ : StronglyMeasurable[wienerFiltration W hW.measurable c] ψ) (hφ2 : MemLp φ 2 P)
    (hψ2 : MemLp ψ 2 P) :
    ∫ ω, (φ ω * (W b ω - W a ω)) * (ψ ω * (W d ω - W c ω)) ∂P =
      (∫ ω, φ ω * ψ ω ∂P) * overlap a b c d := by
  rcases le_total a c with hac | hca
  · exact hW.cross_of_le ha hab hac hcd hφ hψ hφ2 hψ2
  · have h := hW.cross_of_le hc hcd hca hab hψ hφ hψ2 hφ2
    rw [overlap_comm]
    simp_rw [mul_comm (φ _ * _) (ψ _ * _), mul_comm (φ _) (ψ _)]
    exact h

/-- `E[φ (W v - W u) | 𝓕 u] = 0` for square-integrable `𝓕 u`-measurable `φ`. -/
lemma condExp_mul_incr {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) {φ : Ω → ℝ}
    (hφ : StronglyMeasurable[wienerFiltration W hW.measurable u] φ) (hφ2 : MemLp φ 2 P) :
    P[fun ω => φ ω * (W v ω - W u ω) | wienerFiltration W hW.measurable u] =ᵐ[P] 0 := by
  have := hW.isProbabilityMeasure
  set 𝓕 := wienerFiltration W hW.measurable
  have h1 : P[φ * (W v - W u) | 𝓕 u] =ᵐ[P] φ * P[W v - W u | 𝓕 u] :=
    condExp_mul_of_stronglyMeasurable_left hφ
      ((hW.memLp_mul_incr hu huv hφ hφ2).integrable one_le_two)
      (hW.integrable_incr hu huv)
  have h2 : P[W v - W u | 𝓕 u] =ᵐ[P] fun _ => ∫ ω, (W v - W u) ω ∂P :=
    condExp_indep_eq (hW.measurable_sub u v).comap_le (𝓕.le u)
      (comap_measurable (W v - W u)).stronglyMeasurable (hW.indep_past u v hu huv)
  have h3 : ∫ ω, (W v - W u) ω ∂P = 0 := hW.integral_incr hu huv
  change P[φ * (W v - W u) | 𝓕 u] =ᵐ[P] 0
  filter_upwards [h1, h2] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, h3, mul_zero]; rfl

end IsWiener

/-- The indicator `1_{(a,b]}` as a real function. -/
def ind (a b : ℝ) (s : ℝ) : ℝ := (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s

lemma integrable_ind_mul_ind (a b c d : ℝ) : Integrable (fun s => ind a b s * ind c d s) := by
  have : (fun s => ind a b s * ind c d s) =
      (Set.Ioc (max a c) (min b d)).indicator (fun _ => (1 : ℝ)) := by
    funext s
    rw [← Set.Ioc_inter_Ioc]
    simp only [ind, Set.indicator, Set.mem_inter_iff]
    split_ifs <;> simp_all
  rw [this]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (integrableOn_const (by simp [Real.volume_Ioc]))

lemma integral_ind_mul_ind (a b c d : ℝ) : ∫ s, ind a b s * ind c d s = overlap a b c d :=
  integral_indicator_mul_indicator a b c d

/-- **A simple (elementary) nonanticipating integrand** (Gardiner §4.2.1, §4.2.4):
`G(s) = Σᵢ φᵢ 1_{(aᵢ, bᵢ]}(s)`, a finite sum over an index type `ι`, where `0 ≤ aᵢ ≤ bᵢ` and
each value `φᵢ` is square integrable and measurable with respect to the natural filtration at the
left endpoint `aᵢ`.  The pieces may overlap; a step function on a partition is the special case
of adjacent intervals. -/
structure SimpleIntegrand (W : ℝ → Ω → ℝ) (hWm : ∀ t, Measurable (W t)) (P : Measure Ω)
    (ι : Type*) [Fintype ι] where
  /-- left endpoints -/
  left : ι → ℝ
  /-- right endpoints -/
  right : ι → ℝ
  /-- values -/
  val : ι → Ω → ℝ
  left_nonneg : ∀ i, 0 ≤ left i
  left_le_right : ∀ i, left i ≤ right i
  adapted : ∀ i, StronglyMeasurable[wienerFiltration W hWm (left i)] (val i)
  memLp : ∀ i, MemLp (val i) 2 P

namespace SimpleIntegrand

variable {hWm : ∀ t, Measurable (W t)} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The integrand as a process, `G(s, ω) = Σᵢ φᵢ(ω) 1_{(aᵢ, bᵢ]}(s)`. -/
def process (H : SimpleIntegrand W hWm P ι) (s : ℝ) (ω : Ω) : ℝ :=
  ∑ i, H.val i ω * ind (H.left i) (H.right i) s

/-- **The stochastic integral of a simple integrand**, `∫ G dW = Σᵢ φᵢ (W(bᵢ) - W(aᵢ))`
(the left-point sum of Gardiner (4.2.41)). -/
def integral (H : SimpleIntegrand W hWm P ι) (ω : Ω) : ℝ :=
  ∑ i, H.val i ω * (W (H.right i) ω - W (H.left i) ω)

/-- The running integral `∫₀ᵗ G dW = Σᵢ φᵢ (W(bᵢ ∧ t) - W(aᵢ ∧ t))`. -/
def running (H : SimpleIntegrand W hWm P ι) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i, H.val i ω * (W (min (H.right i) t) ω - W (min (H.left i) t) ω)

/-- The sum of two simple integrands (concatenation of their pieces). -/
def add (H : SimpleIntegrand W hWm P ι) (K : SimpleIntegrand W hWm P κ) :
    SimpleIntegrand W hWm P (ι ⊕ κ) where
  left := Sum.elim H.left K.left
  right := Sum.elim H.right K.right
  val := Sum.elim H.val K.val
  left_nonneg i := by cases i <;> simp [H.left_nonneg, K.left_nonneg]
  left_le_right i := by cases i <;> simp [H.left_le_right, K.left_le_right]
  adapted i := by cases i <;> simp [H.adapted, K.adapted]
  memLp i := by cases i <;> simp [H.memLp, K.memLp]

/-- A scalar multiple of a simple integrand. -/
def smul (c : ℝ) (H : SimpleIntegrand W hWm P ι) : SimpleIntegrand W hWm P ι where
  left := H.left
  right := H.right
  val i := fun ω => c * H.val i ω
  left_nonneg := H.left_nonneg
  left_le_right := H.left_le_right
  adapted i := (H.adapted i).const_mul c
  memLp i := (H.memLp i).const_mul c

/-- **Linearity**: `∫ (G + H) dW = ∫ G dW + ∫ H dW`. -/
theorem integral_add (H : SimpleIntegrand W hWm P ι) (K : SimpleIntegrand W hWm P κ) :
    (H.add K).integral = H.integral + K.integral := by
  funext ω
  simp [integral, add, Fintype.sum_sum_type]

theorem process_add (H : SimpleIntegrand W hWm P ι) (K : SimpleIntegrand W hWm P κ) :
    (H.add K).process = H.process + K.process := by
  funext s ω
  simp [process, add, Fintype.sum_sum_type]

theorem running_add (H : SimpleIntegrand W hWm P ι) (K : SimpleIntegrand W hWm P κ) :
    (H.add K).running = H.running + K.running := by
  funext t ω
  simp [running, add, Fintype.sum_sum_type]

/-- **Linearity**: `∫ cG dW = c ∫ G dW`. -/
theorem integral_smul (c : ℝ) (H : SimpleIntegrand W hWm P ι) :
    (H.smul c).integral = c • H.integral := by
  funext ω
  simp [integral, smul, Finset.mul_sum, mul_assoc]

theorem process_smul (c : ℝ) (H : SimpleIntegrand W hWm P ι) :
    (H.smul c).process = c • H.process := by
  funext s ω
  simp [process, smul, Finset.mul_sum, mul_assoc]

section Wiener

variable {hW : IsWiener W P}

lemma memLp_piece (hW : IsWiener W P) (H : SimpleIntegrand W hW.measurable P ι) (i : ι) :
    MemLp (fun ω => H.val i ω * (W (H.right i) ω - W (H.left i) ω)) 2 P :=
  hW.memLp_mul_incr (H.left_nonneg i) (H.left_le_right i) (H.adapted i) (H.memLp i)

/-- The simple integral is square integrable. -/
theorem memLp_integral (hW : IsWiener W P) (H : SimpleIntegrand W hW.measurable P ι) :
    MemLp H.integral 2 P := by
  have := memLp_finset_sum' (Finset.univ : Finset ι) fun i _ => H.memLp_piece hW i
  convert this using 1
  funext ω; simp [integral]

/-- **(4.2.40)–(4.2.41): the mean of the simple integral vanishes**, `⟨∫ G dW⟩ = 0`. -/
theorem integral_mean (hW : IsWiener W P) (H : SimpleIntegrand W hW.measurable P ι) :
    ∫ ω, H.integral ω ∂P = 0 := by
  have := hW.isProbabilityMeasure
  simp only [integral]
  rw [integral_finset_sum _ fun i _ => (H.memLp_piece hW i).integrable one_le_two]
  refine Finset.sum_eq_zero fun i _ => ?_
  exact (hW.mul_incr (H.left_nonneg i) (H.left_le_right i) (H.adapted i)
    ((H.memLp i).integrable one_le_two)).2

/-- The correlation of two simple integrals as a double sum (Gardiner (4.2.43)–(4.2.44)):
`⟨∫ G dW ∫ H dW⟩ = Σᵢ Σⱼ ⟨φᵢψⱼ⟩ |(aᵢ,bᵢ] ∩ (cⱼ,dⱼ]|`. -/
theorem integral_mul_eq_sum (hW : IsWiener W P) (H : SimpleIntegrand W hW.measurable P ι)
    (K : SimpleIntegrand W hW.measurable P κ) :
    ∫ ω, H.integral ω * K.integral ω ∂P = ∑ i, ∑ j, (∫ ω, H.val i ω * K.val j ω ∂P) *
      overlap (H.left i) (H.right i) (K.left j) (K.right j) := by
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

lemma integral_process_mul (hW : IsWiener W P) (H : SimpleIntegrand W hW.measurable P ι)
    (K : SimpleIntegrand W hW.measurable P κ) (s : ℝ) :
    ∫ ω, H.process s ω * K.process s ω ∂P = ∑ i, ∑ j, (∫ ω, H.val i ω * K.val j ω ∂P) *
      (ind (H.left i) (H.right i) s * ind (K.left j) (K.right j) s) := by
  simp only [process, Finset.sum_mul_sum]
  have hint : ∀ i j, Integrable (fun ω => H.val i ω * ind (H.left i) (H.right i) s *
      (K.val j ω * ind (K.left j) (K.right j) s)) P := fun i j => by
    have := ((H.memLp i).integrable_mul (K.memLp j)).mul_const
      (ind (H.left i) (H.right i) s * ind (K.left j) (K.right j) s)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]; ring
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_mul_const]
  congr 1; funext ω; ring

/-- **(4.2.42): the correlation formula (Itô isometry) for simple integrands**,
`⟨∫ G dW ∫ H dW⟩ = ∫ ds ⟨G(s) H(s)⟩`. -/
theorem integral_mul (hW : IsWiener W P) (H : SimpleIntegrand W hW.measurable P ι)
    (K : SimpleIntegrand W hW.measurable P κ) :
    ∫ ω, H.integral ω * K.integral ω ∂P =
      ∫ s, (∫ ω, H.process s ω * K.process s ω ∂P) := by
  simp_rw [integral_process_mul hW H K]
  have hint : ∀ i j, Integrable (fun s => (∫ ω, H.val i ω * K.val j ω ∂P) *
      (ind (H.left i) (H.right i) s * ind (K.left j) (K.right j) s)) := fun i j =>
    (integrable_ind_mul_ind _ _ _ _).const_mul _
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j,
    integral_mul_eq_sum hW H K]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_ind_mul_ind]

/-- **The Itô isometry for simple integrands**, `⟨(∫ G dW)²⟩ = ∫ ds ⟨G(s)²⟩`. -/
theorem integral_sq (hW : IsWiener W P) (H : SimpleIntegrand W hW.measurable P ι) :
    ∫ ω, H.integral ω ^ 2 ∂P = ∫ s, (∫ ω, H.process s ω ^ 2 ∂P) := by
  simp_rw [sq]; exact integral_mul hW H H

/-! ### The running integral is a martingale -/

/-- One piece of the running integral, `φ (W(b ∧ t) - W(a ∧ t))`. -/
def piece (W : ℝ → Ω → ℝ) (φ : Ω → ℝ) (a b t : ℝ) (ω : Ω) : ℝ :=
  φ ω * (W (min b t) ω - W (min a t) ω)

omit [MeasurableSpace Ω] in
lemma piece_eq_zero {φ : Ω → ℝ} {a b t : ℝ} (hab : a ≤ b) (ht : t ≤ a) :
    piece W φ a b t = 0 := by
  funext ω
  simp [piece, min_eq_right ht, min_eq_right (ht.trans hab)]

omit [MeasurableSpace Ω] in
lemma piece_eq {φ : Ω → ℝ} {a b t : ℝ} (ht : a ≤ t) :
    piece W φ a b t = fun ω => φ ω * (W (min b t) ω - W a ω) := by
  funext ω
  simp [piece, min_eq_left ht]

section Piece

variable (hW : IsWiener W P) {φ : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
  (hφ : StronglyMeasurable[wienerFiltration W hW.measurable a] φ) (hφ2 : MemLp φ 2 P)
include ha hab hφ hφ2

lemma piece_memLp (t : ℝ) : MemLp (piece W φ a b t) 2 P := by
  have := hW.isProbabilityMeasure
  rcases le_or_gt t a with ht | ht
  · rw [piece_eq_zero hab ht]; exact MemLp.zero
  · rw [piece_eq ht.le]
    exact hW.memLp_mul_incr ha (le_min hab ht.le) hφ hφ2

omit hφ2 in
lemma piece_sm (t : ℝ) :
    StronglyMeasurable[wienerFiltration W hW.measurable t] (piece W φ a b t) := by
  rcases le_or_gt t a with ht | ht
  · rw [piece_eq_zero hab ht]; exact stronglyMeasurable_zero
  · rw [piece_eq ht.le]
    exact (hφ.mono ((wienerFiltration W hW.measurable).mono ht.le)).mul
      (hW.sm_incr ha (le_min hab ht.le) (min_le_right _ _))

lemma piece_condExp {s t : ℝ} (hst : s ≤ t) :
    P[piece W φ a b t | wienerFiltration W hW.measurable s] =ᵐ[P] piece W φ a b s := by
  have := hW.isProbabilityMeasure
  set 𝓕 := wienerFiltration W hW.measurable
  rcases le_or_gt t a with hta | hat
  · rw [piece_eq_zero hab hta, piece_eq_zero hab (hst.trans hta), condExp_zero]
  rcases le_or_gt s a with hsa | has
  · -- the piece starts after `s`: tower property through `𝓕 a`
    rw [piece_eq_zero hab hsa, piece_eq hat.le]
    have hz := hW.condExp_mul_incr ha (le_min hab hat.le) hφ hφ2
    refine (condExp_condExp_of_le (𝓕.mono hsa) (𝓕.le a)).symm.trans ?_
    refine (condExp_congr_ae hz).trans ?_
    rw [condExp_zero]
  · -- the piece started before `s`
    have hbs : a ≤ min b s := le_min hab has.le
    have hbt : min b s ≤ min b t := min_le_min_left b hst
    rw [piece_eq hat.le, piece_eq has.le]
    have hsplit : (fun ω => φ ω * (W (min b t) ω - W a ω)) =
        (fun ω => φ ω * (W (min b s) ω - W a ω)) +
          fun ω => φ ω * (W (min b t) ω - W (min b s) ω) := by
      funext ω; simp only [Pi.add_apply]; ring
    have hX1 : StronglyMeasurable[𝓕 s] (fun ω => φ ω * (W (min b s) ω - W a ω)) :=
      (hφ.mono (𝓕.mono has.le)).mul (hW.sm_incr ha hbs (min_le_right _ _))
    have hX1i : Integrable (fun ω => φ ω * (W (min b s) ω - W a ω)) P :=
      (hW.memLp_mul_incr ha hbs hφ hφ2).integrable one_le_two
    have hX2 : P[fun ω => φ ω * (W (min b t) ω - W (min b s) ω) | 𝓕 s] =ᵐ[P] 0 := by
      rcases le_or_gt b s with hbs' | hsb
      · have h1 : min b s = b := min_eq_left hbs'
        have h2 : min b t = b := min_eq_left (hbs'.trans hst)
        have : (fun ω => φ ω * (W (min b t) ω - W (min b s) ω)) = 0 := by
          funext ω; simp [h1, h2]
        rw [this, condExp_zero]
      · have h1 : min b s = s := min_eq_right hsb.le
        rw [h1]
        have hs0 : 0 ≤ s := ha.trans has.le
        exact hW.condExp_mul_incr hs0 (le_min (hsb.le) hst) (hφ.mono (𝓕.mono has.le)) hφ2
    have hX2i : Integrable (fun ω => φ ω * (W (min b t) ω - W (min b s) ω)) P := by
      have hi1 := (hW.memLp_mul_incr ha (hbs.trans hbt) hφ hφ2).integrable one_le_two
      have := hi1.sub hX1i
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Pi.sub_apply]; ring
    rw [hsplit]
    refine (condExp_add hX1i hX2i _).trans ?_
    rw [condExp_of_stronglyMeasurable (𝓕.le s) hX1 hX1i]
    filter_upwards [hX2] with ω h
    simp [h]

end Piece

lemma running_eq_sum (H : SimpleIntegrand W hWm P ι) (t : ℝ) :
    H.running t = ∑ i, piece W (H.val i) (H.left i) (H.right i) t := by
  funext ω; simp [running, piece]

/-- **The martingale property of the running simple integral**: `t ↦ ∫₀ᵗ G dW` is a
martingale with respect to the natural filtration of `W`. -/
theorem martingale_running (hW : IsWiener W P) (H : SimpleIntegrand W hW.measurable P ι) :
    Martingale H.running (wienerFiltration W hW.measurable) P := by
  have := hW.isProbabilityMeasure
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · rw [running_eq_sum]
    exact Finset.stronglyMeasurable_sum _ fun i _ =>
      piece_sm hW (H.left_nonneg i) (H.left_le_right i) (H.adapted i) t
  · rw [running_eq_sum, running_eq_sum]
    refine (condExp_finset_sum (fun i _ => (piece_memLp hW (H.left_nonneg i) (H.left_le_right i)
      (H.adapted i) (H.memLp i) t).integrable one_le_two) _).trans ?_
    have h : ∀ i, P[piece W (H.val i) (H.left i) (H.right i) t |
        wienerFiltration W hW.measurable s] =ᵐ[P] piece W (H.val i) (H.left i) (H.right i) s :=
      fun i => piece_condExp hW (H.left_nonneg i) (H.left_le_right i) (H.adapted i) (H.memLp i)
        hst
    filter_upwards [Filter.eventually_all.mpr h] with ω hω
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hω i

/-- At any time after the last right endpoint the running integral is the full integral. -/
theorem running_eq_integral (H : SimpleIntegrand W hWm P ι) {T : ℝ}
    (hT : ∀ i, H.right i ≤ T) : H.running T = H.integral := by
  funext ω
  simp only [running, integral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [min_eq_left (hT i), min_eq_left ((H.left_le_right i).trans (hT i))]

end Wiener

end SimpleIntegrand

end Gardiner.Ito
