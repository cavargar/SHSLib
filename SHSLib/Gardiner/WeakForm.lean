/-
The weak form of the differential Chapman–Kolmogorov equation: equations
(3.4.8)–(3.4.16) of Gardiner, §3.4.1.
-/
import SHSLib.Gardiner.Taylor

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-! ### Elementary boundedness facts for a compactly supported `C²` test function -/

lemma exists_bound_of_contDiff_hasCompactSupport {g : Sp n → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x| ≤ C := by
  obtain ⟨x₀, hx₀⟩ := (hg.norm).exists_forall_ge_of_hasCompactSupport hs.norm
  exact ⟨‖g x₀‖, norm_nonneg _, fun x => hx₀ x⟩

lemma hasCompactSupport_pd {f : Sp n → ℝ} (hs : HasCompactSupport f)
    (i : Fin n) : HasCompactSupport (pd f i) := by
  have h := hs.fderiv ℝ
  refine h.mono ?_
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx ⊢
  intro hcon
  exact hx (by simp [pd, hcon])

lemma hasCompactSupport_pd2 {f : Sp n → ℝ} (hs : HasCompactSupport f)
    (i j : Fin n) : HasCompactSupport (pd2 f i j) :=
  hasCompactSupport_pd (hasCompactSupport_pd hs j) i

lemma abs_coord_le_norm (v : Sp n) (i : Fin n) : |v i| ≤ ‖v‖ := PiLp.norm_apply_le v i

/-- On the region `|x - z| < ε` the Taylor polynomial (3.4.10) is bounded. -/
lemma taylorPoly_bounded (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ (nearDiag ε : Set (Sp n × Sp n)), |taylorPoly f q.2 q.1| ≤ C := by
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hpd : ∀ i : Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |pd f i z| ≤ C := fun i =>
    exists_bound_of_contDiff_hasCompactSupport (continuous_pd f h1 i)
      (hasCompactSupport_pd hs i)
  have hpd2 : ∀ i j : Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |pd2 f i j z| ≤ C := fun i j =>
    exists_bound_of_contDiff_hasCompactSupport (continuous_pd2 f hf i j)
      (hasCompactSupport_pd2 hs i j)
  choose Cp hCp0 hCp using hpd
  choose Cq hCq0 hCq using hpd2
  have hCpsum : (0 : ℝ) ≤ ∑ i, Cp i := Finset.sum_nonneg fun i _ => hCp0 i
  have hCqsum : (0 : ℝ) ≤ ∑ i, ∑ j, Cq i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hCq0 i j
  refine ⟨(∑ i, Cp i) * ε + (1 / 2) * ((∑ i, ∑ j, Cq i j) * ε ^ 2),
    add_nonneg (mul_nonneg hCpsum hε.le)
      (mul_nonneg (by norm_num) (mul_nonneg hCqsum (by positivity))), ?_⟩
  rintro ⟨x, z⟩ hq
  have hd : ‖x - z‖ < ε := by simpa [nearDiag, dist_eq_norm] using hq
  have hco : ∀ i : Fin n, |x i - z i| ≤ ε := fun i =>
    le_of_lt (lt_of_le_of_lt (by simpa [sub_apply] using abs_coord_le_norm (x - z) i) hd)
  have hlin : |∑ i, pd f i z * (x i - z i)| ≤ (∑ i, Cp i) * ε := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact mul_le_mul (hCp i z) (hco i) (abs_nonneg _) (hCp0 i)
  have hquad : |∑ i, ∑ j, pd2 f i j z * (x i - z i) * (x j - z j)|
      ≤ (∑ i, ∑ j, Cq i j) * ε ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_mul, sq]
    calc |pd2 f i j z| * |x i - z i| * |x j - z j|
        ≤ Cq i j * ε * ε := by
          refine mul_le_mul (mul_le_mul (hCq i j z) (hco i) (abs_nonneg _) (hCq0 i j)) (hco j)
            (abs_nonneg _) (mul_nonneg (hCq0 i j) hε.le)
      _ = Cq i j * (ε * ε) := by ring
  calc |taylorPoly f z x|
      ≤ |∑ i, pd f i z * (x i - z i)|
        + |(1 / 2 : ℝ) * ∑ i, ∑ j, pd2 f i j z * (x i - z i) * (x j - z j)| :=
        abs_add_le _ _
    _ ≤ (∑ i, Cp i) * ε + (1 / 2) * ((∑ i, ∑ j, Cq i j) * ε ^ 2) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
        exact add_le_add hlin (by linarith [hquad])

/-! ### Integrability helpers -/

variable {p : ℝ → Sp n → ℝ} {k : ℝ → Sp n → Sp n → ℝ} {t : ℝ}

lemma integrableOn_mul_of_bounded {W : Sp n × Sp n → ℝ} (hW : Integrable W)
    {g : Sp n × Sp n → ℝ} (hg : Continuous g) {s : Set (Sp n × Sp n)} (hs : MeasurableSet s)
    {C : ℝ} (hb : ∀ q ∈ s, |g q| ≤ C) : IntegrableOn (fun q => g q * W q) s := by
  refine Integrable.bdd_mul (c := C) hW.restrict hg.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem hs] with q hq using hb q hq

lemma integrable_mul_of_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : α → ℝ} (hW : Integrable W μ) {g : α → ℝ} (hg : AEStronglyMeasurable g μ)
    {C : ℝ} (hb : ∀ x, |g x| ≤ C) : Integrable (fun x => g x * W x) μ :=
  Integrable.bdd_mul (c := C) hW hg (Filter.Eventually.of_forall hb)

/-! ### From (3.4.8) to (3.4.9) -/

/-- Combination of (3.4.8) and (3.4.9): using the Chapman–Kolmogorov equation and the
normalisation of the transition density, the difference quotient is a single double
integral of `f(x) - f(z)`. -/
theorem diffQuot_eq (f : Sp n → ℝ) (dt : ℝ)
    (hck : ∀ x, p (t + dt) x = ∫ z, k dt z x * p t z)
    (hnorm : ∀ z, ∫ x, k dt z x = 1)
    (hprod : Integrable (fun q : Sp n × Sp n => f q.1 * kernelWeight p k t dt q))
    (hprod' : Integrable (fun q : Sp n × Sp n => f q.2 * kernelWeight p k t dt q)) :
    diffQuot p f t dt
      = (1 / dt) * ∫ q, (f q.1 - f q.2) * kernelWeight p k t dt q := by
  have hvol : (volume : Measure (Sp n × Sp n)) = (volume : Measure (Sp n)).prod volume :=
    Measure.volume_eq_prod _ _
  -- the positive term, via the Chapman–Kolmogorov equation
  have h1 : ∫ x, f x * p (t + dt) x = ∫ q, f q.1 * kernelWeight p k t dt q := by
    have : ∀ x, f x * p (t + dt) x = ∫ z, f x * (k dt z x * p t z) := by
      intro x
      rw [MeasureTheory.integral_const_mul, ← hck x]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall this)]
    rw [hvol]
    exact MeasureTheory.integral_integral (by rw [← hvol]; exact hprod)
  -- the negative term, via the normalisation of the transition density
  have h2 : ∫ q, f q.2 * kernelWeight p k t dt q = ∫ z, f z * p t z := by
    rw [hvol, MeasureTheory.integral_prod_symm _ (by rw [← hvol]; exact hprod')]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (∫ x, f (x, z).2 * kernelWeight p k t dt (x, z)) = f z * p t z
    have hx : ∀ x, f (x, z).2 * kernelWeight p k t dt (x, z) = (f z * p t z) * k dt z x := by
      intro x; simp only [kernelWeight]; ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hx),
      MeasureTheory.integral_const_mul, hnorm z, mul_one]
  have h3 : ∫ q, (f q.1 - f q.2) * kernelWeight p k t dt q
      = (∫ q, f q.1 * kernelWeight p k t dt q) - ∫ q, f q.2 * kernelWeight p k t dt q := by
    rw [← MeasureTheory.integral_sub hprod hprod']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    ring
  have h4 : (∫ x, f x * p (t + dt) x) - ∫ z, f z * p t z
      = ∫ q, (f q.1 - f q.2) * kernelWeight p k t dt q := by
    rw [h3, h1, h2]
  simp only [diffQuot]
  rw [h4, one_div, inv_mul_eq_div]

/-! ### (3.4.12): splitting into the two regions and the Taylor expansion -/

/-- (3.4.12): the difference quotient is the sum of the three contributions
`Q12` (lines 1,2), `Q3` (line 3) and `Qjump` (lines 4–6). -/
theorem diffQuot_split (f : Sp n → ℝ) (dt ε : ℝ)
    (hInear : IntegrableOn
        (fun q : Sp n × Sp n => taylorPoly f q.2 q.1 * kernelWeight p k t dt q) (nearDiag ε))
    (hIrem : IntegrableOn
        (fun q : Sp n × Sp n => taylorRem f q.2 q.1 * kernelWeight p k t dt q) (nearDiag ε))
    (hIfar : IntegrableOn
        (fun q : Sp n × Sp n => (f q.1 - f q.2) * kernelWeight p k t dt q) (farDiag ε))
    (hbase : diffQuot p f t dt = (1 / dt) * ∫ q, (f q.1 - f q.2) * kernelWeight p k t dt q) :
    diffQuot p f t dt = Q12 p k f t dt ε + Q3 p k f t dt ε + Qjump p k f t dt ε := by
  have hfun : (fun q : Sp n × Sp n => (f q.1 - f q.2) * kernelWeight p k t dt q)
      = fun q => taylorPoly f q.2 q.1 * kernelWeight p k t dt q
          + taylorRem f q.2 q.1 * kernelWeight p k t dt q := by
    funext q; rw [taylor_decomp f q.2 q.1]; ring
  have hInearFull : IntegrableOn
      (fun q : Sp n × Sp n => (f q.1 - f q.2) * kernelWeight p k t dt q) (nearDiag ε) := by
    rw [hfun]; exact hInear.add hIrem
  have hIfull : Integrable (fun q : Sp n × Sp n => (f q.1 - f q.2) * kernelWeight p k t dt q) := by
    have : IntegrableOn (fun q : Sp n × Sp n => (f q.1 - f q.2) * kernelWeight p k t dt q)
        (nearDiag ε ∪ (nearDiag ε)ᶜ) := by
      rw [MeasureTheory.integrableOn_union]
      exact ⟨hInearFull, by rw [← farDiag_eq_compl]; exact hIfar⟩
    rwa [Set.union_compl_self, MeasureTheory.integrableOn_univ] at this
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_nearDiag ε) hIfull
  have hnearsplit : ∫ q in nearDiag ε, (f q.1 - f q.2) * kernelWeight p k t dt q
      = (∫ q in nearDiag ε, taylorPoly f q.2 q.1 * kernelWeight p k t dt q)
        + ∫ q in nearDiag ε, taylorRem f q.2 q.1 * kernelWeight p k t dt q := by
    rw [hfun, MeasureTheory.integral_add hInear hIrem]
  rw [hbase, Q12, Q3, Qjump, ← hsplit, hnearsplit, ← farDiag_eq_compl]
  ring

/-! ### (3.4.14): the remainder term is negligible -/

/-- (3.4.14): line 3 of (3.4.12) is bounded by the second moment times the
supremum of the remainder `R` on the `ε`-ball. -/
theorem Q3_le (f : Sp n → ℝ) (dt ε δ : ℝ) (hdt : 0 < dt)
    (hp0 : ∀ z, 0 ≤ p t z) (hk0 : ∀ z x, 0 ≤ k dt z x)
    (hrem : ∀ z x : Sp n, ‖x - z‖ < ε → |taylorRem f z x| ≤ δ * ‖x - z‖ ^ 2)
    (hIrem : IntegrableOn
        (fun q : Sp n × Sp n => taylorRem f q.2 q.1 * kernelWeight p k t dt q) (nearDiag ε))
    (hIsq : IntegrableOn
        (fun q : Sp n × Sp n => ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q) (nearDiag ε)) :
    |Q3 p k f t dt ε| ≤ δ * Qsq p k t dt ε := by
  have hkw : ∀ q : Sp n × Sp n, 0 ≤ kernelWeight p k t dt q := fun q =>
    mul_nonneg (hk0 q.2 q.1) (hp0 q.2)
  have hpt : ∀ q ∈ (nearDiag ε : Set (Sp n × Sp n)),
      |taylorRem f q.2 q.1 * kernelWeight p k t dt q|
        ≤ δ * ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q := by
    intro q hq
    have hd : ‖q.1 - q.2‖ < ε := by simpa [nearDiag, dist_eq_norm] using hq
    rw [abs_mul, abs_of_nonneg (hkw q)]
    exact mul_le_mul_of_nonneg_right (hrem q.2 q.1 hd) (hkw q)
  have hmono : ∫ q in nearDiag ε, |taylorRem f q.2 q.1 * kernelWeight p k t dt q|
      ≤ ∫ q in nearDiag ε, δ * ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q := by
    refine MeasureTheory.integral_mono_ae hIrem.abs ?_ ?_
    · have := hIsq.const_mul δ
      refine this.congr (Filter.Eventually.of_forall fun q => by ring)
    · filter_upwards [ae_restrict_mem (measurableSet_nearDiag ε)] with q hq using hpt q hq
  have habs : |∫ q in nearDiag ε, taylorRem f q.2 q.1 * kernelWeight p k t dt q|
      ≤ ∫ q in nearDiag ε, |taylorRem f q.2 q.1 * kernelWeight p k t dt q| := by
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := (volume : Measure (Sp n × Sp n)).restrict (nearDiag ε))
        (f := fun q => taylorRem f q.2 q.1 * kernelWeight p k t dt q))
  have hconst : ∫ q in nearDiag ε, δ * ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q
      = δ * ∫ q in nearDiag ε, ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => by ring)
  rw [Q3, Qsq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / dt)]
  calc (1 / dt) * |∫ q in nearDiag ε, taylorRem f q.2 q.1 * kernelWeight p k t dt q|
      ≤ (1 / dt) * (δ * ∫ q in nearDiag ε, ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q) := by
        rw [← hconst]
        exact mul_le_mul_of_nonneg_left (habs.trans hmono) (by positivity)
    _ = δ * ((1 / dt) * ∫ q in nearDiag ε, ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q) := by ring

lemma Qsq_nonneg (dt ε : ℝ) (hdt : 0 < dt)
    (hp0 : ∀ z, 0 ≤ p t z) (hk0 : ∀ z x, 0 ≤ k dt z x) :
    0 ≤ Qsq p k t dt ε := by
  refine mul_nonneg (by positivity) ?_
  refine MeasureTheory.setIntegral_nonneg (measurableSet_nearDiag ε) fun q _ => ?_
  exact mul_nonneg (by positivity) (mul_nonneg (hk0 q.2 q.1) (hp0 q.2))

/-! ### (3.4.15): recombination of lines 4–6 -/

/-- (3.4.15): after the change of variables `x ↔ z` in the gain term, the jump
contribution takes the familiar master-equation form. -/
theorem jumpPre_eq_jumpTerm (W : Sp n → Sp n → ℝ) (f : Sp n → ℝ) (ε : ℝ)
    (hI : IntegrableOn (fun q : Sp n × Sp n => f q.1 * (W q.1 q.2 * p t q.2)) (farDiag ε))
    (hI' : IntegrableOn (fun q : Sp n × Sp n => f q.2 * (W q.1 q.2 * p t q.2)) (farDiag ε))
    (hIs : IntegrableOn (fun q : Sp n × Sp n => f q.2 * (W q.2 q.1 * p t q.1)) (farDiag ε)) :
    jumpPre p W f t ε = jumpTerm p W f t ε := by
  classical
  have hmeas : MeasurableSet (farDiag ε : Set (Sp n × Sp n)) := measurableSet_farDiag ε
  have hvol : (volume : Measure (Sp n × Sp n)) = (volume : Measure (Sp n)).prod volume :=
    Measure.volume_eq_prod _ _
  set F1 : Sp n × Sp n → ℝ := fun q => f q.1 * (W q.1 q.2 * p t q.2) with hF1
  set F2 : Sp n × Sp n → ℝ := fun q => f q.2 * (W q.1 q.2 * p t q.2) with hF2
  set F1' : Sp n × Sp n → ℝ := fun q => f q.2 * (W q.2 q.1 * p t q.1) with hF1'
  set G : Sp n × Sp n → ℝ :=
    fun q => f q.2 * (W q.2 q.1 * p t q.1 - W q.1 q.2 * p t q.2) with hG
  -- (i) split the integrand of `jumpPre`
  have hsplit : jumpPre p W f t ε
      = (∫ q in farDiag ε, F1 q) - ∫ q in farDiag ε, F2 q := by
    rw [jumpPre, ← MeasureTheory.integral_sub hI hI']
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => by
      simp only [hF1, hF2]; ring)
  -- (ii) the change of variables `x ↔ z` in the gain term
  have hpt : ∀ q : Sp n × Sp n,
      (Set.indicator (farDiag ε) F1) q.swap = Set.indicator (farDiag ε) F1' q := by
    intro q
    by_cases hq : q ∈ (farDiag ε : Set (Sp n × Sp n))
    · rw [Set.indicator_of_mem (farDiag_symm hq), Set.indicator_of_mem hq]
      simp [hF1, hF1']
    · have hq' : q.swap ∉ (farDiag ε : Set (Sp n × Sp n)) := by
        intro h
        exact hq (by simpa using farDiag_symm h)
      rw [Set.indicator_of_notMem hq', Set.indicator_of_notMem hq]
  have hswap : (∫ q in farDiag ε, F1 q) = ∫ q in farDiag ε, F1' q := by
    have hs := MeasureTheory.integral_prod_swap (μ := (volume : Measure (Sp n)))
      (ν := (volume : Measure (Sp n))) (Set.indicator (farDiag ε) F1)
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)] at hs
    rw [← hvol, MeasureTheory.integral_indicator hmeas,
      MeasureTheory.integral_indicator hmeas] at hs
    exact hs.symm
  -- (iii) recombine into the master-equation form
  have hIG : IntegrableOn G (farDiag ε) := by
    have := hIs.sub hI'
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply, hF1', hF2, hG]; ring
  have hcomb : (∫ q in farDiag ε, F1' q) - (∫ q in farDiag ε, F2 q)
      = ∫ q in farDiag ε, G q := by
    rw [← MeasureTheory.integral_sub hIs hI']
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => by
      simp only [hF1', hF2, hG]; ring)
  -- (iv) write the double integral as an iterated one
  have hiter : (∫ q in farDiag ε, G q) = jumpTerm p W f t ε := by
    have hind : Integrable (Set.indicator (farDiag ε) G)
        ((volume : Measure (Sp n)).prod volume) := by
      rw [← hvol]
      exact (MeasureTheory.integrable_indicator_iff hmeas).mpr hIG
    rw [← MeasureTheory.integral_indicator hmeas, hvol,
      MeasureTheory.integral_prod_symm _ hind]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (∫ x, Set.indicator (farDiag ε) G (x, z))
      = f z * ∫ x in (ball z ε)ᶜ, (W z x * p t x - W x z * p t z)
    have hcompl : MeasurableSet ((ball z ε)ᶜ : Set (Sp n)) := measurableSet_ball.compl
    have hindeq : ∀ x : Sp n, Set.indicator (farDiag ε) G (x, z)
        = Set.indicator ((ball z ε)ᶜ) (fun x => G (x, z)) x := by
      intro x
      by_cases hx : ((x, z) : Sp n × Sp n) ∈ farDiag ε
      · have hx' : x ∈ ((ball z ε)ᶜ : Set (Sp n)) := by
          simpa [Metric.mem_ball, not_lt] using (hx : ε ≤ dist x z)
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      · have hx' : x ∉ ((ball z ε)ᶜ : Set (Sp n)) := by
          simp only [farDiag, Set.mem_setOf_eq, not_le] at hx
          simp [Metric.mem_ball, hx]
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hindeq),
      MeasureTheory.integral_indicator hcompl, ← MeasureTheory.integral_const_mul]
  rw [hsplit, hswap, hcomb, hiter]

/-! ### (3.4.16): the weak form of the differential Chapman–Kolmogorov equation -/

/-- **The weak form of the differential Chapman–Kolmogorov equation**, (3.4.16).

`L` is the time derivative `∂_t ∫ dz f(z) p(z,t|y,t')` of (3.4.8), `driftDiffTerm`
is the drift/diffusion contribution (3.4.13) and `J` is the principal value integral
(3.4.17) of the jump contribution (3.4.15).

The hypotheses are exactly the steps of Gardiner's derivation: `hsplit` is the
decomposition (3.4.12), `h12` is the passage to the limit in lines 1 and 2 giving
(3.4.13) up to `O(ε)` (encoded by the error function `e`), `hsq` and `hM` express
that the second moment (3.4.14) stays bounded, `hjump` is the limit of lines 4–6,
and `hPV` is the existence of the principal value integral (3.4.17). -/
theorem differentialCK_weak
    (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (W : Sp n → Sp n → ℝ)
    (f : Sp n → ℝ) (L J : ℝ) (e M : ℝ → ℝ) (C : ℝ)
    (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hsplit : ∀ dt > 0, ∀ ε > 0,
      diffQuot p f t dt = Q12 p k f t dt ε + Q3 p k f t dt ε + Qjump p k f t dt ε)
    (hQ3le : ∀ dt > 0, ∀ ε > 0, ∀ δ ≥ (0 : ℝ),
      (∀ z x : Sp n, ‖x - z‖ < ε → |taylorRem f z x| ≤ δ * ‖x - z‖ ^ 2) →
      |Q3 p k f t dt ε| ≤ δ * Qsq p k t dt ε)
    (hD : Tendsto (diffQuot p f t) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (h12 : ∀ ε > 0, Tendsto (fun dt => Q12 p k f t dt ε) (𝓝[>] (0 : ℝ))
      (𝓝 (driftDiffTerm p A B f t + e ε)))
    (he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hsq : ∀ ε > 0, Tendsto (fun dt => Qsq p k t dt ε) (𝓝[>] (0 : ℝ)) (𝓝 (M ε)))
    (hM : ∀ ε > 0, |M ε| ≤ C)
    (hjump : ∀ ε > 0, Tendsto (fun dt => Qjump p k f t dt ε) (𝓝[>] (0 : ℝ))
      (𝓝 (jumpPre p W f t ε)))
    (hPV : Tendsto (fun ε => jumpPre p W f t ε) (𝓝[>] (0 : ℝ)) (𝓝 J)) :
    L = driftDiffTerm p A B f t + J := by
  set IAB := driftDiffTerm p A B f t with hIAB
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hM 1 one_pos)
  set q3 : ℝ → ℝ := fun ε => L - (IAB + e ε) - jumpPre p W f t ε with hq3def
  -- Line 3 of (3.4.12) converges, being the difference of the other three quantities.
  have hQ3lim : ∀ ε > 0, Tendsto (fun dt => Q3 p k f t dt ε) (𝓝[>] (0 : ℝ)) (𝓝 (q3 ε)) := by
    intro ε hε
    have hEq : (fun dt => diffQuot p f t dt - Q12 p k f t dt ε - Qjump p k f t dt ε)
        =ᶠ[𝓝[>] (0 : ℝ)] fun dt => Q3 p k f t dt ε := by
      filter_upwards [self_mem_nhdsWithin] with dt hdt
      have := hsplit dt hdt ε hε
      linarith
    exact Tendsto.congr' hEq ((hD.sub (h12 ε hε)).sub (hjump ε hε))
  -- (3.4.14): the limit of line 3 is arbitrarily small for small `ε`.
  have hbound : ∀ δ > (0 : ℝ), ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → |q3 ε| ≤ δ * C := by
    intro δ hδ
    obtain ⟨ε₀, hε₀, hrem⟩ := uniform_taylorRem f hf hfs hδ
    refine ⟨ε₀, hε₀, fun ε hε hle => ?_⟩
    have hb : ∀ dt ∈ Set.Ioi (0 : ℝ), |Q3 p k f t dt ε| ≤ δ * Qsq p k t dt ε := by
      intro dt hdt
      exact hQ3le dt hdt ε hε δ hδ.le fun z x hx => hrem z x (lt_of_lt_of_le hx hle)
    have h1 : Tendsto (fun dt => |Q3 p k f t dt ε|) (𝓝[>] (0 : ℝ)) (𝓝 |q3 ε|) :=
      (hQ3lim ε hε).abs
    have h2 : Tendsto (fun dt => δ * Qsq p k t dt ε) (𝓝[>] (0 : ℝ)) (𝓝 (δ * M ε)) :=
      (hsq ε hε).const_mul δ
    have hle' : |q3 ε| ≤ δ * M ε := by
      refine le_of_tendsto_of_tendsto h1 h2 ?_
      filter_upwards [self_mem_nhdsWithin] with dt hdt using hb dt hdt
    have hMC : M ε ≤ C := le_trans (le_abs_self _) (hM ε hε)
    exact hle'.trans (by nlinarith)
  -- Hence the limit of line 3 vanishes as `ε → 0`.
  have hq3 : Tendsto q3 (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro η hη
    obtain ⟨ε₀, hε₀, hb⟩ := hbound (η / (2 * (C + 1))) (by positivity)
    filter_upwards [Ioc_mem_nhdsGT hε₀] with ε hε
    have := hb ε hε.1 hε.2
    have hlt : η / (2 * (C + 1)) * C < η := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    simpa [Real.norm_eq_abs] using lt_of_le_of_lt this hlt
  -- (3.4.16): let `ε → 0` in the (ε-independent) left-hand side.
  have hsum : Tendsto (fun ε : ℝ => IAB + e ε + q3 ε + jumpPre p W f t ε) (𝓝[>] (0 : ℝ))
      (𝓝 (IAB + 0 + 0 + J)) :=
    ((tendsto_const_nhds.add he).add hq3).add hPV
  have hconst : (fun ε : ℝ => IAB + e ε + q3 ε + jumpPre p W f t ε) = fun _ => L := by
    funext ε; simp only [hq3def]; ring
  rw [hconst] at hsum
  have := tendsto_nhds_unique tendsto_const_nhds hsum
  simpa using this

/-! ### The derivation, assembled -/

/-- On the region `|x - z| < ε` the Taylor remainder (3.4.10) is bounded. -/
lemma taylorRem_bounded (f : Sp n → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ (nearDiag ε : Set (Sp n × Sp n)), |taylorRem f q.2 q.1| ≤ C := by
  obtain ⟨Cf, hCf0, hCf⟩ := exists_bound_of_contDiff_hasCompactSupport hf.continuous hs
  obtain ⟨Cp, hCp0, hCp⟩ := taylorPoly_bounded f hf hs ε hε
  have : (0 : ℝ) ≤ Cp := hCp0
  refine ⟨2 * Cf + Cp, by positivity, fun q hq => ?_⟩
  have hdec : taylorRem f q.2 q.1 = (f q.1 - f q.2) - taylorPoly f q.2 q.1 := by
    have := taylor_decomp f q.2 q.1; linarith
  rw [hdec]
  calc |f q.1 - f q.2 - taylorPoly f q.2 q.1|
      ≤ |f q.1 - f q.2| + |taylorPoly f q.2 q.1| := abs_sub _ _
    _ ≤ (|f q.1| + |f q.2|) + Cp := add_le_add (abs_sub _ _) (hCp q hq)
    _ ≤ 2 * Cf + Cp := by linarith [hCf q.1, hCf q.2]

/-- **The weak form of the differential Chapman–Kolmogorov equation** (3.4.16), assembled
from the Chapman–Kolmogorov equation, the normalisation of the transition density and
the limits taken in Gardiner's derivation.

Here `hck` is the Chapman–Kolmogorov equation used in (3.4.9), `hnorm` the normalisation
of `p(x, t + Δt | z, t)` used in the last line of (3.4.12), and `hwint` the integrability
of the weight `p(x, t + Δt | z, t) p(z, t | y, t')`.  The remaining hypotheses are the
limits taken in the derivation: `hD` is (3.4.8), `h12` and `he` are lines 1,2 giving
(3.4.13) up to `O(ε)`, `hsq` and `hM` control the second moment appearing in (3.4.14),
`hjump` is the limit of lines 4–6, and `hPV` is the existence of the principal value
integral (3.4.17). -/
theorem differentialCK_weak_of_kernel
    (A : Sp n → Fin n → ℝ) (B : Sp n → Fin n → Fin n → ℝ) (W : Sp n → Sp n → ℝ)
    (f : Sp n → ℝ) (L J : ℝ) (e M : ℝ → ℝ) (C : ℝ)
    (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hp0 : ∀ z, 0 ≤ p t z) (hk0 : ∀ dt z x, 0 ≤ k dt z x)
    (hck : ∀ dt x, p (t + dt) x = ∫ z, k dt z x * p t z)
    (hnorm : ∀ dt z, ∫ x, k dt z x = 1)
    (hwint : ∀ dt, Integrable (kernelWeight p k t dt))
    (hD : Tendsto (diffQuot p f t) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (h12 : ∀ ε > 0, Tendsto (fun dt => Q12 p k f t dt ε) (𝓝[>] (0 : ℝ))
      (𝓝 (driftDiffTerm p A B f t + e ε)))
    (he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hsq : ∀ ε > 0, Tendsto (fun dt => Qsq p k t dt ε) (𝓝[>] (0 : ℝ)) (𝓝 (M ε)))
    (hM : ∀ ε > 0, |M ε| ≤ C)
    (hjump : ∀ ε > 0, Tendsto (fun dt => Qjump p k f t dt ε) (𝓝[>] (0 : ℝ))
      (𝓝 (jumpPre p W f t ε)))
    (hPV : Tendsto (fun ε => jumpPre p W f t ε) (𝓝[>] (0 : ℝ)) (𝓝 J)) :
    L = driftDiffTerm p A B f t + J := by
  obtain ⟨Cf, -, hCf⟩ := exists_bound_of_contDiff_hasCompactSupport hf.continuous hfs
  -- the integrability of every integrand occurring in (3.4.9) and (3.4.12)
  have hprod : ∀ dt, Integrable (fun q : Sp n × Sp n => f q.1 * kernelWeight p k t dt q) :=
    fun dt => integrable_mul_of_bounded (hwint dt)
      (hf.continuous.comp continuous_fst).aestronglyMeasurable (fun q => hCf q.1)
  have hprod' : ∀ dt, Integrable (fun q : Sp n × Sp n => f q.2 * kernelWeight p k t dt q) :=
    fun dt => integrable_mul_of_bounded (hwint dt)
      (hf.continuous.comp continuous_snd).aestronglyMeasurable (fun q => hCf q.2)
  have hdiff : ∀ dt, Integrable
      (fun q : Sp n × Sp n => (f q.1 - f q.2) * kernelWeight p k t dt q) := fun dt =>
    integrable_mul_of_bounded (hwint dt)
      ((hf.continuous.comp continuous_fst).sub
        (hf.continuous.comp continuous_snd)).aestronglyMeasurable
      (fun q => (abs_sub _ _).trans (by linarith [hCf q.1, hCf q.2] :
        |f q.1| + |f q.2| ≤ 2 * Cf))
  have hInear : ∀ dt, ∀ ε > 0, IntegrableOn
      (fun q : Sp n × Sp n => taylorPoly f q.2 q.1 * kernelWeight p k t dt q) (nearDiag ε) := by
    intro dt ε hε
    obtain ⟨Cp, _, hCp⟩ := taylorPoly_bounded f hf hfs ε hε
    exact integrableOn_mul_of_bounded (hwint dt) (continuous_taylorPoly f hf)
      (measurableSet_nearDiag ε) hCp
  have hIrem : ∀ dt, ∀ ε > 0, IntegrableOn
      (fun q : Sp n × Sp n => taylorRem f q.2 q.1 * kernelWeight p k t dt q) (nearDiag ε) := by
    intro dt ε hε
    obtain ⟨Cr, _, hCr⟩ := taylorRem_bounded f hf hfs ε hε
    exact integrableOn_mul_of_bounded (hwint dt) (continuous_taylorRem f hf)
      (measurableSet_nearDiag ε) hCr
  have hIsq : ∀ dt, ∀ ε > 0, IntegrableOn
      (fun q : Sp n × Sp n => ‖q.1 - q.2‖ ^ 2 * kernelWeight p k t dt q) (nearDiag ε) := by
    intro dt ε hε
    refine integrableOn_mul_of_bounded (hwint dt) ?_ (measurableSet_nearDiag ε)
      (C := ε ^ 2) ?_
    · exact (continuous_fst.sub continuous_snd).norm.pow 2
    · intro q hq
      have hd : ‖q.1 - q.2‖ < ε := by simpa [nearDiag, dist_eq_norm] using hq
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hd.le 2
  -- (3.4.12)
  have hsplit : ∀ dt > 0, ∀ ε > 0,
      diffQuot p f t dt = Q12 p k f t dt ε + Q3 p k f t dt ε + Qjump p k f t dt ε := by
    intro dt _ ε hε
    refine diffQuot_split f dt ε (hInear dt ε hε) (hIrem dt ε hε)
      ((hdiff dt).integrableOn) ?_
    exact diffQuot_eq f dt (hck dt) (hnorm dt) (hprod dt) (hprod' dt)
  -- (3.4.14)
  have hQ3le : ∀ dt > 0, ∀ ε > 0, ∀ δ ≥ (0 : ℝ),
      (∀ z x : Sp n, ‖x - z‖ < ε → |taylorRem f z x| ≤ δ * ‖x - z‖ ^ 2) →
      |Q3 p k f t dt ε| ≤ δ * Qsq p k t dt ε := by
    intro dt hdt ε hε δ _ hrem
    exact Q3_le f dt ε δ hdt hp0 (hk0 dt) hrem (hIrem dt ε hε) (hIsq dt ε hε)
  exact differentialCK_weak A B W f L J e M C hf hfs hsplit hQ3le hD h12 he hsq hM hjump hPV

end Gardiner
