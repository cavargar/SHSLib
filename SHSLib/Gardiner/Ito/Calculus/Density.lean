/-
# Density of elementary integrands (Gardiner §4.2.6)

`Gardiner.Ito.exists_elem_approx`: every Itô integrand `G` on `[0, T]` (jointly measurable,
nonanticipating, `⟨∫₀ᵀ G² dt⟩ < ∞`) is the limit, in the norm `⟨∫₀ᵀ (G - H)² dt⟩^{1/2}`, of
elementary integrands `H` supported in `(0, T]`.

The proof follows the classical argument for measurable adapted processes (Doob's
"random shift"):

1. truncation `max (-K) (min K G)` reduces to bounded `G` (dominated convergence);
2. extend `G` by `0` outside `[0, T]` and, for a mesh `h > 0` and a shift `s ∈ (0, h)`, sample it
   at the left end of the cells `(s + jh, s + (j+1)h]`.  This is an elementary integrand, since the
   value on a cell is `𝓕` at its left end.  Averaging the squared error over the shift `s` gives
   exactly the average of `⟨∫ (G(t - q) - G(t))² dt⟩` over `q ∈ (0, h)` (a periodic change of
   variables, `Gardiner.Ito.integral_cellPos`), which tends to `0` with `h` by continuity of
   translation in `L²(ℝ)` (`Gardiner.Ito.tendsto_translate_sq`);
3. hence some shift has small error.
-/
import SHSLib.Gardiner.Ito.Calculus.Translation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito

/-! ### Real-variable lemmas: shifted grids -/

/-- Left end of the cell `(s + jh, s + (j+1)h]` containing `t`. -/
def cellLeft (h s t : ℝ) : ℝ := s + h * (⌈(t - s) / h⌉ - 1)

/-- Position of `v` inside its cell `(jh, (j+1)h]`, a value in `(0, h]`. -/
def cellPos (h v : ℝ) : ℝ := v - h * (⌈v / h⌉ - 1)

lemma cellLeft_eq (h s t : ℝ) : cellLeft h s t = t - cellPos h (t - s) := by
  unfold cellLeft cellPos; ring

lemma cellPos_periodic {h : ℝ} (hh : h ≠ 0) : Function.Periodic (cellPos h) h := by
  intro v
  unfold cellPos
  rw [add_div, div_self hh, Int.ceil_add_one]
  push_cast; ring

lemma cellPos_of_mem {h v : ℝ} (hh : 0 < h) (hv : v ∈ Set.Ioc 0 h) : cellPos h v = v := by
  unfold cellPos
  have : ⌈v / h⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · simp only [Int.cast_one, sub_self]; exact div_pos hv.1 hh
    · simp only [Int.cast_one]; exact (div_le_one hh).mpr hv.2
  rw [this]; simp

lemma measurable_cellLeft (h : ℝ) : Measurable fun p : ℝ × ℝ => cellLeft h p.1 p.2 := by
  unfold cellLeft
  refine measurable_fst.add (measurable_const.mul (Measurable.sub ?_ measurable_const))
  exact (measurable_from_top (f := (Int.cast : ℤ → ℝ))).comp
    (Int.measurable_ceil.comp ((measurable_snd.sub measurable_fst).div_const h))

/-- **The periodic change of variables**: averaging a function of the position inside the cell
over the shift `s ∈ (0, h]` is averaging it over the cell. -/
lemma integral_cellPos {h : ℝ} (hh : 0 < h) (F : ℝ → ℝ) (t : ℝ) :
    ∫ s in Set.Ioc 0 h, F (cellPos h (t - s)) = ∫ q in Set.Ioc 0 h, F q := by
  rw [← intervalIntegral.integral_of_le hh.le, ← intervalIntegral.integral_of_le hh.le,
    intervalIntegral.integral_comp_sub_left (fun v => F (cellPos h v)) t]
  have hper : Function.Periodic (fun v => F (cellPos h v)) h := fun v => by
    simp only [cellPos_periodic hh.ne' v]
  have := hper.intervalIntegral_add_eq (t - h) 0
  rw [show t - h + h = t by ring, zero_add] at this
  rw [sub_zero, this]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun v hv => ?_)
  rw [Set.uIoc_of_le hh.le] at hv
  simp [cellPos_of_mem hh hv]

/-! ### Truncation -/

/-- Truncation at level `K`. -/
def clip (K x : ℝ) : ℝ := max (-K) (min K x)

lemma continuous_clip (K : ℝ) : Continuous (clip K) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma abs_clip_le {K : ℝ} (hK : 0 ≤ K) (x : ℝ) : |clip K x| ≤ K := by
  unfold clip; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clip_of_abs_le {K x : ℝ} (hx : |x| ≤ K) : clip K x = x := by
  unfold clip; rw [abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1]

lemma abs_clip_sub_le {K : ℝ} (hK : 0 ≤ K) (x : ℝ) : |clip K x - x| ≤ |x| := by
  unfold clip
  rcases le_total x K with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-K) x with h2 | h2
    · rw [max_eq_right h2]; simp
    · rw [max_eq_left h2, abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonneg (by linarith)]; linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}

lemma IsItoIntegrand.clip {T : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) {K : ℝ}
    (hK : 0 ≤ K) : IsItoIntegrand 𝓕 P T (fun t ω => clip K (G t ω)) where
  measurable := (continuous_clip K).measurable.comp hG.measurable
  adapted t ht htT := (continuous_clip K).comp_stronglyMeasurable (hG.adapted t ht htT)
  memLp := hG.memLp.of_le ((continuous_clip K).measurable.comp hG.measurable).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      simp only [Function.uncurry, Real.norm_eq_abs]
      rcases le_total (|G p.1 p.2|) K with h | h
      · rw [clip_of_abs_le h]
      · exact (abs_clip_le hK _).trans h)

lemma tendsto_clip [SFinite P] {T : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) :
    Tendsto (fun n : ℕ => ∫ p, (clip n (Function.uncurry G p) - Function.uncurry G p) ^ 2
      ∂(tsMeasure P T)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := tsMeasure P T)
    (F := fun n : ℕ => fun p => (clip n (Function.uncurry G p) - Function.uncurry G p) ^ 2)
    (f := fun _ => 0) (fun p => Function.uncurry G p ^ 2)
    (fun n => ((((continuous_clip n).measurable.comp hG.measurable).sub hG.measurable).pow_const
      2).aestronglyMeasurable)
    hG.memLp.integrable_sq
    (fun n => Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_pow]
      show _ ≤ Function.uncurry G p ^ 2
      rw [← sq_abs (Function.uncurry G p)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_clip_sub_le (Nat.cast_nonneg n) _) 2)
    (Eventually.of_forall fun p => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|Function.uncurry G p|⌉₊] with n hn
      rw [clip_of_abs_le ((Nat.le_ceil _).trans (Nat.cast_le.mpr hn))]; simp)
  simpa using h

/-! ### The bounded case -/

/-- Extension of `G` by `0` outside `[0, T]`. -/
def extIcc (T : ℝ) (G : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (Set.Icc 0 T).indicator (fun t' => G t' ω) t

omit mΩ in
lemma extIcc_of_mem {T : ℝ} {G : ℝ → Ω → ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) (ω : Ω) :
    extIcc T G t ω = G t ω := by
  simp [extIcc, Set.indicator_of_mem ht]

omit mΩ in
lemma extIcc_of_notMem {T : ℝ} {G : ℝ → Ω → ℝ} {t : ℝ} (ht : t ∉ Set.Icc 0 T) (ω : Ω) :
    extIcc T G t ω = 0 := by
  simp [extIcc, Set.indicator_of_notMem ht]

omit mΩ in
lemma abs_extIcc_le {T K : ℝ} {G : ℝ → Ω → ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ω, |G t ω| ≤ K) (t : ℝ)
    (ω : Ω) : |extIcc T G t ω| ≤ K := by
  by_cases ht : t ∈ Set.Icc 0 T
  · rw [extIcc_of_mem ht]; exact hK t ω
  · rw [extIcc_of_notMem ht]; simpa using hK0

lemma measurable_extIcc {T : ℝ} {G : ℝ → Ω → ℝ} (hG : Measurable (Function.uncurry G)) :
    Measurable (Function.uncurry (extIcc T G)) := by
  have : Function.uncurry (extIcc T G) = (Set.Icc 0 T ×ˢ Set.univ).indicator (Function.uncurry G) := by
    funext ⟨t, ω⟩
    by_cases ht : t ∈ Set.Icc 0 T
    · simp [Function.uncurry, extIcc_of_mem ht, Set.indicator_of_mem (Set.mk_mem_prod ht
        (Set.mem_univ ω))]
    · rw [Set.indicator_of_notMem (fun h => ht (Set.mem_prod.mp h).1)]
      simp [Function.uncurry, extIcc_of_notMem ht]
  rw [this]
  exact hG.indicator (measurableSet_Icc.prod MeasurableSet.univ)

lemma measurable_extIcc_apply {T : ℝ} {G : ℝ → Ω → ℝ} (hG : Measurable (Function.uncurry G))
    (t : ℝ) : Measurable (extIcc T G t) :=
  (measurable_extIcc hG).comp (measurable_const.prodMk measurable_id)

lemma extIcc_adapted {T : ℝ} {G : ℝ → Ω → ℝ} (hG : IsItoIntegrand 𝓕 P T G) (t : ℝ) :
    StronglyMeasurable[𝓕 t] (extIcc T G t) := by
  by_cases ht : t ∈ Set.Icc 0 T
  · have : extIcc T G t = G t := funext fun ω => extIcc_of_mem ht ω
    rw [this]; exact hG.adapted t ht.1 ht.2
  · have : extIcc T G t = fun _ => 0 := funext fun ω => extIcc_of_notMem ht ω
    rw [this]; exact stronglyMeasurable_const

section Shift

variable [IsFiniteMeasure P] {T K : ℝ} {G : ℝ → Ω → ℝ}

/-- The elementary integrand obtained by sampling `extIcc T G` at the left ends `s + jh` of the
shifted cells, truncated at `T`. -/
def shiftElem (hG : IsItoIntegrand 𝓕 P T G) (hK0 : 0 ≤ K) (hK : ∀ t ω, |G t ω| ≤ K) (hT : 0 < T)
    {h s : ℝ} (hh : 0 < h) (hs : 0 < s) : ElemIntegrand 𝓕 P (Fin (⌈T / h⌉₊ + 1)) where
  left j := min (s + j * h) T
  right j := min (s + (j + 1) * h) T
  val j := extIcc T G (s + j * h)
  left_nonneg _ := le_min (by positivity) hT.le
  left_le_right _ := min_le_min_right _ (by nlinarith)
  adapted j := by
    by_cases hj : s + j * h ≤ T
    · simp only [min_eq_left hj]; exact extIcc_adapted hG _
    · have : extIcc T G (s + j * h) = fun _ => 0 :=
        funext fun ω => extIcc_of_notMem (fun hm => hj hm.2) ω
      rw [this]; exact stronglyMeasurable_const
  memLp j := MemLp.of_bound (measurable_extIcc_apply hG.measurable _).aestronglyMeasurable K
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact abs_extIcc_le hK0 hK _ ω)

lemma shiftElem_supportedIn (hG : IsItoIntegrand 𝓕 P T G) (hK0 : 0 ≤ K) (hK : ∀ t ω, |G t ω| ≤ K)
    (hT : 0 < T) {h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    (shiftElem hG hK0 hK hT hh hs).SupportedIn T := fun _ => min_le_right _ _

/-- On `(0, T]` the shifted elementary integrand is `extIcc T G` sampled at `cellLeft h s t`. -/
lemma shiftElem_process (hG : IsItoIntegrand 𝓕 P T G) (hK0 : 0 ≤ K) (hK : ∀ t ω, |G t ω| ≤ K)
    (hT : 0 < T) {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (hsh : s < h) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) (ω : Ω) :
    (shiftElem hG hK0 hK hT hh hs).process t ω = extIcc T G (cellLeft h s t) ω := by
  unfold ElemIntegrand.process
  simp only [shiftElem]
  by_cases hts : t ≤ s
  · -- no cell contains `t`, and the sampling time is negative
    have hc : ⌈(t - s) / h⌉ ≤ 0 := Int.ceil_le.mpr (by
      simp only [Int.cast_zero]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le)
    have hneg : cellLeft h s t < 0 := by
      unfold cellLeft
      have : ((⌈(t - s) / h⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hc
      nlinarith
    rw [extIcc_of_notMem (fun hm => absurd hm.1 (not_le.mpr hneg))]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [cellInd_notMem, mul_zero]
    intro hm
    have : t ≤ min (s + (j : ℕ) * h) T := le_min (by nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
      ht.2
    exact absurd hm.1 (not_lt.mpr this)
  · push_neg at hts
    set k := ⌈(t - s) / h⌉ with hk
    have hk1 : 1 ≤ k := Int.one_le_ceil_iff.mpr (div_pos (by linarith) hh)
    set j₀ := (k - 1).toNat with hj₀
    have hj₀r : (j₀ : ℝ) = (k : ℝ) - 1 := by
      have : ((j₀ : ℤ) : ℝ) = ((k - 1 : ℤ) : ℝ) := by
        rw [hj₀, Int.toNat_of_nonneg (by omega)]
      push_cast at this; exact this
    have hklt : (k : ℝ) < (t - s) / h + 1 := Int.ceil_lt_add_one _
    have hkge : (t - s) / h ≤ k := Int.le_ceil _
    have hlo : s + j₀ * h < t := by
      rw [hj₀r]
      have := (lt_div_iff₀ hh).mp (by linarith : (k : ℝ) - 1 < (t - s) / h)
      linarith
    have hhi : t ≤ s + (j₀ + 1) * h := by
      rw [hj₀r]
      have := (div_le_iff₀ hh).mp hkge
      linarith
    have hj₀N : j₀ < ⌈T / h⌉₊ + 1 := by
      have h1 : (j₀ : ℝ) < T / h := by
        rw [lt_div_iff₀ hh]; nlinarith [ht.2]
      have h2 : T / h ≤ (⌈T / h⌉₊ : ℝ) := Nat.le_ceil _
      have : (j₀ : ℝ) < (⌈T / h⌉₊ : ℝ) + 1 := by linarith
      exact_mod_cast this
    have hmem : ∀ j : Fin (⌈T / h⌉₊ + 1),
        t ∈ Set.Ioc (min (s + (j : ℕ) * h) T) (min (s + ((j : ℕ) + 1) * h) T) ↔ (j : ℕ) = j₀ := by
      intro j
      constructor
      · intro hm
        have h1 : s + (j : ℕ) * h < t := by
          rcases min_lt_iff.mp hm.1 with h | h
          · exact h
          · exact absurd ht.2 (not_le.mpr h)
        have h2 : t ≤ s + ((j : ℕ) + 1) * h := hm.2.trans (min_le_left _ _)
        have hceil : k = (j : ℕ) + 1 := by
          rw [hk, Int.ceil_eq_iff]
          push_cast
          constructor
          · rw [lt_div_iff₀ hh]; linarith
          · rw [div_le_iff₀ hh]; linarith
        rw [hj₀, hceil]; simp
      · intro hj
        rw [hj]
        exact ⟨min_lt_of_left_lt hlo, le_min hhi ht.2⟩
    rw [Finset.sum_eq_single ⟨j₀, hj₀N⟩]
    · rw [cellInd_mem ((hmem ⟨j₀, hj₀N⟩).mpr rfl), mul_one]
      congr 1
      unfold cellLeft; rw [hj₀r, ← hk]; ring
    · intro j _ hj
      rw [cellInd_notMem (fun hm => hj (Fin.ext ((hmem j).mp hm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

end Shift

section Average

variable [IsFiniteMeasure P] {T K : ℝ} {G : ℝ → Ω → ℝ}

/-- Squared error of the shifted sampling at `(t, ω)`. -/
def shiftErr (T : ℝ) (G : ℝ → Ω → ℝ) (h s : ℝ) (p : ℝ × Ω) : ℝ :=
  (extIcc T G (cellLeft h s p.1) p.2 - extIcc T G p.1 p.2) ^ 2

/-- Squared translation increment at `(t, ω)`. -/
def transErr (T : ℝ) (G : ℝ → Ω → ℝ) (q : ℝ) (p : ℝ × Ω) : ℝ :=
  (extIcc T G (p.1 - q) p.2 - extIcc T G p.1 p.2) ^ 2

lemma measurable_shiftErr (hG : Measurable (Function.uncurry G)) (h : ℝ) :
    Measurable (fun z : ℝ × (ℝ × Ω) => shiftErr T G h z.1 z.2) := by
  unfold shiftErr
  have h1 : Measurable (fun z : ℝ × (ℝ × Ω) => extIcc T G (cellLeft h z.1 z.2.1) z.2.2) :=
    (measurable_extIcc hG).comp (((measurable_cellLeft h).comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd))
  have h2 : Measurable (fun z : ℝ × (ℝ × Ω) => extIcc T G z.2.1 z.2.2) :=
    (measurable_extIcc hG).comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))
  exact (h1.sub h2).pow_const 2

lemma measurable_transErr (hG : Measurable (Function.uncurry G)) :
    Measurable (fun z : ℝ × (ℝ × Ω) => transErr T G z.1 z.2) := by
  unfold transErr
  have h1 : Measurable (fun z : ℝ × (ℝ × Ω) => extIcc T G (z.2.1 - z.1) z.2.2) :=
    (measurable_extIcc hG).comp (((measurable_fst.comp measurable_snd).sub measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  have h2 : Measurable (fun z : ℝ × (ℝ × Ω) => extIcc T G z.2.1 z.2.2) :=
    (measurable_extIcc hG).comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))
  exact (h1.sub h2).pow_const 2

omit mΩ in
lemma sq_sub_le_of_abs_le {a b K : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K) : (a - b) ^ 2 ≤ (2 * K) ^ 2 := by
  have : |a - b| ≤ 2 * K := by
    calc |a - b| ≤ |a| + |b| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

omit mΩ in
lemma shiftErr_le (hK0 : 0 ≤ K) (hK : ∀ t ω, |G t ω| ≤ K) (h s : ℝ) (p : ℝ × Ω) :
    ‖shiftErr T G h s p‖ ≤ (2 * K) ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_sub_le_of_abs_le (abs_extIcc_le hK0 hK _ _) (abs_extIcc_le hK0 hK _ _)

omit mΩ in
lemma transErr_le (hK0 : 0 ≤ K) (hK : ∀ t ω, |G t ω| ≤ K) (q : ℝ) (p : ℝ × Ω) :
    ‖transErr T G q p‖ ≤ (2 * K) ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_sub_le_of_abs_le (abs_extIcc_le hK0 hK _ _) (abs_extIcc_le hK0 hK _ _)

/-- **Averaging over the shift**: `∫₀ʰ ds ‖shifted sampling - G‖² = ∫₀ʰ dq ‖G(· - q) - G‖²`. -/
lemma integral_shiftErr (hG : Measurable (Function.uncurry G)) (hK0 : 0 ≤ K)
    (hK : ∀ t ω, |G t ω| ≤ K) {h : ℝ} (hh : 0 < h) :
    ∫ s in Set.Ioo 0 h, ∫ p, shiftErr T G h s p ∂(tsMeasure P T) =
      ∫ q in Set.Ioo 0 h, ∫ p, transErr T G q p ∂(tsMeasure P T) := by
  have hi1 : Integrable (Function.uncurry (shiftErr T G h))
      ((volume.restrict (Set.Ioo 0 h)).prod (tsMeasure P T)) :=
    Integrable.of_bound (measurable_shiftErr hG h).aestronglyMeasurable _
      (Eventually.of_forall fun z => shiftErr_le hK0 hK h z.1 z.2)
  have hi2 : Integrable (Function.uncurry (transErr T G))
      ((volume.restrict (Set.Ioo 0 h)).prod (tsMeasure P T)) :=
    Integrable.of_bound (measurable_transErr hG).aestronglyMeasurable _
      (Eventually.of_forall fun z => transErr_le hK0 hK z.1 z.2)
  rw [integral_integral_swap hi1, integral_integral_swap hi2]
  congr 1; funext p
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo]
  have := integral_cellPos hh (fun r => (extIcc T G (p.1 - r) p.2 - extIcc T G p.1 p.2) ^ 2) p.1
  simp only [shiftErr, transErr, cellLeft_eq]
  exact this

lemma memLp_extIcc_path (hG : Measurable (Function.uncurry G)) (hK0 : 0 ≤ K)
    (hK : ∀ t ω, |G t ω| ≤ K) (ω : Ω) : MemLp (fun t => extIcc T G t ω) 2 volume := by
  have hg : MemLp ((Set.Icc 0 T).indicator fun _ => K) 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Icc K (Or.inr measure_Icc_lt_top.ne)
  refine hg.of_le ((measurable_extIcc hG).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Set.Icc 0 T
  · rw [Set.indicator_of_mem ht, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK0,
      extIcc_of_mem ht]
    exact hK t ω
  · rw [Set.indicator_of_notMem ht, extIcc_of_notMem ht]

/-- The averaged translation error tends to `0`. -/
lemma tendsto_transErr (hG : Measurable (Function.uncurry G)) (hK0 : 0 ≤ K)
    (hK : ∀ t ω, |G t ω| ≤ K) (hT : 0 < T) :
    Tendsto (fun q => ∫ p, transErr T G q p ∂(tsMeasure P T)) (𝓝 0) (𝓝 0) := by
  have hint : ∀ q, Integrable (transErr T G q) (tsMeasure P T) := fun q =>
    Integrable.of_bound ((measurable_transErr hG).comp (measurable_const.prodMk
      measurable_id)).aestronglyMeasurable _ (Eventually.of_forall fun p => transErr_le hK0 hK q p)
  have hrw : ∀ q, ∫ p, transErr T G q p ∂(tsMeasure P T) =
      ∫ ω, (∫ t in Set.Ioc 0 T, transErr T G q (t, ω)) ∂P := fun q => by
    have := hint q
    unfold tsMeasure at this ⊢
    exact integral_prod_symm _ this
  simp_rw [hrw]
  have hvol : volume.real (Set.Ioc (0 : ℝ) T) = T := by
    simp [measureReal_def, Real.volume_Ioc, hT.le]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := 𝓝 (0 : ℝ))
    (F := fun q ω => ∫ t in Set.Ioc 0 T, transErr T G q (t, ω)) (f := fun _ => 0)
    (fun _ => (2 * K) ^ 2 * T)
    (Eventually.of_forall fun q => by
      have hm : StronglyMeasurable (Function.uncurry fun t ω => transErr T G q (t, ω)) :=
        ((measurable_transErr hG).comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
      exact (hm.integral_prod_left (μ := volume.restrict (Set.Ioc 0 T))).aestronglyMeasurable)
    (Eventually.of_forall fun q => Eventually.of_forall fun ω => by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (0 : ℝ) T)
        (f := fun t => transErr T G q (t, ω)) (C := (2 * K) ^ 2) measure_Ioc_lt_top
        (fun t _ => transErr_le hK0 hK q (t, ω))
      rwa [hvol] at this)
    (integrable_const _)
    (Eventually.of_forall fun ω => by
      have hf := memLp_extIcc_path hG hK0 hK (T := T) ω
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_translate_sq hf) (Eventually.of_forall fun q =>
          setIntegral_nonneg measurableSet_Ioc fun t _ => sq_nonneg _)
        (Eventually.of_forall fun q => ?_)
      exact setIntegral_le_integral ((memLp_translate hf q).sub hf).integrable_sq
        (Eventually.of_forall fun t => sq_nonneg _))
  simpa using h

omit [IsFiniteMeasure P] in
/-- Almost every point of `tsMeasure P T` has time coordinate in `(0, T]`. -/
lemma ae_mem_Ioc_tsMeasure (T : ℝ) : ∀ᵐ p ∂(tsMeasure P T), p.1 ∈ Set.Ioc 0 T :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)

/-- **Density, bounded case.** -/
lemma exists_elem_approx_bdd (hG : IsItoIntegrand 𝓕 P T G) (hK0 : 0 ≤ K)
    (hK : ∀ t ω, |G t ω| ≤ K) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Σ n, ElemIntegrand 𝓕 P (Fin n), H.2.SupportedIn T ∧
      ∫ p, (Function.uncurry H.2.process p - Function.uncurry G p) ^ 2 ∂(tsMeasure P T) < ε := by
  obtain ⟨r, hr, hrΨ⟩ := Metric.tendsto_nhds_nhds.mp
    (tendsto_transErr hG.measurable hK0 hK hT (P := P)) (ε / 2) (by positivity)
  set h := r / 2 with hhdef
  have hh : 0 < h := by positivity
  set D : ℝ → ℝ := fun s => ∫ p, shiftErr T G h s p ∂(tsMeasure P T) with hD
  set Ψ : ℝ → ℝ := fun q => ∫ p, transErr T G q p ∂(tsMeasure P T) with hΨ
  have hDΨ : ∫ s in Set.Ioo 0 h, D s = ∫ q in Set.Ioo 0 h, Ψ q :=
    integral_shiftErr hG.measurable hK0 hK hh
  have hDi : IntegrableOn D (Set.Ioo 0 h) := by
    have hm : StronglyMeasurable (Function.uncurry (shiftErr T G h)) :=
      (measurable_shiftErr hG.measurable h).stronglyMeasurable
    refine Integrable.of_bound (hm.integral_prod_right (ν := tsMeasure P T)).aestronglyMeasurable
      ((2 * K) ^ 2 * (tsMeasure P T).real Set.univ) (Eventually.of_forall fun s => ?_)
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun p =>
      shiftErr_le hK0 hK h s p)
  have hΨi : IntegrableOn Ψ (Set.Ioo 0 h) := by
    have hm : StronglyMeasurable (Function.uncurry (transErr T G)) :=
      (measurable_transErr hG.measurable).stronglyMeasurable
    refine Integrable.of_bound (hm.integral_prod_right (ν := tsMeasure P T)).aestronglyMeasurable
      ((2 * K) ^ 2 * (tsMeasure P T).real Set.univ) (Eventually.of_forall fun q => ?_)
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun p =>
      transErr_le hK0 hK q p)
  have hvol : volume.real (Set.Ioo (0 : ℝ) h) = h := by
    simp [measureReal_def, Real.volume_Ioo, hh.le]
  have hΨle : ∫ q in Set.Ioo 0 h, Ψ q ≤ ∫ q in Set.Ioo 0 h, ε / 2 := by
    refine setIntegral_mono_on hΨi (integrableOn_const (by simp [Real.volume_Ioo]))
      measurableSet_Ioo fun q hq => ?_
    have hq' : dist q 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hq.1]; linarith [hq.2]
    have := hrΨ hq'
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  obtain ⟨s, hs, hDs⟩ : ∃ s ∈ Set.Ioo 0 h, D s < ε := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∫ s in Set.Ioo 0 h, ε ≤ ∫ s in Set.Ioo 0 h, D s :=
      setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioo])) hDi measurableSet_Ioo
        hcon
    rw [setIntegral_const, hvol, smul_eq_mul] at h1
    rw [setIntegral_const, hvol, smul_eq_mul] at hΨle
    nlinarith
  refine ⟨⟨_, shiftElem hG hK0 hK hT hh hs.1⟩, shiftElem_supportedIn hG hK0 hK hT hh hs.1, ?_⟩
  have : ∫ p, (Function.uncurry (shiftElem hG hK0 hK hT hh hs.1).process p -
      Function.uncurry G p) ^ 2 ∂(tsMeasure P T) = D s := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Ioc_tsMeasure T] with p hp
    simp only [Function.uncurry, shiftErr]
    rw [shiftElem_process hG hK0 hK hT hh hs.1 hs.2 hp,
      extIcc_of_mem (Set.Ioc_subset_Icc_self hp)]
  rw [this]; exact hDs

end Average

/-- **Density of elementary integrands** (Gardiner §4.2.6): every Itô integrand on `[0, T]` is a
limit, in the norm `⟨∫₀ᵀ (G - H)² dt⟩^{1/2}`, of elementary integrands supported in `(0, T]`. -/
theorem exists_elem_approx [IsFiniteMeasure P] {T : ℝ} {G : ℝ → Ω → ℝ}
    (hG : IsItoIntegrand 𝓕 P T G) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Σ n, ElemIntegrand 𝓕 P (Fin n), H.2.SupportedIn T ∧
      ∫ p, (Function.uncurry H.2.process p - Function.uncurry G p) ^ 2 ∂(tsMeasure P T) < ε := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨⟨0, ElemIntegrand.zero⟩, fun i => Fin.elim0 i, ?_⟩
    have : tsMeasure P T = 0 := by
      unfold tsMeasure
      rw [Set.Ioc_eq_empty (not_lt.mpr hT), Measure.restrict_empty, Measure.zero_prod]
    rw [this]; simpa using hε
  obtain ⟨n, hn⟩ := ((tendsto_clip hG).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).exists
  have hGn := hG.clip (Nat.cast_nonneg n)
  obtain ⟨H, hHs, hH⟩ := exists_elem_approx_bdd hGn (Nat.cast_nonneg n)
    (fun t ω => abs_clip_le (Nat.cast_nonneg n) _) hT (ε := ε / 4) (by positivity)
  refine ⟨H, hHs, ?_⟩
  have hHm := H.2.memLp_process (P := P) T
  have i1 : Integrable (fun p => (Function.uncurry H.2.process p -
      clip n (Function.uncurry G p)) ^ 2) (tsMeasure P T) := (hHm.sub hGn.memLp).integrable_sq
  have i2 : Integrable (fun p => (clip n (Function.uncurry G p) -
      Function.uncurry G p) ^ 2) (tsMeasure P T) := (hGn.memLp.sub hG.memLp).integrable_sq
  calc ∫ p, (Function.uncurry H.2.process p - Function.uncurry G p) ^ 2 ∂(tsMeasure P T)
      ≤ ∫ p, (2 * (Function.uncurry H.2.process p - clip n (Function.uncurry G p)) ^ 2 +
          2 * (clip n (Function.uncurry G p) - Function.uncurry G p) ^ 2) ∂(tsMeasure P T) := by
        refine integral_mono ((hHm.sub hG.memLp).integrable_sq) ((i1.const_mul 2).add
          (i2.const_mul 2)) fun p => ?_
        nlinarith [sq_nonneg (Function.uncurry H.2.process p + Function.uncurry G p -
          2 * clip n (Function.uncurry G p))]
    _ = 2 * ∫ p, (Function.uncurry H.2.process p - clip n (Function.uncurry G p)) ^ 2
          ∂(tsMeasure P T) + 2 * ∫ p, (clip n (Function.uncurry G p) - Function.uncurry G p) ^ 2
          ∂(tsMeasure P T) := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ < ε := by
        have := hH
        simp only [Function.uncurry] at this hn ⊢
        linarith

end Gardiner.Ito
