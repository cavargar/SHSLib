/-
# Splitting probabilities in a double well: §9.1.4, (9.1.10)–(9.1.21)

For the Smoluchowski process (9.1.1) with absorbing barriers at the two minima `a < c`, the
splitting probabilities are (9.1.10)
`π_c(x₀) = ∫_a^{x₀} e^{U/D} / ∫_a^c e^{U/D}`, `π_a(x₀) = ∫_{x₀}^c e^{U/D} / ∫_a^c e^{U/D}`.

* `Gardiner.Escape.splitA_add_splitC` — **(9.1.17)** `π_a + π_c = 1` (exact).
* `Gardiner.Escape.splitting_far` — **(9.1.16) with rate**: for `x₀ < b` a finite distance from
  the barrier, `π_c(x₀) = U'(x₀)⁻¹ √(|U''(b)| D/2π) e^{[U(x₀) - U(b)]/D} (1 + O(√D))`.
* `Gardiner.Escape.splitting_near` — **(9.1.20)–(9.1.21) with rate**: for `x₀ = b - y₀√D`,
  `π_c = ½[1 - erf_G(y₀ √|U''(b)|)] + O(√D)` where `erf_G(x) = √(2/π)∫₀ˣ e^{-t²/2} dt`
  (`Gardiner.Escape.gerf`).

**Erratum (9.1.19).**  The printed definition `erf(x) = √(π/2)∫₀ˣ e^{-t²} dt` is not a
normalised error function (its limit at `∞` is `π/(2√2) ≠ 1`), and with it (9.1.20) is false (at
`y₀ → ∞` it gives `½(1 - π/(2√2)) ≠ 0`).  The function that makes (9.1.20)–(9.1.21) correct is
`erf_G(x) = √(2/π)∫₀ˣ e^{-t²/2} dt = erf(x/√2)`; equivalently, with the standard
`erf(x) = (2/√π)∫₀ˣ e^{-t²}`, `π_c → ½ erfc(y₀ √(|U''(b)|/2))`.  See `gauss_tail_eq`.
-/
import SHSLib.Gardiner.Escape.DoubleWell

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-- The splitting probability `π_c(x₀)` of (9.1.10): exit at `c` before `a`. -/
def splitC (U : ℝ → ℝ) (D a c x₀ : ℝ) : ℝ :=
  (∫ x in a..x₀, exp (U x / D)) / ∫ x in a..c, exp (U x / D)

/-- The splitting probability `π_a(x₀)` of (9.1.10): exit at `a` before `c`. -/
def splitA (U : ℝ → ℝ) (D a c x₀ : ℝ) : ℝ :=
  (∫ x in x₀..c, exp (U x / D)) / ∫ x in a..c, exp (U x / D)

/-- The Gaussian-normalised error function `erf_G(x) = √(2/π) ∫₀ˣ e^{-t²/2} dt` that makes
(9.1.20) correct (erratum to (9.1.19)). -/
def gerf (x : ℝ) : ℝ := √(2 / π) * ∫ t in (0 : ℝ)..x, exp (-(t ^ 2 / 2))

/-- **(9.1.17)**: `π_a + π_c = 1` whenever `a < c` and `U` is continuous. -/
theorem splitA_add_splitC {U : ℝ → ℝ} (hU : Continuous U) {a c : ℝ} (hac : a < c) (D x₀ : ℝ) :
    splitA U D a c x₀ + splitC U D a c x₀ = 1 := by
  have hpos : 0 < ∫ x in a..c, exp (U x / D) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (Continuous.intervalIntegrable (by fun_prop) _ _) (fun x _ => exp_pos _) hac
  rw [splitA, splitC, ← add_div, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), div_self hpos.ne']

/-- **Corrected (9.1.20) limit.**  `√(k/2π) ∫_{y₀}^∞ e^{-k t²/2} dt = ½[1 - erf_G(y₀√k)]`. -/
theorem gauss_tail_eq {k y₀ : ℝ} (hk : 0 < k) :
    (∫ t in Ioi y₀, exp (-(k / 2 * t ^ 2))) / √(2 * π / k) = (1 - gerf (y₀ * √k)) / 2 := by
  have hk2 : 0 < k / 2 := by positivity
  have hfeq : (fun t : ℝ => exp (-(k / 2 * t ^ 2))) = fun t => exp (-(k / 2) * t ^ 2) := by
    ext t; ring_nf
  have hint : Integrable (fun t : ℝ => exp (-(k / 2 * t ^ 2))) := by
    rw [hfeq]; exact integrable_exp_neg_mul_sq hk2
  have hI0 : ∫ t in Ioi (0 : ℝ), exp (-(k / 2 * t ^ 2)) = √(2 * π / k) / 2 := by
    rw [hfeq, integral_gaussian_Ioi]; congr 2; field_simp
  have hsplit := intervalIntegral.integral_interval_add_Ioi' (a := 0) (b := y₀)
    (Continuous.intervalIntegrable (by fun_prop : Continuous fun t : ℝ => exp (-(k / 2 * t ^ 2)))
      _ _) hint.integrableOn
  have hsk : 0 < √k := sqrt_pos.mpr hk
  have hsub : ∫ t in (0 : ℝ)..y₀, exp (-(k / 2 * t ^ 2))
      = (√k)⁻¹ * ∫ u in (0 : ℝ)..y₀ * √k, exp (-(u ^ 2 / 2)) := by
    have := intervalIntegral.integral_comp_mul_right (a := 0) (b := y₀)
      (fun u : ℝ => exp (-(u ^ 2 / 2))) hsk.ne'
    simp only [zero_mul, smul_eq_mul] at this
    rw [← this]
    apply intervalIntegral.integral_congr; intro t _
    simp only
    rw [mul_pow, sq_sqrt hk.le]; ring_nf
  rw [hI0] at hsplit
  have hT : ∫ t in Ioi y₀, exp (-(k / 2 * t ^ 2))
      = √(2 * π / k) / 2 - (√k)⁻¹ * ∫ u in (0 : ℝ)..y₀ * √k, exp (-(u ^ 2 / 2)) := by
    rw [← hsub]; linarith
  rw [hT, gerf]
  set J := ∫ u in (0 : ℝ)..y₀ * √k, exp (-(u ^ 2 / 2))
  have h1 : √k * √(2 * π / k) = √(2 * π) := by
    rw [← sqrt_mul hk.le]; congr 1; field_simp
  have h2 : √(2 / π) * √(2 * π) = 2 := by
    rw [← sqrt_mul (by positivity), show 2 / π * (2 * π) = 2 ^ 2 by field_simp,
      sqrt_sq (by norm_num)]
  have h3 : 0 < √(2 * π / k) := sqrt_pos.mpr (by positivity)
  have h4 : 0 < √(2 * π) := sqrt_pos.mpr (by positivity)
  have h2' : √(2 / π) = 2 / √(2 * π) := by rw [eq_div_iff h4.ne']; exact h2
  rw [h2', ← h1]
  field_simp

/-! ### Small-`D` asymptotics -/

lemma small_sqrt {k D : ℝ} (hk : 0 ≤ k) (hD0 : D ≤ 1 / (4 * (k + 1) ^ 2)) :
    k * √D ≤ 1 / 2 := by
  have hk1 : 0 < k + 1 := by linarith
  have h2 : √D ≤ 1 / (2 * (k + 1)) := by
    rw [show 1 / (2 * (k + 1)) = √(1 / (4 * (k + 1) ^ 2)) by
      rw [sqrt_div' _ (by positivity), sqrt_one, show 4 * (k + 1) ^ 2 = (2 * (k + 1)) ^ 2 by
        ring, sqrt_sq (by linarith)]]
    exact sqrt_le_sqrt hD0
  calc k * √D ≤ (k + 1) * (1 / (2 * (k + 1))) :=
        mul_le_mul (by linarith) h2 (sqrt_nonneg _) hk1.le
    _ = 1 / 2 := by field_simp

lemma small_pos (k : ℝ) (hk : 0 ≤ k) : 0 < min 1 (1 / (4 * (k + 1) ^ 2)) := by
  have : 0 < k + 1 := by linarith
  exact lt_min one_pos (by positivity)

lemma le_sqrt_of_le_one {D : ℝ} (hD : 0 ≤ D) (hD1 : D ≤ 1) : D ≤ √D := by
  have h1 : √D ≤ 1 := sqrt_le_one.mpr hD1
  calc D = √D * √D := (mul_self_sqrt hD).symm
    _ ≤ √D * 1 := mul_le_mul_of_nonneg_left h1 (sqrt_nonneg _)
    _ = √D := mul_one _

variable {U : ℝ → ℝ} {a b c : ℝ}

/-- **(9.1.16) with rate.**  Let `x₀` lie at a finite distance below the barrier, with `U`
increasing through `x₀` at slope `g` (`|U(x₀) - U(x₀ - s) - g s| ≤ M s²` on `[0, r]`; for
differentiable `U` this forces `g = U'(x₀)`) and `U < U(x₀) - η` on `[a, x₀ - r]`.  Then
`π_c(x₀) = g⁻¹ √(|U''(b)| D/2π) e^{[U(x₀) - U(b)]/D} (1 + O(√D))`. -/
theorem splitting_far (h : TwoWellHyp U a b c) {x₀ g r M η : ℝ} (hr : 0 < r) (hg : 0 < g)
    (hM : 0 ≤ M) (hMr : M * r ≤ g / 2)
    (hT : ∀ s ∈ Icc 0 r, |U x₀ - U (x₀ - s) - g * s| ≤ M * s ^ 2) (hlo : a ≤ x₀ - r)
    (hη : 0 < η) (hfar : ∀ z ∈ Icc a (x₀ - r), U z + η ≤ U x₀) :
    ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
      |splitC U D a c x₀ / (g⁻¹ * √(h.kb * D / (2 * π)) * exp ((U x₀ - U b) / D)) - 1|
        ≤ C * √D := by
  have hcont := h.cont
  obtain ⟨C0, hC0⟩ := laplace_endpoint (W := fun z => U x₀ - U z) (lo := a) (x₀ := x₀)
    (by fun_prop) hr hg hM hMr hT hlo hη (fun z hz => by have := hfar z hz; linarith)
  obtain ⟨CB, hB⟩ := h.barrier_laplace
  set αb := √(2 * π / h.kb)
  have hαb : 0 < αb := sqrt_pos.mpr (by have := h.hkb; positivity)
  set kb' := max CB 0 / αb
  have hkb' : 0 ≤ kb' := by positivity
  refine ⟨2 * (max C0 0 * g + kb'), min 1 (1 / (4 * (kb' + 1) ^ 2)), small_pos kb' hkb',
    fun D hD hD0 => ?_⟩
  have hD1 : D ≤ 1 := le_trans hD0 (min_le_left _ _)
  have hs : 0 < √D := sqrt_pos.mpr hD
  set P0 := ∫ z in a..x₀, exp (-((U x₀ - U z) / D))
  set Pb := ∫ z in a..c, exp (-((U b - U z) / D))
  have hDg : 0 < D / g := div_pos hD hg
  have e1 : |P0 / (D / g) - 1| ≤ max C0 0 * g * √D := by
    refine (rel_of_abs hDg (((hC0 D hD hD1)).trans
      (mul_le_mul_of_nonneg_right (le_max_left C0 0) (by positivity)))).trans ?_
    rw [show max C0 0 * D ^ 2 / (D / g) = max C0 0 * g * D by field_simp]
    exact mul_le_mul_of_nonneg_left (le_sqrt_of_le_one hD.le hD1)
      (mul_nonneg (le_max_right _ _) hg.le)
  have e2 : |Pb / (αb * √D) - 1| ≤ kb' * √D :=
    rel_sqrt hαb hD ((hB D hD hD1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le))
  have key := div_rate e1 e2 (small_sqrt hkb' (le_trans hD0 (min_le_right _ _)))
  have hPb : Pb ≠ 0 := by
    intro h0; rw [h0, zero_div] at e2
    have := small_sqrt hkb' (le_trans hD0 (min_le_right _ _))
    rw [abs_le] at e2; linarith [e2.1]
  have hnum : ∫ x in a..x₀, exp (U x / D) = exp (U x₀ / D) * P0 := barrierInt_eq U D a x₀ x₀
  have hden : ∫ x in a..c, exp (U x / D) = exp (U b / D) * Pb := barrierInt_eq U D a b c
  have hsq : √(h.kb * D / (2 * π)) * αb = √D := by
    rw [← sqrt_mul (by have := h.hkb; positivity)]; congr 1
    have := h.hkb; field_simp
  have e : splitC U D a c x₀ / (g⁻¹ * √(h.kb * D / (2 * π)) * exp ((U x₀ - U b) / D))
      = (P0 / (D / g)) / (Pb / (αb * √D)) := by
    rw [splitC, hnum, hden, show (U x₀ - U b) / D = U x₀ / D - U b / D by ring, exp_sub]
    have h1 : √(h.kb * D / (2 * π)) = √D / αb := by rw [← hsq]; field_simp
    rw [h1]
    have := exp_pos (U x₀ / D); have := exp_pos (U b / D)
    field_simp
    rw [sq_sqrt hD.le]; ring
  rw [e]
  refine key.trans (le_of_eq ?_)
  ring

/-- **(9.1.20)–(9.1.21) with rate.**  For a starting point `x₀ = b - y₀√D` within `O(√D)` of
the barrier top (`y₀ ≥ 0`),
`π_c(x₀) = ½[1 - erf_G(y₀ √|U''(b)|)] + O(√D) = ½[1 - erf_G((b - x₀)√(|U''(b)|/D))] + O(√D)`,
with `erf_G` the correctly normalised error function `gerf` (erratum (9.1.19)). -/
theorem splitting_near (h : TwoWellHyp U a b c) {y₀ : ℝ} (hy₀ : 0 ≤ y₀) :
    ∃ C D₀, 0 < D₀ ∧ ∀ D, 0 < D → D ≤ D₀ →
      |splitC U D a c (b - y₀ * √D) - (1 - gerf (y₀ * √h.kb)) / 2| ≤ C * √D := by
  have hcont := h.cont
  have hr := h.hr
  have hab := h.sep_ab
  have hbc := h.sep_bc
  obtain ⟨C1, D1, hD1pos, hC1⟩ := laplace_gauss_tail (W := fun z => U b - U z) (lo := a)
    (b := b) (y₀ := y₀) (by fun_prop) h.hr h.hkb h.hM h.hMrb
    (fun s hs => by
      have := h.taylor_b (-s) (by rw [abs_neg, abs_of_nonneg hs.1]; exact hs.2)
      rw [abs_neg, abs_of_nonneg hs.1, neg_sq, ← sub_eq_add_neg] at this
      exact this)
    (by linarith) h.hη
    (fun z hz => by
      have := h.barrier z ⟨hz.1, by linarith [hz.2]⟩ (by
        rw [abs_of_nonpos (by linarith [hz.2])]; linarith [hz.2])
      linarith) hy₀
  obtain ⟨CB, hB⟩ := h.barrier_laplace
  set αb := √(2 * π / h.kb)
  have hαb : 0 < αb := sqrt_pos.mpr (by have := h.hkb; positivity)
  set kb' := max CB 0 / αb
  have hkb' : 0 ≤ kb' := by positivity
  set G := ∫ t in Ioi y₀, exp (-(h.kb / 2 * t ^ 2))
  have hG : 0 ≤ G := setIntegral_nonneg measurableSet_Ioi (fun _ _ => (exp_pos _).le)
  set D₀ := min D1 (min 1 (1 / (4 * (kb' + 1) ^ 2)))
  refine ⟨2 * (αb * max C1 0 + G * max CB 0) / αb ^ 2, D₀,
    lt_min hD1pos (small_pos kb' hkb'), fun D hD hD0 => ?_⟩
  have hDD1 : D ≤ D1 := le_trans hD0 (min_le_left _ _)
  have hD0' : D ≤ min 1 (1 / (4 * (kb' + 1) ^ 2)) := le_trans hD0 (min_le_right _ _)
  have hD1 : D ≤ 1 := le_trans hD0' (min_le_left _ _)
  have hs : 0 < √D := sqrt_pos.mpr hD
  set N := ∫ z in a..b - y₀ * √D, exp (-((U b - U z) / D))
  set Pb := ∫ z in a..c, exp (-((U b - U z) / D))
  have eN : |N - √D * G| ≤ max C1 0 * D :=
    (hC1 D hD hDD1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le)
  have eB : |Pb - αb * √D| ≤ max CB 0 * D :=
    (hB D hD hD1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le)
  have hsm := small_sqrt hkb' (le_trans hD0' (min_le_right _ _))
  have hCB : max CB 0 * D ≤ αb * √D / 2 := by
    have : max CB 0 * √D ≤ αb / 2 := by
      have e : max CB 0 = kb' * αb := by simp only [kb']; field_simp
      rw [e]; nlinarith
    calc max CB 0 * D = max CB 0 * √D * √D := by rw [mul_assoc, mul_self_sqrt hD.le]
      _ ≤ αb / 2 * √D := mul_le_mul_of_nonneg_right this hs.le
      _ = αb * √D / 2 := by ring
  have hPb : αb * √D / 2 ≤ Pb := by
    have := (abs_le.mp eB).1; linarith
  have hPb0 : 0 < Pb := lt_of_lt_of_le (by positivity) hPb
  have hsplit : splitC U D a c (b - y₀ * √D) = N / Pb := by
    rw [splitC, barrierInt_eq U D a b (b - y₀ * √D), barrierInt_eq U D a b c]
    have := exp_pos (U b / D)
    field_simp
    exact mul_div_cancel_right₀ N hPb0.ne'
  have hlim : (1 - gerf (y₀ * √h.kb)) / 2 = G / αb := (gauss_tail_eq h.hkb).symm
  rw [hsplit, hlim, div_sub_div _ _ hPb0.ne' hαb.ne', abs_div,
    abs_of_pos (mul_pos hPb0 hαb)]
  have hnum : |N * αb - Pb * G| ≤ αb * (max C1 0 * D) + G * (max CB 0 * D) := by
    have e : N * αb - Pb * G = αb * (N - √D * G) - G * (Pb - αb * √D) := by ring
    rw [e]
    calc |αb * (N - √D * G) - G * (Pb - αb * √D)|
        ≤ |αb * (N - √D * G)| + |G * (Pb - αb * √D)| := abs_sub _ _
      _ = αb * |N - √D * G| + G * |Pb - αb * √D| := by
          rw [abs_mul, abs_mul, abs_of_pos hαb, abs_of_nonneg hG]
      _ ≤ αb * (max C1 0 * D) + G * (max CB 0 * D) := by gcongr
  rw [div_le_iff₀ (mul_pos hPb0 hαb)]
  have hK : 0 ≤ 2 * (αb * max C1 0 + G * max CB 0) / αb ^ 2 := by
    have := le_max_right C1 0; have := le_max_right CB 0; positivity
  calc |N * αb - Pb * G| ≤ αb * (max C1 0 * D) + G * (max CB 0 * D) := hnum
    _ = 2 * (αb * max C1 0 + G * max CB 0) / αb ^ 2 * √D * (αb * √D / 2 * αb) := by
        field_simp; rw [sq_sqrt hD.le]; ring
    _ ≤ 2 * (αb * max C1 0 + G * max CB 0) / αb ^ 2 * √D * (Pb * αb) := by gcongr

end Gardiner.Escape
