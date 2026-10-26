/-
# The pathwise SDE theorems driven by a genuine Wiener process (Gardiner §6.2, §10.1)

The Itô-free layer `SHSLib.Gardiner.SDE` proves its additive-noise results for **every continuous
driving path** `w`.  A Wiener process (`Gardiner.Ito.IsWiener`) has continuous paths almost
surely, so all of them hold almost surely with `w = W(·, ω)`; for the standard Wiener process
`Gardiner.Ito.stdWiener` they hold for every `ω`.

* **Existence** (`Gardiner.SDE.exists_pathSol`): `Gardiner.Ito.IsWiener.ae_exists_pathSol`; for the
  standard Wiener process and `a = -sin`, `Gardiner.Ito.exists_pathSol_sin_stdWiener`.
* **Euler convergence** (`Gardiner.SDE.euler_pathwise_error_grid`): for a Lipschitz drift and any
  continuous path the Euler scheme with `N` steps converges to the pathwise solution at `T` as
  `N → ∞` (`Gardiner.Ito.euler_tendsto_of_continuous`; the modulus of continuity of the path
  tends to zero by uniform continuity on `[0, T]`).  Hence almost surely for a Wiener path
  (`Gardiner.Ito.IsWiener.ae_euler_tendsto`); instance `dx = -sin x dt + ε dW` with the standard
  Wiener process (`Gardiner.Ito.euler_sin_stdWiener`).
* **Small-noise linearisation** (`Gardiner.SDE.linearisation_error`, the case `N = 1` of
  `Gardiner.SDE.pathwise_expansion`), (6.2.9)–(6.2.14): for `dx = -sin x dt + ε dw`, `x(0) = 0`,
  the first-order term is the pathwise Ornstein–Uhlenbeck process
  `x₁(t) = w(t) - w(0) - e^{-t}∫₀ᵗ eˢ(w(s) - w(0)) ds` (`Gardiner.Ito.ouPath`, which is
  `∫₀ᵗ e^{-(t-s)} dw(s)` after an integration by parts), and `|x(t) - εx₁(t)| ≤ Cε²` on `[0, T]`
  uniformly in `|ε| ≤ 1` (`Gardiner.Ito.sin_linearisation_path`).  With a Wiener path this holds
  almost surely (`Gardiner.Ito.IsWiener.ae_sin_linearisation`), and for the standard Wiener process
  for every `ω`, together with the existence of the solution
  (`Gardiner.Ito.sin_linearisation_stdWiener`).
* **Third-order expansion of the cubic process** (6.2.33) (`Gardiner.SDE.cubic_expansion`, i.e.
  `Gardiner.SDE.pathwise_expansion` with `N = 3`): almost surely for a Wiener path, with a
  path-dependent constant (`Gardiner.Ito.cubic_expansion_path`,
  `Gardiner.Ito.IsWiener.ae_cubic_expansion`).
-/
import SHSLib.Gardiner.Ito.Brownian
import SHSLib.Gardiner.SDE.Cubic

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

noncomputable section

namespace Gardiner.Ito

open Gardiner.SDE

/-! ### Existence of pathwise solutions -/

/-- **`IsPathSol` with a Wiener path.**  For a bounded Lipschitz drift, almost surely the
equation `dx = a(x)dt + ε dW` has a pathwise solution from every initial point. -/
theorem IsWiener.ae_exists_pathSol {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ}
    {P : Measure Ω} (hW : IsWiener W P) {a : ℝ → ℝ} {B K : ℝ≥0} (hLip : LipschitzWith K a)
    (hB : ∀ u, |a u| ≤ B) (ε : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, ∃ x : ℝ → ℝ, x 0 = c ∧ IsPathSol a ε (fun t => W t ω) x T := by
  filter_upwards [hW.cont] with ω hω c
  exact exists_pathSol hLip hB ε hω hT c

lemma abs_neg_sin_sub_le (u v : ℝ) : |-Real.sin u - -Real.sin v| ≤ |u - v| := by
  rw [show -Real.sin u - -Real.sin v = -(Real.sin u - Real.sin v) by ring, abs_neg]
  exact Real.abs_sin_sub_sin_le u v

lemma lipschitzWith_neg_sin : LipschitzWith 1 fun u : ℝ => -Real.sin u :=
  LipschitzWith.of_dist_le_mul fun u v => by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_neg_sin_sub_le u v

/-- Instance: `dx = -sin x dt + ε dW` driven by the standard Wiener process has a pathwise solution
for every sample point and every initial value. -/
theorem exists_pathSol_sin_stdWiener (ε T c : ℝ) (hT : 0 ≤ T) (ω : StdWienerSpace) :
    ∃ x : ℝ → ℝ, x 0 = c ∧ IsPathSol (fun u => -Real.sin u) ε (fun t => stdWiener t ω) x T :=
  exists_pathSol (B := 1) lipschitzWith_neg_sin (fun u => by simpa using Real.abs_sin_le_one u)
    ε (continuous_stdWiener ω) hT c

/-! ### Convergence of the Euler scheme -/

/-- **Pathwise convergence of the Euler scheme for every continuous driving path.**  If `a` is
`L`-Lipschitz and `x` is a pathwise solution on `[0, T]`, the Euler scheme with `N` steps of size
`T/N` converges to `x(T)` as `N → ∞`. -/
theorem euler_tendsto_of_continuous {a : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ u v, |a u - a v| ≤ L * |u - v|) {ε T : ℝ} (hT : 0 < T) {w x : ℝ → ℝ}
    (hw : Continuous w) (hx : IsPathSol a ε w x T) :
    Tendsto (fun N : ℕ => eulerPath a ε (T / N) w (x 0) N) atTop (𝓝 (x T)) := by
  have ha : Continuous a := by
    refine continuous_iff_continuousAt.mpr fun u => Metric.continuousAt_iff.mpr fun e he => ?_
    refine ⟨e / (L + 1), by positivity, fun v hv => ?_⟩
    rw [Real.dist_eq] at hv ⊢
    calc |a v - a u| ≤ L * |v - u| := hLip v u
      _ ≤ L * (e / (L + 1)) := by gcongr
      _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (ha.comp hx.cont).continuousOn
  have hA' : ∀ s ∈ Icc 0 T, |a (x s)| ≤ A := fun s hs => by simpa using hA s hs
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA' 0 ⟨le_rfl, hT.le⟩)
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hw.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  set C := Real.exp (L * T) - 1 with hC
  have hC0 : 0 ≤ C := by
    rw [hC, sub_nonneg]; exact Real.one_le_exp (mul_nonneg hL hT.le)
  rw [Metric.tendsto_atTop]
  intro e he
  set K := C * (|ε| + 1) + 1 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨δ, hδ, hδw⟩ := huc (e / (2 * K)) (by positivity)
  have hτ : Tendsto (fun N : ℕ => T / N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat T
  have hτ' : Tendsto (fun N : ℕ => C * A * (T / N)) atTop (𝓝 0) := by
    simpa using hτ.const_mul (C * A)
  obtain ⟨N₁, hN₁⟩ := (eventually_atTop.mp (hτ.eventually (gt_mem_nhds hδ)))
  obtain ⟨N₂, hN₂⟩ := (eventually_atTop.mp (hτ'.eventually (gt_mem_nhds (half_pos he))))
  refine ⟨max 1 (max N₁ N₂), fun N hN => ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le one_pos (le_of_max_le_left hN)
  have hNa : N₁ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hNb : N₂ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  have hmod : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |s - t| ≤ T / N → |w s - w t| ≤ e / (2 * K) := by
    intro s hs t ht hst
    have := hδw s hs t ht (by rw [Real.dist_eq]; exact lt_of_le_of_lt hst (hN₁ N hNa))
    rw [Real.dist_eq] at this
    exact this.le
  have herr := euler_pathwise_error_grid hL hLip hT hN1 hx ha hA' hmod
  rw [dist_comm, Real.dist_eq]
  have h1 : C * A * (T / N) < e / 2 := hN₂ N hNb
  have h2 : C * (|ε| * (e / (2 * K))) ≤ e / 2 := by
    have hCε : C * |ε| ≤ K := by rw [hK]; nlinarith [abs_nonneg ε]
    calc C * (|ε| * (e / (2 * K))) = (C * |ε|) * (e / (2 * K)) := by ring
      _ ≤ K * (e / (2 * K)) := by gcongr
      _ = e / 2 := by field_simp
  calc |x T - eulerPath a ε (T / N) w (x 0) N| ≤ C * (A * (T / N) + |ε| * (e / (2 * K))) := herr
    _ = C * A * (T / N) + C * (|ε| * (e / (2 * K))) := by ring
    _ < e / 2 + e / 2 := by linarith
    _ = e := by ring

/-- **Euler convergence with a Wiener path.**  Almost surely, for every pathwise solution `x` of
`dx = a(x)dt + ε dW` on `[0, T]` (Lipschitz `a`), the Euler scheme driven by the increments of the
same Wiener path converges to `x(T)`. -/
theorem IsWiener.ae_euler_tendsto {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ}
    {P : Measure Ω} (hW : IsWiener W P) {a : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ u v, |a u - a v| ≤ L * |u - v|) {ε T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ x : ℝ → ℝ, IsPathSol a ε (fun t => W t ω) x T →
      Tendsto (fun N : ℕ => eulerPath a ε (T / N) (fun t => W t ω) (x 0) N) atTop (𝓝 (x T)) := by
  filter_upwards [hW.cont] with ω hω x hx
  exact euler_tendsto_of_continuous hL hLip hT hω hx

/-- **Instance: `dx = -sin x dt + ε dW` with the standard Wiener process.**  For every sample point
and initial value there is a pathwise solution, and the Euler scheme driven by the Brownian
increments converges to it. -/
theorem euler_sin_stdWiener (ε c : ℝ) {T : ℝ} (hT : 0 < T) (ω : StdWienerSpace) :
    ∃ x : ℝ → ℝ, x 0 = c ∧ IsPathSol (fun u => -Real.sin u) ε (fun t => stdWiener t ω) x T ∧
      Tendsto (fun N : ℕ => eulerPath (fun u => -Real.sin u) ε (T / N)
        (fun t => stdWiener t ω) c N) atTop (𝓝 (x T)) := by
  obtain ⟨x, hx0, hx⟩ := exists_pathSol_sin_stdWiener ε T c hT.le ω
  refine ⟨x, hx0, hx, ?_⟩
  have h := euler_tendsto_of_continuous (L := 1) zero_le_one
    (fun u v => by
      show |-Real.sin u - -Real.sin v| ≤ 1 * |u - v|
      rw [one_mul]; exact abs_neg_sin_sub_le u v) hT (continuous_stdWiener ω) hx
  rwa [hx0] at h

/-! ### Small-noise linearisation for `a = -sin` -/

/-- The derivative tower of `a(x) = -sin x` (orders `0, 1, 2`; the higher entries are unused). -/
def sinD : ℕ → ℝ → ℝ
  | 0 => fun z => -Real.sin z
  | 1 => fun z => -Real.cos z
  | 2 => fun z => Real.sin z
  | _ + 3 => fun z => Real.cos z

lemma sinD_hasDerivAt (k : ℕ) (hk : k ≤ 1) (y : ℝ) : HasDerivAt (sinD k) (sinD (k + 1) y) y := by
  interval_cases k
  · exact (Real.hasDerivAt_sin y).neg
  · simpa [sinD] using (Real.hasDerivAt_cos y).neg

lemma sinD_continuous (p : ℕ) : Continuous (sinD p) := by
  match p with
  | 0 => exact Real.continuous_sin.neg
  | 1 => exact Real.continuous_cos.neg
  | 2 => exact Real.continuous_sin
  | _ + 3 => exact Real.continuous_cos

lemma sinD_bound (p : ℕ) (z : ℝ) : |sinD p z| ≤ 1 := by
  match p with
  | 0 => simpa [sinD] using Real.abs_sin_le_one z
  | 1 => simpa [sinD] using Real.abs_cos_le_one z
  | 2 => exact Real.abs_sin_le_one z
  | _ + 3 => exact Real.abs_cos_le_one z

/-- The pathwise Ornstein–Uhlenbeck process `x₁ = ∫₀ᵗ e^{-(t-s)} dw(s)`, written without a
stochastic integral: `x₁(t) = w(t) - w(0) - e^{-t}∫₀ᵗ eˢ(w(s) - w(0)) ds`.  It solves the
first-order equation (6.2.10b) of the hierarchy, `x₁(t) = w(t) - w(0) - ∫₀ᵗ x₁`. -/
def ouPath (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (w t - w 0) - Real.exp (-t) * ∫ s in (0 : ℝ)..t, Real.exp s * (w s - w 0)

lemma continuous_ouPath {w : ℝ → ℝ} (hw : Continuous w) : Continuous (ouPath w) := by
  unfold ouPath
  exact (hw.sub continuous_const).sub ((Real.continuous_exp.comp continuous_neg).mul
    (continuous_primitive' (Real.continuous_exp.mul (hw.sub continuous_const))))

lemma ouPath_eq {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    ouPath w t = (w t - w 0) + ∫ s in (0 : ℝ)..t, -ouPath w s := by
  set g : ℝ → ℝ := fun s => Real.exp s * (w s - w 0)
  have hg : Continuous g := Real.continuous_exp.mul (hw.sub continuous_const)
  set F : ℝ → ℝ := fun t => Real.exp (-t) * ∫ s in (0 : ℝ)..t, g s
  have hF : ∀ t, HasDerivAt F (ouPath w t) t := by
    intro t
    have h1 : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    have h2 : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, g s) (g t) t :=
      intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
        hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    convert h1.mul h2 using 1
    simp only [ouPath, g]
    rw [show Real.exp (-t) * (Real.exp t * (w t - w 0)) =
      (Real.exp (-t) * Real.exp t) * (w t - w 0) by ring, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero]
    ring
  have hint : ∫ s in (0 : ℝ)..t, ouPath w s = F t - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
      ((continuous_ouPath hw).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg, hint]
  simp only [F, intervalIntegral.integral_same, mul_zero, sub_zero, ouPath, g]
  ring

/-- The hierarchy (6.2.10)–(6.2.11) for `a = -sin`, `x(0) = 0`, up to order `1`:
`x₀ = 0`, `x₁ = ouPath w`. -/
def sinHier (w : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 1 => ouPath w
  | _ => fun _ => 0

lemma sinHier_isHierarchy {w : ℝ → ℝ} (hw : Continuous w) (T : ℝ) :
    IsHierarchy sinD w 0 (sinHier w) 1 T := by
  refine ⟨fun n => ?_, fun n hn t _ => ?_⟩
  · match n with
    | 0 => exact continuous_const
    | 1 => exact continuous_ouPath hw
    | _ + 2 => exact continuous_const
  · interval_cases n
    · simp [hierDrift, snCoeff_zero, sinHier, sinD]
    · simp only [hierDrift, snCoeff_one]
      simp only [sinHier, sinD, Real.cos_zero, if_true, one_ne_zero, if_false,
        zero_add]
      rw [ouPath_eq hw t]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp

/-- **(6.2.13)–(6.2.14) for `dx = -sin x dt + ε dw`, every continuous path.**  There is a constant
`C` (depending on the path and on `T`) such that for every `|ε| ≤ 1` and every pathwise solution
with `x(0) = 0`, `|x(t) - ε x₁(t)| ≤ C ε²` on `[0, T]`, where `x₁ = ouPath w` is the pathwise
Ornstein–Uhlenbeck process.  An instance of `Gardiner.SDE.linearisation_error`. -/
theorem sin_linearisation_path {w : ℝ → ℝ} (hw : Continuous w) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, ∀ ε : ℝ, |ε| ≤ 1 → ∀ x : ℝ → ℝ, IsPathSol (fun u => -Real.sin u) ε w x T →
      x 0 = 0 → ∀ t ∈ Icc 0 T, |x t - ε * ouPath w t| ≤ C * ε ^ 2 := by
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_ouPath hw).continuousOn
  have hR' : ∀ t ∈ Icc 0 T, |ouPath w t| ≤ R := fun t ht => by simpa using hR t ht
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR' 0 ⟨le_rfl, hT.le⟩)
  refine ⟨T * Real.exp (1 * T + 1 / 2) * (2 * 1 * Real.exp (2 * R)), fun ε hε x hx hx0 t ht => ?_⟩
  have hH : IsHierarchy sinD w (x 0) (sinHier w) 1 T := by
    rw [hx0]; exact sinHier_isHierarchy hw T
  have h := linearisation_error sinD sinD_hasDerivAt sinD_continuous zero_le_one
    (fun u v => by
      have h1 : |sinD 0 u - sinD 0 v| ≤ |u - v| := abs_neg_sin_sub_le u v
      calc (sinD 0 u - sinD 0 v) * (u - v) ≤ |sinD 0 u - sinD 0 v| * |u - v| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ |u - v| * |u - v| := by gcongr
        _ = 1 * (u - v) ^ 2 := by rw [← abs_mul, abs_mul_self, one_mul, sq])
    hε hT hR0 (x := x) hx hH hR' (fun p _ t _ z _ => sinD_bound p z) t ht
  simpa [sinHier] using h

/-- **The small-noise linearisation with a Wiener path** (almost surely). -/
theorem IsWiener.ae_sin_linearisation {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ}
    {P : Measure Ω} (hW : IsWiener W P) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ ε : ℝ, |ε| ≤ 1 → ∀ x : ℝ → ℝ,
      IsPathSol (fun u => -Real.sin u) ε (fun t => W t ω) x T → x 0 = 0 →
        ∀ t ∈ Icc 0 T, |x t - ε * ouPath (fun t => W t ω) t| ≤ C * ε ^ 2 := by
  filter_upwards [hW.cont] with ω hω
  exact sin_linearisation_path hω hT

/-- **Instance with the standard Wiener process.**  For every sample point there is `C` such that
for every `|ε| ≤ 1` the equation `dx = -sin x dt + ε dW`, `x(0) = 0`, has a pathwise solution and
every such solution satisfies `|x(t) - ε x₁(t)| ≤ C ε²` on `[0, T]`, with `x₁` the pathwise
Ornstein–Uhlenbeck process driven by the Brownian path. -/
theorem sin_linearisation_stdWiener {T : ℝ} (hT : 0 < T) (ω : StdWienerSpace) :
    ∃ C : ℝ, ∀ ε : ℝ, |ε| ≤ 1 →
      (∃ x : ℝ → ℝ, x 0 = 0 ∧ IsPathSol (fun u => -Real.sin u) ε (fun t => stdWiener t ω) x T) ∧
      ∀ x : ℝ → ℝ, IsPathSol (fun u => -Real.sin u) ε (fun t => stdWiener t ω) x T → x 0 = 0 →
        ∀ t ∈ Icc 0 T, |x t - ε * ouPath (fun t => stdWiener t ω) t| ≤ C * ε ^ 2 := by
  obtain ⟨C, hC⟩ := sin_linearisation_path (continuous_stdWiener ω) hT
  exact ⟨C, fun ε hε => ⟨exists_pathSol_sin_stdWiener ε T 0 hT.le ω, hC ε hε⟩⟩

/-! ### The third-order expansion of the cubic process with a Wiener path -/

/-- **(6.2.33), the finite-time expansion of the cubic process, for a continuous path**: there is
`C` such that for every `|ε| ≤ 1` and every pathwise solution of `dx = -x³dt + ε dw` with
`x(0) = 0`, `|x(t) - ε(w(t) - w(0)) + ε³∫₀ᵗ(w - w(0))³| ≤ Cε⁴` on `[0, T]` (an instance of
`Gardiner.SDE.pathwise_expansion` with `N = 3`, through `Gardiner.SDE.cubic_expansion`). -/
theorem cubic_expansion_path {w : ℝ → ℝ} (hw : Continuous w) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, ∀ ε : ℝ, |ε| ≤ 1 → ∀ x : ℝ → ℝ, IsPathSol (cubicD 0) ε w x T → x 0 = 0 →
      ∀ t ∈ Icc 0 T, |x t - (ε * (w t - w 0) + ε ^ 3 * -∫ s in (0 : ℝ)..t, (w s - w 0) ^ 3)| ≤
        C * ε ^ 4 := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (hw.sub continuous_const).continuousOn
  have hB' : ∀ t ∈ Icc 0 T, |w t - w 0| ≤ B := fun t ht => by simpa using hB t ht
  exact ⟨_, fun ε hε x hx hx0 => cubic_expansion hε hT hw hB' hx hx0⟩

/-- **The cubic expansion with a Wiener path** (almost surely). -/
theorem IsWiener.ae_cubic_expansion {Ω : Type*} [MeasurableSpace Ω] {W : ℝ → Ω → ℝ}
    {P : Measure Ω} (hW : IsWiener W P) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ ε : ℝ, |ε| ≤ 1 → ∀ x : ℝ → ℝ,
      IsPathSol (cubicD 0) ε (fun t => W t ω) x T → x 0 = 0 → ∀ t ∈ Icc 0 T,
        |x t - (ε * (W t ω - W 0 ω) + ε ^ 3 * -∫ s in (0 : ℝ)..t, (W s ω - W 0 ω) ^ 3)| ≤
          C * ε ^ 4 := by
  filter_upwards [hW.cont] with ω hω
  exact cubic_expansion_path hω hT

end Gardiner.Ito
