/-
# Pathwise convergence of the Euler scheme for additive noise (Gardiner §10.1.1, §10.1.4)

For additive noise the explicit Euler algorithm (10.1.3), (10.1.15)–(10.1.17),

  `y_{n+1} = y_n + a(y_n) τ + ε (w(τ_{n+1}) - w(τ_n))`,   `τ_n = nτ`,

can be driven by the increments of an **arbitrary continuous path** `w`, and compared with the
pathwise solution `x(t) = x(0) + ∫₀ᵗ a(x) + ε(w(t) - w(0))` of `Gardiner.SDE.IsPathSol`.  No
probability is needed: the error is controlled by the step size and by a modulus of continuity
`ω` of the path (`|w(s) - w(t)| ≤ ω` whenever `|s - t| ≤ τ`).

`Gardiner.SDE.euler_pathwise_error`: if `a` is `L`-Lipschitz and `|a(x(s))| ≤ A` on `[0, T]`, then
for every `n` with `nτ ≤ T`

  `|x(nτ) - y_n| ≤ (e^{L n τ} - 1) (A τ + |ε| ω)`.

For a Brownian path (Hölder of every order `< 1/2`) this gives the pathwise rate `τ^{1/2-}`, the
pathwise counterpart of the strong order `τ^{1/2}` claimed in (10.1.26).  The instance
`Gardiner.SDE.euler_sin_sqrt` treats `a = -sin x` driven by the Hölder-`½` path `w(t) = √t`:
`|x(T) - y_N| ≤ (e^T - 1)(T/N + |ε| √(T/N))`.
-/
import SHSLib.Gardiner.SDE.Pathwise

open Set Finset MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

namespace Gardiner.SDE

/-- The explicit Euler scheme (10.1.15) for `dx = a(x)dt + ε dw`, driven by the increments
`w(τ_{n+1}) - w(τ_n)` of a path `w`. -/
def eulerPath (a : ℝ → ℝ) (ε τ : ℝ) (w : ℝ → ℝ) (y0 : ℝ) : ℕ → ℝ
  | 0 => y0
  | n + 1 => eulerPath a ε τ w y0 n + a (eulerPath a ε τ w y0 n) * τ +
      ε * (w ((n + 1 : ℕ) * τ) - w (n * τ))

/-- The one-step error recursion: `|e_{n+1}| ≤ (1 + Lτ)|e_n| + Lτ(Aτ + |ε|ω)`. -/
theorem euler_step_error {a : ℝ → ℝ} {L A ε τ T ω : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ u v, |a u - a v| ≤ L * |u - v|) (hτ : 0 < τ)
    {w x : ℝ → ℝ} (hx : IsPathSol a ε w x T) (ha : Continuous a)
    (hA : ∀ s ∈ Icc 0 T, |a (x s)| ≤ A)
    (hω : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |s - t| ≤ τ → |w s - w t| ≤ ω)
    (y0 : ℝ) (n : ℕ) (hn : ((n + 1 : ℕ) : ℝ) * τ ≤ T) :
    |x ((n + 1 : ℕ) * τ) - eulerPath a ε τ w y0 (n + 1)| ≤
      (1 + L * τ) * |x (n * τ) - eulerPath a ε τ w y0 n| + L * τ * (A * τ + |ε| * ω) := by
  set t0 : ℝ := n * τ
  set t1 : ℝ := ((n + 1 : ℕ) : ℝ) * τ
  have ht01 : t1 = t0 + τ := by simp [t0, t1]; ring
  have ht0 : 0 ≤ t0 := by positivity
  have ht0T : t0 ≤ T := by linarith
  have hgc : Continuous fun s => a (x s) := ha.comp hx.cont
  set y := eulerPath a ε τ w y0 n
  -- increment of the exact solution
  have hinc : ∀ s ∈ Icc t0 t1, x s - x t0 = (∫ r in t0..s, a (x r)) + ε * (w s - w t0) := by
    intro s hs
    have hs' : s ∈ Icc 0 T := ⟨ht0.trans hs.1, hs.2.trans hn⟩
    rw [hx.eq s hs', hx.eq t0 ⟨ht0, ht0T⟩]
    have := intervalIntegral.integral_interval_sub_left (μ := volume) (hgc.intervalIntegrable 0 s)
      (hgc.intervalIntegrable 0 t0)
    rw [← this]; ring
  have hstep : x t1 - eulerPath a ε τ w y0 (n + 1) =
      (x t0 - y) + ∫ r in t0..t1, (a (x r) - a y) := by
    have h1 := hinc t1 ⟨by linarith, le_rfl⟩
    rw [intervalIntegral.integral_sub (hgc.intervalIntegrable _ _) intervalIntegral.intervalIntegrable_const,
      intervalIntegral.integral_const, ht01]
    simp only [eulerPath, smul_eq_mul]
    rw [← ht01, show ((n : ℕ) : ℝ) * τ = t0 from rfl, ← show t1 = ((n + 1 : ℕ) : ℝ) * τ from rfl]
    rw [ht01] at h1 ⊢
    simp only [add_sub_cancel_left]
    linarith
  -- bound on the integrand
  have hint : ∀ r ∈ Ι t0 t1, ‖a (x r) - a y‖ ≤ L * ((A * τ + |ε| * ω) + |x t0 - y|) := by
    intro r hr
    rw [Set.uIoc_of_le (by linarith)] at hr
    have hr' : r ∈ Icc t0 t1 := ⟨hr.1.le, hr.2⟩
    have hxr : |x r - x t0| ≤ A * τ + |ε| * ω := by
      rw [hinc r hr']
      have hI : ‖∫ s in t0..r, a (x s)‖ ≤ A * |r - t0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
        rw [Set.uIoc_of_le hr.1.le] at hs
        exact hA s ⟨ht0.trans hs.1.le, hs.2.trans (hr.2.trans hn)⟩
      have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA t0 ⟨ht0, ht0T⟩)
      have hW : |w r - w t0| ≤ ω := hω r ⟨ht0.trans hr.1.le, hr.2.trans hn⟩ t0 ⟨ht0, ht0T⟩
        (by rw [abs_of_nonneg (by linarith [hr.1])]; linarith [hr.2])
      calc |(∫ s in t0..r, a (x s)) + ε * (w r - w t0)|
          ≤ |∫ s in t0..r, a (x s)| + |ε| * |w r - w t0| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ A * τ + |ε| * ω := by
            refine add_le_add ?_ (mul_le_mul_of_nonneg_left hW (abs_nonneg _))
            refine hI.trans (mul_le_mul_of_nonneg_left ?_ hA0)
            rw [abs_of_nonneg (by linarith [hr.1])]; linarith [hr.2]
    rw [Real.norm_eq_abs]
    calc |a (x r) - a y| ≤ L * |x r - y| := hLip _ _
      _ ≤ L * ((A * τ + |ε| * ω) + |x t0 - y|) := by
        refine mul_le_mul_of_nonneg_left ?_ hL
        calc |x r - y| = |(x r - x t0) + (x t0 - y)| := by ring_nf
          _ ≤ |x r - x t0| + |x t0 - y| := abs_add_le _ _
          _ ≤ _ := by linarith
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hint
  rw [ht01, show t0 + τ - t0 = τ by ring, abs_of_pos hτ, ← ht01] at hI
  rw [hstep]
  calc |(x t0 - y) + ∫ r in t0..t1, (a (x r) - a y)|
      ≤ |x t0 - y| + ‖∫ r in t0..t1, (a (x r) - a y)‖ := abs_add_le _ _
    _ ≤ |x t0 - y| + L * ((A * τ + |ε| * ω) + |x t0 - y|) * τ := by linarith
    _ = (1 + L * τ) * |x t0 - y| + L * τ * (A * τ + |ε| * ω) := by ring

/-- **Pathwise convergence of the Euler scheme for additive noise.**  If `a` is `L`-Lipschitz,
`|a(x(s))| ≤ A` along the solution on `[0, T]` and `ω` is a modulus of continuity of the driving
path at scale `τ`, the Euler scheme started at `x(0)` satisfies, for every `n` with `nτ ≤ T`,
`|x(nτ) - y_n| ≤ (e^{Lnτ} - 1)(Aτ + |ε|ω)`. -/
theorem euler_pathwise_error {a : ℝ → ℝ} {L A ε τ T ω : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ u v, |a u - a v| ≤ L * |u - v|) (hτ : 0 < τ)
    {w x : ℝ → ℝ} (hx : IsPathSol a ε w x T) (ha : Continuous a)
    (hA : ∀ s ∈ Icc 0 T, |a (x s)| ≤ A)
    (hω : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |s - t| ≤ τ → |w s - w t| ≤ ω)
    (n : ℕ) (hn : (n : ℝ) * τ ≤ T) :
    |x (n * τ) - eulerPath a ε τ w (x 0) n| ≤
      (Real.exp (L * (n * τ)) - 1) * (A * τ + |ε| * ω) := by
  have hT : 0 ≤ T := le_trans (by positivity) hn
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 ⟨le_rfl, hT⟩)
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans (hω 0 ⟨le_rfl, hT⟩ 0 ⟨le_rfl, hT⟩ (by simp; positivity))
  set c := A * τ + |ε| * ω
  have hc : 0 ≤ c := by positivity
  -- discrete Grönwall: `|e_n| ≤ ((1 + Lτ)^n - 1) c`
  have hdisc : ∀ k : ℕ, (k : ℝ) * τ ≤ T →
      |x (k * τ) - eulerPath a ε τ w (x 0) k| ≤ ((1 + L * τ) ^ k - 1) * c := by
    intro k
    induction k with
    | zero => intro _; simp [eulerPath]
    | succ k ih =>
      intro hk
      have hk' : (k : ℝ) * τ ≤ T := le_trans (by push_cast; nlinarith) hk
      have h1 := euler_step_error hL hLip hτ hx ha hA hω (x 0) k hk
      have h2 := ih hk'
      calc |x ((k + 1 : ℕ) * τ) - eulerPath a ε τ w (x 0) (k + 1)|
          ≤ (1 + L * τ) * |x (k * τ) - eulerPath a ε τ w (x 0) k| + L * τ * c := h1
        _ ≤ (1 + L * τ) * (((1 + L * τ) ^ k - 1) * c) + L * τ * c := by
            gcongr
        _ = ((1 + L * τ) ^ (k + 1) - 1) * c := by ring
  refine (hdisc n hn).trans (mul_le_mul_of_nonneg_right ?_ hc)
  have : (1 + L * τ) ^ n ≤ Real.exp (L * (n * τ)) := by
    calc (1 + L * τ) ^ n ≤ Real.exp (L * τ) ^ n :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (L * τ)]) n
      _ = Real.exp (L * (n * τ)) := by rw [← Real.exp_nat_mul]; ring_nf
  linarith

/-- The uniform-grid form: with `τ = T/N`, `|x(T) - y_N| ≤ (e^{LT} - 1)(AT/N + |ε| ω)`. -/
theorem euler_pathwise_error_grid {a : ℝ → ℝ} {L A ε T ω : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ u v, |a u - a v| ≤ L * |u - v|) (hT : 0 < T) {N : ℕ} (hN : 0 < N)
    {w x : ℝ → ℝ} (hx : IsPathSol a ε w x T) (ha : Continuous a)
    (hA : ∀ s ∈ Icc 0 T, |a (x s)| ≤ A)
    (hω : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |s - t| ≤ T / N → |w s - w t| ≤ ω) :
    |x T - eulerPath a ε (T / N) w (x 0) N| ≤
      (Real.exp (L * T) - 1) * (A * (T / N) + |ε| * ω) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkey : (N : ℝ) * (T / N) = T := by field_simp
  have h := euler_pathwise_error hL hLip (by positivity) hx ha hA hω N (by rw [hkey])
  rwa [hkey] at h

/-! ### A concrete instance: `a = -sin x` driven by the Hölder path `√t` -/

lemma abs_sqrt_sub_sqrt_le (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.sqrt s - Real.sqrt t| ≤ Real.sqrt |s - t| := by
  wlog hst : t ≤ s generalizing s t
  · rw [abs_sub_comm, abs_sub_comm s t]; exact this t s ht hs (by linarith)
  have h1 : Real.sqrt t ≤ Real.sqrt s := Real.sqrt_le_sqrt hst
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  rw [Real.le_sqrt (by linarith) (by linarith)]
  have := Real.sq_sqrt hs
  have := Real.sq_sqrt ht
  nlinarith [Real.sqrt_nonneg t]

/-- Instance: `dx = -sin x dt + ε d√t`.  The Euler scheme with `N` steps on `[0, T]` satisfies
`|x(T) - y_N| ≤ (e^T - 1)(T/N + |ε| √(T/N))` for every pathwise solution `x`. -/
theorem euler_sin_sqrt {ε T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N) {x : ℝ → ℝ}
    (hx : IsPathSol (fun u => -Real.sin u) ε (fun t => Real.sqrt t) x T) :
    |x T - eulerPath (fun u => -Real.sin u) ε (T / N) (fun t => Real.sqrt t) (x 0) N| ≤
      (Real.exp T - 1) * (T / N + |ε| * Real.sqrt (T / N)) := by
  have h := euler_pathwise_error_grid (a := fun u => -Real.sin u) (L := 1) (A := 1)
    (ω := Real.sqrt (T / N)) zero_le_one
    (fun u v => by
      simp only [one_mul]
      rw [show -Real.sin u - -Real.sin v = -(Real.sin u - Real.sin v) by ring, abs_neg]
      exact Real.abs_sin_sub_sin_le u v) hT hN hx
    Real.continuous_sin.neg (fun s _ => by simpa using Real.abs_sin_le_one (x s))
    (fun s hs t ht hst => (abs_sqrt_sub_sqrt_le s t hs.1 ht.1).trans (Real.sqrt_le_sqrt hst))
  simpa using h

end Gardiner.SDE

/-! ### Existence of pathwise solutions for bounded Lipschitz drifts -/

namespace Gardiner.SDE

open scoped NNReal Topology

/-- **Existence of the pathwise solution** of `dx = a(x)dt + ε dw` on `[0, T]` for a bounded
Lipschitz drift and any continuous path `w` (Picard–Lindelöf applied to `z = x - ε(w - w(0))`,
`ż = a(z + ε(w(t) - w(0)))`).  This shows that the hypotheses of the pathwise theorems are
satisfiable. -/
theorem exists_pathSol {a : ℝ → ℝ} {B : ℝ≥0} {K : ℝ≥0} (hLip : LipschitzWith K a)
    (hB : ∀ u, |a u| ≤ B) (ε : ℝ) {w : ℝ → ℝ} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T)
    (c : ℝ) : ∃ x : ℝ → ℝ, x 0 = c ∧ IsPathSol a ε w x T := by
  set f : ℝ → ℝ → ℝ := fun t z => a (z + ε * (w t - w 0))
  set Tn : ℝ≥0 := ⟨T, hT⟩
  have hPL : IsPicardLindelof f (tmin := 0) (tmax := T) ⟨0, ⟨le_rfl, hT⟩⟩ c (B * Tn) 0 B K := by
    refine ⟨fun t _ => ?_, fun z _ => ?_, fun t _ z _ => ?_, ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun u _ v _ => ?_
      have := hLip.dist_le_mul (u + ε * (w t - w 0)) (v + ε * (w t - w 0))
      simpa [f, Real.dist_eq] using this
    · exact (hLip.continuous.comp (continuous_const.add
        (continuous_const.mul (hw.sub continuous_const)))).continuousOn
    · simpa [f, Real.norm_eq_abs] using hB _
    · simp [Tn, max_eq_left hT]
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hαc : ContinuousOn α (Icc 0 T) := fun t ht => (hα t ht).continuousWithinAt
  set x : ℝ → ℝ := fun t => α (Set.projIcc 0 T hT t) + ε * (w t - w 0)
  have hxc : Continuous x :=
    (hαc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => Subtype.mem _)).add
      (continuous_const.mul (hw.sub continuous_const))
  have hxα : ∀ t ∈ Icc 0 T, x t = α t + ε * (w t - w 0) := by
    intro t ht
    simp only [x, Set.projIcc_of_mem hT ht]
  have hx0 : x 0 = c := by
    rw [hxα 0 ⟨le_rfl, hT⟩]; simp [hα0]
  refine ⟨x, hx0, hxc, fun t ht => ?_⟩
  -- the integral equation, from the fundamental theorem of calculus
  have hfc : ContinuousOn (fun s => f s (α s)) (Icc 0 T) := by
    refine (hLip.continuous.comp_continuousOn (hαc.add ?_))
    exact (continuous_const.mul (hw.sub continuous_const)).continuousOn
  have hFTC : ∫ s in (0 : ℝ)..t, f s (α s) = α t - α 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hαc.mono (Set.Icc_subset_Icc le_rfl ht.2)) (fun s hs => ?_)
      ((hfc.mono (Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
    have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hmem : Icc 0 T ∈ 𝓝 s := Icc_mem_nhds hs.1 (hs.2.trans_le ht.2)
    exact ((hα s hs').hasDerivAt hmem).hasDerivWithinAt
  have hcongr : ∫ s in (0 : ℝ)..t, a (x s) = ∫ s in (0 : ℝ)..t, f s (α s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht.1] at hs
    simp only [f, hxα s ⟨hs.1, hs.2.trans ht.2⟩]
  rw [hcongr, hFTC, hxα t ht, hx0, ← hα0]
  ring

/-- Non-vacuity of `Gardiner.SDE.euler_sin_sqrt`: the equation `dx = -sin x dt + ε d√t` has a
pathwise solution from every initial point. -/
theorem exists_pathSol_sin_sqrt (ε T c : ℝ) (hT : 0 ≤ T) :
    ∃ x : ℝ → ℝ, x 0 = c ∧ IsPathSol (fun u => -Real.sin u) ε (fun t => Real.sqrt t) x T :=
  exists_pathSol (B := 1) (K := 1)
    (LipschitzWith.of_dist_le_mul fun u v => by
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rw [show -Real.sin u - -Real.sin v = -(Real.sin u - Real.sin v) by ring, abs_neg]
      exact Real.abs_sin_sub_sin_le u v)
    (fun u => by simpa using Real.abs_sin_le_one u) ε Real.continuous_sqrt hT c

end Gardiner.SDE
