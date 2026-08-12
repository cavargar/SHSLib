/-
The vanishing of the higher order moment coefficients: equations (3.4.4)–(3.4.7)
of Gardiner, §3.4 ("Notice that all higher-order coefficients of the form in
(3.4.2,3) must vanish"), together with the last sentence of the paragraph
("Similarly, we can show that all corresponding higher-order quantities also
vanish").
-/
import SHSLib.Gardiner.Basic

open MeasureTheory Filter Topology Metric Set
open scoped BigOperators

noncomputable section

namespace Gardiner

variable {n : ℕ}

/-! ### An elementary vanishing criterion -/

/-- If `|v| ≤ c₁ ε + c₂ ε²` for every small `ε > 0`, then `v = 0`.  This is the step
"`= O(ε)` … so that `C` is zero" of (3.4.7): the coefficient does not depend on
`ε`, while the bound tends to `0` as `ε → 0`. -/
lemma eq_zero_of_abs_le_linear_quadratic {v c₁ c₂ : ℝ}
    (h : ∀ ε, 0 < ε → ε ≤ 1 → |v| ≤ c₁ * ε + c₂ * ε ^ 2) : v = 0 := by
  have hcont : Continuous fun ε : ℝ => c₁ * ε + c₂ * ε ^ 2 := by fun_prop
  have hlim : Tendsto (fun ε : ℝ => c₁ * ε + c₂ * ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => c₁ * ε + c₂ * ε ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using hcont.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have hle : |v| ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε using h ε hε.1 hε.2
  simpa using le_antisymm hle (abs_nonneg v)

/-! ### The core estimate (3.4.7) -/

/-- The pointwise inequality behind (3.4.7): if the extra factor `P` is bounded by
`ε` on the ball `|x - z| < ε`, then the corresponding higher moment integrand is
dominated by `ε` times a mean of two second order integrands. -/
lemma abs_moment_le {P : Sp n → ℝ} {z : Sp n} {i j : Fin n} {ε : ℝ}
    (x : Sp n) (hP : |P x| ≤ ε) :
    |(x i - z i) * (x j - z j) * P x| ≤
      ε * ((1 / 2) * ((x i - z i) * (x i - z i) + (x j - z j) * (x j - z j))) := by
  have hij : |(x i - z i) * (x j - z j)| ≤
      (1 / 2) * ((x i - z i) * (x i - z i) + (x j - z j) * (x j - z j)) := by
    nlinarith [sq_nonneg (|x i - z i| - |x j - z j|), abs_nonneg (x i - z i),
      abs_nonneg (x j - z j), abs_mul (x i - z i) (x j - z j), sq_abs (x i - z i),
      sq_abs (x j - z j)]
  calc |(x i - z i) * (x j - z j) * P x| = |(x i - z i) * (x j - z j)| * |P x| := abs_mul _ _
    _ ≤ ((1 / 2) * ((x i - z i) * (x i - z i) + (x j - z j) * (x j - z j))) * ε :=
        mul_le_mul hij hP (abs_nonneg _)
          (by nlinarith [mul_self_nonneg (x i - z i), mul_self_nonneg (x j - z j)])
    _ = ε * ((1 / 2) * ((x i - z i) * (x i - z i) + (x j - z j) * (x j - z j))) := by ring

/-- **The core of (3.4.7).**  Let `P` be a factor which is bounded by `ε` on every
small ball `|x - z| < ε`.  If the moments
`(1/Δt) ∫_{|x-z|<ε} (x_i - z_i)(x_j - z_j) P(x) p(x, t+Δt|z,t) dx`
converge, as `Δt → 0`, to a value which is `Cval` up to `O(ε)`, then `Cval = 0`.

Together with condition (iii) of §3.4 for the second moments, this is exactly the
chain of estimates (3.4.7); the factor `P` carries all the moment orders beyond the
second. -/
theorem moment_eq_zero_of_bound {k : ℝ → Sp n → Sp n → ℝ} {B : Sp n → Fin n → Fin n → ℝ}
    {z : Sp n} {i j : Fin n} {P : Sp n → ℝ} {Cval K : ℝ}
    (hP : ∀ ε, 0 < ε → ε ≤ 1 → ∀ x ∈ ball z ε, |P x| ≤ ε)
    (h2 : CondDiffusion k B)
    (hk0 : ∀ dt z x, 0 ≤ k dt z x)
    (hint : ∀ (dt ε : ℝ) (i j : Fin n) (z : Sp n),
      IntegrableOn (fun x => (x i - z i) * (x j - z j) * k dt z x) (ball z ε))
    (hlim : ∀ ε > 0, ∃ L : ℝ,
      Tendsto (fun dt : ℝ => (1 / dt) *
          ∫ x in ball z ε, (x i - z i) * (x j - z j) * P x * k dt z x)
        (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ |L - Cval| ≤ K * ε) :
    Cval = 0 := by
  obtain ⟨K', hK'⟩ := h2
  refine eq_zero_of_abs_le_linear_quadratic
    (c₁ := K + (1 / 2) * (B z i i + B z j j)) (c₂ := max K' 0) ?_
  intro ε hε hε1
  obtain ⟨L, hL, hLC⟩ := hlim ε hε
  obtain ⟨Mi, hMi, hMiB⟩ := hK' ε hε i i z
  obtain ⟨Mj, hMj, hMjB⟩ := hK' ε hε j j z
  -- the pointwise estimate, integrated, for every `dt > 0`
  have hstep : ∀ dt ∈ Ioi (0 : ℝ),
      |(1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * P x * k dt z x| ≤
        ε * ((1 / 2) * (((1 / dt) * ∫ x in ball z ε, (x i - z i) * (x i - z i) * k dt z x) +
          ((1 / dt) * ∫ x in ball z ε, (x j - z j) * (x j - z j) * k dt z x))) := by
    intro dt hdt
    have hdt0 : (0 : ℝ) < dt := hdt
    have hmaj : IntegrableOn
        (fun x => ε * ((1 / 2) * ((x i - z i) * (x i - z i) * k dt z x +
          (x j - z j) * (x j - z j) * k dt z x))) (ball z ε) :=
      (((hint dt ε i i z).add (hint dt ε j j z)).const_mul (1 / 2)).const_mul ε
    have hpt : ∀ x ∈ ball z ε,
        |(x i - z i) * (x j - z j) * P x * k dt z x| ≤
          ε * ((1 / 2) * ((x i - z i) * (x i - z i) * k dt z x +
            (x j - z j) * (x j - z j) * k dt z x)) := by
      intro x hx
      have hk : 0 ≤ k dt z x := hk0 dt z x
      have h1 := abs_moment_le (P := P) (z := z) (i := i) (j := j) x (hP ε hε hε1 x hx)
      calc |(x i - z i) * (x j - z j) * P x * k dt z x|
          = |(x i - z i) * (x j - z j) * P x| * k dt z x := by
            rw [abs_mul, abs_of_nonneg hk]
        _ ≤ (ε * ((1 / 2) * ((x i - z i) * (x i - z i) + (x j - z j) * (x j - z j)))) *
              k dt z x := mul_le_mul_of_nonneg_right h1 hk
        _ = ε * ((1 / 2) * ((x i - z i) * (x i - z i) * k dt z x +
              (x j - z j) * (x j - z j) * k dt z x)) := by ring
    have hI : |∫ x in ball z ε, (x i - z i) * (x j - z j) * P x * k dt z x| ≤
        ∫ x in ball z ε, ε * ((1 / 2) * ((x i - z i) * (x i - z i) * k dt z x +
          (x j - z j) * (x j - z j) * k dt z x)) := by
      refine le_trans (abs_integral_le_integral_abs) ?_
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
        hmaj ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx using hpt x hx
    have hsplit : ∫ x in ball z ε, ε * ((1 / 2) * ((x i - z i) * (x i - z i) * k dt z x +
          (x j - z j) * (x j - z j) * k dt z x)) =
        ε * ((1 / 2) * ((∫ x in ball z ε, (x i - z i) * (x i - z i) * k dt z x) +
          ∫ x in ball z ε, (x j - z j) * (x j - z j) * k dt z x)) := by
      rw [integral_const_mul, integral_const_mul,
        integral_add (hint dt ε i i z) (hint dt ε j j z)]
    rw [hsplit] at hI
    have hinv : (0 : ℝ) < 1 / dt := by positivity
    calc |(1 / dt) * ∫ x in ball z ε, (x i - z i) * (x j - z j) * P x * k dt z x|
        = (1 / dt) * |∫ x in ball z ε, (x i - z i) * (x j - z j) * P x * k dt z x| := by
          rw [abs_mul, abs_of_pos hinv]
      _ ≤ (1 / dt) * (ε * ((1 / 2) * ((∫ x in ball z ε, (x i - z i) * (x i - z i) * k dt z x) +
            ∫ x in ball z ε, (x j - z j) * (x j - z j) * k dt z x))) :=
          mul_le_mul_of_nonneg_left hI hinv.le
      _ = ε * ((1 / 2) * (((1 / dt) * ∫ x in ball z ε, (x i - z i) * (x i - z i) * k dt z x) +
            ((1 / dt) * ∫ x in ball z ε, (x j - z j) * (x j - z j) * k dt z x))) := by ring
  -- pass to the limit `dt → 0`
  have hlim' : |L| ≤ ε * ((1 / 2) * (Mi + Mj)) := by
    refine le_of_tendsto_of_tendsto hL.abs (((hMi.add hMj).const_mul (1 / 2)).const_mul ε) ?_
    filter_upwards [self_mem_nhdsWithin] with dt hdt using hstep dt hdt
  -- and compare with the diffusion matrix `B`
  have hK'0 : (0 : ℝ) ≤ max K' 0 := le_max_right _ _
  have hMile : Mi ≤ B z i i + max K' 0 * ε := by
    have h1 : Mi - B z i i ≤ |Mi - B z i i| := le_abs_self _
    have h2 : K' * ε ≤ max K' 0 * ε := by
      have := le_max_left K' (0 : ℝ); nlinarith
    linarith [hMiB]
  have hMjle : Mj ≤ B z j j + max K' 0 * ε := by
    have h1 : Mj - B z j j ≤ |Mj - B z j j| := le_abs_self _
    have h2 : K' * ε ≤ max K' 0 * ε := by
      have := le_max_left K' (0 : ℝ); nlinarith
    linarith [hMjB]
  have hCL : |Cval| ≤ |L| + K * ε := by
    have hsub : |Cval - L| ≤ K * ε := by rwa [abs_sub_comm] at hLC
    calc |Cval| = |L + (Cval - L)| := by ring_nf
      _ ≤ |L| + |Cval - L| := abs_add_le _ _
      _ ≤ |L| + K * ε := by linarith
  nlinarith [hlim', hCL, hMile, hMjle, hε.le, abs_nonneg L]

/-! ### The third order coefficient (3.4.4)–(3.4.7) -/

/-- (3.4.4): the third order quantity `C_{ijk}(z, t)`.  As in (3.4.2), (3.4.3) the
limit of the moment over the `ε`-ball is required to equal `C_{ijk}` up to an error
`O(ε)` which is uniform in `z` (and in `ε`). -/
def CondThird (k : ℝ → Sp n → Sp n → ℝ) (C : Sp n → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∃ K : ℝ, ∀ ε > 0, ∀ (i j l : Fin n) (z : Sp n), ∃ L : ℝ,
    Tendsto (fun dt : ℝ => (1 / dt) *
        ∫ x in ball z ε, (x i - z i) * (x j - z j) * (x l - z l) * k dt z x)
      (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ |L - C z i j l| ≤ K * ε

/-- (3.4.5): the cubic form `C̄(α, z, t) = ∑_{ijk} α_i α_j α_k C_{ijk}(z, t)`. -/
def cubicForm (C : Sp n → Fin n → Fin n → Fin n → ℝ) (α : Sp n) (z : Sp n) : ℝ :=
  ∑ i, ∑ j, ∑ l, α i * α j * α l * C z i j l

/-- The third order coefficient of (3.4.4) vanishes: this is (3.4.7).

The estimate used is the pointwise bound `|a b c| ≤ ε (a² + b²)/2` valid on the ball
`|x - z| < ε`, which plays the role of the Cauchy–Schwarz contraction with `α` in
(3.4.5)–(3.4.7); it reduces the third moment to the second moments controlled by
condition (iii), (3.4.3). -/
theorem CondThird.eq_zero {k : ℝ → Sp n → Sp n → ℝ} {B : Sp n → Fin n → Fin n → ℝ}
    {C : Sp n → Fin n → Fin n → Fin n → ℝ}
    (h3 : CondThird k C) (h2 : CondDiffusion k B)
    (hk0 : ∀ dt z x, 0 ≤ k dt z x)
    (hint : ∀ (dt ε : ℝ) (i j : Fin n) (z : Sp n),
      IntegrableOn (fun x => (x i - z i) * (x j - z j) * k dt z x) (ball z ε))
    (i j l : Fin n) (z : Sp n) : C z i j l = 0 := by
  obtain ⟨K, hK⟩ := h3
  refine moment_eq_zero_of_bound (z := z) (i := i) (j := j) (K := K)
    (P := fun x => x l - z l) ?_ h2 hk0 hint ?_
  · intro ε _ _ x hx
    have hd : ‖x - z‖ < ε := by simpa [dist_eq_norm] using hx
    have hl : |x l - z l| ≤ ‖x - z‖ := by
      simpa [PiLp.sub_apply] using PiLp.norm_apply_le (x - z) l
    exact hl.trans hd.le
  · intro ε hε
    exact hK ε hε i j l z

/-- (3.4.5)–(3.4.7): the cubic form `C̄(α, z, t)` vanishes identically. -/
theorem CondThird.cubicForm_eq_zero {k : ℝ → Sp n → Sp n → ℝ} {B : Sp n → Fin n → Fin n → ℝ}
    {C : Sp n → Fin n → Fin n → Fin n → ℝ}
    (h3 : CondThird k C) (h2 : CondDiffusion k B)
    (hk0 : ∀ dt z x, 0 ≤ k dt z x)
    (hint : ∀ (dt ε : ℝ) (i j : Fin n) (z : Sp n),
      IntegrableOn (fun x => (x i - z i) * (x j - z j) * k dt z x) (ball z ε))
    (α z : Sp n) : cubicForm C α z = 0 := by
  simp [cubicForm, h3.eq_zero h2 hk0 hint _ _ _ z]

/-! ### All higher order coefficients -/

/-- The product `∏_r (x_{i_r} - z_{i_r})` over a list of indices. -/
def coordProd (z x : Sp n) (l : List (Fin n)) : ℝ := (l.map fun r => x r - z r).prod

lemma abs_coordProd_le {z x : Sp n} {ε : ℝ} (hx : x ∈ ball z ε) :
    ∀ l : List (Fin n), |coordProd z x l| ≤ ε ^ l.length := by
  have hd : ‖x - z‖ < ε := by simpa [dist_eq_norm] using hx
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) hd.le
  intro l
  induction l with
  | nil => simp [coordProd]
  | cons r l ih =>
      have hr : |x r - z r| ≤ ε := by
        have : |x r - z r| ≤ ‖x - z‖ := by
          simpa [PiLp.sub_apply] using PiLp.norm_apply_le (x - z) r
        exact this.trans hd.le
      have hprod : coordProd z x (r :: l) = (x r - z r) * coordProd z x l := by
        simp [coordProd]
      rw [hprod, abs_mul, List.length_cons, pow_succ]
      calc |x r - z r| * |coordProd z x l| ≤ ε * ε ^ l.length :=
            mul_le_mul hr ih (abs_nonneg _) hε
        _ = ε ^ l.length * ε := by ring

/-- The moment coefficients of order `≥ 3`: the analogue of (3.4.4) for the moment
`(x_i - z_i)(x_j - z_j) ∏_r (x_{i_r} - z_{i_r})`, where `l` is an arbitrary list of
further indices. -/
def CondHigher (k : ℝ → Sp n → Sp n → ℝ)
    (C : Sp n → Fin n → Fin n → List (Fin n) → ℝ) : Prop :=
  ∃ K : ℝ, ∀ ε > 0, ∀ (i j : Fin n) (l : List (Fin n)) (z : Sp n), ∃ L : ℝ,
    Tendsto (fun dt : ℝ => (1 / dt) *
        ∫ x in ball z ε, (x i - z i) * (x j - z j) * coordProd z x l * k dt z x)
      (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ |L - C z i j l| ≤ K * ε

/-- "Similarly, we can show that all corresponding higher-order quantities also
vanish": every moment coefficient of order at least three vanishes. -/
theorem CondHigher.eq_zero {k : ℝ → Sp n → Sp n → ℝ} {B : Sp n → Fin n → Fin n → ℝ}
    {C : Sp n → Fin n → Fin n → List (Fin n) → ℝ}
    (hC : CondHigher k C) (h2 : CondDiffusion k B)
    (hk0 : ∀ dt z x, 0 ≤ k dt z x)
    (hint : ∀ (dt ε : ℝ) (i j : Fin n) (z : Sp n),
      IntegrableOn (fun x => (x i - z i) * (x j - z j) * k dt z x) (ball z ε))
    (i j : Fin n) (l : List (Fin n)) (hl : l ≠ []) (z : Sp n) : C z i j l = 0 := by
  obtain ⟨K, hK⟩ := hC
  refine moment_eq_zero_of_bound (z := z) (i := i) (j := j) (K := K)
    (P := fun x => coordProd z x l) ?_ h2 hk0 hint ?_
  · intro ε hε hε1 x hx
    have hlen : 1 ≤ l.length := List.length_pos_iff.mpr hl
    have h1 : |coordProd z x l| ≤ ε ^ l.length := abs_coordProd_le hx l
    have h2' : ε ^ l.length ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 hlen
    simpa using h1.trans h2'
  · intro ε hε
    exact hK ε hε i j l z

end Gardiner
