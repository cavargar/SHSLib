/-
# Equilibration of the populations in each well: §9.2, (9.2.1)–(9.2.33), (9.2.46)–(9.2.49)

Kramers' method reduces the double-well Smoluchowski equation to the three relaxation equations
(9.2.8) for the well populations `N_a`, `N_c` and the barrier population `N₀`.  We formalise:

* `flux_identity` — **(9.2.5)**: `U'p + Dp' = D p_s ∂ₓ(p/p_s)` for `p_s ∝ e^{-U/D}`, and
  `kramers_integrated` — **(9.2.6)**, its integral (exact);
* `kramers_ansatz` — **(9.2.7) ⇒ (9.2.8)** (the ansatz is a named hypothesis);
* `barrier_population` — **(9.2.13), corrected** (`N₀ = n₀[μN_a/n_a + κN_c/n_c]/(κ + μ)`);
  `barrier_population_printed_wrong`;
* `threeState_stationary` — **(9.2.14), corrected** (`Ṅ₀ = D{N_a/(n_aκ) + N_c/(n_cμ)
  - N₀ n₀⁻¹(κ⁻¹ + μ⁻¹)}`): adiabatic elimination of `N₀` gives back (9.2.13);
* `relaxation_rates` — **(9.2.16)–(9.2.18), corrected sign** (`Ṅ_a = -r_aN_a + r_cN_c`),
  `τ_r⁻¹ = r_a + r_c = D/(n_a n_c ∫_a^c p_s⁻¹)`;
* `escape_time` — **(9.2.19)–(9.2.20)**: the mean of the exponential decay law is `n_aκ/D`;
* chymotrypsinogen §9.2.2: `chymo_extremum` — **(9.2.30)–(9.2.31)**, exact for locally quadratic
  `U₀`; `chymo_population_ratio` — **(9.2.32)** (printed with the label (9.3.32));
  `chymo_H_ratio`, `chymo_relaxTime` — **(9.2.33)** with the corrections recorded below;
* `discrete_ansatz_M` — **(9.2.46)–(9.2.49)** with the corrected ranges of `ψ`.

**Errata recorded.**
(9.2.4) `n_a = ∫_{-∞}^b p_s` (not `∫^c`).  (9.2.13) `N_a`, `N_c` must be divided by `n_a`, `n_c`.
(9.2.14) the coefficient of `N₀` is `D n₀⁻¹(κ⁻¹ + μ⁻¹)` (and `N₀` enters as `N₀/n₀`).
(9.2.16) `Ṅ_a = -r_a N_a + r_c N_c`.  (9.3.32) is (9.2.32).  (9.2.33) for (9.2.26) the effective
potential is `U/γ` and `D = kT/γ`, so `H` carries a factor `γ` (not `γ⁻¹`) and the factor
`(β_aβ_c)^{1/4}`; with `τ_r(0) = πH(0)` the second line needs `2τ_r(0)` in place of `τ_r(0)`.
(9.2.49) `ψ(z) = n_a⁻¹ Σ_{y=z}^{b-1} P_s(y)` for `z ≤ b` and `n_c⁻¹ Σ_{y=b}^{z-1} P_s(y)` for
`z > b` (the text has upper limits `b` and `z + 1`).
-/
import SHSLib.Gardiner.Escape.DoubleWell

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-! ### (9.2.5)–(9.2.6) -/

/-- **(9.2.5)**: with `p_s = 𝒩 e^{-U/D}`, the probability current of (9.1.1) is
`U'p + Dp' = D p_s ∂ₓ(p/p_s)`. -/
theorem flux_identity {U U' p p' : ℝ → ℝ} {D 𝒩 : ℝ} (hD : 0 < D) (h𝒩 : 0 < 𝒩) {x : ℝ}
    (hU : HasDerivAt U (U' x) x) (hp : HasDerivAt p (p' x) x) :
    HasDerivAt (fun y => p y / (𝒩 * exp (-U y / D)))
      ((U' x * p x + D * p' x) / (D * (𝒩 * exp (-U x / D)))) x := by
  have hs : HasDerivAt (fun y => 𝒩 * exp (-U y / D)) (𝒩 * (exp (-U x / D) * (-U' x / D))) x :=
    ((hU.neg.div_const D).exp).const_mul 𝒩
  have := hp.div hs (by positivity)
  convert this using 1
  have := exp_pos (-U x / D)
  field_simp
  ring

/-- **(9.2.6)**, exact: `∫_a^{x₀} (U'p + Dp')/p_s = D[p(x₀)/p_s(x₀) - p(a)/p_s(a)]`. -/
theorem kramers_integrated {U U' p p' : ℝ → ℝ} {D 𝒩 : ℝ} (hD : 0 < D) (h𝒩 : 0 < 𝒩)
    (hU : ∀ x, HasDerivAt U (U' x) x) (hp : ∀ x, HasDerivAt p (p' x) x)
    (hcont : Continuous fun x => (U' x * p x + D * p' x) / (𝒩 * exp (-U x / D))) (a x₀ : ℝ) :
    ∫ x in a..x₀, (U' x * p x + D * p' x) / (𝒩 * exp (-U x / D))
      = D * (p x₀ / (𝒩 * exp (-U x₀ / D)) - p a / (𝒩 * exp (-U a / D))) := by
  have hd : ∀ x ∈ uIcc a x₀, HasDerivAt (fun y => D * (p y / (𝒩 * exp (-U y / D))))
      ((U' x * p x + D * p' x) / (𝒩 * exp (-U x / D))) x := by
    intro x _
    refine ((flux_identity hD h𝒩 (hU x) (hp x)).const_mul D).congr_deriv ?_
    have := exp_pos (-U x / D)
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable a x₀)]
  ring

/-! ### (9.2.7)–(9.2.18): the three relaxation equations -/

/-- **(9.2.7) ⇒ (9.2.8).**  Under Kramers' ansatz, expressed as the named hypothesis that
`∫_a^{x₀} M/p_s = N_a κ(x₀)` with `p(a)/p_s(a) = N_a/n_a` and `p(x₀)/p_s(x₀) = N₀/n₀`, the exact
identity (9.2.6) (whose time derivative gives `d_t ∫ M/p_s`) becomes
`κ Ṅ_a = D[N₀/n₀ - N_a/n_a]`. -/
theorem kramers_ansatz {Iint NaDot κ D N₀ n₀ Na na pa psa px psx : ℝ}
    (h96 : Iint = D * (px / psx - pa / psa)) (hans : Iint = κ * NaDot)
    (ha : pa / psa = Na / na) (hx : px / psx = N₀ / n₀) :
    κ * NaDot = D * (N₀ / n₀ - Na / na) := by
  rw [← hans, h96, ha, hx]

/-- **(9.2.13), corrected.**  If `κṄ_a = D[N₀/n₀ - N_a/n_a]`, `μṄ_c = D[N₀/n₀ - N_c/n_c]` and
`Ṅ_a = -Ṅ_c`, then `N₀ = n₀[μN_a/n_a + κN_c/n_c]/(κ + μ)`. -/
theorem barrier_population {κ μ D N₀ n₀ Na Nc na nc NaDot : ℝ} (hκ : 0 < κ) (hμ : 0 < μ)
    (hD : 0 < D) (hn₀ : 0 < n₀)
    (ha : κ * NaDot = D * (N₀ / n₀ - Na / na)) (hc : μ * (-NaDot) = D * (N₀ / n₀ - Nc / nc)) :
    N₀ = n₀ * (μ * (Na / na) + κ * (Nc / nc)) / (κ + μ) := by
  have h : D * (μ * (N₀ / n₀ - Na / na) + κ * (N₀ / n₀ - Nc / nc)) = 0 := by
    have : μ * (κ * NaDot) + κ * (μ * (-NaDot)) = 0 := by ring
    rw [ha, hc] at this; linarith
  have h2 : μ * (N₀ / n₀ - Na / na) + κ * (N₀ / n₀ - Nc / nc) = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact h
  have h3 : N₀ / n₀ * (κ + μ) = μ * (Na / na) + κ * (Nc / nc) := by linarith
  rw [eq_div_iff (by positivity)]
  calc N₀ * (κ + μ) = n₀ * (N₀ / n₀ * (κ + μ)) := by field_simp
    _ = n₀ * (μ * (Na / na) + κ * (Nc / nc)) := by rw [h3]

/-- **Erratum (9.2.13).**  The printed `N₀ = n₀[μN_a + κN_c]/(κ + μ)` is not a consequence of
(9.2.8): with `κ = μ = D = n₀ = 1`, `n_a = 1/4`, `n_c = 3/4`, `N_a = N_c = 1/2` the equations
(9.2.8) force `N₀ = 4/3`, not `1/2`. -/
theorem barrier_population_printed_wrong :
    (1 : ℝ) * ((1 : ℝ) * (1 / 2 / (1 / 4)) + 1 * (1 / 2 / (3 / 4))) / (1 + 1) = 4 / 3 ∧
      (1 : ℝ) * (1 * (1 / 2) + 1 * (1 / 2)) / (1 + 1) = 1 / 2 := by
  norm_num

/-- **(9.2.14), corrected.**  The intermediate-state equation
`Ṅ₀ = D{N_a/(n_aκ) + N_c/(n_cμ) - (N₀/n₀)(κ⁻¹ + μ⁻¹)}` has, as its adiabatic (`Ṅ₀ = 0`)
solution, exactly (9.2.13). -/
theorem threeState_stationary {κ μ D N₀ n₀ Na Nc na nc : ℝ} (hκ : 0 < κ) (hμ : 0 < μ)
    (hD : 0 < D) (hn₀ : 0 < n₀) (hna : na ≠ 0) (hnc : nc ≠ 0) :
    D * (Na / (na * κ) + Nc / (nc * μ) - N₀ / n₀ * (κ⁻¹ + μ⁻¹)) = 0 ↔
      N₀ = n₀ * (μ * (Na / na) + κ * (Nc / nc)) / (κ + μ) := by
  constructor
  · intro h
    have h2 : Na / (na * κ) + Nc / (nc * μ) - N₀ / n₀ * (κ⁻¹ + μ⁻¹) = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact h
    field_simp at h2 ⊢
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **(9.2.16)–(9.2.18), corrected sign.**  Eliminating `N₀` from (9.2.8):
`Ṅ_a = -r_a N_a + r_c N_c` with `r_a = D/(n_a I)`, `r_c = D/(n_c I)`, `I = κ + μ = ∫_a^c p_s⁻¹`,
and (for `n_a + n_c = 1`) `r_a + r_c = D/(n_a n_c I)`. -/
theorem relaxation_rates {κ μ D N₀ n₀ Na Nc na nc NaDot : ℝ} (hκ : 0 < κ) (hμ : 0 < μ)
    (hD : 0 < D) (hn₀ : 0 < n₀) (hna : 0 < na) (hnc : 0 < nc)
    (ha : κ * NaDot = D * (N₀ / n₀ - Na / na)) (hc : μ * (-NaDot) = D * (N₀ / n₀ - Nc / nc)) :
    NaDot = -(D / (na * (κ + μ))) * Na + D / (nc * (κ + μ)) * Nc ∧
      (na + nc = 1 → D / (na * (κ + μ)) + D / (nc * (κ + μ)) = D / (na * nc * (κ + μ))) := by
  have hN₀ := barrier_population hκ hμ hD hn₀ ha hc
  refine ⟨?_, fun hsum => ?_⟩
  · rw [hN₀] at ha
    have hκ' := hκ.ne'
    field_simp at ha ⊢
    nlinarith [ha]
  · field_simp
    rw [← hsum]; ring

/-- **(9.2.19)–(9.2.20).**  The decay law `N_a(t) = N_a(0) e^{-Dt/(n_aκ)}` has mean lifetime
`∫₀^∞ e^{-Dt/(n_aκ)} dt = n_a κ/D`. -/
theorem escape_time {D na κ : ℝ} (hD : 0 < D) (hna : 0 < na) (hκ : 0 < κ) :
    ∫ t in Ioi (0 : ℝ), exp (-(D / (na * κ)) * t) = na * κ / D := by
  have hl : 0 < D / (na * κ) := by positivity
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, exp_zero]
  field_simp

/-! ### §9.2.2: reversible denaturation of chymotrypsinogen -/

/-- **(9.2.30)–(9.2.31), exact for a locally quadratic `U₀`.**  If `U₀(x) = U₀(a) + k/2 (x-a)²`
near `a` (`k = U₀''(a) ≠ 0`), then `U = U₀ + xδp` is stationary at `a + βδp`, `β = -1/k`, with
value `U₀(a) + aδp + ½βδp²`.  (The same computation applies at `b`, with `k = U₀''(b) < 0` and
`β_b = -1/U₀''(b) > 0`, and at `c`.) -/
theorem chymo_extremum {U₀a a k δp : ℝ} (hk : k ≠ 0) :
    let U := fun x => U₀a + k / 2 * (x - a) ^ 2 + x * δp
    let β := -1 / k
    HasDerivAt U 0 (a + β * δp) ∧ U (a + β * δp) = U₀a + a * δp + 1 / 2 * β * δp ^ 2 := by
  intro U β
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun x : ℝ => U₀a + k / 2 * (x - a) ^ 2 + x * δp)
        (k / 2 * (2 * (a + β * δp - a)) + δp) (a + β * δp) := by
      have := (((hasDerivAt_id (a + β * δp)).sub_const a).pow 2).const_mul (k / 2)
      have := (this.const_add U₀a).add ((hasDerivAt_id (a + β * δp)).mul_const δp)
      convert this using 1; simp
    convert h1 using 1
    simp only [β]; field_simp; ring
  · simp only [U, β]; field_simp; ring

/-- **(9.2.32)** (printed with the label (9.3.32)).  With `U(x) = U₀(x) + xδp`, quadratic
extrema (9.2.31) and the balance condition (9.2.29) `√k_a e^{U₀(a)/kT} = √k_c e^{U₀(c)/kT}`,
the ratio (9.2.23) `√(k_c/k_a) e^{[U(c) - U(a)]/kT}` equals
`exp[-(a - c)δp/kT - (β_a - β_c)δp²/(2kT)]`. -/
theorem chymo_population_ratio {ka kc U₀a U₀c a c δp kT : ℝ} (hka : 0 < ka) (hkc : 0 < kc)
    (hkT : 0 < kT) (hbal : √ka * exp (U₀a / kT) = √kc * exp (U₀c / kT)) :
    √(kc / ka) * exp (((U₀c + c * δp + 1 / 2 * (-1 / kc) * δp ^ 2)
        - (U₀a + a * δp + 1 / 2 * (-1 / ka) * δp ^ 2)) / kT)
      = exp (-(a - c) / kT * δp - ((-1 / ka) - (-1 / kc)) / (2 * kT) * δp ^ 2) := by
  have hsa : 0 < √ka := sqrt_pos.mpr hka
  have hsc : 0 < √kc := sqrt_pos.mpr hkc
  have hratio : √(kc / ka) = exp (U₀a / kT) / exp (U₀c / kT) := by
    rw [sqrt_div' _ hka.le]
    have := exp_pos (U₀c / kT)
    rw [div_eq_div_iff hsa.ne' this.ne']
    linarith
  rw [hratio, div_mul_eq_mul_div, ← exp_add, ← exp_sub]
  congr 1
  field_simp
  ring

/-- The factor `H` of (9.2.25) for the chymotrypsinogen model (9.2.26), whose effective
potential is `U/γ` and effective diffusion `kT/γ`: `H = γ k_b^{-1/2}(k_a k_c)^{-1/4}
e^{[2U(b) - U(a) - U(c)]/(2kT)}` (curvatures `k = |U''|`). -/
def chymoH (γ ka kb kc Ua Ub Uc kT : ℝ) : ℝ :=
  Hfac (ka / γ) (kb / γ) (kc / γ) (Ua / γ) (Ub / γ) (Uc / γ) (kT / γ)

lemma chymoH_eq {γ ka kb kc Ua Ub Uc kT : ℝ} (hγ : 0 < γ) (hka : 0 < ka) (hkb : 0 < kb)
    (hkc : 0 < kc) (hkT : 0 < kT) :
    chymoH γ ka kb kc Ua Ub Uc kT
      = γ * (√kb)⁻¹ * (√(√(ka * kc)))⁻¹ * exp ((2 * Ub - Ua - Uc) / (2 * kT)) := by
  simp only [chymoH, Hfac]
  have e1 : √(kb / γ) = √kb / √γ := sqrt_div' _ hγ.le
  have e2 : √(√(ka / γ * (kc / γ))) = √(√(ka * kc)) / √γ := by
    rw [show ka / γ * (kc / γ) = ka * kc / γ ^ 2 by ring, sqrt_div' _ (by positivity),
      sqrt_sq hγ.le, sqrt_div' _ hγ.le]
  rw [e1, e2]
  have hsγ : 0 < √γ := sqrt_pos.mpr hγ
  have h1 : 0 < √kb := sqrt_pos.mpr hkb
  have h2 : 0 < √(√(ka * kc)) := sqrt_pos.mpr (sqrt_pos.mpr (mul_pos hka hkc))
  have h3 : (2 * (Ub / γ) - Ua / γ - Uc / γ) / (2 * (kT / γ)) = (2 * Ub - Ua - Uc) / (2 * kT) := by
    field_simp
  rw [h3]
  field_simp
  rw [sq_sqrt hγ.le]

/-- **(9.2.33), corrected.**  With the extrema shifted by (9.2.31) and curvatures unchanged
(locally quadratic `U₀`), `H(δp) = H(0) exp[-(a + c - 2b)δp/(2kT) + (β_b - ½β_a - ½β_c)δp²/(2kT)]`,
and `H(0) = γ β_b^{1/2}(β_aβ_c)^{1/4} e^{[2U₀(b) - U₀(a) - U₀(c)]/(2kT)}` (`β_a = -1/k_a`,
`β_c = -1/k_c`, `β_b = 1/k_b`). -/
theorem chymo_H_ratio {γ ka kb kc U₀a U₀b U₀c a b c δp kT : ℝ} (hγ : 0 < γ) (hka : 0 < ka)
    (hkb : 0 < kb) (hkc : 0 < kc) (hkT : 0 < kT) :
    chymoH γ ka kb kc (U₀a + a * δp + 1 / 2 * (-1 / ka) * δp ^ 2)
        (U₀b + b * δp + 1 / 2 * (1 / kb) * δp ^ 2) (U₀c + c * δp + 1 / 2 * (-1 / kc) * δp ^ 2) kT
      = chymoH γ ka kb kc U₀a U₀b U₀c kT *
        exp (-(a + c - 2 * b) / (2 * kT) * δp
          + (1 / kb - 1 / 2 * (-1 / ka) - 1 / 2 * (-1 / kc)) / (2 * kT) * δp ^ 2) := by
  rw [chymoH_eq hγ hka hkb hkc hkT, chymoH_eq hγ hka hkb hkc hkT, mul_assoc _ (exp _), ← exp_add]
  congr 2
  field_simp
  ring

/-- **(9.2.33), first line, corrected.**  At `δp = 0` (`n_a = n_c = ½`) the relaxation time
(9.2.24) is `τ_r(0) = 2πH(0)·½ = πH(0)`, `H(0) = γ β_b^{1/2}(β_aβ_c)^{1/4}e^{[2U(b)-U(a)-U(c)]/2kT}`
in terms of `β_b = 1/k_b`, `β_aβ_c = 1/(k_ak_c)`. -/
theorem chymo_relaxTime {γ ka kb kc Ua Ub Uc kT : ℝ} (hγ : 0 < γ) (hka : 0 < ka) (hkb : 0 < kb)
    (hkc : 0 < kc) (hkT : 0 < kT) :
    2 * π * chymoH γ ka kb kc Ua Ub Uc kT * √((1 / 2) * (1 / 2))
      = π * γ * √(1 / kb) * √(√(1 / (ka * kc))) * exp ((2 * Ub - Ua - Uc) / (2 * kT)) := by
  rw [chymoH_eq hγ hka hkb hkc hkT, show (1 / 2 : ℝ) * (1 / 2) = (1 / 2) ^ 2 by ring,
    sqrt_sq (by norm_num), sqrt_div' _ hkb.le, sqrt_div' _ (by positivity),
    sqrt_div' _ (by positivity)]
  simp only [sqrt_one]
  ring

/-! ### (9.2.46)–(9.2.49): the discrete ansatz -/

/-- **(9.2.46) ⇒ the corrected (9.2.49).**  If `P(y) = P_s(y) N_a/n_a` for `y < b` with
`n_a = Σ_{y<b} P_s(y)`, then for `z ≤ b`, `M(z) = Σ_{y<z} P(y) = N_a[1 - ψ(z)]` with
`ψ(z) = n_a⁻¹ Σ_{y=z}^{b-1} P_s(y)` (upper limit `b - 1`, not `b`). -/
theorem discrete_ansatz_M {P Ps : ℕ → ℝ} {Na na : ℝ} {b : ℕ} (hna : na = ∑ y ∈ Finset.range b, Ps y)
    (hna0 : na ≠ 0) (hP : ∀ y < b, P y = Ps y * Na / na) {z : ℕ} (hz : z ≤ b) :
    ∑ y ∈ Finset.range z, P y = Na * (1 - (∑ y ∈ Finset.Ico z b, Ps y) / na) := by
  have h1 : ∑ y ∈ Finset.range z, P y = ∑ y ∈ Finset.range z, Ps y * Na / na :=
    Finset.sum_congr rfl fun y hy => hP y (lt_of_lt_of_le (Finset.mem_range.mp hy) hz)
  have h2 : ∑ y ∈ Finset.Ico z b, Ps y = na - ∑ y ∈ Finset.range z, Ps y := by
    rw [Finset.sum_Ico_eq_sub _ hz, hna]
  rw [h1, h2, ← Finset.sum_div, ← Finset.sum_mul]
  field_simp
  ring

end Gardiner.Escape

namespace Gardiner.Escape

/-- **Instances**: the mean escape time (9.2.20) for `D = 1`, `n_a = ½`, `κ = 3` is `3/2`; for
`κ = 1`, `μ = 2`, `D = n₀ = 1`, `n_a = ¼`, `n_c = ¾`, `N_a = N_c = ½`, the relaxation equations
(9.2.8) force `N₀ = 14/9` (9.2.13 corrected) and `Ṅ_a = -4/9 = -r_aN_a + r_cN_c` (9.2.16). -/
theorem populations_instance :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 / (1 / 2 * 3)) * t) = 1 / 2 * 3 / 1 ∧
    (14 / 9 : ℝ) = 1 * (2 * (1 / 2 / (1 / 4)) + 1 * (1 / 2 / (3 / 4))) / (1 + 2) ∧
    (-4 / 9 : ℝ) = -(1 / (1 / 4 * (1 + 2))) * (1 / 2) + 1 / (3 / 4 * (1 + 2)) * (1 / 2) := by
  have ha : (1 : ℝ) * (-4 / 9) = 1 * (14 / 9 / 1 - 1 / 2 / (1 / 4)) := by norm_num
  have hc : (2 : ℝ) * (-(-4 / 9)) = 1 * (14 / 9 / 1 - 1 / 2 / (3 / 4)) := by norm_num
  refine ⟨escape_time one_pos (by norm_num) (by norm_num),
    barrier_population one_pos two_pos one_pos one_pos ha hc,
    (relaxation_rates one_pos two_pos one_pos one_pos (by norm_num) (by norm_num) ha hc).1⟩

end Gardiner.Escape
