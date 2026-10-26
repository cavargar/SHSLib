/-
# Quantitative adiabatic elimination in the Laplace domain

Gardiner, *Handbook of Stochastic Methods*, (6.4.47)–(6.4.52), (6.5.25)–(6.5.28),
(6.5.67)–(6.5.70) and (6.6.23)–(6.6.26): the limits "`γ → ∞` at fixed `s`" of the exactly
eliminated equations, **with explicit error terms**.

The text inverts `s - γL₁ - (1 - P)L₂` formally and expands.  Here no inverse is assumed: the
transformed equations themselves are used as hypotheses, together with

* a reduced inverse `S` of `L₁` on the range of `1 - P` (`S L₁ w = w` whenever `Pw = 0`; this is
  the `L₁⁻¹` of (6.4.52)–(6.4.53) and `-∫₀^∞ e^{L₁t}dt (1 - P)` of (6.5.33));
* bounds `‖S x‖ ≤ c ‖x‖` etc. on the operators that occur.

The boundedness of `L₂` is exactly the assumption the text makes and later flags
(§6.4.5 c: "the assumption that the operator `∂/∂y` is bounded"); it holds e.g. for a
Fourier mode of a translation-invariant problem with a finite-state fast process, see
`SHSLib.Gardiner.Adiabatic.Telegraph`.

* `Gardiner.Adiabatic.kramers_laplace_bound`: from (6.4.47) with `w(0) = 0`,
  `‖w̃‖ ≤ 2‖SL₂ṽ‖/|γ|` and `‖sṽ - v(0) - γ⁻¹(-PL₂SL₂)ṽ‖ ≤ 2c_{PL}K‖SL₂ṽ‖/|γ|²`, i.e. (6.4.52)
  holds with an `O(γ⁻²)` error while the retained term is `O(γ⁻¹)`.
* `Gardiner.Adiabatic.threeScale_laplace_bound`: from the general equations (6.5.67)–(6.5.68)
  (with `L₃` not commuting with `P`, as in §6.5.4, §6.6.3, §6.6.4),
  `‖sṽ - v(0) - (PL₃ - PL₂SL₂)ṽ‖ ≤ C/|γ|`, which is (6.5.70) with an explicit constant.
* `Gardiner.Adiabatic.commuting_laplace_bound`: the special case `PL₃ = L₃P` of (6.5.25)–(6.5.28)
  and (6.6.23)–(6.6.26).
-/
import Mathlib

noncomputable section

namespace Gardiner.Adiabatic

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **(6.4.47) ⟹ (6.4.52) with an explicit `O(γ⁻²)` error.**  Suppose `ṽ, w̃` satisfy the
Laplace-transformed split equations of the Kramers-type problem `∂ₜp = (γL₁ + L₂)p` with
`w(0) = 0`:
`sṽ = PL₂w̃ + v(0)`, `sw̃ = γL₁w̃ + (1 - P)L₂w̃ + L₂ṽ`, `Pw̃ = 0`.
Let `S` invert `L₁` on the range of `1 - P` and `‖Sx‖ ≤ c_S‖x‖`, `‖S(1 - P)L₂x‖ ≤ c_Q‖x‖`,
`‖PL₂x‖ ≤ c_P‖x‖`.  If `|γ| ≥ 2K`, `K = |s|c_S + c_Q`, then
`‖w̃‖ ≤ 2‖SL₂ṽ‖/|γ|` and
`‖(sṽ - v(0)) - γ⁻¹(-PL₂SL₂ṽ)‖ ≤ 2c_P K ‖SL₂ṽ‖/|γ|²`. -/
theorem kramers_laplace_bound (P L₁ L₂ S : E →ₗ[𝕜] E) (γ s : 𝕜) (v w v0 : E)
    (cS cQ cP : ℝ) (hcS : 0 ≤ cS) (hcQ : 0 ≤ cQ) (hcP : 0 ≤ cP)
    (hSL1 : ∀ x, P x = 0 → S (L₁ x) = x) (hPw : P w = 0)
    (hv : s • v = P (L₂ w) + v0)
    (hw : s • w = γ • L₁ w + (L₂ w - P (L₂ w)) + L₂ v)
    (hS : ∀ x, ‖S x‖ ≤ cS * ‖x‖) (hSQ : ∀ x, ‖S (L₂ x - P (L₂ x))‖ ≤ cQ * ‖x‖)
    (hPL : ∀ x, ‖P (L₂ x)‖ ≤ cP * ‖x‖)
    (hγ0 : γ ≠ 0) (hγ : 2 * (‖s‖ * cS + cQ) ≤ ‖γ‖) :
    ‖w‖ ≤ 2 * ‖S (L₂ v)‖ / ‖γ‖ ∧
    ‖(s • v - v0) - γ⁻¹ • (-P (L₂ (S (L₂ v))))‖
      ≤ 2 * cP * (‖s‖ * cS + cQ) * ‖S (L₂ v)‖ / ‖γ‖ ^ 2 := by
  set K := ‖s‖ * cS + cQ with hK
  set a := ‖S (L₂ v)‖
  have hγpos : 0 < ‖γ‖ := norm_pos_iff.2 hγ0
  have hK0 : 0 ≤ K := by positivity
  -- apply `S` to the `w`-equation
  have hSw : γ • w = s • S w - S (L₂ w - P (L₂ w)) - S (L₂ v) := by
    have := congrArg S hw
    rw [S.map_smul, S.map_add, S.map_add, S.map_smul, hSL1 w hPw] at this
    rw [this]; abel
  have hnorm : ‖γ‖ * ‖w‖ ≤ K * ‖w‖ + a := by
    rw [← norm_smul, hSw]
    calc ‖s • S w - S (L₂ w - P (L₂ w)) - S (L₂ v)‖
        ≤ ‖s • S w‖ + ‖S (L₂ w - P (L₂ w))‖ + ‖S (L₂ v)‖ := norm_sub_le_of_le
          (norm_sub_le _ _) le_rfl
      _ ≤ ‖s‖ * (cS * ‖w‖) + cQ * ‖w‖ + a := by
          rw [norm_smul]; gcongr
          · exact hS w
          · exact hSQ w
      _ = K * ‖w‖ + a := by rw [hK]; ring
  have hw_le : ‖w‖ ≤ 2 * a / ‖γ‖ := by
    rw [le_div_iff₀ hγpos]
    nlinarith [norm_nonneg w]
  refine ⟨hw_le, ?_⟩
  -- the corrected `w̃`
  have hcorr : w + γ⁻¹ • S (L₂ v) = γ⁻¹ • (s • S w - S (L₂ w - P (L₂ w))) := by
    calc w + γ⁻¹ • S (L₂ v) = γ⁻¹ • (γ • w) + γ⁻¹ • S (L₂ v) := by
          rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]
      _ = _ := by rw [hSw]; simp only [smul_sub]; abel
  have hcorr_le : ‖w + γ⁻¹ • S (L₂ v)‖ ≤ K * (2 * a / ‖γ‖) / ‖γ‖ := by
    rw [hcorr, norm_smul, norm_inv, inv_mul_eq_div]
    gcongr
    calc ‖s • S w - S (L₂ w - P (L₂ w))‖ ≤ ‖s • S w‖ + ‖S (L₂ w - P (L₂ w))‖ := norm_sub_le _ _
      _ ≤ ‖s‖ * (cS * ‖w‖) + cQ * ‖w‖ := by rw [norm_smul]; gcongr; exacts [hS w, hSQ w]
      _ = K * ‖w‖ := by rw [hK]; ring
      _ ≤ K * (2 * a / ‖γ‖) := by gcongr
  have hid : (s • v - v0) - γ⁻¹ • (-P (L₂ (S (L₂ v)))) = P (L₂ (w + γ⁻¹ • S (L₂ v))) := by
    rw [hv, map_add, map_add, map_smul, map_smul]; simp only [smul_neg, sub_neg_eq_add]; abel
  rw [hid]
  calc ‖P (L₂ (w + γ⁻¹ • S (L₂ v)))‖ ≤ cP * ‖w + γ⁻¹ • S (L₂ v)‖ := hPL _
    _ ≤ cP * (K * (2 * a / ‖γ‖) / ‖γ‖) := by gcongr
    _ = 2 * cP * K * a / ‖γ‖ ^ 2 := by field_simp

/-- **(6.5.67)–(6.5.70) with an explicit `O(γ⁻¹)` error.**  The general three-scale problem
`∂ₜp = (γ²L₁ + γL₂ + L₃)p` with `L₃` not necessarily commuting with `P` (§6.5.4, §6.6.3–§6.6.4).
Write `Qx = x - Px`.  Suppose `w(0) = 0`, `Pṽ = ṽ`, `Pw̃ = 0` and
`sṽ = PL₃ṽ + γPL₂w̃ + PL₃w̃ + v(0)`,
`sw̃ = γ²L₁w̃ + γQL₂w̃ + QL₃w̃ + γL₂ṽ + QL₃ṽ`.
With `S` inverting `L₁` on the range of `Q` and the operator bounds below, for `|γ| ≥ 1` and
`|γ| ≥ 2K`, `K = |s|c_S + c₃ + c₂`,
`‖sṽ - v(0) - (PL₃ - PL₂SL₂)ṽ‖ ≤ [d₂(2Ka + c₃‖ṽ‖) + 2d₃a]/|γ|`, `a = ‖SL₂ṽ‖ + c₃‖ṽ‖`. -/
theorem threeScale_laplace_bound (P L₁ L₂ L₃ S : E →ₗ[𝕜] E) (γ s : 𝕜) (v w v0 : E)
    (cS c₂ c₃ d₂ d₃ : ℝ) (hcS : 0 ≤ cS) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hd₂ : 0 ≤ d₂)
    (hd₃ : 0 ≤ d₃)
    (hSL1 : ∀ x, P x = 0 → S (L₁ x) = x) (hPw : P w = 0)
    (hv : s • v = P (L₃ v) + γ • P (L₂ w) + P (L₃ w) + v0)
    (hw : s • w = γ ^ 2 • L₁ w + γ • (L₂ w - P (L₂ w)) + (L₃ w - P (L₃ w)) + γ • L₂ v
      + (L₃ v - P (L₃ v)))
    (hS : ∀ x, ‖S x‖ ≤ cS * ‖x‖) (hS2 : ∀ x, ‖S (L₂ x - P (L₂ x))‖ ≤ c₂ * ‖x‖)
    (hS3 : ∀ x, ‖S (L₃ x - P (L₃ x))‖ ≤ c₃ * ‖x‖)
    (hP2 : ∀ x, ‖P (L₂ x)‖ ≤ d₂ * ‖x‖) (hP3 : ‖P (L₃ w)‖ ≤ d₃ * ‖w‖)
    (hγ1 : 1 ≤ ‖γ‖) (hγ : 2 * (‖s‖ * cS + c₃ + c₂) ≤ ‖γ‖) :
    ‖s • v - v0 - (P (L₃ v) - P (L₂ (S (L₂ v))))‖
      ≤ (d₂ * (2 * (‖s‖ * cS + c₃ + c₂) * (‖S (L₂ v)‖ + c₃ * ‖v‖) + c₃ * ‖v‖)
          + 2 * d₃ * (‖S (L₂ v)‖ + c₃ * ‖v‖)) / ‖γ‖ := by
  set K := ‖s‖ * cS + c₃ + c₂ with hK
  set a := ‖S (L₂ v)‖ + c₃ * ‖v‖ with ha
  have hγpos : 0 < ‖γ‖ := by linarith
  have hγ0 : γ ≠ 0 := norm_pos_iff.1 hγpos
  have hK0 : 0 ≤ K := by positivity
  have ha0 : 0 ≤ a := by positivity
  set R := s • S w - S (L₃ w - P (L₃ w)) - S (L₃ v - P (L₃ v)) with hR
  have hRle : ‖R‖ ≤ (‖s‖ * cS + c₃) * ‖w‖ + c₃ * ‖v‖ := by
    calc ‖R‖ ≤ ‖s • S w‖ + ‖S (L₃ w - P (L₃ w))‖ + ‖S (L₃ v - P (L₃ v))‖ :=
          norm_sub_le_of_le (norm_sub_le _ _) le_rfl
      _ ≤ ‖s‖ * (cS * ‖w‖) + c₃ * ‖w‖ + c₃ * ‖v‖ := by
          rw [norm_smul]; gcongr; exacts [hS w, hS3 w, hS3 v]
      _ = _ := by ring
  -- apply `S` to the `w`-equation:  `γ w + S L₂ ṽ = γ⁻¹ R - S Q L₂ w̃`
  have hSw : γ • w + S (L₂ v) = γ⁻¹ • R - S (L₂ w - P (L₂ w)) := by
    have := congrArg S hw
    simp only [S.map_smul, S.map_add, hSL1 w hPw] at this
    have h2 : γ ^ 2 • w = γ • (γ • w) := by rw [smul_smul, sq]
    rw [h2] at this
    have h3 : γ • (γ • w + S (L₂ v)) = γ • (γ⁻¹ • R - S (L₂ w - P (L₂ w))) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hγ0, one_smul, hR, smul_add]
      rw [this]; abel
    exact smul_right_injective E hγ0 h3
  have hBle : ‖γ • w + S (L₂ v)‖ ≤ ‖γ‖⁻¹ * ((‖s‖ * cS + c₃) * ‖w‖ + c₃ * ‖v‖) + c₂ * ‖w‖ := by
    rw [hSw]
    calc ‖γ⁻¹ • R - S (L₂ w - P (L₂ w))‖ ≤ ‖γ⁻¹ • R‖ + ‖S (L₂ w - P (L₂ w))‖ := norm_sub_le _ _
      _ ≤ ‖γ‖⁻¹ * ((‖s‖ * cS + c₃) * ‖w‖ + c₃ * ‖v‖) + c₂ * ‖w‖ := by
          rw [norm_smul, norm_inv]; gcongr; exact hS2 w
  -- a priori bound on `w̃`
  have hinv : ‖γ‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hγ1
  have hw_le : ‖w‖ ≤ 2 * a / ‖γ‖ := by
    have h1 : ‖γ‖ * ‖w‖ ≤ ‖γ • w + S (L₂ v)‖ + ‖S (L₂ v)‖ := by
      rw [← norm_smul]
      calc ‖γ • w‖ = ‖(γ • w + S (L₂ v)) - S (L₂ v)‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖γ‖ * ‖w‖ ≤ K * ‖w‖ + a := by
      have e : ‖γ‖⁻¹ * ((‖s‖ * cS + c₃) * ‖w‖ + c₃ * ‖v‖) ≤ (‖s‖ * cS + c₃) * ‖w‖ + c₃ * ‖v‖ :=
        mul_le_of_le_one_left (by positivity) hinv
      nlinarith [norm_nonneg w]
    rw [le_div_iff₀ hγpos]
    nlinarith [norm_nonneg w]
  -- the error
  have hid : s • v - v0 - (P (L₃ v) - P (L₂ (S (L₂ v))))
      = P (L₂ (γ • w + S (L₂ v))) + P (L₃ w) := by
    rw [hv, map_add, map_add, map_smul, map_smul]; abel
  rw [hid]
  have hBle' : ‖γ • w + S (L₂ v)‖ ≤ (2 * K * a + c₃ * ‖v‖) / ‖γ‖ := by
    refine hBle.trans ?_
    have hw' : ‖w‖ ≤ 2 * a := hw_le.trans (div_le_self (by positivity) hγ1)
    rw [le_div_iff₀ hγpos]
    have e1 : ‖γ‖⁻¹ * ((‖s‖ * cS + c₃) * ‖w‖ + c₃ * ‖v‖) * ‖γ‖
        = (‖s‖ * cS + c₃) * ‖w‖ + c₃ * ‖v‖ := by field_simp
    have e2 : c₂ * ‖w‖ * ‖γ‖ ≤ c₂ * (2 * a) := by
      have := mul_le_mul_of_nonneg_left (le_div_iff₀ hγpos |>.1 hw_le) hc₂
      linarith
    rw [add_mul, e1]
    have e3 : (‖s‖ * cS + c₃) * ‖w‖ ≤ (‖s‖ * cS + c₃) * (2 * a) := by gcongr
    nlinarith
  calc ‖P (L₂ (γ • w + S (L₂ v))) + P (L₃ w)‖
      ≤ d₂ * ‖γ • w + S (L₂ v)‖ + d₃ * ‖w‖ := norm_add_le_of_le (hP2 _) hP3
    _ ≤ d₂ * ((2 * K * a + c₃ * ‖v‖) / ‖γ‖) + d₃ * (2 * a / ‖γ‖) := by gcongr
    _ = (d₂ * (2 * K * a + c₃ * ‖v‖) + 2 * d₃ * a) / ‖γ‖ := by field_simp
    _ = _ := by rw [hK, ha]

/-- **(6.5.25)–(6.5.28), (6.6.23)–(6.6.26)**: the case `PL₃ = L₃P`.  Then `PL₃w̃ = 0` and
`(1 - P)L₃ṽ = 0`, the equations reduce to `sṽ = γPL₂w̃ + L₃ṽ + v(0)`,
`sw̃ = γ²L₁w̃ + γ(1 - P)L₂w̃ + L₃w̃ + γL₂ṽ`, and
`‖sṽ - v(0) - (L₃ - PL₂SL₂)ṽ‖ ≤ d₂(2Ka + c₃‖ṽ‖)/|γ|`. -/
theorem commuting_laplace_bound (P L₁ L₂ L₃ S : E →ₗ[𝕜] E) (γ s : 𝕜) (v w v0 : E)
    (cS c₂ c₃ d₂ : ℝ) (hcS : 0 ≤ cS) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hd₂ : 0 ≤ d₂)
    (hcomm : ∀ x, P (L₃ x) = L₃ (P x))
    (hSL1 : ∀ x, P x = 0 → S (L₁ x) = x) (hPv : P v = v) (hPw : P w = 0)
    (hv : s • v = L₃ v + γ • P (L₂ w) + v0)
    (hw : s • w = γ ^ 2 • L₁ w + γ • (L₂ w - P (L₂ w)) + L₃ w + γ • L₂ v)
    (hS : ∀ x, ‖S x‖ ≤ cS * ‖x‖) (hS2 : ∀ x, ‖S (L₂ x - P (L₂ x))‖ ≤ c₂ * ‖x‖)
    (hS3 : ∀ x, ‖S (L₃ x - P (L₃ x))‖ ≤ c₃ * ‖x‖)
    (hP2 : ∀ x, ‖P (L₂ x)‖ ≤ d₂ * ‖x‖)
    (hγ1 : 1 ≤ ‖γ‖) (hγ : 2 * (‖s‖ * cS + c₃ + c₂) ≤ ‖γ‖) :
    ‖s • v - v0 - (L₃ v - P (L₂ (S (L₂ v))))‖
      ≤ d₂ * (2 * (‖s‖ * cS + c₃ + c₂) * (‖S (L₂ v)‖ + c₃ * ‖v‖) + c₃ * ‖v‖) / ‖γ‖ := by
  have hL3v : P (L₃ v) = L₃ v := by rw [hcomm, hPv]
  have hL3w : P (L₃ w) = 0 := by rw [hcomm, hPw, map_zero]
  have hQ3v : L₃ v - P (L₃ v) = 0 := by rw [hL3v, sub_self]
  have h := threeScale_laplace_bound P L₁ L₂ L₃ S γ s v w v0 cS c₂ c₃ d₂ 0 hcS hc₂ hc₃ hd₂
    le_rfl hSL1 hPw (by rw [hv, hL3v, hL3w]; abel)
    (by rw [hw, hL3w, hQ3v, sub_zero, add_zero]) hS hS2 hS3 hP2
    (by rw [hL3w, norm_zero, zero_mul]) hγ1 hγ
  rw [hL3v] at h
  simpa using h

end Gardiner.Adiabatic
