/-
# Projection-operator algebra of adiabatic elimination

Gardiner, *Handbook of Stochastic Methods*, §6.4.1, §6.4.2, §6.4.5, §6.5, §6.5.4, §6.6.1 and
§6.6.3: the purely algebraic part of the projection-operator method.

The operators `L₁, L₂, L₃, P` are elements of an arbitrary ring `R` (in applications
`R = Module.End 𝕜 E` or `E →L[ℝ] E`), acting on an `R`-module `M` (the "vectors" `p, v, w`);
the large parameter `γ` and the Laplace variable `s` are scalars of a field `𝕜` with
`R` a `𝕜`-algebra.  The structural hypotheses of the text are bundled in
`Gardiner.Adiabatic.ProjHyp`: `P² = P` (6.4.26), `PL₁ = L₁P = 0` (6.4.41), `PL₂P = 0` (6.4.36).

* (6.4.42), (6.4.44): `Gardiner.Adiabatic.proj_v_eq`, `Gardiner.Adiabatic.proj_w_eq` (operator
  identities) and their time-domain form `Gardiner.Adiabatic.hasDerivAt_proj_v`,
  `Gardiner.Adiabatic.hasDerivAt_proj_w`.
* (6.4.45)–(6.4.47): the Laplace transform (`Gardiner.Adiabatic.laplace`), the derivative rule
  (6.4.46) (`Gardiner.Adiabatic.laplace_deriv`; the vanishing of the boundary term at infinity is
  a hypothesis) and the transformed equation (`Gardiner.Adiabatic.laplace_v_eq`).
* (6.4.50)–(6.4.51), (6.5.27), (6.5.69), (6.6.25), (6.6.82): the exact elimination of `w̃`
  given an inverse (`Gardiner.Adiabatic.exact_elimination`,
  `Gardiner.Adiabatic.exact_elimination_L3`).
* (6.4.94)–(6.4.101): the long-time expansion to order `γ⁻²` *with an exact remainder*
  (`Gardiner.Adiabatic.resolvent_expansion`, `Gardiner.Adiabatic.longTime_expansion`,
  `Gardiner.Adiabatic.longTime_rearranged`).
* (6.5.18)–(6.5.26), (6.6.22): `PL₃ = L₃P` makes the general equations (6.5.67)–(6.5.68) collapse
  to (6.5.25)–(6.5.26) (`Gardiner.Adiabatic.commuting_L3_v`, `Gardiner.Adiabatic.commuting_L3_w`).
* (6.6.88)–(6.6.105): the commutator manipulations of the second-order corrections
  (`Gardiner.Adiabatic.secondOrder_commutator_form`, `Gardiner.Adiabatic.P_comm_L3_eq_zero`,
  `Gardiner.Adiabatic.secondOrder_reduced`).

The quantitative (normed) versions of the limits `γ → ∞` are in
`SHSLib.Gardiner.Adiabatic.ProjectorBound`; concrete instances are in
`SHSLib.Gardiner.Adiabatic.Telegraph`.
-/
import Mathlib

open MeasureTheory Filter Topology Set

noncomputable section

namespace Gardiner.Adiabatic

/-! ### §6.4.1: projector, null space of `L₁`, and the split equations -/

/-- The structural hypotheses of the projection-operator method: `P² = P` (6.4.26),
`PL₁ = L₁P = 0` (6.4.41) and `PL₂P = 0` (6.4.36). -/
structure ProjHyp {R : Type*} [Ring R] (P L₁ L₂ : R) : Prop where
  idem : P * P = P
  PL1 : P * L₁ = 0
  L1P : L₁ * P = 0
  PL2P : P * L₂ * P = 0

section Ring

variable {R : Type*} [Ring R] {P L₁ L₂ L₃ : R}

lemma ProjHyp.one_sub_idem (h : ProjHyp P L₁ L₂) : (1 - P) * (1 - P) = 1 - P := by
  rw [sub_mul, one_mul, mul_sub, mul_one, h.idem]; abel

lemma ProjHyp.P_one_sub (h : ProjHyp P L₁ L₂) : P * (1 - P) = 0 := by
  rw [mul_sub, mul_one, h.idem, sub_self]

lemma ProjHyp.one_sub_P (h : ProjHyp P L₁ L₂) : (1 - P) * P = 0 := by
  rw [sub_mul, one_mul, h.idem, sub_self]

/-- `(1 - P) L₂ P = L₂ P`, a consequence of `PL₂P = 0` [(6.6.89 ii)]. -/
lemma ProjHyp.one_sub_L2P (h : ProjHyp P L₁ L₂) : (1 - P) * L₂ * P = L₂ * P := by
  rw [sub_mul, sub_mul, one_mul, h.PL2P, sub_zero]

/-- The splitting `p = v + w` of (6.4.39)–(6.4.40). -/
lemma split_vw (P : R) {M : Type*} [AddCommGroup M] [Module R M] (p : M) :
    P • p + (1 - P) • p = p := by
  rw [sub_smul, one_smul]; abel

/-! ### §6.4.2: exact elimination of the irrelevant part -/

/-- **(6.4.50)–(6.4.51)** (with `w(0) = 0`, (6.4.48)): if the transformed equations (6.4.47)
`sṽ = PL₂w̃ + v(0)`, `sw̃ = Kw̃ + L₂ṽ` hold with `K = γL₁ + (1 - P)L₂` and `G` is a left inverse
of `s - K`, then `w̃ = G L₂ ṽ` and `sṽ = PL₂ G L₂ ṽ + v(0)`.  (`s` is written as an element of
`R`, i.e. `s · 1`.) -/
theorem exact_elimination {M : Type*} [AddCommGroup M] [Module R M] (s K G : R) (v w v0 : M)
    (hv : s • v = (P * L₂) • w + v0) (hw : s • w = K • w + L₂ • v)
    (hG : G * (s - K) = 1) :
    w = (G * L₂) • v ∧ s • v = (P * L₂ * G * L₂) • v + v0 := by
  have hw' : w = (G * L₂) • v := by
    have : (s - K) • w = L₂ • v := by rw [sub_smul, hw]; abel
    calc w = (G * (s - K)) • w := by rw [hG, one_smul]
      _ = (G * L₂) • v := by rw [mul_smul, this, mul_smul]
  refine ⟨hw', ?_⟩
  rw [hv, hw', ← mul_smul]
  simp only [mul_assoc]

/-- **(6.5.69), (6.6.82)**: the exact elimination with a third operator `L₃` that need not
commute with `P`.  If `sṽ = PL₃ṽ + Xw̃ + v(0)` and `sw̃ = Kw̃ + Yṽ` and `G(s - K) = 1`, then
`sṽ = (PL₃ + X G Y)ṽ + v(0)`.  The text takes `X = P(γL₂ + L₃)`, `Y = γL₂ + (1 - P)L₃`,
`K = γ²L₁ + γ(1 - P)L₂ + (1 - P)L₃`. -/
theorem exact_elimination_L3 {M : Type*} [AddCommGroup M] [Module R M] (s K G X Y : R)
    (v w v0 : M) (hv : s • v = (P * L₃) • v + X • w + v0) (hw : s • w = K • w + Y • v)
    (hG : G * (s - K) = 1) :
    s • v = (P * L₃ + X * G * Y) • v + v0 := by
  have hw' : w = (G * Y) • v := by
    have : (s - K) • w = Y • v := by rw [sub_smul, hw]; abel
    calc w = (G * (s - K)) • w := by rw [hG, one_smul]
      _ = (G * Y) • v := by rw [mul_smul, this, mul_smul]
  rw [hv, hw']
  simp only [add_smul, mul_smul]

/-- **(6.5.26)**: if `PL₃ = L₃P`, then `(1-P)L₃ = L₃(1-P)`, `(1-P)L₃P = 0` and `PL₃(1-P) = 0`,
so the `L₃`-terms of the general equations (6.5.67)–(6.5.68) reduce to `L₃ṽ` and `L₃w̃`. -/
theorem commuting_L3_w (h : ProjHyp P L₁ L₂) (h3 : P * L₃ = L₃ * P) :
    (1 - P) * L₃ = L₃ * (1 - P) ∧ (1 - P) * L₃ * P = 0 ∧ P * L₃ * (1 - P) = 0 := by
  refine ⟨by rw [sub_mul, mul_sub, one_mul, mul_one, h3], ?_, ?_⟩
  · rw [sub_mul, sub_mul, one_mul, h3, mul_assoc, h.idem, sub_self]
  · rw [mul_sub, mul_one, h3, mul_assoc, h.idem, sub_self]

/-! ### §6.6.3: second-order corrections; commutator algebra (6.6.88)–(6.6.106) -/

/-- **(6.6.89)–(6.6.92)**.  Let `G` satisfy `PG = GP = 0` (the reduced inverse
`(1 - P)L₁⁻¹(1 - P)`).  Then for `v = Pv`,
`P(L₂ + L₃) G [L₂ + (1 - P)L₃] v = P{PL₂ + [P, L₃]} G {L₂ + [L₃, P]} v`. -/
theorem secondOrder_commutator_form (h : ProjHyp P L₁ L₂) (G : R) (hGP : G * P = 0)
    (hPG : P * G = 0) {M : Type*} [AddCommGroup M] [Module R M] (v : M) (hv : P • v = v) :
    (P * (L₂ + L₃) * G * (L₂ + (1 - P) * L₃)) • v
      = (P * (P * L₂ + (P * L₃ - L₃ * P)) * G * (L₂ + (L₃ * P - P * L₃))) • v := by
  have hR : (G * (L₂ + (1 - P) * L₃)) • v = (G * (L₂ + (L₃ * P - P * L₃))) • v := by
    conv_lhs => rw [← hv]
    conv_rhs => rw [← hv]
    rw [← mul_smul, ← mul_smul]
    congr 1
    have e1 : G * (P * L₃ * P) = 0 := by rw [← mul_assoc, ← mul_assoc, hGP, zero_mul, zero_mul]
    have e2 : G * (L₃ * P * P) = G * (L₃ * P) := by rw [mul_assoc L₃, h.idem]
    calc G * (L₂ + (1 - P) * L₃) * P = G * L₂ * P + G * L₃ * P - G * (P * L₃ * P) := by
          noncomm_ring
      _ = G * L₂ * P + G * (L₃ * P * P) - G * (P * L₃ * P) := by
          rw [e2]; noncomm_ring
      _ = G * (L₂ + (L₃ * P - P * L₃)) * P := by noncomm_ring
  have hL : P * (L₂ + L₃) * G = P * (P * L₂ + (P * L₃ - L₃ * P)) * G := by
    have e1 : P * (L₃ * P) * G = 0 := by rw [mul_assoc, mul_assoc, hPG, mul_zero, mul_zero]
    calc P * (L₂ + L₃) * G = (P * P) * L₂ * G + (P * P) * L₃ * G - P * (L₃ * P) * G := by
          rw [h.idem, e1]; noncomm_ring
      _ = P * (P * L₂ + (P * L₃ - L₃ * P)) * G := by noncomm_ring
  calc (P * (L₂ + L₃) * G * (L₂ + (1 - P) * L₃)) • v
      = (P * (L₂ + L₃)) • (G * (L₂ + (1 - P) * L₃)) • v := by
        rw [← mul_smul]; simp only [mul_assoc]
    _ = (P * (L₂ + L₃)) • (G * (L₂ + (L₃ * P - P * L₃))) • v := by rw [hR]
    _ = (P * (L₂ + L₃) * G) • (L₂ + (L₃ * P - P * L₃)) • v := by
        rw [← mul_smul, ← mul_smul]; simp only [mul_assoc]
    _ = _ := by rw [hL, ← mul_smul]

/-- **(6.6.102)**: `P[P, L₃] = 0` as soon as `P L₃ P = P L₃`.  In the text this follows from
(6.6.103)–(6.6.104), `∫ r_x p_x = ∫ s_x p_x = 0`: the operator `P` integrates out `α`, and
`∫ dα (L₃F)(x, α) = L̂₃ ∫ dα F(x, α)` is independent of how `F` depends on `α`. -/
theorem P_comm_L3_eq_zero (h : ProjHyp P L₁ L₂) (hP3 : P * L₃ * P = P * L₃) :
    P * (P * L₃ - L₃ * P) = 0 := by
  rw [mul_sub, ← mul_assoc, h.idem, ← mul_assoc, hP3, sub_self]

/-- **(6.6.105)**: with `P[P, L₃] = 0` the second-order term reduces to
`PL₂ G {L₂ + [L₃, P]} v`. -/
theorem secondOrder_reduced (h : ProjHyp P L₁ L₂) (hP3 : P * L₃ * P = P * L₃) (G : R) :
    P * (P * L₂ + (P * L₃ - L₃ * P)) * G = P * L₂ * G := by
  rw [mul_add, P_comm_L3_eq_zero h hP3, add_zero, ← mul_assoc, h.idem]

end Ring

/-! ### Scalars: (6.4.42)–(6.4.44), (6.5.24)–(6.5.25), §6.4.5 -/

section Algebra

variable {𝕜 : Type*} [Field 𝕜] {R : Type*} [Ring R] [Algebra 𝕜 R] {P L₁ L₂ L₃ : R}

/-- **(6.4.42)**: `P(γL₁ + L₂) = PL₂(1 - P)`, so that `∂ₜv = PL₂w`. -/
theorem proj_v_eq (h : ProjHyp P L₁ L₂) (γ : 𝕜) :
    P * (γ • L₁ + L₂) = P * L₂ * (1 - P) := by
  rw [mul_add, mul_smul_comm, h.PL1, smul_zero, zero_add, mul_sub, mul_one, h.PL2P, sub_zero]

/-- **(6.4.43)–(6.4.44)**: `(1 - P)(γL₁ + L₂) = γL₁(1 - P) + (1 - P)L₂(1 - P) + L₂P`. -/
theorem proj_w_eq (h : ProjHyp P L₁ L₂) (γ : 𝕜) :
    (1 - P) * (γ • L₁ + L₂) = γ • L₁ * (1 - P) + (1 - P) * L₂ * (1 - P) + L₂ * P := by
  have e1 : (1 - P) * (γ • L₁) = γ • L₁ := by
    rw [sub_mul, one_mul, mul_smul_comm, h.PL1, smul_zero, sub_zero]
  have e2 : γ • L₁ * (1 - P) = γ • L₁ := by
    rw [mul_sub, mul_one, smul_mul_assoc, h.L1P, smul_zero, sub_zero]
  have e3 : (1 - P) * L₂ * (1 - P) + L₂ * P = (1 - P) * L₂ := by
    rw [mul_sub, mul_one, h.one_sub_L2P]; abel
  rw [mul_add, e1, e2, add_assoc, e3]

/-- **(6.5.24)–(6.5.25)**: if `PL₃ = L₃P`, then
`P(γ²L₁ + γL₂ + L₃) = γ PL₂(1 - P) + L₃P`, i.e. `sṽ = γPL₂w̃ + L₃ṽ + v(0)`. -/
theorem commuting_L3_v (h : ProjHyp P L₁ L₂) (h3 : P * L₃ = L₃ * P) (γ : 𝕜) :
    P * (γ ^ 2 • L₁ + γ • L₂ + L₃) = γ • (P * L₂ * (1 - P)) + L₃ * P := by
  rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm, h.PL1, smul_zero, zero_add, h3,
    mul_sub, mul_one, h.PL2P, sub_zero]

/-- **The resolvent expansion behind (6.4.98)**.  Let `S` be the reduced inverse of `L₁`
(`L₁ S = Q`, with `Q = 1 - P`) and let `Y` be an inverse of `L₁ + εN` on the range of
`S` (`Y(L₁ + εN)S = S`, `YQ = Y`).  Then
`Y = S - ε SNS + ε² SNSNS - ε³ Y NSNSNS`. -/
theorem resolvent_expansion (Q L₁ S N Y : R) (ε : 𝕜) (hL1S : L₁ * S = Q)
    (hY : Y * (L₁ + ε • N) * S = S) (hYQ : Y * Q = Y) :
    Y = S - ε • (S * N * S) + ε ^ 2 • (S * N * S * N * S)
      - ε ^ 3 • (Y * N * S * N * S * N * S) := by
  have base : Y = S - ε • (Y * N * S) := by
    have h1 := hY
    rw [mul_add, add_mul, mul_assoc Y L₁ S, hL1S, hYQ, mul_smul_comm, smul_mul_assoc] at h1
    exact eq_sub_of_add_eq h1
  have step : ∀ Z : R, Y * Z = S * Z - ε • (Y * N * S * Z) := by
    intro Z
    conv_lhs => rw [base]
    rw [sub_mul, smul_mul_assoc]
  have e2 := step (N * S)
  have e3 := step (N * S * N * S)
  calc Y = S - ε • (Y * (N * S)) := by
        conv_lhs => rw [base]
        simp only [mul_assoc]
    _ = S - ε • (S * N * S) + ε ^ 2 • (Y * (N * S * N * S)) := by
        rw [e2, smul_sub, smul_smul]; simp only [mul_assoc]; module
    _ = _ := by
        rw [e3, smul_sub, smul_smul]; simp only [mul_assoc]; module

/-- **(6.4.94)–(6.4.99)**: with `N = QL₂ - εs₂` (so that `L₁ + εN = L₁ + γ⁻¹QL₂ - γ⁻²s₂`,
`ε = γ⁻¹`) the effective operator `-PL₂ Y L₂` of (6.4.94) equals `A + Bε + (C + D s₂)ε²` with
`A, B, C, D` of (6.4.99), up to the explicit remainder `ε³ R₃`. -/
theorem longTime_expansion (P Q L₁ L₂ S Y : R) (ε s₂ : 𝕜) (hL1S : L₁ * S = Q)
    (hY : Y * (L₁ + ε • (Q * L₂ - (ε * s₂) • (1 : R))) * S = S) (hYQ : Y * Q = Y) :
    -(P * L₂ * Y * L₂)
      = -(P * L₂ * S * L₂) + ε • (P * L₂ * S * Q * L₂ * S * L₂)
        + ε ^ 2 • (-(P * L₂ * S * Q * L₂ * S * Q * L₂ * S * L₂) + s₂ • (-(P * L₂ * S * S * L₂)))
        + ε ^ 3 • (s₂ • (P * L₂ * S * Q * L₂ * S * S * L₂ + P * L₂ * S * S * Q * L₂ * S * L₂)
          - (ε * s₂ ^ 2) • (P * L₂ * S * S * S * L₂)
          + P * L₂ * (Y * (Q * L₂ - (ε * s₂) • 1) * S * (Q * L₂ - (ε * s₂) • 1) * S
            * (Q * L₂ - (ε * s₂) • 1) * S) * L₂) := by
  have hexp := resolvent_expansion (𝕜 := 𝕜) Q L₁ S (Q * L₂ - (ε * s₂) • (1 : R)) Y ε hL1S
    hY hYQ
  set N := Q * L₂ - (ε * s₂) • (1 : R) with hN
  set T := Y * N * S * N * S * N * S
  have e : P * L₂ * (Y * N * S * N * S * N * S) * L₂ = P * L₂ * T * L₂ := rfl
  rw [e]
  conv_lhs => rw [hexp]
  simp only [hN, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc, smul_sub,
    smul_smul, smul_add, mul_add, add_mul, neg_sub, smul_neg]
  module

/-- **(6.4.100)–(6.4.101)**: rearranging `s₂(1 - ε²D)ṽ = (A + Bε + Cε²)ṽ + v(0)`.  Multiplying by
`1 + ε²D` gives `s₂ṽ = [A + Bε + (C + DA)ε²]ṽ + (1 + ε²D)v(0)` up to the explicit remainder
`ε³(DB + εDC + εs₂D²)ṽ`; the corrected initial condition `(1 + ε²D)v(0)` is the "initial layer"
of the text. -/
theorem longTime_rearranged {M : Type*} [AddCommGroup M] [Module R M] [Module 𝕜 M]
    [IsScalarTower 𝕜 R M] (A B C D : R) (ε s₂ : 𝕜) (v v0 : M)
    (h : s₂ • (((1 : R) - ε ^ 2 • D) • v) = (A + ε • B + ε ^ 2 • C) • v + v0) :
    s₂ • v = (A + ε • B + ε ^ 2 • (C + D * A)) • v + ((1 : R) + ε ^ 2 • D) • v0
      + ε ^ 3 • ((D * B + ε • (D * C) + (ε * s₂) • (D * D)) • v) := by
  have hv0 : v0 = (s₂ • ((1 : R) - ε ^ 2 • D) - (A + ε • B + ε ^ 2 • C)) • v := by
    rw [sub_smul, smul_assoc, h]; abel
  rw [hv0, ← mul_smul, ← smul_assoc (ε ^ 3), ← add_smul, ← add_smul, ← smul_one_smul R s₂ v]
  congr 1
  simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_add, smul_sub]
  module

end Algebra

/-! ### Time domain and Laplace transform (§6.4.1–§6.4.2) -/

section TimeDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **(6.4.42) in the time domain**: if `∂ₜp = (γL₁ + L₂)p`, then `v = Pp` satisfies
`∂ₜv = PL₂w` with `w = (1 - P)p`. -/
theorem hasDerivAt_proj_v {P L₁ L₂ : E →L[ℝ] E} (h : ProjHyp P L₁ L₂) (γ : ℝ) (p : ℝ → E)
    (t : ℝ) (hp : HasDerivAt p ((γ • L₁ + L₂) (p t)) t) :
    HasDerivAt (fun t => P (p t)) (P (L₂ ((1 - P) (p t)))) t := by
  have := P.hasFDerivAt.comp_hasDerivAt t hp
  convert this using 1
  have key := congrArg (fun T : E →L[ℝ] E => T (p t)) (proj_v_eq h γ)
  simp only [ContinuousLinearMap.mul_apply] at key
  simp only [key]

/-- **(6.4.44) in the time domain**: `∂ₜw = γL₁w + (1 - P)L₂w + L₂v`. -/
theorem hasDerivAt_proj_w {P L₁ L₂ : E →L[ℝ] E} (h : ProjHyp P L₁ L₂) (γ : ℝ) (p : ℝ → E)
    (t : ℝ) (hp : HasDerivAt p ((γ • L₁ + L₂) (p t)) t) :
    HasDerivAt (fun t => (1 - P) (p t))
      (γ • L₁ ((1 - P) (p t)) + (1 - P) (L₂ ((1 - P) (p t))) + L₂ (P (p t))) t := by
  have := (1 - P).hasFDerivAt.comp_hasDerivAt t hp
  convert this using 1
  have key := congrArg (fun T : E →L[ℝ] E => T (p t)) (proj_w_eq h γ)
  simp only [ContinuousLinearMap.mul_apply] at key
  rw [key]
  simp

variable [CompleteSpace E]

/-- (6.4.45): the Laplace transform `f̃(s) = ∫₀^∞ e^{-st} f(t) dt`. -/
def laplace (f : ℝ → E) (s : ℝ) : E := ∫ t in Ioi 0, Real.exp (-s * t) • f t

/-- **(6.4.46)**: `∫₀^∞ e^{-st} f'(t) dt = s f̃(s) - f(0)`, provided both integrals converge
and `e^{-st} f(t) → 0` as `t → ∞` (the boundary term the text drops). -/
theorem laplace_deriv (f f' : ℝ → E) (s : ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hi : IntegrableOn (fun t => Real.exp (-s * t) • f t) (Ioi 0))
    (hi' : IntegrableOn (fun t => Real.exp (-s * t) • f' t) (Ioi 0))
    (hlim : Tendsto (fun t => Real.exp (-s * t) • f t) atTop (𝓝 0)) :
    laplace f' s = s • laplace f s - f 0 := by
  set g : ℝ → E := fun t => Real.exp (-s * t) • f t
  have hg : ∀ t, HasDerivAt g ((-s) • (Real.exp (-s * t) • f t) + Real.exp (-s * t) • f' t) t := by
    intro t
    have he : HasDerivAt (fun t => Real.exp (-s * t)) (Real.exp (-s * t) * (-s)) t := by
      have := ((hasDerivAt_id t).const_mul (-s)).exp
      simpa using this
    convert he.smul (hf t) using 1
    rw [smul_smul, add_comm]
    congr 2
    ring
  have hint : IntegrableOn (fun t => (-s) • (Real.exp (-s * t) • f t)
      + Real.exp (-s * t) • f' t) (Ioi 0) := (hi.smul (-s)).add hi'
  have hc : ContinuousWithinAt g (Ici 0) 0 := (hg 0).continuousAt.continuousWithinAt
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hc (fun t _ => hg t) hint hlim
  rw [integral_add (f := fun t => (-s) • (Real.exp (-s * t) • f t)) (hi.smul (-s)) hi',
    integral_smul] at key
  simp only [g, mul_zero, Real.exp_zero, one_smul, zero_sub] at key
  unfold laplace
  set I := ∫ t in Ioi 0, Real.exp (-s * t) • f t
  calc (∫ t in Ioi 0, Real.exp (-s * t) • f' t)
      = ((-s) • I + ∫ t in Ioi 0, Real.exp (-s * t) • f' t) + s • I := by rw [neg_smul]; abel
    _ = s • I - f 0 := by rw [key]; abel

/-- **(6.4.47), first line**: the Laplace transform of `∂ₜv = Tw` (with `T = PL₂`) is
`sṽ = Tw̃ + v(0)`; the operator is moved through the Bochner integral. -/
theorem laplace_v_eq (T : E →L[ℝ] E) (v w : ℝ → E) (s : ℝ)
    (hv : ∀ t, HasDerivAt v (T (w t)) t)
    (hi : IntegrableOn (fun t => Real.exp (-s * t) • v t) (Ioi 0))
    (hiw : IntegrableOn (fun t => Real.exp (-s * t) • w t) (Ioi 0))
    (hlim : Tendsto (fun t => Real.exp (-s * t) • v t) atTop (𝓝 0)) :
    s • laplace v s = T (laplace w s) + v 0 := by
  have hi' : IntegrableOn (fun t => Real.exp (-s * t) • T (w t)) (Ioi 0) := by
    have := T.integrable_comp hiw
    simpa [Function.comp_def, T.map_smul] using this
  have h := laplace_deriv v (fun t => T (w t)) s hv hi hi' hlim
  have hT : laplace (fun t => T (w t)) s = T (laplace w s) := by
    unfold laplace
    rw [← T.integral_comp_comm hiw]
    simp [T.map_smul]
  rw [hT] at h
  rw [h]; abel

end TimeDomain


end Gardiner.Adiabatic
