/-
# Mean first-passage times for birth–death processes: §7.4 and §9.2.3

Gardiner, *Handbook of Stochastic Methods*, (7.4.1)–(7.4.19) and (9.2.34)–(9.2.50), for a
one-step process on `ℤ` with birth rates `t⁺(x) > 0` and death rates `t⁻(x) > 0`.

* `bdT_reflA_spec` — **(7.4.2)–(7.4.12)**: `T(x) = Σ_{y=x}^b φ(y) Σ_{z=a}^y 1/[t⁺(z)φ(z)]` solves
  the backward equation (7.4.2) on `[a, b]` with `T(a-1) = T(a)` (7.4.3a) and `T(b+1) = 0`
  (7.4.3b); `bdT_reflA_unique` — it is the only solution.
* `bd_U_recursion` — (7.4.5) with the correct sign: `t⁺U(x) - t⁻U(x-1) = -1` (**erratum**: the
  text prints `+1`; (7.4.8)–(7.4.9) are consistent with `-1`).
* `bdT_reflB_spec` — **(7.4.13), corrected**: with `a - 1` absorbing and `b` reflecting,
  `T(x) = Σ_{y=a}^x [t⁺(y)φ(y)/t⁻(y)] Σ_{z=y}^b 1/[t⁺(z)φ(z)]`; `bdT_reflB_printed_wrong` — the
  printed formula (with `φ(y)` instead of `φ(y-1) = t⁺(y)φ(y)/t⁻(y)`) fails already for a single
  state.
* `absProb_spec`, `absProb_tendsto_summable`, `absProb_tendsto_not_summable` — **(7.4.14)–(7.4.15),
  corrected**: absorption probabilities on `{0, …, N}` and their `N → ∞` limits;
  `absProb_printed_wrong` — the printed `M/(1+M)` with `∏ t⁺/t⁻` gives `½` for a walk that is
  absorbed with probability `1`.
* `bdPhi_detailed_balance` — **(7.4.16)**; `bdT_reflA_stationary` — **(7.4.17)** (corrected upper
  limit `x₃ - 1`).
  `bdT_sharp_peak` — **(7.4.18)–(7.4.19)** with the sharp-peak assumption as a named hypothesis and
  an explicit relative error.
* §7.4.2, what the comparison with the Fokker–Planck equation gets right and wrong:
  `bdRate_km_ratio`, `bdRate_log_ratio_close` (right: for the small-jump model of §7.2.1c the
  exact exponent `log(t⁺/t⁻)` and the Kramers–Moyal exponent `2(t⁺ - t⁻)/(t⁺ + t⁻)` agree to
  `O(δ³)` per step), `km_exponent_lt_log`, `km_barrier_lt`, `km_mfpt_ratio_tendsto` (wrong: for
  jumps of size one in a large system the Kramers–Moyal Fokker–Planck exponent is strictly
  smaller than the exact one, so the Fokker–Planck mean first-passage time is exponentially too
  short).
* `bdSplit_spec` — **(9.2.50)**: the splitting probabilities solve the discrete backward equation
  with `π_c(a) = 0`, `π_c(c) = 1`; `bd_flux_identity` — **(9.2.41)–(9.2.45)**.
-/
import SHSLib.Gardiner.Escape.Splitting
import SHSLib.Gardiner.Approx.JumpStationary

open Finset Filter Topology

noncomputable section

namespace Gardiner.Escape

/-- `φ(x) = ∏_{z=a+1}^x t⁻(z)/t⁺(z)` (7.4.6). -/
def bdPhi (tp tm : ℤ → ℝ) (a x : ℤ) : ℝ := ∏ z ∈ Icc (a + 1) x, tm z / tp z

/-- `S(x) = Σ_{z=a}^x 1/[t⁺(z)φ(z)]` (minus (7.4.9)). -/
def bdS (tp tm : ℤ → ℝ) (a x : ℤ) : ℝ := ∑ z ∈ Icc a x, 1 / (tp z * bdPhi tp tm a z)

/-- **(7.4.12)**: `a` reflecting, `b + 1` absorbing. -/
def bdTreflA (tp tm : ℤ → ℝ) (a b x : ℤ) : ℝ := ∑ y ∈ Icc x b, bdPhi tp tm a y * bdS tp tm a y

/-- **(7.4.13), corrected**: `a - 1` absorbing, `b` reflecting. -/
def bdTreflB (tp tm : ℤ → ℝ) (a b x : ℤ) : ℝ :=
  ∑ y ∈ Icc a x, tp y * bdPhi tp tm a y / tm y * ∑ z ∈ Icc y b, 1 / (tp z * bdPhi tp tm a z)

/-- (7.4.13) **as printed**. -/
def bdTreflBPrinted (tp tm : ℤ → ℝ) (a b x : ℤ) : ℝ :=
  ∑ y ∈ Icc a x, bdPhi tp tm a y * ∑ z ∈ Icc y b, 1 / (tp z * bdPhi tp tm a z)

/-- The backward operator of (7.4.2): `t⁺(x)[T(x+1) - T(x)] + t⁻(x)[T(x-1) - T(x)]`. -/
def bdBwd (tp tm T : ℤ → ℝ) (x : ℤ) : ℝ :=
  tp x * (T (x + 1) - T x) + tm x * (T (x - 1) - T x)

lemma Icc_succ_top {p q : ℤ} (h : p ≤ q + 1) : Icc p (q + 1) = insert (q + 1) (Icc p q) := by
  ext z; simp only [mem_Icc, mem_insert]; omega

lemma Icc_succ_bot {p q : ℤ} (h : p ≤ q) : Icc p q = insert p (Icc (p + 1) q) := by
  ext z; simp only [mem_Icc, mem_insert]; omega

lemma not_mem_Icc_top (p q : ℤ) : q + 1 ∉ Icc p q := by simp

lemma not_mem_Icc_bot (p q : ℤ) : p ∉ Icc (p + 1) q := by simp

section rates

variable {tp tm : ℤ → ℝ} (htp : ∀ x, 0 < tp x) (htm : ∀ x, 0 < tm x)

omit htp htm in
lemma bdPhi_self (a : ℤ) : bdPhi tp tm a a = 1 := by simp [bdPhi]

omit htp htm in
lemma bdPhi_succ {a x : ℤ} (h : a ≤ x) :
    bdPhi tp tm a (x + 1) = bdPhi tp tm a x * (tm (x + 1) / tp (x + 1)) := by
  rw [bdPhi, Icc_succ_top (by omega), prod_insert (not_mem_Icc_top _ _), mul_comm]; rfl

include htp htm in
lemma bdPhi_pos (a x : ℤ) : 0 < bdPhi tp tm a x :=
  prod_pos fun z _ => div_pos (htm z) (htp z)

omit htp htm in
lemma bdS_below (a : ℤ) : bdS tp tm a (a - 1) = 0 := by
  simp [bdS]

omit htp htm in
lemma bdS_succ {a x : ℤ} (h : a ≤ x + 1) :
    bdS tp tm a (x + 1) = bdS tp tm a x + 1 / (tp (x + 1) * bdPhi tp tm a (x + 1)) := by
  rw [bdS, Icc_succ_top h, sum_insert (not_mem_Icc_top _ _), add_comm]; rfl

omit htp htm in
lemma bdTreflA_step {a b x : ℤ} (h : x ≤ b) :
    bdTreflA tp tm a b x = bdPhi tp tm a x * bdS tp tm a x + bdTreflA tp tm a b (x + 1) := by
  rw [bdTreflA, Icc_succ_bot h, sum_insert (not_mem_Icc_bot _ _)]; rfl

include htp in
/-- `t⁻(x) φ(x - 1) = t⁺(x) φ(x)` for `x > a`. -/
lemma bdPhi_balance {a x : ℤ} (h : a < x) :
    tm x * bdPhi tp tm a (x - 1) = tp x * bdPhi tp tm a x := by
  have := bdPhi_succ (tp := tp) (tm := tm) (a := a) (x := x - 1) (by omega)
  rw [sub_add_cancel] at this
  rw [this]; have := (htp x).ne'; field_simp

include htp htm in
/-- **(7.4.2)–(7.4.12).**  The formula (7.4.12) solves the backward equation
`t⁺(x)[T(x+1) - T(x)] + t⁻(x)[T(x-1) - T(x)] = -1` for `a ≤ x ≤ b`, with the reflecting boundary
condition `T(a-1) = T(a)` (7.4.3a) and the absorbing one `T(b+1) = 0` (7.4.3b). -/
theorem bdT_reflA_spec {a b : ℤ} :
    (∀ x, a ≤ x → x ≤ b → bdBwd tp tm (bdTreflA tp tm a b) x = -1) ∧
      bdTreflA tp tm a b (a - 1) = bdTreflA tp tm a b a ∧ bdTreflA tp tm a b (b + 1) = 0 := by
  refine ⟨fun x hax hxb => ?_, ?_, by simp [bdTreflA]⟩
  · have h1 := bdTreflA_step (tp := tp) (tm := tm) (a := a) (b := b) hxb
    have h2 := bdTreflA_step (tp := tp) (tm := tm) (a := a) (b := b) (x := x - 1) (by omega)
    rw [sub_add_cancel] at h2
    have hS := bdS_succ (tp := tp) (tm := tm) (a := a) (x := x - 1) (by omega)
    rw [sub_add_cancel] at hS
    have hbal : tm x * (bdPhi tp tm a (x - 1) * bdS tp tm a (x - 1))
        = tp x * bdPhi tp tm a x * bdS tp tm a (x - 1) := by
      rcases eq_or_lt_of_le hax with h | h
      · subst h; rw [bdS_below]; ring
      · rw [← mul_assoc, bdPhi_balance htp h]
    have hφ := (bdPhi_pos htp htm a x).ne'
    have htpx := (htp x).ne'
    simp only [bdBwd]
    rw [h2, h1]
    have e : tp x * (bdTreflA tp tm a b (x + 1) - (bdPhi tp tm a x * bdS tp tm a x
          + bdTreflA tp tm a b (x + 1))) + tm x * (bdPhi tp tm a (x - 1) * bdS tp tm a (x - 1)
          + (bdPhi tp tm a x * bdS tp tm a x + bdTreflA tp tm a b (x + 1))
          - (bdPhi tp tm a x * bdS tp tm a x + bdTreflA tp tm a b (x + 1)))
        = tm x * (bdPhi tp tm a (x - 1) * bdS tp tm a (x - 1))
          - tp x * bdPhi tp tm a x * bdS tp tm a x := by ring
    rw [e, hbal, hS]
    field_simp
    ring
  · rcases le_or_gt (a - 1) b with h | h
    · rw [bdTreflA_step (tp := tp) (tm := tm) (a := a) (b := b) (x := a - 1) h, bdS_below,
        sub_add_cancel]; ring
    · have e1 : Icc (a - 1) b = ∅ := Icc_eq_empty (by omega)
      have e2 : Icc a b = ∅ := Icc_eq_empty (by omega)
      simp [bdTreflA, e1, e2]

include htp htm in
/-- **Uniqueness for (7.4.2)–(7.4.3).**  Any solution of (7.4.2) on `[a, b]` with `T(a-1) = T(a)`
and `T(b+1) = 0` coincides with (7.4.12) on `[a-1, b+1]`. -/
theorem bdT_reflA_unique {a b : ℤ} {T : ℤ → ℝ}
    (hT : ∀ x, a ≤ x → x ≤ b → bdBwd tp tm T x = -1) (ha : T (a - 1) = T a) (hb : T (b + 1) = 0) :
    ∀ x, a - 1 ≤ x → x ≤ b + 1 → T x = bdTreflA tp tm a b x := by
  obtain ⟨h0, ha0, hb0⟩ := bdT_reflA_spec htp htm (a := a) (b := b)
  set w := fun x => T x - bdTreflA tp tm a b x
  have inc : ∀ x, a - 1 ≤ x → x ≤ b → w (x + 1) = w x := by
    intro x hx
    induction x, hx using Int.le_induction with
    | base => intro _; simp only [w, sub_add_cancel, ha, ha0]
    | succ n hn ih =>
      intro hnb
      have e1 := hT (n + 1) (by omega) hnb
      have e2 := h0 (n + 1) (by omega) hnb
      have ih' := ih (by omega)
      simp only [bdBwd, add_sub_cancel_right] at e1 e2
      simp only [w] at ih' ⊢
      have hpos := htp (n + 1)
      have key : tp (n + 1) * ((T (n + 1 + 1) - bdTreflA tp tm a b (n + 1 + 1))
          - (T (n + 1) - bdTreflA tp tm a b (n + 1))) = 0 := by
        linear_combination e1 - e2 + tm (n + 1) * ih'
      rcases mul_eq_zero.mp key with h | h
      · linarith
      · linarith
  have hconst : ∀ x, a - 1 ≤ x → x ≤ b + 1 → w x = w (a - 1) := by
    intro x hx
    induction x, hx using Int.le_induction with
    | base => intro _; rfl
    | succ n hn ih =>
      intro hnb
      rw [inc n hn (by omega), ih (by omega)]
  intro x hx1 hx2
  have h1 := hconst x hx1 hx2
  have h2 : w (a - 1) = 0 := by
    rcases le_or_gt (a - 1) (b + 1) with h | h
    · rw [← hconst (b + 1) h le_rfl]; simp only [w, hb, hb0, sub_self]
    · omega
  have := h1.trans h2
  simp only [w] at this
  linarith

omit htp htm in
/-- **(7.4.5) with the correct sign**: with `U(x) = T(x+1) - T(x)` (7.4.4), (7.4.2) reads
`t⁺(x)U(x) - t⁻(x)U(x-1) = -1`; the text's `= 1` is a sign misprint (its (7.4.8) has `-1`). -/
theorem bd_U_recursion (T : ℤ → ℝ) (x : ℤ) :
    bdBwd tp tm T x = tp x * (T (x + 1) - T x) - tm x * (T (x - 1 + 1) - T (x - 1)) := by
  simp only [bdBwd, sub_add_cancel]; ring

omit htp htm in
lemma bdTreflB_step {a b x : ℤ} (h : a ≤ x + 1) :
    bdTreflB tp tm a b (x + 1) = bdTreflB tp tm a b x
      + tp (x + 1) * bdPhi tp tm a (x + 1) / tm (x + 1)
        * ∑ z ∈ Icc (x + 1) b, 1 / (tp z * bdPhi tp tm a z) := by
  rw [bdTreflB, Icc_succ_top h, sum_insert (not_mem_Icc_top _ _), add_comm]; rfl

omit htp htm in
lemma bdR_step {b y : ℤ} (h : y ≤ b) (g : ℤ → ℝ) :
    ∑ z ∈ Icc y b, g z = g y + ∑ z ∈ Icc (y + 1) b, g z := by
  rw [Icc_succ_bot h, sum_insert (not_mem_Icc_bot _ _)]

include htp htm in
/-- **(7.4.13), corrected.**  With `a - 1` absorbing and `b` reflecting,
`T(x) = Σ_{y=a}^x [t⁺(y)φ(y)/t⁻(y)] Σ_{z=y}^b 1/[t⁺(z)φ(z)]` solves (7.4.2) on `[a, b]` with
`T(a-1) = 0` and `T(b+1) = T(b)`.  (The factor `t⁺(y)φ(y)/t⁻(y)` is `φ(y-1)`; the text prints
`φ(y)`.) -/
theorem bdT_reflB_spec {a b : ℤ} (hab : a ≤ b) :
    (∀ x, a ≤ x → x ≤ b → bdBwd tp tm (bdTreflB tp tm a b) x = -1) ∧
      bdTreflB tp tm a b (a - 1) = 0 ∧ bdTreflB tp tm a b (b + 1) = bdTreflB tp tm a b b := by
  refine ⟨fun x hax hxb => ?_, by simp [bdTreflB], ?_⟩
  · set R := fun y => ∑ z ∈ Icc y b, 1 / (tp z * bdPhi tp tm a z)
    have h1 := bdTreflB_step (tp := tp) (tm := tm) (a := a) (b := b) (x := x) (by omega)
    have h2 := bdTreflB_step (tp := tp) (tm := tm) (a := a) (b := b) (x := x - 1) (by omega)
    rw [sub_add_cancel] at h2
    have hψ : tp (x + 1) * bdPhi tp tm a (x + 1) / tm (x + 1) = bdPhi tp tm a x := by
      rw [bdPhi_succ hax]; have := (htp (x + 1)).ne'; have := (htm (x + 1)).ne'; field_simp
    have hR := bdR_step hxb (fun z => 1 / (tp z * bdPhi tp tm a z))
    have hφ := (bdPhi_pos htp htm a x).ne'
    have htpx := (htp x).ne'
    have htmx := (htm x).ne'
    simp only [bdBwd]
    rw [h1, hψ]
    rw [show bdTreflB tp tm a b (x - 1) = bdTreflB tp tm a b x
        - tp x * bdPhi tp tm a x / tm x * ∑ z ∈ Icc x b, 1 / (tp z * bdPhi tp tm a z) by
      rw [h2]; ring]
    rw [hR]
    field_simp
    ring
  · rw [bdTreflB_step (tp := tp) (tm := tm) (a := a) (b := b) (x := b) (by omega)]
    simp

/-- **Erratum (7.4.13).**  The printed formula fails for the single state `a = b = 0` with
`t⁺ = 1`, `t⁻ = 2`: it gives `T(0) = 1`, but (7.4.2) then reads `-2 = -1`.  (The true mean exit
time is `1/2`.) -/
theorem bdT_reflB_printed_wrong :
    bdBwd (fun _ => 1) (fun _ => 2) (bdTreflBPrinted (fun _ => 1) (fun _ => 2) 0 0) 0 = -2 := by
  have e1 : Icc (0 : ℤ) 1 = {0, 1} := by decide
  simp [bdBwd, bdTreflBPrinted, bdPhi, e1]

end rates


/-! ### §7.4.1: probability of absorption, (7.4.14)–(7.4.15) corrected -/

/-- `ρ_k = ∏_{j=1}^k μ_j/λ_j` (death over birth rates; `ρ₀ = 1`). -/
def absRho (lam mu : ℕ → ℝ) (k : ℕ) : ℝ := ∏ j ∈ Icc 1 k, mu j / lam j

/-- Probability of absorption at `0` before `N`, from `i`, for the one-step process on
`{0, …, N}` (both ends absorbing): `h_N(i) = Σ_{k=i}^{N-1} ρ_k / Σ_{k=0}^{N-1} ρ_k`. -/
def absProb (lam mu : ℕ → ℝ) (N i : ℕ) : ℝ :=
  (∑ k ∈ Ico i N, absRho lam mu k) / ∑ k ∈ range N, absRho lam mu k

section absorption

variable {lam mu : ℕ → ℝ} (hl : ∀ j, 0 < lam j) (hm : ∀ j, 0 < mu j)
include hl hm

lemma absRho_pos (k : ℕ) : 0 < absRho lam mu k := prod_pos fun j _ => div_pos (hm j) (hl j)

omit hl hm in
lemma absRho_succ (k : ℕ) : absRho lam mu (k + 1) = absRho lam mu k * (mu (k + 1) / lam (k + 1)) :=
  prod_Icc_succ_top (by omega) _

/-- **Absorption probabilities, exact** (the finite-`N` form of (7.4.15)): `h(0) = 1`,
`h(N) = 0` and `λ_i[h(i+1) - h(i)] + μ_i[h(i-1) - h(i)] = 0` for `0 < i < N`. -/
theorem absProb_spec {N : ℕ} (hN : 1 ≤ N) :
    absProb lam mu N 0 = 1 ∧ absProb lam mu N N = 0 ∧
      ∀ i, 1 ≤ i → i + 1 ≤ N → lam i * (absProb lam mu N (i + 1) - absProb lam mu N i)
        + mu i * (absProb lam mu N (i - 1) - absProb lam mu N i) = 0 := by
  have hZ : 0 < ∑ k ∈ range N, absRho lam mu k :=
    sum_pos (fun k _ => absRho_pos hl hm k) (nonempty_range_iff.mpr (by omega))
  refine ⟨?_, by simp [absProb], fun i hi hiN => ?_⟩
  · simp only [absProb, ← range_eq_Ico]; exact div_self hZ.ne'
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [absProb, Nat.add_sub_cancel]
    rw [sum_eq_sum_Ico_succ_bot (by omega : j < N), sum_eq_sum_Ico_succ_bot (by omega : j + 1 < N),
      absRho_succ]
    have := (hl (j + 1)).ne'
    field_simp
    ring

/-- **(7.4.15) corrected, recurrent-to-`0` case.**  If `Σ ρ_k = ∞` the absorption probability at
`0` tends to `1` as the upper barrier recedes, `N → ∞`. -/
theorem absProb_tendsto_not_summable (hns : ¬ Summable (absRho lam mu)) (i : ℕ) :
    Tendsto (fun N => absProb lam mu N i) atTop (𝓝 1) := by
  have hS : Tendsto (fun N => ∑ k ∈ range N, absRho lam mu k) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => (absRho_pos hl hm k).le)).mp hns
  have h0 : Tendsto (fun N => (∑ k ∈ range i, absRho lam mu k) / ∑ k ∈ range N, absRho lam mu k)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hS
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (max i 1)] with N hN
  have hZ : 0 < ∑ k ∈ range N, absRho lam mu k :=
    sum_pos (fun k _ => absRho_pos hl hm k) (nonempty_range_iff.mpr (by omega))
  rw [absProb, sum_Ico_eq_sub _ (by omega : i ≤ N)]
  field_simp

/-- **(7.4.15) corrected, transient case.**  If `Σ ρ_k < ∞`, the absorption probability from `i`
tends to `Σ_{k≥i} ρ_k / Σ_{k≥0} ρ_k = M(i)/(1 + M(1))`, `M(x) = Σ_{k≥x} ρ_k`.  (The text's
(7.4.14)–(7.4.15) use `∏ t⁺/t⁻` instead of `∏ t⁻/t⁺` and `M(x)/(1 + M(x))`.) -/
theorem absProb_tendsto_summable (hs : Summable (absRho lam mu)) (i : ℕ) :
    Tendsto (fun N => absProb lam mu N i) atTop
      (𝓝 ((∑' k, absRho lam mu k - ∑ k ∈ range i, absRho lam mu k) / ∑' k, absRho lam mu k)) := by
  have hS := hs.hasSum.tendsto_sum_nat
  have hpos : 0 < ∑' k, absRho lam mu k :=
    hs.tsum_pos (fun k => (absRho_pos hl hm k).le) 0 (absRho_pos hl hm 0)
  have := (hS.sub_const (∑ k ∈ range i, absRho lam mu k)).div hS hpos.ne'
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop i] with N hN
  rw [absProb, sum_Ico_eq_sub _ hN]
  rfl

end absorption

/-- **Erratum (7.4.14)–(7.4.15).**  For `t⁺ = 1`, `t⁻ = 2` (drift towards the absorbing state)
absorption is certain — the corrected absorption probability from `1` tends to `1` — whereas
the printed `M/(1+M)`, with `M = Σ_{y≥a} ∏_{z=a}^y t⁺/t⁻ = Σ (1/2)^{y+1} = 1`, gives `½`. -/
theorem absProb_printed_wrong :
    Tendsto (fun N => absProb (fun _ => 1) (fun _ => 2) N 1) atTop (𝓝 1) ∧
      (∑' y : ℕ, ∏ _z ∈ range (y + 1), (1 : ℝ) / 2) / (1 + ∑' y : ℕ, ∏ _z ∈ range (y + 1), (1 : ℝ) / 2)
        = 1 / 2 := by
  constructor
  · refine absProb_tendsto_not_summable (fun _ => one_pos) (fun _ => two_pos) ?_ 1
    have e : absRho (fun _ => (1 : ℝ)) (fun _ => 2) = fun k => (2 : ℝ) ^ k := by
      ext k; simp [absRho]
    rw [e, summable_geometric_iff_norm_lt_one]
    norm_num
  · have hM : ∑' y : ℕ, ∏ _z ∈ range (y + 1), (1 : ℝ) / 2 = 1 := by
      simp only [prod_const, card_range]
      rw [show (fun y : ℕ => ((1 : ℝ) / 2) ^ (y + 1)) = fun y => (1 / 2) * (1 / 2 : ℝ) ^ y by
        ext y; ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    rw [hM]; norm_num

/-! ### §7.4.2: comparison with the Fokker–Planck equation -/

section detailed

variable {tp tm P : ℤ → ℝ} (htp : ∀ x, 0 < tp x) (htm : ∀ x, 0 < tm x) (hP : ∀ x, 0 < P x)
  (hdb : ∀ z, tm z * P z = tp (z - 1) * P (z - 1))
include htp htm hP hdb

/-- **(7.4.16)**: under detailed balance (9.2.42), `φ(x) = P_s(0)t⁺(0)/[P_s(x)t⁺(x)]`. -/
theorem bdPhi_detailed_balance {x : ℤ} (hx : 0 ≤ x) :
    bdPhi tp tm 0 x = P 0 * tp 0 / (P x * tp x) := by
  induction x, hx using Int.le_induction with
  | base => rw [bdPhi_self]; have := (hP 0).ne'; have := (htp 0).ne'; field_simp
  | succ n hn ih =>
    rw [bdPhi_succ hn, ih]
    have h := hdb (n + 1)
    rw [add_sub_cancel_right] at h
    have := (hP n).ne'; have := (htp n).ne'; have := (hP (n + 1)).ne'
    have := (htp (n + 1)).ne'; have := (htm (n + 1)).ne'
    have htm' : tm (n + 1) = tp n * P n / P (n + 1) := by
      rw [eq_div_iff (by assumption)]; linarith
    rw [htm']
    field_simp

/-- **(7.4.17), corrected upper limit.**  With `0` reflecting and `x₃` absorbing (so `b = x₃ - 1`
in (7.4.12)), `T(x₁ → x₃) = Σ_{y=x₁}^{x₃-1} [P_s(y)t⁺(y)]⁻¹ Σ_{z=0}^y P_s(z)`.  (The text's upper
limit `x₃` gives the mean time to reach `x₃ + 1`.) -/
theorem bdT_reflA_stationary {x₁ x₃ : ℤ} (hx₁ : 0 ≤ x₁) :
    bdTreflA tp tm 0 (x₃ - 1) x₁ = ∑ y ∈ Icc x₁ (x₃ - 1), (P y * tp y)⁻¹ * ∑ z ∈ Icc 0 y, P z := by
  apply sum_congr rfl
  intro y hy
  have hy0 : 0 ≤ y := le_trans hx₁ (mem_Icc.mp hy).1
  rw [bdS, mul_sum, mul_sum]
  apply sum_congr rfl
  intro z hz
  have hz0 : 0 ≤ z := (mem_Icc.mp hz).1
  rw [bdPhi_detailed_balance htp htm hP hdb hy0, bdPhi_detailed_balance htp htm hP hdb hz0]
  have := (hP 0).ne'; have := (htp 0).ne'; have := (hP y).ne'; have := (htp y).ne'
  have := (hP z).ne'; have := (htp z).ne'
  field_simp

omit htp hP in
/-- The exact stationary distribution of a one-step process with detailed balance:
`P_s(x) = P_s(0) ∏_{z=1}^x t⁺(z-1)/t⁻(z)`, i.e. `log P_s(x) - log P_s(0) = Σ log(t⁺(z-1)/t⁻(z))`. -/
theorem bd_stationary_product {x : ℤ} (hx : 0 ≤ x) :
    P x = P 0 * ∏ z ∈ Icc 1 x, tp (z - 1) / tm z := by
  induction x, hx using Int.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Icc_succ_top (by omega), prod_insert (not_mem_Icc_top _ _), add_sub_cancel_right]
    have h := hdb (n + 1)
    rw [add_sub_cancel_right] at h
    have := (htm (n + 1)).ne'
    rw [mul_comm (tp n / tm (n + 1)), ← mul_assoc, ← ih]
    field_simp
    linarith

/-- **(9.2.50)**: the splitting probability
`π_c(x₀) = Σ_{z=a+1}^{x₀} [P_s(z)t⁻(z)]⁻¹ / Σ_{z=a+1}^c [P_s(z)t⁻(z)]⁻¹` solves the discrete
backward equation `t⁺(x)[π(x+1) - π(x)] + t⁻(x)[π(x-1) - π(x)] = 0` on `a < x < c`, with
`π_c(a) = 0`, `π_c(c) = 1`. -/
theorem bdSplit_spec {a c : ℤ} (hac : a < c) :
    (fun x => (∑ z ∈ Icc (a + 1) x, (P z * tm z)⁻¹) / ∑ z ∈ Icc (a + 1) c, (P z * tm z)⁻¹) a = 0 ∧
    (fun x => (∑ z ∈ Icc (a + 1) x, (P z * tm z)⁻¹) / ∑ z ∈ Icc (a + 1) c, (P z * tm z)⁻¹) c = 1 ∧
    ∀ x, a < x → x < c → bdBwd tp tm
      (fun x => (∑ z ∈ Icc (a + 1) x, (P z * tm z)⁻¹) / ∑ z ∈ Icc (a + 1) c, (P z * tm z)⁻¹) x = 0 := by
  set W := ∑ z ∈ Icc (a + 1) c, (P z * tm z)⁻¹
  have hW : 0 < W :=
    sum_pos (fun z _ => inv_pos.mpr (mul_pos (hP z) (htm z))) ⟨c, by simp; omega⟩
  refine ⟨by simp, div_self hW.ne', fun x hax hxc => ?_⟩
  have d1 : (∑ z ∈ Icc (a + 1) (x + 1), (P z * tm z)⁻¹) / W
      - (∑ z ∈ Icc (a + 1) x, (P z * tm z)⁻¹) / W = (P (x + 1) * tm (x + 1))⁻¹ / W := by
    rw [Icc_succ_top (by omega : a + 1 ≤ x + 1), sum_insert (not_mem_Icc_top _ _)]; ring
  have hx : Icc (a + 1) x = insert x (Icc (a + 1) (x - 1)) := by
    ext z; simp only [mem_Icc, mem_insert]; omega
  have d2 : (∑ z ∈ Icc (a + 1) (x - 1), (P z * tm z)⁻¹) / W
      - (∑ z ∈ Icc (a + 1) x, (P z * tm z)⁻¹) / W = -((P x * tm x)⁻¹ / W) := by
    rw [hx, sum_insert (by simp)]; ring
  simp only [bdBwd]
  rw [d1, d2]
  have h := hdb (x + 1)
  rw [add_sub_cancel_right] at h
  rw [show P (x + 1) * tm (x + 1) = tp x * P x by linarith]
  have := (hP x).ne'; have := (htm x).ne'; have := (htp x).ne'; have := hW.ne'
  field_simp
  ring

end detailed

/-- `|2(r-1)/(r+1)| < |log r|` for `r > 1`. -/
lemma km_lt_log_of_one_lt {r : ℝ} (hr : 1 < r) : 2 * (r - 1) / (r + 1) < Real.log r := by
  let f := fun s : ℝ => Real.log s - 2 * (s - 1) / (s + 1)
  have hderiv : ∀ s, 0 < s → HasDerivAt f (1 / s - 4 / (s + 1) ^ 2) s := by
    intro s hs
    have h1 := Real.hasDerivAt_log hs.ne'
    have h2 : HasDerivAt (fun s : ℝ => 2 * (s - 1) / (s + 1)) (4 / (s + 1) ^ 2) s := by
      have := ((hasDerivAt_id s).sub_const 1 |>.const_mul 2).div ((hasDerivAt_id s).add_const 1)
        (by simp; linarith)
      convert this using 1; simp; field_simp; ring
    convert h1.sub h2 using 1; simp
  have hmono : StrictMonoOn f (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro s hs; exact (hderiv s (lt_of_lt_of_le one_pos hs)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs1 : 1 < s := hs
      rw [(hderiv s (by linarith)).deriv]
      have : 1 / s - 4 / (s + 1) ^ 2 = (s - 1) ^ 2 / (s * (s + 1) ^ 2) := by field_simp; ring
      rw [this]; apply div_pos (by nlinarith) (by positivity)
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hr.le) hr
  simp only [f, Real.log_one, sub_self] at this
  linarith

/-- **Kramers–Moyal versus exact exponent.**  For `r > 0`, `r ≠ 1`:
`|2(r - 1)/(r + 1)| < |log r|`.  With `r = t⁻/t⁺`, `log r` is the exact one-step increment of
`-log P_s` (`bd_stationary_product`), while `2(t⁻ - t⁺)/(t⁻ + t⁺) = -2A/B` (`bdRate_km_ratio`
with unit jumps) is the increment of the potential of the Kramers–Moyal Fokker–Planck equation. -/
theorem km_exponent_lt_log {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    |2 * (r - 1) / (r + 1)| < |Real.log r| := by
  rcases lt_or_gt_of_ne hr1 with h | h
  · have h' : 1 < r⁻¹ := one_lt_inv_iff₀.mpr ⟨hr, h⟩
    have := km_lt_log_of_one_lt h'
    rw [Real.log_inv] at this
    have e : 2 * (r⁻¹ - 1) / (r⁻¹ + 1) = -(2 * (r - 1) / (r + 1)) := by field_simp; ring
    rw [e] at this
    have hl : Real.log r < 0 := Real.log_neg hr h
    have hk : 2 * (r - 1) / (r + 1) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    rw [abs_of_neg hl, abs_of_neg hk]; linarith
  · have := km_lt_log_of_one_lt h
    have hk : 0 < 2 * (r - 1) / (r + 1) := div_pos (by linarith) (by linarith)
    rw [abs_of_pos (Real.log_pos h), abs_of_pos hk]; exact this

/-- **The Kramers–Moyal barrier is too low.**  If along the uphill path `[p, q]` the ratio
`r = t⁻/t⁺` is continuous, `≥ 1`, and `> 1` somewhere, the Kramers–Moyal Fokker–Planck barrier
`∫ 2(r-1)/(r+1)` is strictly smaller than the exact master-equation barrier `∫ log r`. -/
theorem km_barrier_lt {r : ℝ → ℝ} {p q x₀ : ℝ} (hpq : p < q) (hr : ContinuousOn r (Set.Icc p q))
    (hr1 : ∀ x ∈ Set.Icc p q, 1 ≤ r x) (hx₀ : x₀ ∈ Set.Icc p q) (hrx₀ : 1 < r x₀) :
    ∫ x in p..q, 2 * (r x - 1) / (r x + 1) < ∫ x in p..q, Real.log (r x) := by
  have hpos : ∀ x ∈ Set.Icc p q, 0 < r x := fun x hx => lt_of_lt_of_le one_pos (hr1 x hx)
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hpq
  · exact ContinuousOn.div (continuousOn_const.mul (hr.sub continuousOn_const))
      (hr.add continuousOn_const) (fun x hx => by linarith [hpos x hx])
  · exact hr.log (fun x hx => (hpos x hx).ne')
  · intro x hx
    rcases eq_or_lt_of_le (hr1 x (Set.Ioc_subset_Icc_self hx)) with h | h
    · rw [← h]; simp
    · exact (km_lt_log_of_one_lt h).le
  · exact ⟨x₀, hx₀, km_lt_log_of_one_lt hrx₀⟩

/-- **Consequence for mean first-passage times.**  In a system of size `V` (rates
`t^±(x) = V w^±(x/V)`), the mean first-passage time over the barrier behaves as
`e^{V Φ}` with `Φ` the barrier of `-V⁻¹ log P_s`; a strictly smaller Kramers–Moyal barrier
`Φ_KM < Φ` makes the ratio of the exact to the Kramers–Moyal Arrhenius factors diverge. -/
theorem km_mfpt_ratio_tendsto {Φ ΦKM : ℝ} (h : ΦKM < Φ) :
    Tendsto (fun V : ℝ => Real.exp (V * Φ) / Real.exp (V * ΦKM)) atTop atTop := by
  have : (fun V : ℝ => Real.exp (V * Φ) / Real.exp (V * ΦKM)) = fun V => Real.exp (V * (Φ - ΦKM)) := by
    ext V; rw [← Real.exp_sub]; ring_nf
  rw [this]
  exact Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const (by linarith))

/-- **What §7.4.2 gets right: the small-jump model of §7.2.1c.**  For the rates
`t^±(x) = ±A(x)/(2δ) + B(x)/(2δ²)` the Kramers–Moyal ratio is exactly the Fokker–Planck one:
`2(t⁺ - t⁻)/(t⁺ + t⁻) = 2δA/B`. -/
theorem bdRate_km_ratio (A B : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) {x : ℝ} (hB : B x ≠ 0) :
    2 * (Gardiner.bdRate A B δ true x - Gardiner.bdRate A B δ false x)
      / (Gardiner.bdRate A B δ true x + Gardiner.bdRate A B δ false x) = 2 * δ * A x / B x := by
  have e1 : Gardiner.bdRate A B δ true x - Gardiner.bdRate A B δ false x = A x / δ := by
    simp only [Gardiner.bdRate, if_true, Bool.false_eq_true, if_false]; field_simp; ring
  have e2 : Gardiner.bdRate A B δ true x + Gardiner.bdRate A B δ false x = B x / δ ^ 2 := by
    simp only [Gardiner.bdRate, if_true, Bool.false_eq_true, if_false]; field_simp; ring
  rw [e1, e2]
  field_simp

/-- **… and the exact exponent agrees with it to third order.**  For the same rates, with
`v = δA/B`, `|v| ≤ ½`: `|log(t⁺/t⁻) - 2(t⁺ - t⁻)/(t⁺ + t⁻)| ≤ 4|v|³`.  Summed over the `O(1/δ)`
steps of a fixed interval this is `O(δ²)`: as `δ → 0` the birth–death and Fokker–Planck
stationary distributions, hence (via (7.4.16)–(7.4.17)) the mean first-passage time formulas,
coincide (cf. `Gardiner.bdStat_log_rate`). -/
theorem bdRate_log_ratio_close (A B : ℝ → ℝ) {δ : ℝ} (hδ : δ ≠ 0) {x : ℝ} (hB : 0 < B x)
    (hv : |δ * A x / B x| ≤ 1 / 2) :
    |Real.log (Gardiner.bdRate A B δ true x / Gardiner.bdRate A B δ false x)
      - 2 * (Gardiner.bdRate A B δ true x - Gardiner.bdRate A B δ false x)
        / (Gardiner.bdRate A B δ true x + Gardiner.bdRate A B δ false x)| ≤ 4 * |δ * A x / B x| ^ 3 := by
  rw [bdRate_km_ratio A B hδ hB.ne']
  set v := δ * A x / B x
  have hv' := abs_le.mp hv
  have e : Gardiner.bdRate A B δ true x / Gardiner.bdRate A B δ false x = (1 + v) / (1 - v) := by
    simp only [Gardiner.bdRate, if_true, Bool.false_eq_true, if_false, v]
    field_simp
    ring
  rw [e, Real.log_div (by linarith) (by linarith), show 2 * δ * A x / B x = 2 * v by
    simp only [v]; ring]
  exact Gardiner.log_ratio_cubic hv

/-! ### §9.2.3: the flux identities (9.2.41)–(9.2.45) -/

/-- **(9.2.41)**: if `Ṗ(z) = J(z+1) - J(z)` (9.2.34) with `J(0) = 0`, then `Ṁ(x) = J(x)`, where
`M(x) = Σ_{z<x} P(z)` (9.2.36). -/
theorem bd_mass_flux {Pdot J : ℕ → ℝ} (hJ0 : J 0 = 0) (hme : ∀ z, Pdot z = J (z + 1) - J z)
    (x : ℕ) : ∑ z ∈ range x, Pdot z = J x := by
  simp only [hme]; rw [sum_range_sub, hJ0, sub_zero]

/-- **(9.2.44)**: under detailed balance (9.2.42), the flux (9.2.35) is
`J(x) = P_s(x)t⁻(x)[β(x) - β(x-1)]`, `β = P/P_s` (9.2.43). -/
theorem bd_flux_beta {tp tm P Ps : ℕ → ℝ} (hPs : ∀ x, 0 < Ps x)
    (hdb : ∀ x, tm (x + 1) * Ps (x + 1) = tp x * Ps x) (x : ℕ) :
    tm (x + 1) * P (x + 1) - tp x * P x
      = Ps (x + 1) * tm (x + 1) * (P (x + 1) / Ps (x + 1) - P x / Ps x) := by
  have := (hPs x).ne'; have := (hPs (x + 1)).ne'
  field_simp
  linear_combination P x * hdb x

/-- **(9.2.45)**: `Σ_{z=a+1}^{x₀} J(z)/[P_s(z)t⁻(z)] = β(x₀) - β(a)` (telescoping). -/
theorem bd_flux_identity {tp tm P Ps : ℕ → ℝ} (hPs : ∀ x, 0 < Ps x) (htm : ∀ x, 0 < tm x)
    (hdb : ∀ x, tm (x + 1) * Ps (x + 1) = tp x * Ps x) (a n : ℕ) :
    ∑ k ∈ range n, (tm (a + k + 1) * P (a + k + 1) - tp (a + k) * P (a + k))
        / (Ps (a + k + 1) * tm (a + k + 1))
      = P (a + n) / Ps (a + n) - P a / Ps a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, bd_flux_beta hPs hdb]
    have h1 := (hPs (a + n + 1)).ne'; have h2 := (htm (a + n + 1)).ne'
    rw [mul_div_cancel_left₀ _ (mul_ne_zero h1 h2)]
    rw [show a + (n + 1) = a + n + 1 by ring]
    ring

/-! ### (7.4.18)–(7.4.19): the sharp-peak evaluation -/

/-- **(7.4.18)–(7.4.19) with an explicit error.**  If on the summation range the slowly varying
factor `t⁺(y)⁻¹ Σ_{z=0}^y P_s(z)` of (7.4.17) is within a relative error `δ` of its value
`n₁/t⁺(x₂)` at the barrier (the text's sharp-peak assumption, here a named hypothesis), then
`T(x₁ → x₃) = (n₁/t⁺(x₂)) Σ_y P_s(y)⁻¹` up to the relative error `δ`.  (As in
`bdT_reflA_stationary`, the upper limit of the sum is `x₃ - 1`.) -/
theorem bdT_sharp_peak {tp P : ℤ → ℝ} (hP : ∀ y, 0 < P y) {x₁ x₃ x₂ : ℤ} {n₁ δ : ℝ}
    (hpeak : ∀ y ∈ Icc x₁ (x₃ - 1),
      |(tp y)⁻¹ * ∑ z ∈ Icc 0 y, P z - n₁ / tp x₂| ≤ δ * (n₁ / tp x₂)) :
    |∑ y ∈ Icc x₁ (x₃ - 1), (P y * tp y)⁻¹ * ∑ z ∈ Icc 0 y, P z
        - n₁ / tp x₂ * ∑ y ∈ Icc x₁ (x₃ - 1), (P y)⁻¹|
      ≤ δ * (n₁ / tp x₂) * ∑ y ∈ Icc x₁ (x₃ - 1), (P y)⁻¹ := by
  have e : ∑ y ∈ Icc x₁ (x₃ - 1), (P y * tp y)⁻¹ * ∑ z ∈ Icc 0 y, P z
        - n₁ / tp x₂ * ∑ y ∈ Icc x₁ (x₃ - 1), (P y)⁻¹
      = ∑ y ∈ Icc x₁ (x₃ - 1), (P y)⁻¹ * ((tp y)⁻¹ * ∑ z ∈ Icc 0 y, P z - n₁ / tp x₂) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro y _; rw [mul_inv]; ring
  rw [e, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y hy => ?_)
  rw [abs_mul, abs_of_pos (inv_pos.mpr (hP y)), mul_comm (δ * (n₁ / tp x₂))]
  exact mul_le_mul_of_nonneg_left (hpeak y hy) (inv_pos.mpr (hP y)).le

/-- **Instance of (7.4.18)**: for `t⁺ = 1`, `P_s(z) = 2^{-z}`, `x₁ = x₂ = 1`, `x₃ = 2` and
`n₁ = P_s(0) + P_s(1)`, the sharp-peak hypothesis holds with `δ = 0`, so (7.4.17) equals
(7.4.18) exactly. -/
theorem bdT_sharp_peak_instance :
    |∑ y ∈ Icc (1 : ℤ) (2 - 1), ((2 : ℝ) ^ (-y) * 1)⁻¹ * ∑ z ∈ Icc (0 : ℤ) y, (2 : ℝ) ^ (-z)
        - (1 + 2⁻¹) / 1 * ∑ y ∈ Icc (1 : ℤ) (2 - 1), ((2 : ℝ) ^ (-y))⁻¹|
      ≤ 0 * ((1 + 2⁻¹) / 1) * ∑ y ∈ Icc (1 : ℤ) (2 - 1), ((2 : ℝ) ^ (-y))⁻¹ := by
  refine bdT_sharp_peak (tp := fun _ => 1) (P := fun z : ℤ => (2 : ℝ) ^ (-z))
    (fun z => zpow_pos two_pos _) (x₂ := 1) (fun y hy => ?_)
  have hy1 : y = 1 := by simp at hy; omega
  subst hy1
  have : Icc (0 : ℤ) 1 = {0, 1} := by decide
  simp [this]

/-! ### Concrete instance -/

/-- **Instance**: for `t⁺ = 1`, `t⁻ = 2` on `[0, 3]` (reflecting at `0`, absorbing at `4`),
(7.4.12) solves the backward equation; with `P_s(x) = 2^{-x}` (detailed balance) the splitting
probability (9.2.50) between `0` and `3` solves its backward equation, and (7.4.17) holds. -/
theorem bd_instance :
    (∀ x : ℤ, 0 ≤ x → x ≤ 3 →
      bdBwd (fun _ => 1) (fun _ => 2) (bdTreflA (fun _ => 1) (fun _ => 2) 0 3) x = -1) ∧
    (∀ x : ℤ, 0 < x → x < 3 → bdBwd (fun _ => (1 : ℝ)) (fun _ => 2)
      (fun y : ℤ => (∑ z ∈ Icc ((0 : ℤ) + 1) y, ((2 : ℝ) ^ (-z) * 2)⁻¹) /
        ∑ z ∈ Icc ((0 : ℤ) + 1) 3, ((2 : ℝ) ^ (-z) * 2)⁻¹) x = 0) ∧
    bdTreflA (fun _ => 1) (fun _ => 2) 0 (4 - 1) 0
      = ∑ y ∈ Icc (0 : ℤ) (4 - 1), ((2 : ℝ) ^ (-y) * 1)⁻¹ * ∑ z ∈ Icc (0 : ℤ) y, (2 : ℝ) ^ (-z) := by
  have hdb : ∀ z : ℤ, (fun _ : ℤ => (2 : ℝ)) z * (fun z : ℤ => (2 : ℝ) ^ (-z)) z
      = (fun _ : ℤ => (1 : ℝ)) (z - 1) * (fun z : ℤ => (2 : ℝ) ^ (-z)) (z - 1) := by
    intro z
    simp only [neg_sub, one_mul]
    rw [show 1 - z = -z + 1 by ring, zpow_add_one₀ two_ne_zero]; ring
  have hP : ∀ z : ℤ, 0 < (fun z : ℤ => (2 : ℝ) ^ (-z)) z := fun z => zpow_pos two_pos _
  refine ⟨(bdT_reflA_spec (fun _ => one_pos) (fun _ => two_pos)).1, ?_, ?_⟩
  · exact (bdSplit_spec (fun _ => one_pos) (fun _ => two_pos) hP hdb (by norm_num)).2.2
  · exact bdT_reflA_stationary (fun _ => one_pos) (fun _ => two_pos) hP hdb le_rfl

end Gardiner.Escape
