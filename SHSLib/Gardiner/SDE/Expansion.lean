/-
# The expansion algebra of the small-noise expansion (Gardiner (6.2.3)–(6.2.9), (6.2.19)–(6.2.20))

Gardiner §6.2 substitutes `x = x₀ + εx₁ + ε²x₂ + …` into a coefficient function `a(x)` and
collects powers of `ε`:

  `a(x₀ + Σ_{m≥1} εᵐ xₘ) = Σₙ εⁿ aₙ(x₀, …, xₙ)`                                (6.2.3)–(6.2.5)

This involves no noise at all.  We formalize it in full generality, for an arbitrary sequence of
"derivatives" `D p` (in applications `D p = a⁽ᵖ⁾(x₀)`):

* `Gardiner.SDE.pertPoly X n = Σ_{m=1}^n Xₘ εᵐ` (a polynomial in `ε`);
* `Gardiner.SDE.snCoeff D X n` — the coefficient of `εⁿ` in `Σ_{p≤n} (D p/p!) (Σ_{m=1}^n Xₘεᵐ)ᵖ`,
  i.e. Gardiner's `aₙ(x₀, …, xₙ)` (6.2.5);
* `Gardiner.SDE.snCoeff_congr`: `aₙ` only depends on `X₁, …, Xₙ`;
* `Gardiner.SDE.snCoeff_zero` … `Gardiner.SDE.snCoeff_three`: the explicit table (6.2.6);
* `Gardiner.SDE.snCoeff_split`: the structure (6.2.7), `aₙ = xₙ a'(x₀) + Aₙ(x₀, …, xₙ₋₁)` for
  `n ≥ 1`, with `Aₙ = Gardiner.SDE.snA D X n` independent of `xₙ`
  (`Gardiner.SDE.snA_indep`);
* `Gardiner.SDE.snCoeff_stable`: the coefficients do not change if the series is truncated later
  or a remainder `ε^{N+1} Y` is added — this is what makes (6.2.19) well defined;
* `Gardiner.SDE.expansion_remainder`: **the asymptotic property (6.2.20) with an explicit
  constant**.  If `a` has a derivative tower up to order `N + 1` bounded by `M` on the ball of
  radius `(N+1)R` about `X₀`, and `|Xₘ|, |Y| ≤ R`, then for `|ε| ≤ 1`

    `|a(X₀ + Σ_{m=1}^N εᵐXₘ + ε^{N+1}Y) - Σ_{n=0}^N εⁿ aₙ(X)| ≤ 2M e^{(N+1)R} |ε|^{N+1}`,

  i.e. `|â_{N+1}[X₀, …, X_N, Y, ε]| ≤ 2M e^{(N+1)R}` uniformly — the boundedness of Gardiner's
  `â_{n+1}` (6.2.19) that (6.2.20) requires, uniformly on bounded sets.

The same function `snCoeff` gives the expansion (6.2.8) of the noise coefficient `b`.
-/
import SHSLib.Gardiner.Approx.Calculus

open Polynomial Finset
open scoped Nat

noncomputable section

namespace Gardiner.SDE

/-! ### The formal coefficients `aₙ` -/

/-- The perturbation `Σ_{m=1}^n Xₘ εᵐ` as a polynomial in `ε`. -/
def pertPoly (X : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ m ∈ Icc 1 n, C (X m) * Polynomial.X ^ m

/-- The truncated formal Taylor composition `Σ_{p ≤ N} (D p / p!) Hᵖ` (6.2.5). -/
def compPoly (D : ℕ → ℝ) (H : ℝ[X]) (N : ℕ) : ℝ[X] :=
  ∑ p ∈ range (N + 1), C (D p / (p ! : ℝ)) * H ^ p

/-- (6.2.4)–(6.2.5): Gardiner's `aₙ(x₀, x₁, …, xₙ)`, the coefficient of `εⁿ` in
`a(x₀ + Σ_{m≥1} εᵐ xₘ)`, where `D p` stands for `a⁽ᵖ⁾(x₀)`. -/
def snCoeff (D : ℕ → ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  (compPoly D (pertPoly X n) n).coeff n

/-- (6.2.7): Gardiner's `Aₙ(x₀, …, xₙ₋₁)`: `aₙ` with `xₙ` set to zero. -/
def snA (D : ℕ → ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ := snCoeff D (Function.update X n 0) n

lemma pertPoly_coeff_zero (X : ℕ → ℝ) (n : ℕ) : (pertPoly X n).coeff 0 = 0 := by
  simp only [pertPoly, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  refine Finset.sum_eq_zero fun m hm => ?_
  have : m ≠ 0 := by simp at hm; omega
  simp [Ne.symm this]

lemma X_dvd_of_coeff_zero {P : ℝ[X]} (h : P.coeff 0 = 0) : Polynomial.X ∣ P :=
  Polynomial.X_dvd_iff.mpr h

lemma coeff_eq_of_X_pow_dvd_sub {P Q : ℝ[X]} {n : ℕ} (h : Polynomial.X ^ (n + 1) ∣ P - Q) :
    P.coeff n = Q.coeff n := by
  have := (Polynomial.X_pow_dvd_iff.mp h) n (Nat.lt_succ_self n)
  simpa [sub_eq_zero] using this

lemma coeff_pow_eq_zero_of_lt {H : ℝ[X]} (hH : H.coeff 0 = 0) {p n : ℕ} (hn : n < p) :
    (H ^ p).coeff n = 0 := by
  have hd : Polynomial.X ^ p ∣ H ^ p := pow_dvd_pow_of_dvd (X_dvd_of_coeff_zero hH) p
  exact (Polynomial.X_pow_dvd_iff.mp hd) n hn

/-- Coefficient stability: if `H` agrees with `Σ_{m=1}^n Xₘεᵐ` up to order `n` (and has no
constant term), the coefficient of `εⁿ` in `Σ_{p≤N} (D p/p!) Hᵖ` is `aₙ(X)` for every `N ≥ n`. -/
theorem snCoeff_stable (D : ℕ → ℝ) (X : ℕ → ℝ) (H : ℝ[X]) {n N : ℕ} (hnN : n ≤ N)
    (hH0 : H.coeff 0 = 0) (hH : ∀ m, 1 ≤ m → m ≤ n → H.coeff m = X m) :
    (compPoly D H N).coeff n = snCoeff D X n := by
  set P := pertPoly X n
  have hP0 : P.coeff 0 = 0 := pertPoly_coeff_zero X n
  -- `H - P` is divisible by `X^{n+1}`
  have hdiff : Polynomial.X ^ (n + 1) ∣ H - P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [coeff_sub]
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · rw [hH0, hP0, sub_zero]
    · rw [hH d hd0 (by omega)]
      simp only [P, pertPoly, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
      rw [Finset.sum_eq_single d]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exfalso; exact h (by simp; omega)
  have hpow : ∀ p, Polynomial.X ^ (n + 1) ∣ H ^ p - P ^ p := fun p =>
    dvd_trans hdiff (sub_dvd_pow_sub_pow H P p)
  simp only [compPoly, snCoeff, finset_sum_coeff]
  have hsplit : ∑ p ∈ range (N + 1), (C (D p / (p ! : ℝ)) * H ^ p).coeff n =
      ∑ p ∈ range (n + 1), (C (D p / (p ! : ℝ)) * H ^ p).coeff n := by
    symm
    refine Finset.sum_subset (by intro p hp; simp at hp ⊢; omega) ?_
    intro p _ hp
    simp at hp
    rw [coeff_C_mul, coeff_pow_eq_zero_of_lt hH0 (by omega), mul_zero]
  rw [hsplit]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_C_mul, coeff_C_mul, coeff_eq_of_X_pow_dvd_sub (hpow p)]

/-- `aₙ` only depends on `x₁, …, xₙ` (and on `x₀` through `D`). -/
theorem snCoeff_congr (D : ℕ → ℝ) {X X' : ℕ → ℝ} (n : ℕ)
    (h : ∀ m, 1 ≤ m → m ≤ n → X m = X' m) : snCoeff D X n = snCoeff D X' n := by
  have : pertPoly X n = pertPoly X' n := by
    unfold pertPoly
    refine Finset.sum_congr rfl fun m hm => ?_
    simp at hm
    rw [h m hm.1 hm.2]
  unfold snCoeff
  rw [this]

/-- (6.2.6), `n = 0`: `a₀(x₀) = a(x₀)`. -/
theorem snCoeff_zero (D X : ℕ → ℝ) : snCoeff D X 0 = D 0 := by
  simp [snCoeff, compPoly, pertPoly]

lemma pertPoly_succ (X : ℕ → ℝ) (n : ℕ) :
    pertPoly X (n + 1) = pertPoly X n + C (X (n + 1)) * Polynomial.X ^ (n + 1) := by
  unfold pertPoly
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- (6.2.7): for `n ≥ 1`, `aₙ(x₀, …, xₙ) = xₙ a'(x₀) + Aₙ(x₀, …, xₙ₋₁)`. -/
theorem snCoeff_split (D X : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    snCoeff D X n = X n * D 1 + snA D X n := by
  set X' := Function.update X n 0
  set H := pertPoly X n
  set H' := pertPoly X' n
  have hHH : H = H' + C (X n) * Polynomial.X ^ n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [H, H', pertPoly_succ]
    have : pertPoly X k = pertPoly X' k := by
      unfold pertPoly
      refine Finset.sum_congr rfl fun m hm => ?_
      simp at hm
      simp [X', show m ≠ k + 1 by omega]
    rw [this]; simp [X']
  have hH0 : H.coeff 0 = 0 := pertPoly_coeff_zero X n
  have hH'0 : H'.coeff 0 = 0 := pertPoly_coeff_zero X' n
  unfold snA snCoeff compPoly
  rw [finset_sum_coeff, finset_sum_coeff]
  -- compare term by term
  have hterm : ∀ p ∈ range (n + 1), (C (D p / (p ! : ℝ)) * H ^ p).coeff n =
      (C (D p / (p ! : ℝ)) * H' ^ p).coeff n + (if p = 1 then X n * D 1 else 0) := by
    intro p _
    rw [coeff_C_mul, coeff_C_mul]
    rcases Nat.lt_or_ge p 2 with hp | hp
    · interval_cases p
      · simp
      · simp [hHH, coeff_C_mul, coeff_X_pow]; ring
    · -- for `p ≥ 2` the difference `Hᵖ - H'ᵖ` is divisible by `X^{n+1}`
      have hX : Polynomial.X ∣ H := X_dvd_of_coeff_zero hH0
      have hX' : Polynomial.X ∣ H' := X_dvd_of_coeff_zero hH'0
      have hd : Polynomial.X ^ (n + 1) ∣ H ^ p - H' ^ p := by
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
        have hfac : H ^ (q + 2) - H' ^ (q + 2) =
            (H - H') * ∑ i ∈ range (q + 2), H ^ i * H' ^ (q + 1 - i) := by
          rw [← Commute.mul_geom_sum₂ (Commute.all H H')]
          rfl
        rw [hfac, pow_succ]
        refine mul_dvd_mul ?_ ?_
        · rw [hHH]; simp
        · refine Finset.dvd_sum fun i hi => ?_
          simp at hi
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · simpa using dvd_pow hX' (by omega : q + 1 - 0 ≠ 0)
          · exact dvd_mul_of_dvd_left (dvd_pow hX (by omega)) _
      rw [coeff_eq_of_X_pow_dvd_sub hd, if_neg (by omega), add_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [mem_range, show 1 < n + 1 by omega, if_true]
  ring

/-- `Aₙ` is independent of `xₙ`. -/
theorem snA_indep (D X : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    snA D (Function.update X n c) n = snA D X n := by
  unfold snA
  rw [Function.update_idem]

/-- (6.2.6), `n = 1`: `a₁(x₀, x₁) = x₁ a'(x₀)`. -/
theorem snCoeff_one (D X : ℕ → ℝ) : snCoeff D X 1 = X 1 * D 1 := by
  rw [snCoeff_split D X le_rfl]
  have : snA D X 1 = snCoeff D (Function.update X 1 0) 1 := rfl
  rw [this]
  simp [snCoeff, compPoly, pertPoly, Finset.sum_range_succ]

/-- (6.2.6), `n = 2`: `a₂ = x₂ a'(x₀) + ½ x₁² a''(x₀)`. -/
theorem snCoeff_two (D X : ℕ → ℝ) :
    snCoeff D X 2 = X 2 * D 1 + X 1 ^ 2 / 2 * D 2 := by
  rw [snCoeff_split D X (by norm_num)]
  congr 1
  unfold snA snCoeff compPoly pertPoly
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [show Icc 1 2 = {1, 2} by decide]
  simp [Function.update, coeff_X, pow_two,
    Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
  ring

/-- (6.2.6), `n = 3`: `a₃ = x₃ a'(x₀) + x₁x₂ a''(x₀) + (1/6) x₁³ a'''(x₀)`. -/
theorem snCoeff_three (D X : ℕ → ℝ) :
    snCoeff D X 3 = X 3 * D 1 + X 1 * X 2 * D 2 + X 1 ^ 3 / 6 * D 3 := by
  rw [snCoeff_split D X (by norm_num), add_assoc]
  congr 1
  unfold snA snCoeff compPoly pertPoly
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [show Icc 1 3 = {1, 2, 3} by decide]
  simp [Function.update, coeff_X, pow_succ,
    Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, Nat.factorial]
  ring

/-! ### Coefficient majorants and the tail of a polynomial -/

/-- Coefficient majorants are preserved by products. -/
lemma coeff_mul_majorant {A B Ahat Bhat : ℝ[X]} (hA : ∀ n, |A.coeff n| ≤ Ahat.coeff n)
    (hB : ∀ n, |B.coeff n| ≤ Bhat.coeff n) (n : ℕ) :
    |(A * B).coeff n| ≤ (Ahat * Bhat).coeff n := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hA _) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hA _))

lemma coeff_pow_majorant {H Hhat : ℝ[X]} (hH : ∀ n, |H.coeff n| ≤ Hhat.coeff n)
    (hHhat : ∀ n, 0 ≤ Hhat.coeff n) (p : ℕ) :
    (∀ n, |(H ^ p).coeff n| ≤ (Hhat ^ p).coeff n) ∧ (∀ n, 0 ≤ (Hhat ^ p).coeff n) := by
  induction p with
  | zero =>
    refine ⟨fun n => ?_, fun n => ?_⟩ <;>
      · simp only [pow_zero, coeff_one]; split_ifs <;> simp
  | succ p ih =>
    refine ⟨fun n => ?_, fun n => ?_⟩
    · rw [pow_succ, pow_succ]; exact coeff_mul_majorant ih.1 hH n
    · rw [pow_succ, Polynomial.coeff_mul]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (ih.2 _) (hHhat _)

/-- The tail `Σ_{n > N} cₙ εⁿ` of a polynomial is at most `|ε|^{N+1} Σ |cₙ|` for `|ε| ≤ 1`, and
the sum of absolute values of the coefficients is bounded by the value at `1` of any
coefficient majorant. -/
lemma eval_sub_trunc_le (P Phat : ℝ[X]) (hP : ∀ n, |P.coeff n| ≤ Phat.coeff n) (N : ℕ) {ε : ℝ}
    (hε : |ε| ≤ 1) :
    |P.eval ε - ∑ n ∈ range (N + 1), P.coeff n * ε ^ n| ≤ |ε| ^ (N + 1) * Phat.eval 1 := by
  set L := max (N + 1) (max P.natDegree Phat.natDegree + 1)
  have hL1 : N + 1 ≤ L := le_max_left _ _
  have hLP : P.natDegree < L := by
    have := le_max_right (N + 1) (max P.natDegree Phat.natDegree + 1)
    have := le_max_left P.natDegree Phat.natDegree; omega
  have hLPhat : Phat.natDegree < L := by
    have := le_max_right (N + 1) (max P.natDegree Phat.natDegree + 1)
    have := le_max_right P.natDegree Phat.natDegree; omega
  rw [eval_eq_sum_range' hLP, eval_eq_sum_range' hLPhat]
  rw [← Finset.sum_range_add_sum_Ico _ hL1, add_sub_cancel_left]
  have hPhat0 : ∀ n, 0 ≤ Phat.coeff n := fun n => (abs_nonneg _).trans (hP n)
  calc |∑ n ∈ Ico (N + 1) L, P.coeff n * ε ^ n|
      ≤ ∑ n ∈ Ico (N + 1) L, |P.coeff n * ε ^ n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ico (N + 1) L, |ε| ^ (N + 1) * Phat.coeff n := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp at hn
        rw [abs_mul, abs_pow, mul_comm]
        refine mul_le_mul ?_ (hP n) (abs_nonneg _) (by positivity)
        exact pow_le_pow_of_le_one (abs_nonneg _) hε hn.1
    _ = |ε| ^ (N + 1) * ∑ n ∈ Ico (N + 1) L, Phat.coeff n := by rw [Finset.mul_sum]
    _ ≤ |ε| ^ (N + 1) * ∑ n ∈ range L, Phat.coeff n * 1 ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simp only [one_pow, mul_one]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro n; simp only [Finset.mem_Ico, Finset.mem_range]; omega)
          (fun n _ _ => hPhat0 n)

/-! ### The asymptotic property (6.2.19)–(6.2.20) with an explicit constant -/

/-- The perturbation including the remainder term, `Σ_{m=1}^N Xₘ εᵐ + Y ε^{N+1}`. -/
def pertPolyY (X : ℕ → ℝ) (Y : ℝ) (N : ℕ) : ℝ[X] :=
  pertPoly X N + C Y * Polynomial.X ^ (N + 1)

/-- Its coefficient majorant. -/
def pertPolyAbs (X : ℕ → ℝ) (Y : ℝ) (N : ℕ) : ℝ[X] :=
  pertPoly (fun m => |X m|) N + C |Y| * Polynomial.X ^ (N + 1)

lemma pertPoly_coeff (X : ℕ → ℝ) (n m : ℕ) :
    (pertPoly X n).coeff m = if 1 ≤ m ∧ m ≤ n then X m else 0 := by
  simp only [pertPoly, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hm; exfalso; exact hm (by simp; omega)
  · refine Finset.sum_eq_zero fun b hb => ?_
    simp at hb
    have : m ≠ b := by rintro rfl; exact h ⟨hb.1, hb.2⟩
    simp [this]

lemma pertPolyY_coeff (X : ℕ → ℝ) (Y : ℝ) (N m : ℕ) :
    (pertPolyY X Y N).coeff m =
      (if 1 ≤ m ∧ m ≤ N then X m else 0) + (if m = N + 1 then Y else 0) := by
  rw [pertPolyY, coeff_add, pertPoly_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

lemma pertPolyAbs_coeff (X : ℕ → ℝ) (Y : ℝ) (N m : ℕ) :
    (pertPolyAbs X Y N).coeff m =
      (if 1 ≤ m ∧ m ≤ N then |X m| else 0) + (if m = N + 1 then |Y| else 0) := by
  rw [pertPolyAbs, coeff_add, pertPoly_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

lemma pertPolyAbs_majorant (X : ℕ → ℝ) (Y : ℝ) (N : ℕ) :
    (∀ m, |(pertPolyY X Y N).coeff m| ≤ (pertPolyAbs X Y N).coeff m) ∧
    (∀ m, 0 ≤ (pertPolyAbs X Y N).coeff m) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · rw [pertPolyY_coeff, pertPolyAbs_coeff]
    by_cases h1 : 1 ≤ m ∧ m ≤ N <;> by_cases h2 : m = N + 1
    · omega
    · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]; simp
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]; simp
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; simp
  · rw [pertPolyAbs_coeff]
    exact add_nonneg (by split_ifs <;> simp) (by split_ifs <;> simp)

lemma pertPolyY_eval (X : ℕ → ℝ) (Y : ℝ) (N : ℕ) (ε : ℝ) :
    (pertPolyY X Y N).eval ε = ∑ m ∈ Icc 1 N, X m * ε ^ m + Y * ε ^ (N + 1) := by
  simp [pertPolyY, pertPoly, eval_finset_sum]

lemma pertPolyAbs_eval_one (X : ℕ → ℝ) (Y : ℝ) (N : ℕ) :
    (pertPolyAbs X Y N).eval 1 = ∑ m ∈ Icc 1 N, |X m| + |Y| := by
  simp [pertPolyAbs, pertPoly, eval_finset_sum]

lemma abs_pertPolyY_eval_le (X : ℕ → ℝ) (Y : ℝ) (N : ℕ) {ε R : ℝ} (hε : |ε| ≤ 1)
    (hX : ∀ m, 1 ≤ m → m ≤ N → |X m| ≤ R) (hY : |Y| ≤ R) :
    |(pertPolyY X Y N).eval ε| ≤ |ε| * ((N + 1) * R) := by
  rw [pertPolyY_eval]
  have hR : 0 ≤ R := (abs_nonneg _).trans hY
  calc |∑ m ∈ Icc 1 N, X m * ε ^ m + Y * ε ^ (N + 1)|
      ≤ ∑ m ∈ Icc 1 N, |X m * ε ^ m| + |Y * ε ^ (N + 1)| :=
        (abs_add_le _ _).trans (add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _)
    _ ≤ ∑ m ∈ Icc 1 N, |ε| * R + |ε| * R := by
        gcongr with m hm
        · simp at hm
          rw [abs_mul, abs_pow, mul_comm]
          refine mul_le_mul ?_ (hX m hm.1 hm.2) (abs_nonneg _) (abs_nonneg _)
          calc |ε| ^ m ≤ |ε| ^ 1 := pow_le_pow_of_le_one (abs_nonneg _) hε hm.1
            _ = |ε| := pow_one _
        · rw [abs_mul, abs_pow, mul_comm]
          refine mul_le_mul ?_ hY (abs_nonneg _) (abs_nonneg _)
          calc |ε| ^ (N + 1) ≤ |ε| ^ 1 := pow_le_pow_of_le_one (abs_nonneg _) hε (by omega)
            _ = |ε| := pow_one _
    _ = |ε| * ((N + 1) * R) := by simp; ring

lemma sum_pow_div_factorial_le_exp (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    ∑ p ∈ range (N + 1), r ^ p / (p ! : ℝ) ≤ Real.exp r :=
  Real.sum_le_exp_of_nonneg hr (N + 1)

lemma pow_div_factorial_le_exp (r : ℝ) (hr : 0 ≤ r) (n : ℕ) : r ^ n / (n ! : ℝ) ≤ Real.exp r := by
  have := Real.sum_le_exp_of_nonneg hr (n + 1)
  refine le_trans ?_ this
  rw [Finset.sum_range_succ]
  have : 0 ≤ ∑ p ∈ range n, r ^ p / (p ! : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  linarith

/-- **(6.2.19)–(6.2.20) with an explicit constant.**  Let `Da` be a derivative tower of `a`
(`Da 0 = a`, `(Da k)' = Da (k+1)` for `k ≤ N`), bounded by `M` for orders `≤ N + 1` on the ball of
radius `(N + 1)R` around `X₀`.  If `|Xₘ| ≤ R` (`1 ≤ m ≤ N`), `|Y| ≤ R` and `|ε| ≤ 1`, then

  `|a(X₀ + Σ_{m=1}^N εᵐXₘ + ε^{N+1}Y) - Σ_{n=0}^N εⁿ aₙ(X₀, …, Xₙ)| ≤ 2M e^{(N+1)R} |ε|^{N+1}`,

where `aₙ = snCoeff (fun p => Da p X₀) X n`. -/
theorem expansion_remainder (N : ℕ) (Da : ℕ → ℝ → ℝ)
    (hDa : ∀ k ≤ N, ∀ y, HasDerivAt (Da k) (Da (k + 1) y) y)
    (X : ℕ → ℝ) (Y : ℝ) {R M ε : ℝ} (hε : |ε| ≤ 1)
    (hX : ∀ m, 1 ≤ m → m ≤ N → |X m| ≤ R) (hY : |Y| ≤ R)
    (hM : ∀ p ≤ N + 1, ∀ z, |z - X 0| ≤ (N + 1) * R → |Da p z| ≤ M) :
    |Da 0 (X 0 + ∑ m ∈ Icc 1 N, X m * ε ^ m + Y * ε ^ (N + 1)) -
        ∑ n ∈ range (N + 1), snCoeff (fun p => Da p (X 0)) X n * ε ^ n|
      ≤ 2 * M * Real.exp ((N + 1) * R) * |ε| ^ (N + 1) := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hY
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by omega) (X 0) (by simp; positivity))
  set D : ℕ → ℝ := fun p => Da p (X 0)
  set H := pertPolyY X Y N
  set h := H.eval ε
  set r : ℝ := (N + 1) * R
  have hr : 0 ≤ r := by positivity
  have hh : |h| ≤ |ε| * r := abs_pertPolyY_eval_le X Y N hε hX hY
  have hhr : |h| ≤ r := hh.trans (by nlinarith [abs_nonneg ε])
  have heval : X 0 + ∑ m ∈ Icc 1 N, X m * ε ^ m + Y * ε ^ (N + 1) = X 0 + h := by
    simp only [h, H, pertPolyY_eval]; ring
  rw [heval]
  -- Taylor part
  have hT : |Da 0 (X 0 + h) - taylorTower Da N (X 0) h| ≤ M * |h| ^ (N + 1) / ((N + 1)! : ℝ) := by
    refine taylor_tower_bound N Da (X 0) h M hDa fun t ht => hM (N + 1) le_rfl _ ?_
    simp only [add_sub_cancel_left]
    rcases le_total 0 h with h0 | h0
    · rw [Set.uIcc_of_le h0] at ht
      rw [abs_of_nonneg ht.1]; exact ht.2.trans ((le_abs_self h).trans hhr)
    · rw [Set.uIcc_of_ge h0] at ht
      rw [abs_of_nonpos ht.2]
      have : |h| = -h := abs_of_nonpos h0
      linarith [ht.1]
  -- the Taylor polynomial is the evaluation of `compPoly`
  have htay : taylorTower Da N (X 0) h = (compPoly D H N).eval ε := by
    simp only [taylorTower, compPoly, eval_finset_sum, eval_mul, eval_C, eval_pow, D, h]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  -- the truncation is given by the coefficients `aₙ`
  have hcoef : ∀ n ∈ range (N + 1), snCoeff D X n * ε ^ n = (compPoly D H N).coeff n * ε ^ n := by
    intro n hn
    simp at hn
    rw [snCoeff_stable D X H (by omega)]
    · rw [pertPolyY_coeff]; simp
    · intro m hm1 hm2
      rw [pertPolyY_coeff]; simp [hm1, show m ≤ N by omega, show m ≠ N + 1 by omega]
  -- majorant of `compPoly D H N`
  set Hhat := pertPolyAbs X Y N
  have hmaj := pertPolyAbs_majorant X Y N
  set Phat : ℝ[X] := ∑ p ∈ range (N + 1), C (|D p| / (p ! : ℝ)) * Hhat ^ p
  have hPmaj : ∀ n, |(compPoly D H N).coeff n| ≤ Phat.coeff n := by
    intro n
    simp only [compPoly, Phat, finset_sum_coeff, coeff_C_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p ! : ℝ))]
    exact mul_le_mul_of_nonneg_left ((coeff_pow_majorant hmaj.1 hmaj.2 p).1 n) (by positivity)
  have hHhat1 : Hhat.eval 1 ≤ r := by
    rw [pertPolyAbs_eval_one]
    calc ∑ m ∈ Icc 1 N, |X m| + |Y| ≤ ∑ m ∈ Icc 1 N, R + R := by
          gcongr with m hm; simp at hm; exact hX m hm.1 hm.2
      _ = r := by simp [r]; ring
  have hHhat0 : 0 ≤ Hhat.eval 1 := by
    rw [pertPolyAbs_eval_one]; positivity
  have hPhat1 : Phat.eval 1 ≤ M * Real.exp r := by
    simp only [Phat, eval_finset_sum, eval_mul, eval_C, eval_pow]
    calc ∑ p ∈ range (N + 1), |D p| / (p ! : ℝ) * Hhat.eval 1 ^ p
        ≤ ∑ p ∈ range (N + 1), M * (r ^ p / (p ! : ℝ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          simp at hp
          have h1 : |D p| ≤ M := hM p (by omega) (X 0) (by simp; positivity)
          rw [div_mul_eq_mul_div, mul_div_assoc]
          exact mul_le_mul h1 (div_le_div_of_nonneg_right (pow_le_pow_left₀ hHhat0 hHhat1 p)
            (by positivity)) (by positivity) hM0
      _ = M * ∑ p ∈ range (N + 1), r ^ p / (p ! : ℝ) := by rw [Finset.mul_sum]
      _ ≤ M * Real.exp r := mul_le_mul_of_nonneg_left (sum_pow_div_factorial_le_exp r hr N) hM0
  have htail := eval_sub_trunc_le (compPoly D H N) Phat hPmaj N hε
  rw [Finset.sum_congr rfl hcoef]
  calc |Da 0 (X 0 + h) - ∑ n ∈ range (N + 1), (compPoly D H N).coeff n * ε ^ n|
      ≤ |Da 0 (X 0 + h) - taylorTower Da N (X 0) h| +
        |(compPoly D H N).eval ε - ∑ n ∈ range (N + 1), (compPoly D H N).coeff n * ε ^ n| := by
        rw [← htay]; exact abs_sub_le _ _ _
    _ ≤ M * |h| ^ (N + 1) / ((N + 1)! : ℝ) + |ε| ^ (N + 1) * (M * Real.exp r) :=
        add_le_add hT (htail.trans (mul_le_mul_of_nonneg_left hPhat1 (by positivity)))
    _ ≤ M * Real.exp r * |ε| ^ (N + 1) + |ε| ^ (N + 1) * (M * Real.exp r) := by
        gcongr
        calc M * |h| ^ (N + 1) / ((N + 1)! : ℝ) ≤ M * (|ε| * r) ^ (N + 1) / ((N + 1)! : ℝ) := by
              gcongr
          _ = M * (r ^ (N + 1) / ((N + 1)! : ℝ)) * |ε| ^ (N + 1) := by rw [mul_pow]; ring
          _ ≤ M * Real.exp r * |ε| ^ (N + 1) := by
              gcongr; exact pow_div_factorial_le_exp r hr (N + 1)
    _ = 2 * M * Real.exp ((N + 1) * R) * |ε| ^ (N + 1) := by simp only [r]; ring

end Gardiner.SDE
