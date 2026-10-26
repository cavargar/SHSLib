/-
# Concrete instances of the projector method: telegraph noise in a Fourier mode

Gardiner §6.5.1 notes that the elimination procedure works for any Markov fast process, "in
particular, for example, the random telegraph process in which `α(t)` takes on values `±a`".
For a translation-invariant slow equation, a Fourier mode `e^{ikx}` turns `∂/∂x` into `ik`, so
all operators of §6.4–§6.6 become `2 × 2` matrices acting on `(p₊, p₋)`.  In the coordinates
`ρ = p₊ + p₋`, `j = p₊ - p₋` (on `E = ℂ × ℂ` with the sup norm):

* the flip generator with rate `λ` is `L₁(ρ, j) = (0, -2λj)`, its null space is `j = 0` and the
  projector is `P(ρ, j) = (ρ, 0)` [(6.4.25), (6.5.16)];
* the reduced inverse is `S(ρ, j) = (0, -j/(2λ))`;
* multiplication by `-ikb α` is `L₂ = c · swap`, `c = -ikb`, and `PL₂P = 0` because `⟨α⟩ₛ = 0`
  [(6.5.18)–(6.5.19)];
* a drift `-ik a(α)` is `L₃ = a·id + d·swap` (`a = -ik ā`, `d = -ik δ` with `ā, δ` the mean and
  half-difference of `a(±1)`); it commutes with `P` iff `d = 0`.

Instances proved here (all non-degenerate: `c ≠ 0`, and `d ≠ 0` for the non-commuting one):

* `Gardiner.Adiabatic.tg_projHyp`: the structural hypotheses (6.4.26), (6.4.36), (6.4.41).
* `Gardiner.Adiabatic.tg_kramers_bound`: the persistent random walk (Goldstein–Kac), the
  telegraph analogue of the Kramers problem `γL₁ + L₂`: (6.4.52) holds with an explicit
  `O(γ⁻²)` error; the effective operator is `-c²/(2γ)` per unit `λ = 1`, i.e. diffusion.
* `Gardiner.Adiabatic.tg_whiteNoise_bound`: the white-noise limit (6.5.28) for
  `dx/dt = ā + bγα(γ²t)` with an explicit `O(γ⁻¹)` error.
* `Gardiner.Adiabatic.tg_nonCommuting_bound`: (6.5.70) for an `α`-dependent drift,
  `PL₃ ≠ L₃P` (`Gardiner.Adiabatic.tg_not_commute`).
* `Gardiner.Adiabatic.tg_A`, `…_B`, `…_C`, `…_D`, `Gardiner.Adiabatic.tg_corrected`: the operators
  (6.4.99) for the persistent random walk and the corrected equation (6.4.101).
* `Gardiner.Adiabatic.mat_secondOrder`: a `2 × 2` rational instance of the commutator algebra
  (6.6.90)–(6.6.105) with `PL₃ ≠ L₃P`.
-/
import SHSLib.Gardiner.Adiabatic.ProjectorBound
import SHSLib.Gardiner.Adiabatic.Projector

noncomputable section

namespace Gardiner.Adiabatic

/-- A `2 × 2` matrix acting on `ℂ × ℂ`. -/
def tgOp (m₁₁ m₁₂ m₂₁ m₂₂ : ℂ) : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ where
  toFun x := (m₁₁ * x.1 + m₁₂ * x.2, m₂₁ * x.1 + m₂₂ * x.2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

@[simp] lemma tgOp_apply (m₁₁ m₁₂ m₂₁ m₂₂ : ℂ) (x : ℂ × ℂ) :
    tgOp m₁₁ m₁₂ m₂₁ m₂₂ x = (m₁₁ * x.1 + m₁₂ * x.2, m₂₁ * x.1 + m₂₂ * x.2) := rfl

lemma tgOp_mul (a b c d a' b' c' d' : ℂ) :
    tgOp a b c d * tgOp a' b' c' d'
      = tgOp (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  apply LinearMap.ext; intro x; ext <;> simp <;> ring

lemma tgOp_smul (r a b c d : ℂ) : r • tgOp a b c d = tgOp (r * a) (r * b) (r * c) (r * d) := by
  apply LinearMap.ext; intro x; ext <;> simp <;> ring

lemma tgOp_add (a b c d a' b' c' d' : ℂ) :
    tgOp a b c d + tgOp a' b' c' d' = tgOp (a + a') (b + b') (c + c') (d + d') := by
  apply LinearMap.ext; intro x; ext <;> simp <;> ring

lemma tgOp_neg (a b c d : ℂ) : -tgOp a b c d = tgOp (-a) (-b) (-c) (-d) := by
  apply LinearMap.ext; intro x; ext <;> simp <;> ring

lemma tgOp_one : (1 : Module.End ℂ (ℂ × ℂ)) = tgOp 1 0 0 1 := by
  apply LinearMap.ext; intro x; ext <;> simp

lemma tgOp_zero : (0 : Module.End ℂ (ℂ × ℂ)) = tgOp 0 0 0 0 := by
  apply LinearMap.ext; intro x; ext <;> simp

/-- The projector `P(ρ, j) = (ρ, 0)` of (6.4.25)/(6.5.16) for telegraph noise. -/
def tgP : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ := tgOp 1 0 0 0
/-- The flip generator `L₁(ρ, j) = (0, -2λj)`. -/
def tgL1 (lam : ℝ) : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ := tgOp 0 0 0 (-2 * lam)
/-- The reduced inverse `S(ρ, j) = (0, -j/(2λ))` of `L₁`. -/
def tgS (lam : ℝ) : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ := tgOp 0 0 0 (-1 / (2 * lam))
/-- `L₂ = c · swap`, the Fourier transform of `-b α ∂/∂x` (`c = -ikb`). -/
def tgL2 (c : ℂ) : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ := tgOp 0 c c 0
/-- `L₃ = a · id + d · swap`, the Fourier transform of `-a(α) ∂/∂x`. -/
def tgL3 (a d : ℂ) : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ := tgOp a d d a

lemma norm_prod_le (x : ℂ × ℂ) : ‖x.1‖ ≤ ‖x‖ ∧ ‖x.2‖ ≤ ‖x‖ :=
  ⟨norm_fst_le x, norm_snd_le x⟩

lemma norm_zero_snd (y : ℂ) : ‖((0 : ℂ), y)‖ = ‖y‖ := by simp [Prod.norm_def]

lemma norm_fst_zero (y : ℂ) : ‖(y, (0 : ℂ))‖ = ‖y‖ := by simp [Prod.norm_def]

/-- The structural hypotheses (6.4.26), (6.4.36), (6.4.41) for telegraph noise. -/
theorem tg_projHyp (lam : ℝ) (c : ℂ) : ProjHyp tgP (tgL1 lam) (tgL2 c) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tgP, tgL1, tgL2, tgOp_mul, tgOp_zero] <;> congr 1 <;> ring

/-- An `α`-dependent drift does not commute with the projector: `PL₃ ≠ L₃P` when `d ≠ 0`
[(6.5.66), (6.6.79)]. -/
theorem tg_not_commute (a d : ℂ) (hd : d ≠ 0) : tgP * tgL3 a d ≠ tgL3 a d * tgP := by
  intro h
  have := congrArg (fun T : Module.End ℂ (ℂ × ℂ) => (T (0, 1)).1) h
  simp [tgP, tgL3] at this
  exact hd this

lemma norm_le_of_comp {y : ℂ × ℂ} {B : ℝ} (h1 : ‖y.1‖ ≤ B) (h2 : ‖y.2‖ ≤ B) : ‖y‖ ≤ B := by
  rw [Prod.norm_def]; exact max_le h1 h2

/-- **(6.4.47) ⟹ (6.4.52) for the persistent random walk.**  For `dx/dt = c₀ σ(t)` with `σ = ±1`
flipping at rate `γ`, the Fourier-Laplace transformed split equations with `w(0) = 0` read
`sρ̃ = c j̃ + ρ₀`, `sj̃ = -2γ j̃ + c ρ̃` (`c = -ikc₀`).  For `|γ| ≥ |s| + |c|` (and `γ ≠ 0`),
`|sρ̃ - ρ₀ - γ⁻¹ (c²/2) ρ̃| ≤ |c|² (|s| + |c|)|ρ̃| / (2|γ|²)`;
the retained term `γ⁻¹c²/2 = -k²c₀²/(2γ)` is the diffusion operator of the reduced equation. -/
theorem tg_kramers_bound (c γ s ρ j ρ₀ : ℂ) (hγ0 : γ ≠ 0)
    (hγ : ‖s‖ + ‖c‖ ≤ ‖γ‖)
    (hv : s * ρ = c * j + ρ₀) (hw : s * j = -2 * γ * j + c * ρ) :
    ‖s * ρ - ρ₀ - γ⁻¹ * (c ^ 2 / 2 * ρ)‖ ≤ ‖c‖ ^ 2 * (‖s‖ + ‖c‖) * ‖ρ‖ / (2 * ‖γ‖ ^ 2) := by
  have hb := kramers_laplace_bound tgP (tgL1 1) (tgL2 c) (tgS 1) γ s (ρ, 0) (0, j) (ρ₀, 0)
    (1 / 2) (‖c‖ / 2) ‖c‖ (by norm_num) (by positivity) (norm_nonneg _)
    (fun x hx => by
      have : x.1 = 0 := by simpa [tgP] using congrArg Prod.fst hx
      ext <;> simp [tgS, tgL1, this]; ring)
    (by simp [tgP])
    (by ext <;> simp [tgP, tgL2, hv])
    (by ext <;> simp [tgP, tgL1, tgL2, hw]; ring)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgS]
      · simp [tgS]; have := (norm_prod_le x).2; linarith)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgS, tgL2, tgP]; positivity
      · simp [tgS, tgL2, tgP]
        have := (norm_prod_le x).1
        nlinarith [norm_nonneg c, norm_nonneg x.1])
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgP, tgL2]
        exact mul_le_mul_of_nonneg_left (norm_prod_le x).2 (norm_nonneg c)
      · simp [tgP, tgL2]; positivity)
    hγ0 (by nlinarith [norm_nonneg s, norm_nonneg c])
  obtain ⟨-, h2⟩ := hb
  have e : (s • (ρ, (0 : ℂ)) - (ρ₀, 0)) - γ⁻¹ • (-tgP (tgL2 c (tgS 1 (tgL2 c (ρ, 0)))))
      = (s * ρ - ρ₀ - γ⁻¹ * (c ^ 2 / 2 * ρ), 0) := by
    ext <;> simp [tgP, tgL2, tgS]; ring
  have eS : ‖tgS 1 (tgL2 c (ρ, 0))‖ = ‖c‖ * ‖ρ‖ / 2 := by
    rw [show tgS 1 (tgL2 c (ρ, 0)) = ((0 : ℂ), -(c * ρ) / 2) by ext <;> simp [tgS, tgL2]; ring,
      norm_zero_snd]
    simp
  rw [e, norm_fst_zero, eS] at h2
  refine h2.trans (le_of_eq ?_)
  field_simp

/-- **(6.5.25)–(6.5.28) for telegraph noise, with an explicit `O(γ⁻¹)` error.**  For
`dx/dt = ā + b γ α(γ²t)` with `α = ±1` flipping at rate `λ`, a Fourier–Laplace mode satisfies
(`c = -ikb`, `a = -ikā`, `w(0) = 0`)
`sρ̃ = aρ̃ + γc j̃ + ρ₀`, `sj̃ = -2λγ² j̃ + a j̃ + γc ρ̃`.
Then `sρ̃ - ρ₀ = (a + c²/(2λ))ρ̃ + O(γ⁻¹)`: the reduced equation is the Fokker–Planck equation
`∂ₜp̂ = -ā∂ₓp̂ + (b²/(2λ))∂ₓ²p̂` [(6.5.45) with `D = ∫₀^∞⟨α(t)α(0)⟩dt = 1/(2λ)`]. -/
theorem tg_whiteNoise_bound (lam : ℝ) (hlam : 0 < lam) (a c γ s ρ j ρ₀ : ℂ)
    (hγ1 : 1 ≤ ‖γ‖) (hγ : (‖s‖ + ‖a‖ + ‖c‖) / lam ≤ ‖γ‖)
    (hv : s * ρ = a * ρ + γ * c * j + ρ₀)
    (hw : s * j = -2 * lam * γ ^ 2 * j + a * j + γ * c * ρ) :
    ‖s * ρ - ρ₀ - (a + c ^ 2 / (2 * lam)) * ρ‖
      ≤ ‖c‖ * ((‖s‖ + ‖a‖ + ‖c‖) * (‖c‖ + ‖a‖) / (2 * lam ^ 2) + ‖a‖ / (2 * lam)) * ‖ρ‖
        / ‖γ‖ := by
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have h2l : 0 < 2 * lam := by linarith
  have hb := commuting_laplace_bound tgP (tgL1 lam) (tgL2 c) (tgL3 a 0) (tgS lam) γ s (ρ, 0)
    (0, j) (ρ₀, 0) (1 / (2 * lam)) (‖c‖ / (2 * lam)) (‖a‖ / (2 * lam)) ‖c‖ (by positivity)
    (by positivity) (by positivity) (norm_nonneg _)
    (fun x => by ext <;> simp [tgP, tgL3])
    (fun x hx => by
      have : x.1 = 0 := by simpa [tgP] using congrArg Prod.fst hx
      ext <;> simp [tgS, tgL1, this]; field_simp)
    (by ext <;> simp [tgP]) (by simp [tgP])
    (by ext <;> simp [tgP, tgL2, tgL3, hv]; ring)
    (by ext <;> simp [tgP, tgL1, tgL2, tgL3, hw]; ring)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgS]; positivity
      · simp [tgS]; rw [abs_of_pos hlam]; gcongr; exact (norm_prod_le x).2)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgS, tgL2, tgP]; positivity
      · simp [tgS, tgL2, tgP]; rw [abs_of_pos hlam]
        rw [show lam⁻¹ * 2⁻¹ * (‖c‖ * ‖x.1‖) = ‖c‖ / (2 * lam) * ‖x.1‖ by field_simp]
        gcongr; exact (norm_prod_le x).1)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgS, tgL3, tgP]; positivity
      · simp [tgS, tgL3, tgP]; rw [abs_of_pos hlam]
        rw [show lam⁻¹ * 2⁻¹ * (‖a‖ * ‖x.2‖) = ‖a‖ / (2 * lam) * ‖x.2‖ by field_simp]
        gcongr; exact (norm_prod_le x).2)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgP, tgL2]
        exact mul_le_mul_of_nonneg_left (norm_prod_le x).2 (norm_nonneg c)
      · simp [tgP, tgL2]; positivity)
    hγ1 (by
      calc _ = (‖s‖ + ‖a‖ + ‖c‖) / lam := by field_simp
        _ ≤ _ := hγ)
  have e : s • (ρ, (0 : ℂ)) - (ρ₀, 0) - (tgL3 a 0 (ρ, 0) - tgP (tgL2 c (tgS lam (tgL2 c (ρ, 0)))))
      = (s * ρ - ρ₀ - (a + c ^ 2 / (2 * lam)) * ρ, 0) := by
    ext <;> simp [tgP, tgL2, tgL3, tgS]; field_simp; ring
  have eS : tgS lam (tgL2 c (ρ, 0)) = ((0 : ℂ), -(c * ρ) / (2 * lam)) := by
    ext <;> simp [tgL2, tgS]; field_simp
  rw [e, eS, norm_fst_zero, norm_zero_snd, norm_fst_zero] at hb
  refine hb.trans (le_of_eq ?_)
  have h2 : ‖(2 : ℂ) * lam‖ = 2 * lam := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]; norm_num
  rw [norm_div, norm_neg, norm_mul, h2]
  field_simp

/-- **(6.5.67)–(6.5.70) with `PL₃ ≠ L₃P`, explicit `O(γ⁻¹)` error.**  For
`dx/dt = a(α) + bγα(γ²t)` with telegraph `α` the drift operator `L₃ = a·id + d·swap` does not
commute with `P` when `d ≠ 0` (`Gardiner.Adiabatic.tg_not_commute`), and the transformed
equations acquire the extra terms `d j̃` and `d ρ̃`.  Still
`sρ̃ - ρ₀ = (a + c²/(2λ))ρ̃ + O(γ⁻¹)`: only the average drift `ā` survives, as in (6.6.86). -/
theorem tg_nonCommuting_bound (lam : ℝ) (hlam : 0 < lam) (a d c γ s ρ j ρ₀ : ℂ)
    (hγ1 : 1 ≤ ‖γ‖) (hγ : (‖s‖ + (‖a‖ + ‖d‖) + ‖c‖) / lam ≤ ‖γ‖)
    (hv : s * ρ = a * ρ + γ * c * j + d * j + ρ₀)
    (hw : s * j = -2 * lam * γ ^ 2 * j + a * j + γ * c * ρ + d * ρ) :
    ‖s * ρ - ρ₀ - (a + c ^ 2 / (2 * lam)) * ρ‖
      ≤ (‖c‖ * ((‖s‖ + (‖a‖ + ‖d‖) + ‖c‖) * (‖c‖ + (‖a‖ + ‖d‖)) / (2 * lam ^ 2)
          + (‖a‖ + ‖d‖) / (2 * lam)) + ‖d‖ * (‖c‖ + (‖a‖ + ‖d‖)) / lam) * ‖ρ‖ / ‖γ‖ := by
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have h2l : 0 < 2 * lam := by linarith
  have hb := threeScale_laplace_bound tgP (tgL1 lam) (tgL2 c) (tgL3 a d) (tgS lam) γ s (ρ, 0)
    (0, j) (ρ₀, 0) (1 / (2 * lam)) (‖c‖ / (2 * lam)) ((‖a‖ + ‖d‖) / (2 * lam)) ‖c‖ ‖d‖
    (by positivity) (by positivity) (by positivity) (norm_nonneg _) (norm_nonneg _)
    (fun x hx => by
      have : x.1 = 0 := by simpa [tgP] using congrArg Prod.fst hx
      ext <;> simp [tgS, tgL1, this]; field_simp)
    (by simp [tgP])
    (by ext <;> simp [tgP, tgL2, tgL3, hv]; ring)
    (by ext <;> simp [tgP, tgL1, tgL2, tgL3, hw]; ring)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgS]; positivity
      · simp [tgS]; rw [abs_of_pos hlam]; gcongr; exact (norm_prod_le x).2)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgS, tgL2, tgP]; positivity
      · simp [tgS, tgL2, tgP]; rw [abs_of_pos hlam]
        rw [show lam⁻¹ * 2⁻¹ * (‖c‖ * ‖x.1‖) = ‖c‖ / (2 * lam) * ‖x.1‖ by field_simp]
        gcongr; exact (norm_prod_le x).1)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgS, tgL3, tgP]; positivity
      · simp [tgS, tgL3, tgP]; rw [abs_of_pos hlam]
        have h1 := (norm_prod_le x).1
        have h2 := (norm_prod_le x).2
        calc lam⁻¹ * 2⁻¹ * ‖d * x.1 + a * x.2‖ ≤ lam⁻¹ * 2⁻¹ * (‖d‖ * ‖x‖ + ‖a‖ * ‖x‖) := by
              gcongr
              refine (norm_add_le _ _).trans ?_
              rw [norm_mul, norm_mul]; gcongr
          _ = (‖a‖ + ‖d‖) / (2 * lam) * ‖x‖ := by field_simp; ring)
    (fun x => by
      refine norm_le_of_comp ?_ ?_
      · simp [tgP, tgL2]
        exact mul_le_mul_of_nonneg_left (norm_prod_le x).2 (norm_nonneg c)
      · simp [tgP, tgL2]; positivity)
    (by rw [show tgP (tgL3 a d (0, j)) = (d * j, 0) by ext <;> simp [tgP, tgL3], norm_fst_zero,
      norm_zero_snd, norm_mul])
    hγ1 (by
      calc _ = (‖s‖ + (‖a‖ + ‖d‖) + ‖c‖) / lam := by field_simp
        _ ≤ _ := hγ)
  have e : s • (ρ, (0 : ℂ)) - (ρ₀, 0) - (tgP (tgL3 a d (ρ, 0)) - tgP (tgL2 c (tgS lam (tgL2 c (ρ, 0)))))
      = (s * ρ - ρ₀ - (a + c ^ 2 / (2 * lam)) * ρ, 0) := by
    ext <;> simp [tgP, tgL2, tgL3, tgS]; field_simp; ring
  have eS : tgS lam (tgL2 c (ρ, 0)) = ((0 : ℂ), -(c * ρ) / (2 * lam)) := by
    ext <;> simp [tgL2, tgS]; field_simp
  rw [e, eS, norm_fst_zero, norm_zero_snd, norm_fst_zero] at hb
  refine hb.trans (le_of_eq ?_)
  have h2 : ‖(2 : ℂ) * lam‖ = 2 * lam := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]; norm_num
  rw [norm_div, norm_neg, norm_mul, h2]
  field_simp

/-! ### The operators (6.4.99) and the corrected equation (6.4.101) for the persistent walk -/

/-- `Q = 1 - P` in the telegraph model. -/
lemma tg_Q : (1 : Module.End ℂ (ℂ × ℂ)) - tgP = tgOp 0 0 0 1 := by
  rw [tgOp_one, tgP]; apply LinearMap.ext; intro x; ext <;> simp

/-- (6.4.99), `A = -PL₂L₁⁻¹L₂ = (c²/2) P` for the persistent random walk (`λ = 1`); with
`c = -ikc₀` this is `-k²c₀²/2`, the diffusion operator. -/
theorem tg_A (c : ℂ) : -(tgP * tgL2 c * tgS 1 * tgL2 c) = tgOp (c ^ 2 / 2) 0 0 0 := by
  simp only [tgP, tgL2, tgS, tgOp_mul, tgOp_neg]; congr 1 <;> push_cast <;> ring

/-- (6.4.104): `B = PL₂L₁⁻¹(1 - P)L₂L₁⁻¹L₂ = 0`. -/
theorem tg_B (c : ℂ) : tgP * tgL2 c * tgS 1 * (1 - tgP) * tgL2 c * tgS 1 * tgL2 c = 0 := by
  rw [tg_Q, tgOp_zero]; simp only [tgP, tgL2, tgS, tgOp_mul]; congr 1 <;> ring

/-- (6.4.99): `C = -PL₂L₁⁻¹(1-P)L₂L₁⁻¹(1-P)L₂L₁⁻¹L₂ = 0` for the persistent walk. -/
theorem tg_C (c : ℂ) :
    -(tgP * tgL2 c * tgS 1 * (1 - tgP) * tgL2 c * tgS 1 * (1 - tgP) * tgL2 c * tgS 1 * tgL2 c)
      = 0 := by
  rw [tg_Q, tgOp_zero]; simp only [tgP, tgL2, tgS, tgOp_mul, tgOp_neg]; congr 1 <;> ring

/-- (6.4.99): `D = -PL₂L₁⁻²L₂ = -(c²/4) P`. -/
theorem tg_D (c : ℂ) : -(tgP * tgL2 c * tgS 1 * tgS 1 * tgL2 c) = tgOp (-(c ^ 2 / 4)) 0 0 0 := by
  simp only [tgP, tgL2, tgS, tgOp_mul, tgOp_neg]; congr 1 <;> push_cast <;> ring

/-- The inverse `-(2 + ε²s₂)⁻¹ Q` of `L₁ + ε(1 - P)L₂ - ε²s₂` on the range of `S`. -/
def tgY (ε s₂ : ℂ) : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ := tgOp 0 0 0 (-(2 + ε ^ 2 * s₂)⁻¹)

lemma tg_L1S : tgL1 1 * tgS 1 = 1 - tgP := by
  rw [tg_Q]; simp only [tgL1, tgS, tgOp_mul]; congr 1 <;> push_cast <;> ring

lemma tg_YQ (ε s₂ : ℂ) : tgY ε s₂ * (1 - tgP) = tgY ε s₂ := by
  rw [tg_Q]; simp only [tgY, tgOp_mul]; congr 1 <;> ring

lemma tg_Yinv (c ε s₂ : ℂ) (h : 2 + ε ^ 2 * s₂ ≠ 0) :
    tgY ε s₂ * (tgL1 1 + ε • ((1 - tgP) * tgL2 c - (ε * s₂) • (1 : Module.End ℂ (ℂ × ℂ))))
      * tgS 1 = tgS 1 := by
  rw [tg_Q, tgOp_one]
  simp only [tgY, tgL1, tgS, tgL2, tgOp_mul, tgOp_smul, tgOp_add, sub_eq_add_neg, tgOp_neg]
  congr 1 <;> push_cast <;> field_simp <;> ring

/-- **(6.4.94)–(6.4.99) for the persistent walk.**  The exact inverse of
`L₁ + ε(1 - P)L₂ - ε²s₂` on the range of `S` is `Y = -(2 + ε²s₂)⁻¹ Q`, and the effective operator
`-PL₂YL₂ = c²/(2 + ε²s₂)` has the expansion `A + εB + ε²(C + s₂D) + ε³R₃` of
`Gardiner.Adiabatic.longTime_expansion`, i.e. `c²/2 - ε²s₂c²/4 + O(ε³)`. -/
theorem tg_longTime (c ε s₂ : ℂ) (h : 2 + ε ^ 2 * s₂ ≠ 0) :
    -(tgP * tgL2 c * tgY ε s₂ * tgL2 c) = tgOp (c ^ 2 / (2 + ε ^ 2 * s₂)) 0 0 0 ∧
    -(tgP * tgL2 c * tgY ε s₂ * tgL2 c)
      = -(tgP * tgL2 c * tgS 1 * tgL2 c) + ε • (tgP * tgL2 c * tgS 1 * (1 - tgP) * tgL2 c * tgS 1 * tgL2 c)
        + ε ^ 2 • (-(tgP * tgL2 c * tgS 1 * (1 - tgP) * tgL2 c * tgS 1 * (1 - tgP) * tgL2 c
            * tgS 1 * tgL2 c) + s₂ • (-(tgP * tgL2 c * tgS 1 * tgS 1 * tgL2 c)))
        + ε ^ 3 • (s₂ • (tgP * tgL2 c * tgS 1 * (1 - tgP) * tgL2 c * tgS 1 * tgS 1 * tgL2 c
            + tgP * tgL2 c * tgS 1 * tgS 1 * (1 - tgP) * tgL2 c * tgS 1 * tgL2 c)
          - (ε * s₂ ^ 2) • (tgP * tgL2 c * tgS 1 * tgS 1 * tgS 1 * tgL2 c)
          + tgP * tgL2 c * (tgY ε s₂ * ((1 - tgP) * tgL2 c - (ε * s₂) • 1) * tgS 1
            * ((1 - tgP) * tgL2 c - (ε * s₂) • 1) * tgS 1
            * ((1 - tgP) * tgL2 c - (ε * s₂) • 1) * tgS 1) * tgL2 c) := by
  have key := longTime_expansion (𝕜 := ℂ) (R := Module.End ℂ (ℂ × ℂ)) tgP (1 - tgP) (tgL1 1)
    (tgL2 c) (tgS 1) (tgY ε s₂) ε s₂ tg_L1S (tg_Yinv c ε s₂ h) (tg_YQ ε s₂)
  refine ⟨?_, by with_reducible_and_instances exact key⟩
  simp only [tgY, tgP, tgL2, tgOp_mul, tgOp_neg]; congr 1 <;> field_simp <;> ring

/-- **(6.4.100)–(6.4.101) for the persistent walk**: the corrected equation with the modified
initial condition.  If `s₂(1 - ε²D)ṽ = Aṽ + v(0)` (here `B = C = 0`, `A = c²/2`, `D = -c²/4`),
then `s₂ṽ = (A + ε²DA)ṽ + (1 + ε²D)v(0) + ε³(εs₂D²)ṽ`, obtained from
`Gardiner.Adiabatic.longTime_rearranged`. -/
theorem tg_corrected (c ε s₂ ρ ρ₀ : ℂ)
    (h : s₂ * ((1 + ε ^ 2 * (c ^ 2 / 4)) * ρ) = c ^ 2 / 2 * ρ + ρ₀) :
    s₂ * ρ = (c ^ 2 / 2 + ε ^ 2 * (-(c ^ 2 / 4) * (c ^ 2 / 2))) * ρ
      + (1 + ε ^ 2 * (-(c ^ 2 / 4))) * ρ₀ + ε ^ 3 * (ε * s₂ * (c ^ 2 / 4) ^ 2 * ρ) := by
  have key := longTime_rearranged (𝕜 := ℂ) (R := Module.End ℂ (ℂ × ℂ)) (M := ℂ × ℂ)
    (tgOp (c ^ 2 / 2) 0 0 0) 0 0 (tgOp (-(c ^ 2 / 4)) 0 0 0) ε s₂ (ρ, 0) (ρ₀, 0)
    (by
      rw [tgOp_one]
      ext <;> simp [tgOp_smul, tgOp_add, sub_eq_add_neg, tgOp_neg]
      linear_combination h)
  have := congrArg Prod.fst key
  simp [tgOp_mul, tgOp_smul, tgOp_add, tgOp_one] at this
  linear_combination this

/-! ### A matrix instance of the commutator algebra (6.6.88)–(6.6.105) -/

/-- A rank-one projector `P = u wᵀ` (`u = (1,1)`, `w = (1,0)`). -/
def mP : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 1, 0]
/-- `L₁` with `PL₁ = L₁P = 0`. -/
def mL1 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, -1]
/-- `L₂` with `PL₂P = 0`. -/
def mL2 : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; 0, 0]
/-- `L₃` with `PL₃P = PL₃` but `PL₃ ≠ L₃P`. -/
def mL3 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]
/-- A reduced inverse `G` with `PG = GP = 0`. -/
def mG : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; -1, 1]

theorem mat_projHyp : ProjHyp mP mL1 mL2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [mP, mL1, mL2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat_not_commute : mP * mL3 ≠ mL3 * mP := by
  intro h
  have := congrFun (congrFun h 1) 0
  simp [mP, mL3, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- **(6.6.90)–(6.6.105) on a concrete instance with `PL₃ ≠ L₃P`**: for `v = Pv` the
second-order term `P(L₂ + L₃)G[L₂ + (1 - P)L₃]v` equals `PL₂G{L₂ + [L₃, P]}v`. -/
theorem mat_secondOrder :
    (mP * (mL2 + mL3) * mG * (mL2 + (1 - mP) * mL3)) • mP
      = (mP * mL2 * mG * (mL2 + (mL3 * mP - mP * mL3))) • mP := by
  rw [secondOrder_commutator_form mat_projHyp mG
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [mG, mP, Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [mG, mP, Matrix.mul_apply, Fin.sum_univ_two])
    mP (by rw [smul_eq_mul]; exact mat_projHyp.idem),
    secondOrder_reduced mat_projHyp
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [mL3, mP, Matrix.mul_apply, Fin.sum_univ_two])]

end Gardiner.Adiabatic
