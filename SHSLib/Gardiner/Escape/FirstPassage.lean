/-
# Mean first-passage times and exit probabilities in one dimension: §5.2.7–5.2.8

Gardiner, *Handbook of Stochastic Methods*, (5.2.139)–(5.2.190), for the homogeneous backward
operator `A(x)∂ₓ + ½B(x)∂ₓ²` with `A`, `B` continuous and `B > 0`.

The ODE layer is exact.  A function `u` *solves the backward equation with right-hand side `f`*
(`IsBwdSol A B f u`) if it is twice differentiable everywhere with
`A u' + ½ B u'' = f`.  With `ψ(x) = exp ∫_a^x 2A/B` (5.2.157), `Φ(x) = ∫_a^x 1/ψ`,
`I_f(y) = ∫_a^y ψ f/B` and `K_f(x) = ∫_a^x I_f/ψ`:

* `flux_deriv` — the key identity `(ψ u')' = (2ψ/B)(A u' + ½ B u'')`;
* `combo_isBwdSol` — `c₀ + c₁Φ - 2K_f` solves `A u' + ½Bu'' = -f` (all solutions are of this form);
* `bwd_unique`, `bwd_unique_refl_a`, `bwd_unique_refl_b` — uniqueness under the boundary
  conditions (5.2.155), (5.2.159), and their mirror images;
* `mfptTwo_spec` — **(5.2.154)–(5.2.155), (5.2.158)**, two absorbing barriers;
* `mfptReflA_spec` — **(5.2.160)**, reflecting at `a`; `mfptReflB_spec` — **(5.2.161)**;
* `exitA_spec` — **(5.2.186)–(5.2.189)** (corrected: `1/ψ`, not `ψ`), `exitA_add_exitB`
  **(5.2.188)**; `exitA_printed_wrong` shows the printed (5.2.189) fails;
* `condExit_spec` — **(5.2.183)–(5.2.185)** solved, the general form of (9.1.24);
  `condExit_add` — `π_a T(a,x) + π_b T(b,x) = T(x)`;
* `moment_ibp` — the integration by parts behind (5.2.149)–(5.2.152), giving
  `⟨Tⁿ⟩ = n ∫₀^∞ t^{n-1} G dt`; `moments_printed_wrong` shows the printed (5.2.152) (without the
  factor `n`) fails for `G = e^{-t}`;
* `mfpt_ode_of_backward` — (5.2.153)–(5.2.154) from (5.2.144), with the interchange of `∂ₓ`
  and `∫₀^∞ dt` as named hypotheses;
  `condExit_ode_of_backward` — (5.2.177)–(5.2.183) likewise; `backward_ode_instance`;
* `ou_exit_instance` — the Ornstein–Uhlenbeck process on `(-1, 1)`;
* `smolReflA_eq` — for the Smoluchowski equation (5.2.162) (`A = -U'`, `B = 2D`), (5.2.160)
  becomes `D⁻¹∫_x^b e^{U/D} ∫_a^y e^{-U/D}`, whose `a → -∞` limit is (5.2.165), i.e.
  `Gardiner.Escape.mfptBarrier` (`smolReflA_tendsto`; instance `doubleWell_reflect_limit`).
-/
import SHSLib.Gardiner.Escape.Kramers

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Gardiner.Escape

/-- `u` solves the backward equation `A u' + ½ B u'' = f` (twice differentiable on `ℝ`). -/
def IsBwdSol (A B f u : ℝ → ℝ) : Prop :=
  ∃ u1 u2 : ℝ → ℝ, ∀ x, HasDerivAt u (u1 x) x ∧ HasDerivAt u1 (u2 x) x ∧
    A x * u1 x + B x / 2 * u2 x = f x

/-- `ψ(x) = exp ∫_a^x 2A/B` (5.2.157). -/
def fpPsi (A B : ℝ → ℝ) (a x : ℝ) : ℝ := exp (∫ t in a..x, 2 * A t / B t)

/-- `Φ(x) = ∫_a^x dy/ψ(y)`. -/
def fpPhi (A B : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ y in a..x, (fpPsi A B a y)⁻¹

/-- `I_f(y) = ∫_a^y ψ(z) f(z)/B(z) dz`. -/
def fpI (A B f : ℝ → ℝ) (a y : ℝ) : ℝ := ∫ z in a..y, fpPsi A B a z * f z / B z

/-- `K_f(x) = ∫_a^x I_f(y)/ψ(y) dy`. -/
def fpK (A B f : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ y in a..x, (fpPsi A B a y)⁻¹ * fpI A B f a y

lemma fpPsi_pos (A B : ℝ → ℝ) (a x : ℝ) : 0 < fpPsi A B a x := exp_pos _

section ode

variable {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B) (hBpos : ∀ x, 0 < B x)
include hA hB hBpos

lemma cont_drift : Continuous fun t => 2 * A t / B t :=
  Continuous.div (by fun_prop) hB (fun t => (hBpos t).ne')

lemma fpPsi_hasDerivAt (a x : ℝ) :
    HasDerivAt (fpPsi A B a) (2 * A x / B x * fpPsi A B a x) x := by
  have h := ((cont_drift hA hB hBpos).integral_hasStrictDerivAt a x).hasDerivAt
  have := h.exp
  rw [mul_comm] at this
  exact this

lemma fpPsi_cont (a : ℝ) : Continuous (fpPsi A B a) :=
  continuous_iff_continuousAt.mpr fun x => (fpPsi_hasDerivAt hA hB hBpos a x).continuousAt

lemma fpPsi_inv_cont (a : ℝ) : Continuous fun y => (fpPsi A B a y)⁻¹ :=
  (fpPsi_cont hA hB hBpos a).inv₀ (fun y => (fpPsi_pos A B a y).ne')

lemma fpPhi_hasDerivAt (a x : ℝ) : HasDerivAt (fpPhi A B a) (fpPsi A B a x)⁻¹ x :=
  ((fpPsi_inv_cont hA hB hBpos a).integral_hasStrictDerivAt a x).hasDerivAt

/-- **(ψ u')' = (2ψ/B)(A u' + ½ B u'').** -/
theorem flux_deriv (a : ℝ) {u1 u2 : ℝ → ℝ} {x : ℝ} (h1 : HasDerivAt u1 (u2 x) x) :
    HasDerivAt (fun y => fpPsi A B a y * u1 y)
      (2 * fpPsi A B a x / B x * (A x * u1 x + B x / 2 * u2 x)) x := by
  have := (fpPsi_hasDerivAt hA hB hBpos a x).mul h1
  convert this using 1
  have := (hBpos x).ne'
  field_simp

variable {f : ℝ → ℝ} (hf : Continuous f)
include hf

lemma fpI_cont_integrand (a : ℝ) : Continuous fun z => fpPsi A B a z * f z / B z :=
  Continuous.div ((fpPsi_cont hA hB hBpos a).mul hf) hB (fun t => (hBpos t).ne')

lemma fpI_hasDerivAt (a y : ℝ) :
    HasDerivAt (fpI A B f a) (fpPsi A B a y * f y / B y) y :=
  ((fpI_cont_integrand hA hB hBpos hf a).integral_hasStrictDerivAt a y).hasDerivAt

lemma fpI_cont (a : ℝ) : Continuous (fpI A B f a) :=
  continuous_iff_continuousAt.mpr fun x => (fpI_hasDerivAt hA hB hBpos hf a x).continuousAt

lemma fpK_hasDerivAt (a x : ℝ) :
    HasDerivAt (fpK A B f a) ((fpPsi A B a x)⁻¹ * fpI A B f a x) x :=
  (((fpPsi_inv_cont hA hB hBpos a).mul (fpI_cont hA hB hBpos hf a)).integral_hasStrictDerivAt
    a x).hasDerivAt

/-- **General solution.**  `u = c₀ + c₁Φ - 2K_f` solves `A u' + ½ B u'' = -f`, with
`u' = ψ⁻¹(c₁ - 2 I_f)`. -/
theorem combo_isBwdSol (a c₀ c₁ : ℝ) :
    IsBwdSol A B (fun x => -f x) (fun x => c₀ + c₁ * fpPhi A B a x - 2 * fpK A B f a x) := by
  refine ⟨fun x => (fpPsi A B a x)⁻¹ * (c₁ - 2 * fpI A B f a x),
    fun x => -(2 * A x / B x) * (fpPsi A B a x)⁻¹ * (c₁ - 2 * fpI A B f a x) - 2 * f x / B x,
    fun x => ⟨?_, ?_, ?_⟩⟩
  · have := ((fpPhi_hasDerivAt hA hB hBpos a x).const_mul c₁).const_add c₀ |>.sub
      ((fpK_hasDerivAt hA hB hBpos hf a x).const_mul 2)
    convert this using 1; ring
  · have hψ := fpPsi_hasDerivAt hA hB hBpos a x
    have hψ0 := (fpPsi_pos A B a x).ne'
    have hinv := hψ.inv hψ0
    have hI := ((fpI_hasDerivAt hA hB hBpos hf a x).const_mul 2).const_sub c₁
    have := hinv.mul hI
    convert this using 1
    have := (hBpos x).ne'
    simp only [Pi.inv_apply]
    field_simp
    ring
  · have := (hBpos x).ne'
    have := (fpPsi_pos A B a x).ne'
    field_simp
    ring

end ode

section unique

variable {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B) (hBpos : ∀ x, 0 < B x)
include hA hB hBpos

/-- Homogeneous solutions are `u(a) + cΦ`. -/
lemma homog_form (a : ℝ) {u : ℝ → ℝ} (hu : IsBwdSol A B (fun _ => 0) u) :
    ∃ c, (∀ x, u x = u a + c * fpPhi A B a x) ∧ ∀ u1 : ℝ → ℝ, (∀ x, HasDerivAt u (u1 x) x) →
      ∀ x, u1 x = c * (fpPsi A B a x)⁻¹ := by
  obtain ⟨u1, u2, h⟩ := hu
  set ψ := fpPsi A B a
  have hflux : ∀ x, HasDerivAt (fun y => ψ y * u1 y) 0 x := by
    intro x
    have := flux_deriv hA hB hBpos a (h x).2.1
    rw [(h x).2.2, mul_zero] at this
    exact this
  have hconst : ∀ x, ψ x * u1 x = ψ a * u1 a := fun x =>
    is_const_of_deriv_eq_zero (fun y => (hflux y).differentiableAt)
      (fun y => (hflux y).deriv) x a
  set c := ψ a * u1 a
  have hu1 : ∀ x, u1 x = c * (ψ x)⁻¹ := by
    intro x
    have hx : ψ x ≠ 0 := (fpPsi_pos A B a x).ne'
    rw [← hconst x]; field_simp
  refine ⟨c, ?_, ?_⟩
  · have hd : ∀ x, HasDerivAt (fun y => u y - c * fpPhi A B a y) 0 x := by
      intro x
      have := (h x).1.sub ((fpPhi_hasDerivAt hA hB hBpos a x).const_mul c)
      rw [hu1 x, sub_self] at this
      exact this
    intro x
    have := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).deriv) x a
    have hΦa : fpPhi A B a a = 0 := intervalIntegral.integral_same
    rw [hΦa, mul_zero, sub_zero] at this
    linarith
  · intro v1 hv1 x
    rw [((h x).1.unique (hv1 x)).symm]; exact hu1 x

lemma fpPhi_pos {a b : ℝ} (hab : a < b) : 0 < fpPhi A B a b :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((fpPsi_inv_cont hA hB hBpos a).intervalIntegrable _ _)
    (fun y _ => inv_pos.mpr (fpPsi_pos A B a y)) hab

omit hA hB hBpos in
lemma isBwdSol_sub {f g u v : ℝ → ℝ} (hu : IsBwdSol A B f u) (hv : IsBwdSol A B g v) :
    IsBwdSol A B (fun x => f x - g x) (fun x => u x - v x) := by
  obtain ⟨u1, u2, hu⟩ := hu
  obtain ⟨v1, v2, hv⟩ := hv
  refine ⟨fun x => u1 x - v1 x, fun x => u2 x - v2 x, fun x =>
    ⟨(hu x).1.sub (hv x).1, (hu x).2.1.sub (hv x).2.1, ?_⟩⟩
  show A x * (u1 x - v1 x) + B x / 2 * (u2 x - v2 x) = f x - g x
  rw [← (hu x).2.2, ← (hv x).2.2]; ring

omit hA hB hBpos in
lemma isBwdSol_add {f g u v : ℝ → ℝ} (hu : IsBwdSol A B f u) (hv : IsBwdSol A B g v) :
    IsBwdSol A B (fun x => f x + g x) (fun x => u x + v x) := by
  obtain ⟨u1, u2, hu⟩ := hu
  obtain ⟨v1, v2, hv⟩ := hv
  refine ⟨fun x => u1 x + v1 x, fun x => u2 x + v2 x, fun x =>
    ⟨(hu x).1.add (hv x).1, (hu x).2.1.add (hv x).2.1, ?_⟩⟩
  show A x * (u1 x + v1 x) + B x / 2 * (u2 x + v2 x) = f x + g x
  rw [← (hu x).2.2, ← (hv x).2.2]; ring

/-- **Uniqueness with two absorbing barriers** (5.2.155): two solutions of
`A u' + ½ B u'' = f` that agree at `a < b` agree everywhere. -/
theorem bwd_unique {a b : ℝ} (hab : a < b) {f u v : ℝ → ℝ} (hu : IsBwdSol A B f u)
    (hv : IsBwdSol A B f v) (ha : u a = v a) (hb : u b = v b) : u = v := by
  have hw : IsBwdSol A B (fun _ => 0) (fun x => u x - v x) := by
    have := isBwdSol_sub hu hv
    simpa only [sub_self] using this
  obtain ⟨c, hc, -⟩ := homog_form hA hB hBpos a hw
  have hΦ := fpPhi_pos hA hB hBpos (A := A) (B := B) hab
  have h0 : c = 0 := by
    have := hc b
    simp only [ha, hb, sub_self, zero_add] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd h hΦ.ne'
  ext x
  have := hc x
  simp only [ha, sub_self, h0, zero_mul, add_zero] at this
  linarith

/-- **Uniqueness with `a` reflecting, `b` absorbing** (5.2.159): agreement at `b` and of the
derivatives at `a`. -/
theorem bwd_unique_refl_a {a b : ℝ} {f u v : ℝ → ℝ} (hu : IsBwdSol A B f u)
    (hv : IsBwdSol A B f v) (ha : deriv u a = deriv v a) (hb : u b = v b) : u = v := by
  have hw : IsBwdSol A B (fun _ => 0) (fun x => u x - v x) := by
    have := isBwdSol_sub hu hv
    simpa only [sub_self] using this
  obtain ⟨u1, u2, hu'⟩ := hu
  obtain ⟨v1, v2, hv'⟩ := hv
  obtain ⟨c, hc, hc'⟩ := homog_form hA hB hBpos a hw
  have hd := hc' (fun x => u1 x - v1 x) (fun x => (hu' x).1.sub (hv' x).1) a
  rw [(hu' a).1.deriv, (hv' a).1.deriv] at ha
  rw [ha, sub_self] at hd
  have h0 : c = 0 := by
    rcases mul_eq_zero.mp hd.symm with h | h
    · exact h
    · exact absurd h (inv_pos.mpr (fpPsi_pos A B a a)).ne'
  have hb' := hc b
  simp only [hb, sub_self, h0, zero_mul, add_zero] at hb'
  ext x
  have := hc x
  simp only [h0, zero_mul, add_zero] at this
  linarith

/-- **Uniqueness with `a` absorbing, `b` reflecting.** -/
theorem bwd_unique_refl_b {a b : ℝ} {f u v : ℝ → ℝ} (hu : IsBwdSol A B f u)
    (hv : IsBwdSol A B f v) (ha : u a = v a) (hb : deriv u b = deriv v b) : u = v := by
  have hw : IsBwdSol A B (fun _ => 0) (fun x => u x - v x) := by
    have := isBwdSol_sub hu hv
    simpa only [sub_self] using this
  obtain ⟨u1, u2, hu'⟩ := hu
  obtain ⟨v1, v2, hv'⟩ := hv
  obtain ⟨c, hc, hc'⟩ := homog_form hA hB hBpos a hw
  have hd := hc' (fun x => u1 x - v1 x) (fun x => (hu' x).1.sub (hv' x).1) b
  rw [(hu' b).1.deriv, (hv' b).1.deriv] at hb
  rw [hb, sub_self] at hd
  have h0 : c = 0 := by
    rcases mul_eq_zero.mp hd.symm with h | h
    · exact h
    · exact absurd h (inv_pos.mpr (fpPsi_pos A B a b)).ne'
  ext x
  have := hc x
  simp only [ha, sub_self, h0, zero_mul, add_zero] at this
  linarith

end unique

/-! ### The explicit solutions -/

/-- The Green-function solution of `A u' + ½ B u'' = -f`, `u(a) = u(b) = 0`:
`u = 2[Φ(x) K_f(b)/Φ(b) - K_f(x)]`. -/
def greenSol (A B f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  2 * (fpPhi A B a x * fpK A B f a b / fpPhi A B a b - fpK A B f a x)

/-- **(5.2.158)** as printed: the mean exit time from `(a, b)` with two absorbing barriers. -/
def mfptTwo (A B : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  2 * ((∫ y in a..x, (fpPsi A B a y)⁻¹) *
      (∫ y' in x..b, (fpPsi A B a y')⁻¹ * ∫ z in a..y', fpPsi A B a z / B z) -
    (∫ y in x..b, (fpPsi A B a y)⁻¹) *
      (∫ y' in a..x, (fpPsi A B a y')⁻¹ * ∫ z in a..y', fpPsi A B a z / B z)) /
    ∫ y in a..b, (fpPsi A B a y)⁻¹

/-- **(5.2.160)**: `a` reflecting, `b` absorbing. -/
def mfptReflA (A B : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  2 * ∫ y in x..b, (fpPsi A B a y)⁻¹ * ∫ z in a..y, fpPsi A B a z / B z

/-- **(5.2.161)**: `a` absorbing, `b` reflecting. -/
def mfptReflB (A B : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  2 * ∫ y in a..x, (fpPsi A B a y)⁻¹ * ∫ z in y..b, fpPsi A B a z / B z

/-- **(5.2.189), corrected**: probability of exit through `a`,
`π_a(x) = ∫_x^b ψ⁻¹ / ∫_a^b ψ⁻¹`. -/
def exitA (A B : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  (∫ y in x..b, (fpPsi A B a y)⁻¹) / ∫ y in a..b, (fpPsi A B a y)⁻¹

/-- **(5.2.190), corrected**: probability of exit through `b`. -/
def exitB (A B : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  (∫ y in a..x, (fpPsi A B a y)⁻¹) / ∫ y in a..b, (fpPsi A B a y)⁻¹

/-- (5.2.189) **as printed** (with `ψ` in place of `1/ψ`). -/
def exitAPrinted (A B : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  (∫ y in x..b, fpPsi A B a y) / ∫ y in a..b, fpPsi A B a y

lemma ii {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) : IntervalIntegrable g volume a b :=
  hg.intervalIntegrable a b

lemma fpI_one (A B : ℝ → ℝ) (a y : ℝ) :
    fpI A B (fun _ => 1) a y = ∫ z in a..y, fpPsi A B a z / B z := by
  simp only [fpI, mul_one]

lemma fpK_zero (A B : ℝ → ℝ) (a x : ℝ) : fpK A B (fun _ => 0) a x = 0 := by
  simp [fpK, fpI]

lemma greenSol_eq_combo (A B f : ℝ → ℝ) (a b : ℝ) :
    greenSol A B f a b = fun x => 0 + (2 * fpK A B f a b / fpPhi A B a b) * fpPhi A B a x
      - 2 * fpK A B f a x := by
  ext x; simp only [greenSol]; ring

section solutions

variable {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B) (hBpos : ∀ x, 0 < B x)
include hA hB hBpos

lemma combo_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (a c₀ c₁ x : ℝ) :
    HasDerivAt (fun x => c₀ + c₁ * fpPhi A B a x - 2 * fpK A B f a x)
      ((fpPsi A B a x)⁻¹ * (c₁ - 2 * fpI A B f a x)) x := by
  have := ((fpPhi_hasDerivAt hA hB hBpos a x).const_mul c₁).const_add c₀ |>.sub
    ((fpK_hasDerivAt hA hB hBpos hf a x).const_mul 2)
  convert this using 1; ring

lemma fpK_cont_integrand {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous fun y => (fpPsi A B a y)⁻¹ * fpI A B f a y :=
  (fpPsi_inv_cont hA hB hBpos a).mul (fpI_cont hA hB hBpos hf a)

/-- **The Green-function solution**: `greenSol f` solves `A u' + ½Bu'' = -f` with
`u(a) = u(b) = 0`, and it is the only such solution. -/
theorem greenSol_spec {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    IsBwdSol A B (fun x => -f x) (greenSol A B f a b) ∧ greenSol A B f a b a = 0 ∧
      greenSol A B f a b b = 0 ∧
      ∀ u, IsBwdSol A B (fun x => -f x) u → u a = 0 → u b = 0 → u = greenSol A B f a b := by
  have hΦ := fpPhi_pos hA hB hBpos (A := A) (B := B) hab
  have hsol : IsBwdSol A B (fun x => -f x) (greenSol A B f a b) := by
    rw [greenSol_eq_combo]; exact combo_isBwdSol hA hB hBpos hf a _ _
  have ha : greenSol A B f a b a = 0 := by
    simp [greenSol, fpPhi, fpK]
  have hb : greenSol A B f a b b = 0 := by
    simp only [greenSol]; field_simp; ring
  refine ⟨hsol, ha, hb, fun u hu hua hub => ?_⟩
  exact bwd_unique hA hB hBpos hab hu hsol (by rw [hua, ha]) (by rw [hub, hb])

/-- (5.2.158) is the Green-function solution with `f = 1`. -/
lemma mfptTwo_eq_greenSol {a b : ℝ} (hab : a < b) :
    mfptTwo A B a b = greenSol A B (fun _ => 1) a b := by
  ext x
  have hΦ' : (∫ y in a..b, (fpPsi A B a y)⁻¹) ≠ 0 := (fpPhi_pos hA hB hBpos hab).ne'
  have h1 := intervalIntegral.integral_interval_sub_left
    (ii (fpPsi_inv_cont hA hB hBpos a) a b) (ii (fpPsi_inv_cont hA hB hBpos a) a x)
  have h2 := intervalIntegral.integral_interval_sub_left
    (ii (fpK_cont_integrand hA hB hBpos (f := fun _ => (1:ℝ)) continuous_const a) a b)
    (ii (fpK_cont_integrand hA hB hBpos (f := fun _ => (1:ℝ)) continuous_const a) a x)
  simp only [fpI_one A B] at h2
  simp only [mfptTwo, greenSol, fpPhi, fpK, fpI_one A B]
  rw [← h1, ← h2]
  have alg : ∀ P Q R S : ℝ, P ≠ 0 → 2 * (Q * (R - S) - (P - Q) * S) / P = 2 * (Q * R / P - S) := by
    intro P Q R S hP; field_simp; ring
  exact alg _ _ _ _ hΦ'

/-- **(5.2.154)–(5.2.155), (5.2.158).**  The printed mean exit time with two absorbing
barriers solves `A T' + ½ B T'' = -1`, `T(a) = T(b) = 0`, and is the unique such solution. -/
theorem mfptTwo_spec {a b : ℝ} (hab : a < b) :
    IsBwdSol A B (fun _ => -1) (mfptTwo A B a b) ∧ mfptTwo A B a b a = 0 ∧
      mfptTwo A B a b b = 0 ∧
      ∀ u, IsBwdSol A B (fun _ => -1) u → u a = 0 → u b = 0 → u = mfptTwo A B a b := by
  rw [mfptTwo_eq_greenSol hA hB hBpos hab]
  exact greenSol_spec hA hB hBpos continuous_const hab

/-- **(5.2.160).**  With `a` reflecting and `b` absorbing, `T(x) = 2∫_x^b ψ⁻¹ ∫_a^y ψ/B`
solves `A T' + ½ B T'' = -1`, `T'(a) = 0`, `T(b) = 0` (5.2.159), uniquely. -/
theorem mfptReflA_spec (a b : ℝ) :
    IsBwdSol A B (fun _ => -1) (mfptReflA A B a b) ∧ HasDerivAt (mfptReflA A B a b) 0 a ∧
      mfptReflA A B a b b = 0 ∧
      ∀ u, IsBwdSol A B (fun _ => -1) u → deriv u a = 0 → u b = 0 → u = mfptReflA A B a b := by
  have heq : mfptReflA A B a b =
      fun x => 2 * fpK A B (fun _ => 1) a b + 0 * fpPhi A B a x - 2 * fpK A B (fun _ => 1) a x := by
    ext x
    have h2 := intervalIntegral.integral_interval_sub_left
      (ii (fpK_cont_integrand hA hB hBpos (f := fun _ => (1:ℝ)) continuous_const a) a b)
      (ii (fpK_cont_integrand hA hB hBpos (f := fun _ => (1:ℝ)) continuous_const a) a x)
    simp only [fpI_one A B] at h2
    simp only [mfptReflA, fpK, fpI_one A B]
    rw [← h2]; ring
  have hsol : IsBwdSol A B (fun _ => -1) (mfptReflA A B a b) := by
    rw [heq]; exact combo_isBwdSol hA hB hBpos continuous_const a _ _
  have hder : HasDerivAt (mfptReflA A B a b) 0 a := by
    rw [heq]
    convert combo_hasDerivAt hA hB hBpos continuous_const a _ _ a using 1
    simp [fpI]
  have hb : mfptReflA A B a b b = 0 := by simp [mfptReflA]
  refine ⟨hsol, hder, hb, fun u hu hua hub => ?_⟩
  exact bwd_unique_refl_a hA hB hBpos hu hsol (by rw [hua, hder.deriv]) (by rw [hub, hb])

/-- **(5.2.161).**  With `a` absorbing and `b` reflecting, `T(x) = 2∫_a^x ψ⁻¹ ∫_y^b ψ/B`
solves `A T' + ½ B T'' = -1`, `T(a) = 0`, `T'(b) = 0`, uniquely. -/
theorem mfptReflB_spec (a b : ℝ) :
    IsBwdSol A B (fun _ => -1) (mfptReflB A B a b) ∧ mfptReflB A B a b a = 0 ∧
      HasDerivAt (mfptReflB A B a b) 0 b ∧
      ∀ u, IsBwdSol A B (fun _ => -1) u → u a = 0 → deriv u b = 0 → u = mfptReflB A B a b := by
  have hIc := fpI_cont hA hB hBpos (continuous_const (y := (1 : ℝ))) a
  have heq : mfptReflB A B a b =
      fun x => 0 + 2 * fpI A B (fun _ => 1) a b * fpPhi A B a x
        - 2 * fpK A B (fun _ => 1) a x := by
    ext x
    have hin : ∀ y, ∫ z in y..b, fpPsi A B a z / B z
        = fpI A B (fun _ => 1) a b - fpI A B (fun _ => 1) a y := by
      intro y
      rw [fpI_one A B, fpI_one A B]
      have hc : Continuous fun z => fpPsi A B a z / B z := by
        have := fpI_cont_integrand hA hB hBpos (continuous_const (y := (1 : ℝ))) a
        simpa only [mul_one] using this
      exact (intervalIntegral.integral_interval_sub_left (ii hc a b) (ii hc a y)).symm
    simp only [mfptReflB, hin, fpK, fpPhi]
    rw [show (fun y => (fpPsi A B a y)⁻¹ * (fpI A B (fun _ => 1) a b - fpI A B (fun _ => 1) a y))
        = fun y => fpI A B (fun _ => 1) a b * (fpPsi A B a y)⁻¹
          - (fpPsi A B a y)⁻¹ * fpI A B (fun _ => 1) a y by ext y; ring]
    rw [intervalIntegral.integral_sub
      (ii ((fpPsi_inv_cont hA hB hBpos a).const_smul _ |>.congr (fun _ => smul_eq_mul _ _)) a x)
      (ii (fpK_cont_integrand hA hB hBpos (f := fun _ => (1:ℝ)) continuous_const a) a x),
      intervalIntegral.integral_const_mul]
    ring
  have hsol : IsBwdSol A B (fun _ => -1) (mfptReflB A B a b) := by
    rw [heq]; exact combo_isBwdSol hA hB hBpos continuous_const a _ _
  have hder : HasDerivAt (mfptReflB A B a b) 0 b := by
    rw [heq]
    convert combo_hasDerivAt hA hB hBpos continuous_const a _ _ b using 1
    ring
  have ha : mfptReflB A B a b a = 0 := by simp [mfptReflB]
  refine ⟨hsol, ha, hder, fun u hu hua hub => ?_⟩
  exact bwd_unique_refl_b hA hB hBpos hu hsol (by rw [hua, ha]) (by rw [hub, hder.deriv])

/-- **(5.2.186)–(5.2.189), corrected.**  `π_a(x) = ∫_x^b ψ⁻¹ / ∫_a^b ψ⁻¹` solves
`A π' + ½ B π'' = 0` with `π_a(a) = 1`, `π_a(b) = 0` (5.2.187), uniquely. -/
theorem exitA_spec {a b : ℝ} (hab : a < b) :
    IsBwdSol A B (fun _ => 0) (exitA A B a b) ∧ exitA A B a b a = 1 ∧ exitA A B a b b = 0 ∧
      ∀ u, IsBwdSol A B (fun _ => 0) u → u a = 1 → u b = 0 → u = exitA A B a b := by
  have hΦ := fpPhi_pos hA hB hBpos (A := A) (B := B) hab
  have heq : exitA A B a b = fun x => 1 + (-1 / fpPhi A B a b) * fpPhi A B a x
      - 2 * fpK A B (fun _ => 0) a x := by
    ext x
    have h1 := intervalIntegral.integral_interval_sub_left
      (ii (fpPsi_inv_cont hA hB hBpos a) a b) (ii (fpPsi_inv_cont hA hB hBpos a) a x)
    simp only [exitA, fpK_zero A B, fpPhi]
    rw [← h1]
    have hΦ' : (∫ y in a..b, (fpPsi A B a y)⁻¹) ≠ 0 := hΦ.ne'
    have alg : ∀ P Q : ℝ, P ≠ 0 → (P - Q) / P = 1 + -1 / P * Q - 2 * 0 := by
      intro P Q hP; field_simp; ring
    exact alg _ _ hΦ'
  have hsol : IsBwdSol A B (fun _ => 0) (exitA A B a b) := by
    rw [heq]
    have := combo_isBwdSol hA hB hBpos (f := fun _ => 0) continuous_const a 1 (-1 / fpPhi A B a b)
    simpa only [neg_zero] using this
  have ha : exitA A B a b a = 1 := by
    simp only [exitA]; exact div_self hΦ.ne'
  have hb : exitA A B a b b = 0 := by simp [exitA]
  refine ⟨hsol, ha, hb, fun u hu hua hub => ?_⟩
  exact bwd_unique hA hB hBpos hab hu hsol (by rw [hua, ha]) (by rw [hub, hb])

/-- **(5.2.188)**: `π_a + π_b = 1`. -/
theorem exitA_add_exitB {a b : ℝ} (hab : a < b) (x : ℝ) :
    exitA A B a b x + exitB A B a b x = 1 := by
  have hΦ := fpPhi_pos hA hB hBpos (A := A) (B := B) hab
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (ii (fpPsi_inv_cont hA hB hBpos a) a x) (ii (fpPsi_inv_cont hA hB hBpos a) x b)
  rw [exitA, exitB, ← add_div, add_comm, h1]
  exact div_self hΦ.ne'

lemma exitA_cont (a b : ℝ) : Continuous (exitA A B a b) := by
  have hc : Continuous fun x => ∫ y in x..b, (fpPsi A B a y)⁻¹ := by
    have : (fun x => ∫ y in x..b, (fpPsi A B a y)⁻¹)
        = fun x => -∫ y in b..x, (fpPsi A B a y)⁻¹ := by
      ext x; exact intervalIntegral.integral_symm _ _
    rw [this]
    exact (intervalIntegral.continuous_primitive (fun _ _ => ii (fpPsi_inv_cont hA hB hBpos a) _ _) b).neg
  exact hc.div_const _

/-- **(9.1.24) in general form.**  The solution of (5.2.183)–(5.2.185),
`π_a(x) T(a, x) = greenSol π_a`, equals
`2[π_b(x)(K(b) - K(x)) - π_a(x) K(x)]` with `K = K_{π_a}`: in the Smoluchowski case
(`2/B = 1/D`, `ψ ∝ p_s`) this is exactly Gardiner's (9.1.24) multiplied by `π_a(x)`. -/
theorem greenSol_eq_split {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (x : ℝ) :
    greenSol A B f a b x = 2 * (exitB A B a b x * (fpK A B f a b - fpK A B f a x)
      - exitA A B a b x * fpK A B f a x) := by
  have h := exitA_add_exitB hA hB hBpos hab x
  have hB' : exitB A B a b x = fpPhi A B a x / fpPhi A B a b := rfl
  have hA' : exitA A B a b x = 1 - fpPhi A B a x / fpPhi A B a b := by linarith
  rw [hA', hB', greenSol]; ring

/-- **(5.2.183)–(5.2.185) solved.**  `w = π_a T(a, ·) := greenSol π_a` solves
`A w' + ½ B w'' = -π_a`, `w(a) = w(b) = 0`, uniquely. -/
theorem condExit_spec {a b : ℝ} (hab : a < b) :
    IsBwdSol A B (fun x => -exitA A B a b x) (greenSol A B (exitA A B a b) a b) ∧
      greenSol A B (exitA A B a b) a b a = 0 ∧ greenSol A B (exitA A B a b) a b b = 0 ∧
      ∀ u, IsBwdSol A B (fun x => -exitA A B a b x) u → u a = 0 → u b = 0 →
        u = greenSol A B (exitA A B a b) a b :=
  greenSol_spec hA hB hBpos (exitA_cont hA hB hBpos a b) hab

lemma exitB_cont (a b : ℝ) : Continuous (exitB A B a b) :=
  (intervalIntegral.continuous_primitive (fun _ _ => ii (fpPsi_inv_cont hA hB hBpos a) _ _) a).div_const _

/-- **`π_a T(a, x) + π_b T(b, x) = T(x)`**: the conditional exit times average to the
unconditional mean exit time (5.2.158). -/
theorem condExit_add {a b : ℝ} (hab : a < b) :
    (fun x => greenSol A B (exitA A B a b) a b x + greenSol A B (exitB A B a b) a b x)
      = mfptTwo A B a b := by
  obtain ⟨sA, aA, bA, -⟩ := greenSol_spec hA hB hBpos (exitA_cont hA hB hBpos a b) hab
  obtain ⟨sB, aB, bB, -⟩ := greenSol_spec hA hB hBpos (exitB_cont hA hB hBpos a b) hab
  obtain ⟨-, -, -, huniq⟩ := mfptTwo_spec hA hB hBpos hab
  refine huniq _ ?_ (by rw [aA, aB, add_zero]) (by rw [bA, bB, add_zero])
  have := isBwdSol_add sA sB
  have e : (fun x => -exitA A B a b x + -exitB A B a b x) = fun _ => -1 := by
    ext x; have := exitA_add_exitB hA hB hBpos hab x; linarith
  rwa [e] at this

end solutions

/-! ### Errata: the printed (5.2.189) and (5.2.152) -/

lemma fpPsi_const_drift (x : ℝ) : fpPsi (fun _ => 1) (fun _ => 2) 0 x = exp x := by
  simp [fpPsi]

/-- **Erratum (5.2.189)–(5.2.190).**  With `ψ` in place of `1/ψ` the printed exit probability
does not solve (5.2.186): for `A = 1`, `B = 2` on `(0, 1)` (`ψ(x) = eˣ`), the printed
`π_a(x) = (e - eˣ)/(e - 1)` has `A π' + ½ B π'' = -2eˣ/(e - 1) ≠ 0`. -/
theorem exitA_printed_wrong :
    ¬ IsBwdSol (fun _ => 1) (fun _ => 2) (fun _ => 0)
      (exitAPrinted (fun _ => 1) (fun _ => 2) 0 1) := by
  rintro ⟨u1, u2, h⟩
  have he : (1 : ℝ) < exp 1 := by
    have := add_one_lt_exp (x := (1 : ℝ)) one_ne_zero; linarith
  have hE : exp 1 - 1 ≠ 0 := by linarith
  have hP : exitAPrinted (fun _ => 1) (fun _ => 2) 0 1 = fun x => (exp 1 - exp x) / (exp 1 - 1) := by
    ext x
    simp only [exitAPrinted, fpPsi_const_drift, integral_exp, exp_zero]
  have hd : ∀ x, HasDerivAt (exitAPrinted (fun _ => 1) (fun _ => 2) 0 1)
      (-exp x / (exp 1 - 1)) x := by
    intro x; rw [hP]
    have := ((hasDerivAt_exp x).const_sub (exp 1)).div_const (exp 1 - 1)
    convert this using 1
  have hu1 : u1 = fun x => -exp x / (exp 1 - 1) := by
    ext x; exact (h x).1.unique (hd x)
  have hd2 : ∀ x, HasDerivAt u1 (-exp x / (exp 1 - 1)) x := by
    intro x; rw [hu1]
    have := (hasDerivAt_exp x).neg.div_const (exp 1 - 1)
    convert this using 1
  have h0 := (h 0).2.2
  rw [(h 0).2.1.unique (hd2 0), hu1] at h0
  simp only [exp_zero] at h0
  have : -1 / (exp 1 - 1) < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
  linarith

/-- **(5.2.149)–(5.2.152), corrected.**  If the survival probability `G(t) = Prob(T ≥ t)` is
differentiable on `(0, ∞)`, continuous at `0`, and `tⁿ G(t) → 0`, then
`⟨Tⁿ⟩ = -∫₀^∞ tⁿ ∂ₜG dt = n ∫₀^∞ t^{n-1} G dt`. -/
theorem moment_ibp {G g : ℝ → ℝ} (n : ℕ) (hn : 1 ≤ n)
    (hG : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt G (g t) t) (hG0 : ContinuousWithinAt G (Ioi 0) 0)
    (hint1 : IntegrableOn (fun t => t ^ n * g t) (Ioi 0))
    (hint2 : IntegrableOn (fun t => (n : ℝ) * t ^ (n - 1) * G t) (Ioi 0))
    (hinf : Tendsto (fun t => t ^ n * G t) atTop (𝓝 0)) :
    -∫ t in Ioi (0 : ℝ), t ^ n * g t = n * ∫ t in Ioi (0 : ℝ), t ^ (n - 1) * G t := by
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * t ^ (n - 1)) t :=
    fun t _ => hasDerivAt_pow n t
  have h0 : Tendsto ((fun t : ℝ => t ^ n) * G) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ n) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_pow n).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [zero_pow (by omega : n ≠ 0)] using this
    simpa using h1.mul hG0.tendsto
  have := integral_Ioi_mul_deriv_eq_deriv_mul hu hG hint1 hint2 h0 hinf
  simp only [sub_self, zero_sub] at this
  rw [this, neg_neg, ← integral_const_mul]
  congr 1; ext t; ring

/-- **Erratum (5.2.152).**  The printed `T_n = ∫₀^∞ t^{n-1} G dt` lacks the factor `n`.  For the
exponential survival law `G(t) = e^{-t}`: `⟨T²⟩ = -∫ t² dG = ∫ t² e^{-t} = 2`, while the printed
formula gives `∫ t e^{-t} = 1`. -/
theorem moments_printed_wrong :
    -∫ t in Ioi (0 : ℝ), t ^ 2 * (-exp (-t)) = 2 ∧
      ∫ t in Ioi (0 : ℝ), t ^ (2 - 1) * exp (-t) = 1 := by
  have G3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two]
    norm_num
  have g2 : ∫ x in Ioi (0 : ℝ), exp (-x) * x ^ ((2 : ℝ) - 1) = 1 := by
    rw [← Real.Gamma_eq_integral (by norm_num), Real.Gamma_two]
  have g3 : ∫ x in Ioi (0 : ℝ), exp (-x) * x ^ ((3 : ℝ) - 1) = 2 := by
    rw [← Real.Gamma_eq_integral (by norm_num), G3]
  constructor
  · rw [← integral_neg, ← g3]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]; ring
  · rw [← g2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [show (2 : ℝ) - 1 = ((1 : ℕ) : ℝ) by norm_num, rpow_natCast]; ring

/-- **(5.2.153)–(5.2.154) from (5.2.144).**  Suppose `G(x, ·)` satisfies the backward equation
`∂ₜG = A ∂ₓG + ½ B ∂ₓ²G` on `t > 0` (5.2.144), with `G(x, 0⁺) = 1`, `G(x, ∞) = 0` (5.2.145),
and the (named) interchange hypotheses that `T' = ∫₀^∞ ∂ₓG dt` and `T'' = ∫₀^∞ ∂ₓ²G dt`
for `T = ∫₀^∞ G dt` (5.2.150).  Then `A T' + ½ B T'' = -1` (5.2.154). -/
theorem mfpt_ode_of_backward {A B : ℝ → ℝ} {G Gt Gx Gxx : ℝ → ℝ → ℝ} {T1 T2 : ℝ → ℝ} (x : ℝ)
    (hbwd : ∀ t ∈ Ioi (0 : ℝ), Gt x t = A x * Gx x t + B x / 2 * Gxx x t)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (G x) (Gt x t) t)
    (hG0 : ContinuousWithinAt (G x) (Ici 0) 0) (hG0' : G x 0 = 1)
    (hGinf : Tendsto (G x) atTop (𝓝 0))
    (hix : IntegrableOn (Gx x) (Ioi 0)) (hixx : IntegrableOn (Gxx x) (Ioi 0))
    (hT1 : T1 x = ∫ t in Ioi (0 : ℝ), Gx x t) (hT2 : T2 x = ∫ t in Ioi (0 : ℝ), Gxx x t) :
    A x * T1 x + B x / 2 * T2 x = -1 := by
  have hit : IntegrableOn (Gt x) (Ioi 0) := by
    have h' : IntegrableOn (fun t => A x * Gx x t + B x / 2 * Gxx x t) (Ioi 0) :=
      (hix.const_mul _).add (hixx.const_mul _)
    exact h'.congr_fun (fun t ht => (hbwd t ht).symm) measurableSet_Ioi
  have h153 := integral_Ioi_of_hasDerivAt_of_tendsto hG0 hderiv hit hGinf
  rw [hG0', zero_sub] at h153
  rw [hT1, hT2, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hix.const_mul _) (hixx.const_mul _), ← h153]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (hbwd t ht).symm)

/-- **(5.2.181)–(5.2.184) ⇒ (5.2.183).**  Suppose `g_a(x, ·)` satisfies the backward equation
`∂ₜg_a = A ∂ₓg_a + ½ B ∂ₓ²g_a` on `t > 0` (5.2.181), with `g_a(x, 0⁺) = π_a(x)` (5.2.184) and
`g_a(x, ∞) = 0`, and the (named) interchange hypotheses that `w' = ∫₀^∞ ∂ₓg_a dt`,
`w'' = ∫₀^∞ ∂ₓ²g_a dt` for `w = ∫₀^∞ g_a dt = π_a T(a, ·)` (5.2.182).  Then
`A w' + ½ B w'' = -π_a` (5.2.183). -/
theorem condExit_ode_of_backward {A B πa : ℝ → ℝ} {G Gt Gx Gxx : ℝ → ℝ → ℝ} {T1 T2 : ℝ → ℝ}
    (x : ℝ) (hbwd : ∀ t ∈ Ioi (0 : ℝ), Gt x t = A x * Gx x t + B x / 2 * Gxx x t)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (G x) (Gt x t) t)
    (hG0 : ContinuousWithinAt (G x) (Ici 0) 0) (hG0' : G x 0 = πa x)
    (hGinf : Tendsto (G x) atTop (𝓝 0))
    (hix : IntegrableOn (Gx x) (Ioi 0)) (hixx : IntegrableOn (Gxx x) (Ioi 0))
    (hT1 : T1 x = ∫ t in Ioi (0 : ℝ), Gx x t) (hT2 : T2 x = ∫ t in Ioi (0 : ℝ), Gxx x t) :
    A x * T1 x + B x / 2 * T2 x = -πa x := by
  have hit : IntegrableOn (Gt x) (Ioi 0) := by
    have h' : IntegrableOn (fun t => A x * Gx x t + B x / 2 * Gxx x t) (Ioi 0) :=
      (hix.const_mul _).add (hixx.const_mul _)
    exact h'.congr_fun (fun t ht => (hbwd t ht).symm) measurableSet_Ioi
  have h153 := integral_Ioi_of_hasDerivAt_of_tendsto hG0 hderiv hit hGinf
  rw [hG0', zero_sub] at h153
  rw [hT1, hT2, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hix.const_mul _) (hixx.const_mul _), ← h153]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (hbwd t ht).symm)

/-- **Instance of (5.2.153)–(5.2.154) and (5.2.181)–(5.2.183)**: for `A = 0`, `B = 2` the
function `G(x, t) = e^{-t} cos x` solves the backward equation; at `x = 0` (where `G(0, 0) = 1`)
`mfpt_ode_of_backward` gives `T'' = -1`, and for every `x` `condExit_ode_of_backward` gives
`w'' = -cos x`. -/
theorem backward_ode_instance (x : ℝ) :
    (0 : ℝ) * (∫ t in Ioi (0 : ℝ), -(exp (-t) * sin 0)) +
        2 / 2 * (∫ t in Ioi (0 : ℝ), -(exp (-t) * cos 0)) = -1 ∧
    (0 : ℝ) * (∫ t in Ioi (0 : ℝ), -(exp (-t) * sin x)) +
        2 / 2 * (∫ t in Ioi (0 : ℝ), -(exp (-t) * cos x)) = -cos x := by
  have hint : ∀ c : ℝ, IntegrableOn (fun t => -(exp (-t) * c)) (Ioi 0) := fun c => by
    have h : IntegrableOn (fun t => exp (-t) * c) (Ioi 0) := by
      simpa using (exp_neg_integrableOn_Ioi 0 one_pos).mul_const c
    exact h.neg
  have hd : ∀ y t : ℝ, HasDerivAt (fun t => exp (-t) * cos y) (-(exp (-t) * cos y)) t :=
    fun y t => by simpa using ((hasDerivAt_neg t).exp).mul_const (cos y)
  have hc : ∀ y, ContinuousWithinAt (fun t => exp (-t) * cos y) (Ici 0) 0 := fun y =>
    (by fun_prop : Continuous fun t : ℝ => exp (-t) * cos y).continuousWithinAt
  have hinf : ∀ y, Tendsto (fun t => exp (-t) * cos y) atTop (𝓝 0) := fun y => by
    simpa using (tendsto_exp_neg_atTop_nhds_zero.mul_const (cos y))
  constructor
  · exact mfpt_ode_of_backward (A := fun _ => 0) (B := fun _ => 2)
      (G := fun y t => exp (-t) * cos y) (Gt := fun y t => -(exp (-t) * cos y))
      (Gx := fun y t => -(exp (-t) * sin y)) (Gxx := fun y t => -(exp (-t) * cos y))
      (T1 := fun y => ∫ t in Ioi (0 : ℝ), -(exp (-t) * sin y))
      (T2 := fun y => ∫ t in Ioi (0 : ℝ), -(exp (-t) * cos y)) 0
      (fun t _ => by simp) (fun t _ => hd 0 t) (hc 0) (by simp) (hinf 0) (hint _) (hint _) rfl rfl
  · exact condExit_ode_of_backward (A := fun _ => 0) (B := fun _ => 2) (πa := cos)
      (G := fun y t => exp (-t) * cos y) (Gt := fun y t => -(exp (-t) * cos y))
      (Gx := fun y t => -(exp (-t) * sin y)) (Gxx := fun y t => -(exp (-t) * cos y))
      (T1 := fun y => ∫ t in Ioi (0 : ℝ), -(exp (-t) * sin y))
      (T2 := fun y => ∫ t in Ioi (0 : ℝ), -(exp (-t) * cos y)) x
      (fun t _ => by simp) (fun t _ => hd x t) (hc x) (by simp) (hinf x) (hint _) (hint _) rfl rfl

/-! ### Concrete instance: the Ornstein–Uhlenbeck process on `(-1, 1)` -/

/-- **Instance of (5.2.154)–(5.2.158), (5.2.186)–(5.2.189) and (5.2.183):** for the
Ornstein–Uhlenbeck process `A(x) = -x`, `B = 2` on `(-1, 1)`, the mean exit time, the exit
probability and the conditional exit time solve their boundary-value problems, and
`π_a T(a,·) + π_b T(b,·) = T`. -/
theorem ou_exit_instance :
    IsBwdSol (fun x => -x) (fun _ => 2) (fun _ => -1) (mfptTwo (fun x => -x) (fun _ => 2) (-1) 1) ∧
    mfptTwo (fun x => -x) (fun _ => 2) (-1) 1 (-1) = 0 ∧
    mfptTwo (fun x => -x) (fun _ => 2) (-1) 1 1 = 0 ∧
    IsBwdSol (fun x => -x) (fun _ => 2) (fun _ => 0) (exitA (fun x => -x) (fun _ => 2) (-1) 1) ∧
    exitA (fun x => -x) (fun _ => 2) (-1) 1 (-1) = 1 ∧
    exitA (fun x => -x) (fun _ => 2) (-1) 1 1 = 0 ∧
    (fun x => greenSol (fun x => -x) (fun _ => 2) (exitA (fun x => -x) (fun _ => 2) (-1) 1) (-1) 1 x
      + greenSol (fun x => -x) (fun _ => 2) (exitB (fun x => -x) (fun _ => 2) (-1) 1) (-1) 1 x)
      = mfptTwo (fun x => -x) (fun _ => 2) (-1) 1 := by
  have hA : Continuous fun x : ℝ => -x := by fun_prop
  have hB : Continuous fun _ : ℝ => (2 : ℝ) := continuous_const
  have hBp : ∀ _ : ℝ, (0 : ℝ) < 2 := fun _ => by norm_num
  obtain ⟨t1, t2, t3, -⟩ := mfptTwo_spec hA hB hBp (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨e1, e2, e3, -⟩ := exitA_spec hA hB hBp (by norm_num : (-1 : ℝ) < 1)
  exact ⟨t1, t2, t3, e1, e2, e3, condExit_add hA hB hBp (by norm_num)⟩

/-! ### The Smoluchowski case and the link with (5.2.165) -/

section smol

variable {U U' : ℝ → ℝ} (hU : ∀ x, HasDerivAt U (U' x) x) (hU' : Continuous U') {D : ℝ}
  (hD : 0 < D)
include hU hU' hD

/-- For (5.2.162) (`A = -U'`, `B = 2D`): `ψ(x) = e^{-[U(x) - U(a)]/D}`. -/
lemma smol_psi (a x : ℝ) :
    fpPsi (fun x => -U' x) (fun _ => 2 * D) a x = exp (-(U x - U a) / D) := by
  rw [fpPsi]
  congr 1
  have hint : ∫ t in a..x, 2 * -U' t / (2 * D) = ∫ t in a..x, -U' t / D := by
    apply intervalIntegral.integral_congr; intro t _
    simp only; field_simp
  rw [hint, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -U t / D)
    (fun t _ => ((hU t).neg.div_const D)) ((hU'.neg.div_const D).intervalIntegrable _ _)]
  ring

/-- **(5.2.160) for (5.2.162).**  With a reflecting barrier at `a`,
`T(x) = D⁻¹ ∫_x^b dy e^{U(y)/D} ∫_a^y e^{-U(z)/D} dz`. -/
theorem smolReflA_eq (a b x : ℝ) :
    mfptReflA (fun x => -U' x) (fun _ => 2 * D) a b x
      = D⁻¹ * ∫ y in x..b, exp (U y / D) * ∫ z in a..y, exp (-U z / D) := by
  rw [mfptReflA, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro y _
  simp only [smol_psi hU hU' hD]
  have hin : ∫ z in a..y, exp (-(U z - U a) / D) / (2 * D)
      = exp (U a / D) / (2 * D) * ∫ z in a..y, exp (-U z / D) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro z _
    simp only
    rw [show -(U z - U a) / D = U a / D + -U z / D by ring, exp_add]; ring
  rw [hin, ← exp_neg, show -(-(U y - U a) / D) = U y / D + -(U a / D) by ring, exp_add, exp_neg]
  have := exp_pos (U a / D)
  field_simp

/-- **(5.2.164)–(5.2.165) as a true limit.**  Letting the reflecting barrier recede,
`a → -∞`, the mean first-passage time (5.2.160) of the Smoluchowski process converges to
Gardiner's (5.2.165), `Gardiner.Escape.mfptBarrier`, provided `e^{-U/D}` is integrable. -/
theorem smolReflA_tendsto (hint : Integrable fun z => exp (-U z / D)) (b x : ℝ) :
    Tendsto (fun a => mfptReflA (fun x => -U' x) (fun _ => 2 * D) a b x) atBot
      (𝓝 (mfptBarrier U D x b)) := by
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun x => (hU x).continuousAt
  simp only [smolReflA_eq hU hU' hD, mfptBarrier]
  apply Tendsto.const_mul
  set f := fun z => exp (-U z / D)
  have hfc : Continuous f := by fun_prop
  have hf0 : ∀ z, 0 ≤ f z := fun z => (exp_pos _).le
  set M := ∫ z, f z
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun y => exp (U y / D) * M) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun a => ?_
    exact (Continuous.aestronglyMeasurable (by
      exact (by fun_prop : Continuous fun y => exp (U y / D)).mul
        (intervalIntegral.continuous_primitive (fun _ _ => hfc.intervalIntegrable _ _) a)))
  · filter_upwards [eventually_le_atBot (min x b)] with a ha
    refine Eventually.of_forall fun y hy => ?_
    have hay : a ≤ y := by
      have := hy.1; simp only [min_lt_iff] at this ⊢
      rcases this with h | h
      · exact le_trans ha (le_trans (min_le_left _ _) h.le)
      · exact le_trans ha (le_trans (min_le_right _ _) h.le)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg hay (fun z _ => hf0 z)),
      intervalIntegral.integral_of_le hay]
    exact setIntegral_le_integral hint (Eventually.of_forall hf0)
  · exact (by fun_prop : Continuous fun y => exp (U y / D) * M).intervalIntegrable _ _
  · refine Eventually.of_forall fun y _ => ?_
    exact (intervalIntegral_tendsto_integral_Iic y hint.integrableOn tendsto_id).const_mul _

end smol

/-- **Instance of (5.2.164)–(5.2.165):** for the quartic double well `U = x⁴/4 - x²/2` with
`D = 1`, the reflecting-barrier mean first-passage time converges to (5.2.165) as the reflecting
barrier recedes to `-∞`. -/
theorem doubleWell_reflect_limit (b x : ℝ) :
    Tendsto (fun a => mfptReflA (fun y => -(y ^ 3 - y)) (fun _ => 2 * 1) a b x) atBot
      (𝓝 (mfptBarrier (Gardiner.Adiabatic.dwU 0) 1 x b)) := by
  have hU : ∀ y, HasDerivAt (Gardiner.Adiabatic.dwU 0) (y ^ 3 - y) y := by
    intro y
    rw [dwU_zero]
    have := ((hasDerivAt_pow 4 y).div_const 4).sub ((hasDerivAt_pow 2 y).div_const 2)
    convert this using 1; push_cast; ring
  have hint : Integrable fun z => exp (-Gardiner.Adiabatic.dwU 0 z / 1) := by
    simpa only [div_one, integrableOn_univ] using dwU_integrable univ
  exact smolReflA_tendsto (U' := fun y => y ^ 3 - y) hU (by fun_prop) one_pos hint b x

end Gardiner.Escape
