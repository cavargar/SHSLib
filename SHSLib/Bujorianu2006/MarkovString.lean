/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Markov strings: jump times, translations, càdlàg paths, Markov property

Formalization of Section 3.3–3.4 of

  M.L. Bujorianu and J. Lygeros, "Toward a General Theory of Stochastic Hybrid
  Systems", LNCIS 337, Springer, 2006.

A Markov string is obtained by concatenating killed Markov processes: the
current piece is run until its sojourn time `S`, then the string is restarted
from a new state according to the renewal kernel.  The paper describes the
resulting object through

* the recursion `T_{k+1}(ω) = T_k(ω) + S^{i_k}(ω^{i_k})` for the jump times
  (Eq. (10)),
* the translation operators `θ_t(ω) = (θ^{i_k}_{t - T_k}(ω^{i_k}) * ω^{i_{k+1}} * …)`
  (Eq. (13)),
* the counting process `N_t = Σ_k I_{t ≥ T_k}` and Assumption 6 (non-Zeno),
* the Markov property (Eq. (14)) and the càdlàg property (Proposition 3).

We formalize the combinatorial/analytic content of this construction in the
structure `PiecedProcess`, whose axioms are exactly the two properties of the
construction that the proofs of Lemma 1 and Propositions 2–4 use: shifting
inside the current piece does not change the future pieces, and shifting past
the current sojourn time is the same as restarting.  From these we *derive*:

* the shift identity `T_{i+1}(θ_t ω) = T_{k+i+1}(ω) - t` on `{T_k ≤ t < T_{k+1}}`
  (the computation in the proof of Lemma 1);
* the equivalence between the non-Zeno condition and the divergence of the
  jump times;
* right continuity of a path obtained by concatenation (Proposition 3);
* the semigroup property and Chapman–Kolmogorov equation for a process with
  the Markov property (Eq. (14)) (Proposition 2).
-/
import SHSLib.Bujorianu2006.TerminalTimes

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Bujorianu2006

/-! ## The pieced-together construction -/

/-- The data of the pieced-together (Markov string) construction of
Section 3.3: a shift system, the sojourn time `S` of the current piece (a
terminal time, Assumption 5(i)), and the map `restart` sending a trajectory
`ω = ω^{i_0} * ω^{i_1} * …` to the trajectory `ω^{i_1} * ω^{i_2} * …` that the
string follows after the first jump. -/
structure PiecedProcess (Ω : Type*) (X : Type*) extends ShiftSystem Ω X where
  /-- The sojourn time of the current piece. -/
  S : Ω → ℝ≥0∞
  /-- The trajectory followed after the first jump. -/
  restart : Ω → Ω
  /-- Assumption 5(i): `S` is a terminal time (Eq. (5)). -/
  S_terminal : IsTerminalTime toShiftSystem S
  /-- Assumption 5(ii)(b): translating inside the current piece does not change
  the future pieces. -/
  restart_shift : ∀ (t : ℝ) (ω : Ω), 0 ≤ t → ENNReal.ofReal t < S ω →
    restart (θ t ω) = restart ω
  /-- Equation (13): after the current sojourn time the translation operator is
  the translation of the restarted trajectory. -/
  θ_restart : ∀ (t r : ℝ) (ω : Ω), 0 ≤ r → ENNReal.ofReal r = S ω → r ≤ t →
    θ t ω = θ (t - r) (restart ω)

namespace PiecedProcess

variable {Ω X : Type*} (P : PiecedProcess Ω X)

/-- **Equation (10)**: the jump times of the string,
`T_0 = 0`, `T_{k+1}(ω) = S(ω) + T_k(restart ω)`. -/
def jumpTime (P : PiecedProcess Ω X) : ℕ → Ω → ℝ≥0∞
  | 0, _ => 0
  | (k + 1), ω => P.S ω + jumpTime P k (P.restart ω)

@[simp] theorem jumpTime_zero (ω : Ω) : P.jumpTime 0 ω = 0 := by
  simp [jumpTime]

theorem jumpTime_succ (k : ℕ) (ω : Ω) :
    P.jumpTime (k + 1) ω = P.S ω + P.jumpTime k (P.restart ω) := by
  simp [jumpTime]

@[simp] theorem jumpTime_one (ω : Ω) : P.jumpTime 1 ω = P.S ω := by
  simp [jumpTime_succ]

/-- The jump times increase with the index. -/
theorem jumpTime_mono (ω : Ω) : Monotone fun k => P.jumpTime k ω := by
  refine monotone_nat_of_le_succ ?_
  intro k
  induction k generalizing ω with
  | zero => simp
  | succ n ih =>
      rw [jumpTime_succ, jumpTime_succ (k := n + 1)]
      exact add_le_add le_rfl (ih (P.restart ω))
/-- The sojourn time of the first piece is bounded by every later jump time. -/
theorem S_le_jumpTime_succ (k : ℕ) (ω : Ω) : P.S ω ≤ P.jumpTime (k + 1) ω := by
  rw [jumpTime_succ]; exact le_self_add

variable {P}

/-- **Lemma 1, first step**: inside the first piece, translating by `t` shifts
every jump time back by `t`: `T_{k+1}(θ_t ω) = T_{k+1}(ω) - t` whenever
`t < S(ω)`. -/
theorem jumpTime_shift_first (k : ℕ) (t : ℝ) (ω : Ω) (ht : 0 ≤ t)
    (hlt : ENNReal.ofReal t < P.S ω) :
    P.jumpTime (k + 1) (P.θ t ω) = P.jumpTime (k + 1) ω - ENNReal.ofReal t := by
  rw [jumpTime_succ, jumpTime_succ, P.S_terminal t ω ht hlt, P.restart_shift t ω ht hlt,
    ENNReal.sub_add_eq_add_sub hlt.le ENNReal.ofReal_ne_top]

/-- **Lemma 1** (the computation in its proof): if `T_k(ω) ≤ t < T_{k+1}(ω)`
then the jump times of the translated trajectory are the later jump times of
`ω`, shifted back by `t`:
`T_{i+1}(θ_t ω) = T_{k+i+1}(ω) - t`. -/
theorem jumpTime_shift (k i : ℕ) (t : ℝ) (ω : Ω) (ht : 0 ≤ t)
    (hk : P.jumpTime k ω ≤ ENNReal.ofReal t)
    (hk' : ENNReal.ofReal t < P.jumpTime (k + 1) ω) :
    P.jumpTime (i + 1) (P.θ t ω) = P.jumpTime (k + i + 1) ω - ENNReal.ofReal t := by
  induction k generalizing t ω with
  | zero =>
      simpa using jumpTime_shift_first i t ω ht (by simpa using hk')
  | succ n ih =>
      -- the first sojourn time is already over
      have hSle : P.S ω ≤ ENNReal.ofReal t := le_trans (P.S_le_jumpTime_succ n ω) hk
      have hStop : P.S ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSle
      set r : ℝ := (P.S ω).toReal with hr
      have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
      have hrS : ENNReal.ofReal r = P.S ω := ENNReal.ofReal_toReal hStop
      have hrt : r ≤ t := by
        have := hSle
        rw [← hrS] at this
        exact (ENNReal.ofReal_le_ofReal_iff ht).mp this
      have hθ : P.θ t ω = P.θ (t - r) (P.restart ω) := P.θ_restart t r ω hr0 hrS hrt
      -- transfer the hypotheses to the restarted trajectory
      have hsub : ENNReal.ofReal (t - r) = ENNReal.ofReal t - P.S ω := by
        rw [ENNReal.ofReal_sub _ hr0, hrS]
      have hkn : P.jumpTime n (P.restart ω) ≤ ENNReal.ofReal (t - r) := by
        rw [hsub]
        refine ENNReal.le_sub_of_add_le_left hStop ?_
        rw [← P.jumpTime_succ n ω]
        exact hk
      have hkn' : ENNReal.ofReal (t - r) < P.jumpTime (n + 1) (P.restart ω) := by
        rw [hsub]
        refine ENNReal.sub_lt_of_lt_add hSle ?_
        rw [add_comm, ← P.jumpTime_succ (n + 1) ω]
        exact hk'
      have hIH := ih (t - r) (P.restart ω) (by linarith) hkn hkn'
      rw [hθ, hIH]
      -- rewrite `T_{n+i+2}(ω) = S(ω) + T_{n+i+1}(restart ω)`
      have hTsucc : P.jumpTime (n + 1 + i + 1) ω
          = P.S ω + P.jumpTime (n + i + 1) (P.restart ω) := by
        have : n + 1 + i + 1 = (n + i + 1) + 1 := by ring
        rw [this, P.jumpTime_succ]
      rw [hTsucc, hsub]
      -- `a - (u - c) = (c + a) - u` for `c ≤ u`, `c ≠ ⊤`
      set a := P.jumpTime (n + i + 1) (P.restart ω)
      have hu : (ENNReal.ofReal t - P.S ω) + P.S ω = ENNReal.ofReal t :=
        tsub_add_cancel_of_le hSle
      calc a - (ENNReal.ofReal t - P.S ω)
          = (a + P.S ω) - ((ENNReal.ofReal t - P.S ω) + P.S ω) :=
            (ENNReal.add_sub_add_eq_sub_right hStop).symm
        _ = (P.S ω + a) - ENNReal.ofReal t := by rw [hu, add_comm]

variable (P)

/-! ### Explosion time, the counting process and Assumption 6 -/

/-- The explosion time `T_∞ = lim_k T_k`. -/
def explosionTime (ω : Ω) : ℝ≥0∞ := ⨆ k, P.jumpTime k ω

theorem jumpTime_le_explosionTime (k : ℕ) (ω : Ω) :
    P.jumpTime k ω ≤ P.explosionTime ω := le_iSup (fun k => P.jumpTime k ω) k

/-- **Assumption 6** (non-Zeno dynamics), pathwise form: the jump times do not
accumulate, i.e. `T_∞ = ∞`. -/
def NonZeno : Prop := ∀ ω, P.explosionTime ω = ⊤

/-- The number of jumps in `[0, t]`, `N_t = Σ_{k ≥ 1} I_{t ≥ T_k}`, as an
element of `ℕ∞`. -/
def jumpCount (t : ℝ) (ω : Ω) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : P.jumpTime k ω ≤ ENNReal.ofReal t), (k : ℕ∞)

variable {P}

theorem le_jumpCount (k : ℕ) (t : ℝ) (ω : Ω) (h : P.jumpTime k ω ≤ ENNReal.ofReal t) :
    (k : ℕ∞) ≤ P.jumpCount t ω :=
  le_trans (le_iSup (fun _ : P.jumpTime k ω ≤ ENNReal.ofReal t => (k : ℕ∞)) h)
    (le_iSup (fun k : ℕ => ⨆ _ : P.jumpTime k ω ≤ ENNReal.ofReal t, (k : ℕ∞)) k)

/-- `N` is nondecreasing in time. -/
theorem jumpCount_mono (ω : Ω) : Monotone fun t : ℝ => P.jumpCount t ω := by
  intro s t hst
  refine iSup_mono fun k => ?_
  refine iSup_le fun hk => ?_
  exact le_iSup (fun _ : P.jumpTime k ω ≤ ENNReal.ofReal t => (k : ℕ∞))
    (le_trans hk (ENNReal.ofReal_le_ofReal hst))

/-- If some jump time exceeds `t`, then only finitely many jumps occur before
`t`. -/
theorem jumpCount_ne_top_of_lt {t : ℝ} {ω : Ω} {K : ℕ}
    (h : ENNReal.ofReal t < P.jumpTime K ω) : P.jumpCount t ω ≤ (K : ℕ∞) := by
  refine iSup_le fun k => iSup_le fun hk => ?_
  by_contra hcon
  push_neg at hcon
  have hKk : K ≤ k := by exact_mod_cast hcon.le
  exact absurd (le_trans (P.jumpTime_mono ω hKk) hk) (not_le.mpr h)

/-- **Non-Zeno dynamics**: the explosion time is infinite exactly when the jump
times eventually exceed every finite horizon; in that case the counting process
`N_t` is finite for every `t`. -/
theorem explosionTime_eq_top_iff (ω : Ω) :
    P.explosionTime ω = ⊤ ↔ ∀ t : ℝ, ∃ k, ENNReal.ofReal t < P.jumpTime k ω := by
  constructor
  · intro h t
    by_contra hcon
    push_neg at hcon
    have : P.explosionTime ω ≤ ENNReal.ofReal t := iSup_le hcon
    rw [h] at this
    exact absurd (top_le_iff.mp this) ENNReal.ofReal_ne_top
  · intro h
    by_contra hne
    obtain ⟨k, hk⟩ := h (P.explosionTime ω).toReal
    rw [ENNReal.ofReal_toReal hne] at hk
    exact absurd (P.jumpTime_le_explosionTime k ω) (not_le.mpr hk)

/-- Under the non-Zeno assumption, only finitely many jumps occur in a bounded
time interval. -/
theorem jumpCount_ne_top (h : P.NonZeno) (t : ℝ) (ω : Ω) : P.jumpCount t ω ≠ ⊤ := by
  obtain ⟨K, hK⟩ := (explosionTime_eq_top_iff ω).mp (h ω) t
  exact ne_top_of_le_ne_top (by simp) (jumpCount_ne_top_of_lt hK)

end PiecedProcess

/-! ## Proposition 3: the càdlàg property of a concatenation

The paper's argument is that the sample paths of a Markov string are obtained
by concatenating the sample paths of the component processes, in a way that
preserves right continuity and left limits.  The following lemma is the
analytic content of that argument: a path that coincides with a right
continuous function on a right-open interval containing the time `t` is right
continuous at `t`. -/

theorem rightContinuousWithinAt_of_eqOn_Ico {X : Type*} [TopologicalSpace X]
    {f g : ℝ → X} {t a b : ℝ} (hta : a ≤ t) (htb : t < b)
    (heq : Set.EqOn f g (Set.Ico a b))
    (hg : ContinuousWithinAt g (Set.Ici t) t) :
    ContinuousWithinAt f (Set.Ici t) t := by
  have hmem : Set.Ico a b ∈ 𝓝[Set.Ici t] t := by
    refine mem_nhdsWithin.mpr ⟨Set.Iio b, isOpen_Iio, htb, ?_⟩
    rintro y ⟨hyb, hyt⟩
    exact ⟨le_trans hta hyt, hyb⟩
  have hEq : f =ᶠ[𝓝[Set.Ici t] t] g := eventually_of_mem hmem fun y hy => heq hy
  have hft : f t = g t := heq ⟨hta, htb⟩
  rw [ContinuousWithinAt, hft]
  exact Filter.Tendsto.congr' hEq.symm hg

/-- **Proposition 3** (càdlàg property), the piecewise form: if the path `f`
agrees on each interval `[T_k, T_{k+1})` with a right continuous function `g k`,
and the intervals cover `[0, ∞)`, then `f` is right continuous on `[0, ∞)`. -/
theorem rightContinuous_of_concatenation {X : Type*} [TopologicalSpace X]
    (f : ℝ → X) (T : ℕ → ℝ) (g : ℕ → ℝ → X)
    (hpiece : ∀ k, Set.EqOn f (g k) (Set.Ico (T k) (T (k + 1))))
    (hg : ∀ k t, ContinuousWithinAt (g k) (Set.Ici t) t)
    (hcover : ∀ t : ℝ, 0 ≤ t → ∃ k, T k ≤ t ∧ t < T (k + 1)) :
    ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt f (Set.Ici t) t := by
  intro t ht
  obtain ⟨k, hk1, hk2⟩ := hcover t ht
  exact rightContinuousWithinAt_of_eqOn_Ico hk1 hk2 (hpiece k) (hg k t)

/-! ## Proposition 2: the Markov property -/

namespace ShiftSystem

variable {Ω X : Type*} (M : ShiftSystem Ω X)

/-- **Equation (14)**: the simple Markov property of a Markov string, expressed
through a family of expectation operators `E^x[·]`:
`E^x[f · (g ∘ θ_t)] = E^x[f · E^{x_t}[g]]`. -/
def HasMarkovProperty (E : X → (Ω → ℝ) → ℝ) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → ∀ (y : X) (f g : Ω → ℝ),
    E y (fun ω => f ω * g (M.θ t ω)) = E y (fun ω => f ω * E (M.x t ω) g)

variable {M}

/-- The `f = 1` case of the Markov property: `E^x[g ∘ θ_t] = E^x[E^{x_t}[g]]`. -/
theorem markov_apply {E : X → (Ω → ℝ) → ℝ} (hE : M.HasMarkovProperty E)
    {t : ℝ} (ht : 0 ≤ t) (y : X) (g : Ω → ℝ) :
    E y (fun ω => g (M.θ t ω)) = E y (fun ω => E (M.x t ω) g) := by
  simpa using hE t ht y (fun _ => 1) g

/-- **Chapman–Kolmogorov equation** for a Markov string:
`E^x[g ∘ θ_{s+t}] = E^x[E^{x_t}[g ∘ θ_s]]`. -/
theorem markov_chapman_kolmogorov {E : X → (Ω → ℝ) → ℝ} (hE : M.HasMarkovProperty E)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (y : X) (g : Ω → ℝ) :
    E y (fun ω => g (M.θ (s + t) ω)) = E y (fun ω => E (M.x t ω) (fun ω' => g (M.θ s ω'))) := by
  have hshift : ∀ ω, g (M.θ (s + t) ω) = (fun ω' => g (M.θ s ω')) (M.θ t ω) := by
    intro ω
    show g (M.θ (s + t) ω) = g (M.θ s (M.θ t ω))
    rw [M.θ_add s t ω hs ht]
  calc E y (fun ω => g (M.θ (s + t) ω))
      = E y (fun ω => (fun ω' => g (M.θ s ω')) (M.θ t ω)) := by simp only [hshift]
    _ = E y (fun ω => E (M.x t ω) (fun ω' => g (M.θ s ω'))) :=
        markov_apply hE ht y (fun ω' => g (M.θ s ω'))

/-- The transition semigroup `P_t h(x) = E^x[h(x_t)]` of a Markov string. -/
def semigroupOp (E : X → (Ω → ℝ) → ℝ) (t : ℝ) (h : X → ℝ) (y : X) : ℝ :=
  E y (fun ω => h (M.x t ω))

/-- **The transition operators form a semigroup**: `P_{t+s} = P_t ∘ P_s`.  This
is the standard consequence of the Markov property (Eq. (14)) together with the
identity `x_s ∘ θ_t = x_{s+t}` of Lemma 1. -/
theorem semigroupOp_comp {E : X → (Ω → ℝ) → ℝ} (hE : M.HasMarkovProperty E)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : X → ℝ) :
    M.semigroupOp E (t + s) h = M.semigroupOp E t (M.semigroupOp E s h) := by
  funext y
  have hx : ∀ ω, h (M.x (t + s) ω) = (fun ω' => h (M.x s ω')) (M.θ t ω) := by
    intro ω
    show h (M.x (t + s) ω) = h (M.x s (M.θ t ω))
    rw [M.x_shift s t ω hs ht, add_comm s t]
  calc M.semigroupOp E (t + s) h y
      = E y (fun ω => (fun ω' => h (M.x s ω')) (M.θ t ω)) := by
        simp only [semigroupOp, hx]
    _ = E y (fun ω => E (M.x t ω) (fun ω' => h (M.x s ω'))) :=
        markov_apply hE ht y (fun ω' => h (M.x s ω'))
    _ = M.semigroupOp E t (M.semigroupOp E s h) y := rfl

end ShiftSystem

end Bujorianu2006

end
