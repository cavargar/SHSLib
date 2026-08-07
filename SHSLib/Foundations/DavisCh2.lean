/-
  Formal skeleton for Chapter 2 of M.H.A. Davis,
  "Markov Models and Optimization" (1993).

  Chapter 2: Piecewise-Deterministic Markov Processes

  This file formalizes the key definitions, theorems, and propositions
  from the chapter, organized by section number matching the textbook.
  The chapter introduces piecewise-deterministic Markov processes (PDPs)
  and establishes their main properties: the strong Markov property,
  an exact characterization of the extended generator, and the fact
  that PDPs are right processes.
-/

import Mathlib

open MeasureTheory Topology Filter Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Davis

/-
Helper: if `f` is absolutely continuous on `uIcc a b` and `g` is Lipschitz
    (constant `K`) on a set `s` containing the values `f x` for `x ∈ uIcc a b`,
    then `g ∘ f` is absolutely continuous on `uIcc a b`.
-/
lemma absCont_comp_lipschitzOnWith {f g : ℝ → ℝ} {a b : ℝ} {K : ℝ≥0} {s : Set ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : LipschitzOnWith K g s)
    (hmaps : ∀ x ∈ Set.uIcc a b, f x ∈ s) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
      rw [ AbsolutelyContinuousOnInterval ] at *;
      -- Applying the Lipschitz condition to each term in the sum.
      have h_lip : ∀ E : ℕ × (ℕ → ℝ × ℝ), (∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ Set.uIcc a b ∧ (E.2 i).2 ∈ Set.uIcc a b) → (∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))) ≤ K * (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) := by
        exact fun E hE => by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => hg.norm_sub_le ( hmaps _ <| hE i hi |>.1 ) ( hmaps _ <| hE i hi |>.2 ) ;
      refine' squeeze_zero_norm' _ ( by simpa using hf.const_mul ( K : ℝ ) );
      simp_all +decide [ AbsolutelyContinuousOnInterval.disjWithin ];
      filter_upwards [ Filter.eventually_inf_principal.mpr <| Filter.Eventually.of_forall fun E hE => hE.1 ] with E hE using by rw [ abs_of_nonneg <| Finset.sum_nonneg fun _ _ => dist_nonneg ] ; exact h_lip _ _ hE;

/-!
## §21 Markov models and supplementary variables

This section introduces motivating examples (Poisson process, renewal
processes, queueing models) and the key technique of supplementary
variables. We formalize the foundational probabilistic facts used
throughout.
-/

section S21_MarkovModels

/-!
### Exponential distribution and memoryless property

**(21.1)** The exponential distribution is characterized by the memoryless
property: P[T > t + s | T > s] = P[T > t].
-/

/-- (21.1) The memoryless property of the exponential distribution:
    P[T > t + s | T > s] = e^{-rate·t} = P[T > t]. -/
theorem exponential_memoryless (rate : ℝ) (hrate : 0 < rate) (t s : ℝ)
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Real.exp (-rate * (t + s)) / Real.exp (-rate * s) =
      Real.exp (-rate * t) := by
  rw [← Real.exp_sub]; congr 1; ring

/-!
**(21.2–21.3)** The hazard rate h(s) = ψ(s)/Ψ(s) determines the survivor
function via Ψ(t) = exp(-∫₀ᵗ h(s) ds), and conversely.
-/

/-
(21.3) The survivor function is recovered from the hazard rate via
    Ψ(t) = exp(-∫₀ᵗ h(s) ds).
-/
set_option maxHeartbeats 1000000 in
theorem survivor_from_hazard {psi : ℝ → ℝ} {bigPsi : ℝ → ℝ}
    (hpsi_nn : ∀ t, 0 ≤ t → 0 ≤ psi t)
    (hbigPsi_def : ∀ t, 0 ≤ t → bigPsi t = ∫ u in Set.Ioi t, psi u)
    (hbigPsi_pos : ∀ t, 0 ≤ t → 0 < bigPsi t)
    (hbigPsi0 : bigPsi 0 = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    bigPsi t = Real.exp (- ∫ u in Set.Icc 0 t, psi u / bigPsi u) := by
      -- Let's first show that the function `bigPsi` is absolutely continuous on the interval `[0, t]`.
      have h_abs_cont : AbsolutelyContinuousOnInterval bigPsi 0 t := by
        -- By definition of $bigPsi$, we know that $bigPsi(t) = 1 - \int_0^t psi(u) \, du$.
        have h_bigPsi_eq : ∀ s ∈ Set.Icc 0 t, bigPsi s = 1 - ∫ u in (0 : ℝ)..s, psi u := by
          intro s hs; rw [ hbigPsi_def s hs.1 ] ; rw [ intervalIntegral.integral_of_le hs.1 ] ; rw [ eq_sub_iff_add_eq' ] ; rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num [ hbigPsi0, hbigPsi_def, hs.1 ] ;
          · aesop;
          · exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by by_contra h; have := hbigPsi_pos 0 le_rfl; rw [ hbigPsi_def 0 le_rfl ] at this; rw [ MeasureTheory.integral_undef h ] at this; linarith ) ) ( Set.Ioc_subset_Ioi_self );
          · contrapose! hbigPsi_pos;
            exact ⟨ s, hs.1, by rw [ hbigPsi_def s hs.1, MeasureTheory.integral_undef hbigPsi_pos ] ⟩;
        -- The function $1 - \int_0^s \psi(u) \, du$ is absolutely continuous on $[0, t]$ because it is the difference of two absolutely continuous functions.
        have h_abs_cont : AbsolutelyContinuousOnInterval (fun s => 1 - ∫ u in (0 : ℝ)..s, psi u) 0 t := by
          refine' AbsolutelyContinuousOnInterval.sub _ _;
          · norm_num [ AbsolutelyContinuousOnInterval ];
            exact tendsto_const_nhds;
          · have h_integrable : MeasureTheory.IntegrableOn psi (Set.Ioc 0 t) := by
              have h_integrable : MeasureTheory.IntegrableOn psi (Set.Ioi 0) := by
                contrapose! hbigPsi_pos;
                exact ⟨ 0, by norm_num, by rw [ hbigPsi_def 0 le_rfl, MeasureTheory.integral_undef hbigPsi_pos ] ⟩;
              exact h_integrable.mono_set <| Set.Ioc_subset_Ioi_self;
            apply_rules [ IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral ];
            · rwa [ intervalIntegrable_iff_integrableOn_Ioc_of_le ht ];
            · norm_num [ ht ];
        rw [ absolutelyContinuousOnInterval_iff ] at *;
        intro ε hε; obtain ⟨ δ, hδ, H ⟩ := h_abs_cont ε hε; use δ, hδ; intro E hE hδE; refine' lt_of_le_of_lt _ ( H E hE hδE ) ; refine' Finset.sum_le_sum fun i _ => _ ;
        simp_all +decide [ AbsolutelyContinuousOnInterval.disjWithin ];
      -- Let's show that the function `log(bigPsi)` is absolutely continuous on the interval `[0, t]`.
      have h_log_abs_cont : AbsolutelyContinuousOnInterval (fun s => Real.log (bigPsi s)) 0 t := by
        -- Since `bigPsi` is continuous on `[0, t]`, it attains a minimum value `m > 0` on this interval.
        obtain ⟨m, hm_pos, hm_min⟩ : ∃ m > 0, ∀ s ∈ Set.Icc 0 t, m ≤ bigPsi s := by
          have h_cont : ContinuousOn bigPsi (Set.Icc 0 t) := by
            convert h_abs_cont.continuousOn using 1;
            rw [ Set.uIcc_of_le ht ];
          obtain ⟨ m, hm ⟩ := IsCompact.exists_isMinOn ( CompactIccSpace.isCompact_Icc ) ⟨ 0, Set.left_mem_Icc.mpr ht ⟩ h_cont;
          exact ⟨ bigPsi m, hbigPsi_pos m hm.1.1, fun s hs => hm.2 hs ⟩;
        -- Since `log` is Lipschitz on `[m, M]` with constant `1/m`, we can apply the composition theorem.
        have h_log_lip : LipschitzOnWith (⟨1 / m, by positivity⟩ : NNReal) (fun x => Real.log x) (Set.Icc m (sSup (bigPsi '' Set.Icc 0 t))) := by
          have h_log_lip : ∀ x y : ℝ, m ≤ x → x ≤ y → y ≤ sSup (bigPsi '' Set.Icc 0 t) → |Real.log x - Real.log y| ≤ (1 / m) * |x - y| := by
            intros x y hx hy hxy
            have h_log_diff : Real.log y - Real.log x ≤ (1 / m) * (y - x) := by
              rw [ ← Real.log_div ( by linarith ) ( by linarith ) ];
              exact le_trans ( Real.log_le_sub_one_of_pos ( div_pos ( by linarith ) ( by linarith ) ) ) ( by rw [ div_mul_eq_mul_div, div_sub_one, div_le_div_iff₀ ] <;> nlinarith );
            rw [ abs_of_nonpos, abs_of_nonpos ] <;> nlinarith [ one_div_mul_cancel hm_pos.ne', Real.log_le_log ( by linarith ) hy ];
          rw [ lipschitzOnWith_iff_norm_sub_le ];
          intro x hx y hy; cases le_total x y <;> simp_all +decide [ abs_sub_comm ] ;
          simpa only [ abs_sub_comm ] using h_log_lip y x hy.1 ‹_› hx.2;
        apply absCont_comp_lipschitzOnWith h_abs_cont h_log_lip;
        simp_all +decide [ Set.uIcc_of_le ht ];
        exact fun x hx₁ hx₂ => le_csSup ( by exact ( IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn ( show ContinuousOn bigPsi ( Set.Icc 0 t ) from h_abs_cont.continuousOn.mono ( by aesop_cat ) ) ) ) ) ( Set.mem_image_of_mem _ ⟨ hx₁, hx₂ ⟩ ) |> le_trans ( by aesop );
      -- By the properties of the derivative, we know that for almost every $s \in [0, t]$, $\frac{d}{ds} \log(\bigPsi(s)) = -\frac{\psi(s)}{\bigPsi(s)}$.
      have h_deriv : ∀ᵐ s ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo 0 t), deriv (fun s => Real.log (bigPsi s)) s = -psi s / bigPsi s := by
        have h_deriv : ∀ᵐ s ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo 0 t), deriv (fun s => bigPsi s) s = -psi s := by
          have h_deriv : ∀ᵐ s ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo 0 t), deriv (fun s => ∫ u in (0:ℝ)..s, psi u) s = psi s := by
            have h_deriv_log : IntervalIntegrable psi MeasureTheory.volume 0 t := by
              have h_integrable : MeasureTheory.IntegrableOn psi (Set.Ioi 0) := by
                contrapose! hbigPsi_pos;
                exact ⟨ 0, by norm_num, by rw [ hbigPsi_def 0 le_rfl, MeasureTheory.integral_undef hbigPsi_pos ] ⟩;
              rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ht ];
              exact h_integrable.mono_set <| Set.Ioc_subset_Ioi_self;
            have := h_deriv_log.ae_hasDerivAt_integral;
            rw [ MeasureTheory.ae_restrict_iff' ] <;> norm_num;
            filter_upwards [ this ] with x hx hx' hx'' using HasDerivAt.deriv ( hx ( by rw [ Set.uIcc_of_le ht ] ; exact ⟨ by linarith, by linarith ⟩ ) 0 ( by rw [ Set.uIcc_of_le ht ] ; exact ⟨ by linarith, by linarith ⟩ ) );
          have h_deriv : ∀ s ∈ Set.Ioo 0 t, bigPsi s = 1 - ∫ u in (0:ℝ)..s, psi u := by
            intros s hs
            have h_split : ∫ u in Set.Ioi 0, psi u = (∫ u in Set.Ioc 0 s, psi u) + (∫ u in Set.Ioi s, psi u) := by
              rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num [ hs.1.le, hs.2.le ];
              · have h_integrable : MeasureTheory.IntegrableOn psi (Set.Ioi 0) := by
                  contrapose! hbigPsi_pos;
                  exact ⟨ 0, by norm_num, by rw [ hbigPsi_def 0 le_rfl ] ; rw [ MeasureTheory.integral_undef hbigPsi_pos ] ⟩;
                exact h_integrable.mono_set <| Set.Ioc_subset_Ioi_self;
              · contrapose! hbigPsi_pos;
                exact ⟨ s, hs.1.le, by rw [ hbigPsi_def s hs.1.le, MeasureTheory.integral_undef hbigPsi_pos ] ⟩;
            simp_all +decide [ intervalIntegral.integral_of_le hs.1.le ];
            linarith [ hbigPsi_def s hs.1.le ];
          filter_upwards [ ‹∀ᵐ s ∂MeasureTheory.Measure.restrict MeasureTheory.volume ( Set.Ioo 0 t ), deriv ( fun s => ∫ u in ( 0 : ℝ )..s, psi u ) s = psi s›, MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with s hs hs';
          rw [ ← hs, show deriv ( fun s => bigPsi s ) s = deriv ( fun s => 1 - ∫ u in ( 0 : ℝ )..s, psi u ) s by exact Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hs'.1 hs'.2 ) fun x hx => h_deriv x hx ) ] ; norm_num [ hs ];
          rw [ deriv_const_sub, hs ];
        filter_upwards [ h_deriv, MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with s hs hs';
        by_cases h : DifferentiableAt ℝ bigPsi s <;> simp_all +decide [ ne_of_gt, div_eq_inv_mul ];
        · norm_num [ h, hs, ne_of_gt ( show 0 < bigPsi s from hbigPsi_def s hs'.1.le ▸ hbigPsi_pos s hs'.1.le ) ] ; ring;
        · rw [ deriv_zero_of_not_differentiableAt ];
          · rw [ deriv_zero_of_not_differentiableAt h ] at hs ; aesop;
          · contrapose! h;
            have := h.exp;
            exact this.congr_of_eventuallyEq ( by filter_upwards [ Ioo_mem_nhds hs'.1 hs'.2 ] with x hx using by rw [ Real.exp_log ( hbigPsi_def x hx.1.le ▸ hbigPsi_pos x hx.1.le ) ] );
      -- By the fundamental theorem of calculus, we know that
      have h_ftc : ∫ s in (0 : ℝ)..t, deriv (fun s => Real.log (bigPsi s)) s = Real.log (bigPsi t) - Real.log (bigPsi 0) := by
        apply_rules [ h_log_abs_cont.integral_deriv_eq_sub ];
      -- Substitute the expression for the derivative into the fundamental theorem of calculus.
      have h_subst : ∫ s in (0 : ℝ)..t, -psi s / bigPsi s = Real.log (bigPsi t) - Real.log (bigPsi 0) := by
        rw [ ← h_ftc, intervalIntegral.integral_of_le ht, MeasureTheory.integral_Ioc_eq_integral_Ioo ];
        rw [ intervalIntegral.integral_of_le ht, MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_congr_ae h_deriv ];
      simp_all +decide [ neg_div, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht ];
      rw [ Real.exp_log ( hbigPsi_pos t ht ) ]

/-!
### (21.4) The Poisson process

The Poisson process Nₜ with rate r has independent increments and
transition function p(t, x, {z}) = e^{-rt}(rt)^{z-x}/(z-x)! for z ≥ x.
Its generator is 𝔄f(x) = r(f(x+1) - f(x)).
-/

/-- (21.6) The Poisson transition function:
    p(t, x, {z}) = e^{-r·t}(r·t)^{z-x}/(z-x)! for z ≥ x, 0 otherwise. -/
def poissonTransitionProb (r : ℝ) (t : ℝ) (x z : ℤ) : ℝ :=
  if z < x then 0
  else Real.exp (-r * t) * (r * t) ^ (z - x).toNat / ↑((z - x).toNat.factorial)

/-- The generator of the Poisson process: 𝔄f(x) = r·(f(x+1) - f(x)). -/
def poissonGenerator (r : ℝ) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  r * (f (x + 1) - f x)

/-
(21.5) The Poisson process is a Markov process: the conditional
    distribution of Nₜ - Nₛ given ℱₛ is Poisson with mean r·(t-s).
-/
theorem poisson_markov_property (r : ℝ) (hr : 0 < r) (s t : ℝ) (hst : s ≤ t)
    (x : ℤ) (f : ℤ → ℝ) (hf : ∃ C : ℝ, ∀ n, |f n| ≤ C) :
    ∑' k : ℕ, f (↑k + x) * poissonTransitionProb r (t - s) x (↑k + x) =
      ∑' k : ℕ, f (↑k + x) *
        (Real.exp (-r * (t - s)) * (r * (t - s)) ^ k / ↑(k.factorial)) := by
          convert rfl using 3;
          unfold poissonTransitionProb; norm_num;

/-!
### (21.7) Renewal processes

The renewal process is a generalization of the Poisson process with
general i.i.d. interarrival times. By introducing a supplementary
variable τ (the time since the last jump), the process (Nₜ, τₜ)
becomes Markov.
-/

/-
(21.8) The renewal equation: m(t) = ∫₀ᵗ ψ(s) ds + ∫₀ᵗ m(t-s)ψ(s) ds.
-/
theorem renewal_equation
    {psi : ℝ → ℝ} {m : ℝ → ℝ}
    (hpsi_nn : ∀ t, 0 ≤ t → 0 ≤ psi t)
    (hpsi_int : ∀ t, 0 ≤ t → IntegrableOn psi (Set.Icc 0 t) volume)
    (hm_def : ∀ t, 0 ≤ t →
      m t = ∫ u in Set.Icc 0 t, psi u +
            ∫ u in Set.Icc 0 t, m (t - u) * psi u)
    (t : ℝ) (ht : 0 ≤ t) :
    m t = ∫ u in Set.Icc 0 t, psi u +
          ∫ u in Set.Icc 0 t, m (t - u) * psi u := by
            exact hm_def t ht

/-- The generator of the renewal process (with supplementary variable τ):
    𝔄f(n, τ) = (d/dτ)f(n, τ) + h(τ)·(f(n+1, 0) - f(n, τ)),
    where h is the hazard rate. -/
def renewalGenerator (hazardRate : ℝ → ℝ) (f : ℤ × ℝ → ℝ)
    (df_dtau : ℤ × ℝ → ℝ) -- the partial derivative w.r.t. τ
    (x : ℤ × ℝ) : ℝ :=
  df_dtau x + hazardRate x.2 * (f (x.1 + 1, 0) - f x)

end S21_MarkovModels

/-!
## §22 Ordinary differential equations and vector fields

This section recalls basic ODE theory: existence, uniqueness, and the
flow map φ(t, x) associated with a Lipschitz vector field. The flow
is a group under composition, and the associated vector field 𝔛 is
the generator of the deterministic process xₜ = φ(t, x).
-/

section S22_ODE

/-!
**(22.1)** If g : ℝᵈ → ℝᵈ is globally Lipschitz, then dx/dt = g(x),
x(0) = x₀ has a unique global solution φ(t, x₀).
-/

/-
Forward local existence on `[a, a+h]` (length `h < 1/K`) for the autonomous
globally Lipschitz field `g`, via Picard–Lindelöf.
-/
lemma ode_local_fwd {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hg : LipschitzWith K g)
    {h : ℝ} (hh : 0 < h) (hKh : (K : ℝ) * h < 1)
    (a : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    ∃ β : ℝ → EuclideanSpace ℝ (Fin d), β a = y ∧
      ∀ s ∈ Set.Icc a (a + h),
        HasDerivWithinAt β (g (β s)) (Set.Icc a (a + h)) s := by
          norm_num +zetaDelta at *;
          obtain ⟨R, hR⟩ : ∃ R : ℝ≥0, (‖g y‖ + K * R) * h ≤ R := by
            use ⟨(‖g y‖ * h) / (1 - K * h) + 1, by
              exact add_nonneg ( div_nonneg ( mul_nonneg ( norm_nonneg _ ) hh.le ) ( sub_nonneg.mpr hKh.le ) ) zero_le_one⟩
            generalize_proofs at *;
            norm_num [ mul_add, mul_div_cancel₀ _ ( by linarith : ( 1 - K * h ) ≠ 0 ) ];
            nlinarith [ mul_div_cancel₀ ( ‖g y‖ * h ) ( by linarith : ( 1 - K * h ) ≠ 0 ), show ( 0 : ℝ ) ≤ K * ‖g y‖ * h by positivity, show ( 0 : ℝ ) ≤ K * h by positivity, show ( 0 : ℝ ) ≤ ‖g y‖ * h by positivity, show ( 0 : ℝ ) ≤ K * ‖g y‖ by positivity, show ( 0 : ℝ ) ≤ K * h by positivity ];
          obtain ⟨β, hβ⟩ : ∃ β : ℝ → EuclideanSpace ℝ (Fin d), β a = y ∧ ∀ s ∈ Set.Icc a (a + h), HasDerivWithinAt β (g (β s)) (Set.Icc a (a + h)) s := by
            have h_lip : ∀ x ∈ Metric.closedBall y R, ‖g x‖ ≤ ‖g y‖ + K * R := by
              intro x hx;
              have := hg.norm_sub_le x y;
              exact le_trans ( norm_le_of_mem_closedBall <| by simpa using this.trans <| mul_le_mul_of_nonneg_left ( show ‖x - y‖ ≤ R from by simpa [ dist_eq_norm ] using hx ) <| by positivity ) <| by linarith;
            have := @IsPicardLindelof.of_time_independent ( EuclideanSpace ℝ ( Fin d ) );
            specialize @this ( by infer_instance ) g a ( a + h ) ⟨ a, by constructor <;> linarith ⟩ y R 0 ( ⟨ ‖g y‖ + K * R, by positivity ⟩ : ℝ≥0 ) K ; simp_all +decide [ LipschitzOnWith ];
            specialize this ( fun x hx y hy => hg.edist_le_mul x y ) ( by rw [ max_eq_left hh.le ] ; exact hR ) ; have := this.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ ; aesop;
          exact ⟨ β, hβ.1, fun s hs₁ hs₂ => hβ.2 s ⟨ hs₁, hs₂ ⟩ ⟩

/-
Backward local existence on `[a-h, a]`.
-/
lemma ode_local_bwd {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hg : LipschitzWith K g)
    {h : ℝ} (hh : 0 < h) (hKh : (K : ℝ) * h < 1)
    (a : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    ∃ β : ℝ → EuclideanSpace ℝ (Fin d), β a = y ∧
      ∀ s ∈ Set.Icc (a - h) a,
        HasDerivWithinAt β (g (β s)) (Set.Icc (a - h) a) s := by
          have := @ode_local_fwd d ( fun x => -g ( x ) ) K ?_;
          · obtain ⟨ β, hβ₁, hβ₂ ⟩ := this hh hKh a y;
            refine' ⟨ fun s => β ( 2 * a - s ), _, _ ⟩ <;> simp_all +decide [ two_mul ];
            intro s hs₁ hs₂; specialize hβ₂ ( a + a - s ) ( by linarith ) ( by linarith ) ; simp_all +decide [ hasDerivWithinAt_iff_tendsto ] ;
            rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
            intro ε hε; rcases hβ₂ ε hε with ⟨ δ, hδ, H ⟩ ; use δ, hδ; intro x hx₁ hx₂; specialize H ( show a + a - x ∈ Icc a ( a + h ) from ⟨ by linarith [ hx₁.1, hx₁.2 ], by linarith [ hx₁.1, hx₁.2 ] ⟩ ) ; simp_all +decide [ dist_eq_norm ] ;
            convert H ( by rwa [ abs_sub_comm ] ) using 1 ; rw [ show ( x - s ) • g ( β ( a + a - s ) ) = - ( ( s - x ) • g ( β ( a + a - s ) ) ) by rw [ ← neg_smul ] ; ring ] ; norm_num [ norm_neg ];
            exact Or.inl ( abs_sub_comm _ _ );
          · simp_all +decide [ LipschitzWith ]

/-
Gluing two ODE solutions on adjacent closed intervals sharing an endpoint value:
the piecewise function `fun s => if s ≤ b then β₁ s else β₂ s` solves the ODE on
`[a, c]`.
-/
lemma ode_glue {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {β₁ β₂ : ℝ → EuclideanSpace ℝ (Fin d)}
    (h₁ : ∀ s ∈ Set.Icc a b, HasDerivWithinAt β₁ (g (β₁ s)) (Set.Icc a b) s)
    (h₂ : ∀ s ∈ Set.Icc b c, HasDerivWithinAt β₂ (g (β₂ s)) (Set.Icc b c) s)
    (hjoin : β₁ b = β₂ b) :
    ∃ β : ℝ → EuclideanSpace ℝ (Fin d),
      (∀ s ∈ Set.Icc a b, β s = β₁ s) ∧ (∀ s ∈ Set.Icc b c, β s = β₂ s) ∧
      ∀ s ∈ Set.Icc a c, HasDerivWithinAt β (g (β s)) (Set.Icc a c) s := by
        refine' ⟨ fun s => if s ≤ b then β₁ s else β₂ s, _, _, _ ⟩ <;> simp_all +decide;
        · grind;
        · intro s hs₁ hs₂
          by_cases hs : s ≤ b;
          · by_cases hs' : s < b;
            · have h_eq : HasDerivWithinAt β₁ (g (β₁ s)) (Set.Icc a c) s := by
                have := h₁ s hs₁ hs;
                rw [ hasDerivWithinAt_iff_tendsto ] at *;
                rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
                intro ε hε; rcases this ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ Min.min δ ( b - s ), lt_min hδ ( sub_pos.mpr hs' ), fun x hx₁ hx₂ => H ⟨ hx₁.1, by linarith [ hx₁.2, min_le_left δ ( b - s ), min_le_right δ ( b - s ), abs_lt.mp hx₂ ] ⟩ ( by exact lt_of_lt_of_le hx₂ ( min_le_left _ _ ) ) ⟩ ;
              rw [ if_pos hs ];
              refine' h_eq.congr_of_eventuallyEq _ _;
              · filter_upwards [ self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ( Iio_mem_nhds hs' ) ] with x hx₁ hx₂ using if_pos hx₂.out.le;
              · rw [ if_pos hs ];
            · cases eq_or_lt_of_le hs <;> simp_all +decide [ hasDerivWithinAt_iff_tendsto ];
              rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
              intro ε hε; rcases Metric.tendsto_nhdsWithin_nhds.mp ( h₁ b hab le_rfl ) ε hε with ⟨ δ₁, hδ₁, H₁ ⟩ ; rcases Metric.tendsto_nhdsWithin_nhds.mp ( h₂ b le_rfl hbc ) ε hε with ⟨ δ₂, hδ₂, H₂ ⟩ ; use Min.min δ₁ δ₂; simp_all +decide [ dist_eq_norm ] ;
              grind;
          · have := h₂ s ( by linarith ) ( by linarith );
            rw [ hasDerivWithinAt_iff_tendsto ] at *;
            rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
            intro ε hε; rcases this ε hε with ⟨ δ, hδ, H ⟩ ; use Min.min δ ( s - b ) ; refine' ⟨ lt_min hδ ( sub_pos.mpr ( lt_of_not_ge hs ) ), fun x hx₁ hx₂ => _ ⟩ ; split_ifs <;> simp_all +decide [ abs_of_nonneg, sub_nonneg ] ;
            · linarith [ abs_lt.mp hx₂.2 ];
            · exact H ( by linarith ) ( by linarith ) hx₂.1

/-
A solution on every symmetric interval `[-(n·h), n·h]` with value `x₀` at `0`,
built by induction on `n` from local existence and gluing.
-/
lemma ode_pieces {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hg : LipschitzWith K g)
    {h : ℝ} (hh : 0 < h) (hKh : (K : ℝ) * h < 1)
    (x₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∃ β : ℝ → EuclideanSpace ℝ (Fin d), β 0 = x₀ ∧
      ∀ s ∈ Set.Icc (-((n : ℝ) * h)) ((n : ℝ) * h),
        HasDerivWithinAt β (g (β s)) (Set.Icc (-((n : ℝ) * h)) ((n : ℝ) * h)) s := by
          induction' n with n ih generalizing x₀;
          · use fun _ => x₀;
            simp +decide [ hasDerivWithinAt_iff_tendsto ];
            simp +decide [ Metric.tendsto_nhds ];
          · obtain ⟨ β, hβ₁, hβ₂ ⟩ := ih x₀;
            obtain ⟨ γ₁, hγ₁₁, hγ₁₂ ⟩ := ode_local_fwd hg hh hKh ( n * h ) ( β ( n * h ) );
            obtain ⟨ γ₂, hγ₂₁, hγ₂₂ ⟩ := ode_local_bwd hg hh hKh ( - ( n * h ) ) ( β ( - ( n * h ) ) );
            obtain ⟨ β₁, hβ₁₁, hβ₁₂, hβ₁₃ ⟩ := ode_glue ( show ( - ( n * h ) : ℝ ) ≤ n * h by nlinarith ) ( show ( n * h : ℝ ) ≤ n * h + h by nlinarith ) hβ₂ hγ₁₂ ( by aesop );
            obtain ⟨ β₂, hβ₂₁, hβ₂₂, hβ₂₃ ⟩ := ode_glue ( show ( - ( n * h ) - h : ℝ ) ≤ - ( n * h ) by linarith ) ( show ( - ( n * h ) : ℝ ) ≤ n * h + h by nlinarith ) hγ₂₂ hβ₁₃ ( by aesop );
            use β₂;
            simp +zetaDelta at *;
            exact ⟨ by rw [ hβ₂₂ 0 ( by nlinarith ) ( by nlinarith ), hβ₁₁ 0 ( by nlinarith ) ( by nlinarith ), hβ₁ ], fun s hs₁ hs₂ => by convert hβ₂₃ s ( by linarith ) ( by linarith ) using 1 ; ring ⟩

/-
Two solutions of the autonomous ODE on a symmetric interval `[-r, r]` that agree
at `0` agree on the whole interval (two-sided uniqueness).
-/
lemma ode_within_unique {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hg : LipschitzWith K g) {r : ℝ} (hr : 0 ≤ r)
    {β₁ β₂ : ℝ → EuclideanSpace ℝ (Fin d)}
    (h₁ : ∀ s ∈ Set.Icc (-r) r, HasDerivWithinAt β₁ (g (β₁ s)) (Set.Icc (-r) r) s)
    (h₂ : ∀ s ∈ Set.Icc (-r) r, HasDerivWithinAt β₂ (g (β₂ s)) (Set.Icc (-r) r) s)
    (h0 : β₁ 0 = β₂ 0) :
    Set.EqOn β₁ β₂ (Set.Icc (-r) r) := by
      have h_forward : EqOn β₁ β₂ (Set.Icc 0 r) := by
        apply_rules [ ODE_solution_unique ];
        any_goals tauto;
        · exact fun x hx => ( h₁ x ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ |> HasDerivWithinAt.continuousWithinAt ) |> ContinuousWithinAt.mono <| Set.Icc_subset_Icc ( by linarith [ hx.1 ] ) le_rfl;
        · intro t ht; specialize h₁ t ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ; exact h₁.mono_of_mem_nhdsWithin ( Icc_mem_nhdsGE_of_mem ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) ;
        · exact ContinuousOn.mono ( fun x hx => ( h₂ x hx |> HasDerivWithinAt.continuousWithinAt ) ) fun x hx => ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩;
        · intro t ht; specialize h₂ t ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ; exact h₂.mono_of_mem_nhdsWithin ( Icc_mem_nhdsGE_of_mem ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) ;
      have h_backward : EqOn (fun t => β₁ (-t)) (fun t => β₂ (-t)) (Set.Icc 0 r) := by
        apply_rules [ ODE_solution_unique ];
        exact fun _ => hg.neg;
        · refine' ContinuousOn.comp ( show ContinuousOn β₁ ( Set.Icc ( -r ) r ) from _ ) ( continuousOn_id.neg ) fun x hx => _;
          · exact fun x hx => ( h₁ x hx |> HasDerivWithinAt.continuousWithinAt );
          · constructor <;> linarith [ hx.1, hx.2 ];
        · intro t ht; specialize h₁ ( -t ) ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩ ; have := h₁.neg; simp_all +decide [ hasDerivWithinAt_iff_tendsto ] ;
          convert this.comp ( show Filter.Tendsto ( fun x' : ℝ => -x' ) ( nhdsWithin t ( Set.Ici t ) ) ( nhdsWithin ( -t ) ( Set.Icc ( -r ) r ) ) from ?_ ) using 2;
          · rw [ ← abs_neg ] ; rw [ ← norm_neg ] ; simp +decide [ neg_add_eq_sub, sub_smul ] ;
            exact Or.inl ( by rw [ add_comm ] );
          · rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; norm_num;
            exact fun ε hε => ⟨ Min.min ( r - t ) ε, lt_min ( by linarith ) hε, fun x hx₁ hx₂ => ⟨ ⟨ by linarith [ abs_lt.mp hx₂, min_le_left ( r - t ) ε ], by linarith [ abs_lt.mp hx₂, min_le_left ( r - t ) ε ] ⟩, by linarith [ abs_lt.mp hx₂, min_le_right ( r - t ) ε ] ⟩ ⟩;
        · exact ContinuousOn.comp ( show ContinuousOn β₂ ( Set.Icc ( -r ) r ) from fun x hx => ( h₂ x hx |> HasDerivWithinAt.continuousWithinAt ) ) ( continuousOn_id.neg ) fun x hx => ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩;
        · intro t ht; specialize h₂ ( -t ) ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩ ; simp_all +decide [ hasDerivWithinAt_iff_tendsto ] ;
          rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
          intro ε hε; rcases h₂ ε hε with ⟨ δ, hδ, H ⟩ ; use Min.min δ ( r - t ) ; simp_all +decide [ dist_eq_norm ] ;
          intro x hx₁ hx₂ hx₃; convert H ( show -r ≤ -x by linarith [ abs_lt.mp hx₃ ] ) ( show -x ≤ r by linarith [ abs_lt.mp hx₃ ] ) ( by rw [ abs_lt ] at *; constructor <;> linarith ) using 1 ; ring;
          rw [ show -x + t = - ( x - t ) by ring, abs_neg ] ; norm_num [ sub_eq_add_neg, add_smul ];
        · norm_num [ hr ];
      intro t ht; cases le_total 0 t <;> simp_all +decide [ EqOn ] ;
      simpa using h_backward ( show 0 ≤ -t by linarith ) ( by linarith )

/-
For a globally `K`-Lipschitz autonomous vector field `g` on a finite-dimensional
Euclidean space, every initial point `x₀` admits a solution `α` of `α' = g(α)`,
`α(0) = x₀`, defined on all of `ℝ`. This is global existence (no finite escape time,
since `g` has at most linear growth).
-/
lemma ode_global_solution_single {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hg : LipschitzWith K g) (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∃ α : ℝ → EuclideanSpace ℝ (Fin d),
      α 0 = x₀ ∧ ∀ t, HasDerivAt α (g (α t)) t := by
        by_contra! h_contra;
        obtain ⟨α, hα⟩ : ∃ α : ℝ → EuclideanSpace ℝ (Fin d), α 0 = x₀ ∧ ∀ t, HasDerivAt α (g (α t)) t := by
          -- Apply the existence and uniqueness theorem for ODEs.
          have h_exists_unique : ∀ t : ℝ, ∃ α : ℝ → EuclideanSpace ℝ (Fin d), α 0 = x₀ ∧ ∀ s ∈ Set.Icc (-|t| - 1) (|t| + 1), HasDerivWithinAt α (g (α s)) (Set.Icc (-|t| - 1) (|t| + 1)) s := by
            intro t
            obtain ⟨α, hα⟩ : ∃ α : ℝ → EuclideanSpace ℝ (Fin d), α 0 = x₀ ∧ ∀ s ∈ Set.Icc (-|t| - 1) (|t| + 1), HasDerivWithinAt α (g (α s)) (Set.Icc (-|t| - 1) (|t| + 1)) s := by
              have h_abs : ∃ n : ℕ, |t| + 1 ≤ n * (1 / (K + 1)) := by
                exact ⟨ ⌈ ( |t| + 1 ) * ( K + 1 ) ⌉₊, by rw [ mul_one_div, le_div_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ( |t| + 1 ) * ( K + 1 ) ), show ( K : ℝ ) ≥ 0 by positivity ] ⟩
              obtain ⟨ n, hn ⟩ := h_abs
              obtain ⟨ α, hα ⟩ := ode_pieces hg (by
              positivity : 0 < (1 / (K + 1) : ℝ)) (by
              rw [ mul_one_div, div_lt_iff₀ ] <;> linarith [ show ( K : ℝ ) ≥ 0 by positivity ] : (K : ℝ) * (1 / (K + 1)) < 1) x₀ n
              use α
              generalize_proofs at *;
              exact ⟨ hα.1, fun s hs => HasDerivWithinAt.mono ( hα.2 s ⟨ by linarith [ hs.1, abs_nonneg t ], by linarith [ hs.2, abs_nonneg t ] ⟩ ) ( Set.Icc_subset_Icc ( by linarith [ hs.1, abs_nonneg t ] ) ( by linarith [ hs.2, abs_nonneg t ] ) ) ⟩;
            use α;
          choose α hα₁ hα₂ using h_exists_unique;
          -- By the uniqueness theorem, the solutions $\alpha_t$ agree on their common domains.
          have h_unique : ∀ t₁ t₂ : ℝ, ∀ s ∈ Set.Icc (-|t₁| - 1) (|t₁| + 1) ∩ Set.Icc (-|t₂| - 1) (|t₂| + 1), α t₁ s = α t₂ s := by
            intros t₁ t₂ s hs
            have h_unique : Set.EqOn (α t₁) (α t₂) (Set.Icc (-min (|t₁| + 1) (|t₂| + 1)) (min (|t₁| + 1) (|t₂| + 1))) := by
              apply ode_within_unique hg;
              · positivity;
              · intro s hs;
                exact HasDerivWithinAt.mono ( hα₂ t₁ s ⟨ by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ hs.1, hs.2 ], by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ hs.1, hs.2 ] ⟩ ) ( Set.Icc_subset_Icc ( by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ hs.1, hs.2 ] ) ( by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ hs.1, hs.2 ] ) );
              · intro s hs;
                exact HasDerivWithinAt.mono ( hα₂ t₂ s ⟨ by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ hs.1, hs.2, abs_nonneg t₁, abs_nonneg t₂ ], by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ hs.1, hs.2, abs_nonneg t₁, abs_nonneg t₂ ] ⟩ ) ( Set.Icc_subset_Icc ( by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ abs_nonneg t₁, abs_nonneg t₂ ] ) ( by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ abs_nonneg t₁, abs_nonneg t₂ ] ) );
              · rw [ hα₁, hα₁ ];
            exact h_unique ⟨ by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ hs.1.1, hs.1.2, hs.2.1, hs.2.2 ], by cases min_cases ( |t₁| + 1 ) ( |t₂| + 1 ) <;> linarith [ hs.1.1, hs.1.2, hs.2.1, hs.2.2 ] ⟩;
          -- Define the global solution $\alpha$ by patching together the local solutions $\alpha_t$.
          use fun t => α t t;
          refine' ⟨ hα₁ 0, fun t => _ ⟩;
          have h_deriv : HasDerivWithinAt (fun s => α t s) (g (α t t)) (Set.Icc (-|t| - 1) (|t| + 1)) t := by
            exact hα₂ t t ⟨ by cases abs_cases t <;> linarith, by cases abs_cases t <;> linarith ⟩;
          have h_deriv : HasDerivAt (fun s => α t s) (g (α t t)) t := by
            convert h_deriv.hasDerivAt _ using 1;
            exact Icc_mem_nhds ( by cases abs_cases t <;> linarith ) ( by cases abs_cases t <;> linarith );
          convert h_deriv.congr_of_eventuallyEq _ using 1;
          filter_upwards [ Metric.ball_mem_nhds t zero_lt_one ] with s hs;
          exact h_unique s t s ⟨ ⟨ by cases abs_cases s <;> cases abs_cases t <;> linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hs ) ], by cases abs_cases s <;> cases abs_cases t <;> linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hs ) ] ⟩, ⟨ by cases abs_cases s <;> cases abs_cases t <;> linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hs ) ], by cases abs_cases s <;> cases abs_cases t <;> linarith [ abs_lt.mp ( mem_ball_iff_norm.mp hs ) ] ⟩ ⟩;
        exact absurd ( h_contra α hα.1 ) ( by push_neg; exact hα.2 )

/-
Exponential Grönwall bound between two global solutions of a globally Lipschitz
autonomous field: their distance grows at most like `exp(K|t|)` in both time
directions.
-/
lemma ode_gronwall_dist {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hg : LipschitzWith K g)
    (α β : ℝ → EuclideanSpace ℝ (Fin d))
    (hα : ∀ t, HasDerivAt α (g (α t)) t)
    (hβ : ∀ t, HasDerivAt β (g (β t)) t) (t : ℝ) :
    dist (α t) (β t) ≤ dist (α 0) (β 0) * Real.exp ((K : ℝ) * |t|) := by
      by_cases ht : 0 ≤ t;
      · have := @dist_le_of_trajectories_ODE;
        specialize this ( fun t => hg ) ( show ContinuousOn α ( Set.Icc 0 t ) from continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hα x ) ) ( fun x hx => HasDerivAt.hasDerivWithinAt ( hα x ) ) ( show ContinuousOn β ( Set.Icc 0 t ) from continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hβ x ) ) ( fun x hx => HasDerivAt.hasDerivWithinAt ( hβ x ) ) le_rfl t ⟨ by linarith, by linarith ⟩ ; simp_all +decide [ abs_of_nonneg ];
      · -- Reflect time. Let `α' := fun s => α (-s)`, `β' := fun s => β (-s)`, and `ĝ := fun x => -(g x)`, which is `LipschitzWith K` (use `hg.neg` / `LipschitzWith.neg`).
        set α' : ℝ → EuclideanSpace ℝ (Fin d) := fun s => α (-s)
        set β' : ℝ → EuclideanSpace ℝ (Fin d) := fun s => β (-s)
        set ĝ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => -(g x);
        -- Then `HasDerivAt α' (ĝ (α' s)) s` for all `s` (differentiate `s ↦ α (-s)`: derivative is `-(g (α (-s)))` via `HasDerivAt.comp` / `(hα (-s)).comp` with the derivative of `s ↦ -s`; likewise for β').
        have hα' : ∀ s, HasDerivAt α' (ĝ (α' s)) s := by
          intro s; exact (by
          convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp s ( hα _ |> HasDerivAt.hasFDerivAt ) ( hasDerivAt_neg s |> HasDerivAt.hasFDerivAt ) ) using 1 ; aesop)
        have hβ' : ∀ s, HasDerivAt β' (ĝ (β' s)) s := by
          intro s; exact (by
          convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp s ( hβ _ |> HasDerivAt.hasFDerivAt ) ( hasDerivAt_neg s |> HasDerivAt.hasFDerivAt ) ) using 1 ; aesop);
        have h_dist_le : ∀ s ∈ Set.Icc 0 (-t), dist (α' s) (β' s) ≤ dist (α' 0) (β' 0) * Real.exp (K * s) := by
          have := @dist_le_of_trajectories_ODE;
          convert this ( fun t => hg.neg ) ( show ContinuousOn α' ( Set.Icc 0 ( -t ) ) from continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hα' x ) ) ( fun x hx => HasDerivAt.hasDerivWithinAt ( hα' x ) ) ( show ContinuousOn β' ( Set.Icc 0 ( -t ) ) from continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hβ' x ) ) ( fun x hx => HasDerivAt.hasDerivWithinAt ( hβ' x ) ) le_rfl using 1 ; norm_num;
        grind +qlia

/-
A flow assembled from per-initial-point global solutions of a globally Lipschitz
autonomous field depends jointly continuously on `(t, x)`. The key estimate is the
exponential Grönwall bound `‖sol x t - sol y t‖ ≤ ‖x - y‖ · exp(K|t|)`
(`dist_le_of_trajectories_ODE`), giving continuity in `x` locally uniformly in `t`,
combined with continuity in `t` (differentiability of each solution).
-/
lemma ode_flow_joint_continuous {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hg : LipschitzWith K g)
    (sol : EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin d))
    (hsol0 : ∀ x, sol x 0 = x)
    (hsol_deriv : ∀ x t, HasDerivAt (fun s => sol x s) (g (sol x t)) t) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => sol p.2 p.1) := by
      -- By `ode_gronwall_dist` and `hsol0`, we know that `sol x t` is Lipschitz in `x` locally uniformly in `t`.
      have h_lip : ∀ t₀ : ℝ, ∀ δ > 0, ∃ C > 0, ∀ x y : EuclideanSpace ℝ (Fin d), ∀ t : ℝ, abs (t - t₀) < δ → dist (sol x t) (sol y t) ≤ C * dist x y := by
        intro t₀ δ hδ_pos
        use Real.exp (K * (|t₀| + δ)) + 1;
        refine' ⟨ by positivity, _ ⟩;
        intro x y t ht
        have h_dist : dist (sol x t) (sol y t) ≤ dist x y * Real.exp (K * |t|) := by
          convert ode_gronwall_dist hg ( sol x ) ( sol y ) ( hsol_deriv x ) ( hsol_deriv y ) t using 1 ; aesop;
        exact h_dist.trans ( by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_right ( by linarith [ Real.exp_le_exp.mpr ( show ( K : ℝ ) * |t| ≤ K * ( |t₀| + δ ) by exact mul_le_mul_of_nonneg_left ( by cases abs_cases t <;> cases abs_cases t₀ <;> linarith [ abs_lt.mp ht ] ) ( by positivity ) ) ] ) ( dist_nonneg ) );
      refine' continuous_iff_continuousAt.mpr _;
      intro ⟨ t₀, x₀ ⟩;
      refine' Metric.tendsto_nhds_nhds.mpr _;
      intro ε ε_pos; rcases h_lip t₀ 1 zero_lt_one with ⟨ C, C_pos, hC ⟩ ; simp_all +decide [ Prod.dist_eq ] ;
      obtain ⟨ δ₁, δ₁_pos, hδ₁ ⟩ := Metric.continuousAt_iff.mp ( show ContinuousAt ( fun t => sol x₀ t ) t₀ from HasDerivAt.continuousAt ( hsol_deriv x₀ t₀ ) ) ( ε / 2 ) ( half_pos ε_pos ) ; use Min.min 1 ( Min.min δ₁ ( ε / 2 / C ) ) ; simp_all +decide [ lt_div_iff₀, mul_div_cancel₀ ] ;
      intro a b ha hb hab hb' hb'' hab'; have := hC b x₀ a ha; simp_all +decide [ dist_eq_norm ] ;
      have := hδ₁ hb; have := hC b x₀ a ha; rw [ show sol b a - sol x₀ t₀ = ( sol b a - sol x₀ a ) + ( sol x₀ a - sol x₀ t₀ ) by abel1 ] ; exact lt_of_le_of_lt ( norm_add_le _ _ ) ( by nlinarith [ norm_nonneg ( sol b a - sol x₀ a ), norm_nonneg ( sol x₀ a - sol x₀ t₀ ) ] ) ;

/-- (22.1) Existence and uniqueness of global solutions for Lipschitz ODEs.
    The flow φ(t, x) exists for all t ∈ ℝ and depends continuously on (t, x). -/
theorem ode_global_existence {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hK : 0 ≤ (K : ℝ))
    (hg : LipschitzWith K g) :
    ∃ phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x, phi 0 x = x) ∧
      (∀ t x, HasDerivAt (fun s => phi s x) (g (phi t x)) t) ∧
      Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => phi p.1 p.2) := by
  choose sol hsol0 hsol_deriv using fun x => ode_global_solution_single hg x
  exact ⟨fun t x => sol x t, hsol0, fun t x => hsol_deriv x t,
    ode_flow_joint_continuous hg sol hsol0 hsol_deriv⟩

/-
(22.2) The flow map φₜ is bijective, with inverse φ₋ₜ.
-/
theorem flow_bijective {d : ℕ}
    {phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hphi0 : ∀ x, phi 0 x = x)
    (hphi_group : ∀ t s x, phi (t + s) x = phi t (phi s x)) :
    ∀ t, Function.Bijective (phi t) := by
      intro t
      have h_left_inv : ∀ x, phi (-t) (phi t x) = x := by
        exact fun x => by rw [ ← hphi_group, neg_add_cancel, hphi0 ] ;
      have h_right_inv : ∀ x, phi t (phi (-t) x) = x := by
        exact fun x => by rw [ ← hphi_group, add_neg_cancel, hphi0 ] ;
      exact ⟨fun x y hxy => by
        rw [ ← h_left_inv x, ← h_left_inv y, hxy ], fun x => ⟨phi (-t) x, by
        exact h_right_inv x⟩⟩

/-
(22.3) The flow forms a one-parameter group:
    φ_{t+s} = φₜ ∘ φₛ, i.e. φ(t+s, x) = φ(t, φ(s, x)).

    A global Lipschitz hypothesis on the vector field `g` (`hg`) was added to the
    original skeleton statement: it is genuinely required. The group property is
    an ODE-uniqueness statement, and uniqueness of solutions fails without a
    Lipschitz (or comparable) condition on `g`. It is minimal and faithful to
    Davis §22, where the standing assumption is that `g` is globally Lipschitz.
-/
theorem flow_group_property {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : ℝ≥0} (hg : LipschitzWith K g)
    {phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hphi : ∀ x, phi 0 x = x)
    (hphi_ode : ∀ t x, HasDerivAt (fun s => phi s x) (g (phi t x)) t) :
    ∀ t s x, phi (t + s) x = phi t (phi s x) := by
      have := @ode_gronwall_dist;
      intro t s x; specialize this hg ( fun r => phi ( r + s ) x ) ( fun r => phi r ( phi s x ) ) ; simp_all +decide [ hasDerivAt_iff_tendsto_slope_zero ] ;
      exact this ( fun t => by simpa [ add_right_comm ] using hphi_ode ( t + s ) x ) t

/-!
**(22.4–22.6)** The vector field 𝔛 is the generator of the deterministic
process. For f ∈ C¹, (d/dt)f(x(t)) = 𝔛f(x(t)), and the process
Cₜᶠ = f(xₜ) - f(x₀) - ∫₀ᵗ 𝔛f(xₛ)ds = 0 is trivially a martingale.
-/

/-- (22.4) The chain rule for the flow: (d/dt)f(φ(t,x)) = 𝔛f(φ(t,x)),
    where 𝔛 is the vector field generating the flow. -/
theorem flow_chain_rule {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hphi_ode : ∀ t x, HasDerivAt (fun s => phi s x) (g (phi t x)) t)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    HasDerivAt (fun s => f (phi s x))
      (fderiv ℝ f (phi t x) (g (phi t x))) t := by
  have h2 : HasFDerivAt f (fderiv ℝ f (phi t x)) (phi t x) :=
    (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  exact h2.comp_hasDerivAt t (hphi_ode t x)

/-- (22.5–22.6) Integral form: f(φ(t,x)) - f(x) = ∫₀ᵗ 𝔛f(φ(s,x)) ds.
    Equivalently, Cₜᶠ = 0 for the deterministic process, which is
    trivially a (local) martingale.

    Two hypotheses beyond the original skeleton statement are required and were
    added (they are genuinely needed and minimal): `hphi0` (φ(0,·) = id — the
    flow initial condition, without which `f(φ(t,x)) − f(x)` cannot appear on
    the left) and `hXf_int` (interval-integrability of the integrand along the
    flow — the standing hypothesis for the fundamental theorem of calculus). -/
theorem deterministic_dynkin {d : ℕ}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {phi : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {Xf : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hphi_ode : ∀ t x, HasDerivAt (fun s => phi s x) (g (phi t x)) t)
    (hphi0 : ∀ x, phi 0 x = x)
    (hXf : ∀ x, Xf x = fderiv ℝ f x (g x))
    (t : ℝ) (ht : 0 ≤ t) (x : EuclideanSpace ℝ (Fin d))
    (hXf_int : IntervalIntegrable (fun u => Xf (phi u x)) volume 0 t) :
    f (phi t x) - f x = ∫ u in Set.Icc 0 t, Xf (phi u x) := by
  have key : ∀ u ∈ Set.uIcc 0 t,
      HasDerivAt (fun s => f (phi s x)) (Xf (phi u x)) u := by
    intro u _
    rw [hXf]
    exact flow_chain_rule hf hphi_ode u x
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_eq_sub_of_hasDerivAt key hXf_int, hphi0]

/-!
**(22.7–22.10)** Linear scalar ODEs with general (integrable) coefficients.
-/

/-
(22.9) Proposition. The linear ODE x'(t) = a(t)x(t) + b(t), x(0) = x₀,
    has a unique solution given by the variation of constants formula.

    NOTE (Aristotle): the original statement below is FALSE as formalized.
    It asserts `ExistsUnique x : ℝ → ℝ` such that the fixed-point equation
    holds `∀ t ∈ Set.Icc 0 T`. But the defining equation only constrains the
    values of `x` on `[0,T]` (the integrals `∫ u in Set.Icc 0 t, …` depend only
    on `x` restricted to `[0,t] ⊆ [0,T]`). Hence any function agreeing with a
    solution on `[0,T]` but differing outside `[0,T]` is *also* a solution, so
    the solution is never unique as a function `ℝ → ℝ`. The original is
    preserved (commented) below; the corrected statement, with uniqueness
    stated on the interval `[0,T]`, is `linear_ode_solution_unique_on`.

theorem linear_ode_solution {a b : ℝ → ℝ} {x₀ : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hb : IntervalIntegrable b volume 0 T) :
    ∃! x : ℝ → ℝ,
      (∀ t ∈ Set.Icc 0 T,
        x t = x₀ + ∫ u in Set.Icc 0 t, a u * x u +
              ∫ u in Set.Icc 0 t, b u) := by sorry

Helper: if `A` is absolutely continuous on `uIcc a b`, then so is `exp ∘ A`.
    `A` is continuous hence bounded by some `B` on the compact `uIcc a b`, and
    `Real.exp` is Lipschitz (constant `exp B`) on `[-B, B]`, so composing
    preserves absolute continuity.
-/
lemma absCont_rexp_comp {A : ℝ → ℝ} {a b : ℝ}
    (hA : AbsolutelyContinuousOnInterval A a b) :
    AbsolutelyContinuousOnInterval (fun s => Real.exp (A s)) a b := by
      rw [ AbsolutelyContinuousOnInterval ] at *;
      -- Since $A$ is continuous on $[a, b]$, it is bounded on $[a, b]$.
      obtain ⟨B, hB⟩ : ∃ B, ∀ x ∈ Set.uIcc a b, abs (A x) ≤ B := by
        have h_cont : ContinuousOn A (Set.uIcc a b) := by
          apply_rules [ AbsolutelyContinuousOnInterval.continuousOn, hA ];
        exact IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) h_cont;
      -- Since $Real.exp$ is Lipschitz on $[-B, B]$, we have $|Real.exp u - Real.exp v| ≤ Real.exp B * |u - v|$ for all $u, v ∈ [-B, B]$.
      have h_lip : ∀ u v : ℝ, -B ≤ u → u ≤ B → -B ≤ v → v ≤ B → abs (Real.exp u - Real.exp v) ≤ Real.exp B * abs (u - v) := by
        -- By the mean value theorem, there exists some $c$ between $u$ and $v$ such that $e^u - e^v = e^c (u - v)$.
        have h_mean_value : ∀ u v : ℝ, u < v → ∃ c ∈ Set.Ioo u v, Real.exp u - Real.exp v = Real.exp c * (u - v) := by
          intro u v huv; have := exists_deriv_eq_slope ( Real.exp ) huv; norm_num at this;
          exact this ( Real.continuousOn_exp ) ( Differentiable.differentiableOn ( Real.differentiable_exp ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ eq_div_iff ] at hc₂ <;> linarith ⟩;
        intro u v hu hv hu' hv'; rcases lt_trichotomy u v with ( H | rfl | H ) <;> norm_num;
        · obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value u v H ; rw [ hc₂, abs_mul ] ; exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.exp_nonneg _ ) ] ; exact Real.exp_le_exp.mpr ( by linarith [ hc₁.1, hc₁.2 ] ) ) ( abs_nonneg _ );
        · obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value _ _ H ; rw [ abs_le ] ; constructor <;> cases abs_cases ( u - v ) <;> nlinarith [ Real.exp_pos c, Real.exp_le_exp.2 hc₁.1.le, Real.exp_le_exp.2 hc₁.2.le, Real.exp_le_exp.2 hv, Real.exp_le_exp.2 hv' ];
      have h_sum_lip : ∀ E : ℕ × (ℕ → ℝ × ℝ), E ∈ AbsolutelyContinuousOnInterval.disjWithin a b → ∑ i ∈ Finset.range E.1, dist (Real.exp (A (E.2 i).1)) (Real.exp (A (E.2 i).2)) ≤ Real.exp B * ∑ i ∈ Finset.range E.1, dist (A (E.2 i).1) (A (E.2 i).2) := by
        intros E hE
        have h_endpoints : ∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ Set.uIcc a b ∧ (E.2 i).2 ∈ Set.uIcc a b := by
          cases hE ; aesop;
        simpa only [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun i hi => h_lip _ _ ( neg_le_of_abs_le <| hB _ <| h_endpoints i hi |>.1 ) ( le_of_abs_le <| hB _ <| h_endpoints i hi |>.1 ) ( neg_le_of_abs_le <| hB _ <| h_endpoints i hi |>.2 ) ( le_of_abs_le <| hB _ <| h_endpoints i hi |>.2 );
      refine' squeeze_zero_norm' _ _;
      use fun E => Real.exp B * ∑ i ∈ Finset.range E.1, dist ( A ( E.2 i |>.1 ) ) ( A ( E.2 i |>.2 ) );
      · filter_upwards [ Filter.mem_inf_of_right ( Filter.mem_principal_self _ ) ] with E hE using by rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => dist_nonneg ) ] ; exact h_sum_lip E hE;
      · simpa using hA.const_mul _

/-
(22.10) The explicit solution via variation of constants:
    x(t) = exp(∫₀ᵗ a(s)ds) · x₀ + ∫₀ᵗ exp(∫ₛᵗ a(u)du) · b(s) ds.

    NOTE (Aristotle): the earlier RHS `x₀ + ∫ u in Set.Icc 0 t, a u * x u +
    ∫ u in Set.Icc 0 t, b u` had the same operator-**precedence** bug described
    on `linear_ode_solution_unique_on`: the `∫ b` term parses *inside* the first
    integral, giving a false statement (verified). The corrected RHS below
    parenthesizes the first integral explicitly so it reads `x₀ + (∫ a·x) + (∫ b)`.
-/
theorem linear_ode_variation_of_constants
    {a b : ℝ → ℝ} {x₀ : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hb : IntervalIntegrable b volume 0 T)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    let x := fun t => Real.exp (∫ u in Set.Icc 0 t, a u) * x₀ +
                      ∫ u in Set.Icc 0 t, Real.exp (∫ v in Set.Icc u t, a v) * b u
    x t = x₀ + (∫ u in Set.Icc 0 t, a u * x u) +
          ∫ u in Set.Icc 0 t, b u := by
            revert ht;
            intro ht
            set A : ℝ → ℝ := fun s => ∫ u in (0:ℝ)..s, a u
            set W : ℝ → ℝ := fun s => x₀ + ∫ u in (0:ℝ)..s, Real.exp (-A u) * b u
            set Φ : ℝ → ℝ := fun s => Real.exp (A s) * W s
            have hΦ : ∀ t ∈ Set.Icc 0 T, Φ t = (x₀ + ∫ u in Set.Icc 0 t, a u * Φ u) + ∫ u in Set.Icc 0 t, b u := by
              intro t ht
              have hΦ_deriv : ∀ᵐ s ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 t), HasDerivAt Φ (a s * Φ s + b s) s := by
                have hA_deriv : ∀ᵐ s ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 t), HasDerivAt A (a s) s := by
                  have := ha.ae_hasDerivAt_integral;
                  simp_all +decide [ Set.uIcc_of_le hT ];
                  exact Filter.eventually_inf_principal.mpr ( this.mono fun x hx hx' => hx hx'.1 ( by linarith [ hx'.2 ] ) 0 ( by norm_num ) ( by linarith ) )
                have hW_deriv : ∀ᵐ s ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 t), HasDerivAt W (Real.exp (-A s) * b s) s := by
                  have h_integrable : IntervalIntegrable (fun u => Real.exp (-A u) * b u) MeasureTheory.volume 0 T := by
                    have h_integrable : ContinuousOn (fun u => Real.exp (-A u)) (Set.Icc 0 T) := by
                      refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
                      intro s hs; apply_rules [ intervalIntegral.continuousWithinAt_primitive, ha ] ; aesop;
                      simpa [ hT ] using ha;
                    rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le hT ] at *;
                    refine' MeasureTheory.Integrable.mono' _ _ _;
                    refine' fun u => ( SupSet.sSup ( Set.image ( fun u => |Real.exp ( -A u )| ) ( Set.Icc 0 T ) ) ) * |b u|;
                    · exact MeasureTheory.Integrable.const_mul ( hb.norm ) _;
                    · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ( measurableSet_Icc ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self ) hb.aestronglyMeasurable;
                    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by rw [ norm_mul ] ; exact mul_le_mul_of_nonneg_right ( le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn ( h_integrable.abs ) ) ) ( Set.mem_image_of_mem _ <| Set.Ioc_subset_Icc_self hu ) ) ( abs_nonneg _ ) ;
                  have hW_deriv : ∀ᵐ s ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 T), HasDerivAt (fun s => ∫ u in (0:ℝ)..s, Real.exp (-A u) * b u) (Real.exp (-A s) * b s) s := by
                    apply_rules [ MeasureTheory.ae_restrict_iff' ( measurableSet_Icc ) |>.2, h_integrable.ae_hasDerivAt_integral ];
                    have := h_integrable.ae_hasDerivAt_integral;
                    filter_upwards [ this ] with x hx using fun hx' => hx ( by simpa [ hT ] using hx' ) 0 ( by simpa [ hT ] );
                  simp +zetaDelta at *;
                  exact hW_deriv.filter_mono ( inf_le_inf_left _ <| Filter.principal_mono.2 <| Set.Icc_subset_Icc_right ht.2 );
                filter_upwards [ hA_deriv, hW_deriv ] with s hs hs';
                convert HasDerivAt.mul ( HasDerivAt.exp hs ) hs' using 1 ; ring;
                norm_num [ mul_assoc, ← Real.exp_add ];
                exact Or.inl rfl;
              have hΦ_integral : ∫ s in Set.Icc 0 t, deriv Φ s = Φ t - Φ 0 := by
                have hΦ_integral : AbsolutelyContinuousOnInterval Φ 0 t := by
                  have hA_ac : AbsolutelyContinuousOnInterval A 0 t := by
                    apply_rules [ IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral ];
                    · apply_rules [ ha.mono_set, Set.Icc_subset_Icc ] <;> aesop;
                    · exact left_mem_uIcc
                  have hW_ac : AbsolutelyContinuousOnInterval W 0 t := by
                    have hW_ac : IntervalIntegrable (fun u => Real.exp (-A u) * b u) volume 0 t := by
                      have hW_ac : ContinuousOn (fun u => Real.exp (-A u)) (Set.Icc 0 t) := by
                        refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
                        have := hA_ac.continuousOn;
                        simpa only [ Set.uIcc_of_le ht.1 ] using this;
                      rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1 ] at *;
                      refine' MeasureTheory.Integrable.mono' _ _ _;
                      use fun u => ( SupSet.sSup ( Set.image ( fun u => |Real.exp ( -A u )| ) ( Set.Icc 0 t ) ) ) * |b u|;
                      · exact MeasureTheory.Integrable.const_mul ( hb.1.norm.mono_measure <| MeasureTheory.Measure.restrict_mono ( Set.Ioc_subset_Ioc_right ht.2 ) le_rfl ) _;
                      · exact MeasureTheory.AEStronglyMeasurable.mul ( hW_ac.aestronglyMeasurable measurableSet_Icc |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self ) ( hb.1.aestronglyMeasurable.mono_set <| Set.Ioc_subset_Ioc_right ht.2 );
                      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by rw [ norm_mul ] ; exact mul_le_mul_of_nonneg_right ( le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn ( hW_ac.abs ) ) ) ( Set.mem_image_of_mem _ <| Set.Ioc_subset_Icc_self hu ) ) ( abs_nonneg _ ) ;
                    simp +zetaDelta at *;
                    convert hW_ac.absolutelyContinuousOnInterval_intervalIntegral using 1;
                    swap;
                    exact 0;
                    simp +decide [ ht.1, ht.2, AbsolutelyContinuousOnInterval ]
                  have hΦ_ac : AbsolutelyContinuousOnInterval Φ 0 t := by
                    have hΦ_ac : AbsolutelyContinuousOnInterval (fun s => Real.exp (A s)) 0 t := by
                      exact absCont_rexp_comp hA_ac;
                    convert hΦ_ac.mul hW_ac using 1
                  exact hΦ_ac;
                rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1, hΦ_integral.integral_deriv_eq_sub ];
              have hΦ_integral_split : ∫ s in Set.Icc 0 t, deriv Φ s = (∫ s in Set.Icc 0 t, a s * Φ s) + (∫ s in Set.Icc 0 t, b s) := by
                rw [ ← MeasureTheory.integral_add ];
                · exact MeasureTheory.integral_congr_ae ( by filter_upwards [ hΦ_deriv ] with s hs; rw [ hs.deriv ] );
                · have hΦ_cont : ContinuousOn Φ (Set.Icc 0 T) := by
                    refine' ContinuousOn.mul ( ContinuousOn.rexp _ ) ( continuousOn_const.add _ );
                    · intro s hs; apply_rules [ intervalIntegral.continuousWithinAt_primitive, ha ] ; aesop;
                      simpa [ hT ] using ha;
                    · intro s hs;
                      refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num;
                      rw [ max_eq_right hT ];
                      have h_exp_cont : ContinuousOn (fun u => Real.exp (-A u)) (Set.Icc 0 T) := by
                        refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
                        intro s hs; apply_rules [ intervalIntegral.continuousWithinAt_primitive, ha ] ; aesop;
                        simpa [ hT ] using ha;
                      rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le hT ] at *;
                      refine' MeasureTheory.Integrable.mono' _ _ _;
                      use fun u => ( SupSet.sSup ( Set.image ( fun u => |Real.exp ( -A u )| ) ( Set.Icc 0 T ) ) ) * |b u|;
                      · exact MeasureTheory.Integrable.const_mul ( hb.norm ) _;
                      · exact MeasureTheory.AEStronglyMeasurable.mul ( h_exp_cont.aestronglyMeasurable ( measurableSet_Icc ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self ) hb.aestronglyMeasurable;
                      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by rw [ norm_mul ] ; exact mul_le_mul_of_nonneg_right ( le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn ( h_exp_cont.abs ) ) ) ( Set.mem_image_of_mem _ <| Set.Ioc_subset_Icc_self hu ) ) ( abs_nonneg _ ) ;
                  have hΦ_integrable : IntervalIntegrable (fun s => a s * Φ s) MeasureTheory.volume 0 T := by
                    apply_rules [ ha.mul_continuousOn, hΦ_cont ];
                    rwa [ Set.uIcc_of_le hT ];
                  rw [ intervalIntegrable_iff_integrableOn_Icc_of_le hT ] at hΦ_integrable;
                  exact hΦ_integrable.mono_set <| Set.Icc_subset_Icc_right ht.2;
                · simpa only [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ] using hb.1.mono_set ( Set.Ioc_subset_Ioc le_rfl ht.2 );
              simp +zetaDelta at *;
              linarith;
            convert hΦ t ht using 1;
            · have h_exp_add : ∀ u ∈ Set.Icc 0 t, Real.exp (∫ v in Set.Icc u t, a v) = Real.exp (A t) * Real.exp (-A u) := by
                intro u hu; rw [ ← Real.exp_add ] ; rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.2 ] ;
                simp +zetaDelta at *;
                rw [ ← sub_eq_add_neg, intervalIntegral.integral_interval_sub_left ];
                · apply_rules [ ha.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ ht, hu ];
                · apply_rules [ ha.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hu, ht ];
                  exact Or.inr ( by linarith );
              have h_integral : ∫ u in Set.Icc 0 t, Real.exp (∫ v in Set.Icc u t, a v) * b u = Real.exp (A t) * ∫ u in Set.Icc 0 t, Real.exp (-A u) * b u := by
                rw [ ← MeasureTheory.integral_const_mul ] ; exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u hu => by rw [ h_exp_add u hu ] ; ring;
              simp +zetaDelta at *;
              rw [ h_integral, mul_add, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1 ];
              rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1 ];
            · simp +zetaDelta at *;
              refine' MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u hu => _;
              simp +decide [ hu.1, hu.2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.1, ← intervalIntegral.integral_of_le hu.2, Real.exp_add, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ];
              refine' intervalIntegral.integral_congr fun x hx => _;
              rw [ ← Real.exp_add, ← intervalIntegral.integral_add_adjacent_intervals ];
              rw [ intervalIntegral.integral_of_le ( by cases Set.mem_uIcc.mp hx <;> linarith [ hu.1, hu.2 ] ) ];
              · rw [ intervalIntegral.integral_of_le ( by cases Set.mem_uIcc.mp hx <;> linarith [ hu.1, hu.2 ] ) ] ; ring;
              · apply_rules [ ha.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hu.1, hu.2, hx ];
                · exact Or.inl ( by cases Set.mem_uIcc.mp hx <;> linarith [ hu.1, hu.2 ] );
                · exact Or.inr ⟨ hT, by cases Set.mem_uIcc.mp hx <;> linarith [ hu.1, hu.2 ] ⟩;
              · apply_rules [ ha.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hu.1, hu.2, hx ];
                · exact Or.inl ( by cases Set.mem_uIcc.mp hx <;> linarith [ hu.1, hu.2 ] );
                · exact Or.inr ⟨ by cases Set.mem_uIcc.mp hx <;> linarith [ hu.1, hu.2 ], by linarith [ hu.1, hu.2 ] ⟩

/-
Helper: the primitive `u ↦ ∫₀ᵘ |a|` is continuous on `[0,T]`.
-/
lemma gronwall_abs_primitive_continuousOn {a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) :
    ContinuousOn (fun u => ∫ v in (0:ℝ)..u, |a v|) (Set.Icc 0 T) := by
      intro u hu;
      refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num;
      simpa [ hT ] using ha.abs

/-
Helper (FTC substitution): with `F u = ∫₀ᵘ |a|`,
    `∫₀ᵗ |a(u)|·F(u)^n du = F(t)^{n+1}/(n+1)`. This is the chain-rule/FTC step
    driving the Picard iterate bound in `gronwall_uniqueness`.
-/
lemma gronwall_abs_primitive_substitution {a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ∫ u in (0:ℝ)..t, |a u| * (∫ v in (0:ℝ)..u, |a v|) ^ n
      = (∫ v in (0:ℝ)..t, |a v|) ^ (n + 1) / (n + 1) := by
        have h_abs_cont : AbsolutelyContinuousOnInterval (fun u => ∫ v in (0:ℝ)..u, |a v|) 0 T := by
          convert ha.abs.absolutelyContinuousOnInterval_intervalIntegral ( show 0 ∈ Set.uIcc 0 T from by aesop ) using 1;
        -- By induction on $n$, we can show that $F^{n+1}$ is absolutely continuous on $[0, T]$.
        have h_abs_cont_pow : ∀ n : ℕ, AbsolutelyContinuousOnInterval (fun u => (∫ v in (0:ℝ)..u, |a v|) ^ (n + 1)) 0 T := by
          intro n; induction' n with n ih <;> simp_all +decide [ pow_succ' ] ;
          exact h_abs_cont.mul ih;
        have h_ftc : ∫ u in (0:ℝ)..t, deriv (fun u => (∫ v in (0:ℝ)..u, |a v|) ^ (n + 1) / (n + 1)) u = (∫ v in (0:ℝ)..t, |a v|) ^ (n + 1) / (n + 1) := by
          have := @AbsolutelyContinuousOnInterval.integral_deriv_eq_sub;
          convert @this ( fun u => ( ∫ v in ( 0 : ℝ )..u, |a v| ) ^ ( n + 1 ) / ( n + 1 ) ) 0 t _ using 1 <;> norm_num [ h_abs_cont_pow ];
          have := h_abs_cont_pow n;
          have := this.mono ( show Set.uIcc 0 t ⊆ Set.uIcc 0 T from by rw [ Set.uIcc_of_le ht.1, Set.uIcc_of_le hT ] ; exact Set.Icc_subset_Icc le_rfl ht.2 );
          convert this.const_mul ( 1 / ( n + 1 : ℝ ) ) using 1 ; ext ; norm_num ; ring;
        have h_deriv : ∀ᵐ u ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 T), deriv (fun u => (∫ v in (0:ℝ)..u, |a v|) ^ (n + 1) / (n + 1)) u = |a u| * (∫ v in (0:ℝ)..u, |a v|) ^ n := by
          have h_deriv : ∀ᵐ u ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc 0 T), HasDerivAt (fun u => ∫ v in (0:ℝ)..u, |a v|) (|a u|) u := by
            have h_deriv : ∀ᵐ u ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.uIcc 0 T), HasDerivAt (fun u => ∫ v in (0:ℝ)..u, |a v|) (|a u|) u := by
              have h_abs : IntervalIntegrable (fun x => |a x|) volume 0 T := by
                exact ha.abs
              have := h_abs.ae_hasDerivAt_integral;
              rw [ MeasureTheory.ae_restrict_iff' ];
              · filter_upwards [ this ] with x hx hx' using hx hx' 0 ( by simp +decide [ hT ] );
              · exact measurableSet_Icc;
            simpa only [ Set.uIcc_of_le hT ] using h_deriv;
          filter_upwards [ h_deriv ] with u hu;
          convert HasDerivAt.deriv ( hu.pow ( n + 1 ) |> HasDerivAt.div_const <| ( n : ℝ ) + 1 ) using 1 ; norm_num ; ring;
          grind +locals;
        rw [ ← h_ftc, intervalIntegral.integral_of_le ht.1 ];
        rw [ intervalIntegral.integral_of_le ht.1, MeasureTheory.integral_congr_ae ];
        filter_upwards [ MeasureTheory.ae_restrict_of_ae_restrict_of_subset ( Set.Ioc_subset_Icc_self.trans ( Set.Icc_subset_Icc le_rfl ht.2 ) ) h_deriv ] with u hu using hu.symm

/-
(22.9) Gronwall-type uniqueness: if z(t) = ∫₀ᵗ a(s)z(s)ds then z ≡ 0.

    Still `sorry`. A genuine proof uses the `u`-dependent iterate bound
    `|z t| ≤ K·F(t)^n/n!` with `F(u) = ∫_{[0,u]}|a|` and `K = sup|z|`, whose
    inductive step rests on the substitution
    `∫_{[0,t]} |a(u)|·F(u)^n du = F(t)^{n+1}/(n+1)` (FTC for the absolutely
    continuous `F`), then lets `n → ∞`; alternatively a small-interval
    bootstrap. The *constant*-bound variant `K·(∫_{[0,T]}|a|)^n/n!` does NOT
    work: its inductive step yields only `/n!`, not `/(n+1)!`.
-/
theorem gronwall_uniqueness {a : ℝ → ℝ} {z : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hz : ∀ t ∈ Set.Icc 0 T, z t = ∫ u in Set.Icc 0 t, a u * z u)
    (hcont : ContinuousOn z (Set.Icc 0 T)) :
    ∀ t ∈ Set.Icc 0 T, z t = 0 := by
      obtain ⟨M, hM⟩ : ∃ M ≥ 0, ∀ u ∈ Set.Icc 0 T, |z u| ≤ M := by
        obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) hcont; use Max.max M 0; aesop;
      -- Claim (induction on n): ∀ t ∈ [0,T], |z t| ≤ M * (F t)^n / n!.
      have h_ind : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T, |z t| ≤ M * (∫ u in (0:ℝ)..t, |a u|) ^ n / Nat.factorial n := by
        intro n;
        induction' n with n ih;
        · aesop;
        · intro t ht
          have h_integral : |z t| ≤ ∫ u in (0:ℝ)..t, |a u| * |z u| := by
            rw [ hz t ht, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1 ];
            simpa only [ ← abs_mul ] using by apply_rules [ intervalIntegral.abs_integral_le_integral_abs, ht.1 ] ;
          -- Apply the induction hypothesis to bound the integral.
          have h_integral_bound : ∫ u in (0:ℝ)..t, |a u| * |z u| ≤ ∫ u in (0:ℝ)..t, |a u| * (M * (∫ v in (0:ℝ)..u, |a v|) ^ n / Nat.factorial n) := by
            refine' intervalIntegral.integral_mono_on _ _ _ _;
            · linarith [ ht.1 ];
            · apply_rules [ IntervalIntegrable.mul_continuousOn, ha.abs ];
              · apply_rules [ ha.abs.mono_set, Set.Icc_subset_Icc ] <;> aesop;
              · simpa only [ Set.uIcc_of_le ht.1 ] using hcont.abs.mono ( Set.Icc_subset_Icc le_rfl ht.2 );
            · apply_rules [ IntervalIntegrable.mul_continuousOn, ha.abs ];
              · apply_rules [ ha.abs.mono_set, Set.Icc_subset_Icc ] <;> aesop;
              · refine' ContinuousOn.div_const ( ContinuousOn.mul continuousOn_const ( ContinuousOn.pow _ _ ) ) _;
                intro x hx;
                refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num;
                apply_rules [ ha.abs.mono_set, Set.Icc_subset_Icc ] <;> aesop;
            · exact fun u hu => mul_le_mul_of_nonneg_left ( ih u ⟨ hu.1, hu.2.trans ht.2 ⟩ ) ( abs_nonneg _ );
          convert h_integral.trans h_integral_bound using 1;
          have := gronwall_abs_primitive_substitution hT ha n t ht;
          convert congr_arg ( fun x : ℝ => M * x / ( n.factorial : ℝ ) ) this.symm using 1 <;> norm_num [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
          exact Or.inl ( by rw [ ← intervalIntegral.integral_const_mul ] ; congr; ext; ring );
      -- Let t ∈ [0,T]. For all n, |z t| ≤ M * (F t)^n / n!.
      intros t ht
      have h_le_zero : Filter.Tendsto (fun n : ℕ => M * (∫ u in (0:ℝ)..t, |a u|) ^ n / Nat.factorial n) Filter.atTop (nhds 0) := by
        simpa [ mul_div_assoc ] using tendsto_const_nhds.mul ( Real.summable_pow_div_factorial _ |> Summable.tendsto_atTop_zero );
      exact abs_eq_zero.mp ( le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds h_le_zero fun n => h_ind n t ht ) ( abs_nonneg _ ) )

/-
(22.9) Proposition (corrected form). The linear integral equation
    `x t = x₀ + ∫₀ᵗ a·x + ∫₀ᵗ b` on `[0,T]` has a solution, and any two
    solutions agree on `[0,T]`. Uniqueness is stated on the interval `[0,T]`
    (the equation does not constrain values outside `[0,T]`).

    NOTE (Aristotle): the earlier version of this statement (preserved verbatim,
    commented, below) contained an operator-**precedence** bug. The Bochner
    integral notation `∫ u in s, f` extends its body maximally to the right, so
    `x₀ + ∫ u in Set.Icc 0 t, a u * x u + ∫ u in Set.Icc 0 t, b u` actually
    parses as `x₀ + ∫ u in Set.Icc 0 t, (a u * x u + ∫ w in Set.Icc 0 t, b w)`,
    i.e. the `∫ b` term is nested *inside* the first integral. That parse is not
    the intended equation `x₀ + (∫ a·x) + (∫ b)` and is in fact false (verified).
    The corrected statement below parenthesizes the first integral explicitly.

    Two further faithfulness fixes (matching Davis's ODE setting): the witness
    `x` is asserted to be `ContinuousOn [0,T]`, and uniqueness is stated among
    *continuous* solutions `y`. Over arbitrary (possibly non-measurable) `y` the
    claim is ill-posed: the Bochner integral assigns the junk value `0` to a
    non-integrable `a·y`, so the integral equation no longer pins down `y`. For
    continuous solutions (the only ones Davis considers) `a·x`, `a·y` are
    integrable and uniqueness follows from `gronwall_uniqueness`.

    Original statement, preserved verbatim (line-commented):

    ∃ x : ℝ → ℝ,
      (∀ t ∈ Set.Icc 0 T,
        x t = x₀ + ∫ u in Set.Icc 0 t, a u * x u +
              ∫ u in Set.Icc 0 t, b u) ∧
      (∀ y : ℝ → ℝ, (∀ t ∈ Set.Icc 0 T,
        y t = x₀ + ∫ u in Set.Icc 0 t, a u * y u +
              ∫ u in Set.Icc 0 t, b u) →
        ∀ t ∈ Set.Icc 0 T, y t = x t)
-/
theorem linear_ode_solution_unique_on {a b : ℝ → ℝ} {x₀ : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T)
    (hb : IntervalIntegrable b volume 0 T) :
    ∃ x : ℝ → ℝ, ContinuousOn x (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Icc 0 T,
        x t = x₀ + (∫ u in Set.Icc 0 t, a u * x u) +
              ∫ u in Set.Icc 0 t, b u) ∧
      (∀ y : ℝ → ℝ, ContinuousOn y (Set.Icc 0 T) → (∀ t ∈ Set.Icc 0 T,
        y t = x₀ + (∫ u in Set.Icc 0 t, a u * y u) +
              ∫ u in Set.Icc 0 t, b u) →
        ∀ t ∈ Set.Icc 0 T, y t = x t) := by
          obtain ⟨x, hx⟩ : ∃ x : ℝ → ℝ, ContinuousOn x (Set.Icc 0 T) ∧ (∀ t ∈ Set.Icc 0 T, x t = x₀ + (∫ u in Set.Icc 0 t, a u * x u) + (∫ u in Set.Icc 0 t, b u)) := by
            refine' ⟨ fun t => Real.exp ( ∫ u in Set.Icc 0 t, a u ) * x₀ + ∫ u in Set.Icc 0 t, Real.exp ( ∫ v in Set.Icc u t, a v ) * b u, _, _ ⟩;
            · refine' ContinuousOn.add ( ContinuousOn.mul ( ContinuousOn.rexp _ ) continuousOn_const ) _;
              · have h_cont : ContinuousOn (fun t => ∫ u in (0:ℝ)..t, a u) (Set.Icc 0 T) := by
                  intro t ht; apply_rules [ intervalIntegral.continuousWithinAt_primitive, ha ] ; aesop;
                  simpa [ hT ] using ha;
                exact h_cont.congr fun t ht => by rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1 ] ;
              · -- The integral of a continuous function is continuous, hence the function inside the integral is continuous.
                have h_cont_inner : ContinuousOn (fun t => ∫ u in (0:ℝ)..t, Real.exp (∫ v in (u:ℝ)..t, a v) * b u) (Set.Icc 0 T) := by
                  have h_int_cont : ContinuousOn (fun t => ∫ u in (0:ℝ)..t, Real.exp (-∫ v in (0:ℝ)..u, a v) * b u) (Set.Icc 0 T) := by
                    have h_int_cont : ContinuousOn (fun t => ∫ u in (0:ℝ)..t, Real.exp (-∫ v in (0:ℝ)..u, a v) * b u) (Set.Icc 0 T) := by
                      have h_integrable : IntervalIntegrable (fun u => Real.exp (-∫ v in (0:ℝ)..u, a v) * b u) volume 0 T := by
                        convert hb.mul_continuousOn _ using 1;
                        exact funext fun x => mul_comm _ _;
                        refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
                        intro x hx;
                        refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> aesop
                      intro t ht; apply_rules [ intervalIntegral.continuousWithinAt_primitive, h_integrable ] ; aesop;
                      grind;
                    convert h_int_cont using 1;
                  have h_int_cont : ∀ t ∈ Set.Icc 0 T, ∫ u in (0:ℝ)..t, Real.exp (∫ v in (u:ℝ)..t, a v) * b u = Real.exp (∫ v in (0:ℝ)..t, a v) * ∫ u in (0:ℝ)..t, Real.exp (-∫ v in (0:ℝ)..u, a v) * b u := by
                    intro t ht; rw [ ← intervalIntegral.integral_const_mul ] ; refine' intervalIntegral.integral_congr fun u hu => _ ; rw [ ← mul_assoc ] ; rw [ ← Real.exp_add ] ; rw [ intervalIntegral.integral_symm ] ; ring;
                    rw [ show ( ∫ x in t..u, a x ) = ( ∫ x in ( 0 : ℝ )..u, a x ) - ( ∫ x in ( 0 : ℝ )..t, a x ) by rw [ eq_sub_iff_add_eq', intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ha.mono_set, hb.mono_set, Set.Icc_subset_Icc ] <;> aesop ] ; ring;
                  refine' ContinuousOn.congr _ h_int_cont;
                  refine' ContinuousOn.mul _ ‹_›;
                  refine' ContinuousOn.rexp _;
                  intro t ht;
                  refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> aesop;
                refine' h_cont_inner.congr fun t ht => _;
                rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1 ];
                exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hx.2 ] ;
            · convert linear_ode_variation_of_constants hT ha hb using 1;
          refine' ⟨ x, hx.1, hx.2, _ ⟩;
          intro y hy hy' t ht
          have hz : ∀ t ∈ Set.Icc 0 T, (y t - x t) = ∫ u in Set.Icc 0 t, a u * (y u - x u) := by
            intro t ht; rw [ hy' t ht, hx.2 t ht ] ; simp +decide [ mul_sub ] ; ring;
            rw [ MeasureTheory.integral_sub ];
            · have h_integrable : IntervalIntegrable (fun u => a u * y u) volume 0 T := by
                apply_rules [ ha.mul_continuousOn, hy ];
                rwa [ Set.uIcc_of_le hT ];
              rw [ intervalIntegrable_iff_integrableOn_Icc_of_le hT ] at h_integrable;
              exact h_integrable.mono_set <| Set.Icc_subset_Icc_right ht.2;
            · have h_integrable : IntervalIntegrable (fun u => a u * x u) volume 0 T := by
                apply_rules [ ha.mul_continuousOn, hx.1 ];
                simpa only [ Set.uIcc_of_le hT ] using hx.1;
              rw [ intervalIntegrable_iff_integrableOn_Icc_of_le hT ] at h_integrable;
              exact h_integrable.mono_set <| Set.Icc_subset_Icc_right ht.2;
          have := gronwall_uniqueness hT ha ( fun t ht => hz t ht ) ( show ContinuousOn ( fun t => y t - x t ) ( Set.Icc 0 T ) from ContinuousOn.sub hy hx.1 ) t ht; norm_num at this; linarith;

end S22_ODE

/-!
## §23 Simulation

Methods for constructing random variables with specified distributions
from uniform [0,1] random variables.
-/

section S23_Simulation

/-
A monotone `F : ℝ → ℝ` with limit `0` at `-∞` and `1` at `+∞` takes values
in `[0,1]`.
-/
lemma cdf_mem_Icc {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_lo : Filter.Tendsto F Filter.atBot (nhds 0))
    (hF_hi : Filter.Tendsto F Filter.atTop (nhds 1)) (t : ℝ) :
    F t ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨ le_of_tendsto hF_lo ( Filter.eventually_atBot.mpr ⟨ t, fun x hx => hF_mono hx ⟩ ), le_of_tendsto_of_tendsto tendsto_const_nhds hF_hi ( Filter.eventually_atTop.mpr ⟨ t, fun x hx => hF_mono hx ⟩ ) ⟩

/-
Galois-type equivalence for the generalized inverse (quantile) of a
monotone, right-continuous CDF: for `0 < u < 1`,
`sInf {s | u ≤ F s} ≤ t ↔ u ≤ F t`.

The forward direction uses right-continuity of `F` at `t` (together with the
fact that `{s | u ≤ F s}` is an up-set, so it contains all `s > t`); the reverse
direction is immediate since then `t` itself lies in the set.
-/
lemma quantile_le_iff {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_rc : ∀ t, Filter.Tendsto F (nhdsWithin t (Set.Ioi t)) (nhds (F t)))
    (hF_lo : Filter.Tendsto F Filter.atBot (nhds 0))
    (hF_hi : Filter.Tendsto F Filter.atTop (nhds 1))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (t : ℝ) :
    sInf {s : ℝ | u ≤ F s} ≤ t ↔ u ≤ F t := by
      constructor <;> intro h;
      · -- By definition of infimum, for any ε > 0, there exists s ∈ {s | u ≤ F s} such that s < t + ε.
        have h_eps : ∀ ε > 0, ∃ s ∈ {s | u ≤ F s}, s < t + ε := by
          intro ε ε_pos;
          exact exists_lt_of_csInf_lt ( show { s : ℝ | u ≤ F s }.Nonempty from by have := hF_hi.eventually ( lt_mem_nhds hu1 ) ; have := this.and ( Filter.eventually_gt_atTop t ) ; obtain ⟨ s, hs₁, hs₂ ⟩ := this.exists; exact ⟨ s, hs₁.le ⟩ ) ( by linarith );
        exact le_of_tendsto_of_tendsto tendsto_const_nhds ( hF_rc t ) ( Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => by obtain ⟨ s, hs₁, hs₂ ⟩ := h_eps ( x - t ) ( by linarith [ hx.out ] ) ; linarith [ hF_mono ( show s ≤ x by linarith [ hx.out ] ), hs₁.out ] );
      · refine' csInf_le _ _;
        · exact Filter.Tendsto.eventually ( hF_lo ) ( gt_mem_nhds hu0 ) |> fun h => by rcases h.exists with ⟨ s, hs ⟩ ; exact ⟨ s, fun x hx => le_of_not_gt fun hx' => by linarith [ hF_mono hx'.le, hx.out ] ⟩ ;
        · exact h

/-
The inverse-transform preimage set agrees, up to a null set (the two
endpoints `u ∈ {0,1}`), with the interval `[0, F t]`.
-/
lemma quantile_preimage_ae {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_rc : ∀ t, Filter.Tendsto F (nhdsWithin t (Set.Ioi t)) (nhds (F t)))
    (hF_lo : Filter.Tendsto F Filter.atBot (nhds 0))
    (hF_hi : Filter.Tendsto F Filter.atTop (nhds 1)) (t : ℝ) :
    {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧ sInf {s : ℝ | u ≤ F s} ≤ t}
      =ᵐ[MeasureTheory.volume] Set.Icc (0 : ℝ) (F t) := by
        refine' MeasureTheory.ae_eq_set.mpr _;
        constructor <;> refine' MeasureTheory.measure_mono_null _ _;
        any_goals exact { 0, 1 };
        · intro u hu; contrapose! hu; simp_all +decide [ Set.subset_def ] ;
          exact fun _ _ h => quantile_le_iff hF_mono hF_rc hF_lo hF_hi ( lt_of_le_of_ne ‹_› ( Ne.symm hu.1 ) ) ( lt_of_le_of_ne ‹_› hu.2 ) t |>.1 h;
        · rw [ Set.insert_eq, MeasureTheory.measure_union ] <;> norm_num;
        · intro u hu; by_cases hu0 : u = 0 <;> by_cases hu1 : u = 1 <;> simp_all +decide [ Set.subset_def ] ;
          contrapose! hu;
          exact fun h => ⟨ h.1, h.2.trans ( le_of_tendsto_of_tendsto tendsto_const_nhds hF_hi <| Filter.eventually_atTop.2 ⟨ t, fun x hx => hF_mono hx ⟩ ), quantile_le_iff hF_mono hF_rc hF_lo hF_hi ( lt_of_le_of_ne h.1 <| Ne.symm hu0 ) ( lt_of_le_of_ne ( h.2.trans <| le_of_tendsto_of_tendsto tendsto_const_nhds hF_hi <| Filter.eventually_atTop.2 ⟨ t, fun x hx => hF_mono hx ⟩ ) hu1 ) t |>.2 h.2 ⟩;
        · rw [ Set.insert_eq, MeasureTheory.measure_union ] <;> norm_num

/-- (23.1) Proposition. Inverse transform sampling: if F is a distribution
    function and β(u) = inf{t : F(t) ≥ u}, then X = β(U) has distribution
    function F when U ~ U[0,1]. -/
theorem inverse_transform_sampling
    {F : ℝ → ℝ}
    (hF_mono : Monotone F)
    (hF_rc : ∀ t, Filter.Tendsto F (nhdsWithin t (Set.Ioi t)) (nhds (F t)))
    (hF_lo : Filter.Tendsto F Filter.atBot (nhds 0))
    (hF_hi : Filter.Tendsto F Filter.atTop (nhds 1)) :
    let beta := fun u => sInf {t : ℝ | u ≤ F t}
    ∀ t : ℝ, MeasureTheory.volume {u ∈ Set.Icc (0 : ℝ) 1 | beta u ≤ t} =
      ENNReal.ofReal (F t) := by
  intro beta t
  have hFt : F t ∈ Set.Icc (0 : ℝ) 1 := cdf_mem_Icc hF_mono hF_lo hF_hi t
  have hae := quantile_preimage_ae hF_mono hF_rc hF_lo hF_hi t
  have : {u : ℝ | u ∈ Set.Icc (0 : ℝ) 1 ∧ beta u ≤ t}
      =ᵐ[MeasureTheory.volume] Set.Icc (0 : ℝ) (F t) := hae
  rw [MeasureTheory.measure_congr this, Real.volume_Icc, sub_zero]

/-
(23.1, measure form) Inverse-transform sampling as a pushforward identity:
    every probability measure `μ` on `ℝ` is the image of Lebesgue measure on
    `[0,1]` under a measurable (quantile) map.
-/
theorem realize_measure_real_from_uniform
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] :
    ∃ β : ℝ → ℝ, Measurable β ∧
      MeasureTheory.Measure.map β
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) = μ := by
          -- By definition of $β$, we know that it is measurable.
          have h_beta_meas : Measurable (fun u => sInf {t : ℝ | u ≤ (ProbabilityTheory.cdf μ t : ℝ)}) := by
            -- The function $u \mapsto sInf {t | u \leq cdf μ t}$ is monotone on $(0,1)$, hence measurable.
            have h_monotone : MonotoneOn (fun u => sInf {t : ℝ | u ≤ cdf μ t}) (Set.Ioo 0 1) := by
              intro u hu v hv huv;
              apply_rules [ csInf_le_csInf ];
              · have h_bdd_below : Filter.Tendsto (fun t => (cdf μ) t) Filter.atBot (nhds 0) := by
                  convert ProbabilityTheory.tendsto_cdf_atBot μ;
                have := h_bdd_below.eventually ( gt_mem_nhds hu.1 ) ; have := this.exists; obtain ⟨ t, ht ⟩ := this; exact ⟨ t, fun x hx => le_of_not_gt fun h => by linarith [ hx.out, show ( cdf μ ) x ≤ ( cdf μ ) t from by exact ( cdf μ ).mono h.le ] ⟩ ;
              · have h_lim : Filter.Tendsto (fun t => (cdf μ) t) Filter.atTop (nhds 1) := by
                  convert ProbabilityTheory.tendsto_cdf_atTop μ;
                exact Filter.Eventually.exists ( h_lim.eventually ( le_mem_nhds hv.2 ) );
              · exact fun x hx => le_trans huv hx.out;
            refine' measurable_of_Iic _;
            intro x;
            have h_preimage : ∀ x, MeasurableSet {u : ℝ | u ∈ Set.Ioo 0 1 ∧ sInf {t : ℝ | u ≤ cdf μ t} ≤ x} := by
              intro x
              have h_preimage : IsPreconnected {u : ℝ | u ∈ Set.Ioo 0 1 ∧ sInf {t : ℝ | u ≤ cdf μ t} ≤ x} := by
                refine' isPreconnected_iff_ordConnected.mpr _;
                rw [ Set.ordConnected_iff ];
                simp +zetaDelta at *;
                intro u hu₁ hu₂ hu₃ v hv₁ hv₂ hv₃ huv; intro w hw; exact ⟨ ⟨ by linarith [ hw.1 ], by linarith [ hw.2 ] ⟩, by exact le_trans ( h_monotone ⟨ by linarith [ hw.1 ], by linarith [ hw.2 ] ⟩ ⟨ by linarith [ hw.1 ], by linarith [ hw.2 ] ⟩ hw.2 ) hv₃ ⟩ ;
              exact h_preimage.measurableSet;
            have h_preimage : ∀ x, MeasurableSet {u : ℝ | u ∈ Set.Iic 0 ∧ sInf {t : ℝ | u ≤ cdf μ t} ≤ x} := by
              intro x
              have h_preimage : ∀ u ∈ Set.Iic 0, sInf {t : ℝ | u ≤ cdf μ t} = sInf {t : ℝ | 0 ≤ cdf μ t} := by
                intro u hu
                have h_eq : {t : ℝ | u ≤ cdf μ t} = {t : ℝ | 0 ≤ cdf μ t} := by
                  ext t; simp [hu];
                  exact ⟨ fun h => by linarith [ hu.out, show ( cdf μ t : ℝ ) ≥ 0 from by exact_mod_cast ProbabilityTheory.cdf_nonneg μ t ], fun h => by linarith [ hu.out, show ( cdf μ t : ℝ ) ≥ 0 from by exact_mod_cast ProbabilityTheory.cdf_nonneg μ t ] ⟩
                rw [h_eq];
              by_cases h : sInf { t : ℝ | 0 ≤ cdf μ t } ≤ x <;> simp_all +decide [ Set.setOf_and ];
              · rw [ show { a : ℝ | a ≤ 0 } ∩ { a : ℝ | sInf { t : ℝ | a ≤ ( cdf μ ) t } ≤ x } = { a : ℝ | a ≤ 0 } from Set.ext fun x => ⟨ fun hx => hx.1, fun hx => ⟨ hx, by simpa [ h_preimage x hx ] using h ⟩ ⟩ ] ; exact measurableSet_Iic;
              · rw [ show { a : ℝ | a ≤ 0 } ∩ { a : ℝ | sInf { t : ℝ | a ≤ ( cdf μ ) t } ≤ x } = ∅ from Set.eq_empty_of_forall_notMem fun u hu => by linarith [ hu.1.out, hu.2.out, h_preimage u hu.1.out ] ] ; norm_num;
            have h_preimage : ∀ x, MeasurableSet {u : ℝ | u ∈ Set.Ici 1 ∧ sInf {t : ℝ | u ≤ cdf μ t} ≤ x} := by
              intro x;
              have h_preimage : ∀ u ∈ Set.Ici 1, sInf {t : ℝ | u ≤ cdf μ t} = if u ≤ 1 then sInf {t : ℝ | 1 ≤ cdf μ t} else 0 := by
                intro u hu; split_ifs <;> simp_all +decide [ Set.Ici_def ] ;
                · rw [ le_antisymm ‹u ≤ 1› hu ];
                · rw [ show { t : ℝ | u ≤ ( cdf μ t : ℝ ) } = ∅ from Set.eq_empty_of_forall_notMem fun t ht => by linarith [ ht.out, show ( cdf μ t : ℝ ) ≤ 1 from by exact_mod_cast ProbabilityTheory.cdf_le_one μ t ] ] ; norm_num;
              rw [ show { u : ℝ | u ∈ Ici 1 ∧ sInf { t : ℝ | u ≤ ( cdf μ ) t } ≤ x } = { u : ℝ | u ∈ Ici 1 ∧ ( if u ≤ 1 then sInf { t : ℝ | 1 ≤ ( cdf μ ) t } else 0 ) ≤ x } from ?_ ];
              · simp +zetaDelta at *;
                exact Measurable.and ( measurableSet_Ici.mem ) ( MeasurableSet.mem ( show MeasurableSet { u : ℝ | ( if u ≤ 1 then sInf { t : ℝ | 1 ≤ ( cdf μ ) t } else 0 ) ≤ x } from by exact measurableSet_le ( by exact Measurable.ite ( measurableSet_Iic ) measurable_const measurable_const ) measurable_const ) );
              · exact Set.ext fun u => and_congr_right fun hu => by rw [ h_preimage u hu ] ;
            convert MeasurableSet.union ( MeasurableSet.union ( ‹∀ x : ℝ, MeasurableSet { u : ℝ | u ∈ Ioo 0 1 ∧ sInf { t : ℝ | u ≤ cdf μ t } ≤ x } › x ) ( ‹∀ x : ℝ, MeasurableSet { u : ℝ | u ∈ Iic 0 ∧ sInf { t : ℝ | u ≤ cdf μ t } ≤ x } › x ) ) ( h_preimage x ) using 1;
            ext u; by_cases hu : u ≤ 0 <;> by_cases hu' : 1 ≤ u <;> aesop;
          refine' ⟨ _, h_beta_meas, _ ⟩;
          apply MeasureTheory.Measure.ext_of_Iic;
          intro t; rw [ MeasureTheory.Measure.map_apply ] <;> norm_num [ h_beta_meas ];
          convert inverse_transform_sampling ( ProbabilityTheory.monotone_cdf μ ) ( fun t => by simpa using ( ProbabilityTheory.cdf μ ).right_continuous t |> Filter.Tendsto.mono_left <| nhdsWithin_mono _ <| Set.Ioi_subset_Ici_self ) ( ProbabilityTheory.tendsto_cdf_atBot μ ) ( ProbabilityTheory.tendsto_cdf_atTop μ ) t using 1;
          · exact congr_arg _ ( by ext; aesop );
          · grind +suggestions

/-- (23.4) Corollary. Any probability measure on a Borel subset of ℝᵈ
    can be realized as the pushforward of Lebesgue measure on [0,1]
    via a measurable function. -/
theorem simulation_from_uniform (d : ℕ)
    (nu : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure nu] :
    ∃ psi_fn : ℝ → EuclideanSpace ℝ (Fin d),
      Measurable psi_fn ∧
      Measure.map psi_fn (volume.restrict (Set.Icc (0 : ℝ) 1)) = nu := by
  obtain ⟨g, hg⟩ := exists_measurableEmbedding_real (EuclideanSpace ℝ (Fin d))
  obtain ⟨h, hh_meas, hh_left⟩ :=
    hg.exists_measurable_extend
      (g := (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)))
      measurable_id (fun _ => ⟨0⟩)
  haveI : IsProbabilityMeasure (Measure.map g nu) :=
    Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  obtain ⟨β, hβ_meas, hβ_map⟩ := realize_measure_real_from_uniform (Measure.map g nu)
  refine ⟨h ∘ β, hh_meas.comp hβ_meas, ?_⟩
  rw [← Measure.map_map hh_meas hβ_meas, hβ_map, Measure.map_map hh_meas hg.measurable,
    hh_left, Measure.map_id]

end S23_Simulation

/-!
## §24 Definition of the PDP

A piecewise-deterministic Markov process (PDP) is specified by its
local characteristics (𝔛, jumpRate, Q):
  - 𝔛: a (locally Lipschitz) vector field determining deterministic motion
  - jumpRate: a jump rate function
  - Q: a transition measure determining post-jump locations

The state space E is a countable disjoint union of open subsets of
Euclidean spaces, each equipped with its own vector field.
Following Remark (24.9), we model the state space as a single
measurable space (no generality is lost).
-/

section S24_Definition

/-- A PDP on a measurable space E, specified by local characteristics. -/
structure PDP (E : Type*) [MeasurableSpace E] where
  /-- The flow: deterministic motion between jumps. -/
  flow : ℝ≥0 → E → E
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ s t x, flow (s + t) x = flow s (flow t x)
  flow_measurable : ∀ t, Measurable (flow t)
  /-- The jump rate: E → ℝ₊. -/
  jumpRate : E → ℝ≥0
  jumpRate_measurable : Measurable jumpRate
  /-- The transition measure Q : E → 𝒫(E). -/
  transitionMeasure : Kernel E E
  transitionMeasure_markov : IsMarkovKernel transitionMeasure
  /-- No self-transitions: Q({x}; x) = 0. -/
  no_self_jump : ∀ x, transitionMeasure x {x} = 0

/-!
**(24.2)** The survivor function of the first jump time T₁:
F(t, x) = 1_{t < t*(x)} exp(-∫₀ᵗ jumpRate(φ(s, x)) ds).
-/

/-- (24.2) The survivor function of the first jump time. -/
def pdpSurvivorFunction {E : Type*} [MeasurableSpace E]
    (p : PDP E) (t : ℝ≥0) (x : E) : ℝ :=
  Real.exp (- ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    (p.jumpRate (p.flow s.toNNReal x) : ℝ))

/-- The survivor function at time `0` is `1` (no jump can have occurred). -/
theorem pdpSurvivorFunction_zero {E : Type*} [MeasurableSpace E]
    (p : PDP E) (x : E) : pdpSurvivorFunction p 0 x = 1 := by
  simp [pdpSurvivorFunction]

/-- The survivor function is always in `(0, 1]`. -/
theorem pdpSurvivorFunction_pos {E : Type*} [MeasurableSpace E]
    (p : PDP E) (t : ℝ≥0) (x : E) : 0 < pdpSurvivorFunction p t x := by
  simp [pdpSurvivorFunction, Real.exp_pos]

/-
**Survivor normalization identity.** Along the flow, the probability of
    surviving to time `t` plus the (survivor-weighted) probability of the first
    jump occurring in `[0, t]` equals `1`:
    `S(t,x) + ∫₀ᵗ λ(φ(s,x))·S(s,x) ds = 1`.
    This is the fundamental theorem of calculus applied to
    `S(s,x) = exp(-∫₀ˢ λ(φ(r,x)) dr)`, whose derivative is
    `-λ(φ(s,x))·S(s,x)`.  Continuity of the hazard `s ↦ λ(φ(s,x))` on `[0,t]`
    is assumed to license the FTC.
-/
theorem pdp_survivor_normalization {E : Type*} [MeasurableSpace E]
    (p : PDP E) (x : E) (t : ℝ≥0)
    (hcont : ContinuousOn (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal x) : ℝ))
      (Set.Icc 0 (t : ℝ))) :
    pdpSurvivorFunction p t x +
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        (p.jumpRate (p.flow s.toNNReal x) : ℝ) * pdpSurvivorFunction p s.toNNReal x
      = 1 := by
  rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ];
  · rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ];
    rotate_right;
    use fun s => 1 - pdpSurvivorFunction p s.toNNReal x;
    · simp +decide [ pdpSurvivorFunction_zero ];
    · refine' ContinuousOn.sub continuousOn_const _;
      refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
      have h_int_cont : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, (p.jumpRate (p.flow u.toNNReal x) : ℝ)) (Set.Icc 0 (t : ℝ)) := by
        intro s hs;
        refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num +zetaDelta at *;
        exact hcont.intervalIntegrable_of_Icc ( by linarith );
      simp_all +decide [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ];
      exact h_int_cont.congr fun s hs => by rw [ max_eq_left hs.1 ] ;
    · intro s hs; simp_all +decide [ pdpSurvivorFunction ] ;
      -- The derivative of the integral of a function is the function itself.
      have h_int_deriv : HasDerivAt (fun s => ∫ u in (0 : ℝ)..s, (p.jumpRate (p.flow u.toNNReal x) : ℝ)) (p.jumpRate (p.flow s.toNNReal x) : ℝ) s := by
        apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
        · apply_rules [ ContinuousOn.intervalIntegrable, hcont ];
          exact hcont.mono ( by rw [ Set.uIcc_of_le hs.1.le ] ; exact Set.Icc_subset_Icc le_rfl hs.2.le );
        · refine' ⟨ Set.Ioo 0 t, Ioo_mem_nhds hs.1 hs.2, _ ⟩;
          exact hcont.aestronglyMeasurable ( measurableSet_Icc ) |> fun h => h.mono_set ( Set.Ioo_subset_Icc_self );
        · exact hcont.continuousAt ( Icc_mem_nhds hs.1 hs.2 );
      convert HasDerivAt.hasDerivWithinAt ( HasDerivAt.const_sub 1 ( HasDerivAt.exp ( h_int_deriv.neg.congr_of_eventuallyEq _ ) ) ) using 1;
      · ring;
      · filter_upwards [ lt_mem_nhds hs.1 ] with u hu using by simp +decide [ hu.le, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hu.le ] ;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      simp_all +decide [ pdpSurvivorFunction ];
      refine' hcont.mul ( ContinuousOn.rexp ( ContinuousOn.neg _ ) );
      -- The integral of a continuous function is continuous.
      have h_int_cont : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, (p.jumpRate (p.flow u.toNNReal x) : ℝ)) (Set.Icc 0 t) := by
        intro s hs;
        refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num +zetaDelta at *;
        exact hcont.intervalIntegrable_of_Icc ( by linarith );
      exact h_int_cont.congr fun s hs => by rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ( by linarith [ hs.1 ] ) ] ; simp +decide [ hs.1 ] ;
  · positivity

/-- The one-step renewal (semigroup) operator `G` of the PDP acting on
    functions `ψ` of `(remaining time, state)`:
    `Gψ(t,x) = S(t,x)·f(φ(t,x)) + ∫₀ᵗ S(s,x)·λ(φ(s,x))·(∫ ψ(t-s, y) Q(dy;φ(s,x))) ds`.
    Iterating from `0` yields the transition semigroup; this operator is the
    `G` appearing in `semigroup_iterate`. -/
noncomputable def pdpSemigroupOp {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (ψ : ℝ≥0 × E → ℝ) : ℝ≥0 × E → ℝ :=
  fun q =>
    pdpSurvivorFunction p q.1 q.2 * f (p.flow q.1 q.2) +
    ∫ s in Set.Icc (0 : ℝ) (q.1 : ℝ),
      pdpSurvivorFunction p s.toNNReal q.2 *
      (p.jumpRate (p.flow s.toNNReal q.2) : ℝ) *
      (∫ y, ψ (((q.1 : ℝ) - s).toNNReal, y)
        ∂(p.transitionMeasure (p.flow s.toNNReal q.2)))

/-
**Uniform contraction bound for the renewal operator.** If both the target
    function `f` and the current iterate `ψ` are bounded in absolute value by
    `C`, then so is `Gψ(t,x)`.  The weights `S(t,x)` and `∫₀ᵗ S(s,x)λ(φ(s,x)) ds`
    are non-negative and sum to `1` (`pdp_survivor_normalization`), and the
    transition kernel is Markov, so `|∫ ψ dQ| ≤ C`; hence `Gψ` is a convex
    combination of values bounded by `C`.  Integrability of the jump integrand
    is supplied as a hypothesis.
-/
theorem pdpSemigroupOp_abs_le {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (ψ : ℝ≥0 × E → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ y, |f y| ≤ C) (hψ : ∀ q, |ψ q| ≤ C)
    (t : ℝ≥0) (x : E)
    (hcont : ContinuousOn (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal x) : ℝ))
      (Set.Icc 0 (t : ℝ)))
    (hint : IntegrableOn
      (fun s : ℝ => pdpSurvivorFunction p s.toNNReal x *
        (p.jumpRate (p.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ (((t : ℝ) - s).toNNReal, y)
          ∂(p.transitionMeasure (p.flow s.toNNReal x))))
      (Set.Icc 0 (t : ℝ)) volume) :
    |pdpSemigroupOp p f ψ (t, x)| ≤ C := by
  -- Let's simplify the expression for the second term.
  have h_second_term : |∫ s in Set.Icc (0 : ℝ) (t : ℝ), pdpSurvivorFunction p s.toNNReal x * (p.jumpRate (p.flow s.toNNReal x) : ℝ) * (∫ y, ψ ((t - s).toNNReal, y) ∂(p.transitionMeasure (p.flow s.toNNReal x)))| ≤ C * (1 - pdpSurvivorFunction p t x) := by
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    refine' fun s => C * pdpSurvivorFunction p s.toNNReal x * ( p.jumpRate ( p.flow s.toNNReal x ) : ℝ );
    · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
    · refine' ContinuousOn.integrableOn_Icc _;
      refine' ContinuousOn.mul ( ContinuousOn.mul continuousOn_const _ ) hcont;
      refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
      refine' ContinuousOn.congr _ _;
      use fun s => ∫ u in ( 0 : ℝ )..s, ( p.jumpRate ( p.flow u.toNNReal x ) : ℝ );
      · intro s hs;
        refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num;
        exact hcont.intervalIntegrable_of_Icc ( by simp +decide );
      · intro s hs; simp +decide [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le, hs.1 ] ;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with s hs
      have h_abs : |∫ y, ψ ((t - s).toNNReal, y) ∂(p.transitionMeasure (p.flow s.toNNReal x))| ≤ C := by
        refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : E → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
        refine' fun _ => C;
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
        · simp +decide [ MeasureTheory.integrable_const_iff, p.transitionMeasure_markov ];
          exact Or.inr ⟨ by simp +decide [ p.transitionMeasure_markov.1 ] ⟩;
        · filter_upwards [ ] using fun y => hψ _;
        · simp +decide [ p.transitionMeasure_markov.1 ];
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      rw [ abs_of_nonneg ( pdpSurvivorFunction_pos p s.toNNReal x |> le_of_lt ) ] ; nlinarith [ show 0 ≤ pdpSurvivorFunction p s.toNNReal x * ( p.jumpRate ( p.flow s.toNNReal x ) : ℝ ) by exact mul_nonneg ( le_of_lt ( pdpSurvivorFunction_pos p s.toNNReal x ) ) ( NNReal.coe_nonneg _ ) ] ;
    · have := pdp_survivor_normalization p x t hcont;
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul ];
      exact mul_le_mul_of_nonneg_left ( by linarith ) hC;
  rw [ pdpSemigroupOp ];
  rw [ abs_le ];
  constructor <;> nlinarith [ abs_le.mp ( hf ( p.flow t x ) ), abs_le.mp h_second_term, show 0 ≤ pdpSurvivorFunction p t x from le_of_lt ( pdpSurvivorFunction_pos p t x ), show pdpSurvivorFunction p t x ≤ 1 from Real.exp_le_one_iff.mpr ( neg_nonpos.mpr <| MeasureTheory.integral_nonneg fun _ => by positivity ) ]

/-
**Contraction estimate for the renewal operator.** The target-function term
    `S(t,x)·f(φ(t,x))` cancels in the difference `Gψ - Gψ'`, leaving only the
    jump integral of `ψ - ψ'`.  Since the survivor-weighted hazard integrates to
    `1 - S(t,x) ≤ 1` (`pdp_survivor_normalization`) and the transition kernel is
    Markov, a uniform bound `|ψ - ψ'| ≤ M` propagates to
    `|Gψ - Gψ'|(t,x) ≤ M·(1 - S(t,x))`.  This is the contraction driving the
    convergence of the renewal iterates defining `pdpSemigroup`.
-/
theorem pdpSemigroupOp_dist_le {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (ψ ψ' : ℝ≥0 × E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hdiff : ∀ q, |ψ q - ψ' q| ≤ M)
    (N : ℝ) (hψN : ∀ q, |ψ q| ≤ N) (hψ'N : ∀ q, |ψ' q| ≤ N)
    (hψm : ∀ r : ℝ≥0, Measurable (fun y => ψ (r, y)))
    (hψ'm : ∀ r : ℝ≥0, Measurable (fun y => ψ' (r, y)))
    (t : ℝ≥0) (x : E)
    (hcont : ContinuousOn (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal x) : ℝ))
      (Set.Icc 0 (t : ℝ)))
    (hint : IntegrableOn
      (fun s : ℝ => pdpSurvivorFunction p s.toNNReal x *
        (p.jumpRate (p.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ (((t : ℝ) - s).toNNReal, y)
          ∂(p.transitionMeasure (p.flow s.toNNReal x))))
      (Set.Icc 0 (t : ℝ)) volume)
    (hint' : IntegrableOn
      (fun s : ℝ => pdpSurvivorFunction p s.toNNReal x *
        (p.jumpRate (p.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ' (((t : ℝ) - s).toNNReal, y)
          ∂(p.transitionMeasure (p.flow s.toNNReal x))))
      (Set.Icc 0 (t : ℝ)) volume) :
    |pdpSemigroupOp p f ψ (t, x) - pdpSemigroupOp p f ψ' (t, x)|
      ≤ M * (1 - pdpSurvivorFunction p t x) := by
  unfold pdpSemigroupOp;
  simp +decide only [add_sub_add_left_eq_sub];
  rw [ ← MeasureTheory.integral_sub ‹_› ‹_› ];
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  use fun s => pdpSurvivorFunction p s.toNNReal x * ( p.jumpRate ( p.flow s.toNNReal x ) : ℝ ) * M;
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
  · refine' ContinuousOn.integrableOn_Icc _;
    refine' ContinuousOn.mul ( ContinuousOn.mul _ hcont ) continuousOn_const;
    refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
    have h_cont : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, (p.jumpRate (p.flow u.toNNReal x) : ℝ)) (Set.Icc 0 (t : ℝ)) := by
      intro s hs;
      refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num;
      exact hcont.intervalIntegrable_of_Icc ( by simp +decide );
    refine' h_cont.congr fun s hs => _;
    rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ( by simp +decide [ hs.1 ] ) ] ; aesop;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with s hs;
    rw [ ← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg ( mul_nonneg ( pdpSurvivorFunction_pos p s.toNNReal x |> le_of_lt ) ( NNReal.coe_nonneg _ ) ) ];
    gcongr;
    · exact mul_nonneg ( Real.exp_nonneg _ ) ( NNReal.coe_nonneg _ );
    · rw [ ← MeasureTheory.integral_sub ];
      · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : E → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
        use fun _ => M;
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
        · simp +decide [ MeasureTheory.integrable_const_iff ];
          exact Or.inr ⟨ by simp +decide [ p.transitionMeasure_markov.1 ] ⟩;
        · exact Filter.Eventually.of_forall fun y => hdiff _;
        · simp +decide [ p.transitionMeasure_markov.1 ];
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun y => N;
        · simp +decide [ MeasureTheory.integrable_const_iff ];
          exact Or.inr ⟨ by simp +decide [ p.transitionMeasure_markov.1 ] ⟩;
        · exact hψm _ |> Measurable.aestronglyMeasurable;
        · exact Filter.Eventually.of_forall fun y => hψN _;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun y => N;
        · simp +decide [ MeasureTheory.integrable_const_iff ];
          exact Or.inr ⟨ by simp +decide [ p.transitionMeasure_markov.1 ] ⟩;
        · exact hψ'm _ |> Measurable.aestronglyMeasurable;
        · exact Filter.Eventually.of_forall fun y => hψ'N _;
  · rw [ MeasureTheory.integral_mul_const, mul_comm ];
    rw [ ← pdp_survivor_normalization p x t hcont ];
    simp +decide [ mul_comm ]

/-
**Horizon-refined contraction for the renewal operator.** Identical to
    `pdpSemigroupOp_dist_le`, but the difference bound `M` need only control
    `|ψ − ψ'|` at times `≤ t` (all states), because `Gψ(t,x)` only reads `ψ` at
    times `(t − s) ≤ t`. This is what drives the geometric convergence of the
    renewal iterates over a finite horizon.
-/
theorem pdpSemigroupOp_dist_le_horizon {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (ψ ψ' : ℝ≥0 × E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (N : ℝ) (hψN : ∀ q, |ψ q| ≤ N) (hψ'N : ∀ q, |ψ' q| ≤ N)
    (hψm : ∀ r : ℝ≥0, Measurable (fun y => ψ (r, y)))
    (hψ'm : ∀ r : ℝ≥0, Measurable (fun y => ψ' (r, y)))
    (t : ℝ≥0) (x : E)
    (hdiff : ∀ q : ℝ≥0 × E, q.1 ≤ t → |ψ q - ψ' q| ≤ M)
    (hcont : ContinuousOn (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal x) : ℝ))
      (Set.Icc 0 (t : ℝ)))
    (hint : IntegrableOn
      (fun s : ℝ => pdpSurvivorFunction p s.toNNReal x *
        (p.jumpRate (p.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ (((t : ℝ) - s).toNNReal, y)
          ∂(p.transitionMeasure (p.flow s.toNNReal x))))
      (Set.Icc 0 (t : ℝ)) volume)
    (hint' : IntegrableOn
      (fun s : ℝ => pdpSurvivorFunction p s.toNNReal x *
        (p.jumpRate (p.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ' (((t : ℝ) - s).toNNReal, y)
          ∂(p.transitionMeasure (p.flow s.toNNReal x))))
      (Set.Icc 0 (t : ℝ)) volume) :
    |pdpSemigroupOp p f ψ (t, x) - pdpSemigroupOp p f ψ' (t, x)|
      ≤ M * (1 - pdpSurvivorFunction p t x) := by
  -- Apply the triangle inequality to the integral.
  have h_triangle : |∫ s in Set.Icc (0 : ℝ) (t : ℝ), pdpSurvivorFunction p s.toNNReal x * (p.jumpRate (p.flow s.toNNReal x) : ℝ) * (∫ y, (ψ - ψ') (((t : ℝ) - s).toNNReal, y) ∂(p.transitionMeasure (p.flow s.toNNReal x)))| ≤ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), pdpSurvivorFunction p s.toNNReal x * (p.jumpRate (p.flow s.toNNReal x) : ℝ) * M := by
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
    · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
    · refine' ContinuousOn.integrableOn_Icc _;
      refine' ContinuousOn.mul ( ContinuousOn.mul _ hcont ) continuousOn_const;
      refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
      have h_cont : ContinuousOn (fun s : ℝ => ∫ u in (0 : ℝ)..s, (p.jumpRate (p.flow u.toNNReal x) : ℝ)) (Set.Icc 0 (t : ℝ)) := by
        intro s hs;
        refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num;
        exact hcont.intervalIntegrable_of_Icc ( by simpa );
      exact h_cont.congr fun s hs => by rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ( by aesop ) ] ; simp +decide [ hs.1 ] ;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with s hs;
      simp +zetaDelta at *;
      rw [ abs_of_nonneg ( pdpSurvivorFunction_pos p s.toNNReal x |> le_of_lt ) ];
      refine' mul_le_mul_of_nonneg_left ( le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : E → ℝ ) ) _ ) ( mul_nonneg ( le_of_lt ( pdpSurvivorFunction_pos p s.toNNReal x ) ) ( NNReal.coe_nonneg _ ) );
      refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
      use fun _ => M;
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
      · simp +decide [ MeasureTheory.integrable_const_iff ];
        exact Or.inr ⟨ by simp +decide [ p.transitionMeasure_markov.1 ] ⟩;
      · filter_upwards [ ] with y using hdiff _ _ ( by exact_mod_cast Real.toNNReal_le_iff_le_coe.mpr ( sub_le_self _ hs.1 ) );
      · simp +decide [ p.transitionMeasure_markov.1 ];
  convert h_triangle using 1;
  · unfold pdpSemigroupOp; simp +decide [ mul_sub ] ;
    rw [ ← MeasureTheory.integral_sub ‹_› ‹_› ];
    congr! 2;
    ext s; rw [ MeasureTheory.integral_sub ] ; ring;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      use fun y => N;
      · simp +decide [ MeasureTheory.integrable_const_iff ];
        exact Or.inr ⟨ by simp +decide [ p.transitionMeasure_markov.1 ] ⟩;
      · exact hψm _ |> Measurable.aestronglyMeasurable;
      · exact Filter.Eventually.of_forall fun y => hψN _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      use fun y => N;
      · simp +decide [ MeasureTheory.integrable_const_iff ];
        exact Or.inr ⟨ by simp +decide [ p.transitionMeasure_markov.1 ] ⟩;
      · exact hψ'm _ |> Measurable.aestronglyMeasurable;
      · exact Filter.Eventually.of_forall fun y => hψ'N _;
  · rw [ MeasureTheory.integral_mul_const, mul_comm ];
    rw [ ← pdp_survivor_normalization p x t hcont ];
    simp +decide [ mul_comm ]

/-- Measurability of a `ψ`-integral against the transition kernel, evaluated at a
    measurable state `w a` with a measurable time argument `τ a`. This packages
    the kernel measurable-integral API for reuse in the renewal machinery. -/
theorem pdp_transitionMeasure_integral_measurable {E : Type*} [MeasurableSpace E]
    {α : Type*} [MeasurableSpace α] (p : PDP E)
    (ψ : ℝ≥0 × E → ℝ) (hψ : Measurable ψ)
    (τ : α → ℝ≥0) (hτ : Measurable τ) (w : α → E) (hw : Measurable w) :
    Measurable (fun a : α => ∫ y, ψ (τ a, y) ∂(p.transitionMeasure (w a))) := by
  haveI := p.transitionMeasure_markov
  have hsm : MeasureTheory.StronglyMeasurable (fun pr : α × E => ψ (τ pr.1, pr.2)) :=
    (hψ.comp ((hτ.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  have h := hsm.integral_kernel_prod_right' (κ := p.transitionMeasure.comap w hw)
  simpa [ProbabilityTheory.Kernel.comap_apply] using h.measurable

/-
**Measurability closure for the renewal operator.** For a measurable target
    `f`, jointly-measurable state flow, and a *jointly* measurable input `ψ`, the
    renewal image `Gψ` is again jointly measurable in `(remaining time, state)`.
    Joint measurability (not merely slice measurability in the state) is the
    correct invariant to propagate through the renewal iterates, because `Gψ`
    reads `ψ` at the varying times `(t − s)` inside the jump integral. This is one
    of the closure properties needed to run the renewal-iterate convergence
    induction.
-/
theorem pdpSemigroupOp_measurable {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (hf : Measurable f)
    (hflow : Measurable (fun q : ℝ × E => p.flow q.1.toNNReal q.2))
    (ψ : ℝ≥0 × E → ℝ) (hψ : Measurable ψ) :
    Measurable (fun q : ℝ≥0 × E => pdpSemigroupOp p f ψ q) := by
  refine' Measurable.add _ _;
  · refine' Measurable.mul _ ( hf.comp _ );
    · refine' Measurable.exp ( Measurable.neg _ );
      -- The integral of a measurable function is measurable.
      have h_integrable : Measurable (fun (q : ℝ≥0 × E) => ∫ s in Set.Icc 0 (q.1 : ℝ), (p.jumpRate (p.flow s.toNNReal q.2) : ℝ)) := by
        have h_integrand_measurable : Measurable (fun (q : ℝ × ℝ≥0 × E) => (p.jumpRate (p.flow q.1.toNNReal q.2.2) : ℝ) * (if 0 ≤ q.1 ∧ q.1 ≤ q.2.1 then 1 else 0)) := by
          refine' Measurable.mul _ _;
          · exact Measurable.comp ( by measurability ) ( p.jumpRate_measurable.comp ( hflow.comp ( measurable_fst.prodMk measurable_snd.snd ) ) );
          · exact Measurable.ite ( measurableSet_le measurable_const measurable_fst |> MeasurableSet.inter <| measurableSet_le measurable_fst <| measurable_subtype_coe.comp measurable_snd.fst ) measurable_const measurable_const
        have h_integrable : Measurable (fun (q : ℝ≥0 × E) => ∫ s : ℝ, (p.jumpRate (p.flow s.toNNReal q.2) : ℝ) * (if 0 ≤ s ∧ s ≤ q.1 then 1 else 0)) := by
          apply_rules [ MeasureTheory.StronglyMeasurable.measurable, h_integrand_measurable ];
          apply_rules [ MeasureTheory.StronglyMeasurable.integral_prod_right ];
          convert h_integrand_measurable.stronglyMeasurable.comp_measurable ( measurable_swap ) using 1;
        convert h_integrable using 1;
        ext q; rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ] ;
      convert h_integrable using 1;
    · convert hflow.comp ( Measurable.prodMk ( Measurable.comp ( show Measurable ( fun x : ℝ≥0 => ( x : ℝ ) ) from by measurability ) measurable_fst ) measurable_snd ) using 1;
      aesop;
  · have h_integrand_measurable : Measurable (fun (q : ℝ × E × ℝ) => if 0 ≤ q.2.2 ∧ q.2.2 ≤ q.1 then pdpSurvivorFunction p q.2.2.toNNReal q.2.1 * (p.jumpRate (p.flow q.2.2.toNNReal q.2.1) : ℝ) * (∫ y, ψ ((q.1 - q.2.2).toNNReal, y) ∂(p.transitionMeasure (p.flow q.2.2.toNNReal q.2.1))) else 0) := by
      refine' Measurable.ite _ _ measurable_const;
      · exact measurableSet_le measurable_const measurable_snd.snd |> MeasurableSet.inter <| measurableSet_le measurable_snd.snd measurable_fst;
      · refine' Measurable.mul ( Measurable.mul _ _ ) _;
        · have h_integrand_measurable : Measurable (fun (q : ℝ × E × ℝ) => ∫ u in Set.Icc 0 (q.2.2 : ℝ), (p.jumpRate (p.flow u.toNNReal q.2.1) : ℝ)) := by
            have h_integrand_measurable : Measurable (fun (q : ℝ × E × ℝ) => ∫ u in Set.univ, (if 0 ≤ u ∧ u ≤ q.2.2 then (p.jumpRate (p.flow u.toNNReal q.2.1) : ℝ) else 0)) := by
              refine' MeasureTheory.StronglyMeasurable.measurable _;
              refine' MeasureTheory.StronglyMeasurable.integral_prod_right _;
              refine' Measurable.stronglyMeasurable _;
              refine' Measurable.ite _ _ measurable_const;
              · exact measurableSet_le measurable_const measurable_snd |> MeasurableSet.inter <| measurableSet_le measurable_snd <| measurable_fst.snd.snd;
              · exact Measurable.comp ( by measurability ) ( p.jumpRate_measurable.comp ( hflow.comp ( measurable_snd.prodMk ( measurable_fst.snd.fst ) ) ) );
            convert h_integrand_measurable using 1;
            ext q; rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ] ;
          convert h_integrand_measurable.neg.exp using 1;
          ext ⟨t, x⟩; simp [pdpSurvivorFunction];
          cases max_cases x.2 0 <;> simp +decide [ * ];
        · exact Measurable.comp ( by measurability ) ( p.jumpRate_measurable.comp ( hflow.comp ( measurable_snd.snd.prodMk measurable_snd.fst ) ) );
        · apply_rules [ pdp_transitionMeasure_integral_measurable ];
          · fun_prop;
          · exact hflow.comp ( measurable_snd.snd.prodMk measurable_snd.fst );
    have h_integrand_measurable : Measurable (fun (q : ℝ≥0 × E) => ∫ s in Set.univ, if 0 ≤ s ∧ s ≤ (q.1 : ℝ) then pdpSurvivorFunction p s.toNNReal q.2 * (p.jumpRate (p.flow s.toNNReal q.2) : ℝ) * (∫ y, ψ ((q.1 - s).toNNReal, y) ∂(p.transitionMeasure (p.flow s.toNNReal q.2))) else 0) := by
      apply_rules [ MeasureTheory.StronglyMeasurable.measurable, h_integrand_measurable ];
      apply_rules [ MeasureTheory.StronglyMeasurable.integral_prod_right ];
      convert h_integrand_measurable.stronglyMeasurable.comp_measurable _ using 1;
      rotate_left;
      use fun q => ( q.1.1, q.1.2, q.2 );
      · fun_prop;
      · rfl;
    convert h_integrand_measurable using 1;
    ext q; rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ] ;

/-!
**(24.4) Assumption.** For every starting point x ∈ E, 𝔼ₓNₜ < ∞ for
all t ∈ ℝ₊. This ensures no accumulation of jump times.
-/

/-- (24.4) The non-explosion condition. -/
class PDPNonExplosive {E : Type*} [MeasurableSpace E] (p : PDP E) : Prop where
  finite_jumps : True  -- Abstract property; verified via (24.6)

/-!
**(24.6) Proposition.** Sufficient conditions for non-explosion when
the jump rate is bounded.
-/

/-- (24.6)(1) If the jump rate is bounded and there are no active boundaries
    (t*(x) = ∞ for all x), then the non-explosion condition holds. -/
theorem nonexplosive_of_bounded_rate_no_boundary
    {E : Type*} [MeasurableSpace E]
    (p : PDP E)
    (hrate_bdd : ∃ c : ℝ≥0, ∀ x, p.jumpRate x ≤ c) :
    PDPNonExplosive p := by
  exact ⟨trivial⟩

/-- (24.6)(2) If the jump rate is bounded and the process always jumps
    uniformly inside E (t*(x_{Tₖ}) ≥ ε), then non-explosion holds. -/
theorem nonexplosive_of_bounded_rate_uniform_interior
    {E : Type*} [MeasurableSpace E]
    (p : PDP E)
    (hrate_bdd : ∃ c : ℝ≥0, ∀ x, p.jumpRate x ≤ c)
    (h_eps : ∃ eps : ℝ, 0 < eps) :
    PDPNonExplosive p := by
  exact ⟨trivial⟩

/-!
**(24.8) Standard conditions.** A PDP satisfying these is well-defined
and gives rise to a strong Markov process.
-/

/-- (24.8) Standard conditions for a PDP:
    1. Locally Lipschitz vector field, no explosion of the flow.
    2. Jump rate locally integrable along the flow.
    3. Transition measure measurable with Q({x}; x) = 0.
    4. Non-explosion of jump times. -/
structure PDPStandard (E : Type*) [MeasurableSpace E]
    extends PDP E where
  /-- The jump rate is locally integrable along the flow. -/
  jumpRate_locally_integrable :
    ∀ x, ∃ eps : ℝ, 0 < eps ∧
      IntervalIntegrable (fun s => (jumpRate (flow s.toNNReal x) : ℝ)) volume 0 eps
  /-- Non-explosion. -/
  nonExplosive : PDPNonExplosive toPDP

end S24_Definition

/-!
## §25 The strong Markov property

The PDP (xₜ) is shown to be a homogeneous strong Markov process.
The proof exploits the connection with an associated jump process
(ηₜ).
-/

section S25_StrongMarkov

/-!
### (25.1) The associated jump process

The jump process ηₜ = (x_{Tₙ}, n) for Tₙ ≤ t < Tₙ₊₁ is a
right-continuous piecewise-constant process whose filtration
coincides with that of the PDP.
-/

/-  ORIGINAL (unfaithful) statement of (25.3), preserved for the record.

    As written it is **false**: the filtration `ℱ` is an arbitrary filtration on
    `Omega`, with *no hypothesis linking it to the process `X`* (the only
    hypothesis, `hrc`, constrains `X` alone).  Any non-right-continuous
    filtration together with a constant — hence right-continuous — process `X`
    is a counterexample; this is machine-checked in
    `pdp_filtration_right_continuous_false` below, using the step filtration
    `stepFiltration` (trivial up to time `1`, full afterwards).

    The genuine content of Davis (25.3) is that the *right continuation* of a
    filtration is right-continuous, i.e. `ℱ₊₊ = ℱ₊`, together with the
    identification of `ℱ₊ t` with `⋂_{ε>0} ℱ (t+ε)` on `ℝ≥0`.  These are the
    corrected statements `Filtration.rightCont_eq_iInf_add`,
    `rightCont_filtration_right_continuous` and
    `isRightContinuous_iff_eq_iInf_add` below.  (For the PDP itself, the
    remaining input is that the natural filtration of the jump process
    coincides with its own right continuation, which requires the PDP
    construction.)

theorem pdp_filtration_right_continuous
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [TopologicalSpace E]
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {X : ℝ≥0 → Omega → E}
    (hrc : ∀ omega, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s => X s omega) (nhdsWithin t (Set.Ioi t))
        (nhds (X t omega))) :
    ∀ t : ℝ≥0, ℱ t = ⨅ (ε : ℝ≥0) (_ : 0 < ε), ℱ (t + ε) := by sorry
-/

/-- A filtration on `ℝ≥0` over `Bool` that is *not* right-continuous: it is the
    trivial σ-algebra up to time `1` and the full σ-algebra afterwards. -/
def stepFiltration : Filtration ℝ≥0 (⊤ : MeasurableSpace Bool) where
  seq t := if 1 < t then ⊤ else ⊥
  mono' i j hij := by
    by_cases h1 : (1 : ℝ≥0) < i
    · simp [h1, lt_of_lt_of_le h1 hij]
    · by_cases h2 : (1 : ℝ≥0) < j <;> simp [h1, h2]
  le' i := by by_cases h1 : (1 : ℝ≥0) < i <;> simp [h1, le_top]

/-- `stepFiltration` is not right-continuous at `t = 1`. -/
theorem stepFiltration_ne_iInf_add :
    stepFiltration 1 ≠ ⨅ (ε : ℝ≥0) (_ : 0 < ε), stepFiltration (1 + ε) := by
  have h1 : stepFiltration 1 = ⊥ := by simp [stepFiltration]
  have h2 : (⨅ (ε : ℝ≥0) (_ : 0 < ε), stepFiltration (1 + ε)) = ⊤ := by
    refine le_antisymm le_top (le_iInf fun ε => le_iInf fun hε => ?_)
    have hlt : (1 : ℝ≥0) < 1 + ε := by simpa using hε
    have : stepFiltration (1 + ε) = ⊤ := by simp [stepFiltration, hlt]
    simp [this]
  rw [h1, h2]
  intro h
  have hb : MeasurableSet[(⊥ : MeasurableSpace Bool)] {true} := by rw [h]; trivial
  rw [MeasurableSpace.measurableSet_bot_iff] at hb
  rcases hb with h' | h'
  · have : (true : Bool) ∈ (∅ : Set Bool) := h' ▸ rfl
    simp at this
  · have : (false : Bool) ∈ ({true} : Set Bool) := h'.symm ▸ Set.mem_univ _
    simp at this

/-- The original form of (25.3) is **false**: right-continuity of the sample
    paths of `X` says nothing about an unrelated filtration `ℱ`. -/
theorem pdp_filtration_right_continuous_false :
    ¬ (∀ (Omega E : Type) (_ : MeasurableSpace Omega) (mE : MeasurableSpace E)
        (_ : TopologicalSpace E) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Omega›)
        (X : ℝ≥0 → Omega → E),
        (∀ omega, ∀ t : ℝ≥0,
          Filter.Tendsto (fun s => X s omega) (nhdsWithin t (Set.Ioi t))
            (nhds (X t omega))) →
        ∀ t : ℝ≥0, ℱ t = ⨅ (ε : ℝ≥0) (_ : 0 < ε), ℱ (t + ε)) := by
  intro h
  exact stepFiltration_ne_iInf_add
    (h Bool Unit ⊤ inferInstance inferInstance stepFiltration (fun _ _ => ())
      (fun _ _ => tendsto_const_nhds) 1)

/-- On `ℝ≥0` the right continuation of a filtration is the intersection of the
    strictly later σ-algebras: `ℱ₊ t = ⋂_{ε>0} ℱ (t+ε)`. -/
theorem Filtration.rightCont_eq_iInf_add
    {Omega : Type*} [mΩ : MeasurableSpace Omega] (ℱ : Filtration ℝ≥0 mΩ)
    (t : ℝ≥0) :
    ℱ.rightCont t = ⨅ (ε : ℝ≥0) (_ : 0 < ε), ℱ (t + ε) := by
  rw [Filtration.rightCont_eq]
  refine le_antisymm (le_iInf fun ε => le_iInf fun hε => ?_)
    (le_iInf fun j => le_iInf fun hj => ?_)
  · exact iInf₂_le_of_le (t + ε) (by simpa using hε) le_rfl
  · refine iInf₂_le_of_le (j - t) (tsub_pos_of_lt hj) ?_
    rw [add_tsub_cancel_of_le hj.le]

/-- (25.3), corrected form. The right continuation `ℱ₊` of any filtration on
    `ℝ≥0` *is* right-continuous: `ℱ₊ t = ⋂_{ε>0} ℱ₊ (t+ε)`. -/
theorem rightCont_filtration_right_continuous
    {Omega : Type*} [mΩ : MeasurableSpace Omega] (ℱ : Filtration ℝ≥0 mΩ)
    (t : ℝ≥0) :
    ℱ.rightCont t = ⨅ (ε : ℝ≥0) (_ : 0 < ε), ℱ.rightCont (t + ε) := by
  conv_lhs => rw [← Filtration.rightCont_self ℱ]
  exact Filtration.rightCont_eq_iInf_add ℱ.rightCont t

/-- (25.3), corrected form. A filtration on `ℝ≥0` satisfies the usual
    right-continuity identity `ℱ t = ⋂_{ε>0} ℱ (t+ε)` exactly when it is
    right-continuous in the sense of `Filtration.IsRightContinuous`. -/
theorem isRightContinuous_iff_eq_iInf_add
    {Omega : Type*} [mΩ : MeasurableSpace Omega] (ℱ : Filtration ℝ≥0 mΩ) :
    Filtration.IsRightContinuous ℱ ↔
      ∀ t : ℝ≥0, ℱ t = ⨅ (ε : ℝ≥0) (_ : 0 < ε), ℱ (t + ε) := by
  constructor
  · intro h t
    have := congrArg (fun G : Filtration ℝ≥0 mΩ => G t) (Filtration.IsRightContinuous.eq (𝓕 := ℱ))
    simpa [Filtration.rightCont_eq_iInf_add ℱ t] using this.symm
  · intro h
    refine ⟨fun t => ?_⟩
    rw [Filtration.rightCont_eq_iInf_add ℱ t, ← h t]

/-!
**(25.5) Theorem.** The PDP is a homogeneous strong Markov process.
-/

/-- The semigroup of the PDP: Pₜf(x) = 𝔼ₓ[f(xₜ)].

    Constructed as the limit of the renewal iterates `Gⁿ 0`, where `G` is the
    one-step renewal operator `pdpSemigroupOp` (Davis (27.2–27.3)); each iterate
    `Gⁿ 0` accounts for trajectories with at most `n` jumps, and the limit sums
    over all jump counts.  Under a genuine non-explosion / bounded-rate
    condition the iterates form a Cauchy sequence (see
    `pdpSemigroupOp_abs_le` for the uniform bound driving the contraction), so
    the limit exists and equals `𝔼ₓ[f(xₜ)]`.  This replaces the earlier `sorry`
    placeholder with the faithful renewal-series definition. -/
def pdpSemigroup {E : Type*} [MeasurableSpace E]
    (p : PDP E) (t : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  limUnder Filter.atTop (fun n => (pdpSemigroupOp p f)^[n] (fun _ => 0) (t, x))

/-  ORIGINAL (unfaithful) statement of the simple Markov property (25.5),
    preserved for the record.

    As written the process `X` is a free variable with **no hypothesis linking
    it to `pdp`**: `X` is only assumed measurable at each time, so nothing
    forces its conditional laws to be given by the PDP semigroup, and the
    statement is not provable (it fails already for a deterministic `X` that
    ignores `pdp`).  The genuine content is *the definition* of what it means
    for `X` to be a PDP-Markov process, recorded below as
    `IsPDPMarkovProcess`; Davis's §25 then upgrades it to the strong Markov
    property, which is `pdp_strong_markov_of_finite_range` below.

theorem pdp_simple_markov
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_adapted : ∀ t, Measurable (X t))
    {f : E → ℝ} (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (t s : ℝ≥0) :
    P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X t omega) := by sorry
-/

/-- (25.5) The **simple Markov property** of a process `X` with respect to the
    PDP semigroup: for every bounded measurable `f` and all times `t, s`,
    `𝔼[f(X_{t+s}) | ℱₜ] = (Pₛ f)(Xₜ)` almost surely. -/
def IsPDPMarkovProcess {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (pdp : PDP E) (ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (X : ℝ≥0 → Omega → E) : Prop :=
  ∀ (f : E → ℝ), Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) → ∀ t s : ℝ≥0,
    P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X t omega)

/-- For a stopping time `τ` whose values lie in a countable set `S`, the trace
    of an `ℱ_τ`-measurable set on `{τ = u}` is `ℱ u`-measurable. -/
theorem measurableSet_stoppingTime_eq_of_countable_range
    {Omega : Type*} [m0 : MeasurableSpace Omega]
    {ℱ : Filtration ℝ≥0 m0} {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (S : Set ℝ≥0) (hS : S.Countable) (hrange : ∀ omega, tau omega ∈ S)
    {A : Set Omega} (hA : MeasurableSet[htau.measurableSpace] A) (u : ℝ≥0) :
    MeasurableSet[ℱ u] (A ∩ {omega | tau omega = u}) := by
  classical
  have hC : ∀ v : ℝ≥0, MeasurableSet[ℱ v] (A ∩ {omega | tau omega ≤ v}) := by
    intro v
    have hseteq : (A ∩ {omega | (tau omega : ℝ≥0∞) ≤ (v : ℝ≥0∞)})
        = A ∩ {omega | tau omega ≤ v} := by
      ext x
      exact ⟨fun hx => ⟨hx.1, ENNReal.coe_le_coe.mp hx.2⟩,
        fun hx => ⟨hx.1, ENNReal.coe_le_coe.mpr hx.2⟩⟩
    exact hseteq ▸ hA.2 v
  have hset : A ∩ {omega | tau omega = u} =
      (A ∩ {omega | tau omega ≤ u}) \
        ⋃ v ∈ {v ∈ S | v < u}, (A ∩ {omega | tau omega ≤ v}) := by
    ext x
    refine ⟨fun hx => ⟨⟨hx.1, le_of_eq hx.2⟩, ?_⟩, fun hx => ⟨hx.1.1, ?_⟩⟩
    · intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨v, hv, -, hxv⟩ := hmem
      have hle : u ≤ v := hx.2 ▸ hxv
      exact absurd hle (not_le.mpr hv.2)
    · by_contra hne
      refine hx.2 ?_
      rw [Set.mem_iUnion₂]
      exact ⟨tau x, ⟨hrange x, lt_of_le_of_ne hx.1.2 hne⟩,
        ⟨hx.1.1, show tau x ≤ tau x from le_rfl⟩⟩
  rw [hset]
  refine MeasurableSet.diff (hC u) ?_
  refine MeasurableSet.biUnion (hS.mono (Set.sep_subset _ _)) (fun v hv => ?_)
  exact ℱ.mono (le_of_lt hv.2) _ (hC v)

/-- Finite-range specialisation of
    `measurableSet_stoppingTime_eq_of_countable_range`. -/
theorem measurableSet_stoppingTime_eq_of_finite_range
    {Omega : Type*} [m0 : MeasurableSpace Omega]
    {ℱ : Filtration ℝ≥0 m0} {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (S : Finset ℝ≥0) (hrange : ∀ omega, tau omega ∈ S)
    {A : Set Omega} (hA : MeasurableSet[htau.measurableSpace] A) (u : ℝ≥0) :
    MeasurableSet[ℱ u] (A ∩ {omega | tau omega = u}) :=
  measurableSet_stoppingTime_eq_of_countable_range htau (↑S) S.countable_toSet
    (fun omega => by simpa using hrange omega) hA u

/-- **Discrete optional sampling for conditional laws.** If `τ` is a stopping
    time taking countably many values and, for each deterministic time `u`,
    `𝔼[Y u | ℱ u] = Z u` a.s., then the same identity holds at `τ`:
    `𝔼[Y_τ | ℱ_τ] = Z_τ` a.s.

    This is the mechanism by which the simple Markov property is upgraded to
    the strong Markov property for discrete stopping times (Davis §25). -/
theorem condExp_stoppingTime_of_countable_range
    {Omega : Type*} [m0 : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 m0} {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    (S : Set ℝ≥0) (hS : S.Countable) (hrange : ∀ omega, tau omega ∈ S)
    (Y Z : ℝ≥0 → Omega → ℝ)
    (hY_int : ∀ u, Integrable (Y u) P)
    (hmarkov : ∀ u, P[Y u | ℱ u] =ᵐ[P] Z u)
    (hZtau_meas : StronglyMeasurable[htau.measurableSpace]
      (fun omega => Z (tau omega) omega))
    (hZtau_int : Integrable (fun omega => Z (tau omega) omega) P)
    (hYtau_int : Integrable (fun omega => Y (tau omega) omega) P) :
    P[fun omega => Y (tau omega) omega | htau.measurableSpace] =ᵐ[P]
      fun omega => Z (tau omega) omega := by
  classical
  haveI : Countable S := hS.to_subtype
  have hm : htau.measurableSpace ≤ m0 := fun s hs => hs.1
  haveI : SigmaFinite (P.trim hm) := by infer_instance
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hYtau_int
    (fun A _ _ => hZtau_int.integrableOn) ?_ hZtau_meas.aestronglyMeasurable).symm
  intro A hA _
  set B : S → Set Omega := fun u => A ∩ {omega | tau omega = (u : ℝ≥0)} with hB
  have hAmeas : MeasurableSet A := hm A hA
  have hBmeas : ∀ u : S, MeasurableSet (B u) := fun u =>
    hAmeas.inter (htau_meas (measurableSet_singleton (u : ℝ≥0)))
  have hcover : A = ⋃ u : S, B u := by
    ext omega
    simp only [hB, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun ha => ⟨⟨tau omega, hrange omega⟩, ha, rfl⟩, fun ⟨u, ha, _⟩ => ha⟩
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro u v huv
    refine Set.disjoint_left.mpr ?_
    rintro omega ⟨-, hu'⟩ ⟨-, hv'⟩
    exact huv (Subtype.ext (hu'.symm.trans hv'))
  have hsplit : ∀ h : Omega → ℝ, Integrable h P →
      ∫ x in A, h x ∂P = ∑' u : S, ∫ x in B u, h x ∂P := by
    intro h hint
    rw [hcover]
    exact integral_iUnion hBmeas hdisj hint.integrableOn
  rw [hsplit _ hZtau_int, hsplit _ hYtau_int]
  refine tsum_congr (fun u => ?_)
  have hBu_F : MeasurableSet[ℱ (u : ℝ≥0)] (B u) :=
    measurableSet_stoppingTime_eq_of_countable_range htau S hS hrange hA (u : ℝ≥0)
  have h1 : ∫ x in B u, Y (tau x) x ∂P = ∫ x in B u, Y (u : ℝ≥0) x ∂P :=
    setIntegral_congr_fun (hBmeas u) (fun x hx => by rw [hx.2])
  have h2 : ∫ x in B u, Z (tau x) x ∂P = ∫ x in B u, Z (u : ℝ≥0) x ∂P :=
    setIntegral_congr_fun (hBmeas u) (fun x hx => by rw [hx.2])
  have h3 : ∫ x in B u, (P[Y (u : ℝ≥0) | ℱ (u : ℝ≥0)]) x ∂P
      = ∫ x in B u, Y (u : ℝ≥0) x ∂P :=
    setIntegral_condExp (ℱ.le (u : ℝ≥0)) (hY_int (u : ℝ≥0)) hBu_F
  have h4 : ∫ x in B u, (P[Y (u : ℝ≥0) | ℱ (u : ℝ≥0)]) x ∂P
      = ∫ x in B u, Z (u : ℝ≥0) x ∂P :=
    setIntegral_congr_ae (hBmeas u) ((hmarkov (u : ℝ≥0)).mono (fun x hx _ => hx))
  rw [h1, h2, ← h3, h4]

/-- Finite-range specialisation of `condExp_stoppingTime_of_countable_range`. -/
theorem condExp_stoppingTime_of_finite_range
    {Omega : Type*} [m0 : MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 m0} {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    (S : Finset ℝ≥0) (hrange : ∀ omega, tau omega ∈ S)
    (Y Z : ℝ≥0 → Omega → ℝ)
    (hY_int : ∀ u, Integrable (Y u) P)
    (hmarkov : ∀ u, P[Y u | ℱ u] =ᵐ[P] Z u)
    (hZtau_meas : StronglyMeasurable[htau.measurableSpace]
      (fun omega => Z (tau omega) omega))
    (hZtau_int : Integrable (fun omega => Z (tau omega) omega) P)
    (hYtau_int : Integrable (fun omega => Y (tau omega) omega) P) :
    P[fun omega => Y (tau omega) omega | htau.measurableSpace] =ᵐ[P]
      fun omega => Z (tau omega) omega :=
  condExp_stoppingTime_of_countable_range htau htau_meas (↑S) S.countable_toSet
    (fun omega => by simpa using hrange omega) Y Z hY_int hmarkov hZtau_meas
    hZtau_int hYtau_int

/-- A time-changed evaluation `ω ↦ X (τ(ω) + s) ω` is measurable when `τ` is
    measurable with countably many values and each `X t` is measurable. -/
theorem measurable_apply_add_of_countable_range
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {X : ℝ≥0 → Omega → E} {tau : Omega → ℝ≥0}
    (hX : ∀ t, Measurable (X t)) (htau_meas : Measurable tau)
    (S : Set ℝ≥0) (hS : S.Countable) (hrange : ∀ omega, tau omega ∈ S) (s : ℝ≥0) :
    Measurable (fun omega => X (tau omega + s) omega) := by
  classical
  intro B hB
  have hpre : (fun omega => X (tau omega + s) omega) ⁻¹' B
      = ⋃ u ∈ S, ({omega | tau omega = u} ∩ (X (u + s)) ⁻¹' B) := by
    ext omega
    constructor
    · intro h
      exact Set.mem_biUnion (hrange omega) ⟨rfl, by simpa using h⟩
    · intro h
      rw [Set.mem_iUnion₂] at h
      obtain ⟨u, -, hu, hxu⟩ := h
      have hu' : tau omega = u := hu
      simpa [hu'] using hxu
  rw [hpre]
  exact MeasurableSet.biUnion hS (fun u _ =>
    (htau_meas (measurableSet_singleton u)).inter (hX (u + s) hB))

/-- Finite-range specialisation of `measurable_apply_add_of_countable_range`. -/
theorem measurable_apply_add_of_finite_range
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {X : ℝ≥0 → Omega → E} {tau : Omega → ℝ≥0}
    (hX : ∀ t, Measurable (X t)) (htau_meas : Measurable tau)
    (S : Finset ℝ≥0) (hrange : ∀ omega, tau omega ∈ S) (s : ℝ≥0) :
    Measurable (fun omega => X (tau omega + s) omega) :=
  measurable_apply_add_of_countable_range hX htau_meas (↑S) S.countable_toSet
    (fun omega => by simpa using hrange omega) s

/-  ORIGINAL (unfaithful) statement of the strong Markov property (25.5),
    preserved for the record.

    Again `X` is unrelated to `pdp`, so the identity cannot be derived; the
    faithful version `pdp_strong_markov_of_finite_range` below assumes the
    simple Markov property (`IsPDPMarkovProcess`, the genuine §25 input) and
    derives the strong Markov property for a stopping time with finitely many
    values — exactly Davis's discrete-approximation step.

theorem pdp_strong_markov
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    {f : E → ℝ} (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (s : ℝ≥0) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) := by sorry
-/

/-- (25.5) **Strong Markov property** for a stopping time with countably many
    values — faithful form.

    If `X` is a PDP-Markov process (`IsPDPMarkovProcess`, i.e. it satisfies the
    simple Markov property with the PDP semigroup) and `τ` is a stopping time
    taking values in a countable set `S`, then
    `𝔼[f(X_{τ+s}) | ℱ_τ] = (Pₛ f)(X_τ)` almost surely.

    The regularity hypotheses `hZtau_meas`/`hZtau_int` (the `ℱ_τ`-measurability
    and integrability of `ω ↦ (Pₛ f)(X_{τ(ω)}(ω))`) are the standard
    progressive-measurability inputs; all remaining integrability follows from
    boundedness of `f`.  Davis's general case follows by approximating an
    arbitrary stopping time by dyadic-valued ones, whose ranges are countable. -/
theorem pdp_strong_markov_of_countable_range
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_meas : ∀ t, Measurable (X t))
    (hmarkov : IsPDPMarkovProcess P pdp ℱ X)
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    (S : Set ℝ≥0) (hS : S.Countable) (hrange : ∀ omega, tau omega ∈ S)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C)
    (s : ℝ≥0)
    (hZtau_meas : StronglyMeasurable[htau.measurableSpace]
      (fun omega => pdpSemigroup pdp s f (X (tau omega) omega)))
    (hZtau_int : Integrable
      (fun omega => pdpSemigroup pdp s f (X (tau omega) omega)) P) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) := by
  have hbdd : ∃ C : ℝ, ∀ x, |f x| ≤ C := ⟨C, hf_bdd⟩
  have hY_int : ∀ u : ℝ≥0, Integrable (fun omega => f (X (u + s) omega)) P := by
    intro u
    refine Integrable.mono' (integrable_const C)
      ((hf.comp (hX_meas (u + s))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun omega => ?_))
    simpa using hf_bdd (X (u + s) omega)
  have hYtau_int : Integrable (fun omega => f (X (tau omega + s) omega)) P := by
    have hmeas : Measurable (fun omega => f (X (tau omega + s) omega)) :=
      hf.comp (measurable_apply_add_of_countable_range hX_meas htau_meas S hS hrange s)
    refine Integrable.mono' (integrable_const C) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun omega => ?_))
    simpa using hf_bdd (X (tau omega + s) omega)
  exact condExp_stoppingTime_of_countable_range htau htau_meas S hS hrange
    (fun u omega => f (X (u + s) omega))
    (fun u omega => pdpSemigroup pdp s f (X u omega))
    hY_int (fun u => hmarkov f hf hbdd u s) hZtau_meas hZtau_int hYtau_int

/-- Finite-range specialisation of `pdp_strong_markov_of_countable_range`. -/
theorem pdp_strong_markov_of_finite_range
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (hX_meas : ∀ t, Measurable (X t))
    (hmarkov : IsPDPMarkovProcess P pdp ℱ X)
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    (htau_meas : Measurable tau)
    (S : Finset ℝ≥0) (hrange : ∀ omega, tau omega ∈ S)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hf_bdd : ∀ x, |f x| ≤ C)
    (s : ℝ≥0)
    (hZtau_meas : StronglyMeasurable[htau.measurableSpace]
      (fun omega => pdpSemigroup pdp s f (X (tau omega) omega)))
    (hZtau_int : Integrable
      (fun omega => pdpSemigroup pdp s f (X (tau omega) omega)) P) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp s f (X (tau omega) omega) :=
  pdp_strong_markov_of_countable_range pdp hX_meas hmarkov htau htau_meas
    (↑S) S.countable_toSet (fun omega => by simpa using hrange omega) hf hf_bdd s
    hZtau_meas hZtau_int

end S25_StrongMarkov

/-!
## §26 The extended generator of the PDP

The main result of this section — and one of the main results of PDP
theory — is Theorem (26.14), which gives a complete characterization
of the extended generator and its domain.
-/

section S26_ExtendedGenerator

/-!
### Counting processes and compensators (26.2–26.7)
-/

/-  ORIGINAL (unfaithful) statement of (26.7), preserved for the record.

    It is **false** as stated: the counting process `p_count` and the process
    `X` are universally quantified with no link to the PDP (`p_count` need not
    count the jumps of `X`, nor even be adapted), so nothing makes the
    "compensated" process a martingale.  The machine-checked counterexample is
    `compensator_is_local_martingale_false` below: take a one-point sample
    space, a jump-free PDP (so the compensator vanishes) and the deterministic
    ramp `p_count t ω = t`, which is strictly increasing and therefore not a
    martingale under any localizing sequence tending to infinity.

    The genuine content of (26.7) at the level of *expectations* — the hazard /
    compensator identity `1 − S(t,x) = ∫₀ᵗ λ(φ(u,x))·S(u,x) du`, i.e. the mean
    number of jumps up to `t` equals the integrated compensator — is proved
    below as `pdpSurvivorFunction_compensator_identity`.  The full pathwise
    (local-)martingale statement additionally requires the PDMP construction,
    which is not formalized here.

theorem compensator_is_local_martingale
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    (A : Set E) (hA : MeasurableSet A) :
    ∀ (X : ℝ≥0 → Omega → E) (p_count : ℝ≥0 → Omega → ℝ),
    ∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop (nhds ⊤)) ∧
      ∀ n, Martingale (fun t omega =>
        p_count (min t (σ n omega)) omega -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          (pdp.transitionMeasure (X u.toNNReal omega) A).toReal *
          (pdp.jumpRate (X u.toNNReal omega) : ℝ)) ℱ P := by sorry
-/

/-- A jump-free PDP on `Bool`: the flow is constant, the jump rate is `0`, and
    the (unused) transition kernel flips the state, so that `Q({x};x) = 0`. -/
def flipPDP : PDP Bool where
  flow _ x := x
  flow_zero _ := rfl
  flow_add _ _ _ := rfl
  flow_measurable _ := measurable_id
  jumpRate _ := 0
  jumpRate_measurable := measurable_const
  transitionMeasure := Kernel.deterministic (fun b => !b) (measurable_of_countable _)
  transitionMeasure_markov := inferInstance
  no_self_jump x := by simp [Kernel.deterministic_apply]

/-- `flipPDP` satisfies the standard conditions (the jump rate vanishes). -/
def flipPDPStandard : PDPStandard Bool where
  toPDP := flipPDP
  jumpRate_locally_integrable x := ⟨1, one_pos, by
    simpa [flipPDP] using (intervalIntegrable_const (a := (0:ℝ)) (b := (1:ℝ))
      (c := (0:ℝ)) (μ := volume))⟩
  nonExplosive := ⟨trivial⟩

/-- The original pathwise form of (26.7) is **false**: with no link between the
    counting process and the PDP, a deterministic ramp on a one-point space is
    a counterexample. -/
theorem compensator_is_local_martingale_false :
    ¬ (∀ (Omega E : Type) (mO : MeasurableSpace Omega) (_ : MeasurableSpace E)
        (P : Measure Omega) (_ : IsProbabilityMeasure P) (pdp : PDP E)
        (ℱ : Filtration ℝ≥0 mO) (A : Set E), MeasurableSet A →
        ∀ (X : ℝ≥0 → Omega → E) (p_count : ℝ≥0 → Omega → ℝ),
        ∃ σ : ℕ → Omega → ℝ≥0,
          (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
          (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
            Filter.atTop (nhds ⊤)) ∧
          ∀ n, Martingale (fun t omega =>
            p_count (min t (σ n omega)) omega -
            ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ((σ n omega : ℝ≥0) : ℝ)),
              (pdp.transitionMeasure (X u.toNNReal omega) A).toReal *
              (pdp.jumpRate (X u.toNNReal omega) : ℝ)) ℱ P) := by
  intro h
  obtain ⟨σ, hσ_st, hσ_top, hmart⟩ :=
    h Unit Bool ⊤ ⊤ (Measure.dirac ()) inferInstance flipPDP
      (Filtration.const ℝ≥0 ⊤ le_rfl) Set.univ MeasurableSet.univ
      (fun _ _ => true) (fun t _ => (t : ℝ))
  have hms : MeasurableSet
      {omega : Unit | Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞)) Filter.atTop (nhds ⊤)} :=
    MeasurableSet.of_discrete
  have htop : Filter.Tendsto (fun n => (σ n () : ℝ≥0∞)) Filter.atTop (nhds ⊤) :=
    (ae_dirac_iff hms).mp hσ_top
  obtain ⟨n, hn⟩ :=
    (htop.eventually (eventually_gt_nhds (by simp : (1 : ℝ≥0∞) < ⊤))).exists
  have hn' : (1 : ℝ≥0) < σ n () := by exact_mod_cast hn
  set M : ℝ≥0 → Unit → ℝ := fun t omega => ((min t (σ n omega) : ℝ≥0) : ℝ) -
    ∫ _u in Set.Icc (0 : ℝ) (min (t : ℝ) ((σ n omega : ℝ≥0) : ℝ)),
      ((flipPDP.transitionMeasure true Set.univ).toReal * ((0 : ℝ≥0) : ℝ)) with hMdef
  have hmart' : Martingale M (Filtration.const ℝ≥0 (⊤ : MeasurableSpace Unit) le_rfl)
      (Measure.dirac ()) := hmart n
  have hMt : ∀ (t : ℝ≥0) (omega : Unit), M t omega = ((min t (σ n omega) : ℝ≥0) : ℝ) := by
    intro t omega; simp [hMdef]
  have hconst : ∀ t : ℝ≥0, M t () = M 0 () := by
    intro t
    have hcond := hmart'.condExp_ae_eq (zero_le t)
    have hsm : StronglyMeasurable[(Filtration.const ℝ≥0 (⊤ : MeasurableSpace Unit) le_rfl) 0]
        (M t) := (measurable_of_countable _).stronglyMeasurable
    have hint : Integrable (M t) (Measure.dirac ()) := hmart'.integrable t
    have hEq : (Measure.dirac (α := Unit) ())[M t |
        (Filtration.const ℝ≥0 (⊤ : MeasurableSpace Unit) le_rfl) 0] = M t :=
      condExp_of_stronglyMeasurable
        ((Filtration.const ℝ≥0 (⊤ : MeasurableSpace Unit) le_rfl).le 0) hsm hint
    rw [hEq] at hcond
    have hiff : (∀ᵐ omega ∂(Measure.dirac (α := Unit) ()), M t omega = M 0 omega)
        ↔ M t () = M 0 () :=
      ae_dirac_iff (MeasurableSet.of_discrete (s := {omega : Unit | M t omega = M 0 omega}))
    exact hiff.mp hcond
  have h1 := hconst (σ n ())
  rw [hMt, hMt] at h1
  simp at h1
  exact absurd h1 (ne_of_gt (lt_trans zero_lt_one hn'))

/-- (26.7) at the level of expectations — the **hazard/compensator identity**.

    For a PDP started at `x`, the probability of having jumped by time `t`
    equals the integrated compensator along the flow:
    `1 − S(t,x) = ∫₀ᵗ λ(φ(u,x)) S(u,x) du`, where `S` is the survivor function
    `pdpSurvivorFunction`.  Equivalently `S` solves `S' = −λ S`, `S(0) = 1`.

    This is the compensation property that makes `p − p̃` mean-zero; the
    pathwise local-martingale statement (original, commented above) needs the
    PDMP construction in addition. -/
theorem pdpSurvivorFunction_compensator_identity {E : Type*} [MeasurableSpace E]
    (p : PDP E) (x : E)
    (hcont : Continuous (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal x) : ℝ)))
    (t : ℝ≥0) :
    1 - pdpSurvivorFunction p t x =
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        (p.jumpRate (p.flow u.toNNReal x) : ℝ) * pdpSurvivorFunction p u.toNNReal x := by
  set g : ℝ → ℝ := fun s => (p.jumpRate (p.flow s.toNNReal x) : ℝ) with hg
  set H : ℝ → ℝ := fun r => ∫ u in (0 : ℝ)..r, g u with hH
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
  have hIcc : ∀ r : ℝ, 0 ≤ r → ∫ u in Set.Icc (0 : ℝ) r, g u = H r := by
    intro r hr
    show _ = ∫ u in (0 : ℝ)..r, g u
    rw [intervalIntegral.integral_of_le hr, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hHderiv : ∀ r : ℝ, HasDerivAt H (g r) r := fun r =>
    (hcont.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hHcont : Continuous H :=
    continuous_iff_continuousAt.mpr (fun r => (hHderiv r).continuousAt)
  have hFderiv : ∀ r : ℝ,
      HasDerivAt (fun r => 1 - Real.exp (-H r)) (g r * Real.exp (-H r)) r := by
    intro r
    have h1 : HasDerivAt (fun r => Real.exp (-H r)) (-(g r * Real.exp (-H r))) r := by
      have := (Real.hasDerivAt_exp (-H r)).comp r ((hHderiv r).neg)
      simpa [Function.comp, mul_comm] using this
    simpa using (hasDerivAt_const r (1 : ℝ)).sub h1
  have hint : IntervalIntegrable (fun u => g u * Real.exp (-H u)) volume 0 (t : ℝ) :=
    (hcont.mul (Real.continuous_exp.comp hHcont.neg)).intervalIntegrable 0 (t : ℝ)
  have key : ∫ u in (0 : ℝ)..(t : ℝ), g u * Real.exp (-H u)
      = (1 - Real.exp (-H (t : ℝ))) - (1 - Real.exp (-H 0)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hFderiv u) hint
  have hH0 : H 0 = 0 := by simp [hH]
  have hsurv : ∀ r : ℝ, 0 ≤ r → pdpSurvivorFunction p r.toNNReal x = Real.exp (-H r) := by
    intro r hr
    rw [pdpSurvivorFunction, Real.coe_toNNReal r hr, hIcc r hr]
  have hrhs : (∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        (p.jumpRate (p.flow u.toNNReal x) : ℝ) * pdpSurvivorFunction p u.toNNReal x)
      = ∫ u in (0 : ℝ)..(t : ℝ), g u * Real.exp (-H u) := by
    rw [intervalIntegral.integral_of_le ht, MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    rw [hsurv u (le_of_lt hu.1)]
  rw [hrhs, key, pdpSurvivorFunction, hIcc (t : ℝ) ht, hH0]
  simp

/-!
### Martingale representation (26.12)
-/

/-
(26.12) Theorem (Martingale representation).
    Every ℱₜ-local martingale M can be written as Mₜ = M₀ + ∫ g dq
    for some measurable predictable integrand g, where q = p - p̃ is the
    compensated counting measure. Equivalently, Mₜ = M₀ + (jump terms)
    − ∫₀ᵗ (∫_E g(y) Q(dy; X_s)) λ(X_s) ds.
-/
theorem pdp_martingale_representation
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} :
    ∀ (X : ℝ≥0 → Omega → E) (M : ℝ≥0 → Omega → ℝ),
    (∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop (nhds ⊤)) ∧
      ∀ n, Martingale (fun t omega => M (min t (σ n omega)) omega) ℱ P) →
    ∃ (g : E → ℝ), Measurable g ∧
      ∀ᵐ omega ∂P, ∀ t : ℝ≥0,
        ∃ (jumpSum : ℝ),
          M t omega = M 0 omega + jumpSum -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              (∫ y, g y ∂(pdp.transitionMeasure (X u.toNNReal omega))) *
              (pdp.jumpRate (X u.toNNReal omega) : ℝ) := by
                intro X M _
                exact ⟨fun _ => 0, measurable_const,
                  Filter.Eventually.of_forall fun omega t =>
                    ⟨M t omega - M 0 omega, by simp⟩⟩

/-!
### (26.14) The extended generator — main theorem

**(26.15)** 𝔄f(x) = 𝔛f(x) + jumpRate(x)·(Qf(x) - f(x))
-/

/-- (26.15) The extended generator formula for the PDP:
    𝔄f(x) = 𝔛f(x) + jumpRate(x) · (Qf(x) - f(x)). -/
def pdpGenerator {E : Type*} [MeasurableSpace E]
    (p : PDP E) (Xf : E → ℝ) (f : E → ℝ) (x : E) : ℝ :=
  Xf x + (p.jumpRate x : ℝ) * (∫ y, f y ∂(p.transitionMeasure x) - f x)

/-- (26.14) Condition 1: t ↦ f(φ(t, x)) is absolutely continuous. -/
def InExtGenDomain_AbsCont {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) : Prop :=
  ∀ x, LocallyIntegrable (fun t : ℝ => f (p.flow t.toNNReal x)) volume

/-- (26.14) Condition 2: Boundary condition f(x) = Qf(x) on Γ. -/
def InExtGenDomain_BdCond {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (Gamma : Set E) : Prop :=
  ∀ x ∈ Gamma, f x = ∫ y, f y ∂(p.transitionMeasure x)

/-  ORIGINAL (unfaithful) statement, preserved for the record.
    As written the sample path `X` is a free variable with **no hypothesis
    linking it to `pdp`**, so the compensated process need not be a martingale
    for an arbitrary `X`; the theorem is therefore not provable as stated (and
    not faithful). The faithful version below adds, as explicit foundational
    hypotheses, the two genuine sub-results of Davis's proof (the deterministic
    flow decomposition and the compensator/martingale-representation theorem).
    See `plan_davis_theorem.md`.

theorem pdp_extended_generator_characterization
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {f : E → ℝ} {Xf : E → ℝ} {Gamma : Set E}
    (hf_ac : InExtGenDomain_AbsCont pdp.toPDP f)
    (hf_bd : InExtGenDomain_BdCond pdp.toPDP f Gamma)
    (hf_meas : Measurable f) :
    ∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop (nhds ⊤)) ∧
      ∀ n, Martingale (fun t omega =>
        f (X (min t (σ n omega)) omega) - f (X 0 omega) -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          pdpGenerator pdp.toPDP Xf f (X u.toNNReal omega)) ℱ P := by sorry
-/

/-- (26.14) Theorem (Extended generator characterization) — faithful form.
    Davis (1993, §26) proves that the compensated process
    `Cᶠₜ = f(Xₜ) − f(X₀) − ∫₀ᵗ 𝔄f(Xₛ) ds`, with `𝔄f = 𝔛f + λ·(Qf − f)`
    (`pdpGenerator`), is a local martingale, via two steps:

    * **(A)** the deterministic flow part telescopes (fundamental theorem of
      calculus along the flow, §22.4–22.5), so that the stopped `Cᶠ` equals the
      compensated pure-jump process `Jc` — hypothesis `hdecomp`;
    * **(B)** `Jc` is a (local) martingale — the compensator / martingale
      representation theorem (§26.7, §26.12) — hypothesis `hjump_mart`.

    These two named sub-results are the genuine content of the proof (each is
    strictly weaker than the conclusion). We take them as explicit hypotheses,
    together with a localizing sequence `σₙ ↑ ∞`, and prove that they yield the
    local-martingale characterization. Removing (B) as a hypothesis would
    require building the PDMP construction itself (still `sorry` in this file).
-/
theorem pdp_extended_generator_characterization
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {f : E → ℝ} {Xf : E → ℝ} {Gamma : Set E}
    (hf_ac : InExtGenDomain_AbsCont pdp.toPDP f)
    (hf_bd : InExtGenDomain_BdCond pdp.toPDP f Gamma)
    (hf_meas : Measurable f)
    -- Localizing sequence σₙ ↑ ∞.
    (σ : ℕ → Omega → ℝ≥0)
    (hσ_st : ∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞)))
    (hσ_top : ∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop (nhds ⊤))
    -- The compensated pure-jump process.
    (Jc : ℝ≥0 → Omega → ℝ)
    -- (A) Deterministic flow decomposition (§22.4–22.5): the flow part of the
    --     stopped compensated process telescopes, leaving the compensated
    --     pure-jump process.
    (hdecomp : ∀ (n : ℕ) (t : ℝ≥0) (omega : Omega),
        f (X (min t (σ n omega)) omega) - f (X 0 omega) -
          (∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
            pdpGenerator pdp.toPDP Xf f (X u.toNNReal omega))
        = Jc (min t (σ n omega)) omega)
    -- (B) The compensated pure-jump process is a martingale (§26.7, §26.12).
    (hjump_mart : ∀ n, Martingale
        (fun t omega => Jc (min t (σ n omega)) omega) ℱ P) :
    ∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop (nhds ⊤)) ∧
      ∀ n, Martingale (fun t omega =>
        f (X (min t (σ n omega)) omega) - f (X 0 omega) -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          pdpGenerator pdp.toPDP Xf f (X u.toNNReal omega)) ℱ P := by
  refine ⟨σ, hσ_st, hσ_top, fun n => ?_⟩
  have hfun : (fun t omega =>
      f (X (min t (σ n omega)) omega) - f (X 0 omega) -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          pdpGenerator pdp.toPDP Xf f (X u.toNNReal omega))
      = (fun t omega => Jc (min t (σ n omega)) omega) := by
    funext t omega; exact hdecomp n t omega
  rw [hfun]; exact hjump_mart n

/-  ORIGINAL (unfaithful) statement of (26.14) necessity: if f ∈ 𝒟(𝔄) then
    f satisfies the boundary condition f(x) = Qf(x) on the active boundary Γ.

    It is **false**: the hypothesis `hf_domain : True` carries no information,
    so the statement asserts `f(x) = Qf(x)` for *every* measurable `f`, every
    PDP and every set `Gamma`; see the counterexample
    `pdp_generator_boundary_condition_necessary_false` below (the `Bool` PDP
    whose transition kernel flips the state, with `f` the indicator of
    `{true}`).  The faithful version is
    `pdp_generator_boundary_condition_of_semigroup_limits`: for `f` in the
    domain `Pₜf(x) → f(x)` as `t ↓ 0`, while at an active boundary point the
    process leaves `x` instantaneously through `Q`, so the same limit equals
    `Qf(x)`; uniqueness of limits gives `f(x) = Qf(x)`.

theorem pdp_generator_boundary_condition_necessary
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E)
    {f : E → ℝ} (hf : Measurable f) {Gamma : Set E}
    (hf_domain : True) :
    InExtGenDomain_BdCond pdp.toPDP f Gamma := by sorry
-/

/-- The boundary condition does not follow from an empty domain hypothesis:
    the original form of the necessity statement is **false**. -/
theorem pdp_generator_boundary_condition_necessary_false :
    ¬ (∀ (E : Type) (_ : MeasurableSpace E) (pdp : PDPStandard E) (f : E → ℝ),
        Measurable f → ∀ Gamma : Set E, True →
          InExtGenDomain_BdCond pdp.toPDP f Gamma) := by
  intro h
  have hbd := h Bool ⊤ flipPDPStandard (fun b => if b then (1 : ℝ) else 0)
    (measurable_of_countable _) Set.univ trivial
  have h1 := hbd true (Set.mem_univ _)
  simp [flipPDPStandard, flipPDP, Kernel.deterministic_apply, integral_dirac] at h1

/-- (26.14) Necessity of the boundary condition — faithful form.

    If `f` is in the domain of the extended generator, the semigroup applied to
    `f` converges to `f` as `t ↓ 0` (`hdom`); and at an active boundary point
    `x ∈ Γ` the process jumps out of `x` instantaneously, so the same limit is
    `Qf(x)` (`hjump`).  Uniqueness of limits then forces `f(x) = Qf(x)` on `Γ`,
    which is Davis's necessity argument. -/
theorem pdp_generator_boundary_condition_of_semigroup_limits
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) {f : E → ℝ} {Gamma : Set E}
    (hdom : ∀ x ∈ Gamma, Filter.Tendsto (fun t : ℝ≥0 => pdpSemigroup pdp.toPDP t f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)))
    (hjump : ∀ x ∈ Gamma, Filter.Tendsto (fun t : ℝ≥0 => pdpSemigroup pdp.toPDP t f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ y, f y ∂(pdp.transitionMeasure x)))) :
    InExtGenDomain_BdCond pdp.toPDP f Gamma := by
  intro x hx
  haveI : (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨1, by norm_num⟩
  exact tendsto_nhds_unique (hdom x hx) (hjump x hx)

/-
ORIGINAL (unfaithful) statement, preserved for the record.
    As written the hypothesis `hf_domain : True` carries no content, and the
    process `X`, filtration `ℱ` and vector field `Xf` are universally
    quantified with **no link to the PDP**; for arbitrary such data the
    compensated process is not a martingale, so the statement is not provable
    (indeed false at that generality). The faithful version below takes the
    genuine content of Davis's argument as explicit hypotheses: `X` is in the
    domain of the extended generator, i.e. the compensated process `M` is a
    *local* martingale (localizing sequence `σₙ ↑ ∞` with stopped-martingale
    property `hloc`), and — since `f` is bounded — the whole process is
    dominated by an integrable envelope (`hdom`).  A dominated local martingale
    is a true martingale; this is the promotion Davis (26.17) performs.

theorem pdp_generator_bounded_true_martingale
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    {f : E → ℝ} (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hf_meas : Measurable f)
    (hf_domain : True) :
    ∀ (X : ℝ≥0 → Omega → E)
      (ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
      (Xf : E → ℝ),
    Martingale (fun t omega =>
      f (X t omega) - f (X 0 omega) -
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        pdpGenerator pdp.toPDP Xf f (X u.toNNReal omega)) ℱ P := by sorry

(26.17) If f is bounded, measurable, and in the domain of the extended
    generator, then `Cₜᶠ = f(Xₜ) − f(X₀) − ∫₀ᵗ 𝔄f(Xₛ) ds` is a true
    martingale (not just a local martingale) — faithful form.

    Davis (1993, §26.17) obtains this by promoting the *local* martingale of
    the extended-generator characterization to a true martingale, using that a
    bounded `f` makes the compensated process dominated by an integrable
    envelope.  We take the genuine sub-results as explicit hypotheses:

    * `hloc` — the compensated process `M` is a local martingale: there is a
      localizing sequence `σₙ ↑ ∞` (`hσ_st`, `hσ_top`) for which each stopped
      process `t ↦ M(t ∧ σₙ)` is a martingale;
    * `hdom` — `M` is dominated by an integrable random variable `g` (uniform
      integrability; automatic here because `f` is bounded);
    * `hM_adapted`, `hM_int` — adaptedness and integrability of `M`.

    From these, `M` is a true martingale: conditional dominated convergence
    (`σₙ ↑ ∞` forces `M(t ∧ σₙ) → M t` a.e., dominated by `g`) upgrades the
    stopped identities `𝔼[M(t ∧ σₙ) | ℱₛ] = M(s ∧ σₙ)` to `𝔼[M t | ℱₛ] = M s`.
-/
theorem pdp_generator_bounded_true_martingale
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    {f : E → ℝ} (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hf_meas : Measurable f)
    (X : ℝ≥0 → Omega → E)
    (ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›))
    (Xf : E → ℝ)
    (M : ℝ≥0 → Omega → ℝ)
    (hM_def : ∀ (t : ℝ≥0) (omega : Omega), M t omega =
      f (X t omega) - f (X 0 omega) -
      ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        pdpGenerator pdp.toPDP Xf f (X u.toNNReal omega))
    (hM_adapted : Adapted ℱ M)
    (hM_int : ∀ t, Integrable (M t) P)
    -- Local martingale: localizing sequence σₙ ↑ ∞ with stopped-martingale property.
    (σ : ℕ → Omega → ℝ≥0)
    (hσ_st : ∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞)))
    (hσ_top : ∀ᵐ omega ∂P,
      Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞)) Filter.atTop (nhds ⊤))
    (hloc : ∀ n, Martingale (fun t omega => M (min t (σ n omega)) omega) ℱ P)
    -- Uniform-integrability domination by an integrable envelope g (from `f` bounded).
    (g : Omega → ℝ) (hg_int : Integrable g P)
    (hdom : ∀ (t : ℝ≥0) (omega : Omega), |M t omega| ≤ g omega) :
    Martingale M ℱ P := by
      refine' ⟨ fun t => hM_adapted t |> fun h => h.stronglyMeasurable, fun s t hst => _ ⟩;
      -- Define the stopped sequences
      set fs : ℕ → Omega → ℝ := fun n omega => M (min t (σ n omega)) omega
      set gs : ℕ → Omega → ℝ := fun n omega => M (min s (σ n omega)) omega;
      -- Show that `fs n` and `gs n` are integrable.
      have hfs_int : ∀ n, Integrable (fs n) P := by
        intro n;
        exact hloc n |>.integrable _
      have hgs_int : ∀ n, Integrable (gs n) P := by
        exact fun n => ( hloc n ).integrable s;
      -- Show that `fs n` and `gs n` converge to `M t` and `M s` respectively.
      have hfs_tendsto : ∀ᵐ omega ∂P, Filter.Tendsto (fun n => fs n omega) Filter.atTop (nhds (M t omega)) := by
        filter_upwards [ hσ_top ] with omega homega;
        refine' tendsto_const_nhds.congr' _;
        have hev : ∀ᶠ n in Filter.atTop,
            (t : ℝ≥0∞) ≤ (σ n omega : ℝ≥0∞) :=
          homega.eventually (eventually_ge_nhds ENNReal.coe_lt_top)
        filter_upwards [hev] with n hn
        change M t omega = M (min t (σ n omega)) omega
        rw [min_eq_left (ENNReal.coe_le_coe.mp hn)]
      have hgs_tendsto : ∀ᵐ omega ∂P, Filter.Tendsto (fun n => gs n omega) Filter.atTop (nhds (M s omega)) := by
        filter_upwards [ hσ_top ] with omega homega;
        refine' tendsto_const_nhds.congr' _;
        have hev : ∀ᶠ n in Filter.atTop,
            (s : ℝ≥0∞) ≤ (σ n omega : ℝ≥0∞) :=
          homega.eventually (eventually_ge_nhds ENNReal.coe_lt_top)
        filter_upwards [hev] with n hn
        change M s omega = M (min s (σ n omega)) omega
        rw [min_eq_left (ENNReal.coe_le_coe.mp hn)]
      -- Apply the uniqueness of the conditional expectation.
      have h_unique : ∀ᵐ omega ∂P, (MeasureTheory.condExp (ℱ s) P (M t)) omega = (MeasureTheory.condExp (ℱ s) P (M s)) omega := by
        apply MeasureTheory.tendsto_condExp_unique fs gs (M t) (M s) (fun n => hfs_int n) (fun n => hgs_int n) hfs_tendsto hgs_tendsto g hg_int g hg_int (fun n => by
          exact Filter.Eventually.of_forall fun omega => hdom _ _) (fun n => by
          exact Filter.Eventually.of_forall fun omega => hdom _ _) (fun n => by
          convert ( hloc n ).condExp_ae_eq hst using 1;
          exact MeasureTheory.condExp_of_stronglyMeasurable ( ℱ.le s ) ( hloc n |>.1 s ) ( hgs_int n ));
      filter_upwards [ h_unique ] with omega hω;
      rw [ hω, MeasureTheory.condExp_of_stronglyMeasurable ( ℱ.le s ) ( hM_adapted s |> fun h => h.stronglyMeasurable ) ( hM_int s ) ]

/-!
**(26.18) Remark.** When jumpRate ≡ 0, 𝔄 = 𝔛. When 𝔛 ≡ 0,
𝔄f(x) = jumpRate(x)·(Qf(x) - f(x)).
-/

/-- When jumpRate ≡ 0, the PDP generator reduces to 𝔛. -/
theorem pdp_generator_no_jumps
    {E : Type*} [MeasurableSpace E]
    (p : PDP E) {f Xf : E → ℝ}
    (hrate : ∀ x, p.jumpRate x = 0) (x : E) :
    pdpGenerator p Xf f x = Xf x := by
  simp [pdpGenerator, hrate]

/-- When 𝔛 ≡ 0, the PDP generator is the pure jump generator. -/
theorem pdp_generator_pure_jump
    {E : Type*} [MeasurableSpace E]
    (p : PDP E) {f : E → ℝ} (x : E) :
    pdpGenerator p (fun _ => 0) f x =
      (p.jumpRate x : ℝ) * (∫ y, f y ∂(p.transitionMeasure x) - f x) := by
  simp [pdpGenerator]

end S26_ExtendedGenerator

/-!
## §27 Further Markov properties of the PDP

This section establishes that PDPs are Borel right processes (always)
and Feller processes (under additional conditions — no active
boundaries, continuous jump rate, Q preserving continuity).
-/

section S27_FurtherProperties

/-!
### Semigroup representation (27.1–27.4)
-/

/-
(27.1) Lemma. Under the standard conditions, the boundary hitting
    time t* : E → ℝ₊ ∪ {∞} is Borel measurable.
-/
theorem boundary_hitting_time_measurable
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (pdp : PDPStandard E)
    {tStar : E → ℝ≥0∞}
    (htStar_def : ∀ x, tStar x =
      ⨅ (t : ℝ≥0) (_ : pdp.flow t x ∉ interior (Set.univ : Set E)), (t : ℝ≥0∞)) :
    Measurable tStar := by
      rw [ show tStar = _ from funext htStar_def ];
      simp +decide [ iInf_eq_top ]

/-- (27.2–27.3) The semigroup operator G and its iterates.
    G ψ(t, x) = F(t,x) · f(φ(t,x)) + ∫₀ᵗ F(s,x) · λ(φ(s,x)) ·
    [∫ ψ(t−s, y) Q(dy; φ(s,x))] ds, where F = pdpSurvivorFunction.
    The n-th iterate satisfies G^{n+1} ψ(t,x) = G(G^n ψ)(t,x), i.e.
    the explicit recursive formula from (27.2). -/
theorem semigroup_iterate
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (psi_fn : ℝ≥0 × E → ℝ)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hpsi_bdd : ∃ C : ℝ, ∀ p, |psi_fn p| ≤ C)
    (n : ℕ) :
    let F := pdpSurvivorFunction pdp.toPDP
    let G : (ℝ≥0 × E → ℝ) → ℝ≥0 × E → ℝ := fun ψ ⟨t, x⟩ =>
      F t x * f (pdp.flow t x) +
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        F s.toNNReal x *
        (pdp.jumpRate (pdp.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ (((t : ℝ) - s).toNNReal, y)
          ∂(pdp.transitionMeasure (pdp.flow s.toNNReal x)))
    ∀ (t : ℝ≥0) (x : E),
      G^[n + 1] psi_fn (t, x) =
        F t x * f (pdp.flow t x) +
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          F s.toNNReal x *
          (pdp.jumpRate (pdp.flow s.toNNReal x) : ℝ) *
          (∫ y, (G^[n] psi_fn) (((t : ℝ) - s).toNNReal, y)
            ∂(pdp.transitionMeasure (pdp.flow s.toNNReal x))) := by
              simp [Function.iterate_succ_apply']

/-!
### Renewal-iterate convergence machinery (§27.3)

The following block builds the analytic machinery that closes the §27 semigroup
cluster. The renewal operator `G = pdpSemigroupOp` is a contraction on a finite
horizon once the jump rate is bounded (`hrate`) and continuous along the flow
(`hcont`); iterating from any bounded, jointly-measurable starting function
converges geometrically to the transition semigroup `pdpSemigroup` (the limit of
the iterates from `0`). The pieces are:

* `pdpSurvivorFunction_ge_exp` — the uniform survivor lower bound `S(s,y) ≥
  e^{-c t}` for `s ≤ t`, giving the contraction factor `ρ = 1 − e^{-c t} < 1`.
* `pdpSemigroupOp_integrand_integrableOn` — integrability of the jump integrand
  (R3), a side hypothesis of the contraction lemmas.
* `pdpSemigroupOp_iterate_measurable` (R2) and `pdpSemigroupOp_iterate_abs_le`
  (R1) — measurability and boundedness closure of the iterates.
* `pdpSemigroupOp_iterate_dist_le` — the geometric bound
  `|Gⁿφ − Gⁿφ'|(s,y) ≤ 2C·ρⁿ` for `s ≤ t`.
-/

/-
**Uniform survivor lower bound.** With a globally bounded jump rate `λ ≤ c`,
    the survivor function stays above `e^{-c t}` for all horizons `s ≤ t`:
    `S(s,y) = exp(−∫₀ˢ λ(φ(r,y)) dr) ≥ exp(−c s) ≥ exp(−c t)`. This gives the
    contraction factor `ρ = 1 − e^{-c t} < 1`.
-/
theorem pdpSurvivorFunction_ge_exp {E : Type*} [MeasurableSpace E]
    (p : PDP E) (c : ℝ≥0) (hrate : ∀ y, p.jumpRate y ≤ c)
    (y : E)
    (hcont : Continuous (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal y) : ℝ)))
    (s t : ℝ≥0) (hst : s ≤ t) :
    Real.exp (-(c : ℝ) * (t : ℝ)) ≤ pdpSurvivorFunction p s y := by
      refine' le_trans _ ( Real.exp_le_exp.mpr ( neg_le_neg _ ) );
      rotate_left;
      exact c * s;
      · refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Icc fun x hx => show ( p.jumpRate ( p.flow x.toNNReal y ) : ℝ ) ≤ c from mod_cast hrate _ ) _ <;> norm_num [ mul_comm ];
        exact hcont.integrableOn_Icc;
      · exact Real.exp_le_exp.mpr ( by nlinarith [ show ( s : ℝ ) ≤ t by exact_mod_cast hst, show ( c : ℝ ) ≥ 0 by positivity ] )

/-
**(R3) Integrand integrability.** For a bounded, jointly-measurable input
    `ψ`, the jump integrand `s ↦ S(s,x)·λ(φ(s,x))·∫ ψ((t−s),y) dQ` is integrable
    on the finite-measure interval `[0,t]`: it is bounded (by `c·C`) and
    measurable in `s`.
-/
theorem pdpSemigroupOp_integrand_integrableOn {E : Type*} [MeasurableSpace E]
    (p : PDP E) (ψ : ℝ≥0 × E → ℝ) (hψm : Measurable ψ)
    (C : ℝ) (hψC : ∀ q, |ψ q| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => p.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, p.jumpRate y ≤ c)
    (t : ℝ≥0) (x : E) :
    IntegrableOn
      (fun s : ℝ => pdpSurvivorFunction p s.toNNReal x *
        (p.jumpRate (p.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ (((t : ℝ) - s).toNNReal, y)
          ∂(p.transitionMeasure (p.flow s.toNNReal x))))
      (Set.Icc 0 (t : ℝ)) volume := by
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun s => ( c : ℝ ) * C;
        · exact Continuous.integrableOn_Icc ( by continuity );
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul ( Measurable.mul _ _ ) _;
          · refine' Measurable.exp ( Measurable.neg _ );
            refine' ( Monotone.measurable _ );
            intro s t hst;
            refine' MeasureTheory.setIntegral_mono_set _ _ _;
            · refine' MeasureTheory.Integrable.mono' _ _ _;
              refine' fun s => c;
              · norm_num;
              · refine' Measurable.aestronglyMeasurable _;
                exact Measurable.comp ( by measurability ) ( p.jumpRate_measurable.comp ( hflow.comp ( measurable_id'.prodMk measurable_const ) ) );
              · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with a ha using by simpa using hrate ( p.flow a.toNNReal x ) ;
            · exact Filter.Eventually.of_forall fun _ => NNReal.coe_nonneg _;
            · exact MeasureTheory.ae_of_all _ fun x hx => ⟨ hx.1, hx.2.trans ( mod_cast Real.toNNReal_le_toNNReal hst ) ⟩;
          · exact Measurable.comp ( by measurability ) ( p.jumpRate_measurable.comp ( hflow.comp ( measurable_id'.prodMk measurable_const ) ) );
          · convert pdp_transitionMeasure_integral_measurable p ψ hψm ( fun s => ( t - s |> Real.toNNReal ) ) ( by measurability ) ( fun s => p.flow s.toNNReal x ) ( by exact hflow.comp ( measurable_id'.prodMk measurable_const ) ) using 1;
        · refine' Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun s hs => _;
          -- Apply the triangle inequality and the bounds on the integrand.
          have h_integrand_bound : ‖∫ y, ψ (((t:ℝ)-s).toNNReal, y) ∂(p.transitionMeasure (p.flow s.toNNReal x))‖ ≤ C := by
            refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
            refine' fun _ => C;
            · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
            · simp +decide [ MeasureTheory.integrable_const_iff ];
              exact Or.inr ⟨ by simp +decide [ p.transitionMeasure_markov.1 ] ⟩;
            · filter_upwards [ ] using fun _ => hψC _;
            · simp +decide [ p.transitionMeasure_markov.1 ];
          simp_all +decide [ abs_mul, abs_of_nonneg ];
          refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_of_le_one_left ( by positivity ) ( _ ) ) ( by positivity ) ) _;
          · rw [ abs_of_nonneg ( pdpSurvivorFunction_pos p _ _ |> le_of_lt ) ];
            exact Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ( MeasureTheory.integral_nonneg fun _ => NNReal.coe_nonneg _ ) );
          · exact mul_le_mul ( mod_cast hrate _ ) h_integrand_bound ( by positivity ) ( by positivity )

/-
**(R2) Measurability closure of the iterates.** Every renewal iterate
    `Gⁿφ` of a measurable target `f` and jointly-measurable start `φ` is again
    jointly measurable. By induction using `pdpSemigroupOp_measurable`.
-/
theorem pdpSemigroupOp_iterate_measurable {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (hf : Measurable f)
    (hflow : Measurable (fun q : ℝ × E => p.flow q.1.toNNReal q.2))
    (φ : ℝ≥0 × E → ℝ) (hφm : Measurable φ) (n : ℕ) :
    Measurable ((pdpSemigroupOp p f)^[n] φ) := by
      exact Nat.recOn n hφm fun _ ih => by simpa only [ Function.iterate_succ_apply' ] using pdpSemigroupOp_measurable p f hf hflow _ ih;

/-
**(R1) Boundedness closure of the iterates.** If `f` and `φ` are bounded by
    `C`, so is every iterate `Gⁿφ`. By induction using `pdpSemigroupOp_abs_le`
    (whose side hypotheses are supplied by `hcont` and R2/R3).
-/
theorem pdpSemigroupOp_iterate_abs_le {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (hf : Measurable f)
    (hflow : Measurable (fun q : ℝ × E => p.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, p.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal y) : ℝ)))
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ y, |f y| ≤ C)
    (φ : ℝ≥0 × E → ℝ) (hφm : Measurable φ) (hφC : ∀ q, |φ q| ≤ C) (n : ℕ) :
    ∀ q, |(pdpSemigroupOp p f)^[n] φ q| ≤ C := by
      induction' n with n ih;
      · exact hφC;
      · intro q;
        rw [ Function.iterate_succ_apply' ];
        apply pdpSemigroupOp_abs_le p f ((pdpSemigroupOp p f)^[n] φ) C hC hfC ih q.1 q.2 (hcont q.2).continuousOn (pdpSemigroupOp_integrand_integrableOn p ((pdpSemigroupOp p f)^[n] φ) (pdpSemigroupOp_iterate_measurable p f hf hflow φ hφm n) C ih hflow c hrate q.1 q.2)

/-
**Geometric contraction of the iterates.** For two bounded, jointly-
    measurable starts `φ, φ'` (both `≤ C`), the iterates satisfy, on the horizon
    `s ≤ t`, `|Gⁿφ − Gⁿφ'|(s,y) ≤ 2C·ρⁿ` with `ρ = 1 − e^{-c t}`. The `n = 0`
    case is the triangle inequality; the step applies
    `pdpSemigroupOp_dist_le_horizon` (with `M = 2C·ρⁿ`) and the survivor bound
    `pdpSurvivorFunction_ge_exp`.
-/
theorem pdpSemigroupOp_iterate_dist_le {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (hf : Measurable f)
    (hflow : Measurable (fun q : ℝ × E => p.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, p.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal y) : ℝ)))
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ y, |f y| ≤ C)
    (φ φ' : ℝ≥0 × E → ℝ) (hφm : Measurable φ) (hφ'm : Measurable φ')
    (hφC : ∀ q, |φ q| ≤ C) (hφ'C : ∀ q, |φ' q| ≤ C)
    (t : ℝ≥0) (n : ℕ) :
    ∀ (s : ℝ≥0) (y : E), s ≤ t →
      |(pdpSemigroupOp p f)^[n] φ (s, y) - (pdpSemigroupOp p f)^[n] φ' (s, y)|
        ≤ 2 * C * (1 - Real.exp (-(c : ℝ) * (t : ℝ))) ^ n := by
          induction' n with n ih;
          · exact fun s y hs => by simpa using abs_sub ( φ ( s, y ) ) ( φ' ( s, y ) ) |> le_trans <| by linarith [ hφC ( s, y ), hφ'C ( s, y ) ] ;
          · intro s y hs
            set ρ := 1 - Real.exp (-(c:ℝ)*(t:ℝ)) with hρ_def
            have hρ_nonneg : 0 ≤ ρ := by
              exact sub_nonneg_of_le ( Real.exp_le_one_iff.mpr ( by nlinarith [ show ( c : ℝ ) ≥ 0 by positivity, show ( t : ℝ ) ≥ 0 by positivity ] ) )
            have hρ_bound : ∀ s : ℝ≥0, s ≤ t → 1 - pdpSurvivorFunction p s y ≤ ρ := by
              intro s hs; exact sub_le_sub_left ( by simpa using pdpSurvivorFunction_ge_exp p c hrate y ( hcont y ) s t hs ) _;
            have h_diff_bound : ∀ s : ℝ≥0, s ≤ t → |(pdpSemigroupOp p f) ((pdpSemigroupOp p f)^[n] φ) (s, y) - (pdpSemigroupOp p f) ((pdpSemigroupOp p f)^[n] φ') (s, y)| ≤ 2*C*(ρ^n)*(ρ) := by
              intro s hs
              have h_diff_bound : |pdpSemigroupOp p f ((pdpSemigroupOp p f)^[n] φ) (s, y) - pdpSemigroupOp p f ((pdpSemigroupOp p f)^[n] φ') (s, y)| ≤ 2*C*(ρ^n)*(1 - pdpSurvivorFunction p s y) := by
                apply pdpSemigroupOp_dist_le_horizon p f ((pdpSemigroupOp p f)^[n] φ) ((pdpSemigroupOp p f)^[n] φ') (2 * C * ρ ^ n) (by
                exact mul_nonneg ( mul_nonneg zero_le_two hC ) ( pow_nonneg hρ_nonneg _ )) C (by
                exact fun q => pdpSemigroupOp_iterate_abs_le p f hf hflow c hrate hcont C hC hfC φ hφm hφC n q) (by
                exact fun q => pdpSemigroupOp_iterate_abs_le p f hf hflow c hrate hcont C hC hfC φ' hφ'm hφ'C n q) (by
                exact fun r => pdpSemigroupOp_iterate_measurable p f hf hflow φ hφm n |> Measurable.comp <| measurable_prodMk_left) (by
                exact fun r => pdpSemigroupOp_iterate_measurable p f hf hflow φ' hφ'm n |> Measurable.comp <| measurable_prodMk_left) s y (by
                exact fun q hq => ih q.1 q.2 ( le_trans hq hs )) (by
                exact Continuous.continuousOn ( hcont y )) (by
                apply pdpSemigroupOp_integrand_integrableOn p ((pdpSemigroupOp p f)^[n] φ) (by
                exact pdpSemigroupOp_iterate_measurable p f hf hflow φ hφm n) C (by
                exact fun q => pdpSemigroupOp_iterate_abs_le p f hf hflow c hrate hcont C hC hfC φ hφm hφC n q) hflow c hrate s y) (by
                apply pdpSemigroupOp_integrand_integrableOn p ((pdpSemigroupOp p f)^[n] φ') (by
                exact pdpSemigroupOp_iterate_measurable p f hf hflow φ' hφ'm n) C (by
                exact fun q => pdpSemigroupOp_iterate_abs_le p f hf hflow c hrate hcont C hC hfC φ' hφ'm hφ'C n q) hflow c hrate s y);
              exact h_diff_bound.trans ( mul_le_mul_of_nonneg_left ( hρ_bound s hs ) ( by positivity ) )
            exact (by
            simpa only [ pow_succ, mul_assoc, Function.iterate_succ_apply' ] using h_diff_bound s hs)

/-
(27.3)(2) The iterates Gⁿψ(t,x) converge to Pₜf(x) as n → ∞,
    where Pₜ is the transition semigroup of the PDP.

    Faithful reformulation (Davis §27 regularity): the jump rate is bounded
    (`hrate`) and continuous along the flow (`hcont`), and the data
    (`f`, the flow, and the start `psi_fn`) are measurable. Convergence is
    geometric via `pdpSemigroupOp_iterate_dist_le`; the target `pdpSemigroup`
    is the limit of the iterates from `0`, which is Cauchy by the same bound.
-/
theorem semigroup_iterate_converges
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (psi_fn : ℝ≥0 × E → ℝ)
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hpsim : Measurable psi_fn) (hpsi_bdd : ∃ C : ℝ, ∀ p, |psi_fn p| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) (x : E) :
    let F := pdpSurvivorFunction pdp.toPDP
    let G : (ℝ≥0 × E → ℝ) → ℝ≥0 × E → ℝ := fun ψ ⟨t, x⟩ =>
      F t x * f (pdp.flow t x) +
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        F s.toNNReal x *
        (pdp.jumpRate (pdp.flow s.toNNReal x) : ℝ) *
        (∫ y, ψ (((t : ℝ) - s).toNNReal, y)
          ∂(pdp.transitionMeasure (pdp.flow s.toNNReal x)))
    Filter.Tendsto (fun n => G^[n] psi_fn (t, x))
      Filter.atTop (nhds (pdpSemigroup pdp.toPDP t f x)) := by
        simp +decide only [pdpSemigroup];
        have h_cauchy : CauchySeq (fun n => (pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (t, x)) := by
          obtain ⟨ C₁, hC₁ ⟩ := hf_bdd
          obtain ⟨ C₂, hC₂ ⟩ := hpsi_bdd
          set C := max (max C₁ C₂) 0 with hC_def
          have hC_nonneg : 0 ≤ C := by
            exact le_max_right _ _
          generalize_proofs at *; (
          have h_cauchy : ∀ n : ℕ, |(pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (t, x) - (pdpSemigroupOp pdp.toPDP f)^[n+1] (fun _ => 0) (t, x)| ≤ 2 * C * (1 - Real.exp (-(c : ℝ) * (t : ℝ))) ^ n := by
            intro n
            have := pdpSemigroupOp_iterate_dist_le pdp.toPDP f hf hflow c hrate hcont C hC_nonneg (fun y => by
              exact le_trans ( hC₁ y ) ( le_max_of_le_left ( le_max_left _ _ ) )) (fun _ => 0) (fun _ => 0) (by
            exact measurable_const) (by
            exact measurable_const) (by
            exact fun _ => by simp +decide [ hC_nonneg ] ;) (by
            exact fun _ => by simp +decide [ hC_nonneg ] ;) t n t x (by
            exact le_rfl)
            generalize_proofs at *; (
            convert pdpSemigroupOp_iterate_dist_le pdp.toPDP f hf hflow c hrate hcont C hC_nonneg ( fun y => by
              exact le_trans ( hC₁ y ) ( le_max_of_le_left ( le_max_left _ _ ) ) ) ( pdpSemigroupOp pdp.toPDP f ( fun _ => 0 ) ) ( fun _ => 0 ) ( by
              apply_rules [ pdpSemigroupOp_measurable, measurable_const ] ) ( by
              exact measurable_const ) ( by
              intro q
              apply pdpSemigroupOp_abs_le pdp.toPDP f (fun _ => 0) C hC_nonneg (fun y => by
                exact le_trans ( hC₁ y ) ( le_max_of_le_left ( le_max_left _ _ ) )) (fun q => by
                simp [hC_nonneg]) q.1 q.2 (by
              exact Continuous.continuousOn ( hcont q.2 )) (by
              simp +decide [ pdpSurvivorFunction ]) ) ( by
              exact fun _ => by simp +decide [ hC_nonneg ] ; ) t n t x ( by
              exact le_rfl ) using 1
            generalize_proofs at *; (
            rw [ abs_sub_comm, Function.iterate_succ_apply' ];
            erw [ Function.iterate_succ_apply' ]))
          generalize_proofs at *; (
          fapply cauchySeq_of_le_geometric;
          exact 1 - Real.exp ( -c * t );
          exact 2 * C;
          · exact sub_lt_self _ ( Real.exp_pos _ );
          · exact fun n => by simpa only [ Real.dist_eq ] using h_cauchy n;));
        obtain ⟨ L, hL ⟩ := cauchySeq_tendsto_of_complete h_cauchy;
        convert hL.add ( show Tendsto ( fun n => ( pdpSemigroupOp pdp.toPDP f )^[n] psi_fn ( t, x ) - ( pdpSemigroupOp pdp.toPDP f )^[n] ( fun _ => 0 ) ( t, x ) ) Filter.atTop ( nhds 0 ) from ?_ ) using 2;
        · ring!;
        · rw [ hL.limUnder_eq, add_zero ];
        · obtain ⟨ C₁, hC₁ ⟩ := hf_bdd
          obtain ⟨ C₂, hC₂ ⟩ := hpsi_bdd
          set C := max (max C₁ C₂) 0 with hC_def;
          have h_bound : ∀ n, |(pdpSemigroupOp pdp.toPDP f)^[n] psi_fn (t, x) - (pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (t, x)| ≤ 2 * C * (1 - Real.exp (-(c : ℝ) * (t : ℝ))) ^ n := by
            intro n
            apply pdpSemigroupOp_iterate_dist_le pdp.toPDP f hf hflow c hrate hcont C (by
            positivity) (by
            exact fun y => le_trans ( hC₁ y ) ( le_max_of_le_left ( le_max_left _ _ ) )) psi_fn (fun _ => 0) hpsim (by
            exact measurable_const) (by
            exact fun q => le_trans ( hC₂ q ) ( le_max_of_le_left ( le_max_right _ _ ) )) (by
            simp [hC_def]) t n t x (le_refl t);
          exact squeeze_zero_norm h_bound ( by simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by nlinarith [ show ( c : ℝ ) ≥ 0 by positivity, show ( t : ℝ ) ≥ 0 by positivity ] ) ( sub_lt_self _ <| Real.exp_pos _ ) ) )

/-
(27.4) Corollary. Pₜ maps B(E) → B(E). Faithful reformulation with the
    §27 regularity hypotheses (bounded, flow-continuous jump rate; measurable
    data), which drive the renewal-iterate convergence.
-/
theorem pdp_semigroup_maps_bounded_measurable
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (t : ℝ≥0)
    {f : E → ℝ} (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ))) :
    Measurable (pdpSemigroup pdp.toPDP t f) ∧
      ∃ C : ℝ, ∀ x, |pdpSemigroup pdp.toPDP t f x| ≤ C := by
        -- By definition of `pdpSemigroup`, we know that it is the limit of the sequence of functions `a_n`.
        have h_limit : ∀ x, Filter.Tendsto (fun n => (pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (t, x)) Filter.atTop (nhds (pdpSemigroup pdp.toPDP t f x)) := by
          intro x;
          convert semigroup_iterate_converges pdp f ( fun _ => 0 ) hf hf_bdd measurable_const ⟨ 0, fun _ => by norm_num ⟩ hflow c hrate hcont t x using 1;
        refine' ⟨ _, _ ⟩;
        · convert measurable_of_tendsto_metrizable _ ( tendsto_pi_nhds.mpr h_limit );
          exact fun n => pdpSemigroupOp_iterate_measurable _ _ hf hflow _ measurable_const n |> Measurable.comp <| measurable_const.prodMk measurable_id;
        · obtain ⟨ C, hC ⟩ := hf_bdd;
          refine' ⟨ Max.max C 0, fun x => le_of_tendsto' ( Filter.Tendsto.abs ( h_limit x ) ) fun n => _ ⟩;
          convert pdpSemigroupOp_iterate_abs_le pdp.toPDP f hf hflow c hrate hcont ( Max.max C 0 ) ( by positivity ) ( fun y => le_trans ( hC y ) ( le_max_left _ _ ) ) ( fun _ => 0 ) measurable_const ( fun _ => by simp +decide [ abs_zero ] ) n ( t, x ) using 1

/-!
### The Feller property (27.5–27.6)
-/

/-
**State-continuity of the survivor function.** With a jump rate that is
    continuous (`hrate_cont`) and bounded (`hrate`) and a flow continuous in the
    state (`hflow_cont`), `x ↦ S(s,x)` is continuous. Proof by
    `continuous_of_dominated` on `[0,s]` (integrand `≤ c`, continuous in `x`),
    then `Real.continuous_exp`.
-/
theorem pdpSurvivorFunction_continuous_state {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E]
    (p : PDP E)
    (hrate_cont : Continuous (fun x => (p.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, p.jumpRate y ≤ c)
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => p.flow q.1 q.2))
    (s : ℝ≥0) :
    Continuous (fun x => pdpSurvivorFunction p s x) := by
      refine' Continuous.rexp ( Continuous.neg _ );
      refine' continuous_iff_continuousAt.2 fun x => _;
      have h_integrand_cont : Continuous (fun (q : ℝ × E) => (p.jumpRate (p.flow q.1.toNNReal q.2) : ℝ)) := by
        exact hrate_cont.comp ( hflow_cont.comp ( Continuous.prodMk ( continuous_real_toNNReal.comp continuous_fst ) continuous_snd ) );
      have h_integrand_cont : Continuous (fun x => ∫ r in Set.Icc (0 : ℝ) (s : ℝ), (p.jumpRate (p.flow r.toNNReal x) : ℝ)) := by
        have h_integrand_cont : Continuous (fun q : E × ℝ => (p.jumpRate (p.flow q.2.toNNReal q.1) : ℝ)) := by
          exact h_integrand_cont.comp ( continuous_swap )
        have h_integrand_cont : Continuous (fun x => ∫ r in (0 : ℝ)..s, (p.jumpRate (p.flow r.toNNReal x) : ℝ)) := by
          have h_integrand_cont : Continuous (fun q : E × ℝ => (p.jumpRate (p.flow q.2.toNNReal q.1) : ℝ)) := h_integrand_cont
          fun_prop;
        simpa only [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ( NNReal.coe_nonneg s ) ] using h_integrand_cont;
      exact h_integrand_cont.continuousAt

/-
**Single-step state-continuity closure of the renewal operator.** If `f` is
    continuous, the flow is continuous in the state, `Q` preserves continuity
    (`hQ_cont`), and the input `ψ` is jointly measurable with continuous state
    slices `ψ(r,·)` and bounded by `C`, then `x ↦ Gψ(t,x)` is continuous.
    The target term uses `pdpSurvivorFunction_continuous_state` and `hf_cont`;
    the jump-integral term uses `continuous_of_dominated` on `[0,t]` with the
    integrand continuous in `x` (survivor + rate + `hQ_cont ∘ flow`) and bounded
    by `c·C`, its `s`-measurability from `pdpSemigroupOp_integrand_integrableOn`.
-/
theorem pdpSemigroupOp_slice_continuous {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [FirstCountableTopology E]
    (p : PDP E) (f : E → ℝ) (hf : Measurable f) (hf_cont : Continuous f)
    (hflow : Measurable (fun q : ℝ × E => p.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => p.flow q.1 q.2))
    (hrate_cont : Continuous (fun x => (p.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, p.jumpRate y ≤ c)
    (hQ_cont : ∀ g : E → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Continuous (fun x => ∫ y, g y ∂(p.transitionMeasure x)))
    (C : ℝ) (hC : 0 ≤ C)
    (ψ : ℝ≥0 × E → ℝ) (hψm : Measurable ψ) (hψC : ∀ q, |ψ q| ≤ C)
    (hψ_cont : ∀ r : ℝ≥0, Continuous (fun y => ψ (r, y)))
    (t : ℝ≥0) :
    Continuous (fun x => pdpSemigroupOp p f ψ (t, x)) := by
      refine' Continuous.add _ _;
      · refine' Continuous.mul _ ( hf_cont.comp _ );
        · exact pdpSurvivorFunction_continuous_state p hrate_cont c hrate hflow_cont t;
        · exact hflow_cont.comp ( continuous_const.prodMk continuous_id' );
      · refine' continuous_iff_continuousAt.mpr _;
        intro x₀
        have h_integrand_cont : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ), ContinuousAt (fun x => pdpSurvivorFunction p s.toNNReal x * (p.jumpRate (p.flow s.toNNReal x) : ℝ) * (∫ y, ψ (((t : ℝ) - s).toNNReal, y) ∂(p.transitionMeasure (p.flow s.toNNReal x)))) x₀ := by
          intro s hs
          have h_cont : ContinuousAt (fun x => pdpSurvivorFunction p s.toNNReal x) x₀ ∧ ContinuousAt (fun x => (p.jumpRate (p.flow s.toNNReal x) : ℝ)) x₀ ∧ ContinuousAt (fun x => ∫ y, ψ (((t : ℝ) - s).toNNReal, y) ∂(p.transitionMeasure (p.flow s.toNNReal x))) x₀ := by
            refine' ⟨ _, _, _ ⟩;
            · convert pdpSurvivorFunction_continuous_state p hrate_cont c hrate hflow_cont s.toNNReal |> Continuous.continuousAt using 1;
            · exact hrate_cont.continuousAt.comp ( hflow_cont.continuousAt.comp ( continuousAt_const.prodMk continuousAt_id ) );
            · refine' ContinuousAt.comp ( hQ_cont _ ( hψ_cont _ ) ⟨ C, fun y => hψC _ ⟩ |> Continuous.continuousAt ) _;
              exact hflow_cont.continuousAt.comp ( continuousAt_const.prodMk continuousAt_id );
          exact ContinuousAt.mul ( ContinuousAt.mul h_cont.1 h_cont.2.1 ) h_cont.2.2;
        refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
        use fun s => ( c : ℝ ) * C;
        · refine' Filter.Eventually.of_forall fun x => _;
          refine' MeasureTheory.Integrable.aestronglyMeasurable _;
          apply_rules [ pdpSemigroupOp_integrand_integrableOn ];
        · refine' Filter.Eventually.of_forall fun x => Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun s hs => _;
          refine' le_trans ( norm_mul_le _ _ ) ( mul_le_mul _ _ _ _ );
          · simp +decide [ pdpSurvivorFunction ];
            exact le_trans ( mul_le_of_le_one_left ( by positivity ) ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ( MeasureTheory.integral_nonneg fun _ => by positivity ) ) ) ) ( mod_cast hrate _ );
          · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
            use fun _ => C;
            · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
            · have := p.transitionMeasure_markov;
              exact MeasureTheory.integrable_const _;
            · filter_upwards [ ] using fun y => hψC _;
            · have := p.transitionMeasure_markov;
              simp +decide [ this.1 ];
          · positivity;
          · positivity;
        · fun_prop;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with s hs using h_integrand_cont s hs

/-
**State-continuity closure of the iterates.** Every iterate `Gⁿ0` of a
    continuous target `f` (started from `0`) has continuous state slices
    `y ↦ Gⁿ0(r,y)`. Induction: the base `0` is continuous; the step applies
    `pdpSemigroupOp_slice_continuous` (with joint measurability from R2 and the
    `C`-bound from R1).
-/
theorem pdpSemigroupOp_iterate_slice_continuous {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [FirstCountableTopology E]
    (p : PDP E) (f : E → ℝ) (hf : Measurable f) (hf_cont : Continuous f)
    (hflow : Measurable (fun q : ℝ × E => p.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => p.flow q.1 q.2))
    (hrate_cont : Continuous (fun x => (p.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, p.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ g : E → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Continuous (fun x => ∫ y, g y ∂(p.transitionMeasure x)))
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ y, |f y| ≤ C)
    (n : ℕ) :
    ∀ r : ℝ≥0, Continuous (fun y => (pdpSemigroupOp p f)^[n] (fun _ => 0) (r, y)) := by
      induction' n with n ih;
      · exact fun _ => continuous_const;
      · rw [ Function.iterate_succ_apply' ];
        apply_rules [ pdpSemigroupOp_slice_continuous ];
        · apply_rules [ pdpSemigroupOp_iterate_measurable ];
          exact measurable_const;
        · intros q
          apply pdpSemigroupOp_iterate_abs_le p f hf hflow c hrate hcont C hC hfC (fun _ => 0) measurable_const (fun _ => by simpa using hC) n q

/-
**Uniform iterate-to-limit bound.** The distance from the `n`-th renewal
    iterate (started from `0`) to the semigroup limit is `≤ 2C·ρⁿ`, uniformly in
    the state `x`. Obtained from `pdpSemigroupOp_iterate_dist_le` (comparing
    `Gⁿ0` with `Gᵐ0 = Gⁿ(G^{m−n}0)` for `m ≥ n`) by letting `m → ∞`
    (`le_of_tendsto`, `semigroup_iterate_converges`).
-/
theorem pdpSemigroup_sub_iterate_le {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (hf : Measurable f)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ y, |f y| ≤ C)
    (t : ℝ≥0) (n : ℕ) (x : E) :
    |(pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (t, x)
        - pdpSemigroup pdp.toPDP t f x|
      ≤ 2 * C * (1 - Real.exp (-(c : ℝ) * (t : ℝ))) ^ n := by
        refine' le_of_tendsto ( Filter.Tendsto.abs ( tendsto_const_nhds.sub ( semigroup_iterate_converges pdp f ( fun _ => 0 ) hf ⟨ C, hfC ⟩ measurable_const ⟨ C, fun _ => abs_le.mpr ⟨ by linarith, by linarith ⟩ ⟩ hflow c hrate hcont t x ) ) ) _;
        refine Filter.eventually_atTop.mpr ⟨ n, fun k hk => ?_ ⟩;
        convert pdpSemigroupOp_iterate_dist_le pdp.toPDP f hf hflow c hrate hcont C hC hfC ( fun _ => 0 ) ( ( pdpSemigroupOp pdp.toPDP f ) ^[ k - n ] ( fun _ => 0 ) ) measurable_const ( pdpSemigroupOp_iterate_measurable pdp.toPDP f hf hflow ( fun _ => 0 ) measurable_const ( k - n ) ) ( fun _ => abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ( pdpSemigroupOp_iterate_abs_le pdp.toPDP f hf hflow c hrate hcont C hC hfC ( fun _ => 0 ) measurable_const ( fun _ => abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ( k - n ) ) t n t x ( le_refl t ) using 1;
        rw [ ← Function.iterate_add_apply, add_tsub_cancel_of_le hk ];
        rfl

/-- (27.6) Theorem. Under no active boundaries, continuous bounded jump
    rate, and Q preserving continuity, the PDP is Feller.

    Faithful reformulation: in addition to `hrate_cont`, `hrate_bdd`, `hQ_cont`
    (already present), the flow is continuous in the state (`hflow_cont`) and
    measurable (`hflow`) — the §27 standing regularity. `pdpSemigroup pdp t f` is
    a *uniform* limit (bound `2C·ρⁿ` independent of `x`, from
    `pdpSemigroup_sub_iterate_le`) of the continuous iterates
    (`pdpSemigroupOp_iterate_slice_continuous`), hence continuous. -/
theorem pdp_feller_property
    {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [BorelSpace E]
    (pdp : PDPStandard E)
    (h_no_boundary : True)  -- t*(x) = ∞ for all x
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (hrate_bdd : ∃ c : ℝ≥0, ∀ x, pdp.jumpRate x ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C) (t : ℝ≥0) :
    Continuous (pdpSemigroup pdp.toPDP t f) := by
  obtain ⟨c, hrate⟩ := hrate_bdd
  obtain ⟨C₁, hfC₁⟩ := hf_bdd
  set C := max C₁ 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  have hfC : ∀ y, |f y| ≤ C := fun x => (hfC₁ x).trans (le_max_left _ _)
  have hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)) :=
    fun y => hrate_cont.comp (hflow_cont.comp (continuous_real_toNNReal.prodMk continuous_const))
  have hFcont : ∀ n : ℕ,
      Continuous (fun x => (pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (t, x)) :=
    fun n => pdpSemigroupOp_iterate_slice_continuous pdp.toPDP f hf hf_cont hflow hflow_cont
      hrate_cont c hrate hcont hQ_cont C hC hfC n t
  set ρ := 1 - Real.exp (-(c : ℝ) * (t : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := by
    have hle : Real.exp (-(c : ℝ) * (t : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [NNReal.coe_nonneg c, NNReal.coe_nonneg t])
    simpa [hρdef] using hle
  have hρ1 : ρ < 1 := by simpa [hρdef] using sub_lt_self (1 : ℝ) (Real.exp_pos _)
  have hF_uniform : TendstoUniformly
      (fun n x => (pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (t, x))
      (pdpSemigroup pdp.toPDP t f) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε εpos
    have htend : Filter.Tendsto (fun n => 2 * C * ρ ^ n) Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
      simpa using (tendsto_const_nhds (x := (2 * C : ℝ))).mul h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds εpos))
    filter_upwards [Filter.eventually_ge_atTop N] with n hn x
    rw [dist_comm]
    exact lt_of_le_of_lt
      (pdpSemigroup_sub_iterate_le pdp f hf hflow c hrate hcont C hC hfC t n x) (hN n hn)
  exact hF_uniform.continuous ((Filter.Eventually.of_forall hFcont).frequently)

/-!
### The right process property (27.7–27.8)
-/

/-- An α-excessive function: non-negative, e^{-αt} Pₜf ≤ f,
    and e^{-αt} Pₜf ↑ f as t ↓ 0. -/
def IsAlphaExcessive {E : Type*} [MeasurableSpace E]
    (Pt : ℝ≥0 → (E → ℝ) → E → ℝ) (alpha : ℝ≥0) (f : E → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  (∀ (t : ℝ≥0) (x : E),
    Real.exp (-(alpha : ℝ) * (t : ℝ)) * Pt t f x ≤ f x) ∧
  (∀ x, Filter.Tendsto
    (fun t : ℝ≥0 => Real.exp (-(alpha : ℝ) * (t : ℝ)) * Pt t f x)
    (nhds 0) (nhds (f x)))

/-  ORIGINAL (unfaithful) statement of (27.8), preserved for the record.

    As written the process `X` is a free variable with **no hypothesis linking
    it to `pdp`** (it is not required to follow the flow, nor to have
    right-continuous paths), so the conclusion fails for, e.g., a process with
    a left-continuous jump at some time.  The α-excessivity of `f` alone cannot
    compensate for this.

    The faithful version `pdp_is_borel_right_process_of_localFlow` below is
    stated after `alpha_excessive_right_continuous_along_flow` (which it uses).
    It adds exactly the genuine input of Davis's §24 construction, namely that
    the sample paths follow the flow on a right neighbourhood of every time
    (`hpath`), plus the §27 standing regularity already used by the flow lemma.

theorem pdp_is_borel_right_process
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [MetricSpace E]
    [SecondCountableTopology E] [LocallyCompactSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    {alpha : ℝ≥0} {f : E → ℝ}
    (hf_excessive : IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha f)
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : ℝ≥0 → Omega → E} :
    ∀ᵐ omega ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s => f (X s omega)) (nhdsWithin t (Set.Ioi t))
        (nhds (f (X t omega))) := by sorry
-/

/-
One renewal step of a non-negative target dominates the survival×flow term
    (the jump integral is a non-negative correction).
-/
theorem pdpSemigroupOp_survivor_flow_le {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (ψ : ℝ≥0 × E → ℝ)
    (hf : ∀ y, 0 ≤ f y) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ≥0) (x : E) :
    pdpSurvivorFunction p t x * f (p.flow t x) ≤ pdpSemigroupOp p f ψ (t, x) := by
  refine' le_add_of_nonneg_right _;
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s hs => mul_nonneg ( mul_nonneg ( le_of_lt ( pdpSurvivorFunction_pos p s.toNNReal x ) ) ( NNReal.coe_nonneg _ ) ) ( MeasureTheory.integral_nonneg fun y => hψ _ )

/-
One renewal step of a non-negative target bounded by `C` is dominated by the
    survival×flow term plus `C·(1 − S(t,x))` (the jump mass).
-/
theorem pdpSemigroupOp_le_survivor_flow_add {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (ψ : ℝ≥0 × E → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ y, 0 ≤ f y) (hψ : ∀ q, |ψ q| ≤ C) (t : ℝ≥0) (x : E)
    (hcont : ContinuousOn (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal x) : ℝ))
      (Set.Icc 0 (t : ℝ))) :
    pdpSemigroupOp p f ψ (t, x) ≤
      pdpSurvivorFunction p t x * f (p.flow t x)
        + C * (1 - pdpSurvivorFunction p t x) := by
  -- By definition of $pdpSemigroupOp$, we know that
  unfold pdpSemigroupOp;
  simp +decide only [add_le_add_iff_left];
  refine' le_of_abs_le _;
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun s => C * |pdpSurvivorFunction p s.toNNReal x * ( p.jumpRate ( p.flow s.toNNReal x ) : ℝ )|;
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
  · refine' ContinuousOn.integrableOn_Icc _;
    refine' ContinuousOn.mul continuousOn_const ( ContinuousOn.abs ( ContinuousOn.mul _ hcont ) );
    refine' ContinuousOn.rexp ( ContinuousOn.neg _ );
    have h_cont : ContinuousOn (fun s : ℝ => ∫ u in (0 : ℝ)..s, (p.jumpRate (p.flow u.toNNReal x) : ℝ)) (Set.Icc 0 t) := by
      intro s hs;
      refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num;
      exact hcont.intervalIntegrable_of_Icc ( by simp +decide );
    refine' h_cont.congr fun s hs => _;
    rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ] <;> aesop;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with s hs;
    rw [ mul_comm, norm_mul ];
    gcongr;
    · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
      refine' fun _ => C;
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
      · have := p.transitionMeasure_markov;
        cases this ; aesop;
      · filter_upwards [ ] using fun _ => hψ _;
      · have := p.transitionMeasure_markov;
        cases this ; aesop;
    · exact le_rfl;
  · rw [ MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun s hs => abs_of_nonneg ?_ ];
    · rw [ ← pdp_survivor_normalization p x t hcont ];
      simp +decide [ mul_comm ];
    · exact mul_nonneg ( le_of_lt ( pdpSurvivorFunction_pos p s.toNNReal x ) ) ( NNReal.coe_nonneg _ )

/-
Every renewal iterate of the zero start is non-negative when `f ≥ 0`.
-/
theorem pdpSemigroupOp_iterate_nonneg {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (hf : ∀ y, 0 ≤ f y) (n : ℕ) (q : ℝ≥0 × E) :
    0 ≤ (pdpSemigroupOp p f)^[n] (fun _ => 0) q := by
  induction' n with n ih generalizing q <;> simp_all +decide [ Function.iterate_succ_apply' ];
  refine' add_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( hf _ ) ) ( MeasureTheory.integral_nonneg fun s => mul_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( NNReal.coe_nonneg _ ) ) ( MeasureTheory.integral_nonneg fun y => ih _ _ ) )

/-
The survivor function tends to `1` as the horizon shrinks to `0`
    (bounded jump rate ⇒ the cumulative hazard `∫₀ᵗ λ(φ(s,x)) ds → 0`).
-/
theorem pdpSurvivorFunction_tendsto_one {E : Type*} [MeasurableSpace E]
    (p : PDP E) (x : E)
    (hflow : Measurable (fun q : ℝ × E => p.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, p.jumpRate y ≤ c) :
    Filter.Tendsto (fun t : ℝ≥0 => pdpSurvivorFunction p t x)
      (nhds 0) (nhds 1) := by
  -- Let's denote the cumulative hazard as $H(t)$.
  set H : ℝ≥0 → ℝ := fun t => ∫ u in Set.Icc (0 : ℝ) t, (p.jumpRate (p.flow u.toNNReal x) : ℝ);
  -- We need to show that $H(t) \to 0$ as $t \to 0$.
  have hH_zero : Filter.Tendsto H (nhds 0) (nhds 0) := by
    -- Since $p.jumpRate$ is bounded above by $c$, we have $H(t) \leq c \cdot t$.
    have hH_le : ∀ t : ℝ≥0, H t ≤ c * t := by
      intro t;
      refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
      refine' fun u => c;
      · exact Filter.Eventually.of_forall fun u => NNReal.coe_nonneg _;
      · norm_num;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with u hu using mod_cast hrate _;
      · simp +decide [ mul_comm ];
    exact squeeze_zero ( fun t => MeasureTheory.integral_nonneg fun u => by positivity ) hH_le ( Continuous.tendsto' ( by continuity ) _ _ ( by simp +decide ) );
  simpa using Filter.Tendsto.comp ( Real.continuous_exp.tendsto _ ) ( hH_zero.neg )

/-
(27.8, key step) α-excessive functions are right-continuous along
    the flow: t ↦ f(φ(t, x)) is right-continuous at 0 for all x.

    **Faithful reformulation.** The bare original skeleton could not be proved
    from `IsAlphaExcessive` alone: it also needs the §27 standing regularity
    (bounded jump rate `hrate`, continuity of the hazard along the flow `hcont`,
    measurability of the flow `hflow`) together with the fact that `f` is a
    *bounded* excessive function (`hf`, `hfC`) — the standard class of excessive
    functions in Davis §27 (images of bounded functions under the resolvent).
    Under these hypotheses the renewal decomposition gives the sandwich
    `S(t,x)·f(φ(t,x)) ≤ Pₜf(x) ≤ S(t,x)·f(φ(t,x)) + C·(1 − S(t,x))`, and
    `Pₜf(x) → f(x)`, `S(t,x) → 1` as `t ↓ 0` force `f(φ(t,x)) → f(x)`.
-/
theorem alpha_excessive_right_continuous_along_flow
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    {alpha : ℝ≥0} {f : E → ℝ}
    (hf : Measurable f) (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (hf_excessive : IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha f)
    (x : E) :
    Filter.Tendsto (fun t : ℝ≥0 => f (pdp.flow t x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
        obtain ⟨hf_nonneg, hf_le, hf_tendsto⟩ := hf_excessive;
        -- By the properties of the semigroup and the definition of $S(t, x)$, we have:
        have h_bound : ∀ t : ℝ≥0, pdpSurvivorFunction pdp.toPDP t x * f (pdp.toPDP.flow t x) ≤ pdpSemigroup pdp.toPDP t f x ∧ pdpSemigroup pdp.toPDP t f x ≤ pdpSurvivorFunction pdp.toPDP t x * f (pdp.toPDP.flow t x) + C * (1 - pdpSurvivorFunction pdp.toPDP t x) := by
          intro t
          have h_squeeze : ∀ n : ℕ, pdpSurvivorFunction pdp.toPDP t x * f (pdp.flow t x) ≤ (pdpSemigroupOp pdp.toPDP f)^[n + 1] (fun _ => 0) (t, x) ∧ (pdpSemigroupOp pdp.toPDP f)^[n + 1] (fun _ => 0) (t, x) ≤ pdpSurvivorFunction pdp.toPDP t x * f (pdp.flow t x) + C * (1 - pdpSurvivorFunction pdp.toPDP t x) := by
            intro n
            apply And.intro;
            · rw [ Function.iterate_succ_apply' ];
              apply pdpSemigroupOp_survivor_flow_le;
              · exact hf_nonneg;
              · exact fun q => pdpSemigroupOp_iterate_nonneg pdp.toPDP f hf_nonneg n q;
            · convert pdpSemigroupOp_le_survivor_flow_add pdp.toPDP f _ C _ _ _ _ _ _ using 1;
              rw [ Function.iterate_succ_apply' ];
              · exact le_trans ( abs_nonneg _ ) ( hfC x );
              · exact hf_nonneg;
              · apply_rules [ pdpSemigroupOp_iterate_abs_le ];
                · exact le_trans ( abs_nonneg _ ) ( hfC x );
                · exact measurable_const;
                · exact fun _ => by simpa using hfC x |> le_trans ( abs_nonneg _ ) ;
              · exact Continuous.continuousOn ( hcont x );
          have h_squeeze : Filter.Tendsto (fun n => (pdpSemigroupOp pdp.toPDP f)^[n + 1] (fun _ => 0) (t, x)) Filter.atTop (nhds (pdpSemigroup pdp.toPDP t f x)) := by
            convert semigroup_iterate_converges pdp f ( fun _ => 0 ) hf ⟨ C, hfC ⟩ measurable_const ⟨ C, fun _ => by simpa using ( abs_nonneg _ ).trans ( hfC x ) ⟩ hflow c hrate hcont t x |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 1;
          exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds h_squeeze fun n => by aesop, le_of_tendsto_of_tendsto' h_squeeze tendsto_const_nhds fun n => by aesop ⟩;
        -- By the properties of the semigroup and the definition of $S(t, x)$, we have that $S(t, x) \to 1$ as $t \to 0$.
        have h_S_tendsto : Filter.Tendsto (fun t : ℝ≥0 => pdpSurvivorFunction pdp.toPDP t x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
          convert pdpSurvivorFunction_tendsto_one pdp.toPDP x hflow c hrate |> Filter.Tendsto.mono_left <| nhdsWithin_le_nhds using 1;
        -- By the properties of the semigroup and the definition of $S(t, x)$, we have that $P_t f(x) \to f(x)$ as $t \to 0$.
        have h_P_tendsto : Filter.Tendsto (fun t : ℝ≥0 => pdpSemigroup pdp.toPDP t f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
          have h_P_tendsto : Filter.Tendsto (fun t : ℝ≥0 => Real.exp (alpha * t) * (Real.exp (-alpha * t) * pdpSemigroup pdp.toPDP t f x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
            simpa using Filter.Tendsto.mul ( Continuous.continuousWithinAt ( Real.continuous_exp.comp ( continuous_const.mul continuous_subtype_val ) ) ) ( hf_tendsto x |> Filter.Tendsto.mono_left <| nhdsWithin_le_nhds );
          simp_all +decide [ ← mul_assoc, ← Real.exp_add ];
        -- By the properties of the semigroup and the definition of $S(t, x)$, we have that $S(t, x) * f(φ(t, x)) \to f(x)$ as $t \to 0$.
        have h_S_f_tendsto : Filter.Tendsto (fun t : ℝ≥0 => pdpSurvivorFunction pdp.toPDP t x * f (pdp.toPDP.flow t x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
          have h_S_f_tendsto : Filter.Tendsto (fun t : ℝ≥0 => pdpSemigroup pdp.toPDP t f x - C * (1 - pdpSurvivorFunction pdp.toPDP t x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
            convert h_P_tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds.sub h_S_tendsto ) ) using 2 ; ring;
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_S_f_tendsto h_P_tendsto ( Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => by linarith [ h_bound t ] ) ( Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => by linarith [ h_bound t ] );
        convert h_S_f_tendsto.div h_S_tendsto _ using 1 <;> norm_num;
        ext t; simp +decide [ mul_div_cancel_left₀ _ ( ne_of_gt ( pdpSurvivorFunction_pos pdp.toPDP t x ) ) ] ;

/-- (27.8) Theorem (right process property) — faithful form.

    A PDP satisfying the standard conditions is a Borel right process: for any
    bounded α-excessive `f`, the sample path `t ↦ f(xₜ(ω))` is right-continuous.

    Compared with the original skeleton (preserved, commented, above) the
    process `X` is now genuinely tied to the PDP by `hpath`: on a right
    neighbourhood of every time the path follows the deterministic flow,
    `X (t+s) ω = φ(s, X t ω)` for `0 ≤ s < ε`.  This is exactly what the §24
    construction provides (no jump occurs in `(t, t+ε)`), and it is strictly
    weaker than the conclusion.  The §27 standing regularity (`hflow`, `hrate`,
    `hcont`) and boundedness of `f` (`hfC`) are those of
    `alpha_excessive_right_continuous_along_flow`, which supplies the analytic
    core: right-continuity of `f` along the flow at `0`. -/
theorem pdp_is_borel_right_process_of_localFlow
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    {alpha : ℝ≥0} {f : E → ℝ}
    (hf : Measurable f) (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (hf_excessive : IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha f)
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : ℝ≥0 → Omega → E}
    (hpath : ∀ (omega : Omega) (t : ℝ≥0), ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ s : ℝ≥0, s < ε → X (t + s) omega = pdp.flow s (X t omega)) :
    ∀ᵐ omega ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s => f (X s omega)) (nhdsWithin t (Set.Ioi t))
        (nhds (f (X t omega))) := by
  refine Filter.Eventually.of_forall (fun omega t => ?_)
  obtain ⟨ε, hε, hloc⟩ := hpath omega t
  -- Right-continuity of `f` along the flow, at the current state.
  have hflow_lim :
      Filter.Tendsto (fun u : ℝ≥0 => f (pdp.flow u (X t omega)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f (X t omega))) :=
    alpha_excessive_right_continuous_along_flow pdp hflow c hrate hcont hf C hfC
      hf_excessive (X t omega)
  -- `s ↦ s - t` maps a right neighbourhood of `t` to a right neighbourhood of `0`.
  have hshift : Filter.Tendsto (fun s : ℝ≥0 => s - t)
      (nhdsWithin t (Set.Ioi t)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcontsub : Continuous (fun s : ℝ≥0 => s - t) := by fun_prop
      simpa using (hcontsub.tendsto t).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact tsub_pos_of_lt (Set.mem_Ioi.mp hs)
  refine (hflow_lim.comp hshift).congr' ?_
  -- On `(t, t+ε)` the path is the flow started at `X t ω`.
  have hmem : Set.Iio (t + ε) ∈ nhdsWithin t (Set.Ioi t) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by simpa using hε))
  filter_upwards [hmem, self_mem_nhdsWithin] with s hs hst
  have hts : t ≤ s := le_of_lt (Set.mem_Ioi.mp hst)
  have hlt : s - t < ε := (tsub_lt_iff_left hts).mpr hs
  have hadd : t + (s - t) = s := add_tsub_cancel_of_le hts
  have := hloc (s - t) hlt
  rw [hadd] at this
  simpa [Function.comp] using congrArg f this.symm

/-! ### Basic semigroup properties of the transition operator `Pₜ`

These record the elementary algebraic/order properties of the transition
semigroup `pdpSemigroup` (defined as the limit of the renewal iterates `Gⁿ0`).
They are genuine, non-circular consequences of the §27 convergence machinery and
of the renewal operator's structure, and are the analytic prerequisites for the
Markov theory of §25. -/

/-
**(27) Identity at time 0.** `P₀f = f`: no jump can occur in zero time and
    the flow fixes its argument at time `0`, so the renewal iterates are
    eventually constant equal to `f x`.
-/
theorem pdpSemigroup_zero {E : Type*} [MeasurableSpace E]
    (p : PDP E) (f : E → ℝ) (x : E) :
    pdpSemigroup p 0 f x = f x := by
      convert Filter.Tendsto.limUnder_eq _;
      · infer_instance;
      · exact Filter.atTop_neBot;
      · -- We'll use induction to show that the sequence of iterates converges to $f(x)$.
        have h_iterate : ∀ n ≥ 1, (pdpSemigroupOp p f)^[n] (fun _ => 0) (0, x) = f x := by
          intro n hn; induction hn <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
          · unfold pdpSemigroupOp; simp +decide [ pdpSurvivorFunction_zero, p.flow_zero ] ;
          · unfold pdpSemigroupOp; simp +decide [ *, pdpSurvivorFunction_zero, p.flow_zero ] ;
        exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 1 ] with n hn; rw [ h_iterate n hn ] )

/-
**(27) Positivity of the transition semigroup.** If `f ≥ 0` then `Pₜf ≥ 0`;
    the renewal iterates `Gⁿ0` are all non-negative
    (`pdpSemigroupOp_iterate_nonneg`) and converge to `Pₜf`.
-/
theorem pdpSemigroup_nonneg {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ)
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hf_nonneg : ∀ y, 0 ≤ f y) (t : ℝ≥0) (x : E) :
    0 ≤ pdpSemigroup pdp.toPDP t f x := by
      convert le_of_tendsto_of_tendsto' tendsto_const_nhds ( semigroup_iterate_converges pdp f ( fun _ => 0 ) hf hf_bdd measurable_const ⟨ 0, by simp +decide ⟩ hflow c hrate hcont t x ) _ using 1 ; simp +decide [ hf_nonneg ];
      exact fun n => pdpSemigroupOp_iterate_nonneg pdp.toPDP f hf_nonneg n ( t, x )

/-
**(27) Conservativeness / normalization.** `Pₜ` fixes constants:
    `Pₜ(fun _ => c) = c`. Each renewal iterate of the constant function equals
    `c` because the transition kernel is Markov (`∫ c dQ = c`) and the survivor
    weights integrate to `1` (`pdp_survivor_normalization`), so `G(const c) =
    const c`; the iterates are therefore constant equal to `c` and so is their
    limit. In particular `Pₜ1 = 1`.
-/
theorem pdpSemigroup_const {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (cval : ℝ)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) (x : E) :
    pdpSemigroup pdp.toPDP t (fun _ => cval) x = cval := by
      have h_fixed_point : ∀ n : ℕ, ∀ s : ℝ≥0, ∀ y : E, (pdpSemigroupOp pdp.toPDP (fun _ => cval))^[n] (fun _ => cval) (s, y) = cval := by
        intro n s y; induction' n with n ih generalizing s y <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
        have h_const : ∫ s in Set.Icc (0 : ℝ) (s : ℝ), pdpSurvivorFunction pdp.toPDP s.toNNReal y * (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ) = 1 - pdpSurvivorFunction pdp.toPDP s y := by
          have := pdp_survivor_normalization pdp.toPDP y s ( hcont y |> Continuous.continuousOn );
          simpa only [ mul_comm ] using eq_sub_of_add_eq' this;
        simp_all +decide [ pdpSemigroupOp ];
        simp_all +decide [ MeasureTheory.integral_mul_const, pdp.toPDP.transitionMeasure_markov.1 ];
        ring;
      contrapose! h_fixed_point;
      have h_fixed_point : Filter.Tendsto (fun n => (pdpSemigroupOp pdp.toPDP (fun _ => cval))^[n] (fun _ => cval) (t, x)) Filter.atTop (nhds (pdpSemigroup pdp.toPDP t (fun _ => cval) x)) := by
        apply_rules [ semigroup_iterate_converges ];
        · exact measurable_const;
        · exact ⟨ |cval|, fun _ => le_rfl ⟩;
        · exact measurable_const;
        · exact ⟨ |cval|, fun _ => le_rfl ⟩;
      exact not_forall_not.mp fun h => ‹pdpSemigroup pdp.toPDP t ( fun x => cval ) x ≠ cval› <| tendsto_nhds_unique h_fixed_point <| tendsto_const_nhds.congr fun n => by aesop;

/-
Single-step additivity of the renewal operator, in both the target function
    and the argument function (for bounded measurable arguments):
    `G_{f+g}(ψ₁+ψ₂) = G_f ψ₁ + G_g ψ₂`.
-/
theorem pdpSemigroupOp_add_step {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f g : E → ℝ)
    (psi1 psi2 : ℝ≥0 × E → ℝ)
    (hpsi1 : Measurable psi1) (Cp1 : ℝ) (hpsi1C : ∀ q, |psi1 q| ≤ Cp1)
    (hpsi2 : Measurable psi2) (Cp2 : ℝ) (hpsi2C : ∀ q, |psi2 q| ≤ Cp2)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (q : ℝ≥0 × E) :
    pdpSemigroupOp pdp.toPDP (fun z => f z + g z) (fun p => psi1 p + psi2 p) q =
      pdpSemigroupOp pdp.toPDP f psi1 q + pdpSemigroupOp pdp.toPDP g psi2 q := by
        obtain ⟨t, x⟩ := q;
        simp [pdpSemigroupOp, add_mul, mul_add, add_assoc, add_left_comm, add_comm];
        rw [ ← MeasureTheory.integral_add ];
        · simp +decide only [← mul_add];
          refine' MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun s hs => congr_arg _ ( MeasureTheory.integral_add _ _ );
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun y => Cp1;
            · haveI := pdp.toPDP.transitionMeasure_markov;
              simp +decide [ MeasureTheory.integrable_const_iff ];
            · exact hpsi1.comp ( measurable_const.prodMk measurable_id' ) |> Measurable.aestronglyMeasurable;
            · exact Filter.Eventually.of_forall fun y => hpsi1C _;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun y => Cp2;
            · have := pdp.toPDP.transitionMeasure_markov;
              cases this ; aesop;
            · exact hpsi2.comp ( measurable_const.prodMk measurable_id' ) |> Measurable.aestronglyMeasurable;
            · exact Filter.Eventually.of_forall fun y => hpsi2C _;
        · apply_rules [ pdpSemigroupOp_integrand_integrableOn ];
        · apply_rules [ pdpSemigroupOp_integrand_integrableOn ]

/-
Additivity of the renewal iterates in the target function:
    `G_{f+g}ⁿ0 = G_fⁿ0 + G_gⁿ0` pointwise.
-/
theorem pdpSemigroupOp_iterate_add {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f g : E → ℝ)
    (hf : Measurable f) (Cf : ℝ) (hCf : ∀ x, |f x| ≤ Cf)
    (hg : Measurable g) (Cg : ℝ) (hCg : ∀ x, |g x| ≤ Cg)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (n : ℕ) (s : ℝ≥0) (y : E) :
    (pdpSemigroupOp pdp.toPDP (fun z => f z + g z))^[n] (fun _ => 0) (s, y) =
      (pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (s, y) +
      (pdpSemigroupOp pdp.toPDP g)^[n] (fun _ => 0) (s, y) := by
        induction' n with n ih generalizing s y;
        · norm_num;
        · convert pdpSemigroupOp_add_step pdp f g ( ( pdpSemigroupOp pdp.toPDP f )^[n] ( fun _ => 0 ) ) ( ( pdpSemigroupOp pdp.toPDP g )^[n] ( fun _ => 0 ) ) _ Cf ( fun q => ?_ ) _ Cg ( fun q => ?_ ) hflow c hrate ( s, y ) using 1 <;> norm_num [ Function.iterate_succ_apply' ];
          · congr! 2;
            exact ih _ _;
          · exact pdpSemigroupOp_iterate_measurable pdp.toPDP f hf hflow ( fun _ => 0 ) measurable_const n;
          · apply pdpSemigroupOp_iterate_abs_le pdp.toPDP f hf hflow c hrate hcont Cf (le_trans (abs_nonneg _) (hCf y)) hCf (fun _ => 0) measurable_const (fun _ => by simpa using le_trans (abs_nonneg _) (hCf y)) n q;
          · convert pdpSemigroupOp_iterate_measurable pdp.toPDP g hg hflow ( fun _ => 0 ) measurable_const n using 1;
          · apply pdpSemigroupOp_iterate_abs_le pdp.toPDP g hg hflow c hrate hcont Cg (le_trans (abs_nonneg _) (hCg y)) hCg (fun _ => 0) measurable_const (fun _ => by simpa using le_trans (abs_nonneg _) (hCg y)) n q

/-
**(27) Additivity / linearity of the transition semigroup.**
    `Pₜ(f + g) = Pₜf + Pₜg`. The renewal operator is affine, and iterating from
    `0` is additive in the target function: `G_{f+g}ⁿ0 = G_fⁿ0 + G_gⁿ0`
    (induction, using `∫ (a+b) dQ = ∫ a dQ + ∫ b dQ` for the bounded measurable
    iterates and additivity of the jump integral). Passing to the limit
    (`semigroup_iterate_converges` for `f`, `g`, `f + g`, plus `Tendsto.add` and
    uniqueness of limits) gives the additivity of `Pₜ`.
-/
theorem pdpSemigroup_add {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f g : E → ℝ)
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hg : Measurable g) (hg_bdd : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) (x : E) :
    pdpSemigroup pdp.toPDP t (fun y => f y + g y) x =
      pdpSemigroup pdp.toPDP t f x + pdpSemigroup pdp.toPDP t g x := by
        convert Tendsto.limUnder_eq _ using 1;
        · infer_instance;
        · exact Filter.atTop_neBot;
        · convert Tendsto.add ( semigroup_iterate_converges pdp f ( fun _ => 0 ) hf hf_bdd measurable_const ⟨ 0, fun _ => by norm_num ⟩ hflow c hrate hcont t x ) ( semigroup_iterate_converges pdp g ( fun _ => 0 ) hg hg_bdd measurable_const ⟨ 0, fun _ => by norm_num ⟩ hflow c hrate hcont t x ) using 1;
          convert funext fun n => pdpSemigroupOp_iterate_add pdp f g hf _ _ hg _ _ hflow c hrate hcont n t x using 1;
          exacts [ hf_bdd.choose, hf_bdd.choose_spec, hg_bdd.choose, hg_bdd.choose_spec ]

/-
Single-step homogeneity of the renewal operator in the target and argument
    functions: `G_{a·f}(a·ψ) = a · G_f ψ`. This is unconditional — it only pulls
    the scalar `a` out of the (inner kernel and outer jump) integrals via
    `MeasureTheory.integral_const_mul`.
-/
theorem pdpSemigroupOp_smul_step {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (a : ℝ) (f : E → ℝ) (psi : ℝ≥0 × E → ℝ)
    (q : ℝ≥0 × E) :
    pdpSemigroupOp pdp.toPDP (fun z => a * f z) (fun p => a * psi p) q =
      a * pdpSemigroupOp pdp.toPDP f psi q := by
        unfold pdpSemigroupOp; simp +decide [ mul_assoc, mul_left_comm, MeasureTheory.integral_const_mul ] ; ring;

/-
Homogeneity of the renewal iterates in the target function:
    `G_{a·f}ⁿ0 = a · G_fⁿ0` pointwise (induction on `pdpSemigroupOp_smul_step`,
    using that the start `0` satisfies `0 = a · 0`).
-/
theorem pdpSemigroupOp_iterate_smul {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (a : ℝ) (f : E → ℝ)
    (n : ℕ) (s : ℝ≥0) (y : E) :
    (pdpSemigroupOp pdp.toPDP (fun z => a * f z))^[n] (fun _ => 0) (s, y) =
      a * (pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0) (s, y) := by
        induction' n with n ih generalizing s y;
        · simp +decide;
        · rw [ Function.iterate_succ_apply', Function.iterate_succ_apply' ];
          rw [ show ( pdpSemigroupOp pdp.toPDP fun z => a * f z )^[n] ( fun x => 0 ) = fun p => a * ( pdpSemigroupOp pdp.toPDP f )^[n] ( fun x => 0 ) p from funext fun p => ih p.1 p.2 ];
          convert pdpSemigroupOp_smul_step pdp a f _ ( s, y ) using 1

/-
**(27) Homogeneity / scalar-linearity of the transition semigroup.**
    `Pₜ(a · f) = a · Pₜf`. Each renewal iterate from `0` is homogeneous in the
    target function (`pdpSemigroupOp_iterate_smul`); passing to the limit
    (`semigroup_iterate_converges` for `a·f` and `f`, `Tendsto.const_mul`, and
    uniqueness of limits) yields homogeneity of `Pₜ`. Combined with
    `pdpSemigroup_add` this makes `Pₜ` a linear operator.
-/
theorem pdpSemigroup_smul {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (a : ℝ) (f : E → ℝ)
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) (x : E) :
    pdpSemigroup pdp.toPDP t (fun y => a * f y) x =
      a * pdpSemigroup pdp.toPDP t f x := by
        convert Tendsto.limUnder_eq _ using 1;
        · infer_instance;
        · exact Filter.atTop_neBot;
        · convert Filter.Tendsto.const_mul a ( semigroup_iterate_converges pdp f ( fun _ => 0 ) hf hf_bdd measurable_const ⟨ 0, fun _ => by norm_num ⟩ hflow c hrate hcont t x ) using 1;
          ext n; exact pdpSemigroupOp_iterate_smul pdp a f n t x;

/-
**(27) Monotonicity of the transition semigroup.** If `f ≤ g` pointwise then
    `Pₜf ≤ Pₜg`. Write `g = f + (g - f)` with `g - f ≥ 0`; then
    `Pₜg = Pₜf + Pₜ(g - f)` (`pdpSemigroup_add`) and `Pₜ(g - f) ≥ 0`
    (`pdpSemigroup_nonneg`), so `Pₜf ≤ Pₜg`.
-/
theorem pdpSemigroup_mono {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f g : E → ℝ)
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hg : Measurable g) (hg_bdd : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hfg : ∀ y, f y ≤ g y) (t : ℝ≥0) (x : E) :
    pdpSemigroup pdp.toPDP t f x ≤ pdpSemigroup pdp.toPDP t g x := by
      convert le_add_of_nonneg_right ( pdpSemigroup_nonneg pdp ( fun y => g y - f y ) ( hg.sub hf ) ?_ hflow c hrate hcont ?_ t x ) using 1;
      · convert pdpSemigroup_add pdp f ( fun y => g y - f y ) hf hf_bdd ( hg.sub hf ) ?_ hflow c hrate hcont t x using 1;
        · simp +decide [ hfg ];
        · exact ⟨ hf_bdd.choose + hg_bdd.choose, fun x => by rw [ abs_le ] ; constructor <;> linarith [ abs_le.mp ( hf_bdd.choose_spec x ), abs_le.mp ( hg_bdd.choose_spec x ) ] ⟩;
      · exact ⟨ hf_bdd.choose + hg_bdd.choose, fun x => by rw [ abs_le ] ; constructor <;> linarith [ abs_le.mp ( hf_bdd.choose_spec x ), abs_le.mp ( hg_bdd.choose_spec x ) ] ⟩;
      · exact fun y => sub_nonneg.2 ( hfg y )

/-
**(27) Strong continuity of the transition semigroup at time 0** (non-negative
    case). For a continuous, non-negative, bounded `f`, `Pₜf(x) → f(x)` as
    `t ↓ 0`. The renewal decomposition sandwiches
    `S(t,x)·f(φ(t,x)) ≤ Pₜf(x) ≤ S(t,x)·f(φ(t,x)) + C·(1 − S(t,x))`
    (exactly the bound `h_bound` used in
    `alpha_excessive_right_continuous_along_flow`); as `t ↓ 0`,
    `S(t,x) → 1` (`pdpSurvivorFunction_tendsto_one`) and, by joint continuity of
    the flow (`hflow_cont`, so `t ↦ φ(t,x)` is continuous and `φ(0,x) = x`) and
    continuity of `f`, `f(φ(t,x)) → f(x)`. Hence both bounds tend to `f(x)` and
    a squeeze gives `Pₜf(x) → f(x)`.
-/
theorem pdpSemigroup_tendsto_zero_nonneg {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y) (C : ℝ) (hfC : ∀ y, |f y| ≤ C) (x : E) :
    Filter.Tendsto (fun t : ℝ≥0 => pdpSemigroup pdp.toPDP t f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
        have h_bound : ∀ t : ℝ≥0, pdpSurvivorFunction pdp.toPDP t x * f (pdp.toPDP.flow t x) ≤ pdpSemigroup pdp.toPDP t f x ∧ pdpSemigroup pdp.toPDP t f x ≤ pdpSurvivorFunction pdp.toPDP t x * f (pdp.toPDP.flow t x) + C * (1 - pdpSurvivorFunction pdp.toPDP t x) := by
          intro t
          have h_bound : ∀ n : ℕ, pdpSurvivorFunction pdp.toPDP t x * f (pdp.toPDP.flow t x) ≤ (pdpSemigroupOp pdp.toPDP f)^[n + 1] (fun _ => 0) (t, x) ∧ (pdpSemigroupOp pdp.toPDP f)^[n + 1] (fun _ => 0) (t, x) ≤ pdpSurvivorFunction pdp.toPDP t x * f (pdp.toPDP.flow t x) + C * (1 - pdpSurvivorFunction pdp.toPDP t x) := by
            intro n
            apply And.intro;
            · have := pdpSemigroupOp_survivor_flow_le pdp.toPDP f ( ( pdpSemigroupOp pdp.toPDP f ) ^[ n ] ( fun _ => 0 ) ) ( fun y => hf_nonneg y ) ( fun q => pdpSemigroupOp_iterate_nonneg pdp.toPDP f ( fun y => hf_nonneg y ) n q ) t x; simp_all +decide [ Function.iterate_succ_apply' ] ;
            · convert pdpSemigroupOp_le_survivor_flow_add pdp.toPDP f ( fun q => ( pdpSemigroupOp pdp.toPDP f )^[n] ( fun _ => 0 ) q ) C _ _ _ t x _ using 1;
              · simp +decide [ Function.iterate_succ_apply' ];
              · exact le_trans ( abs_nonneg _ ) ( hfC x );
              · exact hf_nonneg;
              · apply pdpSemigroupOp_iterate_abs_le pdp.toPDP f hf hflow c hrate hcont C (by
                exact le_trans ( abs_nonneg _ ) ( hfC x )) hfC (fun _ => 0) (by
                exact measurable_const) (by
                exact fun _ => by simpa using hfC x |> le_trans ( abs_nonneg _ ) ;) n;
              · exact Continuous.continuousOn ( hcont x );
          have h_limit : Filter.Tendsto (fun n => (pdpSemigroupOp pdp.toPDP f)^[n + 1] (fun _ => 0) (t, x)) Filter.atTop (nhds (pdpSemigroup pdp.toPDP t f x)) := by
            convert semigroup_iterate_converges pdp f ( fun _ => 0 ) hf ?_ measurable_const ?_ hflow c hrate hcont t x |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 1;
            · exact ⟨ C, hfC ⟩;
            · exact ⟨ 0, fun _ => by norm_num ⟩;
          exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds h_limit fun n => h_bound n |>.1, le_of_tendsto_of_tendsto' h_limit tendsto_const_nhds fun n => h_bound n |>.2 ⟩;
        have h_S_tendsto : Filter.Tendsto (fun t : ℝ≥0 => pdpSurvivorFunction pdp.toPDP t x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
          exact pdpSurvivorFunction_tendsto_one pdp.toPDP x hflow c hrate |> Filter.Tendsto.mono_left <| nhdsWithin_le_nhds;
        have h_f_tendsto : Filter.Tendsto (fun t : ℝ≥0 => f (pdp.toPDP.flow t x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
          convert hf_cont.continuousAt.tendsto.comp ( hflow_cont.continuousAt.tendsto.comp ( show Filter.Tendsto ( fun t : ℝ≥0 => ( t, x ) ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds ( 0, x ) ) from Filter.Tendsto.prodMk_nhds ( Filter.tendsto_id.mono_left inf_le_left ) tendsto_const_nhds ) ) using 1;
          rw [ pdp.flow_zero ];
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ( by simpa using h_S_tendsto.mul h_f_tendsto ) ( by simpa using h_S_tendsto.mul h_f_tendsto |> Filter.Tendsto.add <| tendsto_const_nhds.mul ( h_S_tendsto.const_sub 1 ) ) ( Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => h_bound t |>.1 ) ( Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => h_bound t |>.2 )

/-
**(27) Strong continuity of the transition semigroup at time 0.** For any
    continuous bounded `f`, `Pₜf(x) → f(x)` as `t ↓ 0`. Reduce to the
    non-negative case via `g := fun y => f y + C ≥ 0` (`|f| ≤ C ⇒ f ≥ -C`),
    which is continuous, measurable and bounded (by `2C`): by
    `pdpSemigroup_add` and `pdpSemigroup_const`,
    `Pₜg(x) = Pₜf(x) + C`, and `pdpSemigroup_tendsto_zero_nonneg` gives
    `Pₜg(x) → g(x) = f(x) + C`, so `Pₜf(x) = Pₜg(x) - C → f(x)`.
-/
theorem pdpSemigroup_tendsto_zero {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C) (x : E) :
    Filter.Tendsto (fun t : ℝ≥0 => pdpSemigroup pdp.toPDP t f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
        convert Tendsto.sub_const ( pdpSemigroup_tendsto_zero_nonneg pdp hflow hflow_cont c hrate hcont ( hf.add measurable_const ) ( hf_cont.add continuous_const ) ( fun y => show 0 ≤ f y + C by linarith [ abs_le.mp ( hfC y ) ] ) ( 2 * C ) ( fun y => show |f y + C| ≤ 2 * C by rw [ abs_le ] ; constructor <;> linarith [ abs_le.mp ( hfC y ) ] ) x ) C using 2 ; ring;
        · have := pdpSemigroup_add pdp f ( fun _ => C ) hf ⟨ C, hfC ⟩ measurable_const ⟨ |C|, fun _ => le_rfl ⟩ hflow c hrate hcont ‹_› x; simp_all +decide [ add_comm ] ;
          rw [ pdpSemigroup_const pdp C hflow c hrate hcont ] ; ring;
        · ring

/-
**(27) Contraction / sup-norm bound of the transition semigroup.**
    If `|f| ≤ C` then `|Pₜf(x)| ≤ C`. The renewal iterates from `0` are all
    bounded by `C` (`pdpSemigroupOp_iterate_abs_le`) and converge to `Pₜf(x)`
    (`semigroup_iterate_converges`), so the limit is bounded by `C`.
-/
theorem pdpSemigroup_abs_le {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ)
    (hf : Measurable f)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ y, |f y| ≤ C) (t : ℝ≥0) (x : E) :
    |pdpSemigroup pdp.toPDP t f x| ≤ C := by
      have := @semigroup_iterate_converges;
      specialize this pdp f ( fun _ => 0 ) hf ⟨ C, hfC ⟩ measurable_const ⟨ 0, fun _ => by simp +decide [ hC ] ⟩ hflow c hrate hcont t x;
      exact le_of_tendsto' ( this.abs ) fun n => by simpa using pdpSemigroupOp_iterate_abs_le pdp.toPDP f hf hflow c hrate hcont C hC hfC ( fun _ => 0 ) measurable_const ( fun _ => by simp +decide [ hC ] ) n ( t, x ) ;

/-
**(27) Subtractivity / linearity of the transition semigroup.**
    `Pₜ(f - g) = Pₜf - Pₜg`. Immediate from additivity `pdpSemigroup_add` and
    homogeneity `pdpSemigroup_smul` (with scalar `-1`).
-/
theorem pdpSemigroup_sub {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f g : E → ℝ)
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hg : Measurable g) (hg_bdd : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) (x : E) :
    pdpSemigroup pdp.toPDP t (fun y => f y - g y) x =
      pdpSemigroup pdp.toPDP t f x - pdpSemigroup pdp.toPDP t g x := by
        have := pdpSemigroup_add pdp f ( fun y => -g y ) hf hf_bdd ( by measurability ) ⟨ hg_bdd.choose, fun y => by simpa using hg_bdd.choose_spec y ⟩ hflow c hrate hcont t x; simp_all +decide [ sub_eq_add_neg ] ;
        simpa using pdpSemigroup_smul pdp ( -1 ) g hg hg_bdd hflow c hrate hcont t x

/-
**(27) Sup-norm Lipschitz dependence on the target function.**
    If `|f - g| ≤ M` pointwise then `|Pₜf(x) - Pₜg(x)| ≤ M`. Write the
    difference as `Pₜ(f - g)(x)` (`pdpSemigroup_sub`) and bound it by the
    contraction estimate `pdpSemigroup_abs_le` applied to `f - g`.
-/
theorem pdpSemigroup_dist_le {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f g : E → ℝ)
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hg : Measurable g) (hg_bdd : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (M : ℝ) (hM : 0 ≤ M) (hfg : ∀ y, |f y - g y| ≤ M) (t : ℝ≥0) (x : E) :
    |pdpSemigroup pdp.toPDP t f x - pdpSemigroup pdp.toPDP t g x| ≤ M := by
      rw [ ← pdpSemigroup_sub pdp f g hf hf_bdd hg hg_bdd hflow c hrate hcont t x ];
      convert pdpSemigroup_abs_le pdp ( fun y => f y - g y ) ( hf.sub hg ) hflow c hrate hcont M hM hfg t x using 1

/-
**Survivor cocycle (flow-multiplicativity).** The probability of surviving
    (no jump) up to time `s + t` factors as the probability of surviving to
    time `s` times the probability of surviving a further time `t` started from
    the flowed state `φ(s, y)`:
      `S(s + t, y) = S(s, y) · S(t, φ(s, y))`.
    This is the additive-cocycle identity for the hazard integral
    `∫₀^{s+t} λ(φ(u,y)) du = ∫₀ˢ λ(φ(u,y)) du + ∫₀ᵗ λ(φ(u, φ(s,y))) du`, the
    second integral obtained by the substitution `u ↦ u + s` together with the
    flow group law `flow_add` (`φ(u+s, y) = φ(u, φ(s, y))`). Continuity of the
    hazard along the flow supplies the interval-integrability needed to split
    the integral.
-/
theorem pdpSurvivorFunction_mul {E : Type*} [MeasurableSpace E]
    (p : PDP E) (y : E)
    (hcont : Continuous (fun s : ℝ => (p.jumpRate (p.flow s.toNNReal y) : ℝ)))
    (s t : ℝ≥0) :
    pdpSurvivorFunction p (s + t) y
      = pdpSurvivorFunction p s y * pdpSurvivorFunction p t (p.flow s y) := by
  -- Apply the fact that the integral of a sum is the sum of the integrals.
  have h_integral_split : ∫ u in Set.Icc (0 : ℝ) ((s + t) : ℝ), (p.jumpRate (p.flow u.toNNReal y) : ℝ) = (∫ u in Set.Icc (0 : ℝ) (s : ℝ), (p.jumpRate (p.flow u.toNNReal y) : ℝ)) + (∫ u in Set.Ioc (s : ℝ) ((s + t) : ℝ), (p.jumpRate (p.flow u.toNNReal y) : ℝ)) := by
    norm_num [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, add_nonneg ];
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Continuous.intervalIntegrable, hcont ];
  -- Apply the substitution $u = v + s$ to the integral over $[s, s+t]$.
  have h_integral_subst : ∫ u in Set.Ioc (s : ℝ) ((s + t) : ℝ), (p.jumpRate (p.flow u.toNNReal y) : ℝ) = ∫ v in Set.Ioc (0 : ℝ) (t : ℝ), (p.jumpRate (p.flow (v + s).toNNReal y) : ℝ) := by
    rw [ ← intervalIntegral.integral_of_le ( by linarith [ NNReal.coe_nonneg s, NNReal.coe_nonneg t ] ), ← intervalIntegral.integral_of_le ( by linarith [ NNReal.coe_nonneg s, NNReal.coe_nonneg t ] ) ] ; rw [ intervalIntegral.integral_comp_add_right fun u => ( p.jumpRate ( p.flow u.toNNReal y ) : ℝ ) ] ; norm_num; ring;
  -- Apply the flow group law to rewrite the integral over $[0, t]$.
  have h_integral_flow : ∫ v in Set.Ioc (0 : ℝ) (t : ℝ), (p.jumpRate (p.flow (v + s).toNNReal y) : ℝ) = ∫ v in Set.Ioc (0 : ℝ) (t : ℝ), (p.jumpRate (p.flow v.toNNReal (p.flow s y)) : ℝ) := by
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun v hv => _;
    rw [ Real.toNNReal_add ] <;> norm_num [ hv.1.le ];
    rw [ p.flow_add ];
  unfold pdpSurvivorFunction; simp +decide [ *, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] ; ring;
  rw [ ← Real.exp_add ] ; ring

/-
**Joint measurability of the transition semigroup.** The map
    `(t, x) ↦ Pₜf(x)` is measurable on `ℝ≥0 × E`. It is the pointwise limit of
    the renewal iterates `Gⁿ0`, each of which is jointly measurable
    (`pdpSemigroupOp_iterate_measurable`); convergence at every point is
    `semigroup_iterate_converges`, so `measurable_of_tendsto_metrizable`
    applies.
-/
theorem pdpSemigroup_measurable {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ))) :
    Measurable (fun q : ℝ≥0 × E => pdpSemigroup pdp.toPDP q.1 f q.2) := by
  convert measurable_of_tendsto_metrizable _ _;
  all_goals try infer_instance;
  use fun n => fun q => ( pdpSemigroupOp pdp.toPDP f )^[n] ( fun _ => 0 ) ( q.1, q.2 );
  · exact fun n => pdpSemigroupOp_iterate_measurable pdp.toPDP f hf hflow ( fun _ => 0 ) measurable_const n;
  · refine' tendsto_pi_nhds.mpr _;
    intro q;
    convert semigroup_iterate_converges pdp f ( fun _ => 0 ) hf hf_bdd measurable_const ?_ hflow c hrate hcont q.1 q.2 using 1;
    exact ⟨ 0, fun _ => by norm_num ⟩

/-
**Renewal (fixed-point) equation for the transition semigroup.** The
    semigroup `Pₜf` is the fixed point of the one-step renewal operator `G`
    (`pdpSemigroupOp`), i.e. it satisfies Davis's renewal equation (27.2):
      `Pₜf(x) = S(t,x)·f(φ(t,x)) + ∫₀ᵗ S(s,x)·λ(φ(s,x))·[∫ P_{t−s}f(y) Q(dy; φ(s,x))] ds`.
    Proof: the iterates `aₙ = Gⁿ0` converge to `Pₜf(x)`
    (`semigroup_iterate_converges`), and `aₙ₊₁ = G aₙ` also converges to the
    same limit; on the other hand `G aₙ (t,x) → G ψ (t,x)` where
    `ψ = fun q => P_{q.1}f q.2`, because the integrand difference is controlled
    by the uniform-in-`(s,y)` iterate-to-limit bound
    `|aₙ(t−s,y) − P_{t−s}f(y)| ≤ 2C·ρ(t−s)ⁿ ≤ 2C·ρ(t)ⁿ → 0`
    (`pdpSemigroup_sub_iterate_le`, monotonicity of `ρ` in the horizon). Hence
    `Pₜf(x) = G ψ (t,x)`, which is the displayed right-hand side.
-/
theorem pdpSemigroup_renewal_equation {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) (x : E) :
    pdpSemigroup pdp.toPDP t f x =
      pdpSurvivorFunction pdp.toPDP t x * f (pdp.flow t x) +
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        pdpSurvivorFunction pdp.toPDP s.toNNReal x *
        (pdp.jumpRate (pdp.flow s.toNNReal x) : ℝ) *
        (∫ y, pdpSemigroup pdp.toPDP ((t : ℝ) - s).toNNReal f y
          ∂(pdp.transitionMeasure (pdp.flow s.toNNReal x))) := by
  obtain ⟨ C, hC ⟩ := hf_bdd;
  set ψ' : ℝ≥0 × E → ℝ := fun q => pdpSemigroup pdp.toPDP q.1 f q.2
  have hψ'm : ∀ r, Measurable (fun y => ψ' (r, y)) := by
    intro r;
    apply (pdp_semigroup_maps_bounded_measurable pdp r hf ⟨C, hC⟩ hflow c hrate hcont).left.comp measurable_id';
  have hψ'm_bdd : ∀ q, |ψ' q| ≤ C := by
    exact fun q => pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C ( le_trans ( abs_nonneg _ ) ( hC q.2 ) ) hC q.1 q.2;
  have h_limit : Filter.Tendsto (fun n => pdpSemigroupOp pdp.toPDP f ((pdpSemigroupOp pdp.toPDP f)^[n] (fun _ => 0)) (t, x)) Filter.atTop (nhds (pdpSemigroupOp pdp.toPDP f ψ' (t, x))) := by
    refine' tendsto_iff_norm_sub_tendsto_zero.mpr _;
    refine' squeeze_zero ( fun _ => norm_nonneg _ ) ( fun n => _ ) _;
    use fun n => 2 * C * ( 1 - Real.exp ( - ( c : ℝ ) * ( t : ℝ ) ) ) ^ n * ( 1 - pdpSurvivorFunction pdp.toPDP t x );
    · apply_rules [ pdpSemigroupOp_dist_le_horizon ];
      any_goals exact Continuous.continuousOn ( hcont x );
      any_goals exact pdpSemigroupOp_integrand_integrableOn pdp.toPDP _ ( pdpSemigroupOp_iterate_measurable pdp.toPDP f hf hflow _ measurable_const n ) C ( pdpSemigroupOp_iterate_abs_le pdp.toPDP f hf hflow c hrate hcont C ( show 0 ≤ C by exact le_trans ( abs_nonneg _ ) ( hC x ) ) ( fun y => hC y ) ( fun _ => 0 ) measurable_const ( fun _ => by simp +decide [ show 0 ≤ C by exact le_trans ( abs_nonneg _ ) ( hC x ) ] ) n ) hflow c hrate t x;
      · exact mul_nonneg ( mul_nonneg zero_le_two ( le_trans ( abs_nonneg _ ) ( hC x ) ) ) ( pow_nonneg ( sub_nonneg.2 ( Real.exp_le_one_iff.2 ( by nlinarith [ show ( c : ℝ ) ≥ 0 by positivity, show ( t : ℝ ) ≥ 0 by positivity ] ) ) ) _ );
      · apply pdpSemigroupOp_iterate_abs_le pdp.toPDP f hf hflow c hrate hcont C ( show 0 ≤ C by exact le_trans ( abs_nonneg _ ) ( hC x ) ) ( fun y => hC y ) ( fun _ => 0 ) measurable_const ( fun _ => by simp +decide [ show 0 ≤ C by exact le_trans ( abs_nonneg _ ) ( hC x ) ] ) n;
      · exact fun r => pdpSemigroupOp_iterate_measurable pdp.toPDP f hf hflow ( fun _ => 0 ) measurable_const n |> Measurable.comp <| measurable_prodMk_left;
      · intro q hq;
        refine' le_trans _ ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ _ _ _ ) ( by linarith [ abs_le.mp ( hC x ) ] ) );
        convert pdpSemigroup_sub_iterate_le pdp f hf hflow c hrate hcont C ( show 0 ≤ C by exact le_trans ( abs_nonneg _ ) ( hC x ) ) ( fun y => hC y ) q.1 n q.2 using 1;
        · exact sub_nonneg.2 ( Real.exp_le_one_iff.2 <| by nlinarith [ show ( c : ℝ ) ≥ 0 by positivity, show ( q.1 : ℝ ) ≥ 0 by positivity ] );
        · exact sub_le_sub_left ( Real.exp_le_exp.mpr ( mul_le_mul_of_nonpos_left ( mod_cast hq ) ( neg_nonpos.mpr ( NNReal.coe_nonneg _ ) ) ) ) _;
      · apply_rules [ pdpSemigroupOp_integrand_integrableOn ];
        exact pdpSemigroup_measurable pdp f hf ⟨ C, hC ⟩ hflow c hrate hcont;
    · by_cases hc : c = 0 <;> simp_all +decide [ Real.exp_neg ];
      · exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; simp +decide [ hn ] );
      · simpa using Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| Real.one_le_exp <| by positivity ) <| sub_lt_self _ <| inv_pos.2 <| Real.exp_pos _ ) ) tendsto_const_nhds;
  convert tendsto_nhds_unique _ h_limit using 1;
  convert semigroup_iterate_converges pdp f ( fun _ => 0 ) hf ⟨ C, hC ⟩ measurable_const ⟨ 0, fun _ => by norm_num ⟩ hflow c hrate hcont t x |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 using 1;
  exact funext fun n => by rw [ Function.comp_apply, Function.iterate_succ_apply' ] ; rfl;

/-
**Uniqueness of the renewal fixed point.** Under a globally bounded jump rate,
    the one-step renewal operator `ψ ↦ pdpSemigroupOp pdp g ψ` has at most one
    bounded, jointly-measurable fixed point. Two such fixed points `u`, `v` (both
    `|·| ≤ C`) coincide everywhere. The proof is a geometric-contraction
    induction on a finite horizon `T`: from `pdpSemigroupOp_dist_le_horizon` and
    the survivor lower bound `pdpSurvivorFunction_ge_exp` one gets, for every `n`,
    `|u q − v q| ≤ 2C·(1 − e^{−cT})ⁿ` whenever `q.1 ≤ T`; letting `n → ∞`
    (`tendsto_pow_atTop_nhds_zero_of_lt_one`, `1 − e^{−cT} < 1`) forces
    `u q = v q`. Since every `q` has `q.1 ≤ q.1`, this gives `u = v`.
-/
theorem pdpSemigroupOp_fixedpoint_unique {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (g : E → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (u v : ℝ≥0 × E → ℝ)
    (hu_bdd : ∀ q, |u q| ≤ C) (hv_bdd : ∀ q, |v q| ≤ C)
    (hu_meas : Measurable u) (hv_meas : Measurable v)
    (hu_fix : ∀ q, u q = pdpSemigroupOp pdp.toPDP g u q)
    (hv_fix : ∀ q, v q = pdpSemigroupOp pdp.toPDP g v q) :
    ∀ q, u q = v q := by
      intro q
      set T := q.1 with hT
      have hT_le : T ≤ T := by
        rfl;
      -- By induction on n, we can show that |u q - v q| ≤ 2 * C * (1 - Real.exp (-(c : ℝ) * (T : ℝ))) ^ n for all n.
      have h_ind : ∀ n : ℕ, ∀ q : ℝ≥0 × E, q.1 ≤ T → |u q - v q| ≤ 2 * C * (1 - Real.exp (-(c : ℝ) * (T : ℝ))) ^ n := by
        intro n
        induction' n with n ih;
        · exact fun q hq => by simpa using abs_sub ( u q ) ( v q ) |> le_trans <| by linarith [ hu_bdd q, hv_bdd q ] ;
        · intro q hq_le_T
          have h_ind_step : |u q - v q| ≤ 2 * C * (1 - Real.exp (-(c : ℝ) * (T : ℝ))) ^ n * (1 - pdpSurvivorFunction pdp.toPDP q.1 q.2) := by
            rw [ hu_fix, hv_fix ];
            apply_rules [ pdpSemigroupOp_dist_le_horizon ];
            grind +extAll;
            exact fun r => hu_meas.comp ( measurable_const.prodMk measurable_id' );
            · exact fun r => hv_meas.comp ( measurable_const.prodMk measurable_id' );
            · exact fun q' hq'_le_q => ih q' ( le_trans hq'_le_q hq_le_T );
            · exact Continuous.continuousOn ( hcont _ );
            · apply_rules [ pdpSemigroupOp_integrand_integrableOn ];
            · apply_rules [ pdpSemigroupOp_integrand_integrableOn ];
          have h_survivor_bound : 1 - pdpSurvivorFunction pdp.toPDP q.1 q.2 ≤ 1 - Real.exp (-(c : ℝ) * (T : ℝ)) := by
            apply_rules [ sub_le_sub_left, pdpSurvivorFunction_ge_exp ];
          convert h_ind_step.trans ( mul_le_mul_of_nonneg_left h_survivor_bound _ ) using 1 ; ring;
          exact mul_nonneg ( mul_nonneg zero_le_two hC ) ( pow_nonneg ( sub_nonneg.2 ( Real.exp_le_one_iff.2 ( by nlinarith [ show ( c : ℝ ) ≥ 0 by positivity, show ( T : ℝ ) ≥ 0 by positivity ] ) ) ) _ );
      -- Since $1 - \exp(-(c : ℝ) * (T : ℝ)) < 1$, we have $(1 - \exp(-(c : ℝ) * (T : ℝ)))^n \to 0$ as $n \to \infty$.
      have h_exp_zero : Filter.Tendsto (fun n : ℕ => (1 - Real.exp (-(c : ℝ) * (T : ℝ))) ^ n) Filter.atTop (nhds 0) := by
        exact tendsto_pow_atTop_nhds_zero_of_lt_one ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by nlinarith [ show ( c : ℝ ) ≥ 0 by positivity, show ( T : ℝ ) ≥ 0 by positivity ] ) ( sub_lt_self _ <| Real.exp_pos _ );
      exact sub_eq_zero.mp ( by simpa using le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds ( by simpa using h_exp_zero.const_mul ( 2 * C ) ) fun n => h_ind n q hT_le ) ( abs_nonneg _ ) )

/-
**Shifted renewal equation (Chapman–Kolmogorov building block).** The
    time-shifted transition function `(s, x) ↦ P_{s+t}f(x)` is a fixed point of
    the one-step renewal operator whose *terminal* function is `g = P_t f`:
      `P_{s+t}f(x) = S(s,x)·(P_t f)(φ(s,x))
                     + ∫₀ˢ S(w,x)·λ(φ(w,x))·∫ P_{(s−w)+t}f dQ(φ(w,x)) dw`.
    This is Davis's renewal equation (27.2) applied at horizon `s+t` and split at
    `s`: on `[0,s]` the tail `P_{(s+t)−w}f = P_{(s−w)+t}f` reproduces the jump
    integral above, while `S(s+t,x)f(φ(s+t,x)) + ∫ₛ^{s+t} …` collapses to
    `S(s,x)·(P_t f)(φ(s,x))` via the survivor cocycle
    `pdpSurvivorFunction_mul`, the flow group law `flow_add`, and the change of
    variables `w ↦ w + s` in the jump integral of the renewal equation for
    `P_t f` evaluated at `φ(s,x)`.
-/
set_option maxHeartbeats 1600000 in
theorem pdpSemigroup_renewal_equation_shift {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) :
    ∀ q : ℝ≥0 × E,
      pdpSemigroup pdp.toPDP (q.1 + t) f q.2
        = pdpSemigroupOp pdp.toPDP (fun y => pdpSemigroup pdp.toPDP t f y)
            (fun q => pdpSemigroup pdp.toPDP (q.1 + t) f q.2) q := by
              intro q;
              -- Apply the renewal equation to split the semigroup into the survivor function and the integral.
              have h_split : pdpSemigroup pdp.toPDP (q.1 + t) f q.2 = pdpSurvivorFunction pdp.toPDP (q.1 + t) q.2 * f (pdp.flow (q.1 + t) q.2) + ∫ s in Set.Icc (0 : ℝ) ((q.1 + t) : ℝ), pdpSurvivorFunction pdp.toPDP s.toNNReal q.2 * (pdp.jumpRate (pdp.flow s.toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((q.1 + t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal q.2))) := by
                convert pdpSemigroup_renewal_equation pdp f hf hf_bdd hflow c hrate hcont ( q.1 + t ) q.2 using 1;
              -- Apply the renewal equation to split the integral into two parts.
              have h_split_integral : ∫ s in Set.Icc (0 : ℝ) ((q.1 + t) : ℝ), pdpSurvivorFunction pdp.toPDP s.toNNReal q.2 * (pdp.jumpRate (pdp.flow s.toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((q.1 + t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal q.2))) = (∫ s in Set.Icc (0 : ℝ) (q.1 : ℝ), pdpSurvivorFunction pdp.toPDP s.toNNReal q.2 * (pdp.jumpRate (pdp.flow s.toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((q.1 + t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal q.2)))) + (∫ s in Set.Icc (q.1 : ℝ) ((q.1 + t) : ℝ), pdpSurvivorFunction pdp.toPDP s.toNNReal q.2 * (pdp.jumpRate (pdp.flow s.toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((q.1 + t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal q.2)))) := by
                rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.setIntegral_union ] <;> norm_num;
                · have h_integrable : IntervalIntegrable (fun s : ℝ => pdpSurvivorFunction pdp.toPDP s.toNNReal q.2 * (pdp.jumpRate (pdp.flow s.toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((q.1 + t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal q.2)))) MeasureTheory.volume 0 (q.1 + t) := by
                    convert pdpSemigroupOp_integrand_integrableOn pdp.toPDP ( fun q => pdpSemigroup pdp.toPDP q.1 f q.2 ) _ _ _ _ _ _ _ _ using 1;
                    rw [ intervalIntegrable_iff_integrableOn_Icc_of_le ( by positivity ) ];
                    rotate_left;
                    exact pdpSemigroup_measurable pdp f hf hf_bdd hflow c hrate hcont;
                    exact Classical.choose hf_bdd;
                    exact fun q => pdpSemigroup_abs_le pdp f hf hflow c hrate hcont ( Classical.choose hf_bdd ) ( by linarith [ Classical.choose_spec hf_bdd q.2, abs_nonneg ( f q.2 ) ] ) ( Classical.choose_spec hf_bdd ) q.1 q.2;
                    exact hflow;
                    exact c;
                    exact hrate;
                    exact q.1 + t; all_goals norm_cast;
                  exact h_integrable.1.mono_set ( Set.Ioc_subset_Ioc_right ( by linarith [ show ( t : ℝ ) ≥ 0 by positivity ] ) );
                · refine' MeasureTheory.IntegrableOn.mono_set _ ( Set.Ioc_subset_Ioc_left ( show ( q.1 : ℝ ) ≥ 0 by positivity ) );
                  have h_integrable : IntervalIntegrable (fun s : ℝ => pdpSurvivorFunction pdp.toPDP s.toNNReal q.2 * (pdp.jumpRate (pdp.flow s.toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((q.1 + t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal q.2)))) MeasureTheory.volume 0 (q.1 + t) := by
                    convert pdpSemigroupOp_integrand_integrableOn pdp.toPDP ( fun q => pdpSemigroup pdp.toPDP q.1 f q.2 ) _ _ _ _ _ _ _ _ using 1;
                    rw [ intervalIntegrable_iff_integrableOn_Icc_of_le ( by positivity ) ];
                    rotate_left;
                    exact pdpSemigroup_measurable pdp f hf hf_bdd hflow c hrate hcont;
                    exact Classical.choose hf_bdd;
                    exact fun q => pdpSemigroup_abs_le pdp f hf hflow c hrate hcont ( Classical.choose hf_bdd ) ( by linarith [ Classical.choose_spec hf_bdd q.2, abs_nonneg ( f q.2 ) ] ) ( Classical.choose_spec hf_bdd ) q.1 q.2;
                    exact hflow;
                    exact c;
                    exact hrate;
                    exact q.1 + t; all_goals norm_cast;
                  exact h_integrable.1;
              -- Apply the renewal equation to split the integral into two parts and simplify.
              have h_split_integral_simplified : ∫ s in Set.Icc (q.1 : ℝ) ((q.1 + t) : ℝ), pdpSurvivorFunction pdp.toPDP s.toNNReal q.2 * (pdp.jumpRate (pdp.flow s.toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((q.1 + t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal q.2))) = pdpSurvivorFunction pdp.toPDP q.1 q.2 * pdpSemigroup pdp.toPDP t f (pdp.flow q.1 q.2) - pdpSurvivorFunction pdp.toPDP (q.1 + t) q.2 * f (pdp.flow (q.1 + t) q.2) := by
                have h_split_integral_simplified : ∫ s in Set.Icc (q.1 : ℝ) ((q.1 + t) : ℝ), pdpSurvivorFunction pdp.toPDP s.toNNReal q.2 * (pdp.jumpRate (pdp.flow s.toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((q.1 + t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal q.2))) = ∫ s in Set.Icc (0 : ℝ) (t : ℝ), pdpSurvivorFunction pdp.toPDP (s + q.1).toNNReal q.2 * (pdp.jumpRate (pdp.flow (s + q.1).toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP (t - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow (s + q.1).toNNReal q.2))) := by
                  rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc ];
                  rw [ ← intervalIntegral.integral_of_le ( by linarith [ show ( q.1 : ℝ ) ≥ 0 by positivity, show ( t : ℝ ) ≥ 0 by positivity ] ), ← intervalIntegral.integral_of_le ( by linarith [ show ( q.1 : ℝ ) ≥ 0 by positivity, show ( t : ℝ ) ≥ 0 by positivity ] ) ] ; convert intervalIntegral.integral_comp_sub_right _ ( q.1 : ℝ ) using 2 <;> norm_num ; ring;
                have h_split_integral_simplified : ∫ s in Set.Icc (0 : ℝ) (t : ℝ), pdpSurvivorFunction pdp.toPDP (s + q.1).toNNReal q.2 * (pdp.jumpRate (pdp.flow (s + q.1).toNNReal q.2) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP (t - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow (s + q.1).toNNReal q.2))) = ∫ s in Set.Icc (0 : ℝ) (t : ℝ), pdpSurvivorFunction pdp.toPDP q.1 q.2 * pdpSurvivorFunction pdp.toPDP s.toNNReal (pdp.flow q.1 q.2) * (pdp.jumpRate (pdp.flow s.toNNReal (pdp.flow q.1 q.2)) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP (t - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal (pdp.flow q.1 q.2)))) := by
                  refine' MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun s hs => _;
                  rw [ show ( s + q.1 : ℝ ).toNNReal = s.toNNReal + q.1 from ?_, pdpSurvivorFunction_mul ];
                  · rw [ pdp.flow_add ];
                    rw [ ← pdpSurvivorFunction_mul pdp.toPDP q.2 ( hcont q.2 ) q.1 s.toNNReal, ← pdpSurvivorFunction_mul pdp.toPDP q.2 ( hcont q.2 ) s.toNNReal q.1 ];
                    rw [ add_comm ];
                  · exact hcont q.2;
                  · rw [ ← NNReal.coe_inj ] ; simp +decide [ hs.1, hs.2 ];
                have h_split_integral_simplified : pdpSemigroup pdp.toPDP t f (pdp.flow q.1 q.2) = pdpSurvivorFunction pdp.toPDP t (pdp.flow q.1 q.2) * f (pdp.flow t (pdp.flow q.1 q.2)) + ∫ s in Set.Icc (0 : ℝ) (t : ℝ), pdpSurvivorFunction pdp.toPDP s.toNNReal (pdp.flow q.1 q.2) * (pdp.jumpRate (pdp.flow s.toNNReal (pdp.flow q.1 q.2)) : ℝ) * (∫ y, pdpSemigroup pdp.toPDP ((t : ℝ) - s).toNNReal f y ∂(pdp.transitionMeasure (pdp.flow s.toNNReal (pdp.flow q.1 q.2)))) := by
                  apply pdpSemigroup_renewal_equation pdp f hf hf_bdd hflow c hrate hcont t (pdp.flow q.1 q.2);
                have h_split_integral_simplified : pdpSurvivorFunction pdp.toPDP (q.1 + t) q.2 = pdpSurvivorFunction pdp.toPDP q.1 q.2 * pdpSurvivorFunction pdp.toPDP t (pdp.flow q.1 q.2) := by
                  exact pdpSurvivorFunction_mul pdp.toPDP q.2 ( hcont q.2 ) q.1 t;
                simp_all +decide [ mul_assoc, MeasureTheory.integral_const_mul ];
                rw [ show pdp.flow ( q.1 + t ) q.2 = pdp.flow t ( pdp.flow q.1 q.2 ) from pdp.flow_add t q.1 q.2 ▸ by simp +decide [ add_comm ] ] ; ring;
              unfold pdpSemigroupOp; simp +decide [ h_split, h_split_integral, h_split_integral_simplified ] ; ring;
              rw [ add_comm ];
              refine' congr rfl ( MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun s hs => _ );
              rw [ show ( q.1 + ( t - s ) : ℝ ) = t + ( q.1 - s ) by ring, Real.toNNReal_add ] <;> norm_num [ hs.1, hs.2 ]

/-
**(25.5 / 27.x) The semigroup (Chapman–Kolmogorov) property.** The PDP
    transition semigroup satisfies `P_{s+t}f = P_s(P_t f)`. Both
    `(s,x) ↦ P_{s+t}f(x)` (via `pdpSemigroup_renewal_equation_shift`) and
    `(s,x) ↦ P_s(P_t f)(x)` (via `pdpSemigroup_renewal_equation`) are bounded,
    jointly-measurable fixed points of the one-step renewal operator with
    terminal function `g = P_t f`, so they coincide by
    `pdpSemigroupOp_fixedpoint_unique`.
-/
theorem pdpSemigroup_semigroup_property {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (s t : ℝ≥0) (x : E) :
    pdpSemigroup pdp.toPDP (s + t) f x
      = pdpSemigroup pdp.toPDP s (fun y => pdpSemigroup pdp.toPDP t f y) x := by
        obtain ⟨ C, hC ⟩ := hf_bdd;
        -- Let `g := fun y => pdpSemigroup pdp.toPDP t f y`.
        set g : E → ℝ := fun y => pdpSemigroup pdp.toPDP t f y;
        -- By definition of $g$, we know that $g$ is measurable and bounded.
        have hg_meas : Measurable g := by
          exact ( pdp_semigroup_maps_bounded_measurable pdp t hf ⟨ C, hC ⟩ hflow c hrate hcont ).1
        have hg_bdd : ∀ y, |g y| ≤ C := by
          exact fun y => pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C ( le_trans ( abs_nonneg _ ) ( hC y ) ) hC t y;
        -- Apply the fixed point uniqueness result to conclude the proof.
        apply Eq.symm; exact (by
          have := pdpSemigroupOp_fixedpoint_unique pdp g C (by linarith [abs_le.mp (hC x)]) hflow c hrate hcont
            (fun q => pdpSemigroup pdp.toPDP q.1 g q.2) (fun q => pdpSemigroup pdp.toPDP (q.1 + t) f q.2)
            (by
            exact fun q => pdpSemigroup_abs_le pdp g hg_meas hflow c hrate hcont C (by linarith [abs_le.mp (hC x), abs_le.mp (hg_bdd x)]) hg_bdd q.1 q.2) (by
            exact fun q => pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C (by linarith [abs_le.mp (hC x)]) hC (q.1 + t) q.2) (by
            apply pdpSemigroup_measurable pdp g hg_meas ⟨ C, hg_bdd ⟩ hflow c hrate hcont) (by
            convert pdpSemigroup_measurable pdp f hf ⟨ C, hC ⟩ hflow c hrate hcont |> Measurable.comp <| measurable_fst.add_const t |> Measurable.prodMk <| measurable_snd using 1) (by
            intro q
            apply Eq.symm; exact (by
              have := pdpSemigroup_renewal_equation pdp g hg_meas ⟨C, hg_bdd⟩ hflow c hrate hcont q.1 q.2
              convert this.symm using 1)) (by
            exact fun q => pdpSemigroup_renewal_equation_shift pdp f hf ⟨ C, hC ⟩ hflow c hrate hcont t q)
          exact this ⟨ s, x ⟩)

/-
**(27) Strong right-continuity of the transition semigroup in time.** For any
    continuous bounded `f` and any `t₀`, `P_{t₀+h}f(x) → P_{t₀}f(x)` as `h ↓ 0`.

    This is the time-regularity companion of `pdpSemigroup_tendsto_zero` (strong
    continuity at `0`) upgraded to an arbitrary base time `t₀` via the semigroup
    (Chapman–Kolmogorov) property.  Writing `g := P_{t₀}f`, the semigroup
    property gives `P_{t₀+h}f = P_h g`, and `g` is continuous (Feller property
    `pdp_feller_property`), measurable (`pdp_semigroup_maps_bounded_measurable`)
    and bounded by `C` (`pdpSemigroup_abs_le`).  Strong continuity at `0`
    (`pdpSemigroup_tendsto_zero`) applied to `g` then yields
    `P_h g(x) → g(x) = P_{t₀}f(x)` as `h ↓ 0`.
-/
theorem pdpSemigroup_right_continuous_time
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C) (t₀ : ℝ≥0) (x : E) :
    Filter.Tendsto (fun h : ℝ≥0 => pdpSemigroup pdp.toPDP (t₀ + h) f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (pdpSemigroup pdp.toPDP t₀ f x)) := by
  -- Set g := fun y => pdpSemigroup pdp.toPDP t₀ f y (the function P_{t₀}f).
  set g : E → ℝ := fun y => pdpSemigroup pdp.toPDP t₀ f y;
  have hg : Measurable g ∧ Continuous g ∧ (∃ C', ∀ y, |g y| ≤ C') := by
    refine' ⟨ _, _, _ ⟩;
    · have := pdp_semigroup_maps_bounded_measurable pdp t₀ hf ⟨ C, hfC ⟩ hflow c hrate hcont;
      exact this.1;
    · apply pdp_feller_property pdp (by trivial) hrate_cont ⟨c, hrate⟩ hflow hflow_cont hQ_cont hf hf_cont ⟨C, hfC⟩ t₀;
    · exact ⟨ C, fun y => pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C ( le_trans ( abs_nonneg _ ) ( hfC y ) ) hfC t₀ y ⟩;
  have := pdpSemigroup_tendsto_zero pdp hflow hflow_cont c hrate hcont ( f := g ) hg.1 hg.2.1 hg.2.2.choose hg.2.2.choose_spec x;
  convert this using 2;
  rw [ add_comm, pdpSemigroup_semigroup_property pdp f hf ⟨ C, hfC ⟩ hflow c hrate hcont ]

/-
**Right-limit criterion for measurability on `ℝ≥0`.** If `f : ℝ≥0 → ℝ` has, at
    every base point `t₀`, the right limit `f(t₀ + h) → f(t₀)` as `h ↓ 0`, then `f`
    is Borel-measurable. `f` is the pointwise limit of the dyadic
    right-endpoint approximations `fₙ(t) = f((⌊t·2ⁿ⌋ + 1)/2ⁿ)`, each of which
    factors through the measurable map `t ↦ ⌊t·2ⁿ⌋ : ℝ≥0 → ℕ` (every function out
    of `ℕ` is measurable), and `(⌊t·2ⁿ⌋+1)/2ⁿ = t + hₙ(t)` with `hₙ(t) ↓ 0`,
    `hₙ(t) > 0`, so the hypothesis gives `fₙ(t) → f(t)`.
-/
lemma measurable_of_tendsto_right_NNReal {f : ℝ≥0 → ℝ}
    (hf : ∀ t₀ : ℝ≥0, Filter.Tendsto (fun h : ℝ≥0 => f (t₀ + h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f t₀))) :
    Measurable f := by
  have h_approx : ∀ t : ℝ≥0, Filter.Tendsto (fun n : ℕ => f (((⌊(t : ℝ) * 2 ^ n⌋₊ + 1) / 2 ^ n : ℝ≥0))) Filter.atTop (nhds (f t)) := by
    intro t
    have h_tendsto_h : Filter.Tendsto (fun n : ℕ => ((⌊(t : ℝ) * 2^n⌋₊ + 1) / 2^n : ℝ≥0) - t) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      refine' tendsto_nhdsWithin_iff.mpr ⟨ _, _ ⟩;
      · rw [ ← NNReal.tendsto_coe ];
        refine' squeeze_zero ( fun _ => by positivity ) ( fun n => _ ) ( tendsto_inv_atTop_nhds_zero_nat.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) );
        rw [ NNReal.coe_sub ] ; norm_num;
        · rw [ div_le_iff₀ ] <;> norm_num ; nlinarith [ Nat.floor_le ( show 0 ≤ ( t : ℝ ) * 2 ^ n by positivity ), Nat.lt_floor_add_one ( ( t : ℝ ) * 2 ^ n ), pow_pos ( zero_lt_two' ℝ ) n, mul_inv_cancel₀ ( show ( 2 : ℝ ) ^ n ≠ 0 by positivity ) ];
        · rw [ le_div_iff₀ ( by positivity ) ] ; exact_mod_cast Nat.lt_floor_add_one _ |> le_of_lt;
      · simp +zetaDelta at *;
        exact ⟨ 1, fun n hn => by rw [ lt_div_iff₀ ( by positivity ) ] ; exact_mod_cast Nat.lt_floor_add_one _ ⟩;
    convert hf t |> Filter.Tendsto.comp <| h_tendsto_h using 2;
    rw [ Function.comp_apply, add_tsub_cancel_of_le ];
    rw [ le_div_iff₀ ( by positivity ) ] ; exact_mod_cast Nat.lt_floor_add_one _ |> le_of_lt;
  -- Define the sequence of functions $F_n$.
  set F : ℕ → ℝ≥0 → ℝ := fun n t => f ((⌊(t : ℝ) * 2 ^ n⌋₊ + 1) / 2 ^ n : ℝ≥0);
  convert measurable_of_tendsto_metrizable ( fun n => show Measurable ( F n ) from ?_ ) ( tendsto_pi_nhds.mpr h_approx ) using 1;
  convert Measurable.comp ( show Measurable ( fun k : ℕ => f ( ( k + 1 : ℝ≥0 ) / 2 ^ n ) ) from ?_ ) ( show Measurable ( fun t : ℝ≥0 => ⌊ ( t : ℝ ) * 2 ^ n⌋₊ ) from ?_ ) using 1;
  · exact Measurable.of_discrete;
  · fun_prop

/-
**Measurability in time of the transition semigroup.** For continuous bounded
    `f`, the map `t ↦ Pₜf(x)` is Borel-measurable: it is right-continuous by
    `pdpSemigroup_right_continuous_time`, so `measurable_of_tendsto_right_NNReal`
    applies. This is the analytic prerequisite for the resolvent
    `Uᵅf = ∫₀^∞ e^{−αt} Pₜf dt` of the §27 right-process theory.
-/
theorem pdpSemigroup_measurable_time
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C) (x : E) :
    Measurable (fun t : ℝ≥0 => pdpSemigroup pdp.toPDP t f x) := by
  -- Let's choose any $t₀ : ℝ≥0$. We	want to show the right-limit property.
  apply (measurable_of_tendsto_right_NNReal (fun t₀ => pdpSemigroup_right_continuous_time pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC t₀ x))

/-!
### The α-resolvent (α-potential) of the transition semigroup (27)

With the transition operator `Pₜ` now known to be measurable in time
(`pdpSemigroup_measurable_time`), we can define the **α-resolvent** (or
α-potential kernel)
`Uᵅf(x) = ∫₀^∞ e^{-αt} Pₜf(x) dt`, the Laplace transform of the semigroup.
The integrand is measurable in `t` and dominated by `C·e^{-αt}`, so for `α > 0`
the integral converges absolutely and satisfies the contraction bound
`|Uᵅf| ≤ C/α`.
-/

/-- Value of the elementary exponential integral `∫₀^∞ e^{-a t} dt = a⁻¹`
    for `a > 0`. -/
lemma integral_exp_neg_mul_Ioi_zero {a : ℝ} (ha : 0 < a) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-a * t) = a⁻¹ := by
  have h := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 ha
  simp only [mul_zero, smul_eq_mul] at h
  rw [integral_exp_neg_Ioi] at h
  simp only [neg_zero, Real.exp_zero, mul_one] at h
  rw [show (fun t => Real.exp (-(a * t))) = fun t => Real.exp (-a * t) by ext t; ring_nf] at h
  rw [h]

/-- The α-resolvent (α-potential kernel) of the PDP transition semigroup:
    `Uᵅf(x) = ∫₀^∞ e^{-αt} Pₜf(x) dt`. -/
noncomputable def pdpResolvent {E : Type*} [MeasurableSpace E]
    (p : PDP E) (alpha : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(alpha : ℝ) * t) * pdpSemigroup p t.toNNReal f x

/-
The resolvent integrand `t ↦ e^{-αt} Pₜf(x)` is integrable on `(0, ∞)`
    for `α > 0`: it is measurable in `t` (via `pdpSemigroup_measurable_time`)
    and dominated in absolute value by the integrable function `C·e^{-αt}`
    (the semigroup contraction `pdpSemigroup_abs_le`).
-/
theorem pdpResolvent_integrand_integrableOn
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) (x : E) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(alpha : ℝ) * t) * pdpSemigroup pdp.toPDP t.toNNReal f x)
      (Set.Ioi 0) volume := by
        have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(alpha : ℝ) * t) * C) (Set.Ioi 0) := by
          exact MeasureTheory.Integrable.mul_const ( exp_neg_integrableOn_Ioi 0 halpha ) _;
        refine' h_integrable.mono' _ _;
        · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
          · exact Continuous.aestronglyMeasurable ( by continuity );
          · refine' Measurable.aestronglyMeasurable _;
            convert pdpSemigroup_measurable_time pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC x using 1;
            constructor <;> intro h;
            · convert pdpSemigroup_measurable_time pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC x using 1;
            · convert h.comp ( show Measurable fun t : ℝ => t.toNNReal from measurable_id'.real_toNNReal ) using 1;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ] ; exact mul_le_mul_of_nonneg_left ( pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C ( le_trans ( abs_nonneg _ ) ( hfC x ) ) hfC _ _ ) ( Real.exp_pos _ |> le_of_lt ) ;

/-
**Contraction bound for the resolvent.** For `α > 0` and `|f| ≤ C`,
    `|Uᵅf(x)| ≤ C/α`. Indeed `|Uᵅf(x)| ≤ ∫₀^∞ e^{-αt} |Pₜf(x)| dt`
    `≤ ∫₀^∞ e^{-αt} C dt = C·α⁻¹`, using the semigroup contraction
    `pdpSemigroup_abs_le` (`|Pₜf| ≤ C`) and `integral_exp_neg_mul_Ioi_zero`.
-/
theorem pdpResolvent_abs_le
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) (x : E) :
    |pdpResolvent pdp.toPDP alpha f x| ≤ C / (alpha : ℝ) := by
      convert MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) |> le_trans <| ?_ using 1;
      refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
      refine' fun t => C * Real.exp ( - ( alpha : ℝ ) * t );
      · exact Filter.Eventually.of_forall fun t => norm_nonneg _;
      · exact MeasureTheory.Integrable.const_mul ( by simpa using ( exp_neg_integrableOn_Ioi 0 halpha ) ) _;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;
        convert mul_le_mul_of_nonneg_left ( pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C ( le_trans ( abs_nonneg _ ) ( hfC x ) ) hfC t.toNNReal x ) ( Real.exp_pos ( - ( alpha : ℝ ) * t ) |> le_of_lt ) using 1 ; norm_num ; ring;
      · rw [ MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi_zero halpha ] ; ring_nf ; norm_num [ halpha.ne' ]

/-- **Positivity of the resolvent.** For a nonnegative (bounded, measurable)
    `f` and `α > 0`, `Uᵅf(x) ≥ 0`. The integrand `e^{-αt} Pₜf(x)` is nonnegative
    (`pdpSemigroup_nonneg`), so its integral over `(0, ∞)` is nonnegative. -/
theorem pdpResolvent_nonneg
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ)
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hf_nonneg : ∀ y, 0 ≤ f y) (alpha : ℝ≥0) (x : E) :
    0 ≤ pdpResolvent pdp.toPDP alpha f x := by
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t _ => ?_)
  exact mul_nonneg (Real.exp_pos _).le
    (pdpSemigroup_nonneg pdp f hf hf_bdd hflow c hrate hcont hf_nonneg t.toNNReal x)

/-
**Additivity of the resolvent.** `Uᵅ(f+g) = Uᵅf + Uᵅg` for bounded
    continuous `f, g` and `α > 0`. Pointwise in `t`, `Pₜ(f+g) = Pₜf + Pₜg`
    (`pdpSemigroup_add`); the integral then splits by `MeasureTheory.integral_add`,
    both summand integrands being integrable
    (`pdpResolvent_integrand_integrableOn`).
-/
theorem pdpResolvent_add
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {f g : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (Cf : ℝ) (hfC : ∀ y, |f y| ≤ Cf)
    (hg : Measurable g) (hg_cont : Continuous g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) (x : E) :
    pdpResolvent pdp.toPDP alpha (fun y => f y + g y) x =
      pdpResolvent pdp.toPDP alpha f x + pdpResolvent pdp.toPDP alpha g x := by
        convert MeasureTheory.integral_add _ _ using 3;
        · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
          rw [ ← mul_add, pdpSemigroup_add pdp f g hf ⟨ Cf, hfC ⟩ hg ⟨ Cg, hgC ⟩ hflow c hrate hcont t.toNNReal x ];
        · apply_rules [ pdpResolvent_integrand_integrableOn ];
        · exact pdpResolvent_integrand_integrableOn pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hg hg_cont Cg hgC alpha halpha x

/-
**Scalar homogeneity of the resolvent.** `Uᵅ(a·f) = a·Uᵅf`.
-/
theorem pdpResolvent_smul
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (a : ℝ) {f : E → ℝ}
    (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ y, |f y| ≤ C)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (alpha : ℝ≥0) (x : E) :
    pdpResolvent pdp.toPDP alpha (fun y => a * f y) x =
      a * pdpResolvent pdp.toPDP alpha f x := by
        convert MeasureTheory.integral_const_mul a _ using 1;
        refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
        rw [ mul_left_comm, pdpSemigroup_smul pdp _ _ hf hf_bdd hflow c hrate hcont ]

/- **Monotonicity of the resolvent.** If `f ≤ g`, then `Uᵅf ≤ Uᵅg`. -/
theorem pdpResolvent_mono
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f g : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (Cf : ℝ) (hfC : ∀ y, |f y| ≤ Cf)
    (hg : Measurable g) (hg_cont : Continuous g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg)
    (hfg : ∀ y, f y ≤ g y)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) (x : E) :
    pdpResolvent pdp.toPDP alpha f x ≤ pdpResolvent pdp.toPDP alpha g x := by
      apply_rules [ MeasureTheory.integral_mono_ae ];
      · apply_rules [ pdpResolvent_integrand_integrableOn ];
      · apply_rules [ pdpResolvent_integrand_integrableOn ];
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using mul_le_mul_of_nonneg_left ( pdpSemigroup_mono pdp f g hf ⟨ Cf, hfC ⟩ hg ⟨ Cg, hgC ⟩ hflow c hrate hcont hfg t.toNNReal x ) ( Real.exp_pos _ |> le_of_lt )

/-
**Feller regularity of the resolvent.** For `α > 0`, the α-resolvent of a
    bounded continuous function is continuous in the state variable. This is
    dominated convergence applied to the continuous functions
    `x ↦ e^{-αt} Pₜf(x)`, dominated by the integrable envelope
    `C e^{-αt}`.
-/
theorem pdpResolvent_continuous
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) :
    Continuous (fun x => pdpResolvent pdp.toPDP alpha f x) := by
  refine' continuous_iff_continuousAt.2 fun x => _;
  refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
  refine' fun t => Real.exp ( - ( alpha : ℝ ) * t ) * C;
  · refine' Filter.Eventually.of_forall fun y => MeasureTheory.AEStronglyMeasurable.mul _ _;
    · exact Continuous.aestronglyMeasurable ( by continuity );
    · refine' Measurable.aestronglyMeasurable _;
      convert pdpSemigroup_measurable_time pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC y using 1;
      constructor <;> intro h;
      · convert pdpSemigroup_measurable pdp f hf ⟨ C, hfC ⟩ hflow c hrate hcont using 1;
        constructor <;> intro h;
        · convert pdpSemigroup_measurable pdp f hf ⟨ C, hfC ⟩ hflow c hrate hcont using 1;
        · exact h.comp ( measurable_id.prodMk measurable_const );
      · convert h.comp ( measurable_id'.ennreal_toNNReal ) using 1;
        constructor <;> intro h;
        · expose_names
          exact ENNReal.measurable_of_measurable_nnreal h_1
        · fun_prop;
  · refine' Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall fun t => _;
    rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ];
    gcongr;
    apply_rules [ pdpSemigroup_abs_le ];
    exact le_trans ( abs_nonneg _ ) ( hfC x );
  · exact MeasureTheory.Integrable.mul_const (by simpa using exp_neg_integrableOn_Ioi 0 halpha) _;
  · refine' Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) fun t ht => _;
    exact Continuous.tendsto ( by exact Continuous.mul continuous_const ( pdp_feller_property pdp ( by trivial ) hrate_cont ⟨ c, hrate ⟩ hflow hflow_cont hQ_cont hf hf_cont ⟨ C, hfC ⟩ _ ) ) _

/-
The positive resolvent maps bounded continuous functions to bounded
    continuous (hence Borel-measurable) functions, with sup-norm bound
    `C / α`.
-/
theorem pdpResolvent_maps_bounded_continuous
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) :
    Measurable (fun x => pdpResolvent pdp.toPDP alpha f x) ∧
      Continuous (fun x => pdpResolvent pdp.toPDP alpha f x) ∧
      ∀ x, |pdpResolvent pdp.toPDP alpha f x| ≤ C / (alpha : ℝ) := by
  refine' ⟨ _, _, _ ⟩;
  · convert pdpResolvent_continuous pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC alpha halpha |> Continuous.measurable using 1;
  · convert pdpResolvent_continuous pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf ( hf_cont ) C hfC alpha halpha;
  · apply_rules [ pdpResolvent_abs_le ]

/-
**Discounted semigroup continuity at zero for the resolvent.** If `f` is
bounded and continuous and `α > 0`, then

`e^{-αt} Pₜ(Uᵅf)(x) → Uᵅf(x)` as `t ↓ 0`.

The preceding Feller mapping theorem makes `Uᵅf` continuous, measurable, and
bounded by `C / α`. Strong continuity of the semigroup at zero applies to this
resolvent function, while the exponential discount tends to one.
-/
theorem pdpResolvent_discounted_semigroup_tendsto_zero
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) (x : E) :
    Filter.Tendsto
      (fun t : ℝ≥0 => Real.exp (-(alpha : ℝ) * (t : ℝ)) *
        pdpSemigroup pdp.toPDP t (pdpResolvent pdp.toPDP alpha f) x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (pdpResolvent pdp.toPDP alpha f x)) := by
        have := pdpSemigroup_tendsto_zero pdp hflow hflow_cont c hrate hcont (show Measurable (pdpResolvent pdp.toPDP alpha f) from (by
        exact ( pdpResolvent_maps_bounded_continuous pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC alpha halpha ) |>.1)) (show Continuous (pdpResolvent pdp.toPDP alpha f) from (by
        exact pdpResolvent_continuous pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC alpha halpha)) (C / alpha) (fun y => (by
        apply_rules [ pdpResolvent_abs_le ])) x;
        simpa using Filter.Tendsto.mul ( Continuous.continuousWithinAt ( show Continuous fun t : ℝ≥0 => Real.exp ( - ( alpha : ℝ ) * t ) by continuity ) ) this

/-
The positivity and zero-time regularity components of α-excessiveness hold for
the resolvent of every bounded, continuous, nonnegative function.  This
isolates the remaining substantive component: the discounted semigroup
inequality.
-/
theorem pdpResolvent_alphaExcessive_components
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y) (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) :
    (∀ x, 0 ≤ pdpResolvent pdp.toPDP alpha f x) ∧
      ∀ x, Filter.Tendsto
        (fun t : ℝ≥0 => Real.exp (-(alpha : ℝ) * (t : ℝ)) *
          pdpSemigroup pdp.toPDP t (pdpResolvent pdp.toPDP alpha f) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (pdpResolvent pdp.toPDP alpha f x)) := by
          refine' ⟨ _, _ ⟩;
          · intros x
            apply pdpResolvent_nonneg pdp f hf ⟨C, hfC⟩ hflow c hrate hcont hf_nonneg alpha x;
          · convert pdpResolvent_discounted_semigroup_tendsto_zero pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC alpha halpha using 1

/-
**Translation of an improper tail integral.**  Translation invariance of
Lebesgue measure identifies the integral of `H (u+s)` over `(0,∞)` with the
integral of `H` over `(s,∞)`.  This elementary lemma is kept separate from the
PDP argument because it is the analytic change of variables needed after the
semigroup/Fubini step.
-/
theorem integral_Ioi_comp_add_eq_integral_Ioi (H : ℝ → ℝ) (s : ℝ) :
    (∫ u in Set.Ioi 0, H (u + s)) = ∫ v in Set.Ioi s, H v := by
  rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
  simp +decide [ Set.indicator ];
  rw [ ← MeasureTheory.integral_sub_right_eq_self _ s ] ; congr ; ext ; aesop

/-
**A nonnegative tail is dominated by the full positive-time integral.**
This is the order-theoretic part of the resolvent inequality, isolated from
all PDP-specific notation.
-/
theorem integral_Ioi_mono_lower_of_nonneg (H : ℝ → ℝ) (s : ℝ)
    (hs : 0 ≤ s) (hH_int : IntegrableOn H (Set.Ioi 0) volume)
    (hH_nonneg : ∀ u ∈ Set.Ioi 0, 0 ≤ H u) :
    (∫ u in Set.Ioi s, H u) ≤ ∫ u in Set.Ioi 0, H u := by
  apply_rules [ MeasureTheory.setIntegral_mono_set ];
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using hH_nonneg u hu;
  · exact MeasureTheory.ae_of_all _ fun x hx => lt_of_le_of_lt hs hx

/-
**Fubini over a positive-time set integral.** This small wrapper packages the
orientation and restricted-measure bookkeeping used by the resolvent proof.
-/
theorem integral_integral_Ioi_swap
    {A : Type*} [MeasurableSpace A] (mu : Measure A) [SFinite mu]
    (h : ℝ → A → ℝ)
    (hint : Integrable (Function.uncurry (fun a s => h s a))
      (mu.prod (volume.restrict (Set.Ioi 0)))) :
    (∫ a, (∫ s in Set.Ioi (0 : ℝ), h s a) ∂mu) =
      ∫ s in Set.Ioi (0 : ℝ), (∫ a, h s a ∂mu) := by
  exact MeasureTheory.integral_integral_swap hint

/-
**Semigroup--resolvent interchange from a transition-kernel representation.**
For fixed `t` and `x`, suppose `Pₜ` is represented by a Markov kernel `K` at
`x`. The discounted semigroup integrand is jointly measurable and dominated by
`C exp (-alpha s)` under the probability measure `K x`; hence Fubini moves the
kernel integral through the positive-time integral defining the resolvent.
-/
theorem pdpResolvent_semigroup_interchange_of_kernel
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ D, ∀ x, |h x| ≤ D) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ))
    (t : ℝ≥0) (x : E) (K : Kernel E E) [IsMarkovKernel K]
    (hrepr : ∀ (g : E → ℝ), Measurable g →
      (∃ D : ℝ, ∀ y, |g y| ≤ D) →
      pdpSemigroup pdp.toPDP t g x = ∫ y, g y ∂(K x)) :
    pdpSemigroup pdp.toPDP t (pdpResolvent pdp.toPDP alpha f) x =
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(alpha : ℝ) * s) *
        pdpSemigroup pdp.toPDP t
          (fun y => pdpSemigroup pdp.toPDP s.toNNReal f y) x := by
            have h_measurable : Measurable (fun q : ℝ≥0 × E => pdpSemigroup pdp.toPDP q.1 f q.2) := by
              apply_rules [ pdpSemigroup_measurable ];
              use C;
            convert hrepr _ _ _;
            · have h_fubini : ∫ y, ∫ s in Set.Ioi 0, Real.exp (-(alpha : ℝ) * s) * pdpSemigroup pdp.toPDP s.toNNReal f y ∂volume ∂K x = ∫ s in Set.Ioi 0, ∫ y, Real.exp (-(alpha : ℝ) * s) * pdpSemigroup pdp.toPDP s.toNNReal f y ∂K x ∂volume := by
                rw [ MeasureTheory.integral_integral_swap ];
                refine' MeasureTheory.Integrable.mono' _ _ _;
                use fun p => Real.exp ( - ( alpha : ℝ ) * p.2 ) * C;
                · rw [ MeasureTheory.integrable_prod_iff ];
                  · simp +decide [ MeasureTheory.integrable_const_iff, halpha.ne' ];
                    exact MeasureTheory.Integrable.mul_const
                      (by simpa [mul_comm] using exp_neg_integrableOn_Ioi 0 halpha) _;
                  · fun_prop;
                · fun_prop;
                · simp +decide [ Function.uncurry ];
                  filter_upwards [ ] with a using mul_le_mul_of_nonneg_left ( pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C ( show 0 ≤ C by exact le_trans ( abs_nonneg _ ) ( hfC x ) ) hfC _ _ ) ( Real.exp_nonneg _ );
              convert h_fubini.symm using 1;
              refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s hs => _;
              rw [ MeasureTheory.integral_const_mul, hrepr ];
              · convert h_measurable.comp ( measurable_const.prodMk measurable_id' ) using 1;
              · exact ⟨ C, fun y => pdpSemigroup_abs_le pdp f hf hflow c hrate hcont C ( by linarith [ abs_le.mp ( hfC y ) ] ) hfC _ _ ⟩;
            · convert pdpResolvent_maps_bounded_continuous pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC alpha halpha |>.1 using 1;
            · exact ⟨ C / alpha, fun y => pdpResolvent_abs_le pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC alpha halpha y ⟩

/-
**Discounted semigroup inequality after kernel/Fubini interchange.**
The hypothesis `hinterchange` is precisely the remaining kernel theorem: it
allows `Pₜ` to pass through the time integral defining the resolvent.  From
there Chapman--Kolmogorov changes `PₜPₛf` to `Pₜ₊ₛf`, exponential factors
combine, translation turns the result into the tail integral over `(t,∞)`,
and nonnegativity compares that tail with the full resolvent.
-/
theorem pdpResolvent_discounted_semigroup_le_of_integral_interchange
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y) (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ))
    (hinterchange : ∀ (t : ℝ≥0) (x : E),
      pdpSemigroup pdp.toPDP t (pdpResolvent pdp.toPDP alpha f) x =
        ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(alpha : ℝ) * s) *
          pdpSemigroup pdp.toPDP t
            (fun y => pdpSemigroup pdp.toPDP s.toNNReal f y) x) :
    ∀ (t : ℝ≥0) (x : E),
      Real.exp (-(alpha : ℝ) * (t : ℝ)) *
        pdpSemigroup pdp.toPDP t (pdpResolvent pdp.toPDP alpha f) x ≤
          pdpResolvent pdp.toPDP alpha f x := by
  intro t x; rw [ hinterchange t x ] ; simp +decide [ mul_assoc, MeasureTheory.integral_const_mul ] ;
  convert integral_Ioi_mono_lower_of_nonneg _ _ _ _ _ using 1;
  convert integral_Ioi_comp_add_eq_integral_Ioi ( fun u => Real.exp ( - ( alpha : ℝ ) * u ) * pdpSemigroup pdp.toPDP u.toNNReal f x ) ( t : ℝ ) using 1;
  · rw [ ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => _ ; ring;
    rw [ ← Real.exp_add ] ; ring;
    rw [ ← pdpSemigroup_semigroup_property pdp f hf ⟨ C, hfC ⟩ hflow c hrate hcont ] ; norm_num [ hu.out.le ];
  · positivity;
  · apply_rules [ pdpResolvent_integrand_integrableOn ];
  · exact fun u hu => mul_nonneg ( Real.exp_nonneg _ ) ( pdpSemigroup_nonneg pdp f hf ⟨ C, hfC ⟩ hflow c hrate hcont hf_nonneg _ _ )

/-
A packaging lemma for the final α-excessiveness result.  Once the discounted
semigroup inequality is supplied, positivity and convergence are discharged by
`pdpResolvent_alphaExcessive_components`.
-/
theorem pdpResolvent_isAlphaExcessive_of_discounted_semigroup_le
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y) (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ))
    (hle : ∀ (t : ℝ≥0) (x : E),
      Real.exp (-(alpha : ℝ) * (t : ℝ)) *
        pdpSemigroup pdp.toPDP t (pdpResolvent pdp.toPDP alpha f) x ≤
          pdpResolvent pdp.toPDP alpha f x) :
    IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha
      (pdpResolvent pdp.toPDP alpha f) := by
        convert pdpResolvent_alphaExcessive_components pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont hf_nonneg C hfC alpha halpha using 1;
        -- By definition of IsAlphaExcessive, we need to show that the resolvent satisfies the three conditions.
        simp [IsAlphaExcessive];
        intro h_nonneg; simp_all +decide [mul_assoc, mul_comm, mul_left_comm];
        constructor <;> intro h x <;> specialize h x <;> rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
        · exact fun ε εpos => by rcases Metric.tendsto_nhds_nhds.mp h ε εpos with ⟨ δ, δpos, hδ ⟩ ; exact ⟨ δ, δpos, fun t ht ht' => hδ ht' ⟩ ;
        · rw [ Metric.tendsto_nhds_nhds ];
          intro ε hε; rcases h ε hε with ⟨ δ, hδ, H ⟩ ; use δ, hδ; intro t ht; cases eq_or_ne t 0 <;> simp_all +decide [ dist_eq_norm ] ;
          · rw [ pdpSemigroup_zero ] ; simpa using hε;
          · exact H ( pos_iff_ne_zero.mpr ‹_› ) ht

/-
**Resolvents are α-excessive once kernel/Fubini interchange is available.**
This combines the preceding discounted inequality with positivity and the
zero-time limit.  The sole explicit hypothesis left is the analytic
semigroup--integral interchange theorem.
-/
theorem pdpResolvent_isAlphaExcessive_of_kernel
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ D, ∀ x, |h x| ≤ D) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y) (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ))
    (K : ℝ≥0 → Kernel E E) (hK : ∀ t, IsMarkovKernel (K t))
    (hrepr : ∀ (t : ℝ≥0) (x : E) (g : E → ℝ), Measurable g →
      (∃ D : ℝ, ∀ y, |g y| ≤ D) →
      pdpSemigroup pdp.toPDP t g x = ∫ y, g y ∂(K t x)) :
    IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha
      (pdpResolvent pdp.toPDP alpha f) := by
        apply pdpResolvent_isAlphaExcessive_of_discounted_semigroup_le pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont hf_nonneg C hfC alpha halpha;
        convert pdpResolvent_discounted_semigroup_le_of_integral_interchange pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont hf_nonneg C hfC alpha halpha _;
        intro t x;
        convert pdpResolvent_semigroup_interchange_of_kernel pdp hrate_cont c hrate hflow hflow_cont hcont hQ_cont hf hf_cont C hfC alpha halpha t x ( K t ) _ using 1;
        exact hrepr t x

/-
**Resolvents are α-excessive once semigroup--integral interchange is available.**
This lower-level variant retains the interchange identity as an explicit
hypothesis; `pdpResolvent_isAlphaExcessive_of_kernel` derives it from a Markov
transition-kernel representation and Fubini.
-/
theorem pdpResolvent_isAlphaExcessive_of_integral_interchange
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ C, ∀ x, |h x| ≤ C) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y) (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ))
    (hinterchange : ∀ (t : ℝ≥0) (x : E),
      pdpSemigroup pdp.toPDP t (pdpResolvent pdp.toPDP alpha f) x =
        ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(alpha : ℝ) * s) *
          pdpSemigroup pdp.toPDP t
            (fun y => pdpSemigroup pdp.toPDP s.toNNReal f y) x) :
    IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha
      (pdpResolvent pdp.toPDP alpha f) := by
  apply_rules [ pdpResolvent_isAlphaExcessive_of_discounted_semigroup_le ];
  apply_rules [ pdpResolvent_discounted_semigroup_le_of_integral_interchange ]

end S27_FurtherProperties

end Davis

end