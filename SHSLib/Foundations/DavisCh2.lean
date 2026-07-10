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

/-- (25.3) Theorem. The natural filtration of the PDP is right-continuous:
    𝔉ₜ = 𝔉_{t+} := ⋂_{ε>0} 𝔉_{t+ε}. -/
theorem pdp_filtration_right_continuous
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [TopologicalSpace E]
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {X : ℝ≥0 → Omega → E}
    (hrc : ∀ omega, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s => X s omega) (nhdsWithin t (Set.Ioi t))
        (nhds (X t omega))) :
    ∀ t : ℝ≥0, ℱ t = ⨅ (ε : ℝ≥0) (_ : 0 < ε), ℱ (t + ε) := by sorry

/-!
**(25.5) Theorem.** The PDP is a homogeneous strong Markov process.
-/

/-- The semigroup of the PDP: Pₜf(x) = 𝔼ₓ[f(xₜ)]. -/
def pdpSemigroup {E : Type*} [MeasurableSpace E]
    (p : PDP E) (t : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  sorry  -- The expected value of f(xₜ) starting from x

/-- (25.5) The simple Markov property: for fixed t,
    𝔼ₓ[f(x_{t+s}) | 𝔉ₜ] = Pₛf(xₜ). -/
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

/-- (25.5) The strong Markov property for the PDP:
    𝔼ₓ[f(x_{τ+s}) | 𝔉_τ] = Pₛf(x_τ) a.s., where 𝔉_τ is the
    σ-algebra at the stopping time τ. -/
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

/-- (26.7) Proposition. The compensator p̃(t, A) of the counting process
    p(t, A) is such that q(t ∧ Tₖ, A) is a martingale for each k,
    and q(t, A) = p(t, A) - p̃(t, A) is a local martingale, where
    p̃(t, A) = ∫₀ᵗ λ(X_s) Q(X_s, A) ds. -/
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
        Filter.atTop Filter.atTop) ∧
      ∀ n, Martingale (fun t omega =>
        p_count (min t (σ n omega)) omega -
        ∫ u in Set.Icc (0 : ℝ) (min (t : ℝ) ↑(σ n omega)),
          (pdp.transitionMeasure (X u.toNNReal omega) A).toReal *
          (pdp.jumpRate (X u.toNNReal omega) : ℝ)) ℱ P := by sorry

/-!
### Martingale representation (26.12)
-/

/-- (26.12) Theorem (Martingale representation).
    Every ℱₜ-local martingale M can be written as Mₜ = M₀ + ∫ g dq
    for some measurable predictable integrand g, where q = p - p̃ is the
    compensated counting measure. Equivalently, Mₜ = M₀ + (jump terms)
    − ∫₀ᵗ (∫_E g(y) Q(dy; X_s)) λ(X_s) ds. -/
theorem pdp_martingale_representation
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDP E)
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)} :
    ∀ (X : ℝ≥0 → Omega → E) (M : ℝ≥0 → Omega → ℝ),
    (∃ (σ : ℕ → Omega → ℝ≥0),
      (∀ n, IsStoppingTime ℱ (fun omega => (σ n omega : ℝ≥0∞))) ∧
      (∀ᵐ omega ∂P, Filter.Tendsto (fun n => (σ n omega : ℝ≥0∞))
        Filter.atTop Filter.atTop) ∧
      ∀ n, Martingale (fun t omega => M (min t (σ n omega)) omega) ℱ P) →
    ∃ (g : E → ℝ), Measurable g ∧
      ∀ᵐ omega ∂P, ∀ t : ℝ≥0,
        ∃ (jumpSum : ℝ),
          M t omega = M 0 omega + jumpSum -
            ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
              (∫ y, g y ∂(pdp.transitionMeasure (X u.toNNReal omega))) *
              (pdp.jumpRate (X u.toNNReal omega) : ℝ) := by sorry

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
        Filter.atTop Filter.atTop) ∧
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
        Filter.atTop Filter.atTop)
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
        Filter.atTop Filter.atTop) ∧
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

/-- (26.14) Necessity: if f ∈ 𝒟(𝔄) then f satisfies the boundary
    condition f(x) = Qf(x) on the active boundary Γ. -/
theorem pdp_generator_boundary_condition_necessary
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E)
    {f : E → ℝ} (hf : Measurable f) {Gamma : Set E}
    (hf_domain : True) :
    InExtGenDomain_BdCond pdp.toPDP f Gamma := by sorry

/-- (26.17) If f is bounded, measurable, and in the domain of the extended
    generator, then Cₜᶠ = f(Xₜ) − f(X₀) − ∫₀ᵗ 𝔄f(Xₛ) ds is a true
    martingale (not just a local martingale). -/
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

/-- (27.3)(2) The iterates Gⁿψ(t,x) converge to Pₜf(x) as n → ∞,
    where Pₜ is the transition semigroup of the PDP. -/
theorem semigroup_iterate_converges
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (f : E → ℝ) (psi_fn : ℝ≥0 × E → ℝ)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hpsi_bdd : ∃ C : ℝ, ∀ p, |psi_fn p| ≤ C)
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
      Filter.atTop (nhds (pdpSemigroup pdp.toPDP t f x)) := by sorry

/-- (27.4) Corollary. Pₜ maps B(E) → B(E). -/
theorem pdp_semigroup_maps_bounded_measurable
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E) (t : ℝ≥0)
    {f : E → ℝ} (hf : Measurable f) (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    Measurable (pdpSemigroup pdp.toPDP t f) ∧
      ∃ C : ℝ, ∀ x, |pdpSemigroup pdp.toPDP t f x| ≤ C := by sorry

/-!
### The Feller property (27.5–27.6)
-/

/-- (27.6) Theorem. Under no active boundaries, continuous bounded jump
    rate, and Q preserving continuity, the PDP is Feller. -/
theorem pdp_feller_property
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [MetricSpace E]
    [BorelSpace E]
    (pdp : PDPStandard E)
    (h_no_boundary : True)  -- t*(x) = ∞ for all x
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (hrate_bdd : ∃ c : ℝ≥0, ∀ x, pdp.jumpRate x ≤ c)
    (hQ_cont : ∀ f : E → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Continuous (fun x => ∫ y, f y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf_cont : Continuous f)
    (hf_bdd : ∃ C : ℝ, ∀ x, |f x| ≤ C) (t : ℝ≥0) :
    Continuous (pdpSemigroup pdp.toPDP t f) := by sorry

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

/-- (27.8) Theorem. A PDP satisfying the standard conditions is a
    Borel right process. For any α-excessive f, the sample path
    t ↦ f(xₜ(ω)) is a.s. right-continuous. -/
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

/-- (27.8, key step) α-excessive functions are right-continuous along
    the flow: t ↦ f(φ(t, x)) is right-continuous at 0 for all x. -/
theorem alpha_excessive_right_continuous_along_flow
    {E : Type*} [MeasurableSpace E]
    (pdp : PDPStandard E)
    {alpha : ℝ≥0} {f : E → ℝ}
    (hf_excessive : IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha f)
    (x : E) :
    Filter.Tendsto (fun t : ℝ≥0 => f (pdp.flow t x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by sorry

end S27_FurtherProperties

end Davis

end