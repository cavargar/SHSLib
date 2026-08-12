import SHSLib.Core.DavisBridge

open MeasureTheory MeasurableSpace Topology Filter

noncomputable section

/-! # The deterministic Dynkin identity along the SHS flow

`SHS.HasGlobalFlow` only records the *integral* form of the ODE
`φ(t) = x₀ + ∫_{t₀}^{t} f(q₀, φ(s), s) ds`.  This module upgrades it to the
differential form and combines it with the chain rule for a `C¹` test function,
producing the deterministic (jump-free) part of Dynkin's formula:

`ψ(q, φ(t₁), t₁) − ψ(q, x₀, t₀) = ∫_{t₀}^{t₁} (⟪∇ₓψ, f⟫ + ∂ₜψ)(q, φ(s), s) ds`,

whose integrand is exactly `SHS.flowGenerator` evaluated along the augmented
trajectory.  For a transition-free system (`m = 0`) the flow generator *is* the
extended generator, so this is Hespanha's Eq. (8) with no probability involved.
-/

namespace SHS

variable {Q : Type*} {n m : ℕ}

/-! ## Regularity of the flow itself -/

/-- On `[t₀, t₁]` the flow is the primitive of the drift along its own
trajectory: `φ(s) = x₀ + ∫_{t₀}^{s} f(q, φ(r), r) dr` as an interval integral. -/
theorem HasGlobalFlow.flow_eq_intervalIntegral (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    {s : ℝ} (hs : t₀ ≤ s) :
    hflow.flow t₀ q x s =
      x + ∫ r in t₀..s, S.f q (hflow.flow t₀ q x r) r := by
  rw [hflow.flow_ode t₀ q x s, intervalIntegral.integral_of_le hs,
    MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The flow is continuous on `[t₀, t₁]` as soon as the drift along the
trajectory is continuous there. -/
theorem HasGlobalFlow.continuousOn_flow (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (q : Q)
    (x : EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s)
      (Set.Icc t₀ t₁)) :
    ContinuousOn (hflow.flow t₀ q x) (Set.Icc t₀ t₁) := by
  have hint : IntervalIntegrable (fun s => S.f q (hflow.flow t₀ q x s) s)
      volume t₀ t₁ :=
    (hcont.mono (by rw [Set.uIcc_of_le ht])).intervalIntegrable
  have hprim : ContinuousOn (fun s => ∫ r in t₀..s,
      S.f q (hflow.flow t₀ q x r) r) (Set.Icc t₀ t₁) := by
    have := intervalIntegral.continuousOn_primitive_interval'
      (a := t₀) (b₁ := t₀) (b₂ := t₁)
      (f := fun s => S.f q (hflow.flow t₀ q x s) s)
      (μ := volume) hint Set.left_mem_uIcc
    rwa [Set.uIcc_of_le ht] at this
  have : ContinuousOn (fun s => x + ∫ r in t₀..s,
      S.f q (hflow.flow t₀ q x r) r) (Set.Icc t₀ t₁) := continuousOn_const.add hprim
  refine this.congr ?_
  intro s hs
  exact hflow.flow_eq_intervalIntegral S t₀ q x hs.1

/-- The flow is continuous on the whole future `[t₀, ∞)` when the drift along
the trajectory is continuous on every compact subinterval. -/
theorem HasGlobalFlow.continuousOn_flow_Ici (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (t₀ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (hcont : ∀ t₁, ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s)
      (Set.Icc t₀ t₁)) :
    ContinuousOn (hflow.flow t₀ q x) (Set.Ici t₀) := by
  intro s hs
  have hs' : t₀ ≤ s := Set.mem_Ici.mp hs
  have hIcc := hflow.continuousOn_flow S t₀ (s + 1) (by linarith) q x (hcont _)
  have hwithin := hIcc s ⟨hs', by linarith⟩
  refine hwithin.mono_of_mem_nhdsWithin ?_
  have hIio : Set.Iio (s + 1) ∈ 𝓝 s :=
    isOpen_Iio.mem_nhds (Set.mem_Iio.mpr (by linarith))
  filter_upwards [mem_nhdsWithin_of_mem_nhds hIio, self_mem_nhdsWithin] with u hu hu'
  exact ⟨hu', le_of_lt hu⟩

/-- **Differential form of the ODE.** At an interior time of `[t₀, t₁]`, where
the drift along the trajectory is continuous, the flow is differentiable with
derivative the drift. -/
theorem HasGlobalFlow.hasDerivAt_flow (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (t₀ t₁ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s)
      (Set.Icc t₀ t₁))
    {s : ℝ} (hs : s ∈ Set.Ioo t₀ t₁) :
    HasDerivAt (hflow.flow t₀ q x) (S.f q (hflow.flow t₀ q x s) s) s := by
  have hle : t₀ ≤ t₁ := le_of_lt (lt_trans hs.1 hs.2)
  have hint : IntervalIntegrable (fun r => S.f q (hflow.flow t₀ q x r) r)
      volume t₀ t₁ :=
    (hcont.mono (by rw [Set.uIcc_of_le hle])).intervalIntegrable
  have hcontAt : ContinuousAt (fun r => S.f q (hflow.flow t₀ q x r) r) s :=
    (hcont.mono Set.Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds hs)
  have hFTC : HasDerivAt (fun u => ∫ r in t₀..u, S.f q (hflow.flow t₀ q x r) r)
      (S.f q (hflow.flow t₀ q x s) s) s := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ hcontAt
    · exact hint.mono_set (by
        rw [Set.uIcc_of_le hle, Set.uIcc_of_le hs.1.le]
        exact Set.Icc_subset_Icc le_rfl hs.2.le)
    · exact ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo t₀ t₁)
        isOpen_Ioo (fun r hr =>
          (hcont.mono Set.Ioo_subset_Icc_self).continuousAt
            (isOpen_Ioo.mem_nhds hr)) s hs
  have hFTC' : HasDerivAt
      (fun u => x + ∫ r in t₀..u, S.f q (hflow.flow t₀ q x r) r)
      (S.f q (hflow.flow t₀ q x s) s) s := by
    simpa using hFTC.const_add x
  refine hFTC'.congr_of_eventuallyEq ?_
  have hnhds : Set.Ioi t₀ ∈ 𝓝 s := isOpen_Ioi.mem_nhds hs.1
  filter_upwards [hnhds] with u hu
  exact hflow.flow_eq_intervalIntegral S t₀ q x (le_of_lt hu)

/-! ## `C¹` test functions -/

/-- A test function whose recorded gradient and time derivative are the genuine
partial derivatives of `toFun`: for every mode `q` the map
`(x, t) ↦ ψ(q, x, t)` is (Fréchet) differentiable with derivative
`(v, h) ↦ ⟪∇ₓψ, v⟫ + h · ∂ₜψ`. -/
def TestFunction.HasPartials (ψ : TestFunction Q n) : Prop :=
  ∀ q x t, HasFDerivAt (fun p : EuclideanSpace ℝ (Fin n) × ℝ => ψ.toFun q p.1 p.2)
    ((innerSL ℝ (ψ.grad_x q x t)).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      (ψ.partial_t q x t) •
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)) (x, t)

/-- A test function with genuine partial derivatives is continuous in the
continuous state and the time. -/
theorem TestFunction.HasPartials.continuous {ψ : TestFunction Q n}
    (hψ : ψ.HasPartials) (q : Q) :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => ψ.toFun q p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  exact ((hψ q p.1 p.2).differentiableAt.continuousAt).congr (by simp)

/-- The chain rule along the flow: `s ↦ ψ(q, φ(s), s)` is differentiable with
derivative the flow generator evaluated at the augmented state. -/
theorem hasDerivAt_testFun_along_flow (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (ψ : TestFunction Q n) (hψ : ψ.HasPartials)
    (t₀ t₁ : ℝ) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s)
      (Set.Icc t₀ t₁))
    {s : ℝ} (hs : s ∈ Set.Ioo t₀ t₁) :
    HasDerivAt (fun r => ψ.toFun q (hflow.flow t₀ q x r) r)
      (S.flowGenerator ψ (q, hflow.flow t₀ q x s, s)) s := by
  have hcurve : HasDerivAt
      (fun r => (hflow.flow t₀ q x r, r))
      (S.f q (hflow.flow t₀ q x s) s, (1 : ℝ)) s :=
    (hflow.hasDerivAt_flow S t₀ t₁ q x hcont hs).prodMk (hasDerivAt_id s)
  have := HasFDerivAt.comp_hasDerivAt (f := fun r => (hflow.flow t₀ q x r, r))
    s (hψ q (hflow.flow t₀ q x s) s) hcurve
  simpa [SHS.flowGenerator, real_inner_comm] using this

/-! ## The deterministic Dynkin identity -/

/-- **Deterministic Dynkin identity (Newton–Leibniz along the flow).**
For a `C¹` test function and a drift that is continuous along the trajectory,

`ψ(q, φ(t₁), t₁) − ψ(q, x, t₀) = ∫_{t₀}^{t₁} (Lᶠψ)(q, φ(s), s) ds`,

where `Lᶠψ = ⟪∇ₓψ, f⟫ + ∂ₜψ` is the flow (drift) part of the generator. -/
theorem flow_dynkin_identity (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (ψ : TestFunction Q n) (hψ : ψ.HasPartials)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (q : Q) (x : EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn (fun s => S.f q (hflow.flow t₀ q x s) s)
      (Set.Icc t₀ t₁))
    (hgen : IntervalIntegrable
      (fun s => S.flowGenerator ψ (q, hflow.flow t₀ q x s, s)) volume t₀ t₁) :
    ψ.toFun q (hflow.flow t₀ q x t₁) t₁ - ψ.toFun q x t₀ =
      ∫ s in t₀..t₁, S.flowGenerator ψ (q, hflow.flow t₀ q x s, s) := by
  have hGcont : ContinuousOn (fun r => ψ.toFun q (hflow.flow t₀ q x r) r)
      (Set.Icc t₀ t₁) := by
    have hflowcont := hflow.continuousOn_flow S t₀ t₁ ht q x hcont
    exact (hψ.continuous q).comp_continuousOn (hflowcont.prodMk continuousOn_id)
  have hderiv : ∀ s ∈ Set.Ioo t₀ t₁,
      HasDerivAt (fun r => ψ.toFun q (hflow.flow t₀ q x r) r)
        (S.flowGenerator ψ (q, hflow.flow t₀ q x s, s)) s :=
    fun s hs => hasDerivAt_testFun_along_flow S hflow ψ hψ t₀ t₁ q x hcont hs
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hGcont
    (fun s hs => (hderiv s hs).hasDerivWithinAt) hgen
  rw [this, hflow.flow_init t₀ q x]

end SHS
