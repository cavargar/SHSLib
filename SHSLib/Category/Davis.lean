/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Davis PDPs in the categorical organization

* `Davis.genPres p` — the generator presentation of a PDP: test functions are
  measurable `f` together with their (right) derivative `Xf` along the flow,
  and the generator is Davis's (26.15), `pdpGenerator p Xf f`.  By definition
  it is the Lévy presentation `Davis.levyData p` (identity landing map).
* `Davis.PDPSys` — the category of PDPs with *conjugacies of local
  characteristics*: measurable maps commuting with the flows, preserving jump
  rates and pushing transition measures forward.  `Davis.PDPSys.toGenPresFunctor`
  is a functor `PDPSys ⥤ GenPres`: such maps intertwine the extended generators,
  so results transfer along them.
* `Davis.finiteSemigroup` — on a finite state space the renewal-defined
  semigroup `pdpSemigroup` of a standard PDP is a transition semigroup in the
  sense of Bujorianu–Lygeros, hence an object of `SemigroupSys`.  Results proved
  for abstract transition semigroups (Bujorianu's Dynkin formula, resolvent
  excessiveness) then hold for the Davis semigroup; we record the Dynkin formula
  and the identification of the two resolvents.
-/
import SHSLib.Category.Levy
import SHSLib.Category.Semigroup
import SHSLib.Foundations.DavisCh2FiniteProcess

open CategoryTheory MeasureTheory Set Filter
open scoped ENNReal NNReal

universe u

noncomputable section

namespace Davis

open SHSCat

section GenPres

variable {E : Type u} [MeasurableSpace E]

/-- `Xf` is the right derivative of `f` along the flow of `p`, at every state:
`d⁺/du f(φ_u z)|_{u=0} = Xf(z)`.  (Since `Ici 0` has unique derivatives at `0`,
`Xf` is determined by `f`.) -/
def IsFlowDerivative (p : PDP E) (f Xf : E → ℝ) : Prop :=
  ∀ z : E, HasDerivWithinAt (fun u : ℝ => f (p.flow u.toNNReal z)) (Xf z) (Ici 0) 0

/-- The flow derivative of a function is unique. -/
theorem IsFlowDerivative.unique {p : PDP E} {f Xf Yf : E → ℝ}
    (h₁ : IsFlowDerivative p f Xf) (h₂ : IsFlowDerivative p f Yf) : Xf = Yf := by
  funext z
  exact (uniqueDiffOn_Ici (0 : ℝ) 0 self_mem_Ici).eq_deriv _ (h₁ z) (h₂ z)

/-- A test function for the Davis extended generator: a measurable function
together with its derivative along the flow. -/
@[ext]
structure GenTest (p : PDP E) : Type u where
  /-- The function. -/
  f : E → ℝ
  /-- Its derivative along the flow (the vector field `𝔛f` of (26.15)). -/
  Xf : E → ℝ
  measurable : Measurable f
  flowDeriv : IsFlowDerivative p f Xf

/-- The Lévy-system data of a PDP: drift `𝔛f`, rate `λ`, post-jump law `Q`. -/
def levyData (p : PDP E) : LevyData.{u} where
  State := E
  Jump := E
  instJump := ‹_›
  Test := GenTest p
  ev := fun φ => φ.f
  drift := fun φ => φ.Xf
  rate := fun x => (p.jumpRate x : ℝ)
  jump := fun x => p.transitionMeasure x
  land := fun _ y => y

/-- **The generator presentation of a Davis PDP** (Davis (26.15)). -/
def genPres (p : PDP E) : GenPres.{u} := (levyData p).toGenPres

@[simp] theorem genPres_State (p : PDP E) : (genPres p).State = E := rfl

@[simp] theorem genPres_ev (p : PDP E) (φ : GenTest p) (x : E) :
    (genPres p).ev φ x = φ.f x := rfl

/-- The generator of `genPres p` is Davis's extended generator formula. -/
theorem genPres_gen (p : PDP E) (φ : GenTest p) (x : E) :
    (genPres p).gen φ x = pdpGenerator p φ.Xf φ.f x := rfl

end GenPres

/-! ### The category of PDPs and conjugacies -/

/-- A PDP bundled with its measurable state space. -/
structure PDPSys : Type (u + 1) where
  /-- The state space. -/
  E : Type u
  /-- Its σ-algebra. -/
  inst : MeasurableSpace E
  /-- The PDP. -/
  pdp : @PDP E inst

attribute [instance] PDPSys.inst

namespace PDPSys

/-- A **conjugacy of local characteristics**: a measurable map commuting with
the flows, preserving jump rates and pushing the transition measures forward. -/
@[ext]
structure Hom (A B : PDPSys.{u}) : Type u where
  /-- The map of state spaces. -/
  toFun : A.E → B.E
  measurable : Measurable toFun
  flow_comm : ∀ (t : ℝ≥0) (x : A.E), B.pdp.flow t (toFun x) = toFun (A.pdp.flow t x)
  jumpRate_comp : ∀ x : A.E, B.pdp.jumpRate (toFun x) = A.pdp.jumpRate x
  transition_map : ∀ x : A.E,
    B.pdp.transitionMeasure (toFun x) = (A.pdp.transitionMeasure x).map toFun

instance : LargeCategory PDPSys.{u} where
  Hom := Hom
  id A := ⟨fun x => x, measurable_id, fun _ _ => rfl, fun _ => rfl,
    fun x => (Measure.map_id).symm⟩
  comp F G := ⟨fun x => G.toFun (F.toFun x), G.measurable.comp F.measurable,
    fun t x => by rw [G.flow_comm, F.flow_comm],
    fun x => by rw [G.jumpRate_comp, F.jumpRate_comp],
    fun x => by
      rw [G.transition_map, F.transition_map, Measure.map_map G.measurable F.measurable]
      rfl⟩

@[simp] theorem id_toFun (A : PDPSys.{u}) (x : A.E) : (𝟙 A : A ⟶ A).toFun x = x := rfl

@[simp] theorem comp_toFun {A B C : PDPSys.{u}} (F : A ⟶ B) (G : B ⟶ C) (x : A.E) :
    (F ≫ G).toFun x = G.toFun (F.toFun x) := rfl

/-- Pull a Davis test function back along a conjugacy. -/
def Hom.pullTest {A B : PDPSys.{u}} (F : A ⟶ B) (φ : GenTest B.pdp) : GenTest A.pdp where
  f := fun x => φ.f (F.toFun x)
  Xf := fun x => φ.Xf (F.toFun x)
  measurable := φ.measurable.comp F.measurable
  flowDeriv := by
    intro z
    have h := φ.flowDeriv (F.toFun z)
    have heq : (fun u : ℝ => φ.f (B.pdp.flow u.toNNReal (F.toFun z)))
        = fun u : ℝ => φ.f (F.toFun (A.pdp.flow u.toNNReal z)) := by
      funext u; rw [F.flow_comm]
    rw [heq] at h
    exact h

/-- **Conjugacies intertwine the Davis extended generators.** -/
theorem Hom.pdpGenerator_pull {A B : PDPSys.{u}} (F : A ⟶ B) (φ : GenTest B.pdp) (x : A.E) :
    pdpGenerator A.pdp (fun y => φ.Xf (F.toFun y)) (fun y => φ.f (F.toFun y)) x
      = pdpGenerator B.pdp φ.Xf φ.f (F.toFun x) := by
  simp only [pdpGenerator]
  rw [F.jumpRate_comp, F.transition_map,
    integral_map F.measurable.aemeasurable φ.measurable.aestronglyMeasurable]

/-- **The functor from PDPs to generator presentations.** -/
def toGenPresFunctor : PDPSys.{u} ⥤ GenPres.{u} where
  obj A := genPres A.pdp
  map {A B} F :=
    { map := F.toFun
      pull := F.pullTest
      ev_pull := fun _ _ => rfl
      gen_pull := fun φ x => F.pdpGenerator_pull φ x }

@[simp] theorem toGenPresFunctor_obj (A : PDPSys.{u}) :
    toGenPresFunctor.obj A = genPres A.pdp := rfl

@[simp] theorem toGenPresFunctor_map_map {A B : PDPSys.{u}} (F : A ⟶ B) (x : A.E) :
    (toGenPresFunctor.map F).map x = F.toFun x := rfl

end PDPSys

/-! ### The finite-state Davis semigroup as a transition semigroup -/

section Finite

variable {E : Type u} [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]

/-- The regularity hypotheses under which the renewal semigroup of a standard
PDP is a genuine semigroup of positive linear operators (the hypotheses of
`pdpSemigroup_semigroup_property`). -/
structure FiniteRegular (pdp : PDPStandard E) : Prop where
  flow_measurable : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2)
  rate_bounded : ∃ c : ℝ≥0, ∀ y, pdp.jumpRate y ≤ c
  rate_continuous : ∀ y, Continuous (fun s : ℝ => (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ))

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
private theorem finite_bdd (g : E → ℝ) : ∃ C : ℝ, ∀ x, |g x| ≤ C :=
  ⟨∑ y : E, |g y|, fun x => Finset.single_le_sum (fun y _ => abs_nonneg (g y))
    (Finset.mem_univ x)⟩

omit [Fintype E] in
private theorem finite_meas [Finite E] (g : E → ℝ) : Measurable g := by
  have : Countable E := Finite.to_countable
  exact measurable_of_countable g

/-- **The Davis renewal semigroup of a finite standard PDP as a transition
semigroup** (Bujorianu–Lygeros, Section 3.2).  Time `t ∈ ℝ` acts through
`t.toNNReal`. -/
def finiteSemigroup (pdp : PDPStandard E) (h : FiniteRegular pdp) :
    Bujorianu2006.TransitionSemigroup E where
  P := fun t g x => pdpSemigroup pdp.toPDP t.toNNReal g x
  P_zero := fun g x => by simp [pdpSemigroup_zero]
  P_add := fun s t g x hs ht => by
    obtain ⟨c, hc⟩ := h.rate_bounded
    rw [Real.toNNReal_add hs ht,
      pdpSemigroup_semigroup_property pdp g (finite_meas g) (finite_bdd g) h.flow_measurable c
        hc h.rate_continuous]
  P_nonneg := fun t g x _ hg => by
    obtain ⟨c, hc⟩ := h.rate_bounded
    exact pdpSemigroup_nonneg pdp g (finite_meas g) (finite_bdd g) h.flow_measurable c hc
      h.rate_continuous hg _ x
  P_sub := fun t g k => by
    obtain ⟨c, hc⟩ := h.rate_bounded
    funext x
    exact pdpSemigroup_sub pdp g k (finite_meas g) (finite_bdd g) (finite_meas k) (finite_bdd k)
      h.flow_measurable c hc h.rate_continuous _ x
  P_const_mul := fun t a g => by
    obtain ⟨c, hc⟩ := h.rate_bounded
    funext x
    exact pdpSemigroup_smul pdp a g (finite_meas g) (finite_bdd g) h.flow_measurable c hc
      h.rate_continuous _ x

/-- The finite Davis semigroup as an object of `SemigroupSys`. -/
def finiteSemigroupSys (pdp : PDPStandard E) (h : FiniteRegular pdp) : SemigroupSys.{u} :=
  ⟨E, finiteSemigroup pdp h⟩

@[simp] theorem finiteSemigroup_P (pdp : PDPStandard E) (h : FiniteRegular pdp) (t : ℝ)
    (g : E → ℝ) (x : E) :
    (finiteSemigroup pdp h).P t g x = pdpSemigroup pdp.toPDP t.toNNReal g x := rfl

/-- Bujorianu's resolvent of the finite Davis semigroup is Davis's resolvent
`pdpResolvent`. -/
theorem finiteSemigroup_resolvent (pdp : PDPStandard E) (h : FiniteRegular pdp)
    (alpha : ℝ≥0) (g : E → ℝ) (x : E) :
    (finiteSemigroup pdp h).resolvent alpha g x = pdpResolvent pdp.toPDP alpha g x := by
  unfold Bujorianu2006.TransitionSemigroup.resolvent pdpResolvent
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [finiteSemigroup_P, neg_mul]

/-- **Bujorianu's resolvent excessiveness, transferred to Davis's resolvent**:
for a nonnegative `g`, `e^{-αt} P_t (U^α g) ≤ U^α g` for the finite Davis
semigroup, given the integrability of the resolvent integrand and the
interchange of `P_t` with the resolvent integral. -/
theorem finite_pdpResolvent_excessive (pdp : PDPStandard E) (h : FiniteRegular pdp)
    (alpha : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) (g : E → ℝ) (x : E) (hg : ∀ y, 0 ≤ g y)
    (hint : IntegrableOn (fun u => Real.exp (-((alpha : ℝ) * u)) *
      (finiteSemigroup pdp h).P u g x) (Ioi (0 : ℝ)))
    (hcomm : (finiteSemigroup pdp h).P t (fun y => ∫ s in Ioi (0 : ℝ),
        Real.exp (-((alpha : ℝ) * s)) * (finiteSemigroup pdp h).P s g y) x
      = ∫ s in Ioi (0 : ℝ), Real.exp (-((alpha : ℝ) * s)) *
        (finiteSemigroup pdp h).P t ((finiteSemigroup pdp h).P s g) x) :
    Real.exp (-((alpha : ℝ) * t)) *
        pdpSemigroup pdp.toPDP t.toNNReal (pdpResolvent pdp.toPDP alpha g) x
      ≤ pdpResolvent pdp.toPDP alpha g x := by
  have hres : pdpResolvent pdp.toPDP alpha g = (finiteSemigroup pdp h).resolvent alpha g := by
    funext y; rw [finiteSemigroup_resolvent]
  have := Bujorianu2006.TransitionSemigroup.resolvent_excessive (S := finiteSemigroup pdp h)
    alpha t g x ht hg hint hcomm
  rw [hres]
  exact this

/-- **Bujorianu's Dynkin formula, transferred to the finite Davis semigroup**:
`P_t f(x) − f(x) = ∫₀ᵗ P_s(Lf)(x) ds`, in Davis's notation `pdpSemigroup`. -/
theorem finite_pdpSemigroup_dynkin (pdp : PDPStandard E) (h : FiniteRegular pdp)
    {f Lf : E → ℝ} (t : ℝ) (ht : 0 ≤ t) (x : E)
    (hcont : ContinuousOn (fun u : ℝ => pdpSemigroup pdp.toPDP u.toNNReal f x) (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivWithinAt (fun u : ℝ => pdpSemigroup pdp.toPDP u.toNNReal f x)
      (pdpSemigroup pdp.toPDP s.toNNReal Lf x) (Ioi s) s)
    (hint : IntervalIntegrable (fun s : ℝ => pdpSemigroup pdp.toPDP s.toNNReal Lf x) volume 0 t) :
    pdpSemigroup pdp.toPDP t.toNNReal f x - f x
      = ∫ s in (0 : ℝ)..t, pdpSemigroup pdp.toPDP s.toNNReal Lf x :=
  Bujorianu2006.TransitionSemigroup.dynkin_formula (S := finiteSemigroup pdp h) t ht x
    hcont hderiv hint

/-- **Bujorianu's Kolmogorov forward equation, transferred to the finite Davis
semigroup**: if `P_t` commutes with the limit defining `Lf`, then
`u ↦ P_u f(x)` has right derivative `P_t(Lf)(x)` at `t`. -/
theorem finite_pdpSemigroup_hasDeriv (pdp : PDPStandard E) (h : FiniteRegular pdp)
    {f Lf : E → ℝ} (t : ℝ) (ht : 0 ≤ t) (x : E)
    (hcomm : Tendsto (fun s : ℝ => (finiteSemigroup pdp h).P t
        (fun y => ((finiteSemigroup pdp h).P s f y - f y) / s) x)
      (nhdsWithin 0 (Ioi 0)) (nhds ((finiteSemigroup pdp h).P t Lf x))) :
    HasDerivWithinAt (fun u : ℝ => pdpSemigroup pdp.toPDP u.toNNReal f x)
      (pdpSemigroup pdp.toPDP t.toNNReal Lf x) (Ioi t) t :=
  Bujorianu2006.TransitionSemigroup.hasDerivWithinAt_semigroup (S := finiteSemigroup pdp h)
    t ht x hcomm

end Finite

end Davis
