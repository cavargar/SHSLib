import SHSLib.Core.DavisObservableCounter

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Canonical jump-counter augmentation

This module turns any SHS with mode space `Q` into an SHS with mode space
`Q × ℕ`.  The added coordinate is constant along deterministic flow and is
incremented by every reset.  Thus the lifted process satisfies
`ModeJumpCounter` canonically, without a model-specific rank proof.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Add a cumulative reset counter to the discrete mode of an SHS. -/
def withJumpCounter (S : SHS Q n m) : SHS (Q × ℕ) n m where
  f := fun qc x t => S.f qc.1 x t
  phi := fun ℓ qc x t => ((S.phi_q ℓ qc.1 x t, qc.2 + 1), S.phi_x ℓ qc.1 x t)
  intensity := fun ℓ qc x t => S.intensity ℓ qc.1 x t
  intensity_nonneg := fun ℓ qc x t => S.intensity_nonneg ℓ qc.1 x t

/-- Lift an initial augmented Davis state by setting its reset counter to zero. -/
def withJumpCounterInitial (initial : DavisState Q n) : DavisState (Q × ℕ) n :=
  ((initial.1, 0), initial.2.1, initial.2.2)

/-- A global flow for the original SHS lifts by leaving the counter fixed. -/
def withJumpCounterGlobalFlow (S : SHS Q n m) (hflow : S.HasGlobalFlow) :
    (S.withJumpCounter).HasGlobalFlow where
  flow := fun t₀ qc x t => hflow.flow t₀ qc.1 x t
  flow_init := fun t₀ qc x => hflow.flow_init t₀ qc.1 x
  flow_ode := by
    intro t₀ qc x t
    exact hflow.flow_ode t₀ qc.1 x t

/-- Measurability of the original intensities is preserved by counter
augmentation. -/
instance withJumpCounter_intensitiesMeasurable
    (S : SHS Q n m) [S.IntensitiesMeasurable] :
    S.withJumpCounter.IntensitiesMeasurable := by
  constructor
  intro ℓ
  have h : Measurable (fun p : Q × EuclideanSpace ℝ (Fin n) × ℝ => S.intensity ℓ p.1 p.2.1 p.2.2) :=
    IntensitiesMeasurable.measurable ℓ
  let g : (Q × ℕ) × (EuclideanSpace ℝ (Fin n) × ℝ) → Q × EuclideanSpace ℝ (Fin n) × ℝ :=
    fun p => (p.1.1, p.2)
  have hg : Measurable g := by measurability
  have heq : (fun p : (Q × ℕ) × (EuclideanSpace ℝ (Fin n) × ℝ) =>
              S.withJumpCounter.intensity ℓ p.1 p.2.1 p.2.2) =
             (fun p : Q × EuclideanSpace ℝ (Fin n) × ℝ => S.intensity ℓ p.1 p.2.1 p.2.2) ∘ g := by
    funext p
    simp only [SHS.withJumpCounter]
    rfl
  rw [heq]
  exact h.comp hg

/-- Joint flow measurability and the restart law lift to the counter-augmented
system. -/
theorem withJumpCounter_globalFlowRegular
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hreg : DavisGlobalFlowRegular S hflow) :
    DavisGlobalFlowRegular S.withJumpCounter
      (withJumpCounterGlobalFlow S hflow) := by
  refine ⟨?measurable_flow, ?restart⟩
  case measurable_flow =>
    unfold withJumpCounterGlobalFlow
    simp only
    have map_meas : Measurable (fun p : ℝ × (Q × ℕ) × EuclideanSpace ℝ (Fin n) × ℝ =>
        (p.1, p.2.1.1, p.2.2.1, p.2.2.2)) := by fun_prop
    convert hreg.measurable_flow.comp map_meas
  case restart =>
    intro t₀ q x t u
    unfold withJumpCounterGlobalFlow
    exact hreg.restart t₀ q.1 x t u

/-- Coordinatewise measurable resets of the original model give regular
resets of the counter augmentation.  The added coordinate makes every reset
nontrivial, independently of what the original reset does. -/
theorem withJumpCounter_resetRegular
    (S : SHS Q n m)
    (hq : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_q ℓ z.1 z.2.1 z.2.2))
    (hx : ∀ ℓ : Fin m, Measurable (fun z : DavisState Q n =>
      S.phi_x ℓ z.1 z.2.1 z.2.2)) :
    DavisResetRegular S.withJumpCounter := by
  refine ⟨?_, ?_⟩
  · intro ℓ
    simp only [withJumpCounter]
    exact Measurable.prodMk
      (Measurable.prodMk
        ((hq ℓ).comp (Measurable.prodMk measurable_fst.fst
          (Measurable.prodMk measurable_snd.fst measurable_snd.snd)))
        (measurable_fst.snd.add_const 1))
      (Measurable.prodMk
        ((hx ℓ).comp (Measurable.prodMk measurable_fst.fst
          (Measurable.prodMk measurable_snd.fst measurable_snd.snd)))
        measurable_snd.snd)
  · intro ℓ z hint heq
    have hc := congrArg (fun y : DavisState (Q × ℕ) n => y.1.2) heq
    change z.1.2 + 1 = z.1.2 at hc
    omega

/-- The second mode coordinate is the canonical mode-level jump counter. -/
def withJumpCounter_modeJumpCounter
    (S : SHS Q n m) (initial : DavisState Q n) :
    ModeJumpCounter S.withJumpCounter (withJumpCounterInitial initial) where
  count := Prod.snd
  measurable_count := measurable_snd
  count_initial := rfl
  count_reset := by
    intro ℓ q x t
    rfl

/-- For the counter-augmented system, all cumulative jump times are stopping
times for the natural path filtration. -/
theorem withJumpCounter_jumpTime_isStoppingTime_natural
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S.withJumpCounter
      (withJumpCounterGlobalFlow S hflow))
    (hr : DavisResetRegular S.withJumpCounter)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (k : ℕ) :
    IsStoppingTime
      (ξ.naturalPathFiltration S.withJumpCounter
        (withJumpCounterGlobalFlow S hflow) hf hr hξ hne
        (withJumpCounterInitial initial))
      (fun ω => ((ξ.jumpTime k ω : ℝ≥0) : ℝ≥0∞)) := by
  exact (withJumpCounter_modeJumpCounter S initial).jumpTime_isStoppingTime_natural
    S.withJumpCounter (withJumpCounterGlobalFlow S hflow) hf hr hξ hne
    (withJumpCounterInitial initial) k

end SHS
