import SHSLib.Core.DavisConditionalHoldingRandomThreshold
import SHSLib.Core.DavisObservableCounter

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The observation filtration of the marked jump history

All the conditional laws of the segment theory are proved on events of the
*discrete* pre-jump history filtration, indexed by the jump number.  The
conditional step law of the one-segment martingale, on the other hand, asks for
identities on the events of a *continuous-time* filtration, indexed by elapsed
time.  This module builds the filtration the marked jump history produces and
shows that its events are exactly the ones the discrete theory can handle.

An observer who watches the marked jump history up to time `s` knows how many
jumps have occurred, when they occurred and which marks they carried, and knows
nothing about the segment currently running beyond the fact that it is still
running.  Formally, an event `A` is observable at time `s` when, for every jump
index `N`, its trace on the event that segment `N` is the active one at `s`
agrees with the trace of an event of the pre-jump history at index `N` on which
that segment has already started:

`A ∩ {segment N active at s} = B ∩ {segment N active at s}`,
`B ∈ ℋ_N`, `B ⊆ {T_N ≤ s}`.

This module proves that the collection of such events is a σ-algebra, that it
is contained in the ambient one (the active events cover the sample space, by
non-explosion), and that it increases with `s` — the last point being the only
delicate one: the trace of an observable event on the event that segment `N` is
active at the *later* time `t` is reassembled from the traces on the events
that segments `k ≤ N` are active at `s`, which the active index at `s` selects.

The resulting `Filtration ℝ≥0` is the one the conditional step law is verified
for in the next module.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The active event of a segment -/

/-- The event that segment `N` is the one running at elapsed time `s`. -/
def DavisJumpNoise.activeEvent {m : ℕ} {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (N : ℕ) (s : ℝ≥0) : Set Ω :=
  {ω | ξ.jumpTime N ω ≤ s ∧ ¬ ξ.jumpTime (N + 1) ω ≤ s}

theorem DavisJumpNoise.mem_activeEvent_iff {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (N : ℕ) (s : ℝ≥0) (ω : Ω) :
    ω ∈ ξ.activeEvent N s ↔
      ξ.jumpTime N ω ≤ s ∧ ¬ ξ.jumpTime (N + 1) ω ≤ s := Iff.rfl

theorem DavisJumpNoise.jumpTime_le_of_mem_activeEvent {m : ℕ} {Ω : Type*}
    {ξ : DavisJumpNoise m Ω} {N : ℕ} {s : ℝ≥0} {ω : Ω}
    (hω : ω ∈ ξ.activeEvent N s) : ξ.jumpTime N ω ≤ s := hω.1

theorem DavisJumpNoise.MeasurableNoise.measurableSet_activeEvent {m : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (N : ℕ) (s : ℝ≥0) :
    MeasurableSet (ξ.activeEvent N s) := by
  unfold DavisJumpNoise.activeEvent
  exact (measurableSet_le (hξ.jumpTime N) measurable_const).inter
    (measurableSet_le (hξ.jumpTime (N + 1)) measurable_const).compl

/-- The event that segment `N` has started by `s` belongs to the pre-jump
history at index `N`. -/
theorem DavisJumpNoise.measurableSet_jumpTime_le_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k N : ℕ) (hkN : k ≤ N)
    (s : ℝ≥0) :
    MeasurableSet[ξ.preJumpHistorySpace S hflow initial N]
      {ω | ξ.jumpTime k ω ≤ s} := by
  have h : Measurable[ξ.preJumpHistorySpace S hflow initial N] (ξ.jumpTime k) :=
    (ξ.measurable_jumpTime_preJumpHistory S hflow hf hr hξ initial k).mono
      (ξ.preJumpHistorySpace_mono S hflow initial hkN) le_rfl
  exact measurableSet_le h measurable_const

/-- The active event of segment `k` belongs to the pre-jump history at any
index past `k`. -/
theorem DavisJumpNoise.measurableSet_activeEvent_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k N : ℕ)
    (hkN : k + 1 ≤ N) (s : ℝ≥0) :
    MeasurableSet[ξ.preJumpHistorySpace S hflow initial N]
      (ξ.activeEvent k s) := by
  unfold DavisJumpNoise.activeEvent
  exact (ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial k N
      (le_trans (Nat.le_succ k) hkN) s).inter
    (ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial
      (k + 1) N hkN s).compl

/-- The active event of segment `N` selects the active segment index. -/
theorem DavisJumpNoise.mem_activeEvent_iff_activeSegmentIndex {m : ℕ}
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive) (N : ℕ)
    (s : ℝ≥0) (ω : Ω) :
    ω ∈ ξ.activeEvent N s ↔ ξ.activeSegmentIndex hne s ω = N := by
  rw [DavisJumpNoise.mem_activeEvent_iff,
    ξ.jumpTime_le_iff_le_activeSegmentIndex hne N s ω,
    ξ.jumpTime_le_iff_le_activeSegmentIndex hne (N + 1) s ω]
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · rintro rfl
    exact ⟨le_rfl, by omega⟩

/-- At each time every sample point lies in exactly one active event. -/
theorem DavisJumpNoise.activeEvent_unique {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive) {N N' : ℕ} {s : ℝ≥0}
    {ω : Ω} (h : ω ∈ ξ.activeEvent N s) (h' : ω ∈ ξ.activeEvent N' s) :
    N = N' := by
  rw [ξ.mem_activeEvent_iff_activeSegmentIndex hne] at h h'
  rw [← h, ← h']

/-- The active events cover the sample space. -/
theorem DavisJumpNoise.mem_activeEvent_activeSegmentIndex {m : ℕ} {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive) (s : ℝ≥0) (ω : Ω) :
    ω ∈ ξ.activeEvent (ξ.activeSegmentIndex hne s ω) s :=
  (ξ.mem_activeEvent_iff_activeSegmentIndex hne _ s ω).2 rfl

/-! ## The observation σ-algebra -/

/-- An event is observable from the marked jump history at time `s` when, on
the event that segment `N` is active at `s`, it agrees with a pre-jump history
event at index `N` on which the segment has started. -/
def DavisJumpNoise.MarkedJumpObservable (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (s : ℝ≥0) (A : Set Ω) : Prop :=
  ∀ N : ℕ, ∃ B : Set Ω,
    MeasurableSet[ξ.preJumpHistorySpace S hflow initial N] B ∧
      (∀ ω ∈ B, ξ.jumpTime N ω ≤ s) ∧
      A ∩ ξ.activeEvent N s = B ∩ ξ.activeEvent N s

/-- The observable events at a fixed time form a σ-algebra. -/
def DavisJumpNoise.markedJumpSpace (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (s : ℝ≥0) :
    MeasurableSpace Ω where
  MeasurableSet' A := ξ.MarkedJumpObservable S hflow initial s A
  measurableSet_empty := fun N =>
    ⟨∅, @MeasurableSet.empty Ω (ξ.preJumpHistorySpace S hflow initial N),
      by simp, by simp⟩
  measurableSet_compl := by
    intro A hA N
    obtain ⟨B, hBmeas, hBstart, hBeq⟩ := hA N
    refine ⟨{ω | ξ.jumpTime N ω ≤ s} \ B, ?_, ?_, ?_⟩
    · exact (ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial
        N N le_rfl s).diff hBmeas
    · exact fun ω hω => hω.1
    · ext ω
      constructor
      · rintro ⟨hωA, hωact⟩
        refine ⟨⟨hωact.1, ?_⟩, hωact⟩
        intro hωB
        exact hωA (by
          have : ω ∈ B ∩ ξ.activeEvent N s := ⟨hωB, hωact⟩
          exact (hBeq ▸ this : ω ∈ A ∩ ξ.activeEvent N s).1)
      · rintro ⟨⟨-, hωB⟩, hωact⟩
        refine ⟨?_, hωact⟩
        intro hωA
        exact hωB (by
          have : ω ∈ A ∩ ξ.activeEvent N s := ⟨hωA, hωact⟩
          exact (hBeq ▸ this : ω ∈ B ∩ ξ.activeEvent N s).1)
  measurableSet_iUnion := by
    intro f hf' N
    choose B hBmeas hBstart hBeq using fun i => hf' i N
    refine ⟨⋃ i, B i, MeasurableSet.iUnion hBmeas, ?_, ?_⟩
    · rintro ω hω
      obtain ⟨i, hωi⟩ := Set.mem_iUnion.mp hω
      exact hBstart i ω hωi
    · ext ω
      constructor
      · rintro ⟨hωU, hωact⟩
        obtain ⟨i, hωi⟩ := Set.mem_iUnion.mp hωU
        refine ⟨Set.mem_iUnion.mpr ⟨i, ?_⟩, hωact⟩
        have : ω ∈ f i ∩ ξ.activeEvent N s := ⟨hωi, hωact⟩
        exact (hBeq i ▸ this : ω ∈ B i ∩ ξ.activeEvent N s).1
      · rintro ⟨hωU, hωact⟩
        obtain ⟨i, hωi⟩ := Set.mem_iUnion.mp hωU
        refine ⟨Set.mem_iUnion.mpr ⟨i, ?_⟩, hωact⟩
        have : ω ∈ B i ∩ ξ.activeEvent N s := ⟨hωi, hωact⟩
        exact ((hBeq i).symm ▸ this : ω ∈ f i ∩ ξ.activeEvent N s).1

theorem DavisJumpNoise.measurableSet_markedJumpSpace_iff
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (s : ℝ≥0) (A : Set Ω) :
    MeasurableSet[ξ.markedJumpSpace S hflow hf hr hξ initial s] A ↔
      ξ.MarkedJumpObservable S hflow initial s A := Iff.rfl

/-- Observable events are ambient measurable: they are the countable union of
their traces on the active events, which cover the sample space. -/
theorem DavisJumpNoise.markedJumpSpace_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (s : ℝ≥0) :
    ξ.markedJumpSpace S hflow hf hr hξ initial s ≤ mΩ := by
  intro A hA
  choose B hBmeas hBstart hBeq using hA
  have hsplit : A = ⋃ N : ℕ, (B N ∩ ξ.activeEvent N s) := by
    ext ω
    constructor
    · intro hωA
      refine Set.mem_iUnion.mpr ⟨ξ.activeSegmentIndex hne s ω, ?_⟩
      have hact := ξ.mem_activeEvent_activeSegmentIndex hne s ω
      have : ω ∈ A ∩ ξ.activeEvent (ξ.activeSegmentIndex hne s ω) s :=
        ⟨hωA, hact⟩
      exact hBeq _ ▸ this
    · intro hω
      obtain ⟨N, hωN⟩ := Set.mem_iUnion.mp hω
      have : ω ∈ B N ∩ ξ.activeEvent N s := hωN
      exact ((hBeq N).symm ▸ this : ω ∈ A ∩ ξ.activeEvent N s).1
  rw [hsplit]
  refine MeasurableSet.iUnion fun N => MeasurableSet.inter ?_ ?_
  · exact (hξ.preJumpHistorySpace_le S hflow hf hr initial N) _ (hBmeas N)
  · exact hξ.measurableSet_activeEvent N s

/-- Observability increases with time. -/
theorem DavisJumpNoise.markedJumpSpace_mono
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) :
    Monotone (ξ.markedJumpSpace S hflow hf hr hξ initial) := by
  intro s t hst A hA
  choose B hBmeas hBstart hBeq using hA
  intro N
  classical
  set Bt : Set Ω := {ω | ξ.jumpTime N ω ≤ t} ∩
    ((⋃ k : Fin N, (B (k : ℕ) ∩ ξ.activeEvent (k : ℕ) s)) ∪
      (B N ∩ {ω | ξ.jumpTime N ω ≤ s})) with hBt
  have hmonoSpace := ξ.preJumpHistorySpace_mono S hflow initial
  have hjumpN : MeasurableSet[ξ.preJumpHistorySpace S hflow initial N]
      {ω | ξ.jumpTime N ω ≤ t} :=
    ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial N N
      le_rfl t
  have hjumpNs : MeasurableSet[ξ.preJumpHistorySpace S hflow initial N]
      {ω | ξ.jumpTime N ω ≤ s} :=
    ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial N N
      le_rfl s
  have hactk : ∀ k : Fin N,
      MeasurableSet[ξ.preJumpHistorySpace S hflow initial N]
        (ξ.activeEvent (k : ℕ) s) := fun k =>
    ξ.measurableSet_activeEvent_preJumpHistory S hflow hf hr hξ initial
      (k : ℕ) N k.2 s
  refine ⟨Bt, ?_, ?_, ?_⟩
  · refine MeasurableSet.inter hjumpN ?_
    refine MeasurableSet.union (MeasurableSet.iUnion fun k => ?_) ?_
    · exact ((hmonoSpace (le_of_lt k.2)) _ (hBmeas (k : ℕ))).inter (hactk k)
    · exact (hBmeas N).inter hjumpNs
  · exact fun ω hω => hω.1
  · ext ω
    constructor
    · rintro ⟨hωA, hωact⟩
      refine ⟨⟨hωact.1, ?_⟩, hωact⟩
      -- the segment active at `s` has index at most `N`
      set k := ξ.activeSegmentIndex hne s ω with hk
      have hactk' : ω ∈ ξ.activeEvent k s :=
        ξ.mem_activeEvent_activeSegmentIndex hne s ω
      have hkN : k ≤ N := by
        by_contra hcon
        push_neg at hcon
        have h1 : ξ.jumpTime (N + 1) ω ≤ ξ.jumpTime k ω :=
          ξ.jumpTime_mono ω hcon
        exact hωact.2 (le_trans h1 (le_trans hactk'.1 hst))
      have hωBk : ω ∈ B k := by
        have : ω ∈ A ∩ ξ.activeEvent k s := ⟨hωA, hactk'⟩
        exact (hBeq k ▸ this : ω ∈ B k ∩ ξ.activeEvent k s).1
      rcases lt_or_eq_of_le hkN with hlt | heq
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨k, hlt⟩, hωBk, hactk'⟩)
      · refine Or.inr ⟨heq ▸ hωBk, ?_⟩
        have : ξ.jumpTime k ω ≤ s := hactk'.1
        rw [heq] at this
        exact this
    · rintro ⟨⟨-, hωBt⟩, hωact⟩
      refine ⟨?_, hωact⟩
      set k := ξ.activeSegmentIndex hne s ω with hk
      have hactk' : ω ∈ ξ.activeEvent k s :=
        ξ.mem_activeEvent_activeSegmentIndex hne s ω
      rcases hωBt with hleft | hright
      · obtain ⟨j, hωj⟩ := Set.mem_iUnion.mp hleft
        have hjk : (j : ℕ) = k := ξ.activeEvent_unique hne hωj.2 hactk'
        have : ω ∈ B (j : ℕ) ∩ ξ.activeEvent (j : ℕ) s := hωj
        exact ((hBeq (j : ℕ)).symm ▸ this : ω ∈ A ∩ ξ.activeEvent (j : ℕ) s).1
      · have hstartN : ξ.jumpTime N ω ≤ s := hright.2
        have hactN : ω ∈ ξ.activeEvent N s := by
          refine ⟨hstartN, ?_⟩
          intro hcon
          exact hωact.2 (le_trans hcon hst)
        have : ω ∈ B N ∩ ξ.activeEvent N s := ⟨hright.1, hactN⟩
        exact ((hBeq N).symm ▸ this : ω ∈ A ∩ ξ.activeEvent N s).1

/-- **The observation filtration of the marked jump history.** -/
def DavisJumpNoise.markedJumpFiltration (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) : Filtration ℝ≥0 mΩ where
  seq := ξ.markedJumpSpace S hflow hf hr hξ initial
  mono' := ξ.markedJumpSpace_mono S hflow hf hr hξ hne initial
  le' := ξ.markedJumpSpace_le S hflow hf hr hξ hne initial

@[simp] theorem DavisJumpNoise.markedJumpFiltration_apply
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (s : ℝ≥0) :
    (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) s =
      ξ.markedJumpSpace S hflow hf hr hξ initial s := rfl

end SHS
