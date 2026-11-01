/-
# Itô diffusions as generator presentations: Dynkin's formula and the martingale problem

The hub category `SHSCat.GenPres` (`SHSLib/Category/GenPres.lean`) phrases Dynkin's formula
(`SatisfiesDynkin`) and the martingale problem (`SolvesMartingaleProblem`) for a process `X`
indexed by all of `ℝ`, without a time horizon. Solutions of SDEs (job E4,
`Gardiner.Ito.StochDE`) live on a finite horizon `[0, T]`, and job E5
(`Gardiner.Ito.Generator`) proves Dynkin's formula on `[0, T]` and the martingale property of the
compensated process stopped at `T`.

This file adds the horizon-`T` versions of the two predicates next to the existing ones (without
changing them), presents a one-dimensional time-homogeneous diffusion
`dx = a(x) dt + b(x) dW` as a `GenPres` (test functions: `C²` with bounded first and second
derivatives; generator `a φ′ + ½ b² φ″`), and transfers E5's results.

| Lean | content |
| --- | --- |
| `GenPres.SolvesMartingaleProblemOn` | martingale problem up to horizon `T` (compensated process stopped at `T`) |
| `GenPres.SatisfiesDynkinOn` | Dynkin's formula for `0 ≤ t ≤ T`; `satisfiesDynkin_iff_forall_on` |
| `ItoDiffusion.genPres` | the generator presentation of `dx = a(x) dt + b(x) dW` |
| `ItoDiffusion.dynkinProcess_eq` | its compensated process is E5's `itoDynkinProc` |
| `ItoDiffusion.solvesMartingaleProblemOn_of_isSDESol` | E5's martingale problem, in `GenPres` form |
| `ItoDiffusion.satisfiesDynkinOn_of_isSDESol`, `satisfiesDynkin_of_isSDESol` | Dynkin's formula on `[0, T]`, and on `[0, ∞)` for global solutions |
| `ItoDiffusion.stdWiener_*`, `ItoDiffusion.sinSDE_satisfiesDynkinOn` | instances: the standard Wiener process; `dx = −sin x dt + σ dW` |
-/
import SHSLib.Category.GenPres
import SHSLib.Gardiner.Ito.SDEBridge

open MeasureTheory Set

noncomputable section

universe u

namespace SHSCat

namespace GenPres

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The martingale problem up to a horizon `T`**: for every test function the compensated
process `φ(X_t) − φ(X_0) − ∫₀ᵗ Lφ(X_s) ds`, read at the clamped time `max 0 (min t T)`
(so held at `0` before time `0` and stopped at `T`), is a martingale for `ℱ`. -/
def SolvesMartingaleProblemOn (A : GenPres.{u}) (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (X : ℝ → Ω → A.State) (T : ℝ) : Prop :=
  ∀ φ : A.Test, Martingale (fun t => A.dynkinProcess φ X (max 0 (min t T))) ℱ P

/-- **Dynkin's formula up to a horizon `T`**: `SatisfiesDynkin` restricted to `0 ≤ t ≤ T`. -/
def SatisfiesDynkinOn (A : GenPres.{u}) (P : Measure Ω) (X : ℝ → Ω → A.State) (T : ℝ) :
    Prop :=
  ∀ (φ : A.Test) (t : ℝ), 0 ≤ t → t ≤ T →
    (∫ ω, A.ev φ (X t ω) ∂P) - ∫ ω, A.ev φ (X 0 ω) ∂P
      = ∫ ω, (∫ s in (0 : ℝ)..t, A.gen φ (X s ω)) ∂P

/-- Dynkin's formula on `[0, ∞)` is Dynkin's formula up to every horizon. -/
theorem satisfiesDynkin_iff_forall_on (A : GenPres.{u}) (P : Measure Ω) (X : ℝ → Ω → A.State) :
    A.SatisfiesDynkin P X ↔ ∀ T, A.SatisfiesDynkinOn P X T :=
  ⟨fun h _ φ t ht _ => h φ t ht, fun h φ t ht => h t φ t ht le_rfl⟩

end GenPres

namespace ItoDiffusion

open Gardiner.Ito Gardiner.Ito.StochDE Gardiner.Ito.Generator Gardiner.Ito.SDEBridge

/-- Test functions: `C²` functions with bounded first and second derivatives. -/
def C2BddTest : Type := {f : ℝ → ℝ // ∃ C1 C2, C2BddDeriv f C1 C2}

/-- The **generator presentation of `dx = a(x) dt + b(x) dW`**: states `ℝ`, test functions
`C2BddTest`, generator `L f = a f′ + ½ b² f″` (E5's `itoGen`). -/
def genPres (a b : ℝ → ℝ) : GenPres.{0} where
  State := ℝ
  Test := C2BddTest
  ev f y := f.1 y
  gen f y := itoGen (fun z _ => a z) (fun z _ => b z) f.1 0 y

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} {a b : ℝ → ℝ} {T K B : ℝ} {ξ : Ω → ℝ} {x : ℝ → Ω → ℝ}

omit mΩ in
/-- The compensated process of `genPres a b` is E5's `itoDynkinProc`. -/
theorem dynkinProcess_eq (φ : (genPres a b).Test) (t : ℝ) (ω : Ω) :
    (genPres a b).dynkinProcess φ x t ω =
      itoDynkinProc (fun z _ => a z) (fun z _ => b z) φ.1 x t ω := rfl

/-- **The martingale problem for SDE solutions, in `GenPres` form.** A solution of the
Lipschitz SDE `dx = a(x) dt + b(x) dW` on `[0, T]` with continuous coefficients, bounded noise
coefficient and continuous paths solves the martingale problem of `genPres a b` up to `T`. -/
theorem solvesMartingaleProblemOn_of_isSDESol (hW : IsFWiener W 𝓕 P)
    (hx : IsSDESol W 𝓕 P (fun y _ => a y) (fun y _ => b y) 0 T ξ x) (hT : 0 ≤ T)
    (hc : SDECoeffs (fun y _ => a y) (fun y _ => b y) 0 T K) (ha : Continuous a)
    (hb : Continuous b) (hB : ∀ y, |b y| ≤ B)
    (hxc : ∀ ω, ContinuousOn (fun t => x t ω) (Icc 0 T)) :
    (genPres a b).SolvesMartingaleProblemOn P 𝓕 x T := by
  intro φ
  obtain ⟨C1, C2, hφ⟩ := φ.2
  exact Generator.IsSDESol.martingale_itoDynkinProc_clamp hW hx hT hc (ha.comp continuous_fst)
    (hb.comp continuous_fst) (fun y _ => hB y) hφ hxc

/-- **Dynkin's formula for SDE solutions, in `GenPres` form**, up to the horizon `T`. -/
theorem satisfiesDynkinOn_of_isSDESol (hW : IsFWiener W 𝓕 P)
    (hx : IsSDESol W 𝓕 P (fun y _ => a y) (fun y _ => b y) 0 T ξ x)
    (hc : SDECoeffs (fun y _ => a y) (fun y _ => b y) 0 T K) (hξ : MemLp ξ 2 P)
    (ha : Continuous a) (hb : Continuous b) (hB : ∀ y, |b y| ≤ B) :
    (genPres a b).SatisfiesDynkinOn P x T := by
  intro φ t ht htT
  obtain ⟨C1, C2, hφ⟩ := φ.2
  have h := Generator.IsSDESol.dynkin hW hx hc hξ (ha.comp continuous_fst)
    (hb.comp continuous_fst) (fun y _ => hB y) hφ le_rfl ht htT
  simp only [genPres, itoGen] at h ⊢
  linarith

/-- **Dynkin's formula on `[0, ∞)`** (`GenPres.SatisfiesDynkin`) for a solution that exists on
every horizon. -/
theorem satisfiesDynkin_of_isSDESol (hW : IsFWiener W 𝓕 P)
    (hx : ∀ T, IsSDESol W 𝓕 P (fun y _ => a y) (fun y _ => b y) 0 T ξ x)
    (hc : ∀ T, ∃ K, SDECoeffs (fun y _ => a y) (fun y _ => b y) 0 T K) (hξ : MemLp ξ 2 P)
    (ha : Continuous a) (hb : Continuous b) (hB : ∀ y, |b y| ≤ B) :
    (genPres a b).SatisfiesDynkin P x := by
  rw [GenPres.satisfiesDynkin_iff_forall_on]
  intro T
  obtain ⟨K, hcK⟩ := hc T
  exact satisfiesDynkinOn_of_isSDESol hW (hx T) hcK hξ ha hb hB

/-! ### Instances -/

/-- **The standard Wiener process solves the martingale problem of `½ d²/dy²`** up to every
horizon. -/
theorem stdWiener_solvesMartingaleProblemOn {T : ℝ} (hT : 0 ≤ T) :
    (genPres (fun _ => 0) (fun _ => 1)).SolvesMartingaleProblemOn stdWienerMeasure
      stdFiltration stdWiener T :=
  solvesMartingaleProblemOn_of_isSDESol isFWiener_stdWiener
    (isSDESol_wiener isFWiener_stdWiener measurable_uncurry_stdWiener T) hT
    (sdeCoeffs_wiener 0 T) continuous_const continuous_const (B := 1) (fun _ => by simp)
    (fun ω => (continuous_stdWiener ω).continuousOn)

/-- **The standard Wiener process satisfies Dynkin's formula for `½ d²/dy²`** on `[0, ∞)`. -/
theorem stdWiener_satisfiesDynkin :
    (genPres (fun _ => 0) (fun _ => 1)).SatisfiesDynkin stdWienerMeasure stdWiener :=
  satisfiesDynkin_of_isSDESol isFWiener_stdWiener
    (fun T => isSDESol_wiener isFWiener_stdWiener measurable_uncurry_stdWiener T)
    (fun T => ⟨1, sdeCoeffs_wiener 0 T⟩) (memLp_const 0) continuous_const continuous_const
    (B := 1) (fun _ => by simp)

/-- **A nonlinear instance.** The solution of `dx = −sin x dt + σ dW`, `x(0) = 0`, driven by the
standard Wiener process satisfies Dynkin's formula of `genPres (−sin) σ` on `[0, T]`. -/
theorem sinSDE_satisfiesDynkinOn (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ x, IsSDESol stdWiener stdFiltration stdWienerMeasure (fun y _ => -Real.sin y)
        (fun _ _ => σ) 0 T (fun _ => 0) x ∧
      (genPres (fun y => -Real.sin y) (fun _ => σ)).SatisfiesDynkinOn stdWienerMeasure x T := by
  obtain ⟨x, hx, -⟩ := sinSDE_existsUnique isFWiener_stdWiener hT σ
    (x0 := fun _ => (0 : ℝ)) stronglyMeasurable_const (memLp_const 0)
  exact ⟨x, hx, satisfiesDynkinOn_of_isSDESol isFWiener_stdWiener hx (sdeCoeffs_sin σ 0 T)
    (memLp_const 0) Real.continuous_sin.neg continuous_const (B := |σ|) (fun _ => le_rfl)⟩

end ItoDiffusion

end SHSCat
