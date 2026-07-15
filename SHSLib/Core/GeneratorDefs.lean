/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SHSLib.Core.Basic

open MeasureTheory MeasurableSpace Topology Filter

noncomputable section

/-! # Test functions and the SHS extended generator

This module contains the definitions shared by the concrete Davis construction
and the generator theorems.  Keeping them separate avoids an import cycle.
-/

/-- A test function `ψ : Q × ℝⁿ × [0,∞) → ℝ` for the extended generator,
required to be C¹ with respect to its second and third arguments. -/
structure SHS.TestFunction (Q : Type*) (n : ℕ) where
  /-- The test function `ψ(q, x, t)`. -/
  toFun : Q → EuclideanSpace ℝ (Fin n) → ℝ → ℝ
  /-- Gradient of `ψ` with respect to `x`. -/
  grad_x : Q → EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)
  /-- Partial derivative of `ψ` with respect to `t`. -/
  partial_t : Q → EuclideanSpace ℝ (Fin n) → ℝ → ℝ

/-- The SHS extended generator (Hespanha, Eq. 9). -/
def SHS.extendedGenerator {Q : Type*} {n m : ℕ} (S : SHS Q n m)
    (ψ : SHS.TestFunction Q n)
    (q : Q) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  @inner ℝ _ _ (ψ.grad_x q x t) (S.f q x t) +
  ψ.partial_t q x t +
  ∑ ℓ : Fin m,
    (ψ.toFun (S.phi_q ℓ q x t) (S.phi_x ℓ q x t) t - ψ.toFun q x t) *
      S.intensity ℓ q x t
